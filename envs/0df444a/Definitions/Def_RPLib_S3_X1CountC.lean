-- Prove2me | Definitions.Def_RPLib_S3_X1CountC
-- name    : RPLib_S3_X1CountC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:24:54.403853+00:00
-- url     : https://prove2.me/theorems/b1d0ed66-8d57-4511-a3de-b489234067be
-- title:
--   Weight-two Ramanujan-Petersson library: Bezout-lite, assembly over components, Nagata shear
-- statement:
--   Bezout-lite, assembly over components, Nagata shear.
--
--   Polynomials in `k[X][Y] = k[X][X]`, evaluated at `v : L × L` by `ev` (part B).
--   * `card_common_le`: a monic irreducible `g` not dividing `h` has boundedly many common zeros with `h`
--     over every field `L ⊇ k` (bound independent of `L`).
--   * `count_good`: for `F ≠ 0` whose factors have unit leading coefficients and nonzero `Y`-derivatives (irreducible
--     ones), a finite set `S` of monic irreducible factors not dividing `E` with
--     `|#{F = 0, E ≠ 0}(L) - Σ_{g ∈ S} #{g = 0}(L)| ≤ C₀` for every finite field `L ⊇ k`, and every common zero of
--     `F` with `E ≠ 0` lies on some `g ∈ S`.
--   * Nagata shear `sig N : f(X, Y) ↦ f(X + Y^N, Y)` (a ring automorphism), `ev_sig`, `isUnit_lc_shS` (leading
--     coefficient in `Y` becomes a unit for large `N`), `derivative_shS_ne_zero` (over `ZMod p`, `p ∤ N`, an irreducible
--     factor keeps `∂/∂Y ≠ 0`; otherwise it would be a `p`-th power, `eq_pow_of_derivs`).
--   * `conv : MvPolynomial (Fin 2) k →ₐ[k] k[X][X]` (`X 0 ↦ C X`, `X 1 ↦ X`), `convBack_conv`, `ev_conv`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_X1CountB

/-!
# X1Count part C: Bezout-lite, assembly over components, Nagata shear (unit S3-X1Count)

Polynomials in `k[X][Y] = k[X][X]`, evaluated at `v : L × L` by `ev` (part B).
* `card_common_le`: a monic irreducible `g` not dividing `h` has boundedly many common zeros with `h`
  over every field `L ⊇ k` (bound independent of `L`).
* `count_good`: for `F ≠ 0` whose factors have unit leading coefficients and nonzero `Y`-derivatives (irreducible
  ones), a finite set `S` of monic irreducible factors not dividing `E` with
  `|#{F = 0, E ≠ 0}(L) - Σ_{g ∈ S} #{g = 0}(L)| ≤ C₀` for every finite field `L ⊇ k`, and every common zero of
  `F` with `E ≠ 0` lies on some `g ∈ S`.
* Nagata shear `sig N : f(X, Y) ↦ f(X + Y^N, Y)` (a ring automorphism), `ev_sig`, `isUnit_lc_shS` (leading
  coefficient in `Y` becomes a unit for large `N`), `derivative_shS_ne_zero` (over `ZMod p`, `p ∤ N`, an irreducible
  factor keeps `∂/∂Y ≠ 0`; otherwise it would be a `p`-th power, `eq_pow_of_derivs`).
* `conv : MvPolynomial (Fin 2) k →ₐ[k] k[X][X]` (`X 0 ↦ C X`, `X 1 ↦ X`), `convBack_conv`, `ev_conv`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.X1Count

open RamanujanPetersson.Places

/-! ### Counting helpers -/

lemma natCard_subtype_eq {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    Nat.card {a // P a} = (Finset.univ.filter P).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by simp)

lemma sum_card_le {ι α : Type*} [DecidableEq ι] [DecidableEq α] (s : Finset ι) (A : ι → Finset α)
    (B : ι → ι → ℕ) (hB : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ B i j) :
    ∑ i ∈ s, (A i).card ≤ (s.biUnion A).card + ∑ i ∈ s, ∑ j ∈ s, B i j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih fun i hi j hj hij =>
      hB i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have h1 := Finset.card_union_add_card_inter (A a) (s.biUnion A)
    have h2 : (A a ∩ s.biUnion A).card ≤ ∑ j ∈ s, B a j := by
      rw [Finset.inter_biUnion]
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j hj => ?_)
      exact hB a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) (by rintro rfl; exact ha hj)
    have h3 : ∑ j ∈ s, B a j ≤ ∑ j ∈ insert a s, B a j :=
      Finset.sum_le_sum_of_subset (Finset.subset_insert a s)
    have h4 : ∑ i ∈ s, ∑ j ∈ s, B i j ≤ ∑ i ∈ s, ∑ j ∈ insert a s, B i j :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset (Finset.subset_insert a s)
    rw [Finset.sum_insert ha, Finset.biUnion_insert, Finset.sum_insert ha]
    omega

/-! ### Bezout-lite -/

section Bezout

variable {k : Type} [Field k]

lemma not_dvd_map_of_monic {g h : k[X][X]} (hg : g.Monic) (hdvd : ¬ g ∣ h) :
    ¬ g.map (algebraMap k[X] (RatFunc k)) ∣ h.map (algebraMap k[X] (RatFunc k)) := by
  intro hd
  have hinj : Function.Injective (algebraMap k[X] (RatFunc k)) := IsFractionRing.injective _ _
  apply hdvd
  rw [← modByMonic_eq_zero_iff_dvd hg]
  have e : h %ₘ g = h - g * (h /ₘ g) := eq_sub_of_add_eq (modByMonic_add_div h g)
  have hd2 : g.map (algebraMap k[X] (RatFunc k)) ∣ (h %ₘ g).map (algebraMap k[X] (RatFunc k)) := by
    rw [e, Polynomial.map_sub, Polynomial.map_mul]
    exact dvd_sub hd (dvd_mul_right _ _)
  have hlt : degree ((h %ₘ g).map (algebraMap k[X] (RatFunc k))) <
      degree (g.map (algebraMap k[X] (RatFunc k))) := by
    rw [degree_map_eq_of_injective hinj, degree_map_eq_of_injective hinj]
    exact degree_modByMonic_lt h hg
  exact (Polynomial.map_eq_zero_iff hinj).mp (eq_zero_of_dvd_of_degree_lt hd2 hlt)

lemma exists_comb {g h : k[X][X]} (hg : g.Monic) (hirr : Irreducible g) (hdvd : ¬ g ∣ h) :
    ∃ (u w : k[X][X]) (r : k[X]), r ≠ 0 ∧ u * g + w * h = C r := by
  have hinj : Function.Injective (algebraMap k[X] (RatFunc k)) := IsFractionRing.injective _ _
  have hirrK : Irreducible (g.map (algebraMap k[X] (RatFunc k))) :=
    (hg.irreducible_iff_irreducible_map_fraction_map (K := RatFunc k)).1 hirr
  obtain ⟨u, w, huw⟩ := hirrK.coprime_iff_not_dvd.2 (not_dvd_map_of_monic hg hdvd)
  obtain ⟨b1, hb1⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors k[X]) u
  obtain ⟨b2, hb2⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors k[X]) w
  refine ⟨C (b2 : k[X]) * IsLocalization.integerNormalization (nonZeroDivisors k[X]) u,
    C (b1 : k[X]) * IsLocalization.integerNormalization (nonZeroDivisors k[X]) w, (b1 : k[X]) * b2,
    mul_ne_zero (nonZeroDivisors.ne_zero b1.2) (nonZeroDivisors.ne_zero b2.2), ?_⟩
  apply Polynomial.map_injective _ hinj
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
  rw [hb1, hb2, Algebra.smul_def, Algebra.smul_def, Polynomial.algebraMap_apply, Polynomial.algebraMap_apply,
    show algebraMap k[X] (RatFunc k) ((b1 : k[X]) * b2) =
      algebraMap k[X] (RatFunc k) b1 * algebraMap k[X] (RatFunc k) b2 from map_mul _ _ _, C_mul]
  linear_combination (C (algebraMap k[X] (RatFunc k) b1) * C (algebraMap k[X] (RatFunc k) b2)) * huw

/-- **Bezout-lite**: a monic irreducible `g` and `h` with `g ∤ h` have boundedly many common zeros. -/
lemma card_common_le {g h : k[X][X]} (hg : g.Monic) (hirr : Irreducible g) (hdvd : ¬ g ∣ h) :
    ∃ C : ℕ, ∀ (L : Type) [Field L] [Finite L] [Algebra k L],
      Nat.card {v : L × L // ev v g = 0 ∧ ev v h = 0} ≤ C := by
  obtain ⟨u, w, r, hr, huw⟩ := exists_comb hg hirr hdvd
  refine ⟨r.natDegree * g.natDegree, fun L _ _ _ => ?_⟩
  classical
  have : Fintype L := Fintype.ofFinite L
  have hrL : r.map (algebraMap k L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap k L).injective).mpr hr
  have hgx : ∀ x : L, g.map ((aeval x : k[X] →ₐ[k] L) : k[X] →+* L) ≠ 0 := fun x => (hg.map _).ne_zero
  have hsub : ∀ v : L × L, (ev v g = 0 ∧ ev v h = 0) → v ∈ (r.map (algebraMap k L)).roots.toFinset.biUnion
      fun x => (g.map ((aeval x : k[X] →ₐ[k] L) : k[X] →+* L)).roots.toFinset.image (Prod.mk x) := by
    rintro v ⟨hg0, hh0⟩
    have hr0 : aeval v.1 r = 0 := by
      have := congrArg (ev v) huw
      rw [map_add, map_mul, map_mul, hg0, hh0, ev_C] at this
      simpa using this.symm
    refine Finset.mem_biUnion.mpr ⟨v.1, ?_, Finset.mem_image.mpr ⟨v.2, ?_, rfl⟩⟩
    · rw [Multiset.mem_toFinset, mem_roots hrL, IsRoot.def, eval_map_algebraMap]; exact hr0
    · rw [Multiset.mem_toFinset, mem_roots (hgx v.1), IsRoot.def, eval_map]; exact hg0
  calc Nat.card {v : L × L // ev v g = 0 ∧ ev v h = 0}
      = (Finset.univ.filter fun v : L × L => ev v g = 0 ∧ ev v h = 0).card := natCard_subtype_eq _
    _ ≤ _ := Finset.card_le_card fun v hv => hsub v (Finset.mem_filter.mp hv).2
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ x ∈ (r.map (algebraMap k L)).roots.toFinset, g.natDegree := Finset.sum_le_sum fun x _ =>
        Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans natDegree_map_le))
    _ = (r.map (algebraMap k L)).roots.toFinset.card * g.natDegree := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ r.natDegree * g.natDegree := Nat.mul_le_mul_right _
        ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans natDegree_map_le))

end Bezout

/-! ### Assembly over the irreducible factors -/

section Assembly

variable {k : Type} [Field k]

lemma ev_ne_zero_of_isUnit {L : Type*} [Field L] [Algebra k L] (v : L × L) {u : k[X][X]} (hu : IsUnit u) :
    ev v u ≠ 0 := (hu.map (ev v)).ne_zero

lemma exists_factor_zero {F : k[X][X]} (hF : F ≠ 0) {L : Type*} [Field L] [Algebra k L] (v : L × L)
    (h : ev v F = 0) : ∃ f ∈ UniqueFactorizationMonoid.factors F, ev v f = 0 := by
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hF
  rw [← hu, map_mul, map_multiset_prod] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h1)
  · exact absurd h1 (ev_ne_zero_of_isUnit v u.isUnit)

/-- The monic associate of `f` (when `lc f` is a unit). -/
noncomputable def monicOf (f : k[X][X]) : k[X][X] := C (Ring.inverse f.leadingCoeff) * f

lemma isUnit_C_inv {f : k[X][X]} (hf : IsUnit f.leadingCoeff) : IsUnit (C (Ring.inverse f.leadingCoeff)) :=
  isUnit_C.mpr hf.ringInverse

lemma monicOf_monic {f : k[X][X]} (hf : IsUnit f.leadingCoeff) : (monicOf f).Monic :=
  monic_C_mul_of_mul_leadingCoeff_eq_one (Ring.inverse_mul_cancel _ hf)

lemma monicOf_associated {f : k[X][X]} (hf : IsUnit f.leadingCoeff) : Associated (monicOf f) f :=
  associated_unit_mul_left f _ (isUnit_C_inv hf)

lemma ev_monicOf {f : k[X][X]} (hf : IsUnit f.leadingCoeff) {L : Type*} [Field L] [Algebra k L] (v : L × L) :
    ev v (monicOf f) = 0 ↔ ev v f = 0 := by
  rw [monicOf, map_mul, mul_eq_zero, or_iff_right (ev_ne_zero_of_isUnit v (isUnit_C_inv hf))]

/-- **Generic count**: `#{F = 0, E ≠ 0}(L)` is the sum over the good monic irreducible factors `g` of `F`
(`g ∤ E`) of `#{g = 0}(L)`, up to a constant independent of the finite field `L ⊇ k`. -/
theorem count_good (F E : k[X][X]) (hF : F ≠ 0) (hlc : ∀ g, g ∣ F → IsUnit g.leadingCoeff)
    (hder : ∀ g, Irreducible g → g ∣ F → derivative g ≠ 0) :
    ∃ S : Finset k[X][X], (∀ g ∈ S, g.Monic ∧ Irreducible g ∧ derivative g ≠ 0 ∧ g ∣ F ∧ ¬ g ∣ E) ∧
      (∀ (L : Type) [Field L] [Algebra k L] (v : L × L), ev v F = 0 → ev v E ≠ 0 → ∃ g ∈ S, ev v g = 0) ∧
      ∃ C : ℕ, ∀ (L : Type) [Field L] [Finite L] [Algebra k L],
        |(Nat.card {v : L × L // ev v F = 0 ∧ ev v E ≠ 0} : ℤ) -
          ∑ g ∈ S, (Nat.card {v : L × L // ev v g = 0} : ℤ)| ≤ C := by
  classical
  set S : Finset k[X][X] :=
    ((UniqueFactorizationMonoid.factors F).map monicOf).toFinset.filter (fun g => ¬ g ∣ E) with hSdef
  have hfac : ∀ f ∈ UniqueFactorizationMonoid.factors F, IsUnit f.leadingCoeff ∧ Irreducible f ∧ f ∣ F :=
    fun f hf => ⟨hlc f (UniqueFactorizationMonoid.dvd_of_mem_factors hf),
      UniqueFactorizationMonoid.irreducible_of_factor f hf, UniqueFactorizationMonoid.dvd_of_mem_factors hf⟩
  have hS : ∀ g ∈ S, g.Monic ∧ Irreducible g ∧ derivative g ≠ 0 ∧ g ∣ F ∧ ¬ g ∣ E := by
    intro g hg
    rw [hSdef, Finset.mem_filter, Multiset.mem_toFinset, Multiset.mem_map] at hg
    obtain ⟨⟨f, hf, rfl⟩, hE⟩ := hg
    obtain ⟨hu, hirr, hdvd⟩ := hfac f hf
    have hirr' : Irreducible (monicOf f) := (monicOf_associated hu).symm.irreducible hirr
    have hdvd' : monicOf f ∣ F := (monicOf_associated hu).dvd.trans hdvd
    exact ⟨monicOf_monic hu, hirr', hder _ hirr' hdvd', hdvd', hE⟩
  have hcov : ∀ (L : Type) [Field L] [Algebra k L] (v : L × L), ev v F = 0 → ev v E ≠ 0 →
      ∃ g ∈ S, ev v g = 0 := by
    intro L _ _ v hF0 hE0
    obtain ⟨f, hf, hf0⟩ := exists_factor_zero hF v hF0
    have hu := (hfac f hf).1
    refine ⟨monicOf f, ?_, (ev_monicOf hu v).mpr hf0⟩
    rw [hSdef, Finset.mem_filter, Multiset.mem_toFinset]
    refine ⟨Multiset.mem_map_of_mem _ hf, fun hd => hE0 ?_⟩
    obtain ⟨q, hq⟩ := hd
    rw [hq, map_mul, (ev_monicOf hu v).mpr hf0, zero_mul]
  have hBz : ∀ x : k[X][X] × k[X][X], ∃ C : ℕ, x.1.Monic → Irreducible x.1 → ¬ x.1 ∣ x.2 →
      ∀ (L : Type) [Field L] [Finite L] [Algebra k L],
        Nat.card {v : L × L // ev v x.1 = 0 ∧ ev v x.2 = 0} ≤ C := by
    intro x
    by_cases h : x.1.Monic ∧ Irreducible x.1 ∧ ¬ x.1 ∣ x.2
    · obtain ⟨C, hC⟩ := card_common_le h.1 h.2.1 h.2.2
      exact ⟨C, fun _ _ _ => hC⟩
    · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose B hB using hBz
  refine ⟨S, hS, hcov, ∑ g ∈ S, B (g, E) + ∑ g ∈ S, ∑ g' ∈ S, B (g, g'), fun L _ _ _ => ?_⟩
  have : Fintype L := Fintype.ofFinite L
  let Z : k[X][X] → Finset (L × L) := fun f => Finset.univ.filter fun v => ev v f = 0
  let P : Finset (L × L) := Finset.univ.filter fun v => ev v F = 0 ∧ ev v E ≠ 0
  have hP : Nat.card {v : L × L // ev v F = 0 ∧ ev v E ≠ 0} = P.card := natCard_subtype_eq _
  have hZ : ∀ f, Nat.card {v : L × L // ev v f = 0} = (Z f).card := fun f => natCard_subtype_eq _
  have h1 : P ⊆ S.biUnion fun g => Z g \ Z E := by
    intro v hv
    obtain ⟨hF0, hE0⟩ := (Finset.mem_filter.mp hv).2
    obtain ⟨g, hg, hg0⟩ := hcov L v hF0 hE0
    refine Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_sdiff.mpr ⟨?_, fun h => hE0 ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg0⟩
    · exact (Finset.mem_filter.mp h).2
  have h2 : (S.biUnion fun g => Z g \ Z E) ⊆ P := by
    intro v hv
    obtain ⟨g, hg, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨hvg, hvE⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨q, hq⟩ := (hS g hg).2.2.2.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, fun h => hvE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)⟩
    rw [hq, map_mul, (Finset.mem_filter.mp hvg).2, zero_mul]
  have h3 : ∀ g ∈ S, ∀ g' ∈ S, g ≠ g' → ((Z g \ Z E) ∩ (Z g' \ Z E)).card ≤ B (g, g') := by
    intro g hg g' hg' hne
    have hnd : ¬ g ∣ g' := fun hd => hne (eq_of_monic_of_associated (hS g hg).1 (hS g' hg').1
      ((hS g hg).2.1.associated_of_dvd (hS g' hg').2.1 hd))
    refine le_trans (Finset.card_le_card ?_) ((natCard_subtype_eq _).symm.le.trans
      (hB (g, g') (hS g hg).1 (hS g hg).2.1 hnd L))
    intro v hv
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Z] at hv ⊢
    exact ⟨hv.1.1, hv.2.1⟩
  have h4 : ∀ g ∈ S, (Z g ∩ Z E).card ≤ B (g, E) := by
    intro g hg
    refine le_trans (Finset.card_le_card ?_) ((natCard_subtype_eq _).symm.le.trans
      (hB (g, E) (hS g hg).1 (hS g hg).2.1 (hS g hg).2.2.2.2 L))
    intro v hv
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Z] at hv ⊢
    exact hv
  have hA := sum_card_le S (fun g => Z g \ Z E) (fun g g' => B (g, g')) h3
  have hP1 : P.card ≤ ∑ g ∈ S, (Z g \ Z E).card := (Finset.card_le_card h1).trans Finset.card_biUnion_le
  have hP2 : (S.biUnion fun g => Z g \ Z E).card ≤ P.card := Finset.card_le_card h2
  have hsplit : ∑ g ∈ S, (Z g).card = ∑ g ∈ S, (Z g \ Z E).card + ∑ g ∈ S, (Z g ∩ Z E).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun g _ => (Finset.card_sdiff_add_card_inter _ _).symm
  have hI : ∑ g ∈ S, (Z g ∩ Z E).card ≤ ∑ g ∈ S, B (g, E) := Finset.sum_le_sum h4
  rw [hP]
  simp only [hZ]
  rw [← Nat.cast_sum, abs_le]
  constructor <;> omega

end Assembly

/-! ### The Nagata shear `f(X, Y) ↦ f(X + Y^N, Y)` -/

section Shift

variable {k : Type*} [Field k]

noncomputable def phiS (s : k[X][X]) : k[X] →+* k[X][X] := (compRingHom (C X + s)).comp (mapRingHom C)

noncomputable def shS (s : k[X][X]) : k[X][X] →+* k[X][X] := eval₂RingHom (phiS s) X

lemma phiS_apply (s : k[X][X]) (a : k[X]) : phiS s a = (a.map C).comp (C X + s) := rfl

lemma shS_C (s : k[X][X]) (a : k[X]) : shS s (C a) = phiS s a := eval₂_C _ _

lemma shS_X (s : k[X][X]) : shS s X = X := eval₂_X _ _

lemma shS_monomial (s : k[X][X]) (n : ℕ) (a : k[X]) : shS s (monomial n a) = phiS s a * X ^ n :=
  eval₂_monomial _ _

lemma phiS_C (s : k[X][X]) (c : k) : phiS s (C c) = C (C c) := by
  rw [phiS_apply, Polynomial.map_C, C_comp]

lemma phiS_X (s : k[X][X]) : phiS s X = C X + s := by
  rw [phiS_apply, Polynomial.map_X, X_comp]

lemma shS_shS (s t : k[X][X]) (h : shS s t = -s) : (shS s).comp (shS t) = RingHom.id _ := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, RingHom.id_apply, shS_C, phiS_C]
    · simp only [RingHom.comp_apply, RingHom.id_apply, shS_C, phiS_X, map_add, h, add_neg_cancel_right]
  · simp only [RingHom.comp_apply, RingHom.id_apply, shS_X]

/-- The shear as a ring automorphism of `k[X][Y]`. -/
noncomputable def sig (N : ℕ) : k[X][X] ≃+* k[X][X] :=
  RingEquiv.ofRingHom (shS (X ^ N)) (shS (-X ^ N))
    (shS_shS _ _ (by rw [map_neg, map_pow, shS_X]))
    (shS_shS _ _ (by rw [map_pow, shS_X, neg_neg]))

lemma sig_apply (N : ℕ) (f : k[X][X]) : sig N f = shS (X ^ N) f := rfl

lemma ev_shS {L : Type*} [Field L] [Algebra k L] (s : k[X][X]) (v : L × L) (f : k[X][X]) :
    ev v (shS s f) = ev (v.1 + ev v s, v.2) f := by
  have key : ((ev v : k[X][X] →ₐ[k] L) : k[X][X] →+* L).comp (shS s) =
      ((ev (v.1 + ev v s, v.2) : k[X][X] →ₐ[k] L) : k[X][X] →+* L) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro c
        simp [shS_C, phiS_C]
      · simp [shS_C, phiS_X]
    · simp [shS_X]
  exact RingHom.congr_fun key f

lemma ev_sig {L : Type*} [Field L] [Algebra k L] (N : ℕ) (v : L × L) (f : k[X][X]) :
    ev v (sig N f) = ev (v.1 + v.2 ^ N, v.2) f := by
  rw [sig_apply, ev_shS, map_pow, ev_X]

/-- Coefficientwise application of a map `k[X] → k[X]`. -/
noncomputable def cmap (φ : k[X] → k[X]) (f : k[X][X]) : k[X][X] :=
  ∑ j ∈ Finset.range (f.natDegree + 1), C (φ (f.coeff j)) * X ^ j

lemma coeff_cmap (φ : k[X] → k[X]) (hφ : φ 0 = 0) (f : k[X][X]) (n : ℕ) :
    (cmap φ f).coeff n = φ (f.coeff n) := by
  simp only [cmap, finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by simp only [Finset.mem_range, not_lt] at h; omega), hφ]

lemma cmap_add (φ : k[X] → k[X]) (hφ : φ 0 = 0) (hadd : ∀ a b, φ (a + b) = φ a + φ b) (p q : k[X][X]) :
    cmap φ (p + q) = cmap φ p + cmap φ q := by
  ext n : 1
  rw [coeff_add, coeff_cmap φ hφ, coeff_cmap φ hφ, coeff_cmap φ hφ, coeff_add, hadd]

lemma cmap_monomial (φ : k[X] → k[X]) (hφ : φ 0 = 0) (n : ℕ) (a : k[X]) :
    cmap φ (monomial n a) = monomial n (φ a) := by
  ext m : 1
  rw [coeff_cmap φ hφ, coeff_monomial, coeff_monomial]
  split_ifs <;> simp [hφ]

lemma derivative_phiS (N : ℕ) (a : k[X]) :
    derivative (phiS (X ^ N) a) = C (N : k[X]) * X ^ (N - 1) * phiS (X ^ N) (derivative a) := by
  rw [phiS_apply, phiS_apply, derivative_comp, derivative_map, derivative_add, derivative_C, zero_add,
    derivative_X_pow]

/-- Chain rule: `∂_Y (σ f) = N Y^(N-1) σ(∂_X f) + σ(∂_Y f)`. -/
lemma derivative_sig (N : ℕ) (f : k[X][X]) :
    derivative (shS (X ^ N) f) =
      (N : k[X][X]) * X ^ (N - 1) * shS (X ^ N) (cmap derivative f) + shS (X ^ N) (derivative f) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, derivative_add, hp, hq, cmap_add _ derivative_zero (fun a b => derivative_add) p q,
      derivative_add, map_add, map_add]
    ring
  | monomial n a =>
    rw [shS_monomial, cmap_monomial _ derivative_zero, shS_monomial, derivative_monomial, shS_monomial,
      derivative_mul, derivative_phiS, derivative_X_pow, map_mul, map_natCast]
    simp only [C_eq_natCast, map_natCast]
    ring

lemma shS_injective (N : ℕ) : Function.Injective (shS (X ^ N) : k[X][X] → k[X][X]) := (sig N).injective

lemma derivs_zero_of (N : ℕ) (hN : (N : k) ≠ 0) (f : k[X][X]) (hf : f.natDegree + 1 < N)
    (h : derivative (shS (X ^ N) f) = 0) : cmap derivative f = 0 ∧ derivative f = 0 := by
  rw [derivative_sig] at h
  have h' : (N : k[X][X]) * X ^ (N - 1) * cmap derivative f + derivative f = 0 := by
    apply shS_injective N
    rw [map_zero, map_add, map_mul, map_mul, map_natCast, map_pow, shS_X]
    exact h
  have hD : derivative f = 0 := by
    ext j : 1
    rw [coeff_zero]
    by_cases hj : N - 1 ≤ j
    · rw [coeff_derivative, coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
    · have := congrArg (Polynomial.coeff · j) h'
      simp only [coeff_add, coeff_zero] at this
      rw [mul_assoc, ← C_eq_natCast, coeff_C_mul, coeff_X_pow_mul', if_neg hj, mul_zero, zero_add] at this
      exact this
  refine ⟨?_, hD⟩
  rw [hD, add_zero] at h'
  have hN' : (N : k[X][X]) ≠ 0 := by
    rw [← C_eq_natCast, ← C_eq_natCast]
    exact C_ne_zero.mpr (C_ne_zero.mpr hN)
  rcases mul_eq_zero.mp h' with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hN'
    · exact absurd h2 (pow_ne_zero _ X_ne_zero)
  · exact h1

/-- After the shear, the leading coefficient in `Y` is a nonzero constant. -/
lemma isUnit_lc_shS (N : ℕ) (hN : 0 < N) (f : k[X][X]) (hf : f ≠ 0) (hdeg : f.natDegree < N) :
    IsUnit (shS (X ^ N) f).leadingCoeff := by
  have hq : (C X + X ^ N : k[X][X]).natDegree = N := by
    rw [add_comm, natDegree_X_pow_add_C]
  have hqm : (C X + X ^ N : k[X][X]).leadingCoeff = 1 := by
    rw [add_comm]; exact monic_X_pow_add_C _ hN.ne'
  have hφdeg : ∀ a : k[X], a ≠ 0 → (phiS (X ^ N) a).natDegree = a.natDegree * N := fun a _ => by
    rw [phiS_apply, natDegree_comp, natDegree_map_eq_of_injective (C_injective), hq]
  have hφlc : ∀ a : k[X], (phiS (X ^ N) a).leadingCoeff = C a.leadingCoeff := fun a => by
    rw [phiS_apply, leadingCoeff_comp (by rw [hq]; exact hN.ne'), leadingCoeff_map_of_injective C_injective,
      hqm, one_pow, mul_one]
  have hφne : ∀ a : k[X], a ≠ 0 → phiS (X ^ N) a ≠ 0 := fun a ha h => by
    have := hφlc a
    rw [h, leadingCoeff_zero] at this
    exact ha (leadingCoeff_eq_zero.mp (C_injective (this.symm.trans C_0.symm)))
  set t : ℕ → k[X][X] := fun j => phiS (X ^ N) (f.coeff j) * X ^ j with ht
  have htdeg : ∀ j ∈ f.support, (t j).natDegree = (f.coeff j).natDegree * N + j := fun j hj => by
    show (phiS (X ^ N) (f.coeff j) * X ^ j).natDegree = _
    rw [natDegree_mul_X_pow j (hφne _ (mem_support_iff.mp hj)), hφdeg _ (mem_support_iff.mp hj)]
  have htne : ∀ j ∈ f.support, t j ≠ 0 := fun j hj =>
    mul_ne_zero (hφne _ (mem_support_iff.mp hj)) (pow_ne_zero _ X_ne_zero)
  have hsum : shS (X ^ N) f = ∑ j ∈ f.support, t j := by
    show eval₂ (phiS (X ^ N)) X f = _
    rw [eval₂_eq_sum, Polynomial.sum_def]
  obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image f.support (fun j => (f.coeff j).natDegree * N + j)
    (nonempty_support_iff.mpr hf)
  have hlt : ∀ j ∈ f.support.erase j0, (t j).natDegree < (t j0).natDegree := by
    intro j hj
    obtain ⟨hne, hjs⟩ := Finset.mem_erase.mp hj
    rw [htdeg j hjs, htdeg j0 hj0]
    refine lt_of_le_of_ne (hmax j hjs) fun he => hne ?_
    have hjN : j < N := lt_of_le_of_lt (le_natDegree_of_mem_supp j hjs) hdeg
    have hj0N : j0 < N := lt_of_le_of_lt (le_natDegree_of_mem_supp j0 hj0) hdeg
    have e1 : (j + (f.coeff j).natDegree * N) % N = j := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjN]
    have e2 : (j0 + (f.coeff j0).natDegree * N) % N = j0 := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj0N]
    calc j = (j + (f.coeff j).natDegree * N) % N := e1.symm
      _ = ((f.coeff j).natDegree * N + j) % N := by rw [add_comm]
      _ = ((f.coeff j0).natDegree * N + j0) % N := by rw [he]
      _ = (j0 + (f.coeff j0).natDegree * N) % N := by rw [add_comm]
      _ = j0 := e2
  have hrest : degree (∑ j ∈ f.support.erase j0, t j) < degree (t j0) := by
    rw [degree_eq_natDegree (htne j0 hj0)]
    refine lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun j hj => ?_)
    rw [degree_eq_natDegree (htne j (Finset.mem_of_mem_erase hj))]
    exact WithBot.coe_lt_coe.mpr (hlt j hj)
  rw [hsum, ← Finset.add_sum_erase _ _ hj0, add_comm, leadingCoeff_add_of_degree_lt hrest]
  show IsUnit (phiS (X ^ N) (f.coeff j0) * X ^ j0).leadingCoeff
  rw [leadingCoeff_mul_X_pow, hφlc]
  exact isUnit_C.mpr (IsUnit.mk0 _ (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hj0)))

end Shift

/-! ### Over `ZMod p`: no irreducible polynomial is a `p`-th power -/

section PthPower

variable (p : ℕ) [Fact p.Prime]

lemma eq_pow_of_derivs (f : (ZMod p)[X][X]) (h1 : cmap derivative f = 0) (h2 : derivative f = 0) :
    ∃ f2 : (ZMod p)[X][X], f = f2 ^ p := by
  have hp := (Fact.out : p.Prime)
  have hc : ∀ n, derivative (f.coeff n) = 0 := fun n => by
    rw [← coeff_cmap _ derivative_zero f n, h1, coeff_zero]
  have hc0 : contract p (0 : (ZMod p)[X]) = 0 := by
    ext n; rw [coeff_contract hp.ne_zero, coeff_zero, coeff_zero]
  refine ⟨cmap (contract p) (contract p f), ?_⟩
  rw [← map_frobenius_expand p]
  ext n : 1
  rw [coeff_map, coeff_expand hp.pos]
  split_ifs with hn
  · rw [coeff_cmap _ hc0, coeff_contract hp.ne_zero, Nat.div_mul_cancel hn, frobenius_def,
      ← ZMod.expand_card, expand_contract p (hc n) hp.ne_zero]
  · rw [map_zero]
    conv_lhs => rw [← expand_contract p h2 hp.ne_zero]
    rw [coeff_expand hp.pos, if_neg hn]

lemma derivative_shS_ne_zero {N : ℕ} (hN : ((N : ℕ) : ZMod p) ≠ 0) {h0 : (ZMod p)[X][X]}
    (hirr : Irreducible h0) (hdeg : h0.natDegree + 1 < N) : derivative (shS (X ^ N) h0) ≠ 0 := by
  intro h
  obtain ⟨h1, h2⟩ := derivs_zero_of N hN h0 hdeg h
  obtain ⟨f2, rfl⟩ := eq_pow_of_derivs p h0 h1 h2
  exact not_irreducible_pow (Fact.out : p.Prime).one_lt.ne' hirr

end PthPower

/-! ### From `MvPolynomial (Fin 2)` to `k[X][Y]` -/

section Conv

variable {k : Type*} [Field k]

/-- `X₀ ↦ X` (inner), `X₁ ↦ Y` (outer). -/
noncomputable def conv : MvPolynomial (Fin 2) k →ₐ[k] k[X][X] := MvPolynomial.aeval ![C X, X]

noncomputable def convBack : k[X][X] →ₐ[k] MvPolynomial (Fin 2) k :=
  aevalTower (aeval (MvPolynomial.X 0)) (MvPolynomial.X 1)

lemma convBack_conv (P : MvPolynomial (Fin 2) k) : convBack (conv P) = P := by
  have : convBack.comp conv = AlgHom.id k (MvPolynomial (Fin 2) k) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [conv, convBack]
  exact AlgHom.congr_fun this P

lemma ev_conv {L : Type*} [Field L] [Algebra k L] (v : L × L) (P : MvPolynomial (Fin 2) k) :
    ev v (conv P) = MvPolynomial.aeval ![v.1, v.2] P := by
  have : (ev (k := k) v).comp (conv (k := k)) = MvPolynomial.aeval ![v.1, v.2] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [conv]
  exact AlgHom.congr_fun this P

end Conv
end RamanujanPetersson.X1Count


