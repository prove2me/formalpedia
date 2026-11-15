-- Prove2me | Definitions.Def_RPLib_S3_SBCount
-- name    : RPLib_S3_SBCount
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:40.512947+00:00
-- url     : https://prove2.me/theorems/7c1c8329-db30-420a-9d71-cd9ad750f697
-- title:
--   Weight-two Ramanujan-Petersson library: Twisted orbit counting (obligation E2, abstract part)
-- statement:
--   Twisted orbit counting (obligation E2, abstract part).
--
--   `G` acts on an `Fq`-algebra `B` by `Fq`-algebra automorphisms, `A → B` with `B^G = A` (`Algebra.IsInvariant`),
--   `L` a finite field and `φ : L →ₐ[Fq] L`. For `y : B →ₐ[Fq] L` and `g : G` put `twist y g = y ∘ g`.
--   Main result `sum_card_twisted_eq`:
--     `Σ_g #{y | y ∘ g = φ ∘ y} = |G| · #{z : A →ₐ[Fq] L | φ ∘ z = z, z lifts to B}`.
--   The proof uses only the transitivity of `G` on the lifts of a fixed `z` (`exists_twist_eq`, from Mathlib's
--   `exists_smul_of_under_eq` and `Ideal.Quotient.stabilizerHom_surjective`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib

/-!
# Twisted orbit counting (obligation E2, abstract part)

`G` acts on an `Fq`-algebra `B` by `Fq`-algebra automorphisms, `A → B` with `B^G = A` (`Algebra.IsInvariant`),
`L` a finite field and `φ : L →ₐ[Fq] L`. For `y : B →ₐ[Fq] L` and `g : G` put `twist y g = y ∘ g`.
Main result `sum_card_twisted_eq`:
  `Σ_g #{y | y ∘ g = φ ∘ y} = |G| · #{z : A →ₐ[Fq] L | φ ∘ z = z, z lifts to B}`.
The proof uses only the transitivity of `G` on the lifts of a fixed `z` (`exists_twist_eq`, from Mathlib's
`exists_smul_of_under_eq` and `Ideal.Quotient.stabilizerHom_surjective`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace RamanujanPetersson.ZetaSB

section Abstract

variable {Fq : Type*} [CommRing Fq]
variable {B : Type*} [CommRing B] [Algebra Fq B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G Fq B]
variable {L : Type*} [Field L] [Algebra Fq L]

/-- `y ∘ g`. -/
noncomputable def twist (y : B →ₐ[Fq] L) (g : G) : B →ₐ[Fq] L :=
  y.comp (MulSemiringAction.toAlgHom Fq B g)

@[simp] theorem twist_apply (y : B →ₐ[Fq] L) (g : G) (b : B) : twist y g b = y (g • b) := rfl

theorem twist_twist (y : B →ₐ[Fq] L) (g h : G) : twist (twist y g) h = twist y (g * h) := by
  ext b; simp [mul_smul]

theorem twist_one (y : B →ₐ[Fq] L) : twist y (1 : G) = y := by
  ext b; simp

theorem comp_twist (φ : L →ₐ[Fq] L) (y : B →ₐ[Fq] L) (g : G) :
    φ.comp (twist y g) = twist (φ.comp y) g := rfl

variable (A : Type*) [CommRing A] [Algebra Fq A] [Algebra A B] [IsScalarTower Fq A B]

/-- Restriction of a point of `B` to `A`. -/
noncomputable def res (y : B →ₐ[Fq] L) : A →ₐ[Fq] L := y.comp (IsScalarTower.toAlgHom Fq A B)

@[simp] theorem res_apply (y : B →ₐ[Fq] L) (a : A) : res A y a = y (algebraMap A B a) := rfl

theorem res_comp (φ : L →ₐ[Fq] L) (y : B →ₐ[Fq] L) : res A (φ.comp y) = φ.comp (res A y) := rfl

variable [SMulCommClass G A B]

theorem res_twist (y : B →ₐ[Fq] L) (g : G) : res A (twist y g) = res A y := by
  ext a; simp [smul_algebraMap]

variable [Algebra.IsInvariant A B G]

/-- Transitivity: two points of `B` with the same restriction to `A = B^G` differ by an element of `G`. -/
theorem exists_twist_eq [Finite G] [Finite L] (y y' : B →ₐ[Fq] L) (h : res A y = res A y') :
    ∃ g : G, y' = twist y g := by
  classical
  have hQ : (RingHom.ker y).IsPrime := RingHom.ker_isPrime y
  have hQ' : (RingHom.ker y').IsPrime := RingHom.ker_isPrime y'
  have hunder : (RingHom.ker y).under A = (RingHom.ker y').under A := by
    ext a
    simp only [Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun z : A →ₐ[Fq] L => z a) h
    simp only [res_apply] at this
    rw [this]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G _ _ hunder
  set Q' : Ideal B := RingHom.ker y' with hQ'def
  set y1 : B →ₐ[Fq] L := twist y g⁻¹ with hy1
  have hker1 : ∀ b : B, b ∈ Q' ↔ y1 b = 0 := by
    intro b
    rw [hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem, RingHom.mem_ker, hy1, twist_apply]
  have hker2 : ∀ b : B, b ∈ Q' ↔ y' b = 0 := fun b => RingHom.mem_ker
  set P : Ideal A := Q'.under A with hPdef
  have : Q'.LiesOver P := ⟨rfl⟩
  -- the two induced embeddings of the residue ring
  let ι1 : B ⧸ Q' →+* L := Ideal.Quotient.lift Q' (y1 : B →+* L) (fun b hb => (hker1 b).mp hb)
  let ι2 : B ⧸ Q' →+* L := Ideal.Quotient.lift Q' (y' : B →+* L) (fun b hb => (hker2 b).mp hb)
  have hι1 : ∀ b, ι1 (Ideal.Quotient.mk Q' b) = y1 b := fun b => rfl
  have hι2 : ∀ b, ι2 (Ideal.Quotient.mk Q' b) = y' b := fun b => rfl
  have inj1 : Function.Injective ι1 := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hι1] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hker1 b).mpr hx)
  have inj2 : Function.Injective ι2 := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hι2] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hker2 b).mpr hx)
  -- the residue ring is a finite field
  have : Finite (B ⧸ Q') := Finite.of_injective ι1 inj1
  have : Q'.IsMaximal := Ideal.Quotient.maximal_of_isField Q' (Finite.isField_of_domain _)
  letI : Field (B ⧸ Q') := Ideal.Quotient.field Q'
  letI : Fintype (B ⧸ Q') := Fintype.ofFinite _
  letI : Fintype L := Fintype.ofFinite L
  set n := Fintype.card (B ⧸ Q') with hn
  have hn1 : 1 < n := Fintype.one_lt_card
  -- both images are the roots of X^n - X
  set S : Finset L := (Polynomial.X ^ n - Polynomial.X : Polynomial L).roots.toFinset with hS
  have hp0 : (Polynomial.X ^ n - Polynomial.X : Polynomial L) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L hn1
  have hScard : S.card ≤ n := by
    calc S.card ≤ (Polynomial.X ^ n - Polynomial.X : Polynomial L).roots.card := Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ n - Polynomial.X : Polynomial L).natDegree := Polynomial.card_roots' _
      _ = n := FiniteField.X_pow_card_sub_X_natDegree_eq L hn1
  have himage : ∀ (ι : B ⧸ Q' →+* L), Function.Injective ι →
      Finset.univ.image ι = S := by
    intro ι hι
    have hsub : Finset.univ.image ι ⊆ S := by
      intro x hx
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx
      rw [hS, Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, ← map_pow, FiniteField.pow_card, sub_self]
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_image_of_injective _ hι, Finset.card_univ]
    exact hScard
  have hrange : ∀ u : B ⧸ Q', ∃ v : B ⧸ Q', ι1 v = ι2 u := by
    intro u
    have : ι2 u ∈ Finset.univ.image ι1 := by
      rw [himage ι1 inj1, ← himage ι2 inj2]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ u)
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp this
    exact ⟨v, hv⟩
  choose σf hσf using hrange
  have σinj : Function.Injective σf := by
    intro u u' huu
    apply inj2
    rw [← hσf u, ← hσf u', huu]
  have σbij : Function.Bijective σf := Finite.injective_iff_bijective.mp σinj
  have σmul : ∀ u v, σf (u * v) = σf u * σf v := by
    intro u v; apply inj1; rw [map_mul, hσf, hσf, hσf, map_mul]
  have σadd : ∀ u v, σf (u + v) = σf u + σf v := by
    intro u v; apply inj1; rw [map_add, hσf, hσf, hσf, map_add]
  have σone : σf 1 = 1 := by apply inj1; rw [hσf, map_one, map_one]
  have σzero : σf 0 = 0 := by apply inj1; rw [hσf, map_zero, map_zero]
  let σh : (B ⧸ Q') →+* (B ⧸ Q') :=
    { toFun := σf, map_one' := σone, map_mul' := σmul, map_zero' := σzero, map_add' := σadd }
  let σr : (B ⧸ Q') ≃+* (B ⧸ Q') := RingEquiv.ofBijective σh σbij
  have hσr : ∀ u, ι1 (σr u) = ι2 u := fun u => hσf u
  have σcomm : ∀ x : A ⧸ P, σr (algebraMap (A ⧸ P) (B ⧸ Q') x) = algebraMap (A ⧸ P) (B ⧸ Q') x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply inj1
    rw [hσr, Ideal.Quotient.algebraMap_mk_of_liesOver, hι1, hι2, hy1, twist_apply, smul_algebraMap]
    have := congrArg (fun z : A →ₐ[Fq] L => z a) h
    simpa only [res_apply] using this.symm
  let σa : (B ⧸ Q') ≃ₐ[A ⧸ P] (B ⧸ Q') := AlgEquiv.ofRingEquiv (f := σr) σcomm
  obtain ⟨⟨s, hs⟩, hsσ⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q' σa
  refine ⟨g⁻¹ * s, ?_⟩
  ext b
  have h1 := congrArg (fun e : (B ⧸ Q') ≃ₐ[A ⧸ P] (B ⧸ Q') => e (Ideal.Quotient.mk Q' b)) hsσ
  simp only [Ideal.Quotient.stabilizerHom_apply] at h1
  -- h1 : mk (s • b) = σa (mk b)
  have h2 : ι1 (Ideal.Quotient.mk Q' (s • b)) = ι2 (Ideal.Quotient.mk Q' b) := by
    rw [show s • b = (⟨s, hs⟩ : MulAction.stabilizer G Q') • b from rfl, h1]; exact hσr _
  rw [hι1, hι2, hy1, twist_apply] at h2
  rw [twist_apply, mul_smul, ← h2]

/-- For a point `y` with `y ∘ t₀ = φ ∘ y`, the twisted solutions are a coset of the stabiliser. -/
theorem card_twistSet_eq [Fintype G] [DecidableEq (B →ₐ[Fq] L)] (φ : L →ₐ[Fq] L) (y : B →ₐ[Fq] L) (t0 : G)
    (ht0 : twist y t0 = φ.comp y) :
    (Finset.univ.filter fun t : G => twist y t = φ.comp y).card =
      (Finset.univ.filter fun s : G => twist y s = y).card := by
  symm
  refine Finset.card_nbij' (fun s => s * t0) (fun t => t * t0⁻¹) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_sigma, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
    rw [← twist_twist, hs, ht0]
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_sigma, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
    rw [← twist_twist, ht, ← ht0, twist_twist, mul_inv_cancel, twist_one]
  · intro s _; simp
  · intro t _; simp

/-- The stabilisers along one fibre of `res` add up to `|G|`. -/
theorem sum_card_stab_fiber [Fintype G] [Finite L] [Fintype (B →ₐ[Fq] L)] [DecidableEq (B →ₐ[Fq] L)]
    [DecidableEq (A →ₐ[Fq] L)] (y0 : B →ₐ[Fq] L) :
    ∑ y ∈ Finset.univ.filter (fun y : B →ₐ[Fq] L => res A y = res A y0),
      (Finset.univ.filter fun s : G => twist y s = y).card = Fintype.card G := by
  classical
  have hk : ∀ y : B →ₐ[Fq] L, ∃ k : G, res A y = res A y0 → y = twist y0 k := by
    intro y
    by_cases hy : res A y = res A y0
    · obtain ⟨k, hk⟩ := exists_twist_eq (G := G) A y0 y hy.symm
      exact ⟨k, fun _ => hk⟩
    · exact ⟨1, fun h => absurd h hy⟩
  choose k hk using hk
  rw [← Finset.card_sigma]
  rw [← Finset.card_univ (α := G)]
  refine Finset.card_nbij' (fun p => k p.1 * p.2)
    (fun h => ⟨twist y0 h, (k (twist y0 h))⁻¹ * h⟩) ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
  · intro h _
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_filter, Finset.mem_sigma, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq]
    refine ⟨res_twist A y0 h, ?_⟩
    have e := hk (twist y0 h) (res_twist A y0 h)
    calc twist (twist y0 h) ((k (twist y0 h))⁻¹ * h)
        = twist (twist y0 (k (twist y0 h))) ((k (twist y0 h))⁻¹ * h) := by rw [← e]
      _ = twist y0 h := by rw [twist_twist, mul_inv_cancel_left]
  · rintro ⟨y, s⟩ hp
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_filter, Finset.mem_sigma, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hp
    obtain ⟨hy, hs⟩ := hp
    have e : twist y0 (k y * s) = y := by rw [← twist_twist, ← hk y hy, hs]
    simp only [e, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro h _
    simp only [mul_inv_cancel_left]

/-- Twisted counting identity. -/
theorem sum_card_twisted_eq [Fintype G] [Finite L] [Fintype (B →ₐ[Fq] L)] [Fintype (A →ₐ[Fq] L)]
    [DecidableEq (B →ₐ[Fq] L)] [DecidableEq (A →ₐ[Fq] L)] (φ : L →ₐ[Fq] L) :
    ∑ g : G, (Finset.univ.filter fun y : B →ₐ[Fq] L => twist y g = φ.comp y).card =
      ∑ z ∈ Finset.univ.filter (fun z : A →ₐ[Fq] L => φ.comp z = z),
        (if ∃ y : B →ₐ[Fq] L, res A y = z then Fintype.card G else 0) := by
  classical
  calc ∑ g : G, (Finset.univ.filter fun y : B →ₐ[Fq] L => twist y g = φ.comp y).card
      = ∑ y : B →ₐ[Fq] L, (Finset.univ.filter fun g : G => twist y g = φ.comp y).card := by
        simp only [Finset.card_filter]; exact Finset.sum_comm
    _ = ∑ z : A →ₐ[Fq] L, ∑ y ∈ Finset.univ.filter (fun y : B →ₐ[Fq] L => res A y = z),
          (Finset.univ.filter fun g : G => twist y g = φ.comp y).card :=
        (Finset.sum_fiberwise _ _ _).symm
    _ = ∑ z ∈ Finset.univ.filter (fun z : A →ₐ[Fq] L => φ.comp z = z),
          (if ∃ y : B →ₐ[Fq] L, res A y = z then Fintype.card G else 0) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hz : φ.comp z = z
        · rw [if_pos hz]
          by_cases hex : ∃ y : B →ₐ[Fq] L, res A y = z
          · rw [if_pos hex]
            obtain ⟨y0, rfl⟩ := hex
            rw [← sum_card_stab_fiber A y0]
            refine Finset.sum_congr rfl fun y hy => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
            have hφy : res A (φ.comp y) = res A y := by rw [res_comp, hy, hz]
            obtain ⟨t0, ht0⟩ := exists_twist_eq (G := G) A y (φ.comp y) hφy.symm
            exact card_twistSet_eq φ y t0 ht0.symm
          · rw [if_neg hex]
            refine Finset.sum_eq_zero fun y hy => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
            exact absurd ⟨y, hy⟩ hex
        · rw [if_neg hz]
          refine Finset.sum_eq_zero fun y hy => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro t _ ht
          apply hz
          rw [← hy, ← res_comp, ← ht, res_twist]

end Abstract

end RamanujanPetersson.ZetaSB


