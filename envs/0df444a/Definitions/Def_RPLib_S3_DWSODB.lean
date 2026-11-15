-- Prove2me | Definitions.Def_RPLib_S3_DWSODB
-- name    : RPLib_S3_DWSODB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T18:19:04.807132+00:00
-- url     : https://prove2.me/theorems/b445783c-383a-43bd-8078-531499ab139c
-- title:
--   Weight-two Ramanujan-Petersson library: the per-trace deficit (A2, A3), conditional on Tate
-- statement:
--   The per-trace deficit (A2, A3), conditional on Tate.
--
--   * `card_orbit_mul_autVC` : `#orbit(W) · #Aut_VC(W) = #G`.
--   * `card_le_orbit` : curves that are all changes of variables of `x` number at most `#orbit(x)`.
--   * `card_orb_le` : under `TateIsogenyPrimeToP`, the curves of trace `t` and content `f` number at most
--     `#redPrim(D/f²) · #G / s(D/f²)` (Pic-class partition, each class inside one orbit, `#Aut ≥ s`).
--   * **`deficit_le`** : `p ∤ t ⇒ ellCount_M(t) - pairCount_t ≤ M² (ellCount_1(t) - #{W : a_W = t}/#G)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSODA

/-!
# S3-DWS-Ordinary, part DB: the per-trace deficit (A2, A3), conditional on Tate

* `card_orbit_mul_autVC` : `#orbit(W) · #Aut_VC(W) = #G`.
* `card_le_orbit` : curves that are all changes of variables of `x` number at most `#orbit(x)`.
* `card_orb_le` : under `TateIsogenyPrimeToP`, the curves of trace `t` and content `f` number at most
  `#redPrim(D/f²) · #G / s(D/f²)` (Pic-class partition, each class inside one orbit, `#Aut ≥ s`).
* **`deficit_le`** : `p ∤ t ⇒ ellCount_M(t) - pairCount_t ≤ M² (ellCount_1(t) - #{W : a_W = t}/#G)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine RPLib.TateNF

namespace RamanujanPetersson.S3.DWSO

open RPLib.Weil RPLib.Isog RPLib.Hasse RPLib.DWS RamanujanPetersson.Hurwitz

lemma card_orbit_mul_autVC {F : Type*} [Field F] (W : WeierstrassCurve F) :
    Nat.card (MulAction.orbit (VariableChange F) W) * Nat.card (AutVC W) = Nat.card (VariableChange F) := by
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm]
  exact Subgroup.card_mul_index _

lemma card_le_orbit {F : Type} [Field F] [Fintype F] {t : ℤ} (s : Finset (WT F t)) (x : WT F t)
    (h : ∀ y ∈ s, ∃ C : VariableChange F, C • x.1 = y.1) :
    s.card ≤ Nat.card (MulAction.orbit (VariableChange F) x.1) := by
  classical
  rw [Nat.card_coe_set_eq]
  have hsub : ((s.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset (WeierstrassCurve F)) :
      Set (WeierstrassCurve F)) ⊆ MulAction.orbit (VariableChange F) x.1 := by
    intro W hW
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe] at hW
    obtain ⟨y, hy, rfl⟩ := hW
    exact MulAction.mem_orbit_iff.mpr (h y hy)
  calc s.card = (s.map ⟨Subtype.val, Subtype.val_injective⟩).card := (Finset.card_map _).symm
    _ = ((s.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset (WeierstrassCurve F)) :
          Set (WeierstrassCurve F)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (MulAction.orbit (VariableChange F) x.1).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

section Main

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {L : Type} [Field L] [Algebra F L] [IsAlgClosed L]
  [DecidableEq L] [Algebra.IsAlgebraic F L]

attribute [local instance] finite_coordinateRing decEqFF

/-- **(A2)** The trace-`t` curves of content `f`: `#s · s(D/f²) ≤ #redPrim(D/f²) · #G`. -/
theorem card_orb_le (hT : TateIsogenyPrimeToP.{0}) (p : ℕ) [Fact p.Prime] [CharP F p] {t : ℤ}
    (hpt : ¬ (p : ℤ) ∣ t) (f : ℤ) (s : Finset (WT F t)) (hs : ∀ x ∈ s, ∃ d : OrdData x.1 L, d.f = f) :
    s.card * QA.sD ((t ^ 2 - 4 * (Fintype.card F : ℤ)) / f ^ 2) ≤
      (redPrim ((t ^ 2 - 4 * (Fintype.card F : ℤ)) / f ^ 2)).card * Nat.card (VariableChange F) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  obtain ⟨d₀, rfl⟩ := hs x₀ hx₀
  have hD₀ := d₀.disc_neg
  have hdiv₀ := div_eq_of_ord d₀
  rw [x₀.2.2] at hdiv₀
  rw [hdiv₀]
  have hdisc : ∀ x ∈ s, ∀ d : OrdData x.1 L, d.f = d₀.f →
      tr d.w ^ 2 + 4 * -(deg d.w : ℤ) = tr d₀.w ^ 2 + 4 * -(deg d₀.w : ℤ) := by
    intro x _ d hdf
    have h1 := div_eq_of_ord d
    rw [x.2.2, hdf] at h1
    exact h1.symm.trans hdiv₀
  have hord : ∀ x : WT F t, ¬ ((ringChar F : ℤ) ∣ RPLib.EllFq.trace x.1) := fun x => by
    rw [ringChar.eq F p, x.2.2]; exact hpt
  have hπ₀ : d₀.toOAct.ι (⟨d₀.b, d₀.f⟩ : Ord d₀) = piE x₀.1 L := by
    rw [OrdData.toOAct_ι]; exact θ_pi d₀
  have hπF : (((⟨d₀.b, d₀.f⟩ : Ord d₀).im.natAbs : ℕ) : F) ≠ 0 := by
    show ((d₀.f.natAbs : ℕ) : F) ≠ 0
    intro h
    rw [CharP.cast_eq_zero_iff F p] at h
    exact not_dvd_f_of_ord d₀ (by rw [x₀.2.2]; exact hpt) (Int.ofNat_dvd_left.mpr h)
  have hcls : ∀ x ∈ s, ∃ c : QA.PicQ hD₀, QuotClass x.1 hD₀ d₀.toOAct c := by
    intro x hx
    obtain ⟨d, hdf⟩ := hs x hx
    have hd := hdisc x hx d hdf
    obtain ⟨k, hk⟩ := two_dvd_sub_of_disc hd.symm
    have hb : tr d.w = tr d₀.w + 2 * k := by linarith
    have ha : -(deg d.w : ℤ) = -(deg d₀.w : ℤ) - k ^ 2 - tr d₀.w * k := by
      rw [hb] at hd; linarith
    have hre : 2 * (d₀.b - k * d₀.f) = 2 * d.b := by
      have h1 := d₀.htr
      have h2 := d.htr
      rw [x₀.2.2] at h1
      rw [x.2.2, hdf, hb] at h2
      linear_combination h2 - h1
    have hπ₁ : (oactComap d.toOAct (shiftEquiv k hb ha)).ι (⟨d₀.b, d₀.f⟩ : Ord d₀) = piE x.1 L := by
      rw [oactComap_ι, shiftEquiv_mk, OrdData.toOAct_ι, ← θ_pi d]
      congr 1
      ext
      · exact mul_left_cancel₀ two_ne_zero hre
      · exact hdf.symm
    have hcard : Nat.card x₀.1.toAffine.Point = Nat.card x.1.toAffine.Point :=
      (numPoints_eq_iff_trace_eq x₀.1 x.1).mpr (by rw [x₀.2.2, x.2.2])
    exact exists_quotClass_of_tate hT hcard (hord x₀) hD₀ hπ₀ hπ₁ hπF
  haveI : Nonempty (QA.PicQ hD₀) := ⟨(hcls x₀ hx₀).choose⟩
  choose! g hg using hcls
  haveI : Finite (Classes (tr d₀.w ^ 2 + 4 * -(deg d₀.w : ℤ))) :=
    Finite.of_surjective _ (toClass_bijective _).2
  haveI : Finite (QA.PicQ hD₀) := Finite.of_equiv _ (QA.classesEquivPic hD₀)
  letI := Fintype.ofFinite (QA.PicQ hD₀)
  have hcardT : (Finset.univ : Finset (QA.PicQ hD₀)).card =
      (redPrim (tr d₀.w ^ 2 + 4 * -(deg d₀.w : ℤ))).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, QA.card_picQ_eq hD₀,
      ← Nat.card_congr (Equiv.ofBijective _ (toClass_bijective _)), Nat.card_eq_fintype_card,
      Fintype.card_coe]
  have hfib : ∀ x ∈ s, (s.filter (fun y => g y = g x)).card * QA.sD (tr d₀.w ^ 2 + 4 * -(deg d₀.w : ℤ)) ≤
      Nat.card (VariableChange F) := by
    intro x hx
    obtain ⟨d, hdf⟩ := hs x hx
    have hle : (s.filter (fun y => g y = g x)).card ≤ Nat.card (MulAction.orbit (VariableChange F) x.1) := by
      apply card_le_orbit
      intro y hy
      rw [Finset.mem_filter] at hy
      exact IsoFq.exists_vc ((isoFq_iff_of_quotClass hD₀ (hg x hx) (hg y hy.1)).mpr hy.2.symm)
    have hA : QA.sD (tr d₀.w ^ 2 + 4 * -(deg d₀.w : ℤ)) ≤ Nat.card (AutVC x.1) := by
      rw [← hdisc x hx d hdf, ← QA.card_units_eq_sD d.disc_neg, ← card_units_endFq d.toOAct]
      exact card_units_le_autVC
    calc _ ≤ Nat.card (MulAction.orbit (VariableChange F) x.1) * Nat.card (AutVC x.1) :=
          Nat.mul_le_mul hle hA
      _ = Nat.card (VariableChange F) := card_orbit_mul_autVC x.1
  have hsD := sD_pos (tr d₀.w ^ 2 + 4 * -(deg d₀.w : ℤ))
  have h := card_le_of_fibers s g Finset.univ (fun x _ => Finset.mem_univ _) _
    (fun x hx => (Nat.le_div_iff_mul_le hsD).mpr (hfib x hx))
  rw [hcardT] at h
  calc s.card * QA.sD _ ≤ (redPrim _).card * (Nat.card (VariableChange F) / QA.sD _) * QA.sD _ :=
        Nat.mul_le_mul_right _ h
    _ = (redPrim _).card * (Nat.card (VariableChange F) / QA.sD _ * QA.sD _) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)

end Main

/-- **(A3) The per-trace deficit**, conditional on Tate: for `p ∤ t`,
`ellCount_M(1,t,q) - pairCount_t ≤ M² (ellCount_1(1,t,q) - #{W : Δ ≠ 0, a_W = t}/#G)`. -/
theorem deficit_le (hT : TateIsogenyPrimeToP.{0}) {p : ℕ} [Fact p.Prime] {m : ℕ}
    (F : Type) [Field F] [Fintype F] [DecidableEq F] (hq : Fintype.card F = p ^ m) {M : ℕ} [NeZero M]
    (hM4 : 4 ≤ M) (hpM : ¬ p ∣ M) {t : ℤ} (hpt : ¬ (p : ℤ) ∣ t) :
    ellCount M 1 t (p ^ m) - pairCount F M t ≤
      (M : ℚ) ^ 2 * (ellCount 1 1 t (p ^ m) - (Nat.card (WT F t) : ℚ) / Nat.card (VariableChange F)) := by
  classical
  have : CharP F p := charP_of_card_eq_prime_pow hq
  have hMF : (M : F) ≠ 0 := fun h => hpM ((CharP.cast_eq_zero_iff F p M).mp h)
  have hord : ∀ x : WT F t, ¬ ((ringChar F : ℤ) ∣ RPLib.EllFq.trace x.1) := fun x => by
    rw [ringChar.eq F p, x.2.2]; exact hpt
  have hd : ∀ x : WT F t, Nonempty (OrdData x.1 (AlgebraicClosure F)) := fun x => exists_ordData (hord x)
  set D : ℤ := t ^ 2 - 4 * ((p ^ m : ℕ) : ℤ) with hD
  set g : WT F t → ℤ := fun x => (Classical.choice (hd x)).f with hg
  have hmaps : ∀ x ∈ (Finset.univ : Finset (WT F t)), g x ∈ fset D := by
    intro x _
    have h := f_mem_fset_of_ord (Classical.choice (hd x))
    rwa [x.2.2, hq] at h
  have hG : (0 : ℚ) < Nat.card (VariableChange F) := by
    have : Nonempty (VariableChange F) := ⟨1⟩
    exact_mod_cast Nat.card_pos
  have h2 : ∀ x : WT F t, Nat.card (PtOrd x.1 M) = Lval M t (g x) (D / (g x) ^ 2) := by
    intro x
    have h := card_ptOrd_eq_Lval (Classical.choice (hd x)) hMF
    rw [x.2.2, hq] at h
    exact h
  have hA1 : (Nat.card (VariableChange F) : ℚ) * pairCount F M t = ∑ f ∈ fset D,
      ((Finset.univ.filter (fun x => g x = f)).card : ℚ) * Lval M t f (D / f ^ 2) := by
    have h := card_G_mul_pairCount (F := F) hM4 t
    rw [Finset.sum_congr rfl (fun x _ => h2 x), ← Finset.sum_fiberwise_of_maps_to hmaps] at h
    rw [← Nat.cast_mul, h]
    push_cast
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const,
      nsmul_eq_mul]
  have hN : (Nat.card (WT F t) : ℚ) = ∑ f ∈ fset D, ((Finset.univ.filter (fun x => g x = f)).card : ℚ) := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmaps]
    push_cast; rfl
  have hpc : (pairCount F M t : ℚ) = ∑ f ∈ fset D,
      ((Finset.univ.filter (fun x => g x = f)).card : ℚ) * Lval M t f (D / f ^ 2) /
        Nat.card (VariableChange F) := by
    rw [← Finset.sum_div, ← hA1]; field_simp
  rw [ellCount_eq_sum, ellCount_eq_sum, hpc, hN, ← Finset.sum_sub_distrib, Finset.sum_div,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  rw [Lval_one]
  have hL : (Lval M t f (D / f ^ 2) : ℚ) ≤ (M : ℚ) ^ 2 := by exact_mod_cast Lval_le M t f _
  have hS : (0 : ℚ) < QA.sD (D / f ^ 2) := by exact_mod_cast sD_pos _
  have hbr : ((Finset.univ.filter (fun x => g x = f)).card : ℚ) / Nat.card (VariableChange F) ≤
      ((redPrim (D / f ^ 2)).card : ℚ) / QA.sD (D / f ^ 2) := by
    rw [div_le_div_iff₀ hG hS]
    have h := card_orb_le (L := AlgebraicClosure F) hT p hpt f (Finset.univ.filter (fun x => g x = f))
      (fun x hx => ⟨Classical.choice (hd x), (Finset.mem_filter.mp hx).2⟩)
    rw [hq] at h
    exact_mod_cast h
  calc ((redPrim (D / f ^ 2)).card : ℚ) * (Lval M t f (D / f ^ 2) : ℚ) / QA.sD (D / f ^ 2) -
        ((Finset.univ.filter (fun x => g x = f)).card : ℚ) * Lval M t f (D / f ^ 2) /
          Nat.card (VariableChange F)
      = (Lval M t f (D / f ^ 2) : ℚ) * (((redPrim (D / f ^ 2)).card : ℚ) / QA.sD (D / f ^ 2) -
          ((Finset.univ.filter (fun x => g x = f)).card : ℚ) / Nat.card (VariableChange F)) := by ring
    _ ≤ (M : ℚ) ^ 2 * (((redPrim (D / f ^ 2)).card : ℚ) / QA.sD (D / f ^ 2) -
          ((Finset.univ.filter (fun x => g x = f)).card : ℚ) / Nat.card (VariableChange F)) :=
        mul_le_mul_of_nonneg_right hL (sub_nonneg.mpr hbr)
    _ = _ := by rw [hD]; push_cast; ring

end RamanujanPetersson.S3.DWSO


