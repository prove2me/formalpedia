-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoefficientFieldBaseChange
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoefficientFieldBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:38.827566+00:00
-- url     : https://prove2.me/theorems/d8bc16ed-3a93-46d6-9aa0-104e768eeae7
-- title:
--   Coefficient Field Base Change
-- statement:
--   Definitions and structural lemmas for Coefficient Field Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CoefficientFieldBaseChange.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
def ze (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
theorem ze_prim {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (ze n) n := Complex.isPrimitiveRoot_exp n hn.ne'
theorem ze_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : ze (n * m) ^ m = ze n := by
  unfold ze
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def subfieldBase (l : Level H) (L : IntermediateField ℚ ℂ) (hr : H.rt0 ∈ L) (hz : ze l.A ∈ L) : Base l L where
  unit n hn := (Nat.cast_ne_zero.mpr hn.ne').isUnit
  ρ := ⟨H.rt0, hr⟩
  ρ_sq := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  ζ := ⟨ze l.A, hz⟩
  ζ_prim := (IsPrimitiveRoot.coe_submonoidClass_iff (N := L)).mp (ze_prim l.A_pos)
def KA (l : Level H) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {H.rt0, ze l.A}
theorem rootZero_mem_adjoin (l : Level H) : H.rt0 ∈ KA l := IntermediateField.subset_adjoin _ _ (by simp)
theorem ze_mem_KA (l : Level H) : ze l.A ∈ KA l := IntermediateField.subset_adjoin _ _ (by simp)
def baseKA (l : Level H) : Base l (KA l) := subfieldBase l (KA l) (rootZero_mem_adjoin l) (ze_mem_KA l)
def dimD (D : Datum H) : ℕ := Module.finrank ℚ (maximalRealSubfield E) * D.p * D.q
structure IsModuli (D : Datum H) (l : Level H) {X : Scheme.{0}} (str : X ⟶ Sp (KA l))
    (univ : Obj D l (baseKA l) str) : Prop where
  smooth : SmoothOfRelativeDimension (dimD D) str
  qproj : IsQProjOver str
  repr : ∀ (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s),
    ∃! f : S ⟶ X, f ≫ str = s ∧ Nonempty (ObjMap o univ f)
  rigid : ∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ X) (o : Obj D l (baseKA l) (v ≫ str)),
    Nonempty (ObjMap o univ v) →
    Nonempty (ObjMap o univ
      (spMap (algebraMap k (DualNumber k)) ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v)) →
    v = spMap (algebraMap k (DualNumber k)) ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v
structure IsCoeffField (l : Level H) (F₀ : IntermediateField ℚ ℂ) : Prop where
  fin : FiniteDimensional ℚ F₀
  conj : ∀ (τ : E →+* ℂ) (x : E), τ x ∈ F₀
  root : ze l.M' ∈ F₀
theorem IsCoeffField.coeff_field_contains_root {l : Level H} {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) : H.rt0 ∈ F₀ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow]
    have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    rw [this]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h2 | h2
  · rw [← h2]; exact h.conj τ _
  · have : H.rt0 = -τ (H.rt : E) := by rw [h2, neg_neg]
    rw [this]; exact neg_mem (h.conj τ _)
theorem IsCoeffField.ze_mem {l : Level H} {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) : ze l.A ∈ F₀ := by
  obtain ⟨m, hm⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
  rw [← ze_pow l.A_pos hm0, ← hm]
  exact pow_mem h.root m
theorem IsCoeffField.KA_le {l : Level H} {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) : KA l ≤ F₀ := by
  rw [KA, IntermediateField.adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact h.coeff_field_contains_root
  · exact h.ze_mem
def IsCoeffField.incl {l : Level H} {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) : KA l →+* F₀ :=
  (IntermediateField.inclusion h.KA_le).toRingHom
def IsCoeffField.base {l : Level H} {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) : Base l F₀ :=
  subfieldBase l F₀ h.coeff_field_contains_root h.ze_mem
def baseChange {l : Level H} {X : Scheme.{0}} (str : X ⟶ Sp (KA l)) {F₀ : IntermediateField ℚ ℂ}
    (h : IsCoeffField l F₀) : Scheme.{0} := pullback str (spMap h.incl)
def baseChangeFst {l : Level H} {X : Scheme.{0}} (str : X ⟶ Sp (KA l)) {F₀ : IntermediateField ℚ ℂ}
    (h : IsCoeffField l F₀) : baseChange str h ⟶ X := pullback.fst str (spMap h.incl)
def baseChangeStr {l : Level H} {X : Scheme.{0}} (str : X ⟶ Sp (KA l)) {F₀ : IntermediateField ℚ ℂ}
    (h : IsCoeffField l F₀) : baseChange str h ⟶ Sp F₀ := pullback.snd str (spMap h.incl)
end GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange


