-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:24:34.983859+00:00
-- url     : https://prove2.me/theorems/033dcb9e-de15-4983-af8c-7204d39060d3
-- title:
--   Isogeny
-- statement:
--   Definitions and structural lemmas for Isogeny, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Theorems.Thm_GroundTheory_Arith_Abelian_aeval_genX_eq_zero_iff
import Theorems.Thm_GroundTheory_Arith_Abelian_map_liftPoint_genericPoint
import Theorems.Thm_GroundTheory_Arith_Abelian_transcendental_genX
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_zsmul
import Theorems.Thm_GroundTheory_Arith_Abelian_zsmul_eq_zero_iff
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian__Sq_ne_zero_of_ne_zero_fd3fba5d47fb
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian_isCoprime____Sq_a9e3a7b07819
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some


set_option autoImplicit false
namespace GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
universe u
variable {F : Type u} [Field F]
section Defs
def yOf {K : Type*} [Field K] (W : WeierstrassCurve K) : W.toAffine.Point → K
  | .zero => 0
  | .some _ y _ => y
theorem eq_some_xOf_yOf {K : Type*} [Field K] (W : WeierstrassCurve K) {P : W.toAffine.Point}
    (hP : P ≠ 0) : ∃ h : W.toAffine.Nonsingular (xOf W P) (yOf W P), P = .some _ _ h := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact ⟨h, rfl⟩
variable (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic]
noncomputable def ratMapValue (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point)
    {L : Type u} [Field L] [Algebra F L] [DecidableEq L] {u v : L}
    (h : (E.baseChange L).toAffine.Equation u v)
    (hu : Transcendental F u) : (E'.baseChange L).toAffine.Point :=
  Point.map (liftPoint E h hu) Q
def RespectsAdd (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra F L] [DecidableEq L] (u₁ v₁ u₂ v₂ u₃ v₃ : L)
    (h₁ : (E.baseChange L).toAffine.Nonsingular u₁ v₁)
    (h₂ : (E.baseChange L).toAffine.Nonsingular u₂ v₂)
    (h₃ : (E.baseChange L).toAffine.Nonsingular u₃ v₃)
    (t₁ : Transcendental F u₁) (t₂ : Transcendental F u₂) (t₃ : Transcendental F u₃),
    Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂ = Point.some u₃ v₃ h₃ →
      ratMapValue E E' Q h₃.1 t₃ = ratMapValue E E' Q h₁.1 t₁ + ratMapValue E E' Q h₂.1 t₂
def IsIsogeny (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) : Prop :=
  (∃ (x y : E.toAffine.FunctionField)
    (h : (E'.baseChange E.toAffine.FunctionField).toAffine.Nonsingular x y),
      Q = .some x y h ∧ Transcendental F x) ∧ RespectsAdd E E' Q
def Isogeny : Type u :=
  {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point // IsIsogeny E E' Q}
namespace Isogeny
variable {E E'} (φ : Isogeny E E')
noncomputable def x : E.toAffine.FunctionField := xOf _ φ.1
noncomputable def y : E.toAffine.FunctionField := yOf _ φ.1
omit [E.IsElliptic] [E'.IsElliptic] in
theorem nonsingular : (E'.baseChange E.toAffine.FunctionField).toAffine.Nonsingular φ.x φ.y := by
  obtain ⟨⟨x, y, h, he, -⟩, -⟩ := φ.2
  simp only [Isogeny.x, Isogeny.y, he]
  exact h
omit [E.IsElliptic] [E'.IsElliptic] in
theorem transcendental_alt : Transcendental F φ.x := by
  obtain ⟨⟨x, y, h, he, ht⟩, -⟩ := φ.2
  simp only [Isogeny.x, he]
  exact ht
noncomputable def comap : E'.toAffine.FunctionField →ₐ[F] E.toAffine.FunctionField :=
  liftPoint E' φ.nonsingular.1 φ.transcendental_alt
noncomputable def degree : ℕ :=
  Module.finrank φ.comap.fieldRange E.toAffine.FunctionField
def IsSeparable : Prop :=
  Algebra.IsSeparable φ.comap.fieldRange E.toAffine.FunctionField
end Isogeny
end Defs
section Mul
variable (E : WeierstrassCurve F) [E.IsElliptic]
noncomputable def ratEmb : RatFunc F →ₐ[F] E.toAffine.FunctionField :=
  RatFunc.liftAlgHom (aeval (genX E)) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (transcendental_iff_injective.mp (transcendental_genX E)))
omit [E.IsElliptic] in
theorem ratEmb_injective : Function.Injective (ratEmb E) :=
  RatFunc.liftAlgHom_injective _ (transcendental_iff_injective.mp (transcendental_genX E))
omit [E.IsElliptic] in
theorem ratEmb_div (p q : F[X]) :
    ratEmb E (algebraMap _ _ p / algebraMap _ _ q) = aeval (genX E) p / aeval (genX E) q :=
  RatFunc.liftAlgHom_apply_div _ _ p q
theorem aeval_genX_ΨSq_ne_zero {n : ℤ} (hn : n ≠ 0) : aeval (genX E) (E.ΨSq n) ≠ 0 := by
  rw [ne_eq, aeval_genX_eq_zero_iff]
  exact ΨSq_ne_zero_of_ne_zero E hn
omit [E.IsElliptic] in
theorem baseChange_eval (p : F[X]) :
    (p.map (algebraMap F E.toAffine.FunctionField)).eval (genX E) = aeval (genX E) p :=
  eval_map_algebraMap _ _
theorem genericPoint_eq :
    genericPoint E = .some (genX E) (genY E) (equation_iff_nonsingular.mp (equation_gen E)) :=
  rfl
theorem zsmul_genericPoint_ne_zero {n : ℤ} (hn : n ≠ 0) : n • genericPoint E ≠ 0 := by
  rw [genericPoint_eq, ne_eq, zsmul_eq_zero_iff]
  show ¬((E.map (algebraMap F E.toAffine.FunctionField)).ΨSq n).eval (genX E) = 0
  rw [map_ΨSq, baseChange_eval]
  exact aeval_genX_ΨSq_ne_zero E hn
theorem xOf_zsmul_genericPoint {n : ℤ} (hn : n ≠ 0) :
    xOf _ (n • genericPoint E) = aeval (genX E) (E.Φ n) / aeval (genX E) (E.ΨSq n) := by
  rw [genericPoint_eq, xOf_zsmul]
  · show ((E.map (algebraMap F E.toAffine.FunctionField)).Φ n).eval (genX E) /
      ((E.map (algebraMap F E.toAffine.FunctionField)).ΨSq n).eval (genX E) = _
    rw [map_Φ, map_ΨSq, baseChange_eval, baseChange_eval]
  · show ((E.map (algebraMap F E.toAffine.FunctionField)).ΨSq n).eval (genX E) ≠ 0
    rw [map_ΨSq, baseChange_eval]
    exact aeval_genX_ΨSq_ne_zero E hn
noncomputable def ratΦΨ (n : ℤ) : RatFunc F :=
  algebraMap _ _ (E.Φ n) / algebraMap _ _ (E.ΨSq n)
omit [E.IsElliptic] in
theorem ratEmb_ratΦΨ (n : ℤ) :
    ratEmb E (ratΦΨ E n) = aeval (genX E) (E.Φ n) / aeval (genX E) (E.ΨSq n) :=
  ratEmb_div E _ _
theorem max_natDegree_ratΦΨ {n : ℤ} (hn : n ≠ 0) :
    max (ratΦΨ E n).num.natDegree (ratΦΨ E n).denom.natDegree = n.natAbs ^ 2 := by
  have hΨ0 : E.ΨSq n ≠ 0 := ΨSq_ne_zero_of_ne_zero E hn
  have hN : 0 < n.natAbs ^ 2 := by have := Int.natAbs_pos.mpr hn; positivity
  have hΦdeg := natDegree_Φ E n
  have hΦ0 : E.Φ n ≠ 0 := fun h => by rw [h, natDegree_zero] at hΦdeg; omega
  have hnum_dvd : (ratΦΨ E n).num ∣ E.Φ n := RatFunc.num_div_dvd _ hΨ0
  have hden_dvd : (ratΦΨ E n).denom ∣ E.ΨSq n := RatFunc.denom_div_dvd _ _
  have hrf0 : ratΦΨ E n ≠ 0 := div_ne_zero
    ((map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr hΦ0)
    ((map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr hΨ0)
  have hnum0 : (ratΦΨ E n).num ≠ 0 := by rwa [ne_eq, RatFunc.num_eq_zero_iff]
  have hcross : (ratΦΨ E n).num * E.ΨSq n = E.Φ n * (ratΦΨ E n).denom := by
    have h1 := RatFunc.num_div_denom (ratΦΨ E n)
    conv_rhs at h1 => rw [ratΦΨ]
    have hb : algebraMap F[X] (RatFunc F) (ratΦΨ E n).denom ≠ 0 :=
      RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _)
    have hd : algebraMap F[X] (RatFunc F) (E.ΨSq n) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr hΨ0
    rw [div_eq_div_iff hb hd, ← map_mul, ← map_mul] at h1
    exact IsFractionRing.injective F[X] (RatFunc F) h1
  have hΦ_dvd : E.Φ n ∣ (ratΦΨ E n).num :=
    (isCoprime_Φ_ΨSq E n).dvd_of_dvd_mul_right ⟨_, hcross⟩
  have hnum : (ratΦΨ E n).num.natDegree = n.natAbs ^ 2 :=
    le_antisymm (hΦdeg ▸ natDegree_le_of_dvd hnum_dvd hΦ0)
      (hΦdeg ▸ natDegree_le_of_dvd hΦ_dvd hnum0)
  have hden : (ratΦΨ E n).denom.natDegree ≤ n.natAbs ^ 2 - 1 :=
    (natDegree_le_of_dvd hden_dvd hΨ0).trans (natDegree_ΨSq_le E n)
  rw [hnum]
  exact max_eq_left (hden.trans (Nat.sub_le _ _))
theorem transcendental_ratΦΨ {n : ℤ} (hn : n ≠ 0) : Transcendental F (ratΦΨ E n) := by
  apply RatFunc.transcendental_of_ne_C
  rintro ⟨c, hc⟩
  have h := max_natDegree_ratΦΨ E hn
  rw [hc, RatFunc.num_C, RatFunc.denom_C, natDegree_C, natDegree_one, max_self] at h
  have := Int.natAbs_pos.mpr hn
  have : 0 < n.natAbs ^ 2 := by positivity
  omega
noncomputable def mulIsogeny (n : ℤ) (hn : n ≠ 0) : Isogeny E E :=
  ⟨n • genericPoint E, by
    obtain ⟨h, he⟩ := eq_some_xOf_yOf _ (zsmul_genericPoint_ne_zero E hn)
    refine ⟨⟨_, _, h, he, ?_⟩, ?_⟩
    · rw [xOf_zsmul_genericPoint E hn, ← ratEmb_ratΦΨ]
      intro halg
      exact transcendental_ratΦΨ E hn ((isAlgebraic_algHom_iff _ (ratEmb_injective E)).mp halg)
    · intro L _ _ _ u₁ v₁ u₂ v₂ u₃ v₃ h₁ h₂ h₃ t₁ t₂ t₃ hadd
      simp only [ratMapValue, map_zsmul]
      rw [map_liftPoint_genericPoint E h₁ t₁, map_liftPoint_genericPoint E h₂ t₂,
        map_liftPoint_genericPoint E h₃ t₃, ← hadd, zsmul_add]⟩
end Mul
section Degree
variable (E : WeierstrassCurve F) [E.IsElliptic]
end Degree
section Separable
variable (E : WeierstrassCurve F) [E.IsElliptic]
end Separable
end GroundTheory.Arith.Abelian


