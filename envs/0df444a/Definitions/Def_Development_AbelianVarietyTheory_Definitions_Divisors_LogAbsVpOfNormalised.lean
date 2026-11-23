-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:42.453922+00:00
-- url     : https://prove2.me/theorems/4f446157-2e0b-4608-a051-2c67233b8cab
-- title:
--   Log Abs Vp Of Normalised
-- statement:
--   Definitions and structural lemmas for Log Abs Vp Of Normalised, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
namespace GlobalTheory.HTLat
section Eigen
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Λ : Type} [CommRing Λ] (ρ : Λ →+* Module.End C V)
def eigSubLat (χ : Λ →+* C) (X : Submodule O V) : Submodule O V :=
  X ⊓ (eigenSub ρ χ).restrictScalars O
variable {ι : Type} [DecidableEq ι] {σ : ι → Λ →+* C} (h : IsSplitting σ)
def eigQuotLat (i : ι) (X : Submodule O V) : Submodule O V :=
  X.map ((proj h ρ i).restrictScalars O)
end Eigen
section Embeddings
variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
def embO (φ : E →+* C) : 𝓞 E →+* O :=
  let e : O ≃+* (algebraMap O C).range := RingEquiv.ofBijective (algebraMap O C).rangeRestrict
    ⟨fun _ _ hab => hv.hom_inj (congrArg Subtype.val hab), (algebraMap O C).rangeRestrict_surjective⟩
  e.symm.toRingHom.comp ((φ.comp (algebraMap (𝓞 E) E)).codRestrict _ fun a =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1
      ((map_isIntegral_int φ (NumberField.RingOfIntegers.isIntegral_coe a)).tower_top)))
end Embeddings
section Graded
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]
def grLat (La : Submodule O U) (F' F : Submodule C U) : Submodule O (U ⧸ F') :=
  (La ⊓ F.restrictScalars O).map (F'.mkQ.restrictScalars O)
def scaleLat (a : C) (La : Submodule O U) : Submodule O U :=
  La.map ((a • LinearMap.id : U →ₗ[C] U).restrictScalars O)
variable (v : Valuation C ℝ≥0)
def latNorm (La : Submodule O U) (x : U) : ℝ≥0 := sInf {r | ∃ a : C, x ∈ scaleLat a La ∧ v a = r}
variable {v}
theorem latNorm_span_singleton (hv : v.Integers O) {g : U} (hg : g ≠ 0) (c : C) :
    latNorm v (Submodule.span O {g}) (c • g) = v c := by
  refine IsLeast.csInf_eq ⟨⟨c, ⟨g, Submodule.mem_span_singleton_self g, rfl⟩, rfl⟩, ?_⟩
  rintro _ ⟨a, ⟨y, hy, hay⟩, rfl⟩
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have h1 : (a * algebraMap O C b) • g = c • g := by
    rw [mul_smul, algebraMap_smul]; exact hay
  rw [← smul_left_injective C hg h1, map_mul]
  exact mul_le_of_le_one_right' (hv.map_le_one b)
end Graded
section Frames
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
variable (C) in

def step (f : Fin N → U) (i : ℕ) : Submodule C U := Submodule.span C (f '' {k | (k : ℕ) < i})
variable (C) in

def grAt (La : Submodule O U) (f : Fin N → U) (i : Fin N) : Submodule O (U ⧸ step C f i) :=
  grLat La (step C f i) (step C f (i + 1))
def grNorm (v : Valuation C ℝ≥0) (La : Submodule O U) (f : Fin N → U) (i : Fin N) : ℝ≥0 :=
  latNorm v (grAt C La f i) ((step C f i).mkQ (f i))
structure AdaptedFrame (W U₁ : Submodule C U) (N j : ℕ) where

  f : Fin N → U
  indep : LinearIndependent C f
  le : j ≤ N
  step_j : step C f j = W
  step_N : step C f N = U₁
def stdFrame (C : Type) [Field C] (N j : ℕ) (hj : j ≤ N) :
    AdaptedFrame (step C (Pi.basisFun C (Fin N)) j) ⊤ N j where
  f := Pi.basisFun C (Fin N)
  indep := (Pi.basisFun C (Fin N)).linearIndependent
  le := hj
  step_j := rfl
  step_N := by
    have : {k : Fin N | (k : ℕ) < N} = Set.univ := Set.eq_univ_of_forall fun k => k.2
    rw [step, this, Set.image_univ, Module.Basis.span_eq]
def logAbs_vp (p : ℕ) (v : Valuation C ℝ≥0) (r : ℝ≥0) : ℝ :=
  -(Real.log p * (Real.log r / Real.log (v (p : C))))
theorem logAbs_vp_self (p : ℕ) (v : Valuation C ℝ≥0) (h0 : v (p : C) ≠ 0) (h1 : v (p : C) < 1) :
    logAbs_vp p v (v (p : C)) = -Real.log p := by
  have : Real.log (v (p : C)) ≠ 0 :=
    (Real.log_neg (NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)) (by exact_mod_cast h1)).ne
  rw [logAbs_vp, div_self this, mul_one]
variable {U' : Type} [AddCommGroup U'] [Module C U'] [Module O U'] [IsScalarTower O C U']
def phiAt_vp (p : ℕ) (v : Valuation C ℝ≥0) (al : U →ₗ[C] U') (LW : Submodule O U)
    (Lom : Submodule O U') (f : Fin N → U) (j : ℕ) (lam : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, lam i * logAbs_vp p v
    (if (i : ℕ) < j then grNorm v LW f i else grNorm v Lom (al ∘ f) i)
example (p : ℕ) (v : Valuation C ℝ≥0) (hv : v.Integers O) (h0 : v (p : C) ≠ 0) (h1 : v (p : C) < 1)
    (x : U) (hx : x ≠ 0) :
    1 * logAbs_vp p v (latNorm v (Submodule.span O {(p : C)⁻¹ • x}) x) = -Real.log p := by
  have hp : (p : C) ≠ 0 := fun h => h0 (by rw [h, map_zero])
  have h2 := latNorm_span_singleton hv (smul_ne_zero (inv_ne_zero hp) hx) (p : C)
  rw [smul_smul, mul_inv_cancel₀ hp, one_smul] at h2
  rw [h2, one_mul, logAbs_vp_self p v h0 h1]
end Frames
end GlobalTheory.HTLat


