-- Prove2me | Definitions.Def_FreeGroupFactorProof25
-- name    : FreeGroupFactorProof25
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T04:32:16.456198+00:00
-- url     : https://prove2.me/theorems/0d026a2c-5600-4e47-b5b5-79851c5026ed
-- title:
--   Free group factors: supporting development, part 25
-- statement:
--   Part 25 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof24

set_option linter.all false

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uA uB uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

end
section

variable {A : Type uA} [CStarAlgebra A]

end

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} [Fintype ι] [DecidableEq ι]

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end

theorem twoNorm_star {G : Type uG} [Group G] (T : groupVonNeumann G) :
    twoNorm (star T) = twoNorm T := by
  classical
  have hsq : (twoNorm (star T) : ℂ)^2 = (twoNorm T : ℂ)^2 := by
    rw [twoNorm_sq, twoNorm_sq, star_star]
    exact canonicalTrace_mul T (star T)
  have hr := congrArg Complex.re hsq
  norm_cast at hr
  nlinarith [norm_nonneg (groupL2 (star T)), norm_nonneg (groupL2 T)]

theorem twoNorm_mul_unitary_right {G : Type uG} [Group G]
    (U : unitary (groupVonNeumann G)) (T : groupVonNeumann G) :
    twoNorm (T*(U : groupVonNeumann G)) = twoNorm T := by
  rw [← twoNorm_star, star_mul]
  change twoNorm (((star U : unitary (groupVonNeumann G)) : groupVonNeumann G) * star T) = _
  rw [twoNorm_mul_unitary_left, twoNorm_star]

theorem twoNorm_iso {G : Type uG} {H : Type uH} [Group G] [Group H]
    (Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H)
    (hΦ : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) (T : groupVonNeumann G) :
    twoNorm (Φ T) = twoNorm T := by
  have hs : Φ (star T) = star (Φ T) := Φ.map_star' T
  have hm : Φ (star T * T) = Φ (star T) * Φ T := Φ.map_mul' (star T) T
  have hsq : (twoNorm (Φ T) : ℂ)^2 = (twoNorm T : ℂ)^2 := by
    rw [twoNorm_sq, twoNorm_sq, ← hs, ← hm, hΦ]
  have hr := congrArg Complex.re hsq
  norm_cast at hr
  nlinarith [norm_nonneg (groupL2 (Φ T)), norm_nonneg (groupL2 T)]

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
open scoped ENNReal

variable {G : Type uG} [Group G]

omit [Group G] in
theorem group_single_total [DecidableEq G] (K : Submodule ℂ (GroupHilbert G))
    (hK : IsClosed (K : Set (GroupHilbert G)))
    (hsingle : ∀ g : G, lp.single 2 g (1 : ℂ) ∈ K) : ⊤ ≤ K := by
  classical
  intro ξ _hξ
  have hs := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ
  apply hK.mem_of_tendsto hs
  filter_upwards [] with s
  apply K.sum_mem
  intro g _hg
  have he : lp.single 2 g (ξ g) = (ξ g) • (lp.single 2 g (1 : ℂ) : GroupHilbert G) := by
    ext x
    simp [lp.single_apply, Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hsingle g)

theorem spatialGroupIso_symm_normal {H : Type uH} [Group H]
    (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (hVN : ∀ T : GroupOperator G,
      T ∈ groupVonNeumann G ↔ e.conjStarAlgEquiv T ∈ groupVonNeumann H) :
    @Continuous _ _ (groupUltraweakTopology H) (groupUltraweakTopology G)
      (spatialGroupIso e hVN).symm := by
  let : TopologicalSpace (GroupOperator G) := ultraweakOperatorTopology G
  let : TopologicalSpace (GroupOperator H) := ultraweakOperatorTopology H
  let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
  let : TopologicalSpace (groupVonNeumann H) := groupUltraweakTopology H
  apply continuous_induced_rng.mpr
  have hinc : Continuous (fun T : groupVonNeumann H => (T : GroupOperator H)) :=
    continuous_induced_dom
  exact (spatial_ultraweak_continuous e.symm).comp hinc

def gaugedRepresentation (e : G ≃* G) (χ : G →* unitary ℂ) : G →* groupVonNeumann G where
  toFun g := (χ g : ℂ) • groupUnitary (e g)
  map_one' := by
    simp only [map_one, Submonoid.coe_one, one_smul]
    exact Subtype.ext leftRegular_one
  map_mul' g h := by
    simp only [map_mul, Submonoid.coe_mul, smul_mul_smul_comm]
    congr 1
    exact Subtype.ext (leftRegular_mul _ _)

@[simp] theorem gaugedRepresentation_apply (e : G ≃* G) (χ : G →* unitary ℂ) (g : G) :
    gaugedRepresentation e χ g = (χ g : ℂ) • groupUnitary (e g) := rfl

theorem gaugedRepresentation_star (e : G ≃* G) (χ : G →* unitary ℂ) (g : G) :
    star (gaugedRepresentation e χ g) = gaugedRepresentation e χ g⁻¹ := by
  simp only [gaugedRepresentation_apply, star_smul, map_inv]
  have hg : star (groupUnitary (e g)) = groupUnitary ((e g)⁻¹) :=
    Subtype.ext (leftRegular_star _)
  rw [hg]
  congr 1

theorem gaugedRepresentation_trace [DecidableEq G] (e : G ≃* G) (χ : G →* unitary ℂ) (g : G) :
    canonicalTrace (gaugedRepresentation e χ g) = if g = 1 then 1 else 0 := by
  classical
  change canonicalTraceLinear ((χ g : ℂ) • groupUnitary (e g)) = _
  rw [map_smul]
  change (χ g : ℂ) • canonicalTrace (groupUnitary (e g)) = _
  rw [canonicalTrace_groupUnitary]
  simp only [e.map_eq_one_iff]
  split_ifs with hg
  · subst g; simp
  · simp

variable {ι : Type uι}

end FreeGroupFactorMain

end

end OAI
end


