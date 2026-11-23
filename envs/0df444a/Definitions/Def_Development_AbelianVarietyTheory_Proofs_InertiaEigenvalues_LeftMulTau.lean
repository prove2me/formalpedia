-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:11.388834+00:00
-- url     : https://prove2.me/theorems/8b72d480-5654-43ac-b50e-79ab8c714c16
-- title:
--   Left Mul Tau
-- statement:
--   Definitions and structural lemmas for Left Mul Tau, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LeftMulTau.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
def bas (hG : A.IsGen τ p) : Module.Basis (Fin r) F A.K :=
  basisOfLinearIndependentOfCardEqFinrank' _ hG.1 (by rw [hG.2.1]; simp)
def pt (hG : A.IsGen τ p) (lam : F) (b c : A.K) : Gl r F :=
  (companion p, (bas A hG).equivFun b, fun i => Algebra.trace F A.K (τ ^ (i : ℕ) * c), lam)
def tm (hG : A.IsGen τ p) : A.Kˣ →* GL (Fin r) F :=
  Units.map (Algebra.leftMulMatrix (bas A hG)).toRingHom.toMonoidHom
def unitsMeas (μK : Measure A.K) : Measure A.Kˣ :=
  (μK.withDensity fun t => ENNReal.ofReal (A.absK t)⁻¹).comap Units.val
def desc (M : Meas r F E)
    (hG : A.IsGen τ p) (lam : F) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ) (x : A.K × A.K) : ℂ :=
  letI := M.mG
  ∫ g, f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) ∂M.μG
end GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
end GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
end GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
end GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
end GlobalTheory.JR.LinDesc


