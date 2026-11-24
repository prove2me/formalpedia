-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:14.666042+00:00
-- url     : https://prove2.me/theorems/b9bd1129-6eec-40b8-9cf0-937fc89d84ff
-- title:
--   KSum Apply
-- statement:
--   Definitions and structural lemmas for KSum Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KSumApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Fin Function
namespace PositivityTheory.Rg.Cz
section
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]
def kLop (T : P →ₗ[ℝ] Module.End ℂ M) : P →ₗ[ℝ] M →ₗ[ℝ] M where
  toFun X := (T X).restrictScalars ℝ
  map_add' X Y := by ext v; simp
  map_smul' c X := by ext v; simp
def kPre (T : P →ₗ[ℝ] Module.End ℂ M) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M) :
    P →ₗ[ℝ] P [⋀^Fin m]→ₗ[ℝ] M where
  toFun X := (kLop T X).compAlternatingMap η
  map_add' X Y := by ext v; simp
  map_smul' c X := by ext v; simp
def kD (T : P →ₗ[ℝ] Module.End ℂ M) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M) :
    P [⋀^Fin (m + 1)]→ₗ[ℝ] M :=
  AlternatingMap.alternatizeUncurryFin (kPre T η)
def kDel (T : P →ₗ[ℝ] Module.End ℂ M) {β : Type} [Fintype β] (b : β → P) {n : ℕ}
    (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) : P [⋀^Fin n]→ₗ[ℝ] M :=
  ∑ i, (kLop T (b i)).compAlternatingMap (θ.curryLeft (b i))
def kIp (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) {β : Type} [Fintype β] (b : β → P) {m : ℕ}
    (η θ : P [⋀^Fin m]→ₗ[ℝ] M) : ℂ :=
  ∑ I : Fin m → β, B (η (b ∘ I)) (θ (b ∘ I))
end
end PositivityTheory.Rg.Cz
end


