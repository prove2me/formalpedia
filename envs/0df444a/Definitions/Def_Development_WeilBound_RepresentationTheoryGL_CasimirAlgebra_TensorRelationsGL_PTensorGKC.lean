-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKC
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:38.092915+00:00
-- url     : https://prove2.me/theorems/ed2d64f1-05a8-4bb6-ac80-a32408eda36e
-- title:
--   PTensor GKC
-- statement:
--   Definitions and structural lemmas for PTensor GKC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKC.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
def cLam (lam : TV n M P →ₗ[ℂ] ℂ) (I : P → Fin n) : M →ₗ[ℂ] ℂ :=
  lam ∘ₗ LinearMap.single ℂ (fun _ : P → Fin n => M) I
def cD {ι : Type} [DecidableEq ι] (bar : ι → ι) (τ : ι) (X : Matrix (Fin n) (Fin n) ℂ) (σ : ι) (i j : Fin n) : ℂ :=
  (if σ = τ then X i j else 0) + (if σ = bar τ then star (X i j) else 0)
end PositivityTheory.Rg.Cz.TGK
end


