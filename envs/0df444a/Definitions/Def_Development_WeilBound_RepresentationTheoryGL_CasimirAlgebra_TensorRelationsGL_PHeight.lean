-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:54.511937+00:00
-- url     : https://prove2.me/theorems/01baef00-19ed-4329-b670-9f5c2409a78e
-- title:
--   PHeight
-- statement:
--   Definitions and structural lemmas for PHeight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean

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
namespace PositivityTheory.Rg.Cz
namespace HeightVanishing
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
def ht (w : List (Fin n × Fin n)) : ℤ := (w.map fun x => ((x.2 : ℕ) : ℤ) - ((x.1 : ℕ) : ℤ)).sum
def word (E : Fin n → Fin n → Module.End ℂ M) (w : List (Fin n × Fin n)) : Module.End ℂ M :=
  (w.map fun x => E x.1 x.2).prod
def W (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (h : ℤ) : Submodule ℂ (Module.End ℂ M) :=
  Submodule.span ℂ {A | ∃ w, w.length ≤ k ∧ ht w = h ∧ word E w = A}
variable (E : Fin n → Fin n → Module.End ℂ M)
section wh
variable {ℓ : M →ₗ[ℂ] ℂ} {ψ : Fin n → Fin n → ℂ} (hE : GlRel E)
  (hψ2 : ∀ a b : Fin n, (a : ℕ) + 1 < b → ψ a b = 0) (hψ : ∀ a b : Fin n, a < b → ℓ ∘ₗ E a b = ψ a b • ℓ)
include hE hψ2 hψ
end wh
section eval
variable {P : Type} [Fintype P] [DecidableEq P]
def H (J I : P → Fin n) : ℤ := ∑ p, (((J p : ℕ) : ℤ) - ((I p : ℕ) : ℤ))
end eval
end HeightVanishing
end PositivityTheory.Rg.Cz
end


