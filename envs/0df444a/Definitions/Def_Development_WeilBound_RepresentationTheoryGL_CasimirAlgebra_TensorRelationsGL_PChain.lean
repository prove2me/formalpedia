-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChain
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:40.611065+00:00
-- url     : https://prove2.me/theorems/02f5cf0f-a031-490c-b2be-54a050f3f400
-- title:
--   PChain
-- statement:
--   Definitions and structural lemmas for PChain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChain.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
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
namespace ChainP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
def Good (E : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℂ) (ℓ : M →ₗ[ℂ] ℂ) (top : Fin n) (m : ℕ)
    (co : Fin m → Fin n) (g : Module.End ℂ (TV n M (Fin m))) : Prop :=
  g ∈ Algebra.adjoin ℂ (Set.range fun j : Fin m => xJ E j) ∧
    ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g ≠ 0 ∧
    (∀ j, (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g) ∘ₗ xJ E j =
      (l (co j) + ((Finset.univ.filter fun i => i < j ∧ co i = co j).card : ℂ)) •
        (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g)) ∧
    ∀ u : ℂ, (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g) ∘ₗ qdet (tE (Finset.univ : Finset (Fin m)) E) u =
      (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g)
end ChainP
end PositivityTheory.Rg.Cz
end


