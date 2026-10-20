-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteRows
-- name    : OAI_Analysis_LipschitzEquivalence_FiniteRows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:00:30.40921+00:00
-- url     : https://prove2.me/theorems/55090e72-2a7b-4189-989a-bc6ecda85403
-- title:
--   Hereditary families of finite rows
-- statement:
--   A row family on a set $A$ is a predicate on finite tuples $v:\{0,\dots,n-1\}\to A$ that is hereditary under subsequences: whenever $v$ is accepted and $e$ is an order embedding, $v\circ e$ is accepted.
--
--   1. **Richness.** A row family is rich if it accepts rows of every length $n$:
--   $$
--   \forall n\ \exists v\in A^n,\ v\text{ accepted}.
--   $$
--   2. **Restriction.** Restricting to a predicate $P$ on $A$ keeps the accepted rows all of whose entries satisfy $P$; this is again hereditary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/FiniteRows.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/FiniteRows.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation

namespace OAI

universe uA uB

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped BigOperators

structure RowFamily (A : Type uA) where
  accepts : ∀ {n : ℕ}, (Fin n → A) → Prop
  hereditary : ∀ {m n : ℕ} (e : Fin m ↪o Fin n) (v : Fin n → A),
    accepts v → accepts (v ∘ e)

namespace RowFamily
variable {A : Type uA} {B : Type uB}

def Rich (R : RowFamily A) : Prop := ∀ n, ∃ v : Fin n → A, R.accepts v

def restrict (R : RowFamily A) (P : A → Prop) : RowFamily A where
  accepts v := R.accepts v ∧ ∀ i, P (v i)
  hereditary e v h := ⟨R.hereditary e v h.1,fun i => h.2 (e i)⟩

end RowFamily
end LipschitzCounterexample.CompactWSC
end

end OAI


