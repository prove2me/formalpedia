-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_DetectingSequence
-- name    : OAI_Analysis_LipschitzEquivalence_DetectingSequence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:14:19.81453+00:00
-- url     : https://prove2.me/theorems/881346ea-b261-4ad4-8a1c-2609214327d8
-- title:
--   Prefixes of the detecting construction
-- statement:
--   A construction prefix of length $n$ records the first $n$ steps of an inductive construction of smooth test functions on a Hilbert space $H$, relative to a set $K$, a set $Q$, constants $C,\rho,\alpha$, a sequence $\mu$ in $\mathcal F(H)$ and tolerances $\varepsilon_i,\eta_i$. It consists of smooth functions $z_i,w_i$ and row items $a_i$ such that, for $i<n$:
--   - $z_i$ is $1$-Lipschitz with $z_i(0)=w_i(0)=0$, and $\langle a_i,z_i\rangle\ge\alpha$;
--   - earlier functions have small gradient mass on later molecules: $\mathrm{mass}_{a_i}(z_j)\le\eta_j$ for $j<i$;
--   - $w_i$ is a damped copy of $z_i$ on $Q$:
--   $$
--   \Bigl\|\nabla w_i(x)-\prod_{j<i}\bigl(1-\|\nabla z_j(x)\|\bigr)\nabla z_i(x)\Bigr\|\le\varepsilon_i\quad(x\in Q).
--   $$
--   Moreover, the triangular rows whose molecules satisfy all the mass constraints remain rich.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/DetectingSequence.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/DetectingSequence.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothCalculus
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_EnergyEstimates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BlockSelection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothMultiplier

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

structure ConstructionPrefix (K Q : Set H) (C ρ α : ℝ) (μ : ℕ → Space H)
    (ε η : ℕ → ℝ) (n : ℕ) where
  z : ℕ → Smooth H
  w : ℕ → Smooth H
  a : ℕ → RowItem K C ρ μ
  lip : ∀ i < n, LipschitzWith 1 (z i).val
  zero : ∀ i < n, (z i).val 0 = 0 ∧ (w i).val 0 = 0
  high : ∀ i < n, α ≤ smoothPair (a i).a (z i)
  mass : ∀ i j, j < i → i < n → gradMass (a i).a (z j) ≤ η j
  error : ∀ i < n, ∀ x ∈ Q,
    ‖Smooth.grad x (w i)-damping (Finset.range i) z x • Smooth.grad x (z i)‖ ≤ ε i
  rich : ((triangularRows K C ρ α μ).restrict
    (fun b => ∀ i < n, gradMass b.a (z i) ≤ η i)).Rich

namespace ConstructionPrefix
variable {K Q : Set H} {C ρ α : ℝ} {μ : ℕ → Space H} {ε η : ℕ → ℝ}

end ConstructionPrefix

end LipschitzCounterexample.CompactWSC
end

end OAI


