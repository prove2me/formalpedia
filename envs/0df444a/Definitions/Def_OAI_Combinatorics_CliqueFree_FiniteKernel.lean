-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
-- name    : OAI_Combinatorics_CliqueFree_FiniteKernel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:01:16.852648+00:00
-- url     : https://prove2.me/theorems/adbd3e14-627c-4ccd-bcf0-59ed909477c3
-- title:
--   Finite Markov kernels: stochasticity, stationarity, reversibility, lazy smoothing and average row entropy
-- statement:
--   Let $I$ be a finite state space. A kernel is a real $I\times I$ matrix $P=(P_{ij})$ with rows $P_{i\cdot}=(P_{ij})_{j\in I}$; products of kernels are matrix products. For vectors $\pi,w\in\mathbb{R}^I$ the file defines the following.
--
--   1. **Stochastic:** every row $P_{i\cdot}$ is a probability vector, i.e. $P_{ij}\ge 0$ and $\sum_{j}P_{ij}=1$.
--
--   2. **Stationary:** $\pi$ is stationary for $P$ if $\sum_{i\in I}\pi_iP_{ij}=\pi_j$ for every $j$, i.e. $\pi P=\pi$.
--
--   3. **Reversible** (detailed balance): $\pi_iP_{ij}=\pi_jP_{ji}$ for all $i,j$.
--
--   4. **Lazy kernel** $\mathrm{lazy}(P)=\tfrac12(\mathrm{Id}+P)$.
--
--   5. **Smoothed kernels** $P^{(j)}=P\,\bigl(\tfrac12(\mathrm{Id}+P)\bigr)^{j}$ for $j\in\mathbb{N}$; in particular $P^{(0)}=P$.
--
--   6. **Average row entropy** of a kernel $K$:
--
--      $$\overline{H}_{\pi,w}(K)=\sum_{i\in I}\pi_i\,H_w(K_{i\cdot}),\qquad H_w(p)=\sum_{j\in I}p_j\log\frac{w_j}{p_j},$$
--
--      where terms with $p_j=0$ vanish and $\log$ is the natural logarithm.
--
--   7. **Label preservation:** for a labelling $\ell:I\to J$ into any type $J$, $P$ preserves $\ell$ if $P_{ij}=0$ whenever $\ell(i)\ne\ell(j)$, so $P$ is block diagonal with respect to the classes of $\ell$.
--
--   8. **Row mass** $K_i(A)=\sum_{j\in A}K_{ij}$ for $i\in I$ and $A\subseteq I$.
--
--   These are the Markov-chain notions used for a random walk inside the neighbourhoods of a weighted graph. Lazy smoothing averages the rows of $P$, and an entropy-telescoping argument over $j$ finds a smoothing index at which the rows of $P^{(j)}$ at the two ends of a typical step are close in total variation, provided the total increase of $\overline{H}_{\pi,w}$ is bounded. Row masses of complements measure leakage of the walk out of a set.
--
--   **Formalization Note** `Kernel I` is `Matrix I I ℝ`; the definitions are `Stochastic`, `Stationary`, `Reversible`, `lazy`, `smoothed P j` (equal to `P * lazy P ^ j`), `avgEntropy π w K`, `Preserves label P` and `rowMass K i A`. A local classical `DecidableEq` instance provides the identity matrix. Entropy terms follow Lean's conventions `Real.log 0 = 0` and division by zero equal to zero.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteKernel.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteKernel.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CliqueFreeLog mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteKernel

open FiniteEntropy
variable {I : Type u} [Fintype I]

abbrev Kernel (I : Type u) := Matrix I I ℝ

local instance instDecidableEq_oAI : DecidableEq I := Classical.decEq I

def Stochastic (P : Kernel I) : Prop := ∀ i, IsProb (P i)
def Stationary (π : I → ℝ) (P : Kernel I) : Prop := ∀ j, ∑ i, π i * P i j = π j
def Reversible (π : I → ℝ) (P : Kernel I) : Prop := ∀ i j, π i * P i j = π j * P j i

noncomputable def lazy (P : Kernel I) : Kernel I := fun i j ↦
  ((if i = j then 1 else 0) + P i j) / 2

noncomputable def smoothed (P : Kernel I) (j : ℕ) : Kernel I := by
  classical
  exact P * lazy P ^ j

def avgEntropy (π w : I → ℝ) (K : Kernel I) : ℝ := ∑ i, π i * entropy w (K i)

variable {J : Type v}

def Preserves (label : I → J) (P : Kernel I) : Prop :=
  ∀ i j, label i ≠ label j → P i j = 0

def rowMass (K : Kernel I) (i : I) (A : Finset I) : ℝ := ∑ j ∈ A, K i j

end FiniteKernel

end CliqueFreeIndependence

end

end OAI


