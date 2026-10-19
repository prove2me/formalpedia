-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
-- name    : OAI_Combinatorics_MatchingPSD_TensorBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:29:44.485258+00:00
-- url     : https://prove2.me/theorems/753e1420-e9b7-4db6-89ca-c90ab18bd128
-- title:
--   Product colorings preserving pair-constancy and the symmetrically normalized pair matrix
-- statement:
--   Let $H$ and $C$ be sets and let $\sigma$ be a permutation of the paired vertex set $H \times \{0,1\}$, in which the pair indexed by $i \in H$ is $\{(i,0),(i,1)\}$. Call a coloring $f : H \times \{0,1\} \to C$ pair-constant if $f(i,0) = f(i,1)$ for all $i \in H$, and write
--
--   $$
--   \mathcal{K}_\sigma(C) = \bigl\{ f : H \times \{0,1\} \to C \;:\; f \text{ and } f \circ \sigma \text{ are both pair-constant} \bigr\}.
--   $$
--
--   The module defines:
--
--   1. The bijection $\mathcal{K}_\sigma(C) \times \mathcal{K}_\sigma(C) \to \mathcal{K}_\sigma(C \times C)$, $(f, g) \mapsto \bigl(v \mapsto (f(v), g(v))\bigr)$, which merges two colorings into one coloring with the product color set; its inverse takes the two coordinate projections. Consequently, for finite $H$ and $C$, $|\mathcal{K}_\sigma(C \times C)| = |\mathcal{K}_\sigma(C)|^2$.
--   2. For a matrix $\gamma \in \mathbb{R}^{C \times C}$ and a weight vector $\pi : C \to \mathbb{R}$, the **normalized pair matrix**
--   $$
--   N_{\gamma,\pi}(i, j) = \frac{\gamma(i, j)}{\sqrt{\pi(i)}\,\sqrt{\pi(j)}} \qquad (i, j \in C).
--   $$
--
--   If $\gamma$ is symmetric and entrywise nonnegative, so is $N_{\gamma,\pi}$; if in addition $C$ is finite, $\pi > 0$ and the row sums of $\gamma$ are $\sum_j \gamma(i,j) = \pi(i)$ (a symmetric joint distribution of two colors with marginal $\pi$), then the vector $(\sqrt{\pi(i)})_{i \in C}$ is fixed by $N_{\gamma,\pi}$, which forces all eigenvalues of $N_{\gamma,\pi}$ into $[-1, 1]$. Both objects enter the bound on the sum over all permutations $\sigma$ of the squared overlaps of pair weights.
--
--   **Formalization Note** The definitions are `commonColoringsProdEquiv σ`, an `Equiv` between subtypes of colorings `H × Bool → C` (respectively `H × Bool → C × C`) cut out by `pairConstant f ∧ pairConstant (f ∘ σ)`, and `normalizedPairMatrix γ π`. Lean's conventions apply to the latter: `Real.sqrt` of a negative number is $0$ and division by $0$ gives $0$, so every entry in a row or column $i$ with $\pi(i) \le 0$ equals $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TensorBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TensorBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix

variable {C : Type u_1} [Fintype C] [DecidableEq C]

end MatchingSmoothing

namespace MatchingSmoothing
open Matrix
variable {H : Type u_2} {C : Type u_3} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

noncomputable def commonColoringsProdEquiv (σ : Equiv.Perm (H × Bool)) :
    ({f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)} ×
      {f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)}) ≃
    {f : H × Bool → C × C // pairConstant f ∧ pairConstant (f ∘ σ)} where
  toFun fg := ⟨fun v => (fg.1.1 v, fg.2.1 v),
    ⟨fun i => Prod.ext (fg.1.2.1 i) (fg.2.2.1 i),
      fun i => Prod.ext (fg.1.2.2 i) (fg.2.2.2 i)⟩⟩
  invFun f := (⟨fun v => (f.1 v).1, ⟨fun i => congrArg Prod.fst (f.2.1 i),
      fun i => congrArg Prod.fst (f.2.2 i)⟩⟩,
    ⟨fun v => (f.1 v).2, ⟨fun i => congrArg Prod.snd (f.2.1 i),
      fun i => congrArg Prod.snd (f.2.2 i)⟩⟩)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def normalizedPairMatrix (γ : Matrix C C ℝ) (π : C → ℝ) : Matrix C C ℝ :=
  fun i j => γ i j / (Real.sqrt (π i) * Real.sqrt (π j))

end MatchingSmoothing

end OAI


