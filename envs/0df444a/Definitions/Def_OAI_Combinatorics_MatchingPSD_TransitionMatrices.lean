-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
-- name    : OAI_Combinatorics_MatchingPSD_TransitionMatrices
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:28:02.517021+00:00
-- url     : https://prove2.me/theorems/e02fb959-1735-4c3b-a2c6-58eaa9207b1d
-- title:
--   Tensor powers of a color matrix, pair diagonals and pair weights of colorings
-- statement:
--   Let $V$ and $H$ be finite sets and let $C$ be a set of colors. Colorings $f : H \times \{0,1\} \to C$ are colorings of the paired vertex set, in which the pair indexed by $i \in H$ is $\{(i,0), (i,1)\}$. The module defines:
--
--   1. For a matrix $U \in \mathbb{R}^{C \times C}$, the **tensor kernel** of $U$ over $V$, the matrix indexed by pairs of colorings $f, g : V \to C$,
--   $$
--   U^{\otimes V}(f, g) = \prod_{v \in V} U\bigl(f(v), g(v)\bigr),
--   $$
--   i.e. the $|V|$-fold Kronecker (tensor) power of $U$, acting on functions of colorings $V \to C$;
--   2. the **pair diagonal** of a vector $d : C \to \mathbb{R}$, a weight on colorings of the paired vertex set,
--   $$
--   \Delta_d(f) = \begin{cases} \prod_{i \in H} d\bigl(f(i,0)\bigr) & \text{if } f(i,0) = f(i,1) \text{ for all } i \in H,\\ 0 & \text{otherwise,}\end{cases}
--   $$
--   colorings with $f(i,0) = f(i,1)$ for all $i$ being called pair-constant;
--   3. the **pair weight** of a matrix $A \in \mathbb{R}^{C \times C}$,
--   $$
--   w_A(f) = \prod_{i \in H} A\bigl(f(i,0), f(i,1)\bigr).
--   $$
--
--   For finite $C$ these are related by $U^{\otimes (H \times \{0,1\})} \Delta_d = w_{U \operatorname{diag}(d) U^{\mathsf T}}$. When $U$ is orthogonal so is its tensor power, and if moreover $|d(c)| \le 1$ for all $c$, then for every permutation $\sigma$ of $H \times \{0,1\}$ the correlation $\sum_f w_A(f)\, w_A(f \circ \sigma)$ with $A = U \operatorname{diag}(d) U^{\mathsf T}$ is at most the number of colorings $f$ such that both $f$ and $f \circ \sigma$ are pair-constant. This is the spectral input for second-moment bounds on color tables of perfect matchings.
--
--   **Formalization Note** The definitions are `tensorKernel U`, a `Matrix (V → C) (V → C) ℝ`, and `pairDiagonal d f`, `pairWeight A f` for colorings `f : H × Bool → C`; the case split in `pairDiagonal` is on the predicate `pairConstant f` and uses decidable equality of colors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TransitionMatrices.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TransitionMatrices.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix

variable {V : Type u_1} {C : Type u_2} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

noncomputable def tensorKernel (U : Matrix C C ℝ) : Matrix (V → C) (V → C) ℝ :=
  fun f g => ∏ v, U (f v) (g v)

variable {H : Type u_3} [Fintype H] [DecidableEq H]

noncomputable def pairDiagonal (d : C → ℝ) (f : H × Bool → C) : ℝ :=
  if pairConstant f then ∏ i, d (f (i, false)) else 0

noncomputable def pairWeight (A : Matrix C C ℝ) (f : H × Bool → C) : ℝ :=
  ∏ i, A (f (i, false)) (f (i, true))

end MatchingSmoothing

end OAI


