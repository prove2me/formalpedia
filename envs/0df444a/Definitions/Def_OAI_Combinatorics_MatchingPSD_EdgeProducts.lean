-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
-- name    : OAI_Combinatorics_MatchingPSD_EdgeProducts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:24:11.573497+00:00
-- url     : https://prove2.me/theorems/5279b588-79bf-4000-81ae-6e9510b7e275
-- title:
--   Span of products of at most $d$ coordinate functions
-- statement:
--   Let $E$ and $X$ be arbitrary sets and let $x = (x_e)_{e \in E}$ be a family of real-valued functions $x_e : X \to \mathbb{R}$, thought of as coordinates on $X$. For $d \in \mathbb{N}$, the **low-degree space** $\mathcal{P}_d(x)$ is the real linear subspace of the vector space $\mathbb{R}^X$ of all functions $X \to \mathbb{R}$ spanned by the pointwise products of at most $d$ coordinates:
--
--   $$
--   \mathcal{P}_d(x) = \operatorname{span}_{\mathbb{R}} \bigl\{\, x_{e_1} x_{e_2} \cdots x_{e_m} \;:\; 0 \le m \le d,\ e_1, \dots, e_m \in E \,\bigr\}.
--   $$
--
--   Repetitions among the $e_j$ are allowed, and the empty product ($m = 0$) is the constant function $1$, so $\mathcal{P}_d(x)$ always contains the constants. In other words, $\mathcal{P}_d(x)$ consists of the functions on $X$ that can be written as real polynomials of degree at most $d$ in the coordinates $x_e$.
--
--   This is the notion of degree used for functions on perfect matchings: there $X$ is the set of perfect matchings of a vertex set and $x_e$ is the indicator that the matching contains the edge $e$. The spaces increase with $d$ and are compatible with multiplication, $f \in \mathcal{P}_d(x)$ and $g \in \mathcal{P}_{d'}(x)$ imply $fg \in \mathcal{P}_{d+d'}(x)$, which makes them suitable for degree bookkeeping.
--
--   **Formalization Note** The definition is `lowDegree x d`, the `Submodule.span ℝ` of the set of functions `(l.map x).prod` for lists `l : List E` of length at most `d`. No finiteness of `E` or `X` is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/EdgeProducts.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/EdgeProducts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
variable {E : Type u_1} {X : Type u_2}

def lowDegree (x : E → X → ℝ) (d : ℕ) : Submodule ℝ (X → ℝ) :=
  Submodule.span ℝ {f | ∃ l : List E, l.length ≤ d ∧ f = (l.map x).prod}

end MatchingSmoothing

end OAI


