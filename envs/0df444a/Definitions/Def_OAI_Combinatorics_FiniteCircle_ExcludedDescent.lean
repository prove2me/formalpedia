-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
-- name    : OAI_Combinatorics_FiniteCircle_ExcludedDescent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:45:43.698266+00:00
-- url     : https://prove2.me/theorems/466e6a63-e8ce-44e6-b214-17242ea54eea
-- title:
--   Reset budget and descent bound for the excluded construction
-- statement:
--   The module introduces the two parameters of the denominator-descent estimate for the excluded costs.
--
--   1. **Pair reset budget.** For $K,T,n,l\in\mathbb{N}$,
--   $$
--   \rho'(K,T,n,l)=\Bigl\lfloor\frac{n+lT+K-3}{K-2}\Bigr\rfloor,
--   $$
--   which for $K\ge3$ equals $\lceil (n+lT)/(K-2)\rceil$.
--   2. **Pair descent bound.** For $m,K,T,B,n,l\in\mathbb{N}$,
--   $$
--   \delta'_m(K,T,B,n,l)=\frac{1}{4^{l}\,B^{\,l+3\rho'(K,T,n,l)}\,m^{5K}}.
--   $$
--
--   These play for the excluded construction the role that the reset budget $\lceil (n+lT)/(K-1)\rceil$ and the bound $1/(4^lT^{l+\rho}h^{4K})$ play for the mask construction. The excluded costs $e_l$ on $\mathbb{Z}/M$ start from the circle cost and average, at each level, over the $m$ phases $x+\sum_{j\ne i}(M/p(l,j))z_j$, minimized over residue patterns $z$. Under the standing assumptions on the parameters and on the primes $p(l,k)$, the descent lemma bounds $e_l(x)\ge\delta'_m(K,T,B,|S|,l)$ for every nonzero phase $x$ whose order divides the product of a set $S$ of at most $K$ primes, all at most $m^5$, none of which equals a prime $p(j,k)$ with $1\le j\le l$.
--
--   **Formalization Note** The definitions are `pairResetBudget K T n l` and `pairDescentBound m K T B n l`. The subtraction and division in `pairResetBudget` are on natural numbers: the numerator is truncated at $0$, and for $K\le2$ the division by $K-2=0$ makes the budget $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/ExcludedDescent.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/ExcludedDescent.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

def pairResetBudget (K T n l : ℕ) : ℕ := (n+l*T+K-3)/(K-2)

noncomputable def pairDescentBound (m K T B n l : ℕ) : ℝ :=
  1/((4:ℝ)^l*(B:ℝ)^(l+3*pairResetBudget K T n l)*(m:ℝ)^(5*K))

end FiniteCircle

end OAI


