-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
-- name    : OAI_Combinatorics_FiniteCircle_MaskDescent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:44:56.074446+00:00
-- url     : https://prove2.me/theorems/b2c80ba5-2bae-4917-b421-3da6298f29ec
-- title:
--   Prime support, reset budget and the descent bound for mask costs
-- statement:
--   The module introduces the bookkeeping quantities of the denominator-descent estimate for mask costs.
--
--   1. **Phase support.** Let $G$ be an abelian group and $S$ a finite set of natural numbers. An element $x\in G$ is supported on $S$ if
--   $$
--   \Bigl(\prod_{q\in S}q\Bigr)\cdot x=0,
--   $$
--   that is, the order of $x$ divides the product of the elements of $S$.
--   2. **Reset budget.** For $K,T,n,l\in\mathbb{N}$,
--   $$
--   \rho(K,T,n,l)=\Bigl\lfloor\frac{n+lT+K-2}{K-1}\Bigr\rfloor,
--   $$
--   which for $K\ge2$ equals $\lceil (n+lT)/(K-1)\rceil$.
--   3. **Descent bound.** For $h,K,T,n,l\in\mathbb{N}$,
--   $$
--   \delta_h(K,T,n,l)=\frac{1}{4^{l}\,T^{\,l+\rho(K,T,n,l)}\,h^{4K}}.
--   $$
--   4. **Freshness below a level.** Given a table $p(j,k)$ (levels $j$, indices $k<h$), a set $S$ of natural numbers is fresh below level $l$ if $p(j,k)\notin S$ for every $1\le j\le l$ and every $k<h$.
--
--   These quantities state the descent lemma for the mask costs $c_l$ on $\mathbb{Z}/M$ (the circle cost at level $0$, and at level $l+1$ the minimum over residue patterns $z$ of the average of $c_l$ over the shifted phases): under the standing assumptions on the parameters and on the primes $p(j,k)$, a nonzero phase $x$ supported on a set $S$ of at most $K$ primes, all at most $h^4$ and fresh below level $l$, satisfies $c_l(x)\ge\delta_h(K,T,|S|,l)$. The reset budget counts how often the set of active primes can be renewed as the induction descends through the levels.
--
--   **Formalization Note** The definitions are `PhaseSupported S x` (the multiple is the natural-number scalar multiple), `resetBudget K T n l`, `descentBound h K T n l` (a real number) and `LowerFresh h p l S`. In `resetBudget` the subtraction and division are on natural numbers: the numerator is truncated at $0$, and for $K\le1$ the division by $K-1=0$ makes the budget $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/MaskDescent.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/MaskDescent.lean by skeleton subtraction
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

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

def PhaseSupported {G : Type*} [AddCommGroup G] (S : Finset ℕ) (x : G) : Prop :=
  (∏ q ∈ S, q) • x = 0

def resetBudget (K T n l : ℕ) : ℕ := (n + l*T + K - 2) / (K-1)

noncomputable def descentBound (h K T n l : ℕ) : ℝ :=
  1 / ((4:ℝ)^l * (T:ℝ)^(l+resetBudget K T n l) * (h:ℝ)^(4*K))

def LowerFresh (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) (S : Finset ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ l → ∀ k : Fin h, p j k ∉ S

end FiniteCircle

end OAI


