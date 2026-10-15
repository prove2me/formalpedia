-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Basic
-- name    : OAI_Combinatorics_InfiniteMatroid_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:45:58.859474+00:00
-- url     : https://prove2.me/theorems/8eada96e-ea74-4230-9ef7-9499276741d0
-- title:
--   The doubled ground set $E_0=D\times\{0,1\}$ of Boolean functions
-- statement:
--   Let $D$ be the set of all pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$ a Boolean function of $m$ variables; it is countably infinite, its $m$-th part consisting of the $2^{2^m}$ Boolean functions of arity $m$. This file introduces the doubled set
--   $$E_0=D\times\{0,1\}=\{(d,b):\ d\in D,\ b\in\{0,1\}\},$$
--   in which every $d\in D$ occurs in two copies $(d,0)$ and $(d,1)$.
--
--   $E_0$ is the ground set of the self-dual matroid $Q$ constructed in the counterexample: the block densities, small sets, density classes and probe functionals, and the bases of $Q$, all live on $E_0$. The ground set $E=\mathbb Z\times D$ of the final pair of matroids is obtained by attaching a copy of $E_0$ to every vertex of a double ray, the two copies of $D$ inside $E_0$ going to the two edges at that vertex.
--
--   **Formalization Note** `E0` is the abbreviation `D × Bool`, where `D` is the sigma type `(m : ℕ) × ((Fin m → Bool) → Bool)` of the base definitions, and `false`, `true` stand for $0$, $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroid mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting

namespace OAI

open Set Matroid

namespace InfiniteMatroidCounterexample

abbrev E0 := D × Bool
end InfiniteMatroidCounterexample

end OAI


