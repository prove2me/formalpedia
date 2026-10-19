-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
-- name    : OAI_Combinatorics_FiniteCircle_Primes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:47:34.828304+00:00
-- url     : https://prove2.me/theorems/ea654f68-864b-4c56-834a-be3e5386c2f7
-- title:
--   Primes in $(n,2n]$ and the standing table of distinct primes
-- statement:
--   The module introduces a dyadic prime interval and the standing hypothesis on the table of primes used by the binary lower-bound constructions.
--
--   1. **Primes in a dyadic interval.** For $n\in\mathbb{N}$,
--   $$
--   \mathcal{P}(n)=\{\,q\ \text{prime}:\ n<q\le 2n\,\}.
--   $$
--   2. **Standing primes.** Let $h\in\mathbb{N}$ and let $p(l,k)$ be a table of natural numbers indexed by $l,k\in\mathbb{N}$. The table is a standing prime table for $h$ if
--      - for every level $1\le l\le h$ and every index $0\le k<h$, the number $p(l,k)$ is a prime with $h^3<p(l,k)\le 2h^3$;
--      - these $h^2$ primes are pairwise distinct, i.e. $(l,k)\mapsto p(l,k)$ is injective on $\{1,\dots,h\}\times\{0,\dots,h-1\}$;
--      - $p(l,k)=1$ for every other pair $(l,k)$, that is, whenever $l=0$, $l>h$ or $k\ge h$.
--
--   The set $\mathcal{P}(n)$ is used to show, via the central binomial coefficient, that a dyadic interval contains many primes, enough to fill an injective $h\times h$ table with primes from $(h^3,2h^3]$. The standing prime table supplies the pairwise distinct large primes indexing the levels and positions of the finite-circle constructions; setting the unused entries to $1$ keeps every entry positive and the entries of each level pairwise coprime at all levels, so the divisibility and positivity hypotheses of the recursive constructions hold everywhere. Such a table exists for all sufficiently large $h$.
--
--   **Formalization Note** `primeInterval n` is the finset of primes in `Finset.Ioc n (2*n)`. `StandingPrimes h p` is a structure (a proposition) with fields `inside`, `inj` and `outside`; the first two quantify over `l k : Fin h` and use the level `l.val + 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Primes.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Primes.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

def primeInterval (n : ℕ) : Finset ℕ := (Finset.Ioc n (2*n)).filter Nat.Prime

structure StandingPrimes (h : ℕ) (p : ℕ → ℕ → ℕ) : Prop where
  inside : ∀ l k : Fin h, Nat.Prime (p (l.val+1) k) ∧ h^3 < p (l.val+1) k ∧ p (l.val+1) k ≤ 2*h^3
  inj : Function.Injective (fun lk : Fin h × Fin h => p (lk.1.val+1) lk.2)
  outside : ∀ l k, ¬(1 ≤ l ∧ l ≤ h ∧ k < h) → p l k = 1

namespace StandingPrimes
variable {h : ℕ} {p : ℕ → ℕ → ℕ} (hp : StandingPrimes h p)
include hp

end StandingPrimes

end FiniteCircle

end OAI


