-- Prove2me | Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_ExtremeLoads
-- name    : LinearHashingPoissonesque_ExpectedLoads_ExtremeLoads
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T19:02:12.428274+00:00
-- url     : https://prove2.me/theorems/f0151e50-29cf-4c38-9a5d-fe7b26b06d13
-- title:
--   All-bin ordered loads and extreme-bin averages
-- statement:
--   Let $S\subseteq A$ be finite and $f:A\to B$, with $B$ a finite set of $n$ bins. Sort the multiset of all $n$ bin loads increasingly as $L^{(1)},\ldots,L^{(n)}$. For $1\le r\le n$, define
--
--   $$L_r^-(S,f)=\frac1r\sum_{j=1}^rL^{(j)},\qquad L_r^+(S,f)=\frac1r\sum_{j=n-r+1}^nL^{(j)}.$$
--
--   The sign $\star\in\{-,+\}$ selects the corresponding average $L_r^\star$. Every bin, including every empty bin, occurs once in the multiset; equal loads retain their multiplicity. These are averages of $r$ loads, rather than single order statistics.
--
--   **Formalization Note** An increasing list and its reverse supply the first $r$ entries for the two signs. All division is real. At the unused input $r=0$ the totalized definitions return zero; the mission theorems require $1\le r\le n$.
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.8, Section 2, Load Statistics; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_BinLoad

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Section 2, p.8: every bin load in increasing order, with multiplicities. -/
noncomputable def sortedLoads {A B : Type*} [Fintype B] (S : Finset A) (f : A → B) : List ℕ :=
  (Finset.univ.val.map (binLoad S f)).sort (· ≤ ·)

/-- Average of the r lightest bins (real division). Totalized by 0 at r = 0. -/
noncomputable def lightestAverage {A B : Type*} [Fintype B]
    (S : Finset A) (f : A → B) (r : ℕ) : ℝ :=
  (((sortedLoads S f).take r).sum : ℝ) / (r : ℝ)

/-- Average of the r heaviest bins. The entire sorted list includes all empty bins. -/
noncomputable def heaviestAverage {A B : Type*} [Fintype B]
    (S : Finset A) (f : A → B) (r : ℕ) : ℝ :=
  (((sortedLoads S f).reverse.take r).sum : ℝ) / (r : ℝ)

/-- The source's two choices ⋆ ∈ {+, −}. -/
inductive Extreme where
  | lightest
  | heaviest
  deriving DecidableEq

noncomputable def extremeAverage {A B : Type*} [Fintype B]
    (S : Finset A) (f : A → B) (r : ℕ) (sign : Extreme) : ℝ :=
  match sign with
  | .lightest => lightestAverage S f r
  | .heaviest => heaviestAverage S f r

end LinearHashingPoissonesque.ExpectedLoads


