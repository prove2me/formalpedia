-- Prove2me | Definitions.Def_SmoothedMIS_ERDiamBound
-- name    : SmoothedMIS_ERDiamBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:33.007198+00:00
-- url     : https://prove2.me/theorems/a9011230-8a77-438f-befc-d69e91106b66
-- title:
--   The diameter bound of Lemma 2.2 for a constant $c'$
-- statement:
--   For an integer $N\ge1$ and $q\in[0,1]$, $G(N,q)$ is the random graph on $N$ vertices in which every pair is an edge independently with probability $q$. For a constant $c'$, the property $\mathrm{ERDiam}(c')$ says: for every integer $N\ge1$ and every $0<q\le 1/2$ with $\nu=Nq\ge c'(\ln N+1)$, a graph $X\sim G(N,q)$ satisfies
--   $$
--   \mathbb P\big[\operatorname{diam}(X)>2r+1\big]\le 3e^{-\nu/c'},\qquad r=\left\lceil\frac{\ln N}{\ln(\nu/8)}\right\rceil+1 .
--   $$
--   Here $\operatorname{diam}(X)=\infty$ when $X$ is disconnected.
--
--   Lemma 2.2 asserts that $\mathrm{ERDiam}(c')$ holds for some absolute constant $c'\ge1$, and Lemma 3.1 is stated in terms of that constant.
--
--   **Formalization Note** The diameter is `SimpleGraph.ediam` (never the junk value $0$ of `SimpleGraph.diam` on disconnected graphs). At the single value $\nu=8$, where the printed $r$ divides by $\ln 1=0$, Lean's convention gives $r=1$; this value cannot occur when $c'\ge 8$, in particular for the paper's $c'=1024$.
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Lemma 2.2, p.10 (PDF p.12); App. A, pp.42–44 (PDF pp.44–46)

import Mathlib
import Definitions.Def_SmoothedMIS_coinLaw

open MeasureTheory

namespace SmoothedMIS

/-- The Erdős–Rényi graph on `Fin N` whose edges are the pairs with coin `true`; under
`coinLaw (Sym2 (Fin N)) q` it is distributed as `G(N, q)` (§2, p.10). Diagonal pairs are
ignored. -/
def erGraph {N : ℕ} (ω : Sym2 (Fin N) → Bool) : SimpleGraph (Fin N) :=
  SimpleGraph.fromEdgeSet {e | ω e = true}

/-- `diamExceeds X m` is the event `diam(X) > m` for an integer `m`, with `diam = ∞` when `X` is
disconnected (`SimpleGraph.ediam`). A diameter is at least `0`, so the event always holds for
`m < 0`. -/
def diamExceeds {V : Type} (X : SimpleGraph V) (m : ℤ) : Prop :=
  m < 0 ∨ ((m.toNat : ℕ∞) < X.ediam)

/-- The radius `r = ⌈ln N / ln(ν/8)⌉ + 1` of Lemma 2.2 (an integer). -/
noncomputable def erRadius (N : ℕ) (ν : ℝ) : ℤ :=
  ⌈Real.log N / Real.log (ν / 8)⌉ + 1

/-- **The diameter bound of Lemma 2.2 for a given constant `c'`** (Dey, Dufoulon, Moses Jr.,
Pandurangan, *Smoothed Analysis for Distributed MIS* (manuscript, sha256 dc2131db…), Lemma 2.2,
p.10): for every integer `N ≥ 1` and every `0 < q ≤ 1/2` with `ν = Nq ≥ c'(ln N + 1)`,
`X ∼ G(N, q)` satisfies `P[diam(X) > 2r + 1] ≤ 3e^{−ν/c'}`, `r = ⌈ln N/ln(ν/8)⌉ + 1`.

**Formalization Note** `diam` is `SimpleGraph.ediam` (`∞` on a disconnected graph); never the
junk-`0` `SimpleGraph.diam`. `ln` is `Real.log`. At the single value `ν = 8`, where the printed
`r` divides by `ln 1 = 0`, Lean's convention gives `r = 1`; for `c' ≥ 8` (in particular the
paper's `c' = 1024`, App. A) this value cannot occur. -/
def ERDiamBound (c' : ℝ) : Prop :=
  ∀ (N : ℕ) (q : ℝ), 1 ≤ N → 0 < q → q ≤ 1 / 2 → c' * (Real.log N + 1) ≤ N * q →
    ((coinLaw (Sym2 (Fin N)) q)
      {ω | diamExceeds (erGraph ω) (2 * erRadius N (N * q) + 1)}).toReal
      ≤ 3 * Real.exp (-(N * q) / c')

end SmoothedMIS


