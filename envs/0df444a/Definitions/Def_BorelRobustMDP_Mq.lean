-- Prove2me | Definitions.Def_BorelRobustMDP_Mq
-- name    : BorelRobustMDP_Mq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:16.433147+00:00
-- url     : https://prove2.me/theorems/045c1a1f-4927-467b-adfd-168b798038f2
-- title:
--   The set $\mathcal M^q(\Omega_n,\mathcal A_n,\mathbb P_n)$ of probability measures with $L^q$ densities
-- statement:
--   For a measure $P$ on the disturbance space and $q\in(1,\infty]$, $\mathcal M^q(P)$ is the set of probability measures $Q$ with $Q\ll P$ and $\frac{dQ}{dP}\in L^q(P)$.
--
--   Ambiguity sets are subsets of this set.
--
--   **Formalization Note.** The exponent lies in $[0,\infty]$, so the essentially bounded case $q=\infty$ is included. The density is the Radon–Nikodym derivative read as a real function.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, §2, p.4

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace BorelRobustMDP

universe v

/-- `𝓜^q(Ω, 𝒜, ℙ)` (Bäuerle & Glauner, arXiv:2007.13103v1, p.4): the probability measures `Q` on
the disturbance space which are absolutely continuous with respect to `P` and whose density
`dQ/dP` lies in `L^q(P)`.

**Formalization Note.** `q : ℝ≥0∞`, so `q = ∞` is the paper's essentially bounded case. The density
is `Q.rnDeriv P` read in `ℝ`; for `Q ≪ P` with `P` finite it is `P`-a.e. finite. -/
def Mq {Z : Type v} [MeasurableSpace Z] (P : Measure Z) (q : ℝ≥0∞) : Set (Measure Z) :=
  {Q | IsProbabilityMeasure Q ∧ Q ≪ P ∧ MemLp (fun z => (Q.rnDeriv P z).toReal) q P}

end BorelRobustMDP


