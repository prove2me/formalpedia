-- Prove2me | Definitions.Def_GMRDiversity_expectedHit
-- name    : GMRDiversity_expectedHit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:42:33.700342+00:00
-- url     : https://prove2.me/theorems/a0d3990f-d592-41c1-b109-f2117d213d0c
-- title:
--   Expected number of queries $\mathbb E\tau$ until the target is queried
-- statement:
--   For a live-pool policy $\pi$ on $\mathfrak G^{\mathrm{par}}_x$ with $x\sim\mathrm{Unif}(\{0,1\}^n)$, let $\tau$ be the first round $t$ with $U_x(z_t)=1$ ($\tau=\infty$ if there is none). The **expected hitting time** is
--   $$
--   \mathbb E\tau=\sum_{T\ge0}\mathbb P(\tau>T)=\sum_{T\ge0}\big(1-V^\pi_T\big)\in[0,\infty].
--   $$
--   It is the quantity bounded in the query count of the upper bound and converted into a value bound by Markov's inequality.
--
--   **Formalization Note** The tail-sum formula is the definition, valued in $[0,\infty]$; it avoids building an infinite-horizon probability space.
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 2, 'Truncation', p.12

import Mathlib
import Definitions.Def_GMRDiversity_value

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Expected number of queries until the target is queried**, `E τ` (Brandenberger, Doron-Arad,
Mossel, *Genetic Algorithms with Optimization Guided Operators*, STOC 2027 submission, manuscript
sha256 f89f4f77…, proof of Lemma 2, "Truncation", p.12: "τ is the number of queries until the first
correct guess is synthesized"), with `x` uniform as throughout §6.

**Formalization Note.** `τ` is the first round `t` with `U_x(z_t) = 1` (`+∞` if there is none). By
the tail-sum formula `E τ = ∑_{T ≥ 0} P(τ > T) = ∑_{T ≥ 0} (1 − V^π_T)`, which is the definition used,
valued in `[0, ∞]`; it avoids an infinite-horizon probability space. -/
noncomputable def expectedHit {n w : ℕ} (π : LivePoolPolicy n w) : ENNReal :=
  ∑' T : ℕ, ENNReal.ofReal (1 - value π T)

end GMRDiversity


