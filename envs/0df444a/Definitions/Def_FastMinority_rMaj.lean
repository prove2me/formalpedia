-- Prove2me | Definitions.Def_FastMinority_rMaj
-- name    : FastMinority_rMaj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:23.291001+00:00
-- url     : https://prove2.me/theorems/168db662-864c-4b4e-b8fb-c2837618318f
-- title:
--   Majority-adoption probability $r(p)=Q(p)+(1-p)^k-p^k$
-- statement:
--   For a sample size $k$ and a minority proportion $0\le p\le 1/2$, let $Q(p)=\Pr[\mathrm{Bin}(k,p)\ge (k+1)/2]$ be the probability that a sample of $k$ agents drawn with replacement contains more minority than majority agents. The **majority-adoption probability** is
--   $$
--   r(p)=Q(p)+(1-p)^k-p^k .
--   $$
--   It is the probability that one agent adopts the current majority opinion in the next round of MINORITY: it adopts the majority if its sample has a minority-majority (probability $Q(p)$, from which the all-minority sample, probability $p^k$, is removed) or if its sample is unanimously majority (probability $(1-p)^k$).
--
--   The quantity drives the minority-size chain: given $X_t=x$, the number $Y$ of agents adopting the current majority is $\mathrm{Bin}(n,r(x/n))$.
--
--   **Formalization Note** $Q$ is the published `MinorityDynamics.qMaj`. For odd $k$, $r(p)=1-p_{\mathrm{adopt}}(p)$, where $p_{\mathrm{adopt}}$ (`MinorityDynamics.pAdopt`) is the minority-adoption probability used by the published chain kernel.
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 2.1, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain

set_option autoImplicit false

open Classical

namespace FastMinority

/-- The **majority-adoption probability** `r(p) = Q(p) + (1 − p)^k − p^k` (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), §2.1,
p.4 = PDF p.6), for a minority proportion `0 ≤ p ≤ 1/2`, where `Q(p) = Pr[Bin(k, p) ≥ (k + 1)/2]`
is the published `MinorityDynamics.qMaj k p`. It is the probability that one agent adopts the
current majority opinion in the next round.

**Formalization Note** `Q` is the published `qMaj`, with `(k + 1)/2` natural-number division
(exact for odd `k`). For odd `k`, `r(p) = 1 − pAdopt k p` (checked in the sanity file for `k = 3`),
where `pAdopt` is the minority-adoption probability used by the published chain `actualKernel`. -/
noncomputable def rMaj (k : ℕ) (p : ℝ) : ℝ :=
  MinorityDynamics.qMaj k p + (1 - p) ^ k - p ^ k

end FastMinority


