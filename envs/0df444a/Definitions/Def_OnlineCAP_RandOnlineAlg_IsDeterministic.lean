-- Prove2me | Definitions.Def_OnlineCAP_RandOnlineAlg_IsDeterministic
-- name    : OnlineCAP_RandOnlineAlg_IsDeterministic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:32.822528+00:00
-- url     : https://prove2.me/theorems/8d9494f4-575d-4bf9-8a21-15d72801f834
-- title:
--   Deterministic online algorithm
-- statement:
--   A randomized online algorithm $(\Omega,\mu,F)$ is **deterministic** when its purchases do not depend on the coins: $F_\omega(s)=F_{\omega'}(s)$ for all $\omega,\omega'\in\Omega$ and every request list $s$.
--
--   For a deterministic algorithm the expected cost in the competitive guarantee is simply its cost, so "$\alpha$-competitive in expectation" becomes the deterministic competitive ratio of §2.2.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §2.2, p.10

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg

namespace OnlineCAP

/-- **Deterministic online algorithm.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §2.2, p.10 (PDF p.10): "Deterministic Competitive
Ratio: A deterministic online algorithm is α-competitive if, for any valid request sequence, the
cost of the algorithm's solution is at most α · OPT".

A randomized online algorithm is deterministic when its purchases do not depend on the coins:
`buy ω s = buy ω' s` for all `ω, ω'` and every request list `s`. For such an algorithm the
expected cost in `IsCompetitive` is the cost.

**Formalization Note.** Every deterministic online algorithm in the paper's sense is of this form
(take `Ω = Unit`). -/
def RandOnlineAlg.IsDeterministic {U Req : Type} (A : RandOnlineAlg U Req) : Prop :=
  ∀ (s : List Req) (ω ω' : A.Ω), A.buy ω s = A.buy ω' s

end OnlineCAP


