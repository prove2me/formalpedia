-- Prove2me | Definitions.Def_LinMaxLoad_probLin
-- name    : LinMaxLoad_probLin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:40.599214+00:00
-- url     : https://prove2.me/theorems/7845f5d4-0f6c-4b15-816d-44662af88e76
-- title:
--   Probability over a uniformly random linear map
-- statement:
--   For a finite field $K$, a finite $K$-vector space $E$, $r \ge 0$ and a property $P$ of linear maps $E \to K^r$,
--
--   $$
--   \Pr_h[P(h)] = \frac{|\{h \in \mathrm{Hom}_K(E,K^r) : P(h)\}|}{|\mathrm{Hom}_K(E,K^r)|},
--   $$
--
--   the probability that a uniformly random linear map $h : E \to K^r$ satisfies $P$, i.e. the expectation of the indicator of $P$. It is the $\Pr_h$ of Lemma 1, of the tail bound in the proof of Theorem 7, and of the kernel computation in the proof of Lemma 7.
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Lemma 1 and proof of Theorem 7, p.8; proof of Lemma 7, p.21

import Mathlib
import Definitions.Def_LinMaxLoad_avgLin

namespace LinMaxLoad

open Classical in
/-- **Probability over a uniformly random linear map** `h : E → K^r` (`Pr_h[·]` in Lemma 1 and
the proof of Theorem 7, p.8, and the proof of Lemma 7, p.21, of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)):
the fraction of all `K`-linear maps `E →ₗ[K] (Fin r → K)` satisfying `P`, i.e. the uniform
average of the indicator of `P`. -/
noncomputable def probLin (K E : Type*) [Field K] [Fintype K] [AddCommGroup E] [Module K E]
    [Finite E] (r : ℕ) (P : (E →ₗ[K] (Fin r → K)) → Prop) : ℝ :=
  avgLin K E r fun h => if P h then 1 else 0

end LinMaxLoad


