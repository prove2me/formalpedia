-- Prove2me | Definitions.Def_LinMaxLoad_expLoad
-- name    : LinMaxLoad_expLoad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:52.009623+00:00
-- url     : https://prove2.me/theorems/6a217ef3-78b2-489b-a4ff-512a7669a017
-- title:
--   Expected max load $\mathbb E_h[M(S,h)]$ for $h : E \to K^r$
-- statement:
--   Let $K$ be a finite field, $E$ a finite $K$-vector space, $r \ge 0$, and $S \subseteq E$ a finite set. The **expected max load** of $S$ into $K^r$ is
--
--   $$
--   \mathbb E_h\big[M(S, h)\big],
--   $$
--
--   where $h : E \to K^r$ is a uniformly random linear map and $M(S,h) = \max_b |S \cap h^{-1}(b)|$ is the max load. With $r = \lceil \log_p |S| \rceil$ and $E = \mathbb F_p^u$ this is the expected linear max load $m(S)$; with general $r$ and $E = \mathbb F_q^u$ or a quotient $E/V$ it is the quantity bounded in Theorem 7 and compared in Lemma 7.
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Definition 2 item 3, p.3; Theorem 7, p.8; Lemma 7, p.21

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_avgLin

namespace LinMaxLoad

open Classical in
/-- **Expected max load under a uniformly random linear map** `E_h[M(S, h)]` for
`h : E → K^r` (Definition 2.3, p.3, Theorem 7, p.8, Lemma 7, p.21, of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)):
the uniform average over all `K`-linear maps `h : E →ₗ[K] (Fin r → K)` of the max load
`M(S, h)` of the finite set `S ⊆ E`. -/
noncomputable def expLoad (K E : Type*) [Field K] [Fintype K] [AddCommGroup E] [Module K E]
    [Finite E] (r : ℕ) (S : Finset E) : ℝ :=
  avgLin K E r fun h => (maxLoad (h : E → Fin r → K) S : ℝ)

end LinMaxLoad


