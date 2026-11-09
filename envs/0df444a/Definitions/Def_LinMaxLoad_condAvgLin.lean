-- Prove2me | Definitions.Def_LinMaxLoad_condAvgLin
-- name    : LinMaxLoad_condAvgLin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:47.843442+00:00
-- url     : https://prove2.me/theorems/8ad9d911-ce49-4e0f-aef6-ac20cf45e180
-- title:
--   Conditional expectation over a random linear map given an event
-- statement:
--   For a finite field $K$, a finite $K$-vector space $E$, $r \ge 0$, an event $P$ on linear maps $E \to K^r$ and a real function $X$ of such maps,
--
--   $$
--   \mathbb E_h[X(h) \mid P(h)] = \frac{\sum_{h : P(h)} X(h)}{|\{h : P(h)\}|},
--   $$
--
--   the average of $X$ over the uniformly random linear maps $h : E \to K^r$ satisfying $P$. In the proof of Lemma 7 it is used with the events $h|_V = \varphi$, giving the conditional expectation $\mathbb E_h[\,\cdot \mid h|_V]$.
--
--   **Formalization Note** On an empty event the value is $0$; every event $h|_V = \varphi$ used in the mission is nonempty, since every linear map on $V$ extends to $E$.
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), proof of Lemma 7, p.21 (E_h[· | h|_V])

import Mathlib
import Definitions.Def_LinMaxLoad_avgLin

namespace LinMaxLoad

open Classical in
/-- **Conditional expectation over a uniformly random linear map given an event**
`E_h[X | P]` (used for `E_h[M(V + T, h) | h|_V]` in the proof of Lemma 7, p.21, of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)):
the uniform average of `X h` over the linear maps `h : E →ₗ[K] (Fin r → K)` satisfying `P`.

**Formalization Note** It is the sum of `X` over the event divided by the number of maps in
it; on an empty event it is `0` (every use in this mission conditions on a nonempty event). -/
noncomputable def condAvgLin (K E : Type*) [Field K] [Fintype K] [AddCommGroup E] [Module K E]
    [Finite E] (r : ℕ) (P : (E →ₗ[K] (Fin r → K)) → Prop)
    (X : (E →ₗ[K] (Fin r → K)) → ℝ) : ℝ :=
  haveI : Fintype (E →ₗ[K] (Fin r → K)) := Fintype.ofFinite _
  (∑ h ∈ Finset.univ.filter P, X h) / ((Finset.univ.filter P).card : ℝ)

end LinMaxLoad


