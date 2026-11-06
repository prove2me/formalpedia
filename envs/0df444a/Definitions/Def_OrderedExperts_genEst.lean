-- Prove2me | Definitions.Def_OrderedExperts_genEst
-- name    : OrderedExperts_genEst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:29.975213+00:00
-- url     : https://prove2.me/theorems/944aa7c5-7159-4436-9088-5889627a7882
-- title:
--   Importance-weighted flow estimator of Lemma 1
-- statement:
--   Let $P$ be a law of the queried pair $(A,B)$ on $\{1,\dots,m\}^2$ with revelation probabilities $q$, let $\varphi_j(e)$ be flows, and let $g$ be a hidden vector with $g(x_0)=0$. For an edge $e=(a,b)$ write $H(e)=g(x_b)-g(x_a)$. The estimator of Lemma 1 is
--   $$
--   \hat g(j)=\sum_a \mathbf 1\{E_1=(0,a)\}\frac{\varphi_j(0,a)}{q(0,a)}H(0,a)+\sum_{1\le a<b}\mathbf 1\{E_2=(a,b)\}\frac{\varphi_j(a,b)}{q(a,b)}H(a,b),
--   $$
--   where the sums run over edges with $q>0$, $E_1=(0,A)$, and $E_2=(A\wedge B,A\vee B)$ is present only when $A\ne B$. On a realization $(A,B)$ each sum has at most one nonzero term.
--
--   **Formalization Note** The flows are a function $\varphi(j,a,b)$; the anchor value $g(x_0)=0$ is built in.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Lemma 1, p.8; Sec. 3.2, p.7

import Definitions.Def_OrderedExperts_revAnchor
import Definitions.Def_OrderedExperts_revInterval

namespace OrderedExperts

/-- **The importance-weighted flow estimator of Lemma 1.**
Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Lemma 1, p.8: "define `ĝ(j) = Σ_a 1{E1 = (0, a)} φj(0, a)/q(0, a) H(0, a) +
Σ_{1≤a<b} 1{E2 = (a, b)} φj(a, b)/q(a, b) H(a, b)`, where the sums run over edges with `q > 0`."
Here `H(e) = g(xb) − g(xa)` with `g(x0) = 0`, `E1 = (0, A)` and `E2 = (A ∧ B, A ∨ B)` when `A ≠ B`.

For a law `P` of the queried pair on `{1, …, m}²`, flows `φ j a b = φj(a, b)` and a hidden vector `g`,
`genEst m P φ g A B j` is the value of `ĝ(j)` on the realization `(A, B)`: the anchor term when
`q(0, A) > 0`, plus the interval term when `A ≠ B` and `q(A∧B, A∨B) > 0`.

**Formalization Note.** The indicator sums collapse to the at most one revealed edge of each kind;
the anchor value `g(x0) = 0` is built in (`H(0, A) = g A`). -/
noncomputable def genEst (m : ℕ) (P : ℕ → ℕ → ℝ) (φ : ℕ → ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (A B j : ℕ) : ℝ :=
  (if 0 < revAnchor m P A then φ j 0 A / revAnchor m P A * g A else 0) +
    if A ≠ B ∧ 0 < revInterval P (min A B) (max A B) then
      φ j (min A B) (max A B) / revInterval P (min A B) (max A B) * (g (max A B) - g (min A B))
    else 0

end OrderedExperts


