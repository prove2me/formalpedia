-- Prove2me | Definitions.Def_OrderedExperts_roundEst
-- name    : OrderedExperts_roundEst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:36:48.479254+00:00
-- url     : https://prove2.me/theorems/38491ea5-d699-4f44-b0ef-63588b8944ab
-- title:
--   Loss-estimate vector of one round of Algorithm 2
-- statement:
--   On round $t$ of Algorithm 2, after the pair $(A_t,B_t)$ of active ranks is drawn from $\pi_t$, the learner forms two endpoint flow estimates with floor $\xi=1/T$ (so $\Lambda_t=1+\log(m_tT)$):
--   1. $\hat\ell^\uparrow_t$, the estimate of $\ell^\uparrow_t$ on the chain read forward (anchor below the chain);
--   2. $\hat\ell^\downarrow_t$, the estimate of $\ell^\downarrow_t$ on the chain read backward: each rank $j$ is replaced by $m_t+1-j$ in $\pi_t$, in the pair, and in the output of the estimator (anchor above the chain).
--
--   The same paid pair feeds both estimators. The cumulative estimate of expert $f$ is updated by
--   $$
--   L_t(f)=L_{t-1}(f)+\hat\ell^\uparrow_t(j_t(f))+\hat\ell^\downarrow_t(j_t(f)).
--   $$
--   This definition is the increment $\hat\ell^\uparrow_t(j_t(f))+\hat\ell^\downarrow_t(j_t(f))$ as a function of the drawn pair.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Algorithm 2, p.11; Sec. 4.1, p.10; Appendix B.2, p.20

import Definitions.Def_OrderedExperts_roundPi
import Definitions.Def_OrderedExperts_chainPt
import Definitions.Def_OrderedExperts_est

namespace OrderedExperts

/-- **The loss-estimate vector of one round of Algorithm 2.**
Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Algorithm 2, p.11: "`ℓ̂↑t ← Estimate(πt, At, Bt, ℓ↑t(xt,At), ℓ↑t(xt,Bt))` on the chain read
forward; `ℓ̂↓t ← Estimate(πt, At, Bt, ℓ↓t(xt,At), ℓ↓t(xt,Bt))` on the chain read backward; Set
`Lt(f) = Lt−1(f) + ℓ̂↑t(jt(f)) + ℓ̂↓t(jt(f))`", and Sec. 4.1, p.10: "reading the chain backward replaces
each rank `j` by `mt + 1 − j` in `πt`, in the pair, and in the output of the estimator". The smoothing
is `ξ = 1/T` (Appendix B.2, p.20).

For the queried pair of ranks `(a, b)`, `roundEst η T rec up down v t a b f` is the increment of
`Lt(f)`: the forward endpoint-flow estimate of `ℓ↑t` at rank `jt(f)` plus the backward estimate of
`ℓ↓t` at rank `jt(f)` (computed with `πt` read backward, the reversed pair `(mt+1−a, mt+1−b)`, the
reversed values `ℓ↓t(xt,mt+1−r)` and evaluated at the reversed rank `mt+1−jt(f)`), both with floor
`ξ = 1/T` and `Λt = 1 + log(mt T)`. The same pair feeds both estimators. -/
noncomputable def roundEst {A : Type*} [LinearOrder A] [OrderBot A] {n : ℕ} (η : ℝ) (T : ℕ)
    (rec : ℕ → Fin n → A) (up down : ℕ → A → ℝ) (v : ℕ → Fin n → ℝ) (t a b : ℕ) :
    Fin n → ℝ :=
  fun f =>
    est (chainSize rec t) (1 / (T : ℝ)) (roundPi η T rec v t)
        (fun j => up t (chainPt rec t j)) a b (rank rec t f) +
      est (chainSize rec t) (1 / (T : ℝ)) (fun j => roundPi η T rec v t (chainSize rec t + 1 - j))
        (fun j => down t (chainPt rec t (chainSize rec t + 1 - j)))
        (chainSize rec t + 1 - a) (chainSize rec t + 1 - b) (chainSize rec t + 1 - rank rec t f)

end OrderedExperts


