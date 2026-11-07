-- Prove2me | Definitions.Def_EffRobustLearn_gVec
-- name    : EffRobustLearn_gVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:35:59.604324+00:00
-- url     : https://prove2.me/theorems/a61662a8-365d-41ed-b577-5afe6562876d
-- title:
--   The vector $g_t$ of the linearization (3.6)
-- statement:
--   For an iterate $\bar\mu$ and a hypothesis $h$, the vector $g$ has coordinate
--   $$\frac{y(2+|\bar\mu(x)|)-\bar\mu(x)}{4|\bar S_{\mathrm{inp}}|(1+|\bar\mu(x)|)}\quad\text{on }(x,y)\in\bar S_{\mathrm{inp}},\qquad \frac1{2|S_{\mathrm{ref}}|}\Big(\frac{\bar\mu(x)}{1+|\bar\mu(x)|}-h(x)\Big)\quad\text{on }x\in S_{\mathrm{ref}}.$$
--
--   It is the linear part of the iteration objective $U_t$.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), eq. (3.6), p.15 (PDF p.16)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM
import Definitions.Def_EffRobustLearn_feasibleSet

namespace EffRobustLearn

/-- The vector `g_t` of (3.6), Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.15, for an iterate `μ̄` and hypothesis `h`:
on `(x, y) ∈ S̄inp` the coordinate `(y(2 + |μ̄(x)|) - μ̄(x)) / (4|S̄inp|(1 + |μ̄(x)|))`, and on `x ∈ Sref` the coordinate
`(1/(2|Sref|)) (μ̄(x)/(1 + |μ̄(x)|) - h(x))`. -/
noncomputable def gVec {X : Type*} {n m : ℕ} (μ h : X → ℝ) (Sinp : Fin n → X × Bool)
    (Sref : Fin m → X) : SampleVec n m :=
  WithLp.toLp 2 (Sum.elim
    (fun i => (pm (Sinp i).2 * (2 + |μ (Sinp i).1|) - μ (Sinp i).1) /
      (4 * (n : ℝ) * (1 + |μ (Sinp i).1|)))
    fun j => (1 / (2 * (m : ℝ))) * (μ (Sref j) / (1 + |μ (Sref j)|) - h (Sref j)))

end EffRobustLearn


