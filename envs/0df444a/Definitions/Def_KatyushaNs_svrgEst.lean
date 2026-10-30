-- Prove2me | Definitions.Def_KatyushaNs_svrgEst
-- name    : KatyushaNs_svrgEst
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:45:54.95555+00:00
-- url     : https://prove2.me/theorems/032b2f9e-aa05-495a-99fd-f7d11218416e
-- title:
--   Variance-reduced gradient estimator $\widetilde\nabla_{k+1}$
-- statement:
--   Let $f = \frac1n\sum_i f_i$. For a snapshot $\widetilde x$, a point $x$ and an index $i \in \{1,\dots,n\}$, the variance-reduced (SVRG) gradient estimator is
--   $$\widetilde\nabla = \nabla f(\widetilde x) + \nabla f_i(x) - \nabla f_i(\widetilde x).$$
--   In Algorithm 2 (lines 6 and 10), $\widetilde x = \widetilde x^s$ is the current snapshot, $x = x_{k+1}$ and $i$ is drawn uniformly at random; averaged over $i$ the estimator equals $\nabla f(x)$.
--
--   **Formalization Note** The index $i$ ranges over `Fin n`; $\nabla$ is Mathlib's `gradient`.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Algorithm 2, lines 6 and 10, p. 15

import Mathlib
import Definitions.Def_KatyushaNs_favg

namespace KatyushaNs

/-- **The variance-reduced gradient estimator `∇̃_{k+1}` (Algorithm 2, lines 6 and 10).**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Algorithm 2, p. 15 (PDF p. 16): line 6 "μ^s ← ∇f(x̃^s)", line 10
"∇̃_{k+1} ← μ^s + ∇fi(x_{k+1}) − ∇fi(x̃^s) where i is randomly chosen from {1, 2, …, n}".

`svrgEst fi xt x i = ∇f(xt) + ∇fᵢ(x) − ∇fᵢ(xt)`, where `xt` is the snapshot `x̃^s`, `x` is the
current point `x_{k+1}` and `i` the sampled index.

**Formalization Note.** The index `i ∈ {1, …, n}` is `i : Fin n`; `∇` is Mathlib's `gradient`. -/
noncomputable def svrgEst {d n : ℕ} (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (xt x : EuclideanSpace ℝ (Fin d)) (i : Fin n) : EuclideanSpace ℝ (Fin d) :=
  gradient (favg fi) xt + gradient (fi i) x - gradient (fi i) xt

end KatyushaNs


