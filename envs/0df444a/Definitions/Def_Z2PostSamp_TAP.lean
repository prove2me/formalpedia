-- Prove2me | Definitions.Def_Z2PostSamp_TAP
-- name    : Z2PostSamp_TAP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:54.364358+00:00
-- url     : https://prove2.me/theorems/cb99c1a4-aeaa-4cd7-88ba-3de83388a1fd
-- title:
--   The conditional TAP objective $\Phi_k$, its gradient and Hessian form, the logit (2.11), and $\Psi_0$
-- statement:
--   Let $\phi(v)=\frac{1+v}2\log\frac{1+v}2+\frac{1-v}2\log\frac{1-v}2$. The conditional TAP objective is
--
--   $$\Phi_k(u;x_{S_k})=\sum_{i\in R_k}\phi(u_i)-\tfrac12u^\top J_{R_k,R_k}u-h^{(k)}(x_{S_k})^\top u+\frac{a_{k/n}}2\|u\|^2,\qquad u\in(-1,1)^{R_k},$$
--
--   with gradient $\nabla_u\Phi_k=\operatorname{arctanh}(u)-J_{R_k,R_k}u-h^{(k)}+a_{k/n}u$ and Hessian quadratic form $v\mapsto\sum_{i\in R_k}\frac{v_i^2}{1-u_i^2}-v^\top J_{R_k,R_k}v+a_{k/n}\|v\|^2$. The logit vector computed from an approximate minimizer $\widehat m$ is
--
--   $$\widehat\ell^{(k)}=h^{(k)}+(J_{R_k,R_k}-a_{k/n}I)\,\widehat m .$$
--
--   The unpinned functional is $\Psi_0(u)=\sum_i\phi(u_i)-\tfrac12u^\top Ju-\frac{\lambda^2n}4\big(1-\frac{\|u\|^2}n\big)^2$ on $(-1,1)^n$, with Hessian form $\sum_i\frac{v_i^2}{1-u_i^2}-v^\top Jv+\lambda^2\big(1-\frac{\|u\|^2}n\big)\|v\|^2-\frac{2\lambda^2}n\langle u,v\rangle^2$.
--
--   These objectives define the sampler's logit computation and carry the local-convexity estimates.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`; sums over $R_k$ ignore the coordinates on $S_k$. $\phi$ uses Lean's $\log0=0$, harmless on the clipped cube. For symmetric $J$ the gradient and the forms are the first and second derivatives; every statement using them concerns symmetric $J$. The coefficient is the exact $a_{k/n}$.
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), §2.3, p.10, (2.10)–(2.11); Algorithm 2 line 5, p.12; (3.2), p.15

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_Z2PostSamp_RevealPath
import Definitions.Def_Z2PostSamp_Scalars

set_option autoImplicit false

open OAI.CriticalSK

namespace Z2PostSamp

noncomputable section

/-!
# The conditional TAP objectives `Φ_k`, `Ψ₀`, their gradients and Hessian forms

Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), §2.3, p.10: `φ(v) = ((1+v)/2) log((1+v)/2) + ((1−v)/2) log((1−v)/2)`,
(2.10) `Φ_k(u; x_{S_k}) = Σ_{i∈R_k} φ(u_i) − ½ uᵀ J_{R_k,R_k} u − ĥ^{(k)}(x_{S_k})ᵀ u
+ (a_{k/n}/2) ‖u‖²` on `(−1,1)^{R_k}`, (2.11) `ℓ̂^{(k)} = ĥ^{(k)} + (J_{R_k,R_k} − a_{k/n} I) m̂^{(k)}`;
Algorithm 2, line 5 (p.12): `∇_u Φ_k = arctanh(u) − J_{R_k,R_k} u − ĥ^{(k)} + a_{k/n} u`;
(3.2), p.15: `Ψ₀(u) = Σ_i φ(u_i) − ½ uᵀ J u − (λ² n/4)(1 − ‖u‖²/n)²` on `(−1,1)ⁿ`.

**Formalization Note.** Vectors are `Fin n → ℝ`; every sum over `R_k` ignores the coordinates on `S_k`
(the objective is a function of `u_{R_k}` only). `φ` uses Lean's `log 0 = 0`, harmless because `Φ_k`
is only evaluated on the clipped cube `[−c_n, c_n]^{R_k} ⊂ (−1,1)^{R_k}`. The Hessians are given as
the explicit quadratic forms `v ↦ vᵀ ∇² v`: for `Φ_k`, `Σ_{R} v_i²/(1 − u_i²) − Σ_{R,R} J_ij v_i v_j
+ a_{k/n} Σ_R v_i²`; for `Ψ₀`, `Σ v_i²/(1 − u_i²) − vᵀ J v + λ²(1 − ‖u‖²/n)‖v‖² − (2λ²/n)⟨u,v⟩²`.
For symmetric `J` and `u ∈ (−1,1)` these are the second derivatives (`φ'' (v) = 1/(1 − v²)`), and
`tapGrad` is the gradient; every statement using them is about symmetric `J`. The coefficient is the
exact `a_{k/n}` (the analytic estimates always use the exact value, p.10).
-/

/-- `φ(v) = ((1+v)/2) log((1+v)/2) + ((1−v)/2) log((1−v)/2)` (p.10). -/
def phi (v : ℝ) : ℝ :=
  (1 + v) / 2 * Real.log ((1 + v) / 2) + (1 - v) / 2 * Real.log ((1 - v) / 2)

/-- The coefficient `a_{k/n}` (2.9). -/
def aCoef (n : ℕ) (lam : ℝ) (k : ℕ) : ℝ := aAl lam ((k : ℝ) / n)

/-- The conditional TAP objective `Φ_k(u; x_{S_k})` of (2.10). -/
def tapObj {n : ℕ} (lam : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n))
    (x : Spin n) (k : ℕ) (u : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Rset I k, phi (u i) - (1 / 2 : ℝ) * ∑ i ∈ Rset I k, ∑ j ∈ Rset I k, J i j * u i * u j
    - ∑ i ∈ Rset I k, field J I x k i * u i + aCoef n lam k / 2 * ∑ i ∈ Rset I k, u i ^ 2

/-- The gradient `∇_u Φ_k(u; x_{S_k}) = arctanh(u) − J_{R_k,R_k} u − h^{(k)} + a_{k/n} u` on `R_k`
(zero on `S_k`). -/
def tapGrad {n : ℕ} (lam : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n))
    (x : Spin n) (k : ℕ) (u : Fin n → ℝ) : Fin n → ℝ := fun i =>
  if i ∈ Rset I k then
    Real.artanh (u i) - ∑ j ∈ Rset I k, J i j * u j - field J I x k i + aCoef n lam k * u i
  else 0

/-- The Hessian quadratic form `vᵀ ∇²_u Φ_k(u) v` on `R_k`. -/
def tapHessQ {n : ℕ} (lam : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n)) (k : ℕ)
    (u v : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Rset I k, v i ^ 2 / (1 - u i ^ 2) - ∑ i ∈ Rset I k, ∑ j ∈ Rset I k, J i j * v i * v j
    + aCoef n lam k * ∑ i ∈ Rset I k, v i ^ 2

/-- The final logit vector (2.11): `ĥ^{(k)} + (J_{R_k,R_k} − a_{k/n} I) m` on `R_k` (zero on `S_k`). -/
def tapLogit {n : ℕ} (lam : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n))
    (x : Spin n) (k : ℕ) (m : Fin n → ℝ) : Fin n → ℝ := fun i =>
  if i ∈ Rset I k then field J I x k i + ∑ j ∈ Rset I k, J i j * m j - aCoef n lam k * m i
  else 0

/-- The unpinned TAP functional `Ψ₀` of (3.2). -/
def Psi0 {n : ℕ} (lam : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) : ℝ :=
  ∑ i, phi (u i) - (1 / 2 : ℝ) * ∑ i, ∑ j, J i j * u i * u j
    - lam ^ 2 * n / 4 * (1 - (∑ i, u i ^ 2) / n) ^ 2

/-- The Hessian quadratic form `vᵀ ∇²Ψ₀(u) v`. -/
def psi0HessQ {n : ℕ} (lam : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) : ℝ :=
  ∑ i, v i ^ 2 / (1 - u i ^ 2) - ∑ i, ∑ j, J i j * v i * v j
    + lam ^ 2 * (1 - (∑ i, u i ^ 2) / n) * ∑ i, v i ^ 2
    - 2 * lam ^ 2 / n * (∑ i, u i * v i) ^ 2

end

end Z2PostSamp


