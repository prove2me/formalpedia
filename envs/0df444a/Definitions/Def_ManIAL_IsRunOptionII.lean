-- Prove2me | Definitions.Def_ManIAL_IsRunOptionII
-- name    : ManIAL_IsRunOptionII
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:54.072554+00:00
-- url     : https://prove2.me/theorems/8b0de19b-5767-4b87-96af-f1efc9dd2aec
-- title:
--   A run of ManIAL with Option II and RGD ($\sigma_k=2^{k/3}$)
-- statement:
--   Fix $\sigma_k=2^{k/3}$ and a constant $G$. A **run of ManIAL with Option II** consists of sequences $(x^k,y^k,z^k)$ following the outer recursion of ManIAL, together with counts $N_k$, such that for every $k$, with $\psi_k=\mathcal L_{\sigma_k}(\cdot,z^k)$ and $L_k=\alpha^2(\ell_{\nabla f}+\sigma_k\|\mathcal A\|^2)+2G\beta$:
--
--   1. RGD with stepsize $1/L_k$ is started at $u_0=x^k$;
--   2. $x^{k+1}=u_t$ for some $t\le2^k$ minimizing $\|\operatorname{grad}\psi_k(u_s)\|$ over $0\le s\le2^k$, i.e. $x^{k+1}$ is an output of $\mathrm{RGD}(\psi_k,L_k,2^k,x^k)$;
--   3. $N_k=2^k+1$, the number of Riemannian gradients evaluated.
--
--   This is ManIAL as used in Theorem 3.8 (b): Option II, a fixed number $2^k$ of RGD iterations in outer iteration $k$.
--
--   **Formalization Note** Every tie-break of the argmin is allowed. The penalty is $2^{k/3}$ (a real power); Theorem 3.8 (b) prints $\sigma_k=1/2^{k/3}$, which contradicts the increasing penalty Algorithm 1 requires and the proof of Theorem 3.6, which uses $\sigma_k=2^{k/3}$.
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Algorithm 1, p.9; Algorithm 2, p.10; Theorem 3.8 (b), p.14; proof of Theorem 3.6, p.13

import Mathlib
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_ManIAL_psi
import Definitions.Def_ManIAL_rgdSeq
import Definitions.Def_ManIAL_Lk
import Definitions.Def_ManIAL_IsManIALIterates

open ZORiem.RGD

namespace ManIAL

/-- A run of ManIAL with **Option II** and Algorithm 2 (RGD) as the subroutine, with
`σ_k = 2^{k/3}` (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, Algorithm 1, p.9, Algorithm 2, p.10,
Theorem 3.8 (b), p.14, with the penalty corrected to `2^{k/3}`). For every `k`, with
`ψ_k = psi f h A σ_k z^k` and `L_k = α²(ℓ_{∇f} + σ_k‖A‖²) + 2Gβ`, `x^{k+1}` is the output of
`RGD(ψ_k, L_k, 2^k, x^k)`: an iterate `u_t`, `t ≤ 2^k`, minimizing `‖grad ψ_k(u_s)‖` over
`0 ≤ s ≤ 2^k` (any tie-break); `N k = 2^k + 1` gradient evaluations; `y^{k+1}`, `z^{k+1}`
follow steps 5–7 (`IsManIALIterates`).

**Formalization Note.** `2^{k/3}` is the real power `(2 : ℝ) ^ ((k : ℝ) / 3)`. Theorem 3.8 (b)
prints `σ_k = 1/2^{k/3}`, which is not increasing as Algorithm 1 requires; the proof of
Theorem 3.6 uses `σ_k = 2^{k/3}`. `N k` counts the evaluations of `grad ψ_k` at
`u_0, …, u_{2^k}` (Algorithm 2's loop runs `t = 0, …, T`). -/
def IsRunOptionII {n m : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (α β ℓf G β₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (y₀ : EuclideanSpace ℝ (Fin m))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m)) (N : ℕ → ℕ) :
    Prop :=
  IsManIALIterates h A β₀ (fun k => (2 : ℝ) ^ ((k : ℝ) / 3)) x₀ y₀ x y z ∧
    ∀ k : ℕ,
      let σk : ℝ := (2 : ℝ) ^ ((k : ℝ) / 3)
      let ψk := psi f h A σk (z k)
      let u := rgdSeq M R ψk (Lk α β G ℓf A σk) (x k)
      ∃ t : ℕ, t ≤ 2 ^ k ∧ x (k + 1) = u t ∧
        (∀ s ≤ 2 ^ k, ‖rgrad M ψk (u t)‖ ≤ ‖rgrad M ψk (u s)‖) ∧ N k = 2 ^ k + 1

end ManIAL


