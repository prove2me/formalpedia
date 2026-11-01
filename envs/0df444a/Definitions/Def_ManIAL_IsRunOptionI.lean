-- Prove2me | Definitions.Def_ManIAL_IsRunOptionI
-- name    : ManIAL_IsRunOptionI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:57.750663+00:00
-- url     : https://prove2.me/theorems/a4a8bad4-a7d5-49cb-a91f-ea30da434f30
-- title:
--   A run of ManIAL with Option I and RGD ($\sigma_k=b^k$, $\epsilon_k=1/\sigma_k$)
-- statement:
--   Fix $b>1$, $\sigma_k=b^k$, $\epsilon_k=1/\sigma_k$ and a constant $G$. A **run of ManIAL with Option I** consists of sequences $(x^k,y^k,z^k)$ following the outer recursion of ManIAL, together with counts $N_k$, such that for every $k$, with $\psi_k=\mathcal L_{\sigma_k}(\cdot,z^k)$ and $L_k=\alpha^2(\ell_{\nabla f}+\sigma_k\|\mathcal A\|^2)+2G\beta$:
--
--   1. RGD with stepsize $1/L_k$ is started at $u_0=x^k$, producing $u_0,u_1,\dots$;
--   2. $x^{k+1}=u_t$ for the **first** index $t$ with $\|\operatorname{grad}\psi_k(u_t)\|\le\epsilon_k$ (criterion (3.12));
--   3. $N_k=t+1$, the number of Riemannian gradients evaluated.
--
--   This is ManIAL as used in Theorem 3.8 (a): Option I with Algorithm 2 as the subroutine, stopped as soon as the inexactness criterion (3.12) holds.
--
--   **Formalization Note** "Use Algorithm 2 as the subroutine … Option I: $x^{k+1}$ satisfies (3.12)" is read as running RGD until (3.12) first holds. The constant $G$, which enters the stepsize through $L_k$, is a parameter of the run.
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Algorithm 1, p.9; Algorithm 2, p.10; Theorem 3.8 (a), p.14

import Mathlib
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_ManIAL_psi
import Definitions.Def_ManIAL_rgdSeq
import Definitions.Def_ManIAL_Lk
import Definitions.Def_ManIAL_IsManIALIterates

open ZORiem.RGD

namespace ManIAL

/-- A run of ManIAL with **Option I** and Algorithm 2 (RGD) as the subroutine, with
`σ_k = b^k` and `ϵ_k = 1/σ_k` (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, Algorithm 1, p.9,
Algorithm 2, p.10, Theorem 3.8 (a), p.14). For every `k`, with `ψ_k = psi f h A σ_k z^k` and
`L_k = α²(ℓ_{∇f} + σ_k‖A‖²) + 2Gβ`: RGD with stepsize `1/L_k` is started at `x^k`, and
`x^{k+1} = u_t` for the **first** index `t` with `‖grad ψ_k(u_t)‖ ≤ ϵ_k` (criterion (3.12));
`N k = t + 1` is the number of gradient evaluations it used; `y^{k+1}`, `z^{k+1}` follow
steps 5–7 (`IsManIALIterates`).

**Formalization Note.** Option I reads "return `x^{k+1}` satisfying (3.12)" with the subroutine
stopped at its first iterate that meets (3.12) (the count of the proof of Theorem 3.8 is the
number of RGD steps taken). `N k` counts the evaluations of `grad ψ_k` at `u_0, …, u_t`. The
constant `G` enters through `L_k` and is a parameter of the run. -/
def IsRunOptionI {n m : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (α β ℓf G b β₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (y₀ : EuclideanSpace ℝ (Fin m))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m)) (N : ℕ → ℕ) :
    Prop :=
  IsManIALIterates h A β₀ (fun k => b ^ k) x₀ y₀ x y z ∧
    ∀ k : ℕ,
      let ψk := psi f h A (b ^ k) (z k)
      let u := rgdSeq M R ψk (Lk α β G ℓf A (b ^ k)) (x k)
      ∃ t : ℕ, x (k + 1) = u t ∧ ‖rgrad M ψk (u t)‖ ≤ 1 / b ^ k ∧
        (∀ s < t, 1 / b ^ k < ‖rgrad M ψk (u s)‖) ∧ N k = t + 1

end ManIAL


