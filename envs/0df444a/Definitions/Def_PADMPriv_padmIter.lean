-- Prove2me | Definitions.Def_PADMPriv_padmIter
-- name    : PADMPriv_padmIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:06.468666+00:00
-- url     : https://prove2.me/theorems/be7e161e-f680-415d-bb54-2f33a6db41bf
-- title:
--   Iterates $\tilde u_{(k)}$ of private PADM (Algorithm 1)
-- statement:
--   Given a data set $D=(d_{(1)},\dots,d_{(n)})$, noise vectors $z_{(1)},\dots,z_{(n)}\in\mathbb R^m$ and a starting point $\tilde x_{(0)}\in\mathbb R^p$, private PADM (Algorithm 1, update (20)) computes
--   $$
--   \tilde u_{(0)} = A\tilde x_{(0)},\qquad \tilde u_{(k)} = T_{f_k}(\tilde u_{(k-1)}) + \frac{z_{(k)}}{2},\quad k=1,\dots,n,
--   $$
--   where $f_k = f(\cdot,d_{(k)})$ and $T_{f_k}$ is the PADM operator (15) with $F$ replaced by $f_k$. The feasible pair of iteration $k$ is $\tilde x_{(k)} = V\tilde u_{(k)}$, $\tilde y_{(k)} = U(c-\tilde u_{(k)})$. Each record is used once, at its own step.
--
--   **Formalization Note** Records and noise vectors are indexed by $\{0,\dots,n-1\}$; step $k$ uses entry $k-1$.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Algorithm 1 and Eq. (20), pp.8–9

import Mathlib
import Definitions.Def_PADMPriv_padmOp
import Definitions.Def_PADMPriv_noisyIter

namespace PADMPriv

/-- The iterates of private PADM, Algorithm 1 and (20) of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), pp.8–9:
`ũ₍₀₎ = A x̃₍₀₎` and `ũ₍ₖ₎ = T_{f_k}(ũ₍ₖ₋₁₎) + z₍ₖ₎/2` for `k = 1, …, n`, where
`f_k = f(·, d₍ₖ₎)` is the loss of the `k`-th record of `D` and `z₍ₖ₎` the `k`-th noise vector.
The feasible pair of iteration `k` is `x̃₍ₖ₎ = Vũ₍ₖ₎`, `ỹ₍ₖ₎ = U(c − ũ₍ₖ₎)` (12).

**Formalization Note** The data set `D` and the noise `z` are `Fin n`-indexed arrays; record and
noise `k + 1` of the paper are `D ⟨k, _⟩`, `z ⟨k, _⟩`. Each record is used once, at its step. -/
noncomputable def padmIter {m p l n : ℕ} {R : Type*} (β : ℝ)
    (f : EuclideanSpace ℝ (Fin p) → R → ℝ) (g : EuclideanSpace ℝ (Fin l) → ℝ)
    (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin p)) (D : Fin n → R) (z : Fin n → EuclideanSpace ℝ (Fin m)) :
    ℕ → EuclideanSpace ℝ (Fin m) :=
  noisyIter (fun k => padmOp β (fun x => f x (D k)) g A B c) (Matrix.toEuclideanLin A x₀)
    (fun k => (1 / 2 : ℝ) • z k)

end PADMPriv


