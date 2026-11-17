-- Prove2me | Definitions.Def_PADMPriv_Supplement_padmLawLap
-- name    : PADMPriv_Supplement_padmLawLap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:49:05.809648+00:00
-- url     : https://prove2.me/theorems/65d004e7-9816-4eb4-8f81-8219e1d80eb9
-- title:
--   Law of the $k$-th iterate of PADM-$L_\lambda$
-- statement:
--   Fix a data set $D=(d_{(1)},\dots,d_{(n)})$, a starting point $\tilde x_{(0)}\in\mathbb R^p$ and a Laplace scale $\lambda>0$. Private PADM (Algorithm 1) with Laplace noise runs
--   $$
--   \tilde u_{(0)}=A\tilde x_{(0)},\qquad \tilde u_{(k)}=T_{f_k}(\tilde u_{(k-1)})+\frac{z_{(k)}}{2},\quad k=1,\dots,n,
--   $$
--   where $f_k=f(\cdot,d_{(k)})$, $T_{f_k}$ is the PADM operator (15) for $f_k$, and $z_{(1)},\dots,z_{(n)}$ are independent with law $L_m(0_m,\lambda)$. This definition is the law of $\tilde u_{(k)}$ for the fixed data set $D$, the randomness being the noise only. At $k=n$ it is the law of the final output of PADM-$L_\lambda$, the mechanism of Theorem 4.3.
--
--   **Formalization Note** The image of the product measure $L_m(0_m,\lambda)^{\otimes n}$ on `Fin n → ℝᵐ` under the published iterate map `PADMPriv.padmIter`, which already halves the noise. It is the Laplace analogue of the published Gaussian `PADMPriv.padmLaw`.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Algorithm 1, p.9; Section 4.3, p.10

import Mathlib
import Definitions.Def_PADMPriv_padmIter
import Definitions.Def_PADMPriv_Supplement_lapNoise

namespace PADMPriv.Supplement

open MeasureTheory

/-- The law of the `k`-th iterate `ũ₍ₖ₎` of PADM-L_λ for a fixed data set `D`
(Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*,
STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), Algorithm 1, p.9, and Section 4.3, p.10):
the noise vectors `z₍₁₎, …, z₍ₙ₎` are independent `L_m(0_m, λ)`. At `k = n` it is the law of the
final output of Theorem 4.3. The Laplace analogue of the published `PADMPriv.padmLaw`.

**Formalization Note** The image of the product measure `L_m(0_m, λ)^{⊗n}` on `Fin n → ℝᵐ` under
`z ↦ ũ₍ₖ₎ = PADMPriv.padmIter … D z k` (the iterate adds `z₍ₖ₎/2`, as in (20)). The scale is
named `s`. -/
noncomputable def padmLawLap {m p l n : ℕ} {R : Type*} (β s : ℝ)
    (f : EuclideanSpace ℝ (Fin p) → R → ℝ) (g : EuclideanSpace ℝ (Fin l) → ℝ)
    (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin p)) (D : Fin n → R) (k : ℕ) :
    Measure (EuclideanSpace ℝ (Fin m)) :=
  (Measure.pi fun _ : Fin n => lapNoise m s).map (fun z => padmIter β f g A B c x₀ D z k)

end PADMPriv.Supplement


