-- Prove2me | Definitions.Def_PADMPriv_padmLaw
-- name    : PADMPriv_padmLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:02.462461+00:00
-- url     : https://prove2.me/theorems/5f762c67-342a-4d78-a02c-378b6d509f85
-- title:
--   Law of the $k$-th iterate of PADM-$N_\sigma$ for fixed data
-- statement:
--   For a fixed data set $D$, the $k$-th iterate $\tilde u_{(k)}$ of private PADM with noise vectors $z_{(1)},\dots,z_{(n)}$ independent and $N(0_m,\sigma^2I_m)$-distributed is a random vector in $\mathbb R^m$; this is its law. At $k=n$ it is the law of the final output of PADM-$N_\sigma$ in Theorem 4.1.
--
--   **Formalization Note** The image of the product Gaussian measure on $(\mathbb R^m)^n$ under $z\mapsto\tilde u_{(k)}$.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Algorithm 1, p.9; Section 4.2, p.10

import Mathlib
import Definitions.Def_PADMPriv_padmIter
import Definitions.Def_PADMPriv_gaussNoise

namespace PADMPriv

open MeasureTheory

/-- The law of the `k`-th iterate `ũ₍ₖ₎` of PADM-N_σ for a fixed data set `D`
(Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), Algorithm 1, p.9, and Section 4.2, p.10): the noise vectors `z₍₁₎, …, z₍ₙ₎` are
independent `N(0_m, σ²I_m)`. At `k = n` it is the law of the final output of Theorem 4.1.

**Formalization Note** The image of the product measure `N(0, σ²I_m)^{⊗n}` on `Fin n → ℝᵐ` under
`z ↦ ũ₍ₖ₎`. -/
noncomputable def padmLaw {m p l n : ℕ} {R : Type*} (β σ : ℝ)
    (f : EuclideanSpace ℝ (Fin p) → R → ℝ) (g : EuclideanSpace ℝ (Fin l) → ℝ)
    (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin p)) (D : Fin n → R) (k : ℕ) :
    Measure (EuclideanSpace ℝ (Fin m)) :=
  (Measure.pi fun _ : Fin n => gaussNoise m σ).map (fun z => padmIter β f g A B c x₀ D z k)

end PADMPriv


