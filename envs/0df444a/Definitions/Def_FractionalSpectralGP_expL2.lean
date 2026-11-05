-- Prove2me | Definitions.Def_FractionalSpectralGP_expL2
-- name    : FractionalSpectralGP_expL2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:55.927327+00:00
-- url     : https://prove2.me/theorems/d4113799-d051-4e50-a542-f3493a0ace5d
-- title:
--   The exponential $e_t(u)=e^{itu}$ as an element of $L^2(d\sigma)$
-- statement:
--   Let $\sigma$ be a finite Borel measure on $\mathbb R$ and $t\in\mathbb R$. The exponential
--
--   $$
--   e_t(u)=e^{itu}
--   $$
--
--   is bounded by $1$, hence belongs to the complex Hilbert space $L^2(d\sigma)$. This definition records $e_t$ as that element of $L^2(d\sigma)$.
--
--   The exponentials $e_\lambda$ are the candidate orthonormal basis vectors in the notion of a spectral pair, and $t\mapsto e_t$ is the curve whose regularity (Lemma 3.2) drives the differentiability of $X_\sigma$.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §3, p.8

import Mathlib

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The exponential `e_t(u) = e^{itu}` as an element of `L²(dσ)` for a finite Borel measure `σ`
on `ℝ` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §3, p.8: "for `t ∈ ℝ`, `e_t(u) = e^{itu}`").

**Formalization Note.** `e_t` is bounded by `1` and continuous, so it lies in `L²(σ; ℂ)` for every
finite `σ`; the membership proof is part of the definition. -/
noncomputable def expL2 (σ : Measure ℝ) [IsFiniteMeasure σ] (t : ℝ) : Lp ℂ 2 σ :=
  (MemLp.of_bound (f := fun u : ℝ => Complex.exp (Complex.I * (t * u))) (by fun_prop) 1
    (ae_of_all _ fun u => by simp [Complex.norm_exp])).toLp _

end FractionalSpectralGP


