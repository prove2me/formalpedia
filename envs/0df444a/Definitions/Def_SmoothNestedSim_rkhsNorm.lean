-- Prove2me | Definitions.Def_SmoothNestedSim_rkhsNorm
-- name    : SmoothNestedSim_rkhsNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:00.23373+00:00
-- url     : https://prove2.me/theorems/a683e60c-6819-4a24-bc94-4c3bca913bbf
-- title:
--   RKHS norm $\|f\|_{\mathcal N_k(\Omega)}$
-- statement:
--   For $f\in\mathcal N_k(\Omega)$ the **RKHS norm** is
--
--   $$
--   \|f\|_{\mathcal N_k(\Omega)} = \Bigl(\min\Bigl\{C\ge0:\ \Bigl(\sum_i c_i f(x_i)\Bigr)^2\le C\sum_{i,j}c_ic_jk(x_i,x_j)\ \text{for all finite families in }\Omega\Bigr\}\Bigr)^{1/2},
--   $$
--
--   which for a positive definite kernel equals the norm of $f$ in the closure of $\mathcal N^0_k(\Omega)$ (the norm induced by $\langle\cdot,\cdot\rangle_{\mathcal N^0_k(\Omega)}$, extended by continuity).
--
--   It is the penalty in the KRR problem (5) and the norm in Lemma EC.3 and (EC.6.2).
--
--   **Formalization Note** The minimum is written as an infimum. For $f\notin\mathcal N_k(\Omega)$ the set is empty and the value is $0$; every statement of the mission uses the norm only for members of $\mathcal N_k(\Omega)$.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §3, p.11 (the norm of N_k(Ω))

import Mathlib
import Definitions.Def_SmoothNestedSim_IsRKHSBound

namespace SmoothNestedSim

/-- **The RKHS norm `‖f‖_{N_k(Ω)}`** (Wang, Wang, Zhang, *Smooth Nested Simulation*,
arXiv:2201.02958v6, §3, p.11): the square root of the least `C` with
`(Σᵢ cᵢ f(xᵢ))² ≤ C Σᵢ Σⱼ cᵢ cⱼ k(xᵢ, xⱼ)` for all finite families of points of `Ω`.

**Formalization Note.** For `f ∈ N_k(Ω)` (see `RKHS`) and a positive definite kernel, the set of
admissible `C` is a nonempty closed half-line `[‖f‖², ∞)` (Aronszajn's criterion), so the
infimum is attained and equals the squared norm of the closure construction on p.11. For
`f ∉ N_k(Ω)` the set is empty and Lean's `sInf ∅ = 0` gives the value `0`; every statement of
the mission uses the norm only for members of `N_k(Ω)`. -/
noncomputable def rkhsNorm {E : Type*} (k : E → E → ℝ) (Ω : Set E) (f : E → ℝ) : ℝ :=
  Real.sqrt (sInf {C : ℝ | IsRKHSBound k Ω f C})

end SmoothNestedSim


