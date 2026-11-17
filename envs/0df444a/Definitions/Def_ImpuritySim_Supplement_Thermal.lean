-- Prove2me | Definitions.Def_ImpuritySim_Supplement_Thermal
-- name    : ImpuritySim_Supplement_Thermal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:31:14.556908+00:00
-- url     : https://prove2.me/theorems/8ded470a-59c6-4075-99bc-878c2bcefbae
-- title:
--   Capped Krylov-depth weights $\min\{d-1,\tau\}$ and the thermal tail parameter $\eta_\tau$
-- statement:
--   Let $H$ be an impurity Hamiltonian in the bandwise form (3.15), with residual-bath modes $i$ carrying a band $\ell(i)$ and a Krylov depth $d(i)\ge1$, and $\omega_\ell=2^\ell\omega$. For a cutoff $\tau\ge1$ the **capped weights** of (6.1) are
--   $$h^{(\beta)}_d=\min\{d-1,\tau\},$$
--   so that $D^{(\beta)}=\sum_i\min\{d(i)-1,\tau\}\,n_i$ and $e^{\frac12D^{(\beta)}}$ is the diagonal operator of the published occupation calculus evaluated at these weights. The **thermal tail parameter** of (6.14) is
--   $$\eta_\tau=\sum_i\exp\Bigl(-\frac{\beta\omega_{\ell(i)}}{8}+\frac12\min\{d(i)-1,\tau\}\Bigr),$$
--   the sum over the residual-bath modes.
--
--   Replacing the true Krylov depth by a capped one is what makes the exponential moment of a thermal state finite and $n$-independent in the thermally gapped regime.
--
--   **Formalization Note** Only $h_d$ with $d\ge1$ is ever read. The residual-bath modes are `F.bath` of the published `BandwiseForm`.
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), (6.1), p.28; (6.14), p.29

import Mathlib
import Definitions.Def_ImpuritySim_Occupation

namespace ImpuritySim.Supplement

/-!
# Capped Krylov-depth weights and the thermal tail parameter `η_τ` of §6.1

J. Jiang, N. Ju, O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation
of quantum impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2): (6.1),
p.28; (6.14), p.29.

**Formalization Note.**
* `hCap τ d = min{d − 1, τ}` is the weight `h^(β)_d` of (6.1) for a real cutoff `τ`; only `d ≥ 1`
  is ever read (the depths of residual-bath modes). With these weights the published
  `BandwiseForm.expHalfD (hCap τ)` is the diagonal operator `e^{D^(β)/2}`,
  `D^(β) = Σ_i min{d(i) − 1, τ} n_i` (6.1).
* `etaTau F β τ = η_τ = Σ_i exp(−β ω_{ℓ(i)}/8 + ½ min{d(i) − 1, τ})` (6.14), the sum over the
  residual-bath modes `i` (the modes carrying a band `ℓ(i)` and a depth `d(i)`, the same index set
  as the sum defining `D^(β)`), with `ω_ℓ = 2^ℓ ω` (`F.omegaL`).
-/

/-- The capped weights `h^(β)_d = min{d − 1, τ}` (6.1). -/
noncomputable def hCap (τ : ℝ) : ℕ → ℝ := fun d => min ((d : ℝ) - 1) τ

/-- `η_τ = Σ_{i ∈ residual bath} exp(−β ω_{ℓ(i)}/8 + ½ min{d(i) − 1, τ})` (6.14). -/
noncomputable def etaTau {n : ℕ} (F : BandwiseForm n) (β τ : ℝ) : ℝ :=
  ∑ i ∈ F.bath, Real.exp (-(β * F.omegaL (F.band i)) / 8 + hCap τ (F.depth i) / 2)

end ImpuritySim.Supplement


