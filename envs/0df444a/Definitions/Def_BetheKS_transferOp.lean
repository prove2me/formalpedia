-- Prove2me | Definitions.Def_BetheKS_transferOp
-- name    : BetheKS_transferOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:05.397831+00:00
-- url     : https://prove2.me/theorems/4a49cd75-13a4-4e7b-a30c-f8eb09068919
-- title:
--   The transfer operator $\mathcal L$ on $L^2(\Omega,\nu)$, its spectral radius $\kappa(\delta)$, $\delta(\mu)$ and $h$
-- statement:
--   On $L^2(\Omega)=L^2(\Omega,\nu)$ (complex-valued, Definition A.2) the **transfer operator** is
--   $$
--   (\mathcal Lf)(T):=\Gamma(T)\sum_{j=1}^Kf(T_j)\qquad\text{(Definition 4.1)},
--   $$
--   and $\kappa=\kappa(\delta)$ is its spectral radius, $\kappa=\sup\{|z|:z\in\sigma(\mathcal L)\}$ (Definition 4.3). The file also defines $\delta(\mu)$, the $\delta>0$ with $\kappa(\delta)=d/\mu$ (Proposition 4.5), the constant function $\mathbf 1$, and the eigenfunction $h=\lim_{L\to\infty}\kappa^{-L}\mathcal L^L\mathbf 1$ of Proposition 4.4 (4) in its normalization.
--
--   **Formalization Note** That the formula defines a bounded operator on a.e.-classes is Observation 4.2 (a milestone), so $\mathcal L$ is defined by choice: the bounded operator agreeing a.e. with the formula, if one exists. Likewise $\delta(\mu)$ is the chosen solution of $\kappa(\delta)=d/\mu$ and $h$ the chosen $L^2$ limit; each is $0$ if none exists. $\kappa$ takes values in $[0,\infty]$.
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Definition 4.1, p.7; Definition 4.3, p.8; Propositions 4.4, 4.5, p.8; App. B, p.16

import Mathlib
import Definitions.Def_BetheKS_GWTree

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace BetheKS

open Classical

/-- **The transfer operator `ℒ`** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256
4da41e16…), Definition 4.1, p.7 (PDF p.8): on `L²(Ω) = L²(Ω, ν)` (complex-valued, Definition A.2),
`(ℒ f)(T) := Γ(T) ∑_{j=1}^{K} f(T_j)`, with `T_1,…,T_K` the forward subtrees and `Γ(T) = Γ_o`.

**Formalization Note.** That this formula defines a bounded operator on a.e.-classes is
Observation 4.2 (a milestone). The operator is therefore defined by choice: it is a bounded
operator satisfying the formula almost everywhere for every `f`, if one exists (it is then unique),
and `0` otherwise. `t, δ` are the parameters of `Γ = Γ_δ`. -/
noncomputable def transferOp (d t δ : ℝ) : Lp ℂ 2 (gwLaw d) →L[ℂ] Lp ℂ 2 (gwLaw d) :=
  if h : ∃ T : Lp ℂ 2 (gwLaw d) →L[ℂ] Lp ℂ 2 (gwLaw d), ∀ f : Lp ℂ 2 (gwLaw d),
      (T f : Offspring → ℂ) =ᵐ[gwLaw d]
        (fun K => (treeGamma t δ K : ℂ) * ∑ j ∈ Finset.range (K []), (f : Offspring → ℂ) (subtree K j))
  then h.choose else 0

/-- **`κ = κ(δ)`, the spectral radius of `ℒ`** (Definition 4.3, p.8):
`κ = sup{|z| : z ∈ σ(ℒ)}`. -/
noncomputable def kappa (d t δ : ℝ) : ℝ≥0∞ := spectralRadius ℂ (transferOp d t δ)

/-- **`δ(µ)`** (Proposition 4.5, p.8): the `δ > 0` with `κ(δ) = d/µ`, chosen when one exists (it is
unique for `t < µ ≤ d` by Proposition 4.5), and `0` otherwise. -/
noncomputable def deltaOf (d t μ : ℝ) : ℝ :=
  if h : ∃ δ : ℝ, 0 < δ ∧ kappa d t δ = ENNReal.ofReal (d / μ) then h.choose else 0

/-- The constant function `1 ∈ L²(Ω, ν)`. -/
noncomputable def oneL2 (d : ℝ) : Lp ℂ 2 (gwLaw d) := Lp.const 2 (gwLaw d) (1 : ℂ)

/-- **The transfer eigenfunction `h`** normalized as in Proposition 4.4 (4), p.8 and its proof
(App. B, p.16, "We can normalize so that `P1 = h`"): the `L²` limit of `κ^{−L} ℒ^L 1`, chosen when
the limit exists, and `0` otherwise. -/
noncomputable def hFun (d t δ : ℝ) : Lp ℂ 2 (gwLaw d) :=
  if h : ∃ g : Lp ℂ 2 (gwLaw d), Tendsto (fun L : ℕ =>
      ‖(((kappa d t δ).toReal : ℂ)⁻¹ ^ L) • ((transferOp d t δ) ^ L) (oneL2 d) - g‖) atTop (𝓝 0)
  then h.choose else 0

end BetheKS


