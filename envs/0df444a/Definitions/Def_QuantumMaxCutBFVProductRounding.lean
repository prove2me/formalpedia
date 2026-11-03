-- Prove2me | Definitions.Def_QuantumMaxCutBFVProductRounding
-- name    : QuantumMaxCutBFVProductRounding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-02T14:43:32.07791+00:00
-- url     : https://prove2.me/theorems/300e70c5-d5ae-4725-8938-3813040b464d
-- title:
--   Per-edge product/matching energy model of the 0.614 quantum max-cut algorithm (BFV hypergeometric $F$, MATCH and PMATCH ratios)
-- statement:
--   **The one-edge energy model of the $0.614$ quantum max-cut analysis** (ALMPS25, arXiv:2504.15276, Section 4.2).
--
--   Let $\rho$ be a (relaxed) $n$-qubit state and fix an edge $\{i,j\}$ of the instance graph. Two real numbers
--   describe the edge:
--
--   * the *Pauli correlation* $s=\tfrac13\operatorname{Tr}\big[(X_iX_j+Y_iY_j+Z_iZ_j)\rho\big]$, and
--   * the *energy* $\operatorname{Tr}[h^{QM}_{ij}\rho]$ against the quantum max-cut edge Hamiltonian
--     $h^{QM}_{ij}=\tfrac12(1-X_iX_j-Y_iY_j-Z_iZ_j)$,
--
--   which are related by $g=\operatorname{Tr}[h^{QM}_{ij}\rho]=\tfrac12(1-3s)$. The level-2 (Pauli-moment)
--   SDP certifies $\sum_e w_e g_e \ge \lambda_{\max}(H_G)$, so $\tfrac12(1-3s)$ is a per-edge *upper*
--   bound on the contribution of an edge, and a rounding algorithm with per-edge expected energy $a(s)$
--   has per-edge ratio $a(s)/\big(\tfrac12(1-3s)\big)=2a(s)/(1-3s)$.
--
--   This definition file fixes the four objects that the analysis manipulates:
--
--   1. `BFVBound.F s`, the **product-state expectation** of the GP19/BFV10 rounding. It is
--      $$F(s)=c\,s\,G(s^2),\qquad c=\frac{2}{3}\Big(\frac{\Gamma(2)}{\Gamma(3/2)}\Big)^2=\frac{8}{3\pi},$$
--      where $G={}_2F_1(\tfrac12,\tfrac12;2;\,\cdot\,)=\sum_n a_n x^n$ is the Gauss hypergeometric function with
--      $a_n=\big((\tfrac12)_n\big)^2/\big((2)_n\,n!\big)$ (ALMPS25 Eq. (17), PT22 Eq. (3), BFV10). Expanding,
--      $F(s)=0.8488\,s+0.1061\,s^3+O(s^5)$.
--   2. `QMC0614.EM d s`, the **MATCH** energy divided by the SDP bound, for a matching-polytope weight $d$:
--      $$E_M(s)=\frac{1+3d\,\bigl[-\tfrac{1+3s}{2}\bigr]^+}{1-3s}.$$
--   3. `QMC0614.EPM d σ s`, the **PMATCH** energy divided by the SDP bound, at partial-entanglement angle
--      $\theta$ written through $\sigma=\sin\theta$ (so $\cos^2\theta=1-\sigma^2$):
--      $$E_{PM}(\sigma,s)=\frac{1-F(s)\cos^2\theta+d\,\sigma\bigl(1-F(s)(1+\sigma)\bigr)\bigl[-\tfrac{1+3s}{2}\bigr]^+}{1-3s}.$$
--   4. `QMC0614.mixture d μ σ s`, the mixture $\mu E_{PM}+(1-\mu)E_M$ whose infimum over $s$ is the certified
--      approximation ratio of ALMPS25 Eq. (19), "best of MATCH and PMATCH".
--
--   The bracket $[x]^+=\max x\,0$ is the rescaled matching weight of GSS25 Lemma 3.4/3.10; it vanishes exactly on
--   $s\ge-1/3$, where the parallel part of the two algorithms' rounding coincides.
-- source:
--   Anshu, Lee, Mousavi, Parekh, Soleimanifar, arXiv:2504.15276 (ESA 2025), Section 4.2, Eqs. (17), (20), (21) and (19); F from PT22 Eq. (3) and Brandao-Fernandes-Vallentin arXiv:0910.5765; matching polytope weights from GSS25 arXiv:2504.11120 Lemma 3.4/3.10.

import Mathlib

set_option autoImplicit false

/-!
# The product/matching per-edge energy model of the 0.614 quantum max-cut analysis

This file fixes the one-edge model that the ALMPS25 (arXiv:2504.15276, Section 4.2) analysis of
quantum max-cut works with, in the normalization of the platform's campaign
`QuantumMaxCutEnergy.exists_approximation`.

For an edge `(i,j)` put `s = (1/3) Tr[(X_iX_j + Y_iY_j + Z_iZ_j) ρ]`, the *Pauli correlation* of a
(relaxed) state. The level-two (Pauli-moment) SDP upper bound on the edge's contribution is then
`(1 - 3 s)/2`, and the two algorithms' per-edge energies, divided by that bound, are:

* `EM d s` — MATCH, with a matching-polytope weight `d` (ALMPS25 Eq. (21));
* `EPM d σ s` — PMATCH with `σ = sin θ`, `θ ∈ [0, π/2]` the partial-entanglement angle
  (ALMPS25 Eq. (20)); note `cos²θ = 1 - σ²`.

The product side of PMATCH enters through `F s`, the BFV rank-three product expectation
(`F s = (8/(3π)) s G(s²)`, `G = ₂F₁(1/2,1/2;2;·)`): the rounding of GP19/BFV10 has expected edge
correlation `E[t_ij] = F(s_ij)`. Up to the sign convention `t_ij = 1` on an untangled edge, `F` is
the `c · s · G(s²)` of ALMPS25 Eq. (17).

Only definitions live here; all bounds on `F` and the three-parameter min-max endgame (ALMPS25
Eq. (19)) are separate theorem nodes.
-/

noncomputable section
open scoped BigOperators

namespace BFVBound

/-- Rising factorial (Pochhammer symbol) `(a)_n = a (a+1) ⋯ (a+n-1)`, in `ℝ`. -/
def poch (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => poch a n * (a + n)

/-- Coefficients of `₂F₁(1/2,1/2;2;x)`: `aₙ = ((1/2)ₙ)^2 / ((2)ₙ · n!)`. -/
def coeff (n : ℕ) : ℝ := (poch (1 / 2) n) ^ 2 / (poch 2 n * (n.factorial : ℝ))

/-- The Gauss hypergeometric series `G x = ₂F₁(1/2,1/2;2;x) = ∑ₙ aₙ xⁿ`. -/
def G (x : ℝ) : ℝ := ∑' n, coeff n * x ^ n

/-- `F s = (8/(3π)) · s · G(s²)`: the expected product-state edge correlation at Pauli
correlation `s` (BFV10; the `F` of ALMPS25 Eq. (17) and PT22 Eq. (3)). -/
def F (s : ℝ) : ℝ := (8 / (3 * Real.pi)) * s * G (s ^ 2)

end BFVBound

namespace QMC0614

open BFVBound

/-- MATCH energy divided by the SDP bound, on one edge with Pauli correlation `s` and
matching-polytope weight `d` (ALMPS25 Eq. (21)):
`EM s = (1 + 3 d [-(1+3s)/2]⁺) / (1 - 3s)`. -/
def EM (d s : ℝ) : ℝ := (1 + 3 * d * max (-(1 + 3 * s) / 2) 0) / (1 - 3 * s)

/-- PMATCH energy divided by the SDP bound, on one edge with Pauli correlation `s`, weight `d`
and `σ = sin θ` (ALMPS25 Eq. (20)):

`EPM σ s = (1 - F s (1 - σ²) + d σ (1 - F s (1 + σ)) [-(1+3s)/2]⁺) / (1 - 3s)`. -/
def EPM (d σ s : ℝ) : ℝ :=
  (1 - F s * (1 - σ ^ 2) + d * σ * (1 - F s * (1 + σ)) * max (-(1 + 3 * s) / 2) 0) /
    (1 - 3 * s)

/-- The two-algorithm mixture of ALMPS25 Eq. (19): `μ` on PMATCH, `1 - μ` on MATCH. -/
def mixture (d μ σ s : ℝ) : ℝ := μ * EPM d σ s + (1 - μ) * EM d s

end QMC0614


