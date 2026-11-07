-- Prove2me | Definitions.Def_LIPAlgorithm_heatDelta
-- name    : LIPAlgorithm_heatDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:48.653205+00:00
-- url     : https://prove2.me/theorems/e7abcc05-bf72-43cd-9387-cbce661d99e2
-- title:
--   The Gaussian heat increment and the collision scale
-- statement:
--   With $\gamma_a$ the Gaussian of density $a^{-n}\rho_a$ on $\mathbb R^n$, the heat increment of $h_j$ at $w$ is
--
--   $$\Delta_j(w)=\mathbb E_{G_t\sim\gamma_t}[h_j(w+G_t)]-\mathbb E_{G_{t/2}\sim\gamma_{t/2}}[h_j(w+G_{t/2})].$$
--
--   The discrete Gaussian $D_{L^*,s}$ has mass $\rho_s(x)/\rho_s(L^*)$ at $x\in L^*$, and its collision scale is $S_2(D_{L^*,s})=(\sum_x \Pr[X=x]^2)^{-1}$. The standing parameters are $s=Cn^2\log n/\lambda$ and $t=8\sqrt n/\lambda$.
--
--   The increment compares a convex function at two heat scales: it is large at ambiguous ranks and small on average, which bounds the ambiguity of a random marker.
--
--   **Formalization Note** The Gaussian, the dual and the discrete Gaussian are published $\texttt{RegevLWE}$ definitions. Logarithms in $s$ have base $2$.
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Definition 2.13, p.13; Definition 4.2, p.21; §4, pp.21–22; §6.3, p.34

import Mathlib
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_LIPAlgorithm_Resolved

namespace LIPAlgorithm

/-- `E_{G_a ∼ γ_a}[h_j(w + G_a)]`, where `γ_a` has density `a^{-n}ρ_a` (Definition 2.13, p.13). -/
noncomputable def heatMean {n : ℕ} (L : Submodule ℤ (E n)) (j : ℕ) (w : E n) (a : ℝ) : ℝ :=
  ∫ g : E n, supportH L j (w + g) * RegevLWE.GaussConv.nu a g

/-- The Gaussian heat increment `Δ_j(w) = E[h_j(w + G_t)] − E[h_j(w + G_{t/2})]` (Definition 4.2, p.21).

**Formalization Note.** For a lattice `h_j` grows at most linearly and `γ_a` is a Gaussian, so these Bochner
integrals are integrals of integrable functions and no default value occurs. -/
noncomputable def heatDelta {n : ℕ} (L : Submodule ℤ (E n)) (j : ℕ) (t : ℝ) (w : E n) : ℝ :=
  heatMean L j w t - heatMean L j w (t / 2)

/-- `Pr_{W ∼ D_{L*,s}}[W ∈ S]`, with the published discrete Gaussian (Definition 2.13, p.13). -/
noncomputable def gaussProb {n : ℕ} (L : Submodule ℤ (E n)) (s : ℝ)
    (S : Set (RegevLWE.GaussConv.dual L)) : ℝ :=
  ∑' w : RegevLWE.GaussConv.dual L,
    S.indicator (RegevLWE.Hyperplane.discreteGaussian (RegevLWE.GaussConv.dual L) s) w

/-- `E_{W ∼ D_{L*,s}}[f(W)]` (Definition 2.13, p.13). -/
noncomputable def gaussExp {n : ℕ} (L : Submodule ℤ (E n)) (s : ℝ) (f : E n → ℝ) : ℝ :=
  ∑' w : RegevLWE.GaussConv.dual L,
    RegevLWE.Hyperplane.discreteGaussian (RegevLWE.GaussConv.dual L) s w * f w

/-- `s = C·n²·log n/λ₁(L)` (§4, p.21; Theorem 4.6, p.24).

**Formalization Note.** The logarithm has base `2`. The paper names no base; a change of base only rescales
`C` in `s`, and base `2` gives the smaller threshold `r*(n)` of Corollary 4.7. -/
noncomputable def scaleS {n : ℕ} (C : ℝ) (L : Submodule ℤ (E n)) : ℝ :=
  C * (n : ℝ) ^ 2 * Real.logb 2 n / RegevLWE.SmoothingLB.lambda1 L

/-- `t = 8√n/λ` (§4.2, p.22). -/
noncomputable def scaleT {n : ℕ} (L : Submodule ℤ (E n)) : ℝ :=
  8 * Real.sqrt n / RegevLWE.SmoothingLB.lambda1 L

/-- The collision scale `S₂(D_{L*,s}) = (∑_{x ∈ L*} Pr[X = x]²)⁻¹` (§6.3, p.34). -/
noncomputable def collisionScale {n : ℕ} (L : Submodule ℤ (E n)) (s : ℝ) : ℝ :=
  (∑' x : RegevLWE.GaussConv.dual L,
    RegevLWE.Hyperplane.discreteGaussian (RegevLWE.GaussConv.dual L) s x ^ 2)⁻¹

end LIPAlgorithm


