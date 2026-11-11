-- Prove2me | Definitions.Def_PriceCapacities_LowerBound_Fourier
-- name    : PriceCapacities_LowerBound_Fourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:21:34.682273+00:00
-- url     : https://prove2.me/theorems/9e06ae0b-7b62-44d8-8f42-0a12a42b0b60
-- title:
--   Fourier analysis on $\{-1,1\}^d$: inner product, parities $\chi_S$, coefficients $\hat g(S)$, least singular value (Appendix B)
-- statement:
--   The hypercube $\{-1,1\}^d$ consists of the sign vectors $y=(y_1,\dots,y_d)$. Real functions on it form the space $F_d$ with inner product and norm
--   $$\langle g,h\rangle=\frac1{2^d}\sum_{y\in\{-1,1\}^d}g(y)h(y),\qquad \|g\|_2=\langle g,g\rangle^{1/2}.$$
--   For $S\subseteq[d]$ the **parity function** is $\chi_S(y)=\prod_{j\in S}y_j$ ($\chi_\emptyset=1$), and the **Fourier coefficient** of $g$ at $S$ is $\hat g(S)=\langle g,\chi_S\rangle$; $|S|$ is its level. For sign vectors $y,u$, $y\odot u=(y_1u_1,\dots,y_du_d)$ is the coordinatewise product, and $-y$ reverses all signs. For a real $N\times N$ matrix $M$ ($N\ge1$) the **least singular value** is
--   $$s_{\min}(M)=\min_{\|v\|_2=1}\|Mv\|_2 .$$
--
--   **Formalization Note.** `Cube d = Fin d → ℤˣ` (ℤˣ = {1, −1}); `sgn` sends a sign to $\pm1\in\mathbb R$; $y\odot u$ is the pointwise product `y * u` and $-y$ the pointwise negation. `cubeInner`, `cubeNorm`, `parity S`, `fourierCoeff g S` are the objects above. `leastSingularValue M` is the infimum of $\|Mv\|_2$ over the unit sphere of $\mathbb R^N$ (nonempty and compact for $N\ge1$, so it is the minimum, which equals the smallest singular value of a square matrix).
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), pp. 61–62, Appendix B; p. 62, Proposition B.3 (s_min)

import Mathlib

open scoped BigOperators

namespace PriceCapacities.LowerBound

/-!
# Fourier analysis on the hypercube `{−1, 1}^d` (Appendix B)

Prabhu, Schwiegelshohn, Shyam, *The Price of Capacities for Clustering Coresets*, STOC 2027
submission (manuscript sha256 ec35f5ef…), p. 61, Appendix B; p. 62, Proposition B.3.

* `Cube d = Fin d → ℤˣ` is `{−1, 1}^d` (`ℤˣ = {1, −1}`); `sgn s ∈ {±1} ⊂ ℝ`. The coordinatewise
  product `y ⊙ u` is the pointwise product `y * u`, and `−y` is the pointwise negation.
* `F_d` is the space `Cube d → ℝ`; `cubeInner g h = 2^{−d} Σ_y g(y) h(y)`, `cubeNorm g = ⟨g, g⟩^{1/2}`.
* `parity S y = χ_S(y) = Π_{j ∈ S} y_j` (`χ_∅ = 1`); `fourierCoeff g S = ĝ(S) = ⟨g, χ_S⟩`.
* `leastSingularValue M` for a square real matrix `M` of size `N ≥ 1` is
  `s_min(M) = min_{‖v‖₂ = 1} ‖M v‖₂`, written as an infimum over the (nonempty, compact) unit
  sphere; the values are `≥ 0`. For `N = 0` it is `0` (never used).
-/

/-- The hypercube `{−1, 1}^d`. -/
abbrev Cube (d : ℕ) : Type := Fin d → ℤˣ

/-- A sign `±1` as a real number. -/
def sgn (s : ℤˣ) : ℝ := ((s : ℤ) : ℝ)

/-- The inner product `⟨g, h⟩ = 2^{−d} Σ_y g(y) h(y)` on `F_d`. -/
noncomputable def cubeInner {d : ℕ} (g h : Cube d → ℝ) : ℝ :=
  ((2 : ℝ) ^ d)⁻¹ * ∑ y : Cube d, g y * h y

/-- The norm `‖g‖₂ = ⟨g, g⟩^{1/2}`. -/
noncomputable def cubeNorm {d : ℕ} (g : Cube d → ℝ) : ℝ :=
  Real.sqrt (cubeInner g g)

/-- The parity function `χ_S(y) = Π_{j ∈ S} y_j`. -/
def parity {d : ℕ} (S : Finset (Fin d)) (y : Cube d) : ℝ :=
  ∏ j ∈ S, sgn (y j)

/-- The Fourier coefficient `ĝ(S) = ⟨g, χ_S⟩`. -/
noncomputable def fourierCoeff {d : ℕ} (g : Cube d → ℝ) (S : Finset (Fin d)) : ℝ :=
  cubeInner g (parity S)

/-- The least singular value `s_min(M) = min_{‖v‖₂ = 1} ‖M v‖₂` of a square real matrix. -/
noncomputable def leastSingularValue {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ⨅ v : {v : Fin N → ℝ // ∑ i, v i ^ 2 = 1}, Real.sqrt (∑ i, (M.mulVec v.1 i) ^ 2)

end PriceCapacities.LowerBound


