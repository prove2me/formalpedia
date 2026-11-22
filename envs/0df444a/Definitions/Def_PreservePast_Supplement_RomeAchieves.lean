-- Prove2me | Definitions.Def_PreservePast_Supplement_RomeAchieves
-- name    : PreservePast_Supplement_RomeAchieves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:26:36.019122+00:00
-- url     : https://prove2.me/theorems/8274fd5e-2afc-477e-a009-fd6e92c52b4d
-- title:
--   The ROME covariance $C_Z$, the equality-constrained oracle and $B$-bit protocols for the covariance edit
-- statement:
--   Fix $0<c<1$, $1\le k\le d$. For $Z\in\mathbb R^{k\times d}$ with $ZZ^\top=I_k$ the **ROME covariance** is
--   $$C_Z=\begin{pmatrix} I_k & cZ\\ cZ^\top & I_d\end{pmatrix},$$
--   the old-loss increment of an update $H\in\mathbb R^{m\times(k+d)}$ is $J_C(H)=\tfrac12\operatorname{tr}(HCH^\top)$, and the **oracle** of the edit $Ha=y$ is
--   $$H^\ast=\frac{y\,(C^{-1}a)^\top}{a^\top C^{-1}a}.$$
--   After $Z$ is encoded, a query gives $a=(v,0)$ with $v\in S^{k-1}$ and $y\in S^{m-1}$ and asks for $H$ with
--   $$Ha=y,\qquad \operatorname{rank}H\le r,\qquad \|H\|_F\le R,\qquad J_{C_Z}(H)-J_{C_Z}(H^\ast)\le\varepsilon .$$
--   A $B$-bit retained-state protocol **achieves** this with failure probability $\delta$ if, for every fixed history and query, the first three conditions hold on every outcome and the regret bound holds with probability at least $1-\delta$. $B^\ast_{\mathrm{ROME}}$ is the least such width.
--
--   **Formalization Note** Inputs are indexed by `Fin k ⊕ Fin d`. The norm constraint is written $\sum_{ij}H_{ij}^2\le R^2$ for $R\ge0$.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Appendix O, p.70 (PDF p.72), eqs. (255)–(258)

import Mathlib

open MeasureTheory Matrix

namespace PreservePast.Supplement

/-- **The ROME covariance** (257), p.70 (PDF p.72): `C_Z = [[I_k, cZ], [cZᵀ, I_d]]` for
`Z ∈ ℝ^{k×d}`, a matrix on the input coordinates `Fin k ⊕ Fin d`. P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Appendix O. -/
def romeCov {k d : ℕ} (c : ℝ) (Z : Matrix (Fin k) (Fin d) ℝ) :
    Matrix (Fin k ⊕ Fin d) (Fin k ⊕ Fin d) ℝ :=
  Matrix.fromBlocks 1 (c • Z) (c • Zᵀ) 1

/-- **The old-loss increment** (255), p.70: `J_C(H) = ½ tr(H C Hᵀ)`. -/
noncomputable def romeLoss {m : ℕ} {ι : Type} [Fintype ι] (C : Matrix ι ι ℝ)
    (H : Matrix (Fin m) ι ℝ) : ℝ :=
  (1 / 2) * Matrix.trace (H * C * Hᵀ)

/-- **The oracle of the equality-constrained edit** (256), p.70: for positive-definite `C`,
`H* = y (C⁻¹a)ᵀ / (aᵀC⁻¹a)`, the unique minimizer of `J_C` subject to `Ha = y`. -/
noncomputable def romeOracle {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℝ)
    (a : ι → ℝ) (y : Fin m → ℝ) : Matrix (Fin m) ι ℝ :=
  Matrix.of fun i j => y i * (C⁻¹ *ᵥ a) j / (a ⬝ᵥ (C⁻¹ *ᵥ a))

/-- **A B-bit retained-state protocol for the ROME covariance edit** (the contract of `B*_ROME`
in Theorem 21). P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Appendix O, p.70 (PDF p.72), (257)–(258): histories are the `Z ∈ ℝ^{k×d}`
with `ZZᵀ = I_k`; "After encoding, a query gives a = (v, 0), v ∈ S^{k−1}, and y ∈ S^{m−1}, and asks
for Ha = y, rank H ≤ r, ‖H‖_F ≤ R, J_{C_Z}(H) − J_{C_Z}(H*) ≤ ε"; "Under Section N's fixed-query
convention": regret at most `ε` with probability `1 − δ` for each fixed history and query, and
feasibility on every outcome.

**Formalization Note.** One coin space; the encoder sees `Z` and the coins, the decoder the
message, the coins and the query `(v, y)`. Exact fit, rank and norm hold for every coin value;
the regret bound holds with probability `≥ 1 − δ`. `‖H‖_F ≤ R` is written
`Σ H_ij² ≤ R²` with `0 ≤ R`. -/
def RomeAchieves {k d m B : ℕ} {Ω : Type*} [MeasurableSpace Ω] (c : ℝ) (r : ℕ) (R ε δ : ℝ)
    (P : Measure Ω) (enc : Matrix (Fin k) (Fin d) ℝ → Ω → Fin (2 ^ B))
    (dec : Fin (2 ^ B) → Ω → (Fin k → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin k ⊕ Fin d) ℝ) :
    Prop :=
  IsProbabilityMeasure P ∧ (∀ Z, Measurable (enc Z)) ∧
    (∀ M v y, Measurable (fun ω => Matrix.of.symm (dec M ω v y))) ∧
    ∀ Z : Matrix (Fin k) (Fin d) ℝ, Z * Zᵀ = 1 →
      ∀ (v : Fin k → ℝ) (y : Fin m → ℝ), ∑ i, v i ^ 2 = 1 → ∑ i, y i ^ 2 = 1 →
        (∀ ω, dec (enc Z ω) ω v y *ᵥ (Sum.elim v 0) = y ∧ (dec (enc Z ω) ω v y).rank ≤ r ∧
          ∑ i, ∑ j, dec (enc Z ω) ω v y i j ^ 2 ≤ R ^ 2) ∧
        ENNReal.ofReal (1 - δ) ≤
          P {ω | romeLoss (romeCov c Z) (dec (enc Z ω) ω v y) -
            romeLoss (romeCov c Z) (romeOracle (romeCov c Z) (Sum.elim v 0) y) ≤ ε}

end PreservePast.Supplement


