-- Prove2me | Definitions.Def_DivQuotient_ProofObjects
-- name    : DivQuotient_ProofObjects
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:01.620991+00:00
-- url     : https://prove2.me/theorems/feadec23-a295-43d8-b16a-3faa71212bcb
-- title:
--   The map $R$ of (EC.1), the acceptance sets $\mathcal A_\beta$, the risk measures $\rho_\beta$ and $r^{\mathbf X}_\beta$
-- statement:
--   Objects built in the proofs of Theorems 1 and 2. Fix a risk measure $\phi$ and an index $D:\mathcal X^n\to\overline{\mathbb R}$, and write $\mathbf X_\phi=(X_1-\phi(X_1),\dots,X_n-\phi(X_n))$.
--
--   1. (EC.1) $R:\mathcal X\to\overline{\mathbb R}$, $R(X)=\inf\{D(\mathbf Y):X\le S(\mathbf Y_\phi),\ \mathbf Y\in\mathcal X^n\}$, with $\inf\varnothing=\infty$.
--   2. $\mathcal A_\beta=\{X\in\mathcal X:R(X)\le\beta\}$.
--   3. $\rho_\beta(X)=\inf\{m\in\mathbb R:X-m\in\mathcal A_\beta\}$, a value in $[-\infty,\infty]$.
--   4. For a real-valued class $(\rho_\beta)$, a level $\alpha$, $\mathbf X\in\mathcal X^n$ and weights $\mathbf w$:
--   $$
--   r^{\mathbf X}_\beta(\mathbf w)=\rho_\beta\Big(\sum_{i=1}^n w_iX_i\Big)-\sum_{i=1}^n\rho_\alpha(w_iX_i).
--   $$
--
--   The proof of Theorem 1 shows that $D$ is recovered from the class $(\rho_\beta)$ through eq. (3).
--
--   **Formalization Note** The infima are `EReal` infima, equal to $+\infty$ on the empty set. The page writes the bound variable of (EC.1) as $\mathbf X$; here it is $\mathbf Y$.
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, proof of Theorem 1, (EC.1) and the definitions of 𝒜_β and ρ_β, p.34; proof of Theorem 2, r^X_β, p.36

import Mathlib
import Definitions.Def_DivQuotient_Axioms

open MeasureTheory

namespace DivQuotient

/-! Objects built in the proofs of Theorems 1 and 2, arXiv:2206.13679v6, pp.33–37. -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}

/-- The centred portfolio `X_φ = (X₁ − φ(X₁), …, Xₙ − φ(Xₙ))` (arXiv:2206.13679v6, p.33). -/
def phiCenter (φ : Lp ℝ ⊤ P → ℝ) (X : Fin n → Lp ℝ ⊤ P) : Fin n → Lp ℝ ⊤ P :=
  fun i => X i - Lp.const ⊤ P (φ (X i))

/-- The auxiliary map (EC.1) (arXiv:2206.13679v6, p.34):
`R(X) = inf{D(Y) : X ≤ S(Y_φ), Y ∈ 𝒳ⁿ}`, with `inf ∅ = ∞`.

**Formalization Note.** The infimum is the `EReal` infimum `⨅`, which is `⊤` on the empty set.
The page writes the bound variable as `X` and the infimand as `D(X)`; here it is `Y`. -/
noncomputable def Rmap (φ : Lp ℝ ⊤ P → ℝ) (D : (Fin n → Lp ℝ ⊤ P) → EReal)
    (X : Lp ℝ ⊤ P) : EReal :=
  ⨅ (Y : Fin n → Lp ℝ ⊤ P) (_ : X ≤ S (phiCenter φ Y)), D Y

/-- The acceptance set `𝒜_β = {X ∈ 𝒳 : R(X) ≤ β}` (arXiv:2206.13679v6, p.34). -/
def acceptSet (φ : Lp ℝ ⊤ P → ℝ) (D : (Fin n → Lp ℝ ⊤ P) → EReal) (β : ℝ) :
    Set (Lp ℝ ⊤ P) :=
  {X | Rmap φ D X ≤ (β : EReal)}

/-- The constructed risk measures `ρ_β(X) = inf{m ∈ ℝ : X − m ∈ 𝒜_β}`
(arXiv:2206.13679v6, p.34).

**Formalization Note.** The infimum is taken in `EReal` (`⊤` on the empty set); it may be `−∞`
(`⊥`). -/
noncomputable def rhoBeta (φ : Lp ℝ ⊤ P → ℝ) (D : (Fin n → Lp ℝ ⊤ P) → EReal) (β : ℝ)
    (X : Lp ℝ ⊤ P) : EReal :=
  ⨅ (m : ℝ) (_ : X - Lp.const ⊤ P m ∈ acceptSet φ D β), (m : EReal)

/-- The function `r^X_β(w) = ρ_β(∑ wᵢXᵢ) − ∑ ρ_α(wᵢXᵢ)` on `Δₙ` (arXiv:2206.13679v6, p.36),
for a real-valued class `ρ`. -/
def rFun (ρ : ℝ → Lp ℝ ⊤ P → ℝ) (α β : ℝ) (X : Fin n → Lp ℝ ⊤ P) (w : Fin n → ℝ) : ℝ :=
  ρ β (∑ i, w i • X i) - ∑ i, ρ α (w i • X i)

end DivQuotient


