-- Prove2me | Definitions.Def_DivQuotient_RiskMeasure
-- name    : DivQuotient_RiskMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:51:42.058041+00:00
-- url     : https://prove2.me/theorems/2e0042de-5422-487a-a225-eb376279554b
-- title:
--   Risk measures on $L^\infty$: monotone, constant additive, positively homogeneous, subadditive; MCP, coherent, sub-linear, linear
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $\mathcal X=L^\infty$ the space of essentially bounded random variables, almost surely equal variables being identified. A value $X>0$ is a loss. A **risk measure** is a map $\phi:\mathcal X\to\mathbb R$. It may have the properties
--
--   1. [M] *monotonicity*: $\phi(X)\le\phi(Y)$ whenever $X\le Y$;
--   2. [CA] *constant additivity*: $\phi(X+c)=\phi(X)+c$ for all $c\in\mathbb R$;
--   3. [PH] *positive homogeneity*: $\phi(\lambda X)=\lambda\phi(X)$ for all $\lambda>0$;
--   4. [SA] *subadditivity*: $\phi(X+Y)\le\phi(X)+\phi(Y)$.
--
--   $\phi$ is **MCP** if it satisfies [M], [CA] and [PH]; **coherent** if it satisfies all four; **sub-linear** if it satisfies [SA] and [PH]; and **linear** if $\phi(aX+bY)=a\phi(X)+b\phi(Y)$ for all $X,Y\in\mathcal X$ and $a,b\in\mathbb R$.
--
--   An **extended MCP risk measure** is a map $\rho:\mathcal X\to[-\infty,\infty)$ satisfying [M], [CA] and [PH] in the extended reals. It is used only for the corrected Theorem 1, where some members of a class can be identically $-\infty$.
--
--   These are the risk measures on which the diversification quotient is built.
--
--   **Formalization Note** $\mathcal X$ is `Lp ℝ ⊤ P`: classes of almost-everywhere-equal functions, with the almost-sure order and the essential-supremum norm. The constant $c$ is `Lp.const ⊤ P c`. Extended values live in `EReal`, where $-\infty+c=-\infty$ and $\lambda\cdot(-\infty)=-\infty$ for $\lambda>0$; the extended class excludes $+\infty$.
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, Notation p.4; §2 pp.5–6 ([M], [CA], [PH], [SA], MCP, coherent); §3.3 pp.10–11 (linear, sub-linear)

import Mathlib

open MeasureTheory

namespace DivQuotient

/-! Risk measures on `L∞` and their properties [M], [CA], [PH], [SA].
Han–Lin–Wang, *Diversification quotients: Quantifying diversification via risk measures*,
arXiv:2206.13679v6, Notation p.4, §2 pp.5–6, §3.3 pp.10–11. -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **[M] Monotonicity** (arXiv:2206.13679v6, p.5): `φ(X) ≤ φ(Y)` whenever `X ≤ Y`.

**Formalization Note.** `𝒳 = L∞` (§3, p.7) is `Lp ℝ ⊤ P`, the space of almost-surely-equal
classes of essentially bounded random variables ("almost surely equal random variables are
treated as identical", p.4). Its order is the almost-sure order. -/
def IsMonotoneRisk (φ : Lp ℝ ⊤ P → ℝ) : Prop :=
  ∀ X Y : Lp ℝ ⊤ P, X ≤ Y → φ X ≤ φ Y

/-- **[CA] Constant additivity** (arXiv:2206.13679v6, p.6): `φ(X + c) = φ(X) + c` for all
`c ∈ ℝ`. The constant `c` is the class `Lp.const ⊤ P c`. -/
def IsCashAdditive (φ : Lp ℝ ⊤ P → ℝ) : Prop :=
  ∀ (X : Lp ℝ ⊤ P) (c : ℝ), φ (X + Lp.const ⊤ P c) = φ X + c

/-- **[PH] Positive homogeneity** (arXiv:2206.13679v6, p.6): `φ(λX) = λφ(X)` for all `λ > 0`. -/
def IsPosHomogeneous (φ : Lp ℝ ⊤ P → ℝ) : Prop :=
  ∀ (l : ℝ) (X : Lp ℝ ⊤ P), 0 < l → φ (l • X) = l * φ X

/-- **[SA] Subadditivity** (arXiv:2206.13679v6, p.6): `φ(X + Y) ≤ φ(X) + φ(Y)`. -/
def IsSubadditive (φ : Lp ℝ ⊤ P → ℝ) : Prop :=
  ∀ X Y : Lp ℝ ⊤ P, φ (X + Y) ≤ φ X + φ Y

/-- **MCP risk measure** (arXiv:2206.13679v6, p.6): [M], [CA] and [PH]. A risk measure is a
map `𝒳 → ℝ` (p.4), so it is real valued. -/
def IsMCP (φ : Lp ℝ ⊤ P → ℝ) : Prop :=
  IsMonotoneRisk φ ∧ IsCashAdditive φ ∧ IsPosHomogeneous φ

/-- **Coherent risk measure** (Artzner et al.; arXiv:2206.13679v6, pp.5–6): [M], [CA], [PH]
and [SA]. -/
def IsCoherent (φ : Lp ℝ ⊤ P → ℝ) : Prop :=
  IsMCP φ ∧ IsSubadditive φ

/-- **Sub-linear risk measure** (arXiv:2206.13679v6, p.11): [SA] and [PH]. -/
def IsSublinear (φ : Lp ℝ ⊤ P → ℝ) : Prop :=
  IsSubadditive φ ∧ IsPosHomogeneous φ

/-- **Linear risk measure** (arXiv:2206.13679v6, p.10): `φ(aX + bY) = aφ(X) + bφ(Y)` for all
`X, Y ∈ 𝒳` and all `a, b ∈ ℝ`. "Non-linear" is `¬ IsLinear φ`. -/
def IsLinear (φ : Lp ℝ ⊤ P → ℝ) : Prop :=
  ∀ (X Y : Lp ℝ ⊤ P) (a b : ℝ), φ (a • X + b • Y) = a * φ X + b * φ Y

/-- **Extended-valued MCP risk measure** (used only for the corrected Theorem 1,
arXiv:2206.13679v6, p.10): `ρ : 𝒳 → [−∞, ∞)` never takes the value `+∞` and satisfies [M],
[CA] and [PH], read in `EReal`.

**Formalization Note.** The paper's risk measures are real valued (p.4). The proof of
Theorem 1 (p.34) builds `ρ_β(X) = inf{m : X − m ∈ 𝒜_β}`, which can be `−∞`; this predicate is
the class needed for that construction (correction C1 of the mission). For a real-valued `φ`,
`IsExtMCP (fun X => (φ X : EReal))` is equivalent to `IsMCP φ`. In `EReal`, `⊥ + c = ⊥` and
`l * ⊥ = ⊥` for `l > 0`, so the value `−∞` is compatible with [CA] and [PH]. -/
def IsExtMCP (ρ : Lp ℝ ⊤ P → EReal) : Prop :=
  (∀ X, ρ X ≠ ⊤) ∧
  (∀ X Y : Lp ℝ ⊤ P, X ≤ Y → ρ X ≤ ρ Y) ∧
  (∀ (X : Lp ℝ ⊤ P) (c : ℝ), ρ (X + Lp.const ⊤ P c) = ρ X + (c : EReal)) ∧
  (∀ (l : ℝ) (X : Lp ℝ ⊤ P), 0 < l → ρ (l • X) = (l : EReal) * ρ X)

end DivQuotient


