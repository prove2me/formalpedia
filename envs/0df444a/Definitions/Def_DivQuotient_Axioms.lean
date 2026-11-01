-- Prove2me | Definitions.Def_DivQuotient_Axioms
-- name    : DivQuotient_Axioms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:14.417099+00:00
-- url     : https://prove2.me/theorems/9396b694-2345-4a91-b29b-e259f73e5152
-- title:
--   Diversification indices and the axioms [+], [LI], [SI], [R]$_\phi$, [N]$_\phi$, [C]$_\phi$, [PC]
-- statement:
--   Fix $n\ge1$ assets. A **diversification index** is a map $D:\mathcal X^n\to\overline{\mathbb R}=[-\infty,\infty]$, where $\mathcal X=L^\infty$. Write $S(\mathbf X)=\sum_{i=1}^n X_i$. For a risk measure $\phi$, two vectors are **$\phi$-marginally equivalent**, $\mathbf X\overset{m}{\simeq}\mathbf Y$, if $\phi(X_i)=\phi(Y_i)$ for each $i$. The axioms are:
--
--   1. [+] $D(\mathbf X)\ge0$ for all $\mathbf X$.
--   2. [LI] $D(\mathbf X+\mathbf c)=D(\mathbf X)$ for all $\mathbf c\in\mathbb R^n$.
--   3. [SI] $D(\lambda\mathbf X)=D(\mathbf X)$ for all $\lambda>0$.
--   4. [R]$_\phi$ $D(\mathbf X)\le D(\mathbf Y)$ whenever $\mathbf X\overset{m}{\simeq}\mathbf Y$ and $S(\mathbf X)\le S(\mathbf Y)$.
--   5. [N]$_\phi$ $D(\mathbf 0)=0$; $D(X,\dots,X)\le1$ for every duplicate portfolio; and $D(\mathbf Y)\ge1$ whenever $\mathbf Y$ is **worse than duplicate**, i.e. there is $X\in\mathcal X$ with $\phi(Y_i)<\phi(X)$ for every $i$ and $S(\mathbf Y)\ge nX$.
--   6. [C]$_\phi$ If $\mathbf Y^k\overset{m}{\simeq}\mathbf X$ for each $k$ and $\|(S(\mathbf X)-S(\mathbf Y^k))_+\|_\infty\to0$, then $(D(\mathbf X)-D(\mathbf Y^k))_+\to0$.
--   7. [PC] For each $\mathbf X\in\mathcal X^n$ and $d\in\overline{\mathbb R}$, the set $\{\mathbf w\in\Delta_n: D(\mathbf w\odot\mathbf X)\le d\}$ is convex, where $\Delta_n$ is the standard simplex and $\mathbf w\odot\mathbf X=(w_1X_1,\dots,w_nX_n)$.
--
--   The file also defines the **semi-continuous form** of [C]$_\phi$: under the same hypotheses, $\liminf_k D(\mathbf Y^k)\ge D(\mathbf X)$, i.e. for every $d<D(\mathbf X)$, eventually $d<D(\mathbf Y^k)$. The printed form implies it; the corrected Theorem 1 uses it.
--
--   **Formalization Note** Vectors are `Fin n → Lp ℝ ⊤ P` (asset $i$ is index $i-1$) and $D$ is `EReal`-valued. The positive part of $D(\mathbf X)-D(\mathbf Y^k)$ is `max (D X - D (Y k)) 0` in `EReal`, where $\infty-\infty=-\infty$, so it is $0$ when both values are $+\infty$. The $L^\infty$ convergence is that of the norm of `Lp.posPart`.
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, §2 p.5 ([+], [LI], [SI]); §3.1 pp.7–8 ([R]φ, worse than duplicate, [N]φ, [C]φ); §3.2 p.9 ([PC]); p.33 (S(X))

import Mathlib
import Definitions.Def_DivQuotient_RiskMeasure

open MeasureTheory Filter Topology

namespace DivQuotient

/-! Diversification indices and the seven axioms [+], [LI], [SI], [R]φ, [N]φ, [C]φ, [PC].
Han–Lin–Wang, arXiv:2206.13679v6, §2 p.5, §3.1 pp.7–8, §3.2 p.9. -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}

/-- The total loss `S(X) = ∑ᵢ Xᵢ` of a portfolio `X ∈ 𝒳ⁿ` (arXiv:2206.13679v6, p.33).

**Formalization Note.** A portfolio is `X : Fin n → Lp ℝ ⊤ P`; asset `i` of the paper is
index `i - 1`. A diversification index is a map `D : (Fin n → Lp ℝ ⊤ P) → EReal` (`ℝ̄`, p.4). -/
def S (X : Fin n → Lp ℝ ⊤ P) : Lp ℝ ⊤ P := ∑ i, X i

/-- **φ-marginal equivalence** `X ≃ᵐ Y` (arXiv:2206.13679v6, p.7): `φ(Xᵢ) = φ(Yᵢ)` for each
`i ∈ [n]`. -/
def MargEquiv (φ : Lp ℝ ⊤ P → ℝ) (X Y : Fin n → Lp ℝ ⊤ P) : Prop :=
  ∀ i, φ (X i) = φ (Y i)

/-- **[+] Non-negativity** (arXiv:2206.13679v6, p.5): `D(X) ≥ 0` for all `X ∈ 𝒳ⁿ`. -/
def AxNonneg (D : (Fin n → Lp ℝ ⊤ P) → EReal) : Prop :=
  ∀ X, 0 ≤ D X

/-- **[LI] Location invariance** (arXiv:2206.13679v6, p.5): `D(X + c) = D(X)` for all
`c ∈ ℝⁿ`. -/
def AxLI (D : (Fin n → Lp ℝ ⊤ P) → EReal) : Prop :=
  ∀ (X : Fin n → Lp ℝ ⊤ P) (c : Fin n → ℝ), D (fun i => X i + Lp.const ⊤ P (c i)) = D X

/-- **[SI] Scale invariance** (arXiv:2206.13679v6, p.5): `D(λX) = D(X)` for all `λ > 0`. -/
def AxSI (D : (Fin n → Lp ℝ ⊤ P) → EReal) : Prop :=
  ∀ (l : ℝ) (X : Fin n → Lp ℝ ⊤ P), 0 < l → D (l • X) = D X

/-- **[R]φ Rationality** (arXiv:2206.13679v6, p.7): `D(X) ≤ D(Y)` whenever `X ≃ᵐ Y` and
`∑ Xᵢ ≤ ∑ Yᵢ`. The order is the almost-sure order of `L∞`. -/
def AxR (φ : Lp ℝ ⊤ P → ℝ) (D : (Fin n → Lp ℝ ⊤ P) → EReal) : Prop :=
  ∀ X Y : Fin n → Lp ℝ ⊤ P, MargEquiv φ X Y → S X ≤ S Y → D X ≤ D Y

/-- **Worse than duplicate** (arXiv:2206.13679v6, p.8): `Y = (Y₁, …, Yₙ)` is worse than
duplicate if there is `X ∈ 𝒳` with `Y ≺ᵐ (X, …, X)`, i.e. `φ(Yᵢ) < φ(X)` for each `i`, and
`∑ Yᵢ ≥ nX`. -/
def IsWorseThanDuplicate (φ : Lp ℝ ⊤ P → ℝ) (Y : Fin n → Lp ℝ ⊤ P) : Prop :=
  ∃ X : Lp ℝ ⊤ P, (∀ i, φ (Y i) < φ X) ∧ (n : ℝ) • X ≤ S Y

/-- **[N]φ Normalization** (arXiv:2206.13679v6, p.8): `D(0) = 0`, `D(X) ≤ 1` if `X` is
duplicate, and `D(X) ≥ 1` if `X` is worse than duplicate. A duplicate portfolio is
`(X, …, X) = fun _ => X`. -/
def AxN (φ : Lp ℝ ⊤ P → ℝ) (D : (Fin n → Lp ℝ ⊤ P) → EReal) : Prop :=
  D 0 = 0 ∧ (∀ X : Lp ℝ ⊤ P, D (fun _ => X) ≤ 1) ∧
  (∀ Y : Fin n → Lp ℝ ⊤ P, IsWorseThanDuplicate φ Y → 1 ≤ D Y)

/-- **[C]φ Continuity, as printed** (arXiv:2206.13679v6, p.8): for `(Yᵏ)ₖ ⊆ 𝒳ⁿ` and `X ∈ 𝒳ⁿ`
with `Yᵏ ≃ᵐ X` for each `k`, if `(∑ Xᵢ − ∑ Yᵢᵏ)₊ → 0` in `L∞`, then `(D(X) − D(Yᵏ))₊ → 0`.

**Formalization Note.** The `L∞` convergence is `‖(S X − S Yᵏ)⁺‖ → 0` with the `L∞` norm and
`Lp.posPart`. The positive part of `D(X) − D(Yᵏ)` is `max (D X - D Yᵏ) 0` in `EReal`, with
the limit in the order topology of `EReal`. `EReal` subtraction gives `⊤ − ⊤ = ⊥`, so the
positive part is `0` when both values are `+∞` (the only reading under which an index taking
the value `∞` can satisfy the axiom); `⊤ − a = ⊤` for `a < ⊤`. -/
def AxC (φ : Lp ℝ ⊤ P → ℝ) (D : (Fin n → Lp ℝ ⊤ P) → EReal) : Prop :=
  ∀ (Y : ℕ → Fin n → Lp ℝ ⊤ P) (X : Fin n → Lp ℝ ⊤ P),
    (∀ k, MargEquiv φ (Y k) X) →
    Tendsto (fun k => ‖Lp.posPart (S X - S (Y k))‖) atTop (𝓝 0) →
    Tendsto (fun k => max (D X - D (Y k)) 0) atTop (𝓝 0)

/-- **[C]φ Continuity, semi-continuous form** (the "special form of semi-continuity" of
arXiv:2206.13679v6, p.8): same hypotheses as `AxC`, conclusion `liminfₖ D(Yᵏ) ≥ D(X)`, written
as: for every `d < D(X)`, eventually `d < D(Yᵏ)`.

**Formalization Note.** This is the reading of [C]φ used in the corrected Theorem 1 of the
mission (correction C2): it agrees with the printed form when `D(X) < ∞` and is implied by it
in general; the printed form fails for some diversification quotients at `D(X) = ∞`. -/
def AxCLsc (φ : Lp ℝ ⊤ P → ℝ) (D : (Fin n → Lp ℝ ⊤ P) → EReal) : Prop :=
  ∀ (Y : ℕ → Fin n → Lp ℝ ⊤ P) (X : Fin n → Lp ℝ ⊤ P),
    (∀ k, MargEquiv φ (Y k) X) →
    Tendsto (fun k => ‖Lp.posPart (S X - S (Y k))‖) atTop (𝓝 0) →
    ∀ d : EReal, d < D X → ∀ᶠ k in atTop, d < D (Y k)

/-- **[PC] Portfolio convexity** (arXiv:2206.13679v6, p.9): the set
`{w ∈ Δₙ : D(w ⊙ X) ≤ d}` is convex for each `X ∈ 𝒳ⁿ` and `d ∈ ℝ̄`, where
`w ⊙ X = (w₁X₁, …, wₙXₙ)` and `Δₙ` is the standard simplex (`stdSimplex ℝ (Fin n)`). -/
def AxPC (D : (Fin n → Lp ℝ ⊤ P) → EReal) : Prop :=
  ∀ (X : Fin n → Lp ℝ ⊤ P) (d : EReal),
    Convex ℝ {w : Fin n → ℝ | w ∈ stdSimplex ℝ (Fin n) ∧ D (fun i => w i • X i) ≤ d}

end DivQuotient


