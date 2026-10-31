-- Prove2me | Definitions.Def_KallMayerSLP_ValueOfInfo_TwoStageSLP
-- name    : KallMayerSLP_ValueOfInfo_TwoStageSLP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:36.405132+00:00
-- url     : https://prove2.me/theorems/3ddd3a1f-1d6a-4e39-acf3-07180d576201
-- title:
--   Two-stage SLP with affine random data $T(\xi),W(\xi),h(\xi),q(\xi)$
-- statement:
--   The data of the general two-stage stochastic linear program with random recourse. The first stage has deterministic data $A\in\mathbb R^{m_1\times n_1}$, $b\in\mathbb R^{m_1}$, $c\in\mathbb R^{n_1}$. The second-stage data depend affinely on a random vector $\xi\in\Xi=\mathbb R^r$:
--
--   $$
--   T(\xi)=T+\sum_{j=1}^r T^j\xi_j,\quad W(\xi)=W+\sum_{j=1}^r W^j\xi_j,\quad h(\xi)=h+\sum_{j=1}^r h^j\xi_j,\quad q(\xi)=q+\sum_{j=1}^r q^j\xi_j,
--   $$
--
--   with deterministic $T,T^j\in\mathbb R^{m_2\times n_1}$, $W,W^j\in\mathbb R^{m_2\times n_2}$, $h,h^j\in\mathbb R^{m_2}$, $q,q^j\in\mathbb R^{n_2}$.
--
--   Two sub-classes are named by the book through the arguments of the recourse function:
--
--   1. $Q(x;T(\xi),h(\xi))$: only $T(\cdot)$ and $h(\cdot)$ are random, $W(\cdot)\equiv W$ and $q(\cdot)\equiv q$ are deterministic;
--   2. $Q(x;h(\xi))$: only $h(\cdot)$ is random, $T(\cdot)\equiv T$, $W(\cdot)\equiv W$, $q(\cdot)\equiv q$ are deterministic.
--
--   These are the problems whose characteristic values $RS$, $EV$, $WS$, $EEV$, $EVPI$, $VSS$ are compared in §2.3.
--
--   **Formalization Note** Indices $j=1,\dots,r$ are $0$-based (`Fin r`). The two sub-classes are built by the constructors `ofRandomTh` and `ofRandomH`, which set the coefficient arrays of the deterministic data to zero. No sign, rank or recourse condition is imposed.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, eq. (2.1), p.199 (PDF 208); §2.3, p.243 (PDF 252); notation Q(x; T(ξ), h(ξ)), Q(x; h(ξ)), p.200 (PDF 209)

import Mathlib

namespace KallMayerSLP.ValueOfInfo

/-- **Data of the general two-stage SLP with random recourse, (2.66) with (2.1).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, §2.3, p.243 (PDF 252), and
eq. (2.1), p.199 (PDF 208): deterministic first-stage data `A ∈ ℝ^{m₁×n₁}`, `b ∈ ℝ^{m₁}`,
`c ∈ ℝ^{n₁}`, and second-stage data that are affine in the random vector `ξ ∈ Ξ = ℝʳ`:
`T(ξ) = T + Σⱼ Tʲ ξⱼ`, `W(ξ) = W + Σⱼ Wʲ ξⱼ`, `h(ξ) = h + Σⱼ hʲ ξⱼ`, `q(ξ) = q + Σⱼ qʲ ξⱼ`,
with `T, Tʲ ∈ ℝ^{m₂×n₁}`, `W, Wʲ ∈ ℝ^{m₂×n₂}`, `h, hʲ ∈ ℝ^{m₂}`, `q, qʲ ∈ ℝ^{n₂}` deterministic.

**Formalization Note.** The fields `T₀, W₀, h₀, q₀` are the book's `T, W, h, q` and
`Tc j, Wc j, hc j, qc j` its `Tʲ, Wʲ, hʲ, qʲ`; the indices `j = 1, …, r` are `Fin r` (0-based).
No sign, rank or recourse condition is imposed (§2.3 treats "an arbitrary recourse problem"). -/
structure TwoStageSLP (r n₁ m₁ n₂ m₂ : ℕ) where
  /-- First-stage constraint matrix `A ∈ ℝ^{m₁×n₁}`. -/
  A : Matrix (Fin m₁) (Fin n₁) ℝ
  /-- First-stage right-hand side `b ∈ ℝ^{m₁}`. -/
  b : Fin m₁ → ℝ
  /-- First-stage cost `c ∈ ℝ^{n₁}`. -/
  c : Fin n₁ → ℝ
  /-- `T ∈ ℝ^{m₂×n₁}`. -/
  T₀ : Matrix (Fin m₂) (Fin n₁) ℝ
  /-- `Tʲ ∈ ℝ^{m₂×n₁}`. -/
  Tc : Fin r → Matrix (Fin m₂) (Fin n₁) ℝ
  /-- `W ∈ ℝ^{m₂×n₂}`. -/
  W₀ : Matrix (Fin m₂) (Fin n₂) ℝ
  /-- `Wʲ ∈ ℝ^{m₂×n₂}`. -/
  Wc : Fin r → Matrix (Fin m₂) (Fin n₂) ℝ
  /-- `h ∈ ℝ^{m₂}`. -/
  h₀ : Fin m₂ → ℝ
  /-- `hʲ ∈ ℝ^{m₂}`. -/
  hc : Fin r → Fin m₂ → ℝ
  /-- `q ∈ ℝ^{n₂}`. -/
  q₀ : Fin n₂ → ℝ
  /-- `qʲ ∈ ℝ^{n₂}`. -/
  qc : Fin r → Fin n₂ → ℝ

namespace TwoStageSLP

variable {r n₁ m₁ n₂ m₂ : ℕ}

/-- `T(ξ) = T + Σ_{j=1}^r Tʲ ξⱼ`, eq. (2.1). -/
def T (P : TwoStageSLP r n₁ m₁ n₂ m₂) (ξ : Fin r → ℝ) : Matrix (Fin m₂) (Fin n₁) ℝ :=
  P.T₀ + ∑ j, ξ j • P.Tc j

/-- `W(ξ) = W + Σ_{j=1}^r Wʲ ξⱼ`, eq. (2.1). -/
def W (P : TwoStageSLP r n₁ m₁ n₂ m₂) (ξ : Fin r → ℝ) : Matrix (Fin m₂) (Fin n₂) ℝ :=
  P.W₀ + ∑ j, ξ j • P.Wc j

/-- `h(ξ) = h + Σ_{j=1}^r hʲ ξⱼ`, eq. (2.1). -/
def h (P : TwoStageSLP r n₁ m₁ n₂ m₂) (ξ : Fin r → ℝ) : Fin m₂ → ℝ :=
  P.h₀ + ∑ j, ξ j • P.hc j

/-- `q(ξ) = q + Σ_{j=1}^r qʲ ξⱼ`, eq. (2.1). -/
def q (P : TwoStageSLP r n₁ m₁ n₂ m₂) (ξ : Fin r → ℝ) : Fin n₂ → ℝ :=
  P.q₀ + ∑ j, ξ j • P.qc j

/-- **The class `Q(x; T(ξ), h(ξ))`: only `T(·)` and `h(·)` random** (p.200, PDF 209: "`Q(x; T(ξ),
h(ξ))` indicates that `T(·), h(·)` are random arrays defined according to (2.1) whereas `W(·) ≡ W`,
`q(·) ≡ q`"). Built from arbitrary affine `T(·)`, `h(·)` and a deterministic `W`, `q`. -/
def ofRandomTh (A : Matrix (Fin m₁) (Fin n₁) ℝ) (b : Fin m₁ → ℝ) (c : Fin n₁ → ℝ)
    (T₀ : Matrix (Fin m₂) (Fin n₁) ℝ) (Tc : Fin r → Matrix (Fin m₂) (Fin n₁) ℝ)
    (W : Matrix (Fin m₂) (Fin n₂) ℝ) (h₀ : Fin m₂ → ℝ) (hc : Fin r → Fin m₂ → ℝ)
    (q : Fin n₂ → ℝ) : TwoStageSLP r n₁ m₁ n₂ m₂ :=
  { A := A, b := b, c := c, T₀ := T₀, Tc := Tc, W₀ := W, Wc := 0, h₀ := h₀, hc := hc,
    q₀ := q, qc := 0 }

/-- **The class `Q(x; h(ξ))`: only `h(·)` random** (p.200, PDF 209: "`Q(x; h(ξ))` stands for `h(·)`
being a random vector due to (2.1) and `T(·) ≡ T`, `W(·) ≡ W`, `q(·) ≡ q` being deterministic
data"). Built from an arbitrary affine `h(·)` and deterministic `T`, `W`, `q`. -/
def ofRandomH (A : Matrix (Fin m₁) (Fin n₁) ℝ) (b : Fin m₁ → ℝ) (c : Fin n₁ → ℝ)
    (T : Matrix (Fin m₂) (Fin n₁) ℝ) (W : Matrix (Fin m₂) (Fin n₂) ℝ) (h₀ : Fin m₂ → ℝ)
    (hc : Fin r → Fin m₂ → ℝ) (q : Fin n₂ → ℝ) : TwoStageSLP r n₁ m₁ n₂ m₂ :=
  { A := A, b := b, c := c, T₀ := T, Tc := 0, W₀ := W, Wc := 0, h₀ := h₀, hc := hc,
    q₀ := q, qc := 0 }

end TwoStageSLP

end KallMayerSLP.ValueOfInfo


