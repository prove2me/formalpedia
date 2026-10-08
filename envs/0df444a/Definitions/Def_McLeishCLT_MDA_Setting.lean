-- Prove2me | Definitions.Def_McLeishCLT_MDA_Setting
-- name    : McLeishCLT_MDA_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:52:50.371811+00:00
-- url     : https://prove2.me/theorems/320cf606-38b6-4941-b013-f605cac17846
-- title:
--   pp. 620–622 — row-wise σ-fields, martingale difference arrays, S_n, max_i |X_{n,i}|, Σ_i X²_{n,i}, T_n, r(x), U_n, Z_{n,j}, J_n, (1.1), (1.2), (2.14)
-- statement:
--   This file fixes the setting of McLeish (1974) and the objects used in the proofs of Theorems (2.1) and (2.3).
--
--   **Setting.** Let $(\Omega,\mathcal F,P)$ be a probability space. For each $n$ let $\{X_{n,i};\ 1\le i\le k_n\}$ be a row of real random variables, and let $\mathcal F_{n,0}\subset\mathcal F_{n,1}\subset\cdots\subset\mathcal F_{n,k_n}\subset\mathcal F$ be an increasing family of sub-σ-fields **belonging to row $n$**; nothing relates the σ-fields of different rows. Write $E_k U = E(U\mid\mathcal F_{n,k})$ for a variable $U$ of the $n$-th row.
--
--   1. The array is **adapted** if each $X_{n,i}$ is $\mathcal F_{n,i}$-measurable.
--   2. It is a **martingale difference array** (m.d.a.) if, in addition, each $X_{n,i}$ is integrable and $E_{i-1}X_{n,i}=0$ almost surely, for all $n$ and $1\le i\le k_n$.
--   3. $S_n=\sum_{i=1}^{k_n}X_{n,i}$, $\ \max_{i\le k_n}|X_{n,i}|$ (taken to be $0$ for an empty row), and $\sum_i X_{n,i}^2$.
--   4. For real $t$, $T_n=\prod_{j=1}^{k_n}(1+itX_{n,j})$, a complex random variable.
--   5. The remainder $r(x)$, for real $x$, defined by $e^{ix}=(1+ix)\exp\{-x^2/2+r(x)\}$, namely
--   $$r(x)=ix+\frac{x^2}{2}-\log(1+ix),$$
--   with the principal branch of the logarithm, and
--   $$U_n=\exp\Big\{-\frac{t^2}{2}\sum_j X_{n,j}^2+\sum_j r(X_{n,j}t)\Big\}.$$
--   6. The truncated array $Z_{n,j}=X_{n,j}\,I\big(\sum_{k=1}^{j-1}X_{n,k}^2\le 2\big)$.
--   7. The random index $J_n=\min\{j\le k_n:\ \sum_{i=1}^{j}X_{n,i}^2>2\}$ if $\sum_iX_{n,i}^2>2$, and $J_n=k_n$ otherwise.
--   8. With $\sigma_{n,i}^2=EX_{n,i}^2\le\infty$: the **Lindeberg condition** (1.1), $\sum_i\int_{\{|X_{n,i}|>\varepsilon\}}X_{n,i}^2\,dP\to0$ for every $\varepsilon>0$; the **variance normalisation** (1.2), $\sum_i\sigma_{n,i}^2\to1$; and condition (2.14), $\limsup_{n}\sum_{i\ne j}EX_{n,i}^2X_{n,j}^2\le1$ (sum over ordered pairs).
--
--   These are the objects in terms of which every theorem of §2 of the paper is stated.
--
--   **Formalization Note** The column index is 0-based: the paper's $X_{n,i}$ ($1\le i\le k_n$) is `X n (i-1)`, while the paper's $\mathcal F_{n,i}$ is `ℱ n i`, so $E_{i-1}X_{n,i}$ is `P[X n j | ℱ n j]` with `X n j` measurable for `ℱ n (j+1)`. Each row has its own `Filtration ℕ m0`; conditions are imposed only on `j < k n`. Integrability is part of the m.d.a. predicate (classically $E_{i-1}X_{n,i}$ presupposes $E|X_{n,i}|<\infty$, and Lean's conditional expectation of a non-integrable function is $0$). Moments in (1.1), (1.2), (2.14) are lower Lebesgue integrals with values in $[0,\infty]$, so infinite second moments are allowed as on the page. `stopJ` is the 0-based $J_n$; at $k_n=0$ it returns the index `0`, outside the (empty) row. The truncated array does not depend on $k_n$.
-- source:
--   McLeish, Dependent central limit theorems and invariance principles, Ann. Probab. 2 (1974), pp. 620–622, (1.1), (1.2), (2.14), definitions before (2.1) and (2.3), proofs of (2.1) and (2.3)

import Mathlib

namespace McLeishCLT.MDA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-! Standing setting of McLeish (1974), pp. 620–622.

For each row `n` the array is `X n j`, `j < k n` (the paper's `X_{n,j+1}`), and the row carries its
own filtration `ℱ n : Filtration ℕ m0` (the paper's `𝓕_{n,i}` is `ℱ n i`). Entries `X n j` with
`j ≥ k n` and σ-fields `ℱ n i` with `i > k n` are never used. -/

/-- The array is adapted (p. 620): the paper's `X_{n,j+1}` is `𝓕_{n,j+1}`-measurable. -/
def IsAdaptedArray {Ω : Type*} {m0 : MeasurableSpace Ω} (ℱ : ℕ → Filtration ℕ m0) (k : ℕ → ℕ)
    (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ n, ∀ j < k n, StronglyMeasurable[ℱ n (j + 1)] (X n j)

/-- Martingale difference array (p. 621): each `X_{n,i}` is `𝓕_{n,i}`-measurable, integrable,
and `E(X_{n,i} | 𝓕_{n,i-1}) = 0` a.s. -/
def IsMDA {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) (ℱ : ℕ → Filtration ℕ m0)
    (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ n, ∀ j < k n, StronglyMeasurable[ℱ n (j + 1)] (X n j) ∧ Integrable (X n j) P ∧
    P[X n j | ℱ n j] =ᵐ[P] 0

/-- The row sum `S_n = Σ_{i=1}^{k_n} X_{n,i}`. -/
def S {Ω : Type*} (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range (k n), X n j ω

/-- `max_{i ≤ k_n} |X_{n,i}|` (equal to `0` for an empty row). -/
noncomputable def maxAbs {Ω : Type*} (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ⨆ j : Fin (k n), |X n j ω|

/-- `Σ_i X²_{n,i}`. -/
def sumSq {Ω : Type*} (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range (k n), X n j ω ^ 2

/-- `T_n = ∏_{j=1}^{k_n} (1 + i t X_{n,j})` (p. 621). -/
noncomputable def prodT {Ω : Type*} (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) : ℂ :=
  ∏ j ∈ Finset.range (k n), (1 + Complex.I * (t : ℂ) * (X n j ω : ℂ))

/-- The remainder `r(x)` of `e^{ix} = (1 + ix) exp{-x²/2 + r(x)}` (p. 621), with the principal
branch of the logarithm. -/
noncomputable def remR (x : ℝ) : ℂ :=
  Complex.I * (x : ℂ) + (x : ℂ) ^ 2 / 2 - Complex.log (1 + Complex.I * (x : ℂ))

/-- `U_n = exp{-t²/2 Σ_j X²_{n,j} + Σ_j r(X_{n,j} t)}` (p. 621). -/
noncomputable def prodU {Ω : Type*} (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) : ℂ :=
  Complex.exp (-(t : ℂ) ^ 2 / 2 * ∑ j ∈ Finset.range (k n), (X n j ω : ℂ) ^ 2
    + ∑ j ∈ Finset.range (k n), remR (X n j ω * t))

/-- The truncated array `Z_{n,j} = X_{n,j} I(Σ_{k=1}^{j-1} X²_{n,k} ≤ 2)` (p. 622), 0-based. -/
noncomputable def trunc {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (n j : ℕ) (ω : Ω) : ℝ :=
  X n j ω * (if ∑ i ∈ Finset.range j, X n i ω ^ 2 ≤ 2 then 1 else 0)

/-- The random index `J_n` (p. 622), 0-based: the first `j < k n` with `Σ_{i ≤ j} X²_{n,i} > 2`
if there is one, and the last index `k n - 1` otherwise. -/
noncomputable def stopJ {Ω : Type*} (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℕ := by
  classical
  exact if h : ∃ j, j < k n ∧ 2 < ∑ i ∈ Finset.range (j + 1), X n i ω ^ 2 then Nat.find h
    else k n - 1

/-- (1.1) The Lindeberg condition: `Σ_i ∫_{|X_{n,i}| > ε} X²_{n,i} dP → 0` for every `ε > 0`. -/
def Lindeberg {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) (k : ℕ → ℕ)
    (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => ∑ j ∈ Finset.range (k n),
    ∫⁻ ω in {ω | ε < |X n j ω|}, ‖X n j ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)

/-- (1.2) `Σ_i σ²_{n,i} → 1`, with `σ²_{n,i} = E X²_{n,i} ≤ ∞`. -/
def VarNormed {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) (k : ℕ → ℕ)
    (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  Tendsto (fun n => ∑ j ∈ Finset.range (k n), ∫⁻ ω, ‖X n j ω‖ₑ ^ 2 ∂P) atTop (𝓝 1)

/-- (2.14) `limsup_n Σ_{i ≠ j} E X²_{n,i} X²_{n,j} ≤ 1`. -/
def Cond214 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) (k : ℕ → ℕ)
    (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  limsup (fun n => ∑ i ∈ Finset.range (k n), ∑ j ∈ (Finset.range (k n)).erase i,
    ∫⁻ ω, ‖X n i ω‖ₑ ^ 2 * ‖X n j ω‖ₑ ^ 2 ∂P) atTop ≤ 1

end McLeishCLT.MDA


