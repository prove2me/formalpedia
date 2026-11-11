-- Prove2me | Definitions.Def_OptimalXOR_Total_Problems
-- name    : OptimalXOR_Total_Problems
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:05:45.263691+00:00
-- url     : https://prove2.me/theorems/f50022c9-86c9-4678-a927-31096620da33
-- title:
--   Communication problems $F:\mathcal X\times\mathcal Y\to\{-1,1,*\}$, $\operatorname{dom}F$, $\mathcal P(\operatorname{dom}F)$, $F^{\oplus n}$, $F^n$, $\mu^n$, XOR-reducibility and $\mathrm{IP}_n$
-- statement:
--   Let $\mathcal X,\mathcal Y$ be finite nonempty sets. A **communication problem** with output set $\mathcal Z$ is a map $F:\mathcal X\times\mathcal Y\to\mathcal Z\cup\{*\}$; the symbol $*$ marks the inputs on which no answer is required. Its **promise domain** is
--   $$\operatorname{dom}F=\{(x,y)\in\mathcal X\times\mathcal Y: F(x,y)\neq *\},$$
--   and $\mathcal P(\operatorname{dom}F)$ is the set of probability distributions on $\mathcal X\times\mathcal Y$ supported on $\operatorname{dom}F$. A **total** function $F:\mathcal X\times\mathcal Y\to\mathcal Z$ is the problem with $\operatorname{dom}F=\mathcal X\times\mathcal Y$. Boolean outputs are the signs $\pm1$, so XOR is multiplication.
--
--   For $F:\mathcal X\times\mathcal Y\to\{-1,1,*\}$ and $n\ge1$, the **XOR power** and the **direct-sum power** are the problems on $\mathcal X^n\times\mathcal Y^n$
--   $$F^{\oplus n}(x,y)=\prod_{i=1}^n F(x_i,y_i),\qquad F^n(x,y)=\big(F(x_1,y_1),\dots,F(x_n,y_n)\big)$$
--   for $(x,y)\in(\operatorname{dom}F)^n$, and $*$ otherwise. For $\mu\in\mathcal P(\mathcal X\times\mathcal Y)$, $\mu^n$ is the law of $n$ independent pairs $(X_i,Y_i)$, each with law $\mu$ (Alice's and Bob's inputs within a pair may be correlated).
--
--   A total $F:\mathcal X\times\mathcal Y\to\{-1,1\}$ is **XOR-reducible** if $F(x,y)=a(x)b(y)$ for some $a:\mathcal X\to\{-1,1\}$, $b:\mathcal Y\to\{-1,1\}$ (Definition 3.10). Every row and every column of $F$ is **constant on its legal inputs** if $F(x,y)=F(x,y')$ and $F(x,y)=F(x',y)$ whenever the pairs involved lie in $\operatorname{dom}F$ (Proposition 2.6). The **inner product function** is $\mathrm{IP}_n(x,y)=(-1)^{\sum_{i=1}^n x_iy_i}$ on $\{0,1\}^n\times\{0,1\}^n$.
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** A problem is `F : X → Y → Option Z` with `none` for $*$; signs are `ℤˣ`; $\mathcal X^n$ is `Fin n → X` (coordinates $0,\dots,n-1$); `total F` turns a total function into a problem. `xorPow F n` and `dirPow F n` return `none` off $(\operatorname{dom}F)^n$. `pmfPow μ n` is the image of the product of $n$ copies of $\mu$ under unzipping into $\mathcal X^n\times\mathcal Y^n$; `pmfPi` is the product of finitely many independent finite laws. $\{0,1\}$ is `Fin 2`.
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 12 (PDF 14) §2.1; p. 18 (PDF 20) Proposition 2.6; p. 29 (PDF 31) Definition 3.10; p. 55 (PDF 57) Corollary B.2

import Mathlib

open scoped ENNReal

namespace OptimalXOR.Total

/-! Sherstov, *Optimal XOR Lemmas for Information Complexity*, STOC 2027 submission,
§2.1 (printed p. 12, PDF p. 14), Definition 3.10 (p. 29, PDF 31), Corollary B.2 (p. 55, PDF 57).

A communication problem with output set `Z` is `F : X → Y → Option Z`; the value `none`
encodes the symbol `∗` ("no answer required"). Output signs `{−1, 1}` are the units `ℤˣ`, in
which XOR is multiplication. Tuples `x = (x₁, …, xₙ) ∈ Xⁿ` are functions `Fin n → X`. -/

noncomputable section

/-- The promise domain `dom F = {(x, y) : F(x, y) ≠ ∗}` (p. 12). -/
def dom {X Y Z : Type} (F : X → Y → Option Z) : Set (X × Y) :=
  {p | (F p.1 p.2).isSome}

/-- `P(dom F)`: the probability distributions on `X × Y` supported on `dom F` (p. 12). -/
def Distributions {X Y Z : Type} (F : X → Y → Option Z) : Set (PMF (X × Y)) :=
  {μ | μ.support ⊆ dom F}

/-- A total function `F : X × Y → Z`, viewed as a communication problem with `dom F = X × Y`. -/
def total {X Y Z : Type} (F : X → Y → Z) : X → Y → Option Z :=
  fun x y => some (F x y)

/-- The XOR power `F^{⊕n}(x, y) = ∏ᵢ F(xᵢ, yᵢ)` for `(x, y) ∈ (dom F)ⁿ`, and `∗` otherwise (p. 12). -/
def xorPow {X Y : Type} (F : X → Y → Option ℤˣ) (n : ℕ) :
    (Fin n → X) → (Fin n → Y) → Option ℤˣ :=
  fun x y =>
    if h : ∀ i, (F (x i) (y i)).isSome then some (∏ i, (F (x i) (y i)).get (h i)) else none

/-- The direct-sum power `Fⁿ(x, y) = (F(x₁, y₁), …, F(xₙ, yₙ))` for `(x, y) ∈ (dom F)ⁿ`, and `∗`
otherwise (p. 12). -/
def dirPow {X Y Z : Type} (F : X → Y → Option Z) (n : ℕ) :
    (Fin n → X) → (Fin n → Y) → Option (Fin n → Z) :=
  fun x y =>
    if h : ∀ i, (F (x i) (y i)).isSome then some (fun i => (F (x i) (y i)).get (h i)) else none

/-- Every row and every column of `F` has a constant value on its legal inputs
(Proposition 2.6, p. 18). -/
def RowsColumnsConstant {X Y Z : Type} (F : X → Y → Option Z) : Prop :=
  (∀ x y y', (x, y) ∈ dom F → (x, y') ∈ dom F → F x y = F x y') ∧
  (∀ y x x', (x, y) ∈ dom F → (x', y) ∈ dom F → F x y = F x' y)

/-- Definition 3.10 (p. 29): a total `F : X × Y → {−1, 1}` is XOR-reducible if
`F(x, y) = a(x) b(y)` for some `a : X → {−1, 1}` and `b : Y → {−1, 1}`. -/
def XORReducible {X Y : Type} (F : X → Y → ℤˣ) : Prop :=
  ∃ a : X → ℤˣ, ∃ b : Y → ℤˣ, ∀ x y, F x y = a x * b y

/-- The inner product function `IPₙ(x, y) = (−1)^{∑ᵢ xᵢ yᵢ}` on `{0,1}ⁿ × {0,1}ⁿ`
(Corollary B.2, p. 55). -/
def innerProduct (n : ℕ) : (Fin n → Fin 2) → (Fin n → Fin 2) → ℤˣ :=
  fun x y => (-1) ^ (∑ i, (x i).val * (y i).val)

/-- The product distribution of independent coordinates with laws `p i`. -/
def pmfPi {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]
    (p : ∀ i, PMF (α i)) : PMF (∀ i, α i) :=
  PMF.ofFintype (fun a => ∏ i, p i (a i)) (by
    have h1 : ∀ i, ∑ a : α i, p i a = (1 : ℝ≥0∞) := fun i => by simpa [tsum_fintype] using (p i).tsum_coe
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
    simp [h1])

/-- `μⁿ ∈ P((dom F)ⁿ)`: the law of `n` independent input pairs `(Xᵢ, Yᵢ)` with common law `μ`
(p. 12), as a distribution on `Xⁿ × Yⁿ`. Independence between Alice's and Bob's inputs within a
pair is not assumed. -/
def pmfPow {X Y : Type} [Fintype X] [Fintype Y] (μ : PMF (X × Y)) (n : ℕ) :
    PMF ((Fin n → X) × (Fin n → Y)) :=
  (pmfPi (fun _ : Fin n => μ)).map (fun q => (fun i => (q i).1, fun i => (q i).2))

end

end OptimalXOR.Total


