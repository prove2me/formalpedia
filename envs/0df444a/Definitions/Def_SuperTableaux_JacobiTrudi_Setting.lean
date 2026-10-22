-- Prove2me | Definitions.Def_SuperTableaux_JacobiTrudi_Setting
-- name    : SuperTableaux_JacobiTrudi_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:54.657012+00:00
-- url     : https://prove2.me/theorems/32fac1e7-31aa-414a-86fd-f927dfe1a8ad
-- title:
--   Def. 2.1, 3.1, 3.11, (3.7), (3.13), (3.14) — A/B-semistandard and rational tableaux, their characters, Kostka and LR numbers
-- statement:
--   Throughout, $\mathcal A$ and $\mathcal B$ are linearly ordered, at most countable, $\mathbb Z_2$-graded sets: $\mathcal A=\mathcal A_0\sqcup\mathcal A_1$ (letters of degree $0$, *even*, and of degree $1$, *odd*), and likewise for $\mathcal B$.
--
--   1. **Super-semistandard tableaux (Definition 2.1).** A filling $T$ of a skew Young diagram with letters of $\mathcal A$ is *$\mathcal A$-semistandard* if its entries weakly increase along each row (left to right) and down each column (top to bottom), the even letters strictly increase down each column and the odd letters strictly increase along each row. $SST_{\mathcal A}(\lambda/\mu)$ is the set of such tableaux; the weight of $T$ is $\mathrm{wt}(T)=\sum_a m_a\epsilon_a$, $m_a$ the number of entries equal to $a$.
--
--   2. **Generalized partitions (3.1)–(3.2).** $\mathbb Z^n_+=\{\lambda=(\lambda_1\ge\cdots\ge\lambda_n)\in\mathbb Z^n\}$ for $n\ge1$; $\lambda+(d^n)=(\lambda_1+d,\dots,\lambda_n+d)$; $\lambda^*=(-\lambda_n,\dots,-\lambda_1)$. $\mathscr P_n\subset\mathbb Z^n_+$ is the set of $\lambda$ with $\lambda_n\ge0$.
--
--   3. **A/B-semistandard tableaux (Definition 3.11).** For $\lambda\in\mathbb Z^n_+$, an element of $SST_{\mathcal A/\mathcal B}(\lambda)$ is a pair $(T^+,T^-)$ with
--   $$T^+\in SST_{\mathcal A}\big((\lambda+(d^n))/\mu\big),\qquad T^-\in SST_{\mathcal B}\big((d^n)/\mu\big)$$
--   for some $d\ge0$ and $\mu\in\mathscr P_n$ with $\lambda+(d^n)\in\mathscr P_n$, $\mu\subset(d^n)$ and $\mu\subset\lambda+(d^n)$. Both tableaux are drawn against the vertical line of $\lambda$ (Example 3.12), so $(d,\mu)$ and $(d+1,\mu+(1^n))$ give the same pair of shapes.
--
--   4. **Characters (3.13), (3.14).** For a partition $\lambda$, $S^{\mathcal A}_\lambda=\sum_{T\in SST_{\mathcal A}(\lambda)}x_{\mathcal A}^T\in\mathbb Z[[x_{\mathcal A}]]$ with $x^T_{\mathcal A}=\prod_a x_a^{m_a}$, and for $\lambda\in\mathbb Z^n_+$
--   $$S^{\mathcal A/\mathcal B}_\lambda=\sum_{(T^+,T^-)\in SST_{\mathcal A/\mathcal B}(\lambda)}x_{\mathcal A}^{T^+}\big(x_{\mathcal B}^{T^-}\big)^{-1}\in\mathbb Z[[x_{\mathcal A},x_{\mathcal B}^{-1}]].$$
--   $S^{\mathcal A/\mathcal B}_k$ ($k\in\mathbb Z$) is the level-one case, and $H^{\mathcal A/\mathcal B}_\mu=\prod_i S^{\mathcal A/\mathcal B}_{\mu_i}$.
--
--   5. **Rational $[n]$-semistandard tableaux (Definition 3.1).** The generalized Young diagram of $\lambda\in\mathbb Z^n_+$ has, in row $k$, the columns $1,\dots,\lambda_k$ if $\lambda_k>0$ and the columns $\lambda_k,\dots,-1$ if $\lambda_k<0$. A filling $T$ with entries in $[n]\cup[-n]$ is a rational $[n]$-semistandard tableau if (1) positive columns hold entries of $[n]=\{1<\cdots<n\}$ and negative columns entries of $[-n]=\{-n<\cdots<-1\}$; (2) rows weakly and columns strictly increase; (3) if $b_1<\cdots<b_s$ are the entries of column $1$ and $-b'_1<\cdots<-b'_t$ those of column $-1$, then $b''_i\le b_i$ for $1\le i\le s$, where $\{b''_1<\cdots<b''_{n-t}\}=[n]\setminus\{b'_1,\dots,b'_t\}$. The content of $T$ is $\nu$ with $\nu_k=m_k-m_{-k}$ (from (3.6)), and the Kostka number $K_{\lambda\mu}$ is the number of rational $[n]$-semistandard tableaux of shape $\lambda$ and content $\mu$. The map $\sigma$ (p. 12) sends a filling of shape $\lambda$ to one of shape $\lambda+(1^n)$: the $-1$st column, with entries $-b_1<\cdots<-b_t$, is removed, a new column $1$ with entries $[n]\setminus\{b_1,\dots,b_t\}$ in increasing order is inserted, and every other cell moves one column to the right.
--
--   6. **Schur and complete symmetric polynomials.** $s_\lambda(x_{[n]})=S^{[n]}_\lambda$ for $\lambda\in\mathscr P_n$ (Example 3.15 (1)); $h_k(x_{[n]})=s_{(k)}(x_{[n]})$ for $k\ge0$ and $h_k=0$ for $k<0$; $h_\mu=\prod_i h_{\mu_i}$.
--
--   7. **Littlewood–Richardson numbers (p. 6, (3.7)).** For partitions, $N^\lambda_{\mu\nu}$ is the number of $\mathbb N$-semistandard tableaux of shape $\lambda/\mu$ in which $k$ occurs $\nu_k$ times and whose column reading word (columns right to left, each top to bottom) is a lattice permutation. For $\lambda,\mu,\nu\in\mathbb Z^n_+$, $c^\lambda_{\mu\nu}=N^{\lambda+((p+q)^n)}_{\mu+(p^n)\,\nu+(q^n)}$ for $p,q$ large.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** Cells are pairs (row, column) in $\mathbb N\times\mathbb Z$ with rows $0$-based. An A/B-tableau is stored in **cut coordinates**: the class of $(d,\mu)$ is the antitone vector $c=\mu-(d^n)$, with $c_i\le\min(0,\lambda_i)$; $T^+$ fills $\{(i,j): c_i<j\le\lambda_i\}$ and $T^-$ fills $\{(i,j): c_i<j\le 0\}$. This is the paper's identification made explicit (a tableau "does not depend on the choice of $d$", p. 27); without it the same pair would be counted once for every $d$. Since rows and columns of every shape used are intervals, semistandardness is imposed on adjacent cells only. The grading is a function `odd : A → Bool` (`true` = degree 1). Characters are `MvPowerSeries` whose coefficient at a monomial is `Nat.card` of the (finite) set of tableaux of that weight; in $\mathbb Z[[x_{\mathcal A},x_{\mathcal B}^{-1}]]$ = `MvPowerSeries (A ⊕ B) ℤ` the variable `Sum.inr b` is the symbol $x_b^{-1}$. Condition (3) of Definition 3.1 uses the increasing enumeration of $[n]\setminus\{b'\}$ (`Finset.orderEmbOfFin`). $c^\lambda_{\mu\nu}$ is evaluated at $p=q=\sum_i(|\lambda_i|+|\mu_i|+|\nu_i|)+1$, which makes all three shapes partitions; Lemma 3.7 makes any such choice give the same value. The printed condition (1) of LR tableaux on p. 6 reads "$\mu_k$"; the content is $\nu$, as used here.
-- source:
--   Kwon, Rational semistandard tableaux and character formula for the Lie superalgebra ĝl∞|∞, arXiv:math/0605005v1, pp. 3–6, 11–18, Definitions 2.1, 3.1, 3.11, (3.1), (3.2), (3.6), (3.7), (3.13), (3.14), Example 3.15 (1), (4.5), the map σ of p. 12

import Mathlib

namespace SuperTableaux.JacobiTrudi

open Classical

noncomputable section

/-! ### Cells and super-semistandard fillings (Definition 2.1)

A cell is a pair `(row, column) : ℕ × ℤ`; rows are 0-based (row `0` is the paper's row 1).
For an A/B-tableau, columns `j ≥ 1` lie right of the paper's vertical line and columns `j ≤ 0`
left of it. -/

/-- Definition 2.1 on a finite cell set whose rows and columns are contiguous (true of every
shape used below): entries weakly increase along rows (left to right) and down columns (top to
bottom); two horizontally adjacent equal entries must be even (`odd = false`, i.e. in `A₀`), so
odd entries are strictly increasing in rows; two vertically adjacent equal entries must be odd
(`odd = true`, i.e. in `A₁`), so even entries are strictly increasing in columns. -/
def IsSemistandard {A : Type*} [LinearOrder A] (odd : A → Bool) (cells : Finset (ℕ × ℤ))
    (T : cells → A) : Prop :=
  (∀ x y : cells, y.1.1 = x.1.1 → y.1.2 = x.1.2 + 1 →
      T x ≤ T y ∧ (T x = T y → odd (T x) = false)) ∧
  (∀ x y : cells, y.1.1 = x.1.1 + 1 → y.1.2 = x.1.2 →
      T x ≤ T y ∧ (T x = T y → odd (T x) = true))

/-- The weight `wt(T) = ∑_a m_a ε_a` of a filling: `m_a` is the number of cells holding `a`. -/
def weight {A : Type*} {cells : Finset (ℕ × ℤ)} (T : cells → A) : A →₀ ℕ :=
  ∑ x, Finsupp.single (T x) 1

/-- The cells `{(i, j) | lo i < j ≤ hi i}` lying between two boundaries `lo, hi : Fin n → ℤ`
(row `i` is the half-open integer interval `(lo i, hi i]`, empty if `hi i ≤ lo i`). -/
def cellsBetween {n : ℕ} (lo hi : Fin n → ℤ) : Finset (ℕ × ℤ) :=
  Finset.univ.biUnion fun i : Fin n => (Finset.Ioc (lo i) (hi i)).image fun j => ((i : ℕ), j)

/-! ### Generalized partitions (3.1)–(3.2) -/

/-- `Z^n_+`: generalized partitions of level `n`, `λ₁ ≥ ⋯ ≥ λₙ` (index `0` is `λ₁`). -/
abbrev GenPartition (n : ℕ) := {la : Fin n → ℤ // Antitone la}

/-- `λ + (d^n)`. -/
def shift {n : ℕ} (la : GenPartition n) (d : ℤ) : GenPartition n :=
  ⟨fun i => la.1 i + d, fun _ _ h => by simpa using la.2 h⟩

/-- `λ* = (−λₙ, …, −λ₁)`, (3.2). -/
def star {n : ℕ} (la : GenPartition n) : GenPartition n :=
  ⟨fun i => -la.1 (Fin.rev i), fun _ _ h => neg_le_neg (la.2 (Fin.rev_le_rev.mpr h))⟩

/-- The level-one generalized partition `(k) ∈ Z^1_+`. -/
def level1 (k : ℤ) : GenPartition 1 := ⟨fun _ => k, antitone_const⟩

/-! ### A/B-semistandard tableaux (Definition 3.11) in cut coordinates -/

/-- A cut for `λ ∈ Z^n_+`: `c = µ − (d^n)` for the paper's pair `(d, µ)` of Definition 3.11,
i.e. the class of `(d, µ)` under `(d, µ) ~ (d + 1, µ + (1^n))`. It is antitone and satisfies
`c i ≤ min 0 (λ i)` (that is `µ ⊂ (d^n)` and `µ ⊂ λ + (d^n)`). -/
def Cut {n : ℕ} (la : GenPartition n) : Type :=
  {c : Fin n → ℤ // Antitone c ∧ ∀ i, c i ≤ min 0 (la.1 i)}

/-- The cells of `T⁺`: the skew shape `(λ + (d^n))/µ`, drawn against the vertical line,
`{(i, j) | c i < j ≤ λ i}`. -/
def plusCells {n : ℕ} (la : GenPartition n) (c : Cut la) : Finset (ℕ × ℤ) :=
  cellsBetween c.1 la.1

/-- The cells of `T⁻`: the skew shape `(d^n)/µ`, `{(i, j) | c i < j ≤ 0}`. -/
def minusCells {n : ℕ} {la : GenPartition n} (c : Cut la) : Finset (ℕ × ℤ) :=
  cellsBetween c.1 (fun _ => 0)

/-- `SST_{A/B}(λ)`: a cut together with an `A`-semistandard `T⁺` on `plusCells` and a
`B`-semistandard `T⁻` on `minusCells`. -/
def ABTab {A B : Type*} [LinearOrder A] [LinearOrder B] (oddA : A → Bool) (oddB : B → Bool)
    {n : ℕ} (la : GenPartition n) : Type _ :=
  Σ c : Cut la, {T : plusCells la c → A // IsSemistandard oddA _ T} ×
    {T : minusCells c → B // IsSemistandard oddB _ T}

/-- The A/B-weight, as one exponent vector on `A ⊕ B`: the `Sum.inl a` entry is the number of
`a`'s in `T⁺` (the exponent of `x_a`), the `Sum.inr b` entry the number of `b`'s in `T⁻` (the
exponent of the variable `x_b^{-1}`). -/
def wtAB {A B : Type*} [LinearOrder A] [LinearOrder B] {oddA : A → Bool} {oddB : B → Bool}
    {n : ℕ} {la : GenPartition n} (X : ABTab oddA oddB la) : (A ⊕ B) →₀ ℕ :=
  (weight X.2.1.1).mapDomain Sum.inl + (weight X.2.2.1).mapDomain Sum.inr

/-- (3.14): `S^{A/B}_λ = ∑_{(T⁺,T⁻) ∈ SST_{A/B}(λ)} x_A^{T⁺} (x_B^{T⁻})^{-1}` in
`ℤ[[x_A, x_B^{-1}]]`, realised as `MvPowerSeries (A ⊕ B) ℤ` where the variable `Sum.inl a` is
`x_a` and the variable `Sum.inr b` is `x_b^{-1}`. The coefficient of a monomial is the number of
A/B-tableaux of that weight. -/
def charAB {A B : Type*} [LinearOrder A] [LinearOrder B] (oddA : A → Bool) (oddB : B → Bool)
    {n : ℕ} (la : GenPartition n) : MvPowerSeries (A ⊕ B) ℤ :=
  fun m => (Nat.card {X : ABTab oddA oddB la // wtAB X = m} : ℤ)

/-- The level-one character `S^{A/B}_k`, `k ∈ ℤ`. -/
def charAB1 {A B : Type*} [LinearOrder A] [LinearOrder B] (oddA : A → Bool) (oddB : B → Bool)
    (k : ℤ) : MvPowerSeries (A ⊕ B) ℤ :=
  charAB oddA oddB (level1 k)

/-- `H^{A/B}_µ = ∏_{i} S^{A/B}_{µ_i}` (proof of Theorem 4.5). -/
def Hprod {A B : Type*} [LinearOrder A] [LinearOrder B] (oddA : A → Bool) (oddB : B → Bool)
    {n : ℕ} (mu : GenPartition n) : MvPowerSeries (A ⊕ B) ℤ :=
  ∏ i, charAB1 oddA oddB (mu.1 i)

/-! ### Ordinary partitions and the characters `S^A_λ` (3.13) -/

/-- The cells of a Young diagram, as cells `(i, j) ∈ ℕ × ℤ`. -/
def ydCells (la : YoungDiagram) : Finset (ℕ × ℤ) :=
  la.cells.image fun p => (p.1, (p.2 : ℤ))

/-- The Young diagram of a generalized partition with nonnegative parts (a partition in `P_n`):
row `i` has `µ i` cells (negative parts, never used, count as `0`). -/
def toYD {n : ℕ} (mu : GenPartition n) : YoungDiagram where
  cells := Finset.univ.biUnion fun i : Fin n =>
    (Finset.range (mu.1 i).toNat).image fun j => ((i : ℕ), j)
  isLowerSet := by
    intro y x hxy hy
    simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion, Finset.mem_coe, Finset.mem_image, Finset.mem_range] at hy ⊢
    obtain ⟨i, j, hj, rfl⟩ := hy
    obtain ⟨h1, h2⟩ := Prod.mk_le_mk.mp hxy
    refine ⟨⟨x.1, lt_of_le_of_lt h1 i.2⟩, x.2, ?_, rfl⟩
    have hmono : mu.1 i ≤ mu.1 ⟨x.1, lt_of_le_of_lt h1 i.2⟩ := mu.2 (Fin.mk_le_mk.mpr h1)
    have : (mu.1 i).toNat ≤ (mu.1 ⟨x.1, lt_of_le_of_lt h1 i.2⟩).toNat := Int.toNat_le_toNat hmono
    omega

/-- `SST_A(λ)` for an ordinary partition `λ`. -/
def SSF {A : Type*} [LinearOrder A] (odd : A → Bool) (la : YoungDiagram) : Type _ :=
  {T : ydCells la → A // IsSemistandard odd _ T}

/-- (3.13): `S^A_λ = ∑_{T ∈ SST_A(λ)} x_A^T ∈ ℤ[[x_A]]`. -/
def charA {A : Type*} [LinearOrder A] (odd : A → Bool) (la : YoungDiagram) : MvPowerSeries A ℤ :=
  fun m => (Nat.card {T : SSF odd la // weight T.1 = m} : ℤ)

/-- `S_λ(x_A)` viewed in `ℤ[[x_A, x_B^{-1}]] = MvPowerSeries (A ⊕ B) ℤ`. -/
def charAinl {A : Type*} [LinearOrder A] (B : Type*) (oddA : A → Bool) (la : YoungDiagram) :
    MvPowerSeries (A ⊕ B) ℤ :=
  fun m => (Nat.card {T : SSF oddA la // (weight T.1).mapDomain Sum.inl = m} : ℤ)

/-- `S_µ(x_B^{-1})` in `MvPowerSeries (A ⊕ B) ℤ`: the character of `SST_B(µ)` in the variables
`x_b^{-1}` (the variables `Sum.inr b`). -/
def charBinr (A : Type*) {B : Type*} [LinearOrder B] (oddB : B → Bool) (mu : YoungDiagram) :
    MvPowerSeries (A ⊕ B) ℤ :=
  fun m => (Nat.card {T : SSF oddB mu // (weight T.1).mapDomain Sum.inr = m} : ℤ)

/-! ### Rational `[n]`-semistandard tableaux (Definition 3.1) and Kostka numbers -/

/-- The generalized Young diagram of `λ ∈ Z^n_+` (p. 11): row `i` has the cells in columns
`1, …, λ i` if `λ i > 0`, and in columns `λ i, …, −1` if `λ i < 0`. -/
def ratCells {n : ℕ} (la : GenPartition n) : Finset (ℕ × ℤ) :=
  cellsBetween (fun i => min 0 (la.1 i) - 1) (fun i => max 0 (la.1 i)) |>.filter fun x => x.2 ≠ 0

/-- Definition 3.1: `T` is a rational `[n]`-semistandard tableau of shape `λ` (entries in
`[n] ∪ [−n] ⊂ ℤ`). Condition (3) is stated with `b_1 < ⋯ < b_s` the entries of column `1`
(`b_{r+1}` sits in row `r`) and `b''_1 < ⋯ < b''_{n−t}` the increasing enumeration of
`[n] \ {b'_1, …, b'_t}`, where `−b'_1 < ⋯ < −b'_t` are the entries of column `−1`. -/
def IsRatSS (n : ℕ) {la : GenPartition n} (T : ratCells la → ℤ) : Prop :=
  -- (1) positive columns hold `[n]`, negative columns hold `[−n]`
  (∀ x : ratCells la, 0 < x.1.2 → 1 ≤ T x ∧ T x ≤ n) ∧
  (∀ x : ratCells la, x.1.2 < 0 → -(n : ℤ) ≤ T x ∧ T x ≤ -1) ∧
  -- (2) rows weakly increasing, columns strictly increasing
  (∀ x y : ratCells la, y.1.1 = x.1.1 → y.1.2 = x.1.2 + 1 → T x ≤ T y) ∧
  (∀ x y : ratCells la, y.1.1 = x.1.1 + 1 → y.1.2 = x.1.2 → T x < T y) ∧
  -- (3) `b''_{r+1} ≤ b_{r+1}` for the entry `b_{r+1}` of column `1` in row `r`
  (let bpp : Finset ℤ :=
      Finset.Icc 1 (n : ℤ) \ (Finset.univ.filter fun x : ratCells la => x.1.2 = -1).image
        fun x => -T x
    ∀ x : ratCells la, x.1.2 = 1 → ∀ h : x.1.1 < bpp.card,
      bpp.orderEmbOfFin rfl ⟨x.1.1, h⟩ ≤ T x)

/-- `SST_{[n]}(λ)`. -/
def RatTab (n : ℕ) (la : GenPartition n) : Type :=
  {T : ratCells la → ℤ // IsRatSS n T}

/-- The content `ν` of `T` (from (3.6)): `ν_k = m_k − m_{−k}`, `m_k` the number of entries equal
to `k`; index `k : Fin n` stands for the letter `k + 1`. -/
def content {n : ℕ} {la : GenPartition n} (T : RatTab n la) : Fin n → ℤ :=
  fun k => ((Finset.univ.filter fun x => T.1 x = (k : ℤ) + 1).card : ℤ) -
    ((Finset.univ.filter fun x => T.1 x = -((k : ℤ) + 1)).card : ℤ)

/-- `K_{λµ} = |SST_{[n]}(λ)_µ|`, the number of rational `[n]`-semistandard tableaux of shape `λ`
with content `µ` (p. 23). -/
def kostka {n : ℕ} (la mu : GenPartition n) : ℕ :=
  Nat.card {T : RatTab n la // content T = mu.1}

/-- The map `σ` of p. 12 on fillings, `SST_{[n]}(λ) → SST_{[n]}(λ + (1^n))`: if the `−1`st
column of `T` holds `−b_1 < ⋯ < −b_t`, it is replaced by a new column `1` holding the increasing
enumeration `b'_1 < ⋯ < b'_{n−t}` of `[n] \ {b_1, …, b_t}` (`b'_{r+1}` in row `r`), and every
other cell moves one column to the right (column `j` of `T` becomes column `j + 1`). -/
def sigmaFill {n : ℕ} {la : GenPartition n} (T : ratCells la → ℤ) :
    ratCells (shift la 1) → ℤ := fun x =>
  if x.1.2 = 1 then
    let comp : Finset ℤ := Finset.Icc 1 (n : ℤ) \
      (Finset.univ.filter fun y : ratCells la => y.1.2 = -1).image fun y => -T y
    if h : x.1.1 < comp.card then comp.orderEmbOfFin rfl ⟨x.1.1, h⟩ else 0
  else
    if h : (x.1.1, x.1.2 - 1) ∈ ratCells la then T ⟨(x.1.1, x.1.2 - 1), h⟩ else 0

/-! ### Schur and complete symmetric polynomials in `n` variables (Example 3.15 (1), (4.5)) -/

/-- `s_λ(x_{[n]}) = S^{[n]}_λ` for `λ ∈ P_n` (all parts `≥ 0`), with `A = [n]` (all letters
even), as the character of `SST_{[n]}(λ)` on the diagram `{(i, j) | 0 < j ≤ λ i}`. Only used
for `λ` with nonnegative parts. -/
def schurN (n : ℕ) (la : GenPartition n) : MvPowerSeries (Fin n) ℤ :=
  fun m => (Nat.card {T : {T : cellsBetween 0 la.1 → Fin n //
      IsSemistandard (fun _ => false) _ T} // weight T.1 = m} : ℤ)

/-- `h_k(x_{[n]})`: the Schur polynomial of the one-row shape `(k)` for `k ≥ 0`, and `0` for
`k < 0` (the convention of (4.5)). -/
def hN (n : ℕ) (k : ℤ) : MvPowerSeries (Fin n) ℤ :=
  if 0 ≤ k then
    fun m => (Nat.card {T : {T : cellsBetween (n := 1) 0 (fun _ => k) → Fin n //
      IsSemistandard (fun _ => false) _ T} // weight T.1 = m} : ℤ)
  else 0

/-- `h_µ(x_{[n]}) = ∏_i h_{µ_i}(x_{[n]})`. -/
def hProdN (n : ℕ) (mu : GenPartition n) : MvPowerSeries (Fin n) ℤ :=
  ∏ i, hN n (mu.1 i)

/-! ### Littlewood–Richardson tableaux (p. 6) and the coefficients `c^λ_{µν}` of (3.7) -/

/-- `w_col` order on cells: `y` is read before (or at) `x` when `y` is in a column further right,
or in the same column and not lower. -/
def colReadLE (y x : ℕ × ℤ) : Prop := x.2 < y.2 ∨ (y.2 = x.2 ∧ y.1 ≤ x.1)

/-- `N^λ_{µν}` for `λ, µ, ν` with nonnegative parts (partitions in `P_n`): the number of
Littlewood–Richardson tableaux of shape `λ/µ` with content `ν`, i.e. `ℕ`-semistandard tableaux
(letters `1 < ⋯ < n`, here `Fin n`) of shape `λ/µ` in which the letter `k` occurs `ν_k` times
and whose column reading word `w_col` is a lattice permutation. It is `0` unless `µ ⊂ λ`. -/
def lrN {n : ℕ} (la mu nu : GenPartition n) : ℕ :=
  if ∀ i, mu.1 i ≤ la.1 i then
    Nat.card {T : cellsBetween mu.1 la.1 → Fin n //
      IsSemistandard (fun _ => false) _ T ∧
      (∀ k : Fin n, (Finset.univ.filter fun x => T x = k).card = nu.1 k) ∧
      ∀ x : cellsBetween mu.1 la.1, ∀ k : ℕ, ∀ hk : k + 1 < n,
        (Finset.univ.filter fun y : cellsBetween mu.1 la.1 =>
            colReadLE y.1 x.1 ∧ T y = ⟨k + 1, hk⟩).card ≤
          (Finset.univ.filter fun y : cellsBetween mu.1 la.1 =>
            colReadLE y.1 x.1 ∧ T y = ⟨k, Nat.lt_of_succ_lt hk⟩).card}
  else 0

/-- `c^λ_{µν} = N^{λ + ((p+q)^n)}_{µ + (p^n), ν + (q^n)}` of (3.7), for `λ, µ, ν ∈ Z^n_+`,
evaluated at the pair `p = q = ∑_i (|λ_i| + |µ_i| + |ν_i|) + 1`, which makes all three shapes
partitions (any such pair gives the same value, Lemma 3.7). -/
def lrc {n : ℕ} (la mu nu : GenPartition n) : ℕ :=
  let p : ℤ := ∑ i, (|la.1 i| + |mu.1 i| + |nu.1 i|) + 1
  lrN (shift la (p + p)) (shift mu p) (shift nu p)

end

end SuperTableaux.JacobiTrudi


