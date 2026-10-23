-- Prove2me | Definitions.Def_BoxTDIMinMax_Separable_Setting
-- name    : BoxTDIMinMax_Separable_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:46.73599+00:00
-- url     : https://prove2.me/theorems/2cbbdc49-888d-4994-88b8-3d0ce7522fe6
-- title:
--   §1.1, §2, §2.2, §3.1–3.2, pp. 4, 7, 10, 12–14 — TDI and box-TDI systems, integral points R̈, discrete convex functions, Φ-fitting and Φ-compatible pairs
-- statement:
--   The objects of Frank and Murota's min-max theorem for separable discrete convex functions over the integral points of a box-TDI polyhedron.
--
--   **Linear systems and total dual integrality.** Let $S$ be a finite ground set (the columns) and $I$ a finite set of rows. For a rational matrix $A\in\mathbb Q^{I\times S}$ and a rational vector $b\in\mathbb Q^I$, the system $Ax\ge b$ defines the polyhedron $R=\{x\in\mathbb R^S : Ax\ge b\}$. For an integral cost vector $c\in\mathbb Z^S$, linear programming duality pairs
--   $$\min\{cx : Ax\ge b\} \;=\; \max\{yb : y\ge 0,\ yA=c\}. \qquad (2.1)$$
--   The system is **totally dual integral (TDI)** if, for every integral $c$ for which the maximum in (2.1) is finite, the maximum has an integral optimal solution $y$. Here "the maximum is finite" means that the dual feasible set $\{y\in\mathbb R^I : y\ge 0,\ yA=c\}$ is nonempty and the dual objective $yb$ is bounded above on it.
--
--   The system $Ax\ge b$ is **box-TDI** if, for every pair of rational (finite-valued) bounding vectors $f\le g$ in $\mathbb Q^S$, the system $[Ax\ge b,\ f\le x\le g]$ is TDI; this system consists of the rows of $A$, the rows $x\ge f$ and the rows $-x\ge -g$. Two auxiliary systems are also named: $[Ax\ge b,\ f'\le x\le g']$ for bounds $f'$, $g'$ some of whose entries are infinite (only the finite bounds give rows), and the system
--   $$[(x_1,x_2)\ge 0,\ Qx_2-Qx_1\ge p_0] \qquad (2.8)$$
--   in the variables $(x_1,x_2)\in\mathbb R^{S}\times\mathbb R^S$, where $p_0=p-Qz^*$.
--
--   **Integral points.** For an integral matrix $Q\in\mathbb Z^{I\times S}$ and an integral vector $p\in\mathbb Z^I$ let $R=\{x : Qx\ge p\}\subseteq\mathbb R^S$ and let
--   $$\ddot R = R\cap\mathbb Z^S \qquad (1.1)$$
--   be its set of integral points.
--
--   **Discrete convex functions.** A function $\varphi:\mathbb Z\to\mathbb Z\cup\{+\infty\}$ has effective domain $\mathrm{dom}(\varphi)=\{k : \varphi(k)<+\infty\}$. It is **discrete convex** if
--   $$\varphi(k-1)+\varphi(k+1)\ge 2\varphi(k)\quad\text{for each } k\in\mathrm{dom}(\varphi) \qquad (1.2)$$
--   and $\mathrm{dom}(\varphi)$ is the set of integers in a (possibly unbounded, possibly empty) interval. Given $\varphi_s$ for each $s\in S$, the separable function is $\Phi(z)=\sum_{s\in S}\varphi_s(z(s))$ for $z\in\mathbb Z^S$ (1.4).
--
--   **Fitting and compatible pairs.** A pair $(k^*,\ell^*)$ of integers is **$\varphi$-fitting** if $\varphi(k^*)$ is finite and
--   $$\varphi(k^*)-\varphi(k^*-1)\le \ell^*\le \varphi(k^*+1)-\varphi(k^*), \qquad (3.1)$$
--   where a difference with an infinite neighbour is $-\infty$ on the left and $+\infty$ on the right. A pair $(z^*,y^*)$ of an integral $z^*\in\mathbb Z^S$ and an integral row vector $y^*\in\mathbb Z^I$ is **$\Phi$-compatible** with respect to $Q$ if $(z^*(s),w^*(s))$ is $\varphi_s$-fitting for every $s\in S$, where $w^*=y^*Q$; that is, $\Phi'(z^*-\mathbf 1)\le y^*Q\le\Phi'(z^*)$ (3.9).
--
--   **Slopes and condition (2.9).** For $k$ with $\varphi(k)$ finite, the lower slope is $\ell=\varphi(k)-\varphi(k-1)\in\mathbb Z\cup\{-\infty\}$ and the upper slope is $u=\varphi(k+1)-\varphi(k)\in\mathbb Z\cup\{+\infty\}$. For bounds $\ell:S\to\mathbb Z\cup\{-\infty\}$, $u:S\to\mathbb Z\cup\{+\infty\}$, write $\tilde\ell(X)=\sum_{s\in X}\ell(s)$. The condition
--   $$\tilde\ell(S^-)\le\tilde u(S^+) \qquad (2.9)$$
--   is required for every pair $(S^-,S^+)$ of disjoint subsets of $S$ with $z^*+\chi_{S^+}-\chi_{S^-}\in R$ (2.10), where $\chi_X$ is the characteristic vector of $X$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** $+\infty$ is `⊤` in `WithTop ℤ`; $\ell$, $u$ and the sums in (2.9) live in `EReal`. The inequalities (3.1) are written additively, $\varphi(k)\le\varphi(k-1)+\ell^*$ and $\varphi(k)+\ell^*\le\varphi(k+1)$, so no $\infty-\infty$ occurs. Two readings are disclosed. (i) (1.2) is required on the domain, and the interval-domain property, which the page states as a fact about discrete convex functions, is part of the definition: without it the domain $\{0,3\}$ would be admitted and Proposition 3.1 would fail. (ii) $\varphi$-fitting includes "$\varphi(k^*)$ finite", since (3.1) involves $\varphi(k^*)$ on both sides. The slopes `lowerSlope`/`upperSlope` are defined by cases; when $\varphi(k)=+\infty$ they return a junk integer and are never used there. Dual variables of TDI are real vectors; integral data $Q$, $p$ enter TDI through their rational casts.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, pp. 4, 7, 10, 12–14, (1.1), (1.2), (1.4), (2.1), box-TDI (p. 7), (2.8), (2.9)–(2.10), (3.1), (3.3), (3.9), ℓ and u (p. 14)

import Mathlib

namespace BoxTDIMinMax.Separable

open Matrix

/-! # Box-TDI systems, integral points, separable discrete convex functions

Frank–Murota, *A Discrete Convex Min-Max Formula for Box-TDI Polyhedra*, arXiv:2007.03507v3:
§1.1 (p. 4, (1.1)–(1.4)), §2 (p. 7, (2.1), TDI and box-TDI), §2.2 (p. 10, (2.9)–(2.10)),
§3.1–3.2 (pp. 12–14, (3.1)–(3.4), (3.9), ℓ and u). -/

section LP

variable {ι S : Type*} [Fintype ι] [Fintype S]

/-- Dual feasible set of (2.1) for the rational system `A x ≥ b` and the integral cost `c`:
real vectors `y` on the rows with `y ≥ 0` and `y A = c`. -/
def DualFeas (A : Matrix ι S ℚ) (c : S → ℤ) : Set (ι → ℝ) :=
  {y | 0 ≤ y ∧ y ᵥ* (A.map ((↑) : ℚ → ℝ)) = fun s => (c s : ℝ)}

/-- Dual objective `y b` of (2.1). -/
noncomputable def dualObj (b : ι → ℚ) (y : ι → ℝ) : ℝ := ∑ i, y i * (b i : ℝ)

/-- (2.1), p. 7: the rational system `A x ≥ b` is **totally dual integral (TDI)** if, for every
integral cost vector `c` for which the maximum `max {y b : y ≥ 0, y A = c}` is finite (the dual is
feasible and its objective is bounded above on the feasible set), this maximum has an integral
optimal solution `y`. -/
def IsTDI (A : Matrix ι S ℚ) (b : ι → ℚ) : Prop :=
  ∀ c : S → ℤ, (DualFeas A c).Nonempty → BddAbove (dualObj b '' DualFeas A c) →
    ∃ y : ι → ℤ, (fun i => (y i : ℝ)) ∈ DualFeas A c ∧
      ∀ y' ∈ DualFeas A c, dualObj b y' ≤ dualObj b (fun i => (y i : ℝ))

/-- The matrix of the system `[A x ≥ b, f ≤ x ≤ g]`, rows `ι ⊕ (S ⊕ S)`: the rows of `A`, then
the rows `x ≥ f` (identity), then the rows `-x ≥ -g` (minus identity). -/
def boxMat [DecidableEq S] (A : Matrix ι S ℚ) : Matrix (ι ⊕ (S ⊕ S)) S ℚ :=
  Matrix.fromRows A (Matrix.fromRows 1 (-1))

/-- The right-hand side of `[A x ≥ b, f ≤ x ≤ g]`: `b`, then `f`, then `-g`. -/
def boxRhs (b : ι → ℚ) (f g : S → ℚ) : ι ⊕ (S ⊕ S) → ℚ :=
  Sum.elim b (Sum.elim f (-g))

/-- p. 7: `A x ≥ b` is **box-TDI** if `[A x ≥ b, f ≤ x ≤ g]` is TDI for every choice of rational
(finite-valued) bounding vectors `f ≤ g`. -/
def IsBoxTDI [DecidableEq S] (A : Matrix ι S ℚ) (b : ι → ℚ) : Prop :=
  ∀ f g : S → ℚ, f ≤ g → IsTDI (boxMat A) (boxRhs b f g)

/-- The integral matrix `Q` viewed as a rational matrix. -/
def ratMat (Q : Matrix ι S ℤ) : Matrix ι S ℚ := Q.map ((↑) : ℤ → ℚ)

/-- The integral vector `p` viewed as a rational vector. -/
def ratVec (p : ι → ℤ) : ι → ℚ := fun i => (p i : ℚ)

/-- The real polyhedron `{x ∈ ℝ^S : A x ≥ b}` of a rational system. -/
def realPts (A : Matrix ι S ℚ) (b : ι → ℚ) : Set (S → ℝ) :=
  {x | ∀ i, (b i : ℝ) ≤ (A.map ((↑) : ℚ → ℝ) *ᵥ x) i}

/-- The matrix of `[A x ≥ b, f' ≤ x ≤ g']` for bounds with infinite entries (Proposition 2.9,
p. 9): `f'(s)` is finite exactly for `s ∈ Tf` and `g'(s)` exactly for `s ∈ Tg`, and only the
finite bounds give rows: `x(t) ≥ f'(t)` for `t ∈ Tf` and `-x(t) ≥ -g'(t)` for `t ∈ Tg`. -/
def partBoxMat [DecidableEq S] (A : Matrix ι S ℚ) (Tf Tg : Finset S) :
    Matrix (ι ⊕ (Tf ⊕ Tg)) S ℚ :=
  Matrix.fromRows A (Matrix.fromRows (Matrix.of fun (t : Tf) s => if s = t.1 then 1 else 0)
    (Matrix.of fun (t : Tg) s => if s = t.1 then -1 else 0))

/-- The right-hand side of `[A x ≥ b, f' ≤ x ≤ g']` matching `partBoxMat`. -/
def partBoxRhs (b : ι → ℚ) (Tf Tg : Finset S) (f' g' : S → ℚ) : ι ⊕ (Tf ⊕ Tg) → ℚ :=
  Sum.elim b (Sum.elim (fun t => f' t.1) (fun t => -g' t.1))

/-- (1.1), p. 4: `R̈ = R ∩ ℤ^S`, the integral points of `R = {x : Q x ≥ p}` for integral `Q`, `p`.
For an integral vector `z`, the real inequality `Q z ≥ p` is the integer one. -/
def intPts (Q : Matrix ι S ℤ) (p : ι → ℤ) : Set (S → ℤ) := {z | ∀ i, p i ≤ (Q *ᵥ z) i}

/-- The matrix of the system (2.8), p. 10, `[(x₁, x₂) ≥ 0, Q x₂ - Q x₁ ≥ p₀]`: columns `S ⊕ S`
(`x₁` on `inl`, `x₂` on `inr`), rows `(S ⊕ S) ⊕ ι` (first the nonnegativity rows, then
`-Q x₁ + Q x₂ ≥ p₀`). -/
def auxMat [DecidableEq S] (Q : Matrix ι S ℤ) : Matrix ((S ⊕ S) ⊕ ι) (S ⊕ S) ℚ :=
  Matrix.fromRows 1 (Matrix.fromCols (-ratMat Q) (ratMat Q))

/-- The right-hand side of (2.8): `0` on the nonnegativity rows and `p₀ = p - Q z*` on the rows
of `Q`. -/
def auxRhs (Q : Matrix ι S ℤ) (p : ι → ℤ) (zStar : S → ℤ) : (S ⊕ S) ⊕ ι → ℚ :=
  Sum.elim 0 (ratVec (p - Q *ᵥ zStar))

end LP

section DiscreteConvex

/-- The effective domain of `φ : ℤ → ℤ ∪ {+∞}` is the set of integers in an interval: if `φ a`
and `φ c` are finite and `a ≤ b ≤ c`, then `φ b` is finite (p. 4, last sentence of the paragraph
of (1.2)–(1.3)). -/
def IntervalDom (φ : ℤ → WithTop ℤ) : Prop :=
  ∀ a b c : ℤ, a ≤ b → b ≤ c → φ a ≠ ⊤ → φ c ≠ ⊤ → φ b ≠ ⊤

/-- (1.2), p. 4: `φ : ℤ → ℤ ∪ {+∞}` (with `+∞ = ⊤`) is **discrete convex** if
`φ(k - 1) + φ(k + 1) ≥ 2 φ(k)` for each `k ∈ dom φ`, and its effective domain is the set of
integers in an interval (as the page states for discrete convex functions). The identically `+∞`
function is not excluded. -/
def DiscConvex (φ : ℤ → WithTop ℤ) : Prop :=
  (∀ k : ℤ, φ k ≠ ⊤ → φ k + φ k ≤ φ (k - 1) + φ (k + 1)) ∧ IntervalDom φ

/-- (1.4), p. 4: the separable function `Φ(z) = ∑_{s ∈ S} φ_s(z(s))`, valued in `ℤ ∪ {+∞}`. -/
def Phi {S : Type*} [Fintype S] (phi : S → ℤ → WithTop ℤ) (z : S → ℤ) : WithTop ℤ :=
  ∑ s, phi s (z s)

/-- (3.1), p. 12, written additively: `(k, l)` is **φ-fitting** if `φ(k)` is finite and
`φ(k) - φ(k - 1) ≤ l ≤ φ(k + 1) - φ(k)`, i.e. `φ(k) ≤ φ(k - 1) + l` and `φ(k) + l ≤ φ(k + 1)`.
A neighbour equal to `+∞` makes the corresponding inequality automatic (`φ'(k) = +∞`,
resp. `φ'(k - 1) = -∞`). -/
def Fitting (φ : ℤ → WithTop ℤ) (k l : ℤ) : Prop :=
  φ k ≠ ⊤ ∧ φ k ≤ φ (k - 1) + (l : WithTop ℤ) ∧ φ k + (l : WithTop ℤ) ≤ φ (k + 1)

/-- (3.9), p. 13: the pair `(z, y)` of integral vectors is **Φ-compatible** with respect to `Q` if
`(z, w)` is Φ-fitting (3.3) for `w = y Q`, i.e. `Φ'(z - 1) ≤ y Q ≤ Φ'(z)` coordinatewise. -/
def Compatible {ι S : Type*} [Fintype ι] (phi : S → ℤ → WithTop ℤ) (Q : Matrix ι S ℤ)
    (z : S → ℤ) (y : ι → ℤ) : Prop :=
  ∀ s, Fitting (phi s) (z s) ((y ᵥ* Q) s)

/-- p. 14: `ℓ(s) = φ'_s(z(s) - 1) = φ(k) - φ(k - 1)` at `k = z(s)`, in `ℤ ∪ {-∞}`: it is `-∞`
when `φ(k - 1) = +∞`. Meaningful only when `φ(k)` is finite; when `φ(k) = +∞` and `φ(k - 1)` is
finite the value is the junk integer `0 - φ(k - 1)`. -/
noncomputable def lowerSlope (φ : ℤ → WithTop ℤ) (k : ℤ) : EReal :=
  if φ (k - 1) = ⊤ then ⊥
  else (((φ k).untopD 0 - (φ (k - 1)).untopD 0 : ℤ) : ℝ)

/-- p. 14: `u(s) = φ'_s(z(s)) = φ(k + 1) - φ(k)` at `k = z(s)`, in `ℤ ∪ {+∞}`: it is `+∞`
when `φ(k + 1) = +∞`. Meaningful only when `φ(k)` is finite; when `φ(k) = +∞` and `φ(k + 1)` is
finite the value is the junk integer `φ(k + 1) - 0`. -/
noncomputable def upperSlope (φ : ℤ → WithTop ℤ) (k : ℤ) : EReal :=
  if φ (k + 1) = ⊤ then ⊤
  else (((φ (k + 1)).untopD 0 - (φ k).untopD 0 : ℤ) : ℝ)

end DiscreteConvex

section MainTool

variable {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]

/-- The characteristic vector `χ_T` of `T ⊆ S`. -/
def chi (T : Finset S) : S → ℤ := fun s => if s ∈ T then 1 else 0

/-- (2.9)–(2.10), p. 10: `ℓ̃(S⁻) ≤ ũ(S⁺)` for every pair `(S⁻, S⁺)` of disjoint subsets of `S`
with `z' = z + χ_{S⁺} - χ_{S⁻} ∈ R` (for integral `z'`, membership in `R` is membership in `R̈`).
Here `ℓ̃(X) = ∑_{s ∈ X} ℓ(s)` (p. 4). The sums are in `EReal`; for bounds `ℓ : S → ℤ ∪ {-∞}` and
`u : S → ℤ ∪ {+∞}` the left sum never contains `+∞` and the right sum never `-∞`. -/
def Cond29 (Q : Matrix ι S ℤ) (p : ι → ℤ) (z : S → ℤ) (lo up : S → EReal) : Prop :=
  ∀ Sm Sp : Finset S, Disjoint Sm Sp → z + chi Sp - chi Sm ∈ intPts Q p →
    ∑ s ∈ Sm, lo s ≤ ∑ s ∈ Sp, up s

end MainTool

end BoxTDIMinMax.Separable


