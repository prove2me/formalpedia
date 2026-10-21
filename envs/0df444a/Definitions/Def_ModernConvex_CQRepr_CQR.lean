-- Prove2me | Definitions.Def_ModernConvex_CQRepr_CQR
-- name    : ModernConvex_CQRepr_CQR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:31:50.88753+00:00
-- url     : https://prove2.me/theorems/bd2aa9bc-ba22-412c-a3cd-53df252eb436
-- title:
--   Ice cream cones, conic quadratic representable (CQr) sets, conic hull, polar, recessive cone, Legendre and projective transformations
-- statement:
--   For $m \ge 2$ the $m$-dimensional **ice cream** (Lorentz, second-order) cone is
--   $$L^m = \Bigl\{x = (x_1,\dots,x_m) \in \mathbb R^m \;\Bigm|\; x_m \ge \sqrt{x_1^2 + \cdots + x_{m-1}^2}\Bigr\}.$$
--   A **direct product of ice cream cones** is $\mathbf K = L^{m_1} \times \cdots \times L^{m_N}$, a cone in $\mathbb R^{m_1} \times \cdots \times \mathbb R^{m_N}$; $y \ge_{\mathbf K} 0$ means $y \in \mathbf K$ and $y >_{\mathbf K} 0$ means $y \in \operatorname{int}\mathbf K$. The file defines, following pp. 79–102 of the book:
--
--   1. The **set given by a conic quadratic representation** $\{x \in \mathbb R^n \mid \exists u \in \mathbb R^p : Ax + Bu + b \ge_{\mathbf K} 0\}$, the projection onto the $x$-space of the solution set of finitely many conic quadratic inequalities in $x$ and additional variables $u$.
--   2. A set $X \subset \mathbb R^n$ is **CQr** (conic quadratic representable, p. 86) if it is such a set for some product $\mathbf K$ of ice cream cones, some $p$ and some data $A, B, b$. No full-rank condition (Assumption A) is imposed on the representation (footnote 12).
--   3. The **conic hull** $X^+ = \{(x,t) \in \mathbb R^n \times \mathbb R : t > 0,\ t^{-1}x \in X\} \cup \{0\}$ (p. 93); its closure $\widehat X^+$ is the **closed conic hull** (p. 94).
--   4. The **polar** $X_* = \{y \in \mathbb R^n \mid y^Tx \le 1\ \forall x \in X\}$ (p. 96).
--   5. The **recessive cone** $\operatorname{Rec}(X) = \{h : x + th \in X\ \forall (x \in X, t \ge 0)\}$ (p. 102).
--   6. For $f : \mathbb R^n \to \mathbb R \cup \{+\infty\}$, the **Legendre transformation** $f_*(y) = \sup_x [y^Tx - f(x)]$ (p. 97).
--   7. For the same $f$, the epigraph of the **projective transformation** $\widehat f^+$ (p. 96): the closure of the epigraph of $f^+(x,s) = sf(x/s)$, $s > 0$, i.e. $\operatorname{Epi}\{\widehat f^+\} = \operatorname{cl}\{(x,t,s) \mid s > 0,\ s^{-1}(x,t) \in \operatorname{Epi}\{f\}\}$.
--
--   These are the objects of the calculus of conic quadratic representability in §3.3 of the book.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ` with the product topology (the Euclidean topology); the Euclidean norm $\|v\|_2$ is written out as `eucNorm` because Mathlib's norm on `Fin n → ℝ` is the sup norm. A product of ice cream cones is a structure `IceCreamProduct` (number of factors $N$, and $d_j = m_j - 1 \ge 1$ per factor); its vectors are indexed by pairs $(j, i)$ with $i \in \{0,\dots,d_j\}$, the last index of each block playing the role of $x_{m_j}$. A point $(x,t) \in \mathbb R^n \times \mathbb R$ of the conic hull is a vector of $\mathbb R^{n+1}$ whose last coordinate is $t$. Functions with values in $\mathbb R \cup \{+\infty\}$ are `EReal`-valued; theorems using them add the hypothesis that $f$ never takes the value $-\infty$. In the Legendre transformation $a - (+\infty) = -\infty$ for real $a$, so points where $f = +\infty$ do not contribute to the supremum. Triples of the projective transformation are ordered $(x,t,s)$ as in Proposition 3.3.2 (p. 96 lists them as $(x,s,t)$).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 79 (L^m, (3.1.1)), p. 86 (CQr set, footnotes 11–12), pp. 93–94 (conic hull, closed conic hull), p. 96 (projective transformation, polar), p. 97 (Legendre transformation), p. 102 (recessive cone)

import Mathlib

open Matrix

namespace ModernConvex.CQRepr

/-- The Euclidean norm `‖v‖₂ = √(∑ᵢ vᵢ²)` of a real vector indexed by a finite type. Written out
explicitly because the norm Mathlib puts on `ι → ℝ` is the sup norm. -/
noncomputable def eucNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The shape of a direct product `K = L^{m₁} × ⋯ × L^{m_N}` of ice cream cones (Ben-Tal–Nemirovski,
p. 79, (3.1.1)): the number `N` of factors and, for each factor `j`, the number `d j = m_j − 1 ≥ 1`
of its "norm" coordinates, so that the factor has dimension `m_j = d j + 1 ≥ 2`. -/
structure IceCreamProduct where
  /-- the number of factors -/
  N : ℕ
  /-- `d j + 1 = m_j` is the dimension of the `j`-th factor -/
  d : Fin N → ℕ
  /-- `m_j ≥ 2` (p. 79) -/
  two_le : ∀ j, 1 ≤ d j

/-- The coordinates of the space `ℝ^{m₁} × ⋯ × ℝ^{m_N}` in which `K` lives: the pair `⟨j, i⟩` is
coordinate `i` of block `j`; inside block `j` the coordinate `Fin.last (d j)` is the last one. -/
abbrev IceCreamProduct.Idx (K : IceCreamProduct) : Type := Σ j : Fin K.N, Fin (K.d j + 1)

/-- The cone `K = L^{m₁} × ⋯ × L^{m_N}` itself (p. 79): `y ∈ K` iff for every block `j` the last
entry of the block is at least the Euclidean norm of the first `m_j − 1` entries,
`y[j]_{m_j} ≥ √(y[j]₁² + ⋯ + y[j]_{m_j−1}²)`. As a subset of `K.Idx → ℝ`. -/
def IceCreamProduct.cone (K : IceCreamProduct) : Set (K.Idx → ℝ) :=
  {y | ∀ j : Fin K.N,
    Real.sqrt (∑ i : Fin (K.d j), y ⟨j, Fin.castSucc i⟩ ^ 2) ≤ y ⟨j, Fin.last (K.d j)⟩}

/-- The set given by a conic quadratic representation (p. 86):
`{x ∈ ℝⁿ | ∃ u ∈ ℝᵖ : Ax + Bu + b ≥_K 0}`, i.e. the projection onto the `x`-space of the solution set
of the system `Ax + Bu + b ∈ K`, where `K` is a direct product of ice cream cones. -/
def cqrSet {n p : ℕ} (K : IceCreamProduct) (A : Matrix K.Idx (Fin n) ℝ)
    (B : Matrix K.Idx (Fin p) ℝ) (b : K.Idx → ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ u : Fin p → ℝ, A *ᵥ x + B *ᵥ u + b ∈ K.cone}

/-- A set `X ⊂ ℝⁿ` is CQr — conic quadratic representable (p. 86) — if it is the projection onto
the `x`-space of the solution set of finitely many conic quadratic inequalities in `x` and
additional variables `u`: there are a direct product `K` of ice cream cones, a number `p` of
additional variables and data `A, B, b` with `X = {x | ∃ u : Ax + Bu + b ≥_K 0}`. As footnote 12
says, no Assumption A is imposed on the representing system. -/
def IsCQr {n : ℕ} (X : Set (Fin n → ℝ)) : Prop :=
  ∃ (K : IceCreamProduct) (p : ℕ) (A : Matrix K.Idx (Fin n) ℝ) (B : Matrix K.Idx (Fin p) ℝ)
    (b : K.Idx → ℝ), X = cqrSet K A B b

/-- The conic hull (p. 93) `X⁺ = {(x, t) ∈ ℝⁿ × ℝ : t > 0, t⁻¹x ∈ X} ∪ {0}` of `X ⊂ ℝⁿ`. A point
`(x, t)` of `ℝⁿ × ℝ` is a vector `z ∈ ℝⁿ⁺¹` with `x = Fin.init z` and `t = z (Fin.last n)`, the
book's lifting of `ℝⁿ` into `ℝⁿ⁺¹` by a new last coordinate. The closed conic hull is
`closure (conicHull X)` (p. 94). -/
def conicHull {n : ℕ} (X : Set (Fin n → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {z | 0 < z (Fin.last n) ∧ (z (Fin.last n))⁻¹ • Fin.init z ∈ X} ∪ {0}

/-- The polar (p. 96) `X∗ = {y ∈ ℝⁿ | yᵀx ≤ 1 ∀ x ∈ X}` of `X ⊂ ℝⁿ`. -/
def polar {n : ℕ} (X : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∀ x ∈ X, y ⬝ᵥ x ≤ 1}

/-- The recessive cone (p. 102) `Rec(X) = {h : x + th ∈ X ∀ (x ∈ X, t ≥ 0)}`. -/
def recessiveCone {n : ℕ} (X : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {h | ∀ x ∈ X, ∀ t : ℝ, 0 ≤ t → x + t • h ∈ X}

/-- The Legendre transformation (conjugate) (p. 97) `f∗(y) = sup_x [yᵀx − f(x)]` of a function
`f : ℝⁿ → ℝ ∪ {+∞}`, computed in `EReal`, where `a − (+∞) = −∞` for real `a`, so points with
`f(x) = +∞` do not contribute; `f∗(y) = −∞` only when `f ≡ +∞`. -/
noncomputable def legendre {n : ℕ} (f : (Fin n → ℝ) → EReal) (y : Fin n → ℝ) : EReal :=
  ⨆ x : Fin n → ℝ, (((y ⬝ᵥ x : ℝ)) : EReal) - f x

/-- The epigraph of the projective transformation `f̂⁺` of `f : ℝⁿ → ℝ ∪ {+∞}` (p. 96): the closure
of the epigraph of `f⁺(x, s) = s f(x/s)` (`s > 0`), i.e.
`Epi{f̂⁺} = cl {(x, t, s) | s > 0, s⁻¹(x, t) ∈ Epi{f}}`. Triples are ordered `(x, t, s)` as in
Proposition 3.3.2 (p. 96 lists the same epigraph as `(x, s, t)`). -/
def projectiveEpi {n : ℕ} (f : (Fin n → ℝ) → EReal) : Set ((Fin n → ℝ) × ℝ × ℝ) :=
  closure {z | 0 < z.2.2 ∧ f (z.2.2⁻¹ • z.1) ≤ ((z.2.2⁻¹ * z.2.1 : ℝ) : EReal)}

end ModernConvex.CQRepr


