-- Prove2me | Definitions.Def_ModernConvex_Truss_Compliance
-- name    : ModernConvex_Truss_Compliance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:31:50.539188+00:00
-- url     : https://prove2.me/theorems/ed1d79c5-439b-4d1a-a042-8b9a94624136
-- title:
--   Ground structures, bar-stiffness matrix, compliance $\mathrm{Compl}_f(t)$, ice cream cones, almost solvability and conic quadratic representability
-- statement:
--   The objects of §3.4.3 of the book (truss topology design) and the conic notions it uses.
--
--   1. **Cones** (pp. 45–51). A set $\mathbf K \subset \mathbb R^\iota$ ($\iota$ a finite index set) is a **convex cone** if it is nonempty, closed under addition and under multiplication by nonnegative reals; it is **pointed** if $a \in \mathbf K$ and $-a \in \mathbf K$ imply $a = 0$. A **good cone** (the standing assumption of p. 46) is a pointed closed convex cone with a nonempty interior. Its **dual cone** is $\mathbf K_* = \{\lambda : \lambda^Ta \ge 0\ \forall a \in \mathbf K\}$. **Assumption A** (p. 53) for a matrix $A$: $Ax = Ax'$ implies $x = x'$ (full column rank).
--   2. **Almost solvability** (p. 62). The linear vector inequality $Ax - b \ge_{\mathbf K} 0$ (i.e. $Ax - b \in \mathbf K$) is almost solvable if for every $\varepsilon > 0$ there is $b'$ with $\|b' - b\|_2 < \varepsilon$ such that $Ax - b' \ge_{\mathbf K} 0$ has a solution $x$.
--   3. **Ice cream cone** (p. 79). $\mathbf L^k = \{x \in \mathbb R^k : x_k \ge \sqrt{x_1^2 + \dots + x_{k-1}^2}\}$; the first $k - 1$ coordinates are indexed by an arbitrary finite set and the last one is singled out.
--   4. **CQr sets and functions** (pp. 86–87). A set $X \subset \mathbb R^N$ is conic quadratic representable (CQr) if there are finitely many conic quadratic inequalities $A_j(x; u) - b_j \ge_{\mathbf L^{m_j}} 0$, $j = 1, \dots, J$, $m_j \ge 2$, in $x$ and additional variables $u \in \mathbb R^l$, such that $x \in X$ iff some $u$ makes all of them hold. A function $g : \mathbb R^N \to \mathbb R \cup \{+\infty\}$ is CQr if its epigraph $\{(x, \tau) : g(x) \le \tau\}$ is a CQr set.
--   5. **Ground structure and truss** (pp. 120–121). A ground structure $(n, m, B_1, \dots, B_n)$ consists of $m \times k_i$ real matrices $B_i$; a truss is $t \in \mathbb R^n$, $t \ge 0$; a load is $f \in \mathbb R^m$. The **bar-stiffness matrix** is
--   $$A(t) = \sum_{i=1}^n t_i B_i B_i^T \qquad (3.4.41).$$
--   6. **Compliance** (p. 121). $\mathrm{Compl}_f(t) = \tfrac12 f^Tv$, where $v$ is a solution of the equilibrium equation $A(t)v = f$ (3.4.42), and $\mathrm{Compl}_f(t) = +\infty$ when that equation has no solution. The **extended compliance** (p. 127) also takes the value $+\infty$ at every $t$ that is not nonnegative.
--   7. **Potential energy** (3.4.43): $\mathcal C_{t,f}(v) = \tfrac12 v^TA(t)v - f^Tv$.
--   8. **The conic quadratic inequality (3.4.49)** (pp. 124–126). $B(t) = \sqrt2\,[\sqrt{t_1}B_1^T; \sqrt{t_2}B_2^T; \dots; \sqrt{t_n}B_n^T]$ (3.4.46), with rows indexed by pairs $(i, j)$, $j \le k_i$; the matrix $A$ and vector $b$ of (3.4.49) are
--   $$Av = \begin{pmatrix} B(t)v \\ -f^Tv \\ +f^Tv\end{pmatrix}, \qquad b = \begin{pmatrix} 0 \\ -1-\tau \\ -1+\tau\end{pmatrix},$$
--   so that $A^T = [\sqrt{2t_1}B_1; \dots; \sqrt{2t_n}B_n; -f; f]$, and $Av - b \ge_{\mathbf L^k} 0$, $k = \sum_i k_i + 2$, with the last row as the cone's last coordinate.
--
--   **Formalization Note** Vectors are functions on finite index types (`Fin m → ℝ`, or a sum/sigma type for the stacked inequality (3.4.49)). The compliance takes values in `EReal`: `⊤` exactly when $A(t)v = f$ has no solution, otherwise the real number $\tfrac12 f^Tv$ for a chosen solution $v$ (independent of the choice since $A(t)$ is symmetric); no junk value is used. $\|b'-b\|_2$ is written as a square root of a sum of squares. In the CQr definition the cones $\mathbf L^{m_j}$ have $m_j = p_j + 2 \ge 2$, and $(x; u)$ is the concatenation of $x$ and $u$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 45–46, 51, 53 (cones, K∗, Assumption A), p. 62 (almost solvable), p. 79 (Lᵏ), pp. 86–87 (CQr), pp. 120–121 ((3.4.41), (3.4.42), compliance), pp. 122–126 ((3.4.43), (3.4.46), (3.4.49)), p. 127 (extended compliance)

import Mathlib

open Matrix

namespace ModernConvex.Truss

/-! ## Cones and linear vector inequalities (Lecture 2, pp. 45–62; Lecture 3, p. 79) -/

/-- A convex cone in `ℝ^ι` in the sense of Ben-Tal–Nemirovski, p. 45 (conditions 1 and 2): a
nonempty set closed under addition and under multiplication by nonnegative reals. -/
def IsConvexCone {ι : Type} [Fintype ι] (K : Set (ι → ℝ)) : Prop :=
  K.Nonempty ∧ (∀ a ∈ K, ∀ a' ∈ K, a + a' ∈ K) ∧ (∀ a ∈ K, ∀ s : ℝ, 0 ≤ s → s • a ∈ K)

/-- `K` is pointed (p. 45, condition 3): `a ∈ K` and `−a ∈ K` imply `a = 0`. -/
def IsPointedSet {ι : Type} [Fintype ι] (K : Set (ι → ℝ)) : Prop :=
  ∀ a : ι → ℝ, a ∈ K → -a ∈ K → a = 0

/-- The standing assumption on the cone `K` of a vector inequality `≥_K` (p. 46): `K` is a pointed
and closed convex cone with a nonempty interior. -/
def IsGoodCone {ι : Type} [Fintype ι] (K : Set (ι → ℝ)) : Prop :=
  IsConvexCone K ∧ IsPointedSet K ∧ IsClosed K ∧ (interior K).Nonempty

/-- The cone dual to `K` (p. 51): `K∗ = {λ | λᵀa ≥ 0 ∀ a ∈ K}`. -/
def dualCone {ι : Type} [Fintype ι] (K : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {l | ∀ a ∈ K, 0 ≤ l ⬝ᵥ a}

/-- Assumption A (p. 53): the matrix `A` has full column rank, i.e. `x ↦ Ax` has trivial kernel. -/
def AssumptionA {ι κ : Type} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) : Prop :=
  Function.Injective A.mulVec

/-- The linear vector inequality `Ax − b ≥_K 0` is *almost solvable* (Proposition 2.4.2(ii),
p. 62): for every `ε > 0` there is `b′` with `‖b′ − b‖₂ < ε` such that `Ax − b′ ≥_K 0` is
solvable. -/
def IsAlmostSolvable {ι κ : Type} [Fintype ι] [Fintype κ] (K : Set (ι → ℝ)) (A : Matrix ι κ ℝ)
    (b : ι → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ b' : ι → ℝ, Real.sqrt (∑ i, (b' i - b i) ^ 2) < ε ∧
    ∃ x : κ → ℝ, A *ᵥ x - b' ∈ K

/-- The ice cream (Lorentz) cone (p. 79), `Lᵏ = {x ∈ ℝᵏ | x_k ≥ √(x₁² + ⋯ + x²_{k−1})}`, with the
coordinates `x₁, …, x_{k−1}` indexed by a finite type `ι` (`Sum.inl`) and the last coordinate `x_k`
by `Sum.inr ()`. -/
def lorentzCone (ι : Type) [Fintype ι] : Set (ι ⊕ Unit → ℝ) :=
  {x | Real.sqrt (∑ j, x (Sum.inl j) ^ 2) ≤ x (Sum.inr ())}

/-! ## Conic quadratic representability (pp. 86–87) -/

/-- A set `X ⊂ ℝ^α` is CQr (p. 86): there are finitely many conic quadratic inequalities
`Aⱼ(x; u) − bⱼ ≥_{L^{mⱼ}} 0`, `j = 1, …, N`, in `x` and additional variables `u ∈ ℝˡ`, such that
`x ∈ X ⇔ ∃ u : Aⱼ(x; u) − bⱼ ≥_{L^{mⱼ}} 0` for all `j`. Here `mⱼ = pⱼ + 2 ≥ 2`, so `L^{mⱼ}` has the
`pⱼ + 1` coordinates `Fin (pⱼ + 1)` before its last one; `(x; u)` is `Sum.elim x u`. -/
def IsCQrSet {α : Type} [Fintype α] (X : Set (α → ℝ)) : Prop :=
  ∃ (l N : ℕ) (p : Fin N → ℕ) (A : (j : Fin N) → Matrix (Fin (p j + 1) ⊕ Unit) (α ⊕ Fin l) ℝ)
    (b : (j : Fin N) → Fin (p j + 1) ⊕ Unit → ℝ),
    ∀ x : α → ℝ, x ∈ X ↔
      ∃ u : Fin l → ℝ, ∀ j : Fin N, A j *ᵥ Sum.elim x u - b j ∈ lorentzCone (Fin (p j + 1))

/-- A function `g : ℝ^β → ℝ ∪ {+∞}` is CQr (p. 87) if its epigraph
`Epi{g} = {(x, τ) | g(x) ≤ τ}` is a CQr set; `(x, τ)` is `z` with `x = z ∘ Sum.inl` and
`τ = z (Sum.inr ())`. -/
def IsCQrFunction {β : Type} [Fintype β] (g : (β → ℝ) → EReal) : Prop :=
  IsCQrSet {z : β ⊕ Unit → ℝ | g (fun i => z (Sum.inl i)) ≤ ((z (Sum.inr ()) : ℝ) : EReal)}

/-! ## Ground structures, trusses, compliance (§3.4.3, pp. 120–127)

A ground structure `(n, m, B₁, …, Bₙ)` is given by `B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ`,
`Bᵢ` an `m × kᵢ` matrix; a truss is `t : Fin n → ℝ` with `t ≥ 0`; a load is `f : Fin m → ℝ`. -/

/-- The bar-stiffness matrix (3.4.41): `A(t) = ∑ᵢ tᵢ Bᵢ Bᵢᵀ`. -/
def stiffness {n m : ℕ} {k : Fin n → ℕ} (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ)
    (t : Fin n → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ i, t i • (B i * (B i)ᵀ)

open Classical in
/-- The compliance `Compl_f(t)` (p. 121): `½ fᵀv`, where `v` is a solution of the equilibrium
equation `A(t)v = f` (3.4.42), and `+∞` when that equation has no solutions. (`fᵀv` is the same for
every solution, since `A(t)` is symmetric, so the chosen solution does not matter.) -/
noncomputable def compliance {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (f : Fin m → ℝ) (t : Fin n → ℝ) : EReal :=
  if h : ∃ v : Fin m → ℝ, stiffness B t *ᵥ v = f then (((1 / 2 : ℝ) * (f ⬝ᵥ h.choose) : ℝ) : EReal)
  else ⊤

open Classical in
/-- The compliance extended by the value `+∞` to the `t`'s that are not nonnegative
(Proposition 3.4.5, p. 127). -/
noncomputable def extendedCompliance {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (f : Fin m → ℝ) (t : Fin n → ℝ) : EReal :=
  if 0 ≤ t then compliance B f t else ⊤

/-- The potential energy of the loaded system (3.4.43): `C_{t,f}(v) = ½ vᵀA(t)v − fᵀv`. -/
noncomputable def potentialEnergy {n m : ℕ} {k : Fin n → ℕ} (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ)
    (t : Fin n → ℝ) (f : Fin m → ℝ) (v : Fin m → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (v ⬝ᵥ (stiffness B t *ᵥ v)) - f ⬝ᵥ v

/-- The matrix (3.4.46): `B(t) = √2 [√t₁ B₁ᵀ; √t₂ B₂ᵀ; …; √tₙ Bₙᵀ]`, whose rows are indexed by the
pairs `(i, j)`, `j < kᵢ` (row `j` of the block `√2 √tᵢ Bᵢᵀ`). -/
noncomputable def stackedMatrix {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) :
    Matrix (Σ i, Fin (k i)) (Fin m) ℝ :=
  Matrix.of fun r c => Real.sqrt 2 * Real.sqrt (t r.1) * B r.1 c r.2

/-- The index set of the conic quadratic inequality (3.4.49): the rows of `B(t)`, then the row of
`−fᵀv` (`Sum.inl (Sum.inr ())`), then the row of `+fᵀv` (`Sum.inr ()`), the last coordinate of the
ice cream cone `Lᵏ`, `k = ∑ᵢ kᵢ + 2`. -/
abbrev CQIIndex {n : ℕ} (k : Fin n → ℕ) : Type := ((Σ i, Fin (k i)) ⊕ Unit) ⊕ Unit

/-- The matrix `A` of (3.4.49): `Av = (B(t)v; −fᵀv; +fᵀv)`, so that
`Aᵀ = [√(2t₁)B₁; …; √(2tₙ)Bₙ; −f; f]` (p. 126). -/
noncomputable def cqiMatrix {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (f : Fin m → ℝ) :
    Matrix (CQIIndex k) (Fin m) ℝ :=
  Matrix.of fun r c =>
    match r with
    | Sum.inl (Sum.inl q) => stackedMatrix B t q c
    | Sum.inl (Sum.inr _) => -f c
    | Sum.inr _ => f c

/-- The right-hand side `b` of (3.4.49): `bᵀ = [0; …; 0; −1 − τ; −1 + τ]` (p. 126). -/
def cqiRhs {n : ℕ} (k : Fin n → ℕ) (τ : ℝ) : CQIIndex k → ℝ
  | Sum.inl (Sum.inl _) => 0
  | Sum.inl (Sum.inr _) => -1 - τ
  | Sum.inr _ => -1 + τ

end ModernConvex.Truss


