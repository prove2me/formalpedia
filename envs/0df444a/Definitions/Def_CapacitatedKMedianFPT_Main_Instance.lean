-- Prove2me | Definitions.Def_CapacitatedKMedianFPT_Main_Instance
-- name    : CapacitatedKMedianFPT_Main_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:26.524758+00:00
-- url     : https://prove2.me/theorems/5a4440a1-8a81-427d-bb48-a2177a6e389e
-- title:
--   Capacitated k-median instances, solutions, cost, optimality and geometric rounding
-- statement:
--   Basic objects of capacitated $k$-median (§2).
--
--   An **instance** $I=((C\cup F,d),U,k)$ consists of a finite metric space $(C\cup F,d)$ whose points are clients $C$ and candidate facilities $F$ (a point may be both), a capacity $U_f\in\mathbb Z_{\ge0}$ for every facility (zero allowed), and an integer $k$ with $1\le k\le|F|$. Its size is $n=|C|+|F|$.
--
--   1. A **solution** is a pair $(S,\varphi)$ with $S\subseteq F$, $|S|=k$, and $\varphi:C\to S$ with $|\varphi^{-1}(f)|\le U_f$ for all $f\in S$. Its cost is $\mathrm{cost}(\varphi)=\sum_{c\in C}d(c,\varphi(c))$.
--   2. The instance is **feasible** if some $k$ facilities have total capacity at least $|C|$, i.e. the $k$ largest capacities sum to at least $|C|$.
--   3. $(S,\varphi)$ is **optimal** if its cost is at most that of every solution, and a **$\rho$-approximation** if its cost is at most $\rho$ times the cost of every solution, i.e. at most $\rho\cdot\mathrm{OPT}(I)$.
--   4. An indexed optimum lists the $k$ facilities of an optimal solution as $o^\star_1,\dots,o^\star_k$; $n_i=|\varphi^{\star-1}(o^\star_i)|$.
--   5. The **uncapacitated** solutions ignore capacities: $S\subseteq F$, $|S|=k$, $\varphi:C\to S$.
--   6. $I$ has **integer distances up to $D$** if $d(x,y)\in\{1,\dots,D\}$ for all distinct points; from §3 on, $D=\lceil 10n^2/\varepsilon\rceil$.
--   7. **Geometric rounding**: $\mu_\varepsilon(0)=0$ and $\mu_\varepsilon(x)=\bigl\lfloor(1+\varepsilon)^{\lceil\log_{1+\varepsilon}x\rceil}\bigr\rfloor$ for integers $x\ge1$.
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note** Points form a finite type `P`; every point is a client or a facility. Assignments are functions `P → P` whose values at non-clients are never read. Approximation is stated against every solution, so $\mathrm{OPT}$ is never formed as an infimum. The metric axioms include $d(x,y)>0$ for $x\neq y$, so clients at the same location are the same point.
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 5, §2 Instances; p. 5–6, Geometric rounding; p. 6, §3 standing assumptions (integer distances up to 10n²/ε, indexed optimum, n_i); p. 9, Algorithm 1 (D = ⌈10n²/ε⌉, uncapacitated instance)

import Mathlib

set_option autoImplicit false

/-!
# Capacitated k-median: instances, solutions, cost, optimality, geometric rounding

Anand, Huang, Jaiswal, Kumar, Lee, Yadav, *A Tight FPT Approximation for Capacitated k-Median*,
STOC 2027 submission #1646 (October 2026), §2 (p. 5–6) and §3 (p. 6–9).
-/

namespace CapacitatedKMedianFPT.Main

open scoped BigOperators

noncomputable section

/-- The data `((C ∪ F, d), U, k)` of a capacitated k-median instance (§2, p. 5) on a point type `P`:
distances `d`, clients `C`, candidate facilities `F` (the two may overlap), capacities `U f ∈ ℕ`
(zero allowed; values off `F` are never read) and the number `k` of facilities to open. -/
structure Instance (P : Type) where
  d : P → P → ℝ
  C : Finset P
  F : Finset P
  U : P → ℕ
  k : ℕ

variable {P : Type} [Fintype P] [DecidableEq P]

namespace Instance

/-- §2, p. 5: `(C ∪ F, d)` is a finite metric space (every point of `P` is a client or a facility),
and `1 ≤ k ≤ |F|`. -/
structure IsValid (I : Instance P) : Prop where
  dist_self : ∀ x, I.d x x = 0
  dist_pos : ∀ x y, x ≠ y → 0 < I.d x y
  dist_symm : ∀ x y, I.d x y = I.d y x
  dist_triangle : ∀ x y z, I.d x z ≤ I.d x y + I.d y z
  cover : ∀ x, x ∈ I.C ∨ x ∈ I.F
  one_le_k : 1 ≤ I.k
  k_le_card : I.k ≤ I.F.card

/-- The size `n = |C| + |F|` of the instance (§2, p. 5). -/
def size (I : Instance P) : ℕ := I.C.card + I.F.card

/-- Feasibility (§2, p. 5): the sum of the `k` largest capacities is at least `|C|`, i.e. some
`k` facilities have total capacity at least `|C|`. -/
def Feasible (I : Instance P) : Prop :=
  ∃ S ⊆ I.F, S.card = I.k ∧ I.C.card ≤ ∑ f ∈ S, I.U f

/-- Number of clients that the assignment `φ` sends to `f`, i.e. `|φ⁻¹(f)|`. -/
def load (I : Instance P) (φ : P → P) (f : P) : ℕ := (I.C.filter (fun c => φ c = f)).card

/-- A solution `(S, φ)` (§2, p. 5): `S ⊆ F`, `|S| = k`, every client is assigned to a facility of
`S`, and `|φ⁻¹(f)| ≤ U_f` for every `f ∈ S`. Values of `φ` at non-clients are never read. -/
def IsSolution (I : Instance P) (S : Finset P) (φ : P → P) : Prop :=
  S ⊆ I.F ∧ S.card = I.k ∧ (∀ c ∈ I.C, φ c ∈ S) ∧ ∀ f ∈ S, I.load φ f ≤ I.U f

/-- The cost `∑_{c ∈ C} d(c, φ(c))` of an assignment. -/
def cost (I : Instance P) (φ : P → P) : ℝ := ∑ c ∈ I.C, I.d c (φ c)

/-- `(S, φ)` is an optimal solution: a solution of cost `OPT(I)`. -/
def IsOptimal (I : Instance P) (S : Finset P) (φ : P → P) : Prop :=
  I.IsSolution S φ ∧ ∀ S' φ', I.IsSolution S' φ' → I.cost φ ≤ I.cost φ'

/-- `(S, φ)` is a solution of cost at most `ρ · OPT(I)`. -/
def IsApprox (I : Instance P) (ρ : ℝ) (S : Finset P) (φ : P → P) : Prop :=
  I.IsSolution S φ ∧ ∀ S' φ', I.IsSolution S' φ' → I.cost φ ≤ ρ * I.cost φ'

/-- An optimal solution `(O⋆, φ⋆)` with its facilities listed as `o⋆_1, …, o⋆_k` (§3, p. 6). -/
def IsIndexedOptimum (I : Instance P) (o : Fin I.k → P) (φ : P → P) : Prop :=
  Function.Injective o ∧ I.IsOptimal (Finset.univ.image o) φ

/-- A solution of the uncapacitated k-median instance underlying `I`: capacities are ignored. -/
def IsUncapSolution (I : Instance P) (S : Finset P) (φ : P → P) : Prop :=
  S ⊆ I.F ∧ S.card = I.k ∧ ∀ c ∈ I.C, φ c ∈ S

/-- A `ρ`-approximate solution of the underlying uncapacitated instance (Algorithm 1, line 2). -/
def IsUncapApprox (I : Instance P) (ρ : ℝ) (S : Finset P) (φ : P → P) : Prop :=
  I.IsUncapSolution S φ ∧ ∀ S' φ', I.IsUncapSolution S' φ' → I.cost φ ≤ ρ * I.cost φ'

/-- All distances between distinct points are positive integers at most `D`. -/
def HasIntDistancesUpTo (I : Instance P) (D : ℕ) : Prop :=
  ∀ x y, x ≠ y → ∃ z : ℕ, 1 ≤ z ∧ z ≤ D ∧ I.d x y = z

end Instance

/-- The bound `D = ⌈10 n² / ε⌉` on distances assumed from §3 on (p. 6, Algorithm 1 p. 9). -/
def distanceBound (n : ℕ) (ε : ℝ) : ℕ := ⌈10 * (n : ℝ) ^ 2 / ε⌉₊

/-- Geometric rounding `μ_ε` (§2, p. 5–6): `μ_ε(0) = 0` and
`μ_ε(x) = ⌊(1+ε)^{⌈log_{1+ε} x⌉}⌋` for integers `x ≥ 1`. -/
def geomRound (ε : ℝ) (x : ℕ) : ℕ :=
  if x = 0 then 0 else ⌊(1 + ε) ^ ⌈Real.logb (1 + ε) x⌉⌋₊

end

end CapacitatedKMedianFPT.Main


