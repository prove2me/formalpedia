-- Prove2me | Definitions.Def_RankOneBimatrix_BinSearch_Setting
-- name    : RankOneBimatrix_BinSearch_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:18.69324+00:00
-- url     : https://prove2.me/theorems/08cac4f4-54dc-4f6c-8663-0f6e16a20f27
-- title:
--   §§3–5 — rank-one game and parameterized LPs
-- statement:
--   The setting defines $(A,-A+ab^\top)$, the auxiliary equilibrium set $\mathcal N$, primal and dual LPs, optimal faces, breakpoints, and the auxiliary LPs of (29) and (39).
--
--   $$P_\lambda:\min v\text{ subject to }A^\top x+\mathbf1v-s=b\lambda,\ x\in X,\ s\ge0;\qquad D_\lambda:\max(\lambda b^\top y+t)\text{ subject to }Ay+\mathbf1t\le0,\ y\in Y.$$
--
--   The same definitions are shared by all milestones. **Formalization Note** Optimality is defined on the full feasible objective image. Absent optional breakpoint endpoints encode the infinite end intervals.
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, pp. 7–18, (8), (10)–(11), (17)–(19), (21), (26)–(29), (39)

import Definitions.Def_RankOneBimatrix_BinSearch_Game

namespace RankOneBimatrix.BinSearch

open Matrix

variable {m n : ℕ}

/-- The second payoff matrix in a game of rank at most one: `-A + a bᵀ`. -/
def rankOneB (A : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin m → ℝ) (b : Fin n → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  -A + vecMulVec a b

/-- Every row is `λ bᵀ`. -/
def onesLam (lam : ℝ) (b : Fin n → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  vecMulVec (fun _ => 1) (lam • b)

/-- The parameterized equilibrium set `𝒩` of equation (11). -/
def NSet (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) :
    Set (ℝ × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | IsNE A (-A + onesLam p.1 b) p.2.1 p.2.2}

/-- The general-rank auxiliary equilibrium set of equation (8). -/
def NSetGeneral (A C : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) :
    Set (ℝ × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | IsNE (A - onesLam p.1 b) (C + onesLam p.1 b) p.2.1 p.2.2}

/-- The hyperplane `H` of equation (10). -/
def Hyperplane (a : Fin m → ℝ) :
    Set (ℝ × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | p.2.1 ⬝ᵥ a = p.1}

/-- A point `(x,v,s)` in the primal LP. -/
abbrev PPoint (m n : ℕ) := (Fin m → ℝ) × ℝ × (Fin n → ℝ)

/-- A point `(y,t)` in the dual LP. -/
abbrev DPoint (n : ℕ) := (Fin n → ℝ) × ℝ

/-- A point `(λ,x,v,s)` in the parameterized primal polyhedron. -/
abbrev PolyPoint (m n : ℕ) := ℝ × (Fin m → ℝ) × ℝ × (Fin n → ℝ)

/-- The feasible set of `Pλ`, equation (19). -/
def PFeas (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ) :
    Set (PPoint m n) :=
  {p | p.1 ∈ Mixed m ∧ (∀ j, 0 ≤ p.2.2 j) ∧
    ∀ j, (A.transpose *ᵥ p.1) j + p.2.1 - p.2.2 j = b j * lam}

/-- The minimizers of the objective `v` on `Pλ`. -/
def POpt (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ) :
    Set (PPoint m n) :=
  {p | p ∈ PFeas A b lam ∧
    IsLeast ((fun q : PPoint m n => q.2.1) '' PFeas A b lam) p.2.1}

/-- The fixed dual polyhedron `D`, equation (18). -/
def DSet (A : Matrix (Fin m) (Fin n) ℝ) : Set (DPoint n) :=
  {p | p.1 ∈ Mixed n ∧ ∀ i, (A *ᵥ p.1) i + p.2 ≤ 0}

/-- Objective of `Dλ`, equation (17). -/
def DValue (b : Fin n → ℝ) (lam : ℝ) (p : DPoint n) : ℝ :=
  lam * (b ⬝ᵥ p.1) + p.2

/-- `Y(λ)`, equation (21): all dual optima. -/
def Yopt (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ) :
    Set (DPoint n) :=
  {p | p ∈ DSet A ∧ IsGreatest (DValue b lam '' DSet A) (DValue b lam p)}

/-- The indices of inequalities strictly slack somewhere on `Y(λ)`, equation (26). -/
noncomputable def Mset (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (lam : ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => ∃ p ∈ Yopt A b lam, (A *ᵥ p.1) i + p.2 < 0)

/-- The indices of coordinates strictly positive somewhere on `Y(λ)`, equation (26). -/
noncomputable def Nset (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (lam : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => ∃ p ∈ Yopt A b lam, 0 < p.1 j)

/-- `P`, equation (27). -/
def PPoly (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) :
    Set (PolyPoint m n) :=
  {p | (p.2.1, p.2.2.1, p.2.2.2) ∈ PFeas A b p.1}

/-- The face `P(M,N)`, equation (28), with zero-based `Fin` indices. -/
def PFace (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) : Set (PolyPoint m n) :=
  {p | p ∈ PPoly A b ∧ (∀ i ∈ M, p.2.1 i = 0) ∧
    (∀ j ∈ N, p.2.2.2 j = 0)}

/-- The maximizers of `BRmax(M,N)`, equation (29). -/
def BRmaxOpt (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) : Set (PolyPoint m n) :=
  {p | p ∈ PFace A b M N ∧
    IsGreatest ((fun q : PolyPoint m n => q.1) '' PFace A b M N) p.1}

/-- The minimizers of `BRmin(M,N)`, equation (29). -/
def BRminOpt (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) : Set (PolyPoint m n) :=
  {p | p ∈ PFace A b M N ∧
    IsLeast ((fun q : PolyPoint m n => q.1) '' PFace A b M N) p.1}

/-- The feasible set of `Pmax(M,N,a,λ')`, equation (39). -/
def PmaxFeas (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) (lam' : ℝ) :
    Set (PolyPoint m n) :=
  {p | p ∈ PFace A b M N ∧ p.1 ≤ p.2.1 ⬝ᵥ a ∧ lam' ≤ p.1}

/-- The feasible set of `Pmin(M,N,a,λ')`, equation (39). -/
def PminFeas (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) (lam' : ℝ) :
    Set (PolyPoint m n) :=
  {p | p ∈ PFace A b M N ∧ p.2.1 ⬝ᵥ a ≤ p.1 ∧ p.1 ≤ lam'}

/-- The maximizers of `λ - xᵀa` in `Pmax`, equation (39). -/
def PmaxOpt (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) (lam' : ℝ) :
    Set (PolyPoint m n) :=
  {p | p ∈ PmaxFeas A a b M N lam' ∧
    IsGreatest ((fun q : PolyPoint m n => q.1 - q.2.1 ⬝ᵥ a) ''
      PmaxFeas A a b M N lam') (p.1 - p.2.1 ⬝ᵥ a)}

/-- The minimizers of `λ - xᵀa` in `Pmin`, equation (39). -/
def PminOpt (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) (lam' : ℝ) :
    Set (PolyPoint m n) :=
  {p | p ∈ PminFeas A a b M N lam' ∧
    IsLeast ((fun q : PolyPoint m n => q.1 - q.2.1 ⬝ᵥ a) ''
      PminFeas A a b M N lam') (p.1 - p.2.1 ⬝ᵥ a)}

/-- Equation (22): a breakpoint has dual optima with different `bᵀy` slopes. -/
def IsBreakpoint (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (lam : ℝ) : Prop :=
  ∃ p q, p ∈ Yopt A b lam ∧ q ∈ Yopt A b lam ∧ b ⬝ᵥ p.1 ≠ b ⬝ᵥ q.1

/-- The predecessor of a breakpoint, or the `-∞` sentinel of Theorem 11. -/
def PrevBreak (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (center : ℝ) : Option ℝ → Prop
  | none => ∀ u, IsBreakpoint A b u → center ≤ u
  | some lo => IsBreakpoint A b lo ∧ lo < center ∧
      ∀ u, IsBreakpoint A b u → u < center → u ≤ lo

/-- The successor of a breakpoint, or the `+∞` sentinel of Theorem 11. -/
def NextBreak (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (center : ℝ) : Option ℝ → Prop
  | none => ∀ u, IsBreakpoint A b u → u ≤ center
  | some hi => IsBreakpoint A b hi ∧ center < hi ∧
      ∀ u, IsBreakpoint A b u → center < u → hi ≤ u

/-- The interval `(λₖ₋₁, λₖ]`, unbounded to the left when `k=1`. -/
def InLeftInterval (prev : Option ℝ) (center lam : ℝ) : Prop :=
  lam ≤ center ∧ ∀ lo ∈ prev, lo < lam

/-- The interval `[λₖ, λₖ₊₁)`, unbounded to the right when `k=K`. -/
def InRightInterval (center : ℝ) (next : Option ℝ) (lam : ℝ) : Prop :=
  center ≤ lam ∧ ∀ hi ∈ next, lam < hi

/-- Schrijver's binary encoding length of a rational in lowest terms. -/
def ratSize (r : ℚ) : ℕ :=
  1 + Nat.size r.num.natAbs + Nat.size r.den

/-- Combined bit length of rational `A`, `a`, and `b`. -/
def inputSize (A : Matrix (Fin m) (Fin n) ℚ)
    (a : Fin m → ℚ) (b : Fin n → ℚ) : ℕ :=
  (∑ i : Fin m, ∑ j : Fin n, ratSize (A i j)) +
    (∑ i : Fin m, ratSize (a i)) + ∑ j : Fin n, ratSize (b j)

end RankOneBimatrix.BinSearch


