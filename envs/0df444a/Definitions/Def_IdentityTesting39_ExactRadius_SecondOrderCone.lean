-- Prove2me | Definitions.Def_IdentityTesting39_ExactRadius_SecondOrderCone
-- name    : IdentityTesting39_ExactRadius_SecondOrderCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:14.860448+00:00
-- url     : https://prove2.me/theorems/7790b5aa-a68d-4051-aabc-4b0e57922de3
-- title:
--   Explicit affine second-order-cone programs for the moment objectives
-- statement:
--   A finite second-order-cone minimization problem consists of affine expressions with fixed real coefficients, a linear objective, a finite list of affine equalities, and a finite list of constraints
--
--   $$\sqrt{\sum_{j=1}^{d}(a_j\cdot x+b_j)^2}\le c\cdot x+e.$$
--
--   The dimension $d+1$ of each cone is recorded. Linear inequalities use $d=0$. Rotated cones $x^2\le yz$, $y,z\ge0$, are represented by $\|(2x,y-z)\|_2\le y+z$.
--
--   The explicit instances have eight slots per label, $r,w,e,z,s_1,s_2,t,\phi$, and one common objective $u$. They impose the scalar moment cones, normalization and the exact radius constraint, and the cost epigraphs $(r-q)^2\le(r+q)t$ and $w^2\le(q^2+w)\phi$. Finally $u\ge n\sum t$ and $u\ge n^2\sum\phi$. Tail branches omit head scalar and collision constraints. All coefficients are computed only from $q,\varepsilon,n$ and fixed numbers. The representation predicate asserts attained equality with the moment value and bounds the variable count, constraint count and total cone dimension. It contains no assumed optimizer or theorem.
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.4, §3, display (2), and Appendix B.3, p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_MomentPrograms

open scoped BigOperators
noncomputable section

namespace IdentityTesting39.ExactRadius

/-- A genuine affine expression: all variable dependence is through fixed coefficients. -/
structure AffineExpr (V : Type) where
  coefficient : V → ℝ
  constant : ℝ

namespace AffineExpr

def eval {V : Type} [Fintype V] (a : AffineExpr V) (x : V → ℝ) : ℝ :=
  (∑ v, a.coefficient v * x v) + a.constant

def const {V : Type} (c : ℝ) : AffineExpr V := ⟨fun _ => 0, c⟩
def coord {V : Type} (v : V) : AffineExpr V := by
  classical
  exact ⟨fun w => if w = v then 1 else 0, 0⟩
def add {V : Type} (a b : AffineExpr V) : AffineExpr V :=
  ⟨fun v => a.coefficient v + b.coefficient v, a.constant+b.constant⟩
def scale {V : Type} (c : ℝ) (a : AffineExpr V) : AffineExpr V :=
  ⟨fun v => c*a.coefficient v, c*a.constant⟩
def sub {V : Type} (a b : AffineExpr V) : AffineExpr V := add a (scale (-1) b)
def sum {V I : Type} (s : Finset I) (a : I → AffineExpr V) : AffineExpr V :=
  ⟨fun v => ∑ i ∈ s, (a i).coefficient v, ∑ i ∈ s, (a i).constant⟩

end AffineExpr

/-- The Euclidean norm inequality ‖Ax+b‖₂ ≤ c·x+d, with its dimension recorded. -/
structure SOCConstraint (V : Type) where
  dimension : ℕ
  vector : Fin dimension → AffineExpr V
  rhs : AffineExpr V

namespace SOCConstraint

def Holds {V : Type} [Fintype V] (C : SOCConstraint V) (x : V → ℝ) : Prop :=
  Real.sqrt (∑ j, ((C.vector j).eval x)^2) ≤ C.rhs.eval x

def nonnegative {V : Type} (a : AffineExpr V) : SOCConstraint V :=
  ⟨0, Fin.elim0, a⟩

/-- x² ≤ yz with y,z≥0 is exactly ‖(2x,y−z)‖₂ ≤ y+z. -/
def rotated {V : Type} (x y z : AffineExpr V) : SOCConstraint V :=
  ⟨2, ![x.scale 2, y.sub z], y.add z⟩

end SOCConstraint

/-- Generic finite SOC minimization; no value or optimizer is part of its data. -/
structure SOCProgram (V : Type) where
  objective : AffineExpr V
  equalities : List (AffineExpr V)
  cones : List (SOCConstraint V)

namespace SOCProgram

def Feasible {V : Type} [Fintype V] (P : SOCProgram V) (x : V → ℝ) : Prop :=
  (∀ a ∈ P.equalities, a.eval x = 0) ∧ (∀ C ∈ P.cones, C.Holds x)
def constraintCount {V : Type} (P : SOCProgram V) : ℕ :=
  P.equalities.length + P.cones.length
def coneDimension {V : Type} (P : SOCProgram V) : ℕ :=
  (P.cones.map (fun C => C.dimension+1)).sum

def RepresentsMinimum {V : Type} [Fintype V] (P : SOCProgram V) (v : ℝ) : Prop :=
  (∃ x, P.Feasible x ∧ P.objective.eval x = v) ∧
  ∀ x, P.Feasible x → v ≤ P.objective.eval x

end SOCProgram

/-- Eight slots per coordinate: r,w,e,z,s₁,s₂,T-epigraph,Φ-epigraph; none is u. -/
abbrev ConeVariables (ι : Type) := Option (ι × Fin 8)

def coneSlot {ι : Type} (i : ι) (j : Fin 8) : AffineExpr (ConeVariables ι) :=
  AffineExpr.coord (some (i,j))

/-- §3's scalar cones, with the q=0 affine face treated separately. -/
def scalarConstraints {ι : Type} (q : ℝ) (i : ι) : List (SOCConstraint (ConeVariables ι)) :=
  let r := coneSlot i 0
  let w := coneSlot i 1
  let e := coneSlot i 2
  let z := coneSlot i 3
  let s₁ := coneSlot i 4
  let s₂ := coneSlot i 5
  let one : AffineExpr (ConeVariables ι) := .const 1
  let A := e.add (z.scale q)
  let B := (r.sub e).sub (z.scale q)
  let s := (w.add (r.scale (2*q))).sub (.const (q^2))
  if q = 0 then
    [.nonnegative (e.sub r), .nonnegative (r.sub e),
     .rotated r w one, .nonnegative (r.sub w)]
  else
    [.nonnegative z, .nonnegative (one.sub z),
     .nonnegative (A.sub (z.scale q)), .nonnegative (z.sub A),
     .nonnegative B, .nonnegative (((one.sub z).scale q).sub B),
     .rotated A z s₁, .rotated B (one.sub z) s₂,
     .nonnegative (s.sub (s₁.add s₂)), .nonnegative ((r.scale q |>.add e).sub s)]

/-- Explicit coefficients from q,ε,n and fixed numbers only. No F_n, choice, or optimizer. -/
def explicitSOC {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (ε n : ℝ) (B : Branch ι) : SOCProgram (ConeVariables ι) := by
  classical
  let I := quadraticCoords B
  let labels := (Finset.univ : Finset ι).toList
  let r := fun (i : ι) => coneSlot i 0
  let w := fun (i : ι) => coneSlot i 1
  let e := fun (i : ι) => coneSlot i 2
  let t := fun (i : ι) => coneSlot i 6
  let f := fun (i : ι) => coneSlot i 7
  let u : AffineExpr (ConeVariables ι) := .coord none
  let mass := AffineExpr.sum Finset.univ r
  let radius := match B with
    | .excess _ => AffineExpr.sum I e
    | _ => AffineExpr.sum I (fun i => ((e i).sub (r i)).add (.const (q i)))
  let localCones := labels.flatMap fun i =>
    [.nonnegative (r i), .rotated ((r i).sub (.const (q i)))
      ((r i).add (.const (q i))) (t i)] ++
    (if i ∈ I then scalarConstraints (q i) i ++
      [.rotated (w i) ((AffineExpr.const (q i^2)).add (w i)) (f i)] else [])
  exact ⟨u, [mass.sub (.const 1)], localCones ++
    [.nonnegative (radius.sub (.const ε)),
     .nonnegative (u.sub ((AffineExpr.sum Finset.univ t).scale n)),
     .nonnegative (u.sub ((AffineExpr.sum I f).scale (n^2))) ]⟩

/-- The three size measures and attained equality for the explicit program. -/
def SOCClaim {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : ℝ) (q : ι → ℝ) (ε n : ℝ) (B : Branch ι) : Prop :=
  let P := explicitSOC q ε n B
  (Fintype.card (ConeVariables ι) : ℝ) ≤ K * Fintype.card ι ∧
  (P.constraintCount : ℝ) ≤ K * Fintype.card ι ∧
  (P.coneDimension : ℝ) ≤ K * Fintype.card ι ∧
  P.RepresentsMinimum (programValue q ε n B)

end IdentityTesting39.ExactRadius


