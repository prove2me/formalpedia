-- Prove2me | Definitions.Def_RobustOpt2009_Linear_Model
-- name    : RobustOpt2009_Linear_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:41:52.996862+00:00
-- url     : https://prove2.me/theorems/69cf6955-08fb-4edc-b124-b16fa024ea35
-- title:
--   Affine robust constraints and explicit conic representations
-- statement:
--   Let $x\in\mathbb R^n$ and $z\in\mathbb R^L$. Affine data consist of nominal coefficients $a^0,b^0$ and shifts $a^\ell,b^\ell$. Robust feasibility means
--   $$ (a^0)^Tx+\sum_\ell z_\ell(a^\ell)^Tx\le b^0+\sum_\ell z_\ell b^\ell\quad\text{for every }z\in Z. $$
--   A lifted uncertainty description consists of columns $P_\ell,Q_j$ and offset $p$, with $Z=\{z:\exists v,\sum_\ell z_\ell P_\ell+\sum_jv_jQ_j+p\in K\}$. A polyhedral cone is a finite intersection of homogeneous closed halfspaces. A certificate consists of $p^Ty+(a^0)^Tx\le b^0$, $Q_j^Ty=0$, $P_\ell^Ty+(a^\ell)^Tx=b^\ell$, and membership of $y$ in the specified certificate cone.
--
--   The standard cone families are a nonnegative orthant, a finite product of Lorentz cones, and the positive semidefinite cone. The last family uses symmetric matrix coefficients and the trace pairing. Strict feasibility means strict Lorentz inequalities or positive definiteness; it is not required for an orthant. An explicit system stores one scalar inequality, finitely many scalar equalities, and a cone block. The reformulation copies the input coefficients, placing the $Q$ equations before the $P$ equations.
--
--   **Formalization Note** Finite real coordinate arrays are used throughout. Lorentz blocks have a distinguished scalar coordinate and $d_s$ vector coordinates; PSD matrices use all $k^2$ entries, with symmetry retained. The size functions count scalar coefficients, variables and the structural cone description, rather than bit complexity of real numbers. They make the polynomial-size clause of Corollary 1.3.5 concrete. All definitions are independent of the theorem conclusions.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Definition 1.3.1 and equations (1.3.4)–(1.3.12), printed pp. 17–21 (PDF pp. 43–47)

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix
open scoped BigOperators

namespace RobustOpt2009.Linear

/-- Affine data of (1.3.4)--(1.3.6); nominal coefficients are separate. -/
structure Data (n L : ℕ) where
  a0 : Fin n → ℝ
  b0 : ℝ
  a : Fin L → Fin n → ℝ
  b : Fin L → ℝ

/-- The original, universally quantified robust constraint. -/
def Robust {n L : ℕ} (D : Data n L) (Z : Set (Fin L → ℝ)) (x : Fin n → ℝ) : Prop :=
  ∀ z ∈ Z, D.a0 ⬝ᵥ x + ∑ l, z l * (D.a l ⬝ᵥ x) ≤ D.b0 + ∑ l, z l * D.b l

/-- The lifted description (1.3.10), with columns of P and Q as vectors. -/
structure Lift (ι : Type) (L u : ℕ) where
  P : Fin L → ι → ℝ
  Q : Fin u → ι → ℝ
  p : ι → ℝ

def Lift.value {ι : Type} {L u : ℕ} (R : Lift ι L u)
    (z : Fin L → ℝ) (v : Fin u → ℝ) : ι → ℝ :=
  fun i => (∑ l, z l * R.P l i) + (∑ j, v j * R.Q j i) + R.p i

def Lift.set {ι : Type} {L u : ℕ} (R : Lift ι L u) (K : Set (ι → ℝ)) : Set (Fin L → ℝ) :=
  {z | ∃ v, R.value z v ∈ K}

/-- Finite homogeneous halfspace description of a polyhedral cone. -/
def Polyhedral {N : ℕ} (K : Set (Fin N → ℝ)) : Prop :=
  ∃ m : ℕ, ∃ A : Fin m → Fin N → ℝ, K = {z | ∀ j, 0 ≤ A j ⬝ᵥ z}

/-- Formula (1.3.12), for a supplied certificate cone C. -/
def Certificate {ι : Type} [Fintype ι] {n L u : ℕ} (D : Data n L)
    (R : Lift ι L u) (C : Set (ι → ℝ)) (x : Fin n → ℝ) (y : ι → ℝ) : Prop :=
  R.p ⬝ᵥ y + D.a0 ⬝ᵥ x ≤ D.b0 ∧
  (∀ j, R.Q j ⬝ᵥ y = 0) ∧
  (∀ l, R.P l ⬝ᵥ y + D.a l ⬝ᵥ x = D.b l) ∧ y ∈ C

/-- The three families in Corollary 1.3.5. A Lorentz block has d+1 coordinates. -/
inductive ConeShape where
  | orthant (N : ℕ)
  | lorentz (m : ℕ) (d : Fin m → ℕ)
  | psd (k : ℕ)

def ConeShape.Index : ConeShape → Type
  | .orthant N => Fin N
  | .lorentz m d => (s : Fin m) × Option (Fin (d s))
  | .psd k => Fin k × Fin k

instance (s : ConeShape) : Fintype s.Index := by
  cases s <;> dsimp [ConeShape.Index] <;> infer_instance

/-- Cone membership is explicit: coordinates, Euclidean block norms, or PSD matrices. -/
def ConeShape.cone : (s : ConeShape) → Set (s.Index → ℝ)
  | .orthant _ => {y | ∀ i, 0 ≤ y i}
  | .lorentz _ _ => {y | ∀ s, Real.sqrt (∑ j, (y ⟨s, some j⟩) ^ 2) ≤ y ⟨s, none⟩}
  | .psd _ => {y | Matrix.PosSemidef (fun i j => y (i,j))}

/-- Interior within the cone's own ambient space; PSD uses the symmetric matrix space. -/
def ConeShape.strictCone : (s : ConeShape) → Set (s.Index → ℝ)
  | .orthant _ => {y | ∀ i, 0 < y i}
  | .lorentz _ _ => {y | ∀ s, Real.sqrt (∑ j, (y ⟨s, some j⟩) ^ 2) < y ⟨s, none⟩}
  | .psd _ => {y | Matrix.PosDef (fun i j => y (i,j))}

/-- Data of an LMI take values in the symmetric matrix space. -/
def ConeShape.ambient : (s : ConeShape) → Set (s.Index → ℝ)
  | .orthant _ => Set.univ
  | .lorentz _ _ => Set.univ
  | .psd _ => {y | ∀ i j, y (i,j) = y (j,i)}

def WellFormed {L u : ℕ} (s : ConeShape) (R : Lift s.Index L u) : Prop :=
  R.p ∈ s.ambient ∧ (∀ l, R.P l ∈ s.ambient) ∧ (∀ j, R.Q j ∈ s.ambient)

/-- Strict feasibility is required in both nonlinear cone cases, never in the orthant case. -/
def Qualified {L u : ℕ} : (s : ConeShape) → Lift s.Index L u → Prop
  | .orthant _, _ => True
  | (.lorentz m d), R => ∃ z v, R.value z v ∈ (ConeShape.lorentz m d).strictCone
  | (.psd k), R => ∃ z v, R.value z v ∈ (ConeShape.psd k).strictCone

/-- A finite explicit conic system: one scalar inequality, e equalities, and a cone block. -/
structure ExplicitSystem (ι : Type) (n e : ℕ) where
  scalarX : Fin n → ℝ
  scalarY : ι → ℝ
  scalarRhs : ℝ
  eqX : Fin e → Fin n → ℝ
  eqY : Fin e → ι → ℝ
  eqRhs : Fin e → ℝ
  cone : Set (ι → ℝ)

def ExplicitSystem.Feasible {ι : Type} [Fintype ι] {n e : ℕ}
    (S : ExplicitSystem ι n e) (x : Fin n → ℝ) (y : ι → ℝ) : Prop :=
  S.scalarX ⬝ᵥ x + S.scalarY ⬝ᵥ y ≤ S.scalarRhs ∧
  (∀ j, S.eqX j ⬝ᵥ x + S.eqY j ⬝ᵥ y = S.eqRhs j) ∧ y ∈ S.cone

/-- Explicit coefficient construction of (1.3.12); equality rows are Q followed by P. -/
def reformulation {ι : Type} {n L u : ℕ} (D : Data n L) (R : Lift ι L u)
    (C : Set (ι → ℝ)) : ExplicitSystem ι n (u + L) where
  scalarX := D.a0
  scalarY := R.p
  scalarRhs := D.b0
  eqX := Fin.addCases (fun _ => 0) D.a
  eqY := Fin.addCases R.Q R.P
  eqRhs := Fin.addCases (fun _ => 0) D.b
  cone := C

/-- Dense scalar storage, including all coefficients and RHS entries of the explicit system. -/
def ExplicitSystem.coefficientCount {ι : Type} [Fintype ι] {n e : ℕ}
    (_S : ExplicitSystem ι n e) : ℕ := (e + 1) * (n + Fintype.card ι + 1)

/-- Structural encoding length for the standard cone constraints, including PSD symmetry. -/
def ConeShape.coneSize : ConeShape → ℕ
  | .orthant N => N
  | .lorentz m d => ∑ s : Fin m, (d s + 1)
  | .psd k => k * k

/-- Input dimension plus dense affine-data storage and the standard cone description. -/
def inputSize {n L u : ℕ} (s : ConeShape) (_D : Data n L) (_R : Lift s.Index L u) : ℕ :=
  1 + n + L + u + Fintype.card s.Index +
  (L + 1) * (n + 1) + (L + u + 1) * Fintype.card s.Index + s.coneSize

/-- Output size counts variables, scalar affine entries, and standard cone description. -/
def outputSize {n L u : ℕ} (s : ConeShape) (D : Data n L) (R : Lift s.Index L u) : ℕ :=
  n + Fintype.card s.Index + (reformulation D R s.cone).coefficientCount + s.coneSize

end RobustOpt2009.Linear


