-- Prove2me | Definitions.Def_SpeedScaling_AVR_Consistent
-- name    : SpeedScaling_AVR_Consistent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:59.553745+00:00
-- url     : https://prove2.me/theorems/49b2c496-d1f1-4bee-b669-17de80ab6a4c
-- title:
--   Execution data and canonical consistent instances
-- statement:
--   Fix disjoint execution intervals $I_j^*=[a_j^*,b_j^*]$, constant nonnegative execution speeds $v_j$, and an A/B label for every job. Its required work is $R_j=v_j(b_j^*-a_j^*)$. An A-job has window $[a_j^*,x_j]$ with $x_j\ge b_j^*$; a B-job has window $[y_j,b_j^*]$ with $y_j\le a_j^*$. The A order uses decreasing execution starts, and the B order uses increasing execution ends.
--
--   The expressions $F_A,F_B$ are Eq. (6) and its symmetric B version, evaluated on these windows. A window is aligned when its free endpoint is an execution-interval boundary. A family is nested when windows with overlapping interiors follow their respective order by containment; endpoint-only contact is allowed, as in the paper's four-interval example. A canonical consistent instance satisfies consistency, alignment, and nesting on both sides.
--
--   This data is the fixed schedule and bipartition used in the reduction to canonical instances.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 379, §5.1, conditions 1–3 and Lemmas 5.4–5.5.

import Definitions.Def_SpeedScaling_AVR_Canonical

namespace SpeedScaling.AVR
noncomputable section
open MeasureTheory
open scoped Classical

/-- Fixed execution intervals, speeds, and job types in the reduction of §5.1. -/
structure ExecData where
  m : ℕ
  aS : Fin m → ℝ
  bS : Fin m → ℝ
  v : Fin m → ℝ
  γ : Fin m → Bool
  hab : ∀ j, aS j < bS j
  hv : ∀ j, 0 ≤ v j
  disjoint : ∀ i j, i ≠ j → Disjoint (Set.Ioo (aS i) (bS i)) (Set.Ioo (aS j) (bS j))

/-- Job `i`'s part of the optimal speed profile. -/
def sStar (D : ExecData) (i : Fin D.m) (t : ℝ) : ℝ :=
  if t ∈ Set.Icc (D.aS i) (D.bS i) then D.v i else 0

/-- Work executed on one of the fixed execution intervals. -/
def req (D : ExecData) (j : Fin D.m) : ℝ :=
  D.v j * (D.bS j - D.aS j)

/-- Descending start-time order for A-jobs. -/
def precedesA (D : ExecData) (i j : Fin D.m) : Prop :=
  D.aS j ≤ D.aS i

/-- Ascending finish-time order for B-jobs. -/
def precedesB (D : ExecData) (i j : Fin D.m) : Prop :=
  D.bS i ≤ D.bS j

/-- A-job deadlines extend beyond the corresponding execution interval. -/
def ConsistentA (D : ExecData) (x : Fin D.m → ℝ) : Prop :=
  ∀ j, D.γ j = true → D.bS j ≤ x j

/-- B-job arrivals precede the corresponding execution interval. -/
def ConsistentB (D : ExecData) (y : Fin D.m → ℝ) : Prop :=
  ∀ j, D.γ j = false → y j ≤ D.aS j

/-- Equation (6) on A-jobs for deadlines `x`. -/
def FA (D : ExecData) (x : Fin D.m → ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.univ.filter (fun j : Fin D.m => D.γ j = true),
    (req D j / (x j - D.aS j)) *
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin D.m => D.γ i = true ∧ precedesA D i j),
        (∫ t in D.aS j..x j, sStar D i t)

/-- The symmetric expression for B-jobs. -/
def FB (D : ExecData) (y : Fin D.m → ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.univ.filter (fun j : Fin D.m => D.γ j = false),
    (req D j / (D.bS j - y j)) *
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin D.m => D.γ i = false ∧ precedesB D i j),
        (∫ t in y j..D.bS j, sStar D i t)

/-- Quadratic optimal energy of A-jobs. -/
def OPTA (D : ExecData) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin D.m => D.γ j = true),
    D.v j ^ 2 * (D.bS j - D.aS j)

/-- Quadratic optimal energy of B-jobs. -/
def OPTB (D : ExecData) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin D.m => D.γ j = false),
    D.v j ^ 2 * (D.bS j - D.aS j)

/-- Each A-job deadline is an execution-interval boundary. -/
def AlignedA (D : ExecData) (x : Fin D.m → ℝ) : Prop :=
  ∀ j, D.γ j = true → ∃ k : Fin D.m, x j = D.aS k ∨ x j = D.bS k

/-- Each B-job arrival is an execution-interval boundary. -/
def AlignedB (D : ExecData) (y : Fin D.m → ℝ) : Prop :=
  ∀ j, D.γ j = false → ∃ k : Fin D.m, y j = D.aS k ∨ y j = D.bS k

/-- Proper nesting of the extended A-job windows. -/
def NestedA (D : ExecData) (x : Fin D.m → ℝ) : Prop :=
  ∀ i j, D.γ i = true → D.γ j = true → i ≠ j → precedesA D i j →
    (Set.Ioo (D.aS i) (x i) ∩ Set.Ioo (D.aS j) (x j)).Nonempty →
      Set.Icc (D.aS i) (x i) ⊆ Set.Icc (D.aS j) (x j)

/-- Proper nesting of the extended B-job windows. -/
def NestedB (D : ExecData) (y : Fin D.m → ℝ) : Prop :=
  ∀ i j, D.γ i = false → D.γ j = false → i ≠ j → precedesB D i j →
    (Set.Ioo (y i) (D.bS i) ∩ Set.Ioo (y j) (D.bS j)).Nonempty →
      Set.Icc (y i) (D.bS i) ⊆ Set.Icc (y j) (D.bS j)

/-- A canonical instance consistent with fixed execution data. -/
def CanonicalConsistent (D : ExecData) (x y : Fin D.m → ℝ) : Prop :=
  ConsistentA D x ∧ ConsistentB D y ∧ AlignedA D x ∧ AlignedB D y ∧
    NestedA D x ∧ NestedB D y

end
end SpeedScaling.AVR


