-- Prove2me | Definitions.Def_ResourceScheduling_Graph_ResDot11
-- name    : ResourceScheduling_Graph_ResDot11
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:23:32.692696+00:00
-- url     : https://prove2.me/theorems/5044651f-a812-498b-8319-c7c39a73cb48
-- title:
--   The decision problems P3 | res·11, p_j = 1 | C_max and Q2 | res·11, p_j = 1 | C_max
-- statement:
--   This module defines the two scheduling problems of Theorems 2 and 3 of Błażewicz, Lenstra and Rinnooy Kan, in their decision versions.
--
--   An instance of type $res{\cdot}11$ without precedence constraints consists of a number $n$ of unit-time jobs, a number $l$ of resources (part of the input), requirements $r_{hj}\in\{0,1\}$ for $h=1,\dots,l$ and $j=1,\dots,n$, and a threshold $y\in\mathbb N$. Every resource has size $s_h=1$.
--
--   1. $P3\,|\,res{\cdot}11,\,p_j=1\,|\,C_{\max}$: on three identical machines (speed $1$), is there a feasible schedule with $C_{\max}\le y$?
--   2. $Q2\,|\,res{\cdot}11,\,p_j=1\,|\,C_{\max}$: the instance also contains two machine speeds $q_1,q_2$, positive integers; on two uniform machines with these speeds (job processing times $1/q_1$ and $1/q_2$), is there a feasible schedule with $C_{\max}\le y$?
--
--   Instances are encoded over $\{\mathtt{1},\mathtt{\#}\}$ with every number in unary: $n$, $l$, the $l\cdot n$ requirements resource by resource, and $y$; for $Q2$ the speeds $q_1,q_2$ come first.
--
--   **Formalization Note.** Speeds and thresholds are restricted to positive integers and natural numbers respectively. This is a subproblem of the problem with rational data, so NP-hardness of these problems is the stronger statement. Machines are indexed from $0$, so $q_1,q_2$ are `q 0, q 1`.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 15, Theorems 2 and 3; pp. 12–13, Section 2; pp. 22–23, Appendix

import Mathlib
import Definitions.Def_ResourceScheduling_Graph_Model
import Definitions.Def_ResourceScheduling_Graph_Complexity

/-!
# The decision problems `P3 | res·11, p_j = 1 | C_max` and `Q2 | res·11, p_j = 1 | C_max`

Błażewicz, Lenstra & Rinnooy Kan (1983), p. 15, Theorems 2 and 3; the model of pp. 12–13 and
pp. 22–23. An instance lists the number of jobs `n`, the number of resources `l` (part of the
input, `λ = ·`), the requirements `r_{hj} ∈ {0, 1}` (`ρ = 1`) and a threshold `y`; every resource
has size 1 (`σ = 1`), there are no precedence constraints, and every job has `p_j = 1`. For
`Q2` the instance also lists the two machine speeds, as positive integers. Thresholds are
natural numbers. Both restrictions (integer speeds, integer thresholds) give a subproblem of the
general one, so hardness of these problems is the stronger statement.
-/

namespace ResourceScheduling.Graph

/-- The job and resource data of an instance of type `res·11` without precedence constraints,
together with a threshold `y` for the decision version. -/
structure ResDot11Data where
  /-- Number of jobs. -/
  n : ℕ
  /-- Number of resources (part of the input). -/
  l : ℕ
  /-- Requirement `r_{hj}` of job `J_j` for resource `R_h`. -/
  r : Fin l → Fin n → ℕ
  r_le : ∀ h j, r h j ≤ 1
  /-- Threshold `y` on `C_max`. -/
  y : ℕ

namespace ResDot11Data

/-- The scheduling instance on `m` machines of speeds `q`: every resource has size 1 and the
precedence digraph has no arcs. -/
def toInstance (x : ResDot11Data) (m : ℕ) (q : Fin m → ℝ) (hq : ∀ i, 0 < q i) : Instance where
  n := x.n
  m := m
  q := q
  q_pos := hq
  l := x.l
  s := fun _ => 1
  s_pos := fun _ => Nat.one_pos
  r := x.r
  arc := fun _ _ => False
  acyclic := by
    intro j h
    cases h with
    | single h => exact h
    | tail _ h => exact h

/-- Unary code: `n`, `l`, the `l · n` requirements `r_{hj}` row by row (resource by resource),
and `y`, each in unary. -/
def enc (x : ResDot11Data) : List Letter :=
  unary x.n ++ unary x.l ++
    (List.finRange x.l).flatMap (fun h => (List.finRange x.n).flatMap fun j => unary (x.r h j)) ++
    unary x.y

end ResDot11Data

/-- Yes-instances of `P3 | res·11, p_j = 1 | C_max`: three identical machines (speed 1), and a
feasible schedule with `C_max ≤ y` exists. -/
def P3Yes (x : ResDot11Data) : Prop :=
  (x.toInstance 3 (fun _ => 1) (fun _ => one_pos)).HasScheduleWithin x.y

/-- Code of an instance of `P3 | res·11, p_j = 1 | C_max`. -/
def encP3 (x : ResDot11Data) : List Letter := x.enc

/-- Yes-instances of `Q2 | res·11, p_j = 1 | C_max`: two uniform machines with the given positive
integer speeds `q_1, q_2` (0-based: `q 0, q 1`), and a feasible schedule with `C_max ≤ y`
exists. -/
def Q2Yes (p : (Fin 2 → ℕ+) × ResDot11Data) : Prop :=
  (p.2.toInstance 2 (fun i => ((p.1 i : ℕ) : ℝ)) (fun i => by exact_mod_cast (p.1 i).pos)).HasScheduleWithin
    p.2.y

/-- Code of an instance of `Q2 | res·11, p_j = 1 | C_max`: the two speeds in unary, then the
job and resource data. -/
def encQ2 (p : (Fin 2 → ℕ+) × ResDot11Data) : List Letter :=
  unary (p.1 0) ++ unary (p.1 1) ++ p.2.enc

end ResourceScheduling.Graph


