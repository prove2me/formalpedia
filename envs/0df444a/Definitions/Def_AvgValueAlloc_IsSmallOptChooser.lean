-- Prove2me | Definitions.Def_AvgValueAlloc_IsSmallOptChooser
-- name    : AvgValueAlloc_IsSmallOptChooser
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:48.281+00:00
-- url     : https://prove2.me/theorems/d8a0b601-3f8c-4168-bde6-4a0257c0af64
-- title:
--   Canonical optimum of the small-edge prefix LP
-- statement:
--   Fix the earned bank $B$. The **small-edge LP** on a multiset of records is (5) with every edge of deficit above $B_j/8$ deleted. A **canonical optimum chooser** assigns to every multiset $A$, group $J$ and record type $u$ a per-copy mass $x_{uj}$ such that giving every copy of $u$ this mass is an optimal solution of the small-edge LP on $A$.
--
--   This is the "deterministic optimum" of aggregated types, divided by occurrence multiplicity, that the service kernel solves on each observed prefix.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2.2, p.5

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_edgeLP

namespace AvgValueAlloc

/-- Small efficient edges into `J`: efficient negative edges with deficit at most `B_j/8`. -/
def smallEdge {n : ℕ} (ρ : Fin n → ℚ) (J : Finset (Fin n)) (B : Fin n → ℝ) (u : Vec n)
    (j : Fin n) : Prop :=
  effEdge ρ J u j ∧ (ρ j : ℝ) - ((u j : ℚ≥0) : ℝ) ≤ B j / 8

/-- **A deterministic canonical optimum of the small-edge service LP, per copy.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2.2, p.5: "each occupied group J solves its
canonical observed-prefix LP, deleting edges with deficit above the original B_j/8. Sort full
negative vectors, aggregate equal types, choose a deterministic optimum and divide each type's mass
by its occurrence multiplicity."

`opt J A u j` is the per-copy mass on edge `(u, j)` for the multiset of records `A`. The chooser
is valid when, for every buyer set `J` and every multiset `A`, giving each copy of a type `u` the
mass `opt J A u j` is a feasible and optimal solution of the LP (5) on `A` restricted to the small
edges into `J` (cutoff `B_j/8`, bank `B`).

**Formalization Note.** Per-copy masses are a function of the type `u` and of the multiset `A`
only, which is the aggregation and division by multiplicity of the page (aggregate mass
= multiplicity × per-copy mass). Requiring optimality for every `J` (not only the groups of the
partition) does not restrict the kernel, which reads `opt` only at groups. -/
def IsSmallOptChooser {n : ℕ} (ρ : Fin n → ℚ) (B : Fin n → ℝ)
    (opt : Finset (Fin n) → Multiset (Vec n) → Vec n → Fin n → ℝ) : Prop :=
  ∀ (J : Finset (Fin n)) (A : Multiset (Vec n)),
    LPFeasible ρ (smallEdge ρ J B) (fun i : Fin A.toList.length => A.toList.get i) B
        (fun i j => opt J A (A.toList.get i) j) ∧
      LPValue (fun i : Fin A.toList.length => A.toList.get i)
          (fun i j => opt J A (A.toList.get i) j) =
        edgeLP ρ (smallEdge ρ J B) (fun i : Fin A.toList.length => A.toList.get i) B

end AvgValueAlloc


