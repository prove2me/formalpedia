-- Prove2me | Definitions.Def_SublinearSteiner_Saving
-- name    : SublinearSteiner_Saving
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:42:46.588832+00:00
-- url     : https://prove2.me/theorems/4edf1e8a-b526-4f38-a9b9-b8fb1e887cd4
-- title:
--   The saving of a system of rows; the savings $Y_i$, $\Phi_i$, $\Psi_U$
-- statement:
--   Given a finite universe $U$, a list of rows (subsets of the universe) and a fixed set of eligible rows, the **saving** of the system is
--   $$\max_{F}\Bigl(\Bigl|\bigcup_{R\in F}R\Bigr|-|F|\Bigr),$$
--   the maximum being over sublists $F$ of eligible rows, including the empty one.
--
--   At a scale $a$, a set $\mathcal Q$ of components and a radius $r$, the row of $v\in V$ consists of the components containing a point within distance $r$ of $v$, and it is eligible if it contains at least three components. Then:
--
--   1. $Y_i$ is the saving of $\mathrm{comp}(G_a(T))$ with radius $3a/5$;
--   2. $\Phi_i$ is the saving of $\mathrm{comp}(G_a(N))$ with radius $5a/8$, for a retained set $N$;
--   3. $\Psi_U$ is the saving of the system of $\Phi_i$ restricted to a set $U$ of components, with the original eligibility.
--
--   **Formalization Note.** Rows are indexed by the points of $V$, so two points with equal rows are two rows of the list. Restricting a system keeps the eligible set as given: eligibility is never recomputed.
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Section 3, p.14; p.15; Section 4.1, p.20; Section 4.4, p.24

import Mathlib
import Definitions.Def_SublinearSteiner_ThresholdGraph

open scoped Classical

namespace SublinearSteiner

/-!
# Savings and the rows of a scale

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), Section 3, p.14 (savings), p.15 (rows of the exact components), and
Section 4.1, p.20 (rows of the cover components).

The saving of a universe `U`, a list of rows and a fixed set of eligible rows is
`max_F (|⋃_{R ∈ F} R| − |F|)` over sublists `F` of eligible rows, including the empty one.

**Formalization Note.**
* Rows are indexed, so two points with the same row are two rows of the list. A sublist is a set of indices.
* `saving U R El` counts only the elements of `U`, and it keeps `El` as given. So restricting a system to a smaller
  universe keeps the original eligibility, as p.20 requires ("this eligibility is never recomputed after deletions").
* A row is indexed by any point of `V`: Sections 3 and 4.1 define rows for all `v ∈ V`, not only nonterminals.
* A row contains a component when a point of the component is within distance `r` of `v`, with `≤` as printed.
-/

variable {n : ℕ}

/-- The saving `max_F (|⋃_{R ∈ F} R| − |F|)` of the universe `U` with rows `R` and eligible rows `El`. The maximum
is over sets of eligible indices, including the empty one, so the value is nonnegative. -/
noncomputable def saving {α ι : Type*} (U : Finset α) (R : ι → Finset α) (El : Finset ι) : ℤ :=
  El.powerset.sup' ⟨∅, Finset.empty_mem_powerset El⟩
    fun F => ((F.biUnion R ∩ U).card : ℤ) - F.card

/-- The row of `v`: the components of `Q` containing a point within distance `r` of `v`. -/
noncomputable def rowAt (w : FinMetric n) (Q : Finset (Finset (Fin n))) (r : ℝ) (v : Fin n) :
    Finset (Finset (Fin n)) :=
  Q.filter fun C => ∃ x ∈ C, w.d v x ≤ r

/-- The points whose row contains at least three components. -/
noncomputable def eligibleCenters (w : FinMetric n) (Q : Finset (Finset (Fin n))) (r : ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter fun v => 3 ≤ (rowAt w Q r v).card

/-- `Y_i`: the saving of the exact components of `G_a(T)` with the rows at radius `3a/5` (p.15). -/
noncomputable def idealSaving (w : FinMetric n) (T : Finset (Fin n)) (a : ℝ) : ℤ :=
  saving (comp w T a) (rowAt w (comp w T a) (3 * a / 5)) (eligibleCenters w (comp w T a) (3 * a / 5))

/-- `Φ_i`: the saving of the components of `G_a(N)` with the rows at radius `5a/8` (p.20). -/
noncomputable def coverSaving (w : FinMetric n) (N : Finset (Fin n)) (a : ℝ) : ℤ :=
  saving (comp w N a) (rowAt w (comp w N a) (5 * a / 8)) (eligibleCenters w (comp w N a) (5 * a / 8))

/-- `Ψ_U`: the saving of the system of `coverSaving` restricted to `U`, with the original eligibility (p.24). -/
noncomputable def restrictedSaving (w : FinMetric n) (N : Finset (Fin n)) (a : ℝ)
    (U : Finset (Finset (Fin n))) : ℤ :=
  saving U (rowAt w (comp w N a) (5 * a / 8)) (eligibleCenters w (comp w N a) (5 * a / 8))

end SublinearSteiner


