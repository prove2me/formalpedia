-- Prove2me | Definitions.Def_PersistClust_Count_MatchingGate
-- name    : PersistClust_Count_MatchingGate
-- status  : Definition
-- author  : @fabianroll
-- created : 2026-10-12T05:48:24.91897+00:00
-- url     : https://prove2.me/theorems/e2a70e22-7092-40ab-8018-53491167317c
-- title:
--   Theorem 4.5 copy-routing predicates: off-diagonal copies, closeness, and demand routing
-- statement:
--   This file defines the copy-level bookkeeping used in the multi-bijection construction of Theorem 4.5 (RR-6968, §4, pp. 18–21).
--
--   A persistence diagram is represented as a function $D$ from the extended plane $[-\infty,+\infty]^2$ to the cardinals. Its off-diagonal part carries copies: `offD D` is the type of pairs $(p,k)$ with $k < D(p)$, one copy for each unit of multiplicity of each off-diagonal point $p$, and `offPt` returns the point $p$ a copy stands for. Two off-diagonal copies are $\varepsilon$-close (`CloseCopy2`) when both coordinates of their points are within $\varepsilon$ in the extended-real closeness of the report (where $\pm\infty$ is close only to itself), and birth-close (`CloseCopy1`) when only the birth (first) coordinate is.
--
--   The demand predicate `DemandsOff` identifies the off-diagonal copies that cannot be absorbed by the diagonal at radius $\varepsilon$: prominent copies (`PromQNE`) — points strictly above the level $\alpha$ in both coordinates admitting no diagonal point $\varepsilon$-close in both coordinates — and high far south-east copies — birth above $\alpha + \varepsilon$ and death more than $2\varepsilon$ below the birth. For such copies, the clause of Theorem 4.5 at a nearby diagonal slot would force a second-coordinate match that the geometry forbids, so they must be routed to genuine off-diagonal partners; all other off-diagonal copies can be sent to the diagonal.
--
--   **Formalization Note** These predicates are the hypotheses under which the standalone assembly theorem `theorem_4_5_matching_assembly` produces the multi-bijection; the definitions are pure declarations, verified to compile in the platform's default environment.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968, 2009, pp. 18–21, the copy and multi-bijection bookkeeping of §4 (Definitions 4.1 and the proof of Theorem 4.5)

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram

namespace PersistClust.Count

/-! ### Copy-routing predicates for the multi-bijection assembly (Theorem 4.5)

The bookkeeping layer between an interleaving of two persistence modules and the
multi-bijection of Theorem 4.5: off-diagonal copies of a diagram, the copy-closeness
predicates, and the demand predicates describing which off-diagonal copies must be
routed to genuine off-diagonal partners (as opposed to being absorbed by the diagonal). -/

/-- The off-diagonal copies of a diagram `D`: pairs `(p, k)` with `k < D p`, i.e. the left
summand of `Copies D`. -/
abbrev offD (D : EReal × EReal → ℕ∞) :=
  {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < D q.1}

/-- The off-diagonal point of the extended plane that a copy stands for. -/
abbrev offPt {D : EReal × EReal → ℕ∞} (q : offD D) : EReal × EReal := q.1.1

/-- ε-closeness of two off-diagonal copies in both coordinates. -/
def CloseCopy2 (ε : ℝ) {D D' : EReal × EReal → ℕ∞} (a : offD D) (b : offD D') : Prop :=
  closeE (offPt a).1 (offPt b).1 ε ∧ closeE (offPt a).2 (offPt b).2 ε

/-- ε-closeness of two off-diagonal copies in the first (birth) coordinate only. -/
def CloseCopy1 (ε : ℝ) {D D' : EReal × EReal → ℕ∞} (a : offD D) (b : offD D') : Prop :=
  closeE (offPt a).1 (offPt b).1 ε

/-- `a` is a prominent copy: its point lies in the quadrant `Q^NE_α` strictly above the
level `α` in both coordinates, and it cannot be absorbed by the diagonal at radius `ε`
(no diagonal point is ε-close to it in both coordinates). -/
def PromQNE (α ε : ℝ) {D : EReal × EReal → ℕ∞} (a : offD D) : Prop :=
  offPt a ∈ QNE α ∧ ¬ (∃ x : EReal, closeE (offPt a).1 x ε ∧ closeE (offPt a).2 x ε)

/-- The copies the diagonal cannot absorb at radius `ε`, which therefore need genuine
off-diagonal partners: prominent QNE copies (non-killable by definition), and "high far"
QSE copies — birth above `α + ε` and more than `2ε` above the diagonal. For such a QSE
copy any ε-birth-close diagonal slot sits above `α`, so the slot's `pt = (x,x)` is a
QNE point and clause (ii) of Theorem 4.5 would additionally demand ε-closeness in the
death coordinate, which `b − d > 2ε` forbids. All other off-diagonal copies kill to the
diagonal: non-prominent QNE and near-diagonal QSE by their `∃x`-witnesses, low QSE
(`b ≤ α + ε`) at `x = b − ε ≤ α`, and QSW anywhere below. -/
def DemandsOff (α ε : ℝ) {D : EReal × EReal → ℕ∞} (a : offD D) : Prop :=
  PromQNE α ε a ∨
  (offPt a ∈ QSE α ∧ α + ε < (offPt a).1 ∧ 2 * ε < (offPt a).1 - (offPt a).2)

end PersistClust.Count


