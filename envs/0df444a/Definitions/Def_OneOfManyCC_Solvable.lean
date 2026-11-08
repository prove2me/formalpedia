-- Prove2me | Definitions.Def_OneOfManyCC_Solvable
-- name    : OneOfManyCC_Solvable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:44.191342+00:00
-- url     : https://prove2.me/theorems/42fecb6f-9947-4c9b-bf1e-af94c5cbb949
-- title:
--   Solvable rectangle: some protocol of depth $\max\{\mathrm{CC}(\mathrm{OneOut}^{\neq}_k(R)),\lceil\log_2|O|\rceil\}$ solves $R$ on it
-- statement:
--   For $A'\subseteq A$ and $B'\subseteq B$, the rectangle $A'\times B'$ is **solvable** if some protocol of depth at most
--
--   $$\max\{\mathrm{CC}(\mathrm{OneOut}^{\neq}_k(R)),\ \lceil\log_2|O|\rceil\}$$
--
--   solves $R$ on $A'\times B'$. A rectangle is regarded as the pair of its sides, so $A\times\varnothing$ and $\varnothing\times B$ are different solvable rectangles. The set $\mathcal H$ of all solvable rectangles is finite. The proof of the main theorem plays a zero-sum game over $\mathcal H$ and turns its optimal mixture into one protocol for $R$.
--
--   **Formalization Note** A rectangle is a pair `Set A × Set B`, never a product set. `Nat.clog 2 m` is $\lceil\log_2 m\rceil$ for $m\ge1$.
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, p.10; §5, proof of Theorem 1.2, p.11

import Mathlib
import Definitions.Def_OneOfManyCC_CC
import Definitions.Def_OneOfManyCC_OneOut

namespace OneOfManyCC

/-- **Solvable rectangle.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, p.10:
"We call the rectangle A′ × B′ solvable if some protocol of depth at most
max{CC(OneOut≠ₖ(R)), ⌈log₂|O|⌉} solves R on it. Also, we regard a rectangle as the pair of its
sides, so that A × ∅ and ∅ × B are different solvable rectangles."

**Formalization Note.** The rectangle is the pair of sides `A' : Set A`, `B' : Set B`, never the
product set. `Nat.clog 2 m` is `⌈log₂ m⌉` for `m ≥ 1`. -/
def Solvable {A B O : Type} [Fintype O] (k : ℕ) (R : A → B → O → Prop)
    (A' : Set A) (B' : Set B) : Prop :=
  ∃ P : Protocol A B O,
    P.depth ≤ max (CC (OneOut k R)) (Nat.clog 2 (Fintype.card O)) ∧ P.SolvesOn R A' B'

/-- The set `H` of all solvable rectangles (§5, proof of Theorem 1.2, p.11), each a pair of sides. -/
def SolvableRect {A B O : Type} [Fintype O] (k : ℕ) (R : A → B → O → Prop) : Type :=
  {r : Set A × Set B // Solvable k R r.1 r.2}

/-- `H` "is finite" (§5, proof of Theorem 1.2, p.11): there are finitely many pairs of subsets of
finite sets. -/
noncomputable instance {A B O : Type} [Fintype A] [Fintype B] [Fintype O] (k : ℕ)
    (R : A → B → O → Prop) : Fintype (SolvableRect k R) := by
  classical
  unfold SolvableRect
  exact inferInstance

end OneOfManyCC


