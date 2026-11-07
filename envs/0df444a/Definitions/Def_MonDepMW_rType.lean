-- Prove2me | Definitions.Def_MonDepMW_rType
-- name    : MonDepMW_rType
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:33.449004+00:00
-- url     : https://prove2.me/theorems/9b5b4818-50aa-46b8-b4e7-3a3fb715a9c5
-- title:
--   $r$-types $\mathcal T_r(G,A)$
-- statement:
--   A vertex $u$ is **complete** to $X$ if $u\notin X$ and $u$ is adjacent to every member of $X$, and **anticomplete** to $X$ if $u\notin X$ and $u$ is adjacent to no member of $X$.
--
--   For $r\geqslant2$, two vertices $u,u'$ have the same **$r$-type over $A$** iff:
--
--   1. $u,u'$ have the same $(r-1)$-type over $A$;
--   2. for each $Q\in\mathcal T_{r-1}(G,A)$, $u$ is complete to $Q-\{u\}$ iff $u'$ is complete to $Q-\{u'\}$;
--   3. for each $Q\in\mathcal T_{r-1}(G,A)$, $u$ is anticomplete to $Q-\{u\}$ iff $u'$ is anticomplete to $Q-\{u'\}$.
--
--   The $1$-types are those of $\mathcal T_1$. These partitions extend 1-types to larger distances, which is what lets a single damping step control radius-$r$ balls.
--
--   **Formalization Note** A part $Q$ is written as the class of a vertex $y$. The index $r=0$ is outside the paper's range; it is assigned $\mathcal T_1$ and no statement uses it.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §5.1, p.18

import Mathlib
import Definitions.Def_MonDepMW_oneType

set_option autoImplicit false

namespace MonDepMW

/-- `u` is complete to `X`. Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.12: "A vertex u in a graph G is complete to a vertex subset A ⊆ V (G) if u ∉ A
and u is adjacent to every member of A." -/
def CompleteTo {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) (X : Set (Fin n)) : Prop :=
  u ∉ X ∧ ∀ x ∈ X, G.Adj u x

/-- `u` is anticomplete to `X`. Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.12: "u is anticomplete to A if u ∉ A and u is non-adjacent to every member
of A." -/
def AnticompleteTo {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) (X : Set (Fin n)) : Prop :=
  u ∉ X ∧ ∀ x ∈ X, ¬ G.Adj u x

/-- One step of the inductive definition of `r`-types, from `Q = 𝒯_{r−1}(G, A)` to `𝒯_r(G, A)`. The part `Q` of the page
is written as the class `{z | Q.r y z}` of a vertex `y`; every part is such a class. -/
def rTypeStep {n : ℕ} (G : SimpleGraph (Fin n)) (Q : Setoid (Fin n)) : Setoid (Fin n) where
  r u u' := Q.r u u' ∧
    (∀ y, CompleteTo G u ({z | Q.r y z} \ {u}) ↔ CompleteTo G u' ({z | Q.r y z} \ {u'})) ∧
    (∀ y, AnticompleteTo G u ({z | Q.r y z} \ {u}) ↔ AnticompleteTo G u' ({z | Q.r y z} \ {u'}))
  iseqv :=
    { refl := fun u => ⟨Q.refl' u, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
      symm := fun h => ⟨Q.symm' h.1, fun y => (h.2.1 y).symm, fun y => (h.2.2 y).symm⟩
      trans := fun h h' => ⟨Q.trans' h.1 h'.1, fun y => (h.2.1 y).trans (h'.2.1 y),
        fun y => (h.2.2 y).trans (h'.2.2 y)⟩ }

/-- **The partition `𝒯_r(G, A)` into `r`-types.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §5.1, p.18: "For an integer r ⩾ 2, we define the partition
𝒯r(G, A) into r-types over A inductively as follows. Two vertices u, u′ ∈ V (G) have the same r-type if and only if the
following conditions are satisfied: u and u′ have the same (r − 1)-type over A; for each Q ∈ 𝒯r−1(G, A), u is complete
to Q − {u} if and only if u′ is complete to Q − {u′}; and for each Q ∈ 𝒯r−1(G, A), u is anticomplete to Q − {u} if and
only if u′ is anticomplete to Q − {u′}."

**Formalization Note.** `rType G A 1 = oneType G A`. The value at `r = 0` is outside the paper's range; it is set to
`oneType G A` and no statement uses it, since all of them carry `1 ≤ r`. -/
def rType {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℕ → Setoid (Fin n)
  | 0 => oneType G A
  | 1 => oneType G A
  | r + 2 => rTypeStep G (rType G A (r + 1))

end MonDepMW


