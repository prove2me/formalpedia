-- Prove2me | Definitions.Def_Disjunctive_IntroDuality_RegularityCondition
-- name    : Disjunctive_IntroDuality_RegularityCondition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:04:03.240825+00:00
-- url     : https://prove2.me/theorems/255d199e-3dee-4552-b295-48684927dec5
-- title:
--   Feasible indices $Q^*$/$Q^{**}$ and the Regularity Condition of Theorem 1.5
-- statement:
--   This definition fixes the two feasibility index sets and the Regularity Condition on which
--   Theorem 1.5 (duality for disjunctive programs) and Corollary 1.6 depend.
--
--   Given a finite index set $Q$ and, for each $h \in Q$, a set $S_h$, write
--
--   $$
--   \mathrm{FeasibleIndices}(S) := \{h \in Q : S_h \ne \emptyset\}.
--   $$
--
--   Applied to the primal systems $X_h$ this gives $Q^* := \{h \in Q : X_h \ne \emptyset\}$;
--   applied to the dual systems $U_h$ it gives $Q^{**} := \{h \in Q : U_h \ne \emptyset\}$. The
--   **Regularity Condition** on a pair of index sets $Q^*, Q^{**} \subseteq Q$ is
--
--   $$
--   \big(Q^* \ne \emptyset \ \wedge\ Q \setminus Q^{**} \ne \emptyset\big) \implies Q^* \setminus
--   Q^{**} \ne \emptyset,
--   $$
--
--   i.e.: if the primal disjunctive program is feasible and the dual is infeasible, then some
--   disjunct's primal system is feasible while its dual system is not. Balas shows (Theorem 1.5)
--   that this condition is exactly what is needed for a linear-programming-style strong duality
--   theorem to hold for disjunctive programs, and (Corollary 1.6) that it cannot be dropped.
--
--   **Formalization Note.** `FeasibleIndices` is stated generically over a dependent family
--   `β : Q → Type*` so the same definition instantiates both $Q^*$ (over $\mathbb{R}^n$-valued
--   $X_h$) and $Q^{**}$ (over the $h$-dependent-dimensional $U_h$). `Qstarstarᶜ` is the complement
--   of $Q^{**}$ relative to the whole index set $Q$, i.e. $Q \setminus Q^{**}$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 13, Section 1.5

import Mathlib

namespace Disjunctive.IntroDuality

/-- `Q* = {h ∈ Q : S_h ≠ ∅}`, the indices whose associated system is feasible (Balas §1.5,
used to build both `Q*` from `X_h` and `Q**` from `U_h`). -/
def FeasibleIndices {Q : Type*} {β : Q → Type*} (S : (h : Q) → Set (β h)) : Set Q :=
  {h | (S h).Nonempty}

/-- The Regularity Condition of Theorem 1.5 (Balas §1.5, p. 13, immediately before the
theorem): `(Q* ≠ ∅ ∧ Q \ Q** ≠ ∅) ⇒ Q* \ Q** ≠ ∅`. -/
def RegularityCondition {Q : Type*} (Qstar Qstarstar : Set Q) : Prop :=
  (Qstar.Nonempty ∧ Qstarstarᶜ.Nonempty) → (Qstar \ Qstarstar).Nonempty

end Disjunctive.IntroDuality


