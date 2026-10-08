-- Prove2me | Definitions.Def_InteractiveConsistency_Authenticated_Procedure
-- name    : InteractiveConsistency_Authenticated_Procedure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:37:06.528+00:00
-- url     : https://prove2.me/theorems/ffdec022-ff06-41da-9910-3579a56c7c65
-- title:
--   Section 5 — the non-NIL set S_pq and its singleton recording procedure
-- statement:
--   Let $P$ be the processors, let $m$ bound the number of faults, and let $\tau$ be the scenario visible to receiver $p$. For an originator $q$, form the set $S_{pq}$ of every non-NIL value $\tau(wq)$ obtained from a string $w$ of at most $m$ distinct intermediate processors in $P\setminus\{p,q\}$:
--
--   $$
--   S_{pq}=\{v\in V:\exists w,\ |w|\le m,\ w\text{ has distinct letters in }P\setminus\{p,q\},\ \tau(wq)=v\}.
--   $$
--
--   The procedure records $v$ for $q$ if $S_{pq}=\{v\}$; it records NIL if the set is empty or contains more than one value. This is the decision rule whose interactive consistency is the mission's target.
--
--   **Formalization Note** The theorem applies the procedure to $p$'s own view $\tau(w)=\sigma(pw)$, and the procedure does not take the nonfaulty set $N$ as input. `Option V` represents $V\cup\{\mathrm{NIL}\}$; the set $S_{pq}$ contains values in $V$ only.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 233, Section 5 procedure paragraph; https://doi.org/10.1145/322186.322188

import Mathlib
import Definitions.Def_InteractiveConsistency_Authenticated_Scenario
set_option autoImplicit false

namespace InteractiveConsistency.Authenticated

/-- The non-NIL values obtained for `q` from paths with distinct intermediate
processors, excluding the receiver `p` and the originator `q`. -/
def S {α V : Type*} [DecidableEq α] (m : ℕ) (P : Finset α)
    (τ : List α → Option V) (p q : α) : Set V :=
  {v | ∃ w : List α, w.Nodup ∧ w.length ≤ m ∧
    (∀ x ∈ w, x ∈ P ∧ x ≠ p ∧ x ≠ q) ∧ τ (w ++ [q]) = some v}

/-- Record the unique non-NIL value when there is one, and NIL otherwise. -/
noncomputable def record {α V : Type*} [DecidableEq α] (m : ℕ) (P : Finset α)
    (τ : List α → Option V) (p q : α) : Option V := by
  classical
  exact if h : ∃ v : V, S m P τ p q = {v} then some h.choose else none

end InteractiveConsistency.Authenticated


