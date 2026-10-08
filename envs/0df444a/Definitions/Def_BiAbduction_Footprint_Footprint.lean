-- Prove2me | Definitions.Def_BiAbduction_Footprint_Footprint
-- name    : BiAbduction_Footprint_Footprint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:54.580207+00:00
-- url     : https://prove2.me/theorems/9181c428-0948-4bf8-83aa-46dd7c8b4876
-- title:
--   Defs. 4.9–4.10 — precise predicates, safe states safe(C), footprints foot(C), and the canonical precondition
-- statement:
--   This file fixes the objects of §4.2.4 (pp. 49–50). Actions are considered without parameters, so an action $\alpha$ enters only through its specification $\{P_\alpha\}\,\alpha\,\{Q_\alpha\}$: an action is a pair of predicates $(P_\alpha, Q_\alpha)$. A **sequence of actions** is nonempty: a first action followed by a (possibly empty) list of further actions.
--
--   1. **Precise predicate (Definition 4.9).** A predicate $P$ is precise if for every stack $s$ and heap $h$ there is at most one subheap $h_f \subseteq h$ with $s, h_f \models P$.
--   2. **Safe states (Definition 4.10(1)).** By induction on the sequence,
--   $$\mathrm{safe}(\alpha) = P_\alpha * \mathsf{true}, \qquad \mathrm{safe}(\alpha; C) = P_\alpha * \big(Q_\alpha \mathbin{-\!\!*} \mathrm{safe}(C)\big).$$
--   3. **Footprint (Definition 4.10(2)).** $\mathrm{foot}(C) = \min(\mathrm{safe}(C))$.
--   4. **Canonical precondition.** The precondition $P_C$ of the canonical spec of $C$, when every call to the bi-abductive prover delivers the best anti-frame: for a single action, $P_\alpha$; for $\alpha; C$, the predicate $P_\alpha * M$, where $P_C$ is the canonical precondition of $C$ and $M$ is a best (≾-least) solution of the abduction question $Q_\alpha * M \models P_C * \mathsf{true}$.
--
--   These are the objects of Theorem 4.11, which identifies the canonical precondition with the footprint.
--
--   **Formalization Note** A sequence is encoded as a head action `α` and a tail list `C`, so `safe α []` is $\mathrm{safe}(\alpha)$ and `safe α (β :: C)` is $\mathrm{safe}(\alpha;\beta;C)$. The paper does not define the canonical spec in §4.2.4; the inductive relation `IsCanonPre` follows the proof of Theorem 4.11 (p. 50), and the anti-frame is any ≾-least solution, *not* the predicate $\min(Q_\alpha \mathbin{-\!\!*} (P_C * \mathsf{true}))$ (that identification is Theorem 3.13). Definition 4.10 assumes every $P_\alpha$ precise; the definitions here are total and the precision hypothesis is carried by the theorems.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 49, Definitions 4.9–4.10; p. 50, Theorem 4.11 and its proof (canonical spec)

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics

namespace BiAbduction.Footprint

/-!
§4.2.4 of Calcagno–Distefano–O'Hearn–Yang (p. 49–50): precise predicates (Definition 4.9),
safe states and footprints of a sequence of actions (Definition 4.10), and the precondition of
the canonical spec (the construction used in Theorem 4.11 and its proof).

Actions ignore parameters (p. 49), so an action enters only through its spec `{Pα} α {Qα}`:
an action *is* the pair `(Pα, Qα)`. A sequence of actions is nonempty, given by its first
action and the list of the remaining ones.
-/

/-- Definition 4.9: `P` is precise if for every `s, h` there is at most one subheap `h_f ⊆ h`
with `s, h_f ⊨ P`. -/
def IsPrecise (P : Pred) : Prop :=
  ∀ (s : Stack) (h h₁ h₂ : Heap), Heap.Subheap h₁ h → Heap.Subheap h₂ h →
    (s, h₁) ∈ P → (s, h₂) ∈ P → h₁ = h₂

/-- An action, given by its spec `{Pα} α {Qα}`: `pre = Pα`, `post = Qα`. -/
structure Action where
  /-- the precondition `Pα` -/
  pre : Pred
  /-- the postcondition `Qα` -/
  post : Pred

/-- Definition 4.10(1): the safe states of the sequence `α; C` (here `α` followed by the list
`C`, so `safe α []` is `safe(α)`):
`safe(α) = Pα ∗ true`, `safe(α; C) = Pα ∗ (Qα −∗ safe(C))`. -/
def safe : Action → List Action → Pred
  | α, [] => sepConj α.pre Set.univ
  | α, β :: C => sepConj α.pre (wand α.post (safe β C))

/-- Definition 4.10(2): the footprint `foot(C) = min(safe(C))`. -/
def foot (α : Action) (C : List Action) : Pred := minSet (safe α C)

/-- `IsCanonPre α C P`: `P` is the precondition of the canonical spec of the sequence `α; C`
when every call to the bi-abductive prover delivers the best anti-frame (Theorem 4.11 and its
proof, p. 50). For a single action it is `Pα`; for `α; C` it is `Pα ∗ M`, where `P_C` is the
canonical precondition of `C` and `M` is the best (`≾`-least) solution of the abduction question
`Qα ∗ ? ⊨ P_C ∗ true`. -/
inductive IsCanonPre : Action → List Action → Pred → Prop
  | single (α : Action) : IsCanonPre α [] α.pre
  | cons (α β : Action) (C : List Action) (PC M : Pred) :
      IsCanonPre β C PC → IsLeastSolution α.post (sepConj PC Set.univ) M →
      IsCanonPre α (β :: C) (sepConj α.pre M)

end BiAbduction.Footprint


