-- Prove2me | Definitions.Def_BiAbduction_Systematic_Incompat
-- name    : BiAbduction_Systematic_Incompat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:10.425022+00:00
-- url     : https://prove2.me/theorems/dad6378a-6e50-49ec-8f70-eab248ada632
-- title:
--   §3.4.3 — the disjunction Incompat(Δ) of incompatible solutions
-- statement:
--   For a left-hand side $\Delta\equiv\big(\bigwedge_{i=1}^n A_i\big)\wedge\big(\ast_{j=1}^m E_j\mapsto E'_j\big)$, where each $A_i$ is an equality or a disequality, define the disjunction of symbolic heaps
--   $$\mathrm{Incompat}(\Delta)=\Big(\bigvee_{i=1}^n\neg A_i\Big)\vee\Big(\bigvee_{j=1}^m E_j=0\Big)\vee\Big(\bigvee_{i,j=1..m,\ i\neq j}E_i=E_j\Big)\vee\Big(\bigvee_{j=1}^m\exists X.\,E_j\mapsto X*\mathsf{true}\Big).$$
--   Here $\neg A_i$ is $A_i$ with $=$ and $\neq$ exchanged, and each pure disjunct is read as $\Pi\wedge\mathsf{true}$ (p. 14). The disjunction describes the states that cannot be combined with $\Delta$: inconsistent pure part, a nil address, two equal addresses, or an address of $\Delta$ already allocated.
--
--   **Formalization Note** The bound variable $X$ is chosen as one more than the largest variable occurring in $\Delta$, so it is fresh for $\Delta$.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 31, §3.4.3 (definition of Incompat(∆))

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Syntax

namespace BiAbduction.Systematic

/-!
§3.4.3 (p. 31): the disjunction `Incompat(Δ)` describing the incompatible solutions.
-/

/-- `¬A` for a pure atom `A`: equality and disequality swapped. -/
def negAtom (a : PureAtom) : PureAtom := (!a.1, a.2)

/-- A variable that does not occur in `Δ` (one more than the largest variable of `Δ`). -/
def freshVar (Δ : LHS) : ℕ := (lhsVars Δ).foldr max 0 + 1

/-- For `Δ ≡ (∧ᵢ Aᵢ) ∧ (∗ⱼ Eⱼ↦E'ⱼ)`,
`Incompat(Δ) = (∨ᵢ ¬Aᵢ) ∨ (∨ⱼ Eⱼ=0) ∨ (∨_{i≠j} Eᵢ=Eⱼ) ∨ (∨ⱼ ∃X. Eⱼ↦X ∗ true)`,
every pure disjunct read as `· ∧ true` and `X` a variable not occurring in `Δ`. -/
def incompat (Δ : LHS) : Disj :=
  Δ.1.map (fun a => ([], ([negAtom a], [], true))) ++
  Δ.2.map (fun pt => ([], ([(true, pt.1, Sum.inr 0)], [], true))) ++
  (List.finRange Δ.2.length).flatMap (fun i =>
    (List.finRange Δ.2.length).flatMap (fun j =>
      if i = j then [] else [([], ([(true, (Δ.2.get i).1, (Δ.2.get j).1)], [], true))])) ++
  Δ.2.map (fun pt => ([freshVar Δ], ([], [(pt.1, Sum.inl (freshVar Δ))], true)))

end BiAbduction.Systematic


