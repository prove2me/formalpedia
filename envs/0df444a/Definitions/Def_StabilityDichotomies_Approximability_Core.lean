-- Prove2me | Definitions.Def_StabilityDichotomies_Approximability_Core
-- name    : StabilityDichotomies_Approximability_Core
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T04:41:06.881346+00:00
-- url     : https://prove2.me/theorems/83e7a644-e02d-4ee6-8244-f9421ae67c7e
-- title:
--   Local consistency, bounded width, and approximate CSP solvers
-- statement:
--   For a finite Boolean CSP instance, a partial assignment is locally satisfying if it satisfies every constraint whose variables are all assigned. A $(k,\ell)$-strategy is a nonempty family of locally satisfying partial assignments of size at most $\ell$, closed under restriction, such that every member with domain of size at most $k$ extends to every containing domain of size at most $\ell$. A language has bounded width if some fixed $1\le k\le\ell$ ensures that every finite instance admitting such a strategy is satisfiable.
--
--   The number of violations counts constraint occurrences, including multiplicities. A randomized solver $(1-\varepsilon)$-approximates the language if its expected number of violated constraints is at most $\varepsilon|C|$ on every satisfiable instance. These definitions support the stable approximability dichotomy.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Definitions 2.1, 2.7 and 2.8, printed pp. 7–9.

import Definitions.Def_StabilityDichotomies_Solvability_Stability

noncomputable section
open scoped Classical

namespace StabilityDichotomies.Solvability

/-- The domain of a Boolean partial assignment. -/
def partialDomain {V : Type} [Fintype V] (h : V → Option Bool) : Finset V :=
  Finset.univ.filter (fun v => (h v).isSome)

/-- Restrict a partial assignment to a set of variables. -/
def partialRestrict {V : Type} (h : V → Option Bool) (S : Finset V) : V → Option Bool :=
  fun v => if v ∈ S then h v else none

/-- A partial assignment satisfies each constraint whose entire scope is in its domain. -/
def LocallySatisfying {Γ : Language} {V : Type} [Fintype V]
    (I : Instance Γ V) (h : V → Option Bool) : Prop :=
  ∀ c ∈ I.constraints, (∀ i, (h (c.scope i)).isSome) →
    c.Satisfied (fun v => (h v).getD false)

/-- A nonempty (k,l)-strategy as in Definition 2.7. -/
def LocalStrategy {Γ : Language} {V : Type} [Fintype V]
    (I : Instance Γ V) (k l : ℕ) (H : Set (V → Option Bool)) : Prop :=
  H.Nonempty ∧
  (∀ h ∈ H, LocallySatisfying I h ∧ (partialDomain h).card ≤ l) ∧
  (∀ h ∈ H, ∀ S : Finset V, S ⊆ partialDomain h → partialRestrict h S ∈ H) ∧
  (∀ S T : Finset V, S ⊆ T → S.card ≤ k → T.card ≤ l →
    ∀ h ∈ H, partialDomain h = S →
      ∃ g ∈ H, partialDomain g = T ∧ partialRestrict g S = h)

/-- Semantic bounded width, using all finite instances and the local strategies of the source. -/
def BoundedWidth (Γ : Language) : Prop :=
  ∃ k l : ℕ, 1 ≤ k ∧ k ≤ l ∧
    ∀ (V : Type) [Fintype V] (I : Instance Γ V) (H : Set (V → Option Bool)),
      LocalStrategy I k l H → Satisfiable I

/-- Number of violated constraint occurrences, retaining multiset multiplicity. -/
def violationCount {Γ : Language} {V : Type} [Fintype V]
    (I : Instance Γ V) (x : V → Bool) : ℕ :=
  (I.constraints.filter (fun c => ¬c.Satisfied x)).card

/-- Expected violation bound on every satisfiable input. -/
def Approximates {Γ : Language} (A : Solver Γ) (ε : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
    (∑ x : V → Bool, (A V I x).toReal * (violationCount I x : ℝ)) ≤
      ε * I.constraints.card

end StabilityDichotomies.Solvability


