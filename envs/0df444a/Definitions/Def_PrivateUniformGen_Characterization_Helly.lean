-- Prove2me | Definitions.Def_PrivateUniformGen_Characterization_Helly
-- name    : PrivateUniformGen_Characterization_Helly
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:55:18.631258+00:00
-- url     : https://prove2.me/theorems/063df0c2-54c9-4aa5-b33e-24e2c3ff5d19
-- title:
--   Finite-intersection Helly number
-- statement:
--   For any family $C$ of subsets of a space, a positive integer $h$ is a finite-intersection Helly bound if every nonempty subfamily $F\subseteq C$ with finite total intersection has a nonempty subfamily $G$ of at most $h$ members with finite intersection:
--
--   $$|\bigcap F|<\infty\ \Longrightarrow\ \exists G\subseteq F,\quad 1\le |G|\le h,\quad |\bigcap G|<\infty.$$
--
--   The number $h_{\mathrm{fin}}(C)$ is the least such positive integer, or infinity if none exists. The family $F$ may be infinite or uncountable. The empty infimum is infinity, so absence of a finite witness bound never becomes zero. This general family-level definition can be applied both to languages and to their infinite-intersection closure.
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Definition 4.6, p. 10. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib

namespace PrivateUniformGen.Characterization

/-- Definition 4.6, p. 10: arbitrary subfamilies, with a nonempty finite witness. -/
def HasFiniteIntersectionHelly {X : Type*} (C : Set (Set X)) (h : ℕ) : Prop :=
  1 ≤ h ∧ ∀ F : Set (Set X), F.Nonempty → F ⊆ C → (⋂₀ F).Finite →
    ∃ G : Finset (Set X), G.Nonempty ∧ (↑G : Set (Set X)) ⊆ F ∧
      G.card ≤ h ∧ (⋂₀ (↑G : Set (Set X))).Finite

/-- The least positive Helly bound, or top when there is none. -/
noncomputable def hellyNumber {X : Type*} (C : Set (Set X)) : ℕ∞ :=
  sInf {h : ℕ∞ | ∃ k : ℕ, h = k ∧ HasFiniteIntersectionHelly C k}

end PrivateUniformGen.Characterization


