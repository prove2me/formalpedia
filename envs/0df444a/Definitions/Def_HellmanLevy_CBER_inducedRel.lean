-- Prove2me | Definitions.Def_HellmanLevy_CBER_inducedRel
-- name    : HellmanLevy_CBER_inducedRel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:53:39.853028+00:00
-- url     : https://prove2.me/theorems/c770b2cd-9d46-4028-bd5f-837c86ada45d
-- title:
--   Relation induced by a map
-- statement:
--   Given a relation $E$ on $\Omega$ and a map $\iota:\Omega\to\Theta$, the **induced relation** on $\Theta$ is
--   $$D=\{(\iota(\omega_1),\iota(\omega_2)) : (\omega_1,\omega_2)\in E\}.$$
--
--   It is the relation whose smoothness and hyperfiniteness Lemma A.1 transfers from $E$.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), Lemma A.1, p.31

import Mathlib

namespace HellmanLevy.CBER

/-- The relation induced on `Θ` by a relation `E` on `Ω` and a map `ι : Ω → Θ`:
`D = {(ι ω₁, ι ω₂) | (ω₁, ω₂) ∈ E}`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), Lemma A.1, p.31. -/
def inducedRel {Ω Θ : Type*} (E : Ω → Ω → Prop) (ι : Ω → Θ) (θ₁ θ₂ : Θ) : Prop :=
  ∃ ω₁ ω₂, ι ω₁ = θ₁ ∧ ι ω₂ = θ₂ ∧ E ω₁ ω₂

end HellmanLevy.CBER


