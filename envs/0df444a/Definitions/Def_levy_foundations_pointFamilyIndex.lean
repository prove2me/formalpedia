-- Prove2me | Definitions.Def_levy_foundations_pointFamilyIndex
-- name    : levy_foundations_pointFamilyIndex
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T22:56:39.25668+00:00
-- url     : https://prove2.me/theorems/cc3e2607-38f2-4f57-bd22-3ec8293f8f08
-- title:
--   Combined count-and-mark index family
-- statement:
--   Unify Poisson counts K(k) and marked points X(k,n) into a dependent family indexed by the disjoint sum of count indices and mark indices, allowing mutual independence to be asserted in one place.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean#L186-L204. Dependent index family and measurable-space instance. Independently authored Prove2Me draft; statement and imports require remote compiler verification.

import Mathlib.Probability.Independence.Basic

namespace LevyFoundations
def pointFamilyIndexType (E : Type) : ℕ ⊕ (ℕ × ℕ) → Type :=
  Sum.elim (fun _ => ℕ) (fun _ => E)
instance instPointFamilyIndexMeasurable (E : Type) [MeasurableSpace E]
    (i : ℕ ⊕ (ℕ × ℕ)) : MeasurableSpace (pointFamilyIndexType E i) := by
  rcases i with k | p
  · exact (inferInstance : MeasurableSpace ℕ)
  · exact (inferInstance : MeasurableSpace E)
def pointFamilyCombined {Ω E : Type} (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E) :
    ∀ i, Ω → pointFamilyIndexType E i
  | Sum.inl k => K k
  | Sum.inr p => X p.1 p.2
end LevyFoundations


