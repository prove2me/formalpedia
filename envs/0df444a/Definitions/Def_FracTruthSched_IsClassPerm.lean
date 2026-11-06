-- Prove2me | Definitions.Def_FracTruthSched_IsClassPerm
-- name    : FracTruthSched_IsClassPerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:11.406869+00:00
-- url     : https://prove2.me/theorems/12f57dcb-add8-4d9f-9611-4804ae42855c
-- title:
--   Relabelling of core tasks within classes
-- statement:
--   A permutation $\gamma$ of the core tasks of $MC_\ell$ **relabels tasks within classes** if it maps every edge of each class $Q_{\{u,v\}}$ to an edge of the same class and fixes every self-loop. These are the relabellings in the symmetry property (iv) of the padding lemma.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Lemma 1 (iv), p.9; App. A, p.23

import Mathlib
import Definitions.Def_FracTruthSched_CoreTask

set_option autoImplicit false

namespace FracTruthSched

/-- A **relabelling of tasks within classes** of `MC_ℓ` (Anastasiadis et al., arXiv:2611.06642v1,
Lemma 1 (iv), p.9: "Relabelling tasks within any class Q{i,j}"; App. A, p.23: permutations "that map
every edge … to a parallel edge and fix every self-loop"): a permutation of the core tasks mapping
every edge of each class `Q{u,v}` into the same class and fixing every self-loop.

**Formalization Note.** These are exactly the products of relabellings of single classes, so a
property preserved under composition holds for all of them as soon as it holds for single-class
relabellings. -/
def IsClassPerm {n ℓ : ℕ} (γ : Equiv.Perm (CoreTask n ℓ)) : Prop :=
  (∀ (p : {p : Fin n × Fin n // p.1 < p.2}) (k : Fin ℓ), ∃ k', γ (.inl (p, k)) = .inl (p, k')) ∧
    ∀ i, γ (.inr i) = .inr i

end FracTruthSched


