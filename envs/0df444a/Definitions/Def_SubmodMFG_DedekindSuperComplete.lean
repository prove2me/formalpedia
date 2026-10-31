-- Prove2me | Definitions.Def_SubmodMFG_DedekindSuperComplete
-- name    : SubmodMFG_DedekindSuperComplete
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:04.732642+00:00
-- url     : https://prove2.me/theorems/7fcf98c2-933f-4147-a843-292cfe75ffe5
-- title:
--   Dedekind super complete lattice (Definition A.1 a))
-- statement:
--   A lattice $L$ is **Dedekind super complete** if every nonempty subset of $L$ that is bounded above (resp. below) has a countable subset with the same least upper bound (resp. greatest lower bound).
--
--   For a complete lattice $L$, where every subset is bounded, this says: for every nonempty $S\subseteq L$ there are countable sets $C,C'\subseteq S$ with
--   $$
--   \sup C=\sup S,\qquad \inf C'=\inf S .
--   $$
--
--   In Section 2 the space of distributions $L$ is assumed to be complete and Dedekind super complete. The property lets a supremum or infimum over an arbitrary set of best responses be realized along a sequence, which is how Assumption 2.1 (2) on sequences reaches $\inf R(\mu)$ and $\sup R(\mu)$.
--
--   **Formalization Note** $L$ carries Mathlib's `CompleteLattice`, so the boundedness proviso is void. The countable subset may be empty; this changes nothing, since $\sup\emptyset=\sup S$ forces $S=\{\bot\}$, and then $C=S$ works.
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, Appendix A, Definition A.1 a), p.33

import Mathlib

namespace SubmodMFG

/-- **Dedekind super complete lattice.**
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, Appendix A, Definition A.1 a), p.33: "We say that L is Dedekind super
complete if every nonempty subset, that is bounded above or below, has a countable subset with
the same least upper bound or greatest lower bound, respectively."

For a complete lattice `L`: every nonempty `S ⊆ L` has a countable subset `C ⊆ S` with
`sup C = sup S`, and a countable subset `C ⊆ S` with `inf C = inf S`.

**Formalization Note.** The paper uses this notion only for complete lattices (§2.1, p.5), so `L`
carries Mathlib's `CompleteLattice`; there every subset is bounded above and below, and the
boundedness proviso is void. The countable subset may be empty; this changes nothing, since
`sSup ∅ = sSup S` forces `S = {⊥}`, and then `C = S` is a nonempty countable choice (dually for
`sInf`). -/
def DedekindSuperComplete (L : Type*) [CompleteLattice L] : Prop :=
  ∀ S : Set L, S.Nonempty →
    (∃ C ⊆ S, C.Countable ∧ sSup C = sSup S) ∧ (∃ C ⊆ S, C.Countable ∧ sInf C = sInf S)

end SubmodMFG


