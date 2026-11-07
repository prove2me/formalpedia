-- Prove2me | Definitions.Def_QuasiStrictNE_IsFaceChain
-- name    : QuasiStrictNE_IsFaceChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:00.080257+00:00
-- url     : https://prove2.me/theorems/9d6a4b85-fd4b-4b06-ab15-4c1a836c5366
-- title:
--   Chain of faces $F_0\subsetneq\cdots\subsetneq F_r$
-- statement:
--   A **chain** of a collection $C$ of sets is a nonempty finite family $F_0\subsetneq F_1\subsetneq\cdots\subsetneq F_r$ ($r\ge 0$) of members of $C$ totally ordered by inclusion. Chains of the face poset are the simplices of its order complex.
--
--   **Formalization Note** A chain is a `Finset` of sets totally ordered by $\subseteq$; its members are distinct, hence strictly increasing.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 4, p.6

import Mathlib

namespace QuasiStrictNE

/-- **A chain of faces** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict
Equilibria*, arXiv:2611.06350, Definition 4, p.6: "the simplices correspond to chains of faces
F0 ⊊ F1 ⊊ · · · ⊊ Fr, r ≥ 0").

`IsFaceChain C σ` holds iff `σ` is a nonempty finite set of members of `C` that is totally ordered by
inclusion.

**Formalization Note** A chain is a `Finset` of sets; its members are distinct, so a chain under `⊆`
is a strict chain `F0 ⊊ ⋯ ⊊ Fr`. -/
def IsFaceChain {d : ℕ} (C : Set (Set (Fin d → ℝ))) (σ : Finset (Set (Fin d → ℝ))) : Prop :=
  σ.Nonempty ∧ (↑σ : Set (Set (Fin d → ℝ))) ⊆ C ∧
    IsChain (· ⊆ ·) (↑σ : Set (Set (Fin d → ℝ)))

end QuasiStrictNE


