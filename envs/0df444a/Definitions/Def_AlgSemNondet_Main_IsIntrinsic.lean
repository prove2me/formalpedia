-- Prove2me | Definitions.Def_AlgSemNondet_Main_IsIntrinsic
-- name    : AlgSemNondet_Main_IsIntrinsic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:47:00.897322+00:00
-- url     : https://prove2.me/theorems/1d797c2c-6eae-4f4d-835b-d6c132d928c9
-- title:
--   Definition 4.2 — intrinsic property of Turing machine operational semantics
-- statement:
--   A property $\mathfrak P$ of a machine $M$ on an input $w$ is **intrinsic** if for every blank-preserving permutation $\pi : \Gamma \to \Gamma$ (that is, $\pi(B) = B$; no condition on the input alphabet), every machine $M$ and every word $w$,
--   $$\mathfrak P(M, w) \iff \mathfrak P(M_\pi, \pi(w)),$$
--   where $\pi(w)$ applies $\pi$ letter by letter.
--
--   Formalization Note: properties are predicates on machines with a fixed state type $Q$, alphabet $\Gamma$ and blank $B$ and on words over $\Gamma$; $M_\pi$ stays in this class.
-- source:
--   Zheng, Zheng, Wang and Huang, An Algebraic Semantic Framework for Nondeterministic Computation, July 2026, Definition 4.2, p.15, held PDF SHA256 729429b16e49937f0b09fd345508cf77ac999be7b0601b781b9e37eb393587fa

import Mathlib
import Definitions.Def_AlgSemNondet_Main_TuringMachine
import Definitions.Def_AlgSemNondet_Main_relabel

namespace AlgSemNondet.Main

/-- Definition 4.2 (intrinsic property). A property `P` of a machine `M` on an input `w` is
intrinsic iff for every blank-preserving permutation `π : Γ → Γ` (`π(B) = B`; no condition on
`Σ`), `M` has `P` on `w` iff `M_π` has `P` on `π(w)` (`π` applied letterwise). -/
def IsIntrinsic {Q Γ : Type*} [Fintype Q] [Fintype Γ] {B : Γ}
    (P : TuringMachine Q Γ B → List Γ → Prop) : Prop :=
  ∀ (π : Equiv.Perm Γ), π B = B →
    ∀ (M : TuringMachine Q Γ B) (w : List Γ), P M w ↔ P (M.relabel π) (w.map π)

end AlgSemNondet.Main


