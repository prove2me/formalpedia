-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_contrComplexity
-- name    : AgnosticTNS_Supplement_contrComplexity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:27:41.19919+00:00
-- url     : https://prove2.me/theorems/6f8bf5eb-2bf8-443c-a403-1442538b99a6
-- title:
--   Complexity (width) of a contraction sequence
-- statement:
--   The **complexity** of a contraction sequence is the maximum degree of a vertex created by a contraction. Because loops are deleted and parallel edges are counted with multiplicity, the vertex representing $S=A\cup B$ created by merging $A$ and $B$ has degree exactly $|\mathrm{cut}_G(S)|$, so
--   $$
--   \text{complexity} = \max_{\text{steps }(A,B)} |\mathrm{cut}_G(A\cup B)|.
--   $$
--   The degrees of the initial vertices are not included; the complexity of the empty sequence is $0$. It bounds the size of every cut created by a contraction and hence the Schmidt rank $\chi^{C}$ of reference states across these cuts.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 5.4 and the paragraph after it, p.41

import Mathlib
import Definitions.Def_AgnosticTNS_cut

namespace AgnosticTNS.Supplement

/-- **The complexity (width) of a contraction sequence**, Definition 5.4, p.41 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
the maximum degree of a vertex created by a contraction; the vertex created by merging `A` and `B`
has degree exactly `|cut_G(A ∪ B)|` (parallel edges counted, loops deleted, p.41). The degrees of
the initial vertices are not included; `0` if there is no step. -/
noncomputable def contrComplexity {n : ℕ} (G : SimpleGraph (Fin n))
    (steps : List (Finset (Fin n) × Finset (Fin n))) : ℕ :=
  (steps.map fun s => (cut G (s.1 ∪ s.2)).card).foldr max 0

end AgnosticTNS.Supplement


