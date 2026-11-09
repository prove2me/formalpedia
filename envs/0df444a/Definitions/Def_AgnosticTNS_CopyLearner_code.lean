-- Prove2me | Definitions.Def_AgnosticTNS_CopyLearner_code
-- name    : AgnosticTNS_CopyLearner_code
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:23.355344+00:00
-- url     : https://prove2.me/theorems/5658ac77-9c7a-45af-aa72-3ba64583c7dc
-- title:
--   Description of a learner at an instance
-- statement:
--   The description of the learner at instance $i$: the number of copies and of ancillas in unary, the output wires, and the circuit. Printing it takes at least as many steps as there are copies and gates, so a polynomial-time printer bounds both.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 3.6, p.23; Proposition 3.10, p.26

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner
import Definitions.Def_QAlgorithms_ClassicalStringListEncoding
open QAlgorithms.Complexity

namespace AgnosticTNS

/-- **The description of a learner at an index**, printed by the uniform generators of Theorem 3.6,
Corollaries 3.7, 5.1, 5.2 and Lemma 3.9 (running time, pp.23–26, 39–40) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the copy count and
the ancilla count in unary, the output wires, and the circuit (the published `encCirc`). Printing it
takes at least as many steps as there are copies and gates. -/
def CopyLearner.code {ι : Type} {nOf dOf : ι → ℕ} (Lr : CopyLearner ι nOf dOf) (i : ι) :
    QAlgorithms.Complexity.Str :=
  encNat (Lr.copies i) ++ encNat (Lr.anc i) ++ encStr ((Lr.out i).map fun w => encNat w.val) ++
    encCirc (Lr.circ i)

end AgnosticTNS


