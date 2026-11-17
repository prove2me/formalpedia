-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_OrthCorrectOut
-- name    : AvgCaseTI_Supplement_OrthCorrectOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:31:11.992692+00:00
-- url     : https://prove2.me/theorems/1ff4e02e-53dd-413f-afe9-0ff13ec8c1dc
-- title:
--   Output codes of orthogonal tensor isomorphism: “Fail” and lists of isomorphisms
-- statement:
--   An algorithm for orthogonal tensor isomorphism outputs either “Fail” or a list of triples of $n\times n$ matrices over $\mathbb F_q$. The output code of “Fail” is the single bit $0$. The output code of a list is a leading bit $1$, the self-delimiting length of the list, and then the entries of its triples, each entry written as in the instance code; the empty list is the report “not orthogonally isomorphic”. No list code equals the “Fail” code.
--
--   An output is a **correct answer** for $(A,B)$ when it is the code of a list whose members are exactly the orthogonal isomorphisms $\mathrm{Isos}(A,B)$ (the empty list when there are none). “Fail” is never a correct answer.
--
--   **Formalization Note** The answer is a set: the order and repetitions of the listed triples are immaterial.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 5.6, pp.33–34 (PDF pp.35–36); §5.1, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_AvgCaseTI_encodeInstance
import Definitions.Def_AvgCaseTI_Supplement_orthIsos

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI
open ExponomialAssortment.FPTAS (encodeNat)

/-- Binary code of an `n × n` matrix over a presented field: the codes `encodeElem` of its entries in
row-major order. -/
noncomputable def encodeMat (P : FieldPres) {n : ℕ} (X : Matrix (Fin n) (Fin n) P.F) : List Bool :=
  (List.ofFn fun i : Fin n => (List.ofFn fun j : Fin n => encodeElem P (X i j)).flatten).flatten

/-- Binary code of a triple of matrices `(Q1, Q2, Q3)`. -/
noncomputable def encodeTriple (P : FieldPres) {n : ℕ}
    (t : Matrix (Fin n) (Fin n) P.F × Matrix (Fin n) (Fin n) P.F × Matrix (Fin n) (Fin n) P.F) :
    List Bool :=
  encodeMat P t.1 ++ encodeMat P t.2.1 ++ encodeMat P t.2.2

/-- The output code of "Fail": the one bit `[false]`. -/
def failCode : List Bool := [false]

/-- The output code of a list of triples: a leading `true`, the self-delimiting length of the list, then
the codes of its triples. The empty list is the report "A and B are not orthogonally isomorphic".
No such code equals `failCode`. -/
noncomputable def encodeIsoList (P : FieldPres) {n : ℕ}
    (l : List (Matrix (Fin n) (Fin n) P.F × Matrix (Fin n) (Fin n) P.F × Matrix (Fin n) (Fin n) P.F)) :
    List Bool :=
  true :: (encodeNat l.length ++ (l.map (encodeTriple P)).flatten)

/-- **A correct answer of orthogonal tensor isomorphism.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 5.6, pp.33–34 (PDF pp.35–36): "It outputs the complete set of orthogonal
isomorphisms, correctly reports nonisomorphism, or returns “Fail”."

`OrthCorrectOut P A B out`: `out` is the code of a list of triples whose members are exactly the
orthogonal isomorphisms from `A` to `B` (the empty list when there is none). "Fail" is never a
correct answer.

**Formalization Note.** The answer is a set, so the order and repetitions of the listed triples are
immaterial. -/
def OrthCorrectOut (P : FieldPres) {n : ℕ} (A B : Tensor3 P.F n) (out : List Bool) : Prop :=
  ∃ l : List (Matrix (Fin n) (Fin n) P.F × Matrix (Fin n) (Fin n) P.F × Matrix (Fin n) (Fin n) P.F),
    out = encodeIsoList P l ∧ ∀ t, t ∈ l ↔ t ∈ orthIsos A B

end AvgCaseTI.Supplement


