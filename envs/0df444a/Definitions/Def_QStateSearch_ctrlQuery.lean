-- Prove2me | Definitions.Def_QStateSearch_ctrlQuery
-- name    : QStateSearch_ctrlQuery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:17.633349+00:00
-- url     : https://prove2.me/theorems/419e08c9-cd8b-4b1f-8df1-a12bcf628a8a
-- title:
--   Controlled oracle call $\mathrm{c}\text{-}O$
-- statement:
--   For a $D\times D$ matrix $O$ the **controlled oracle call** on $\{0,1\}\times[D]\times W$ is
--   $$
--   |0,i,w\rangle\mapsto|0,i,w\rangle,\qquad |1,i,w\rangle\mapsto\sum_{j}O_{ji}\,|1,j,w\rangle ,
--   $$
--   that is, $|0\rangle\langle0|\otimes I\otimes I+|1\rangle\langle1|\otimes O\otimes I$. The oracle acts on the oracle-input register and only when the control qubit is $|1\rangle$.
--
--   As in Aaronson and Kuperberg, controlled calls are allowed; this only strengthens the verifier. An uncontrolled call is the special case in which the control has been set to $|1\rangle$.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.1, p.8

import Mathlib
import Definitions.Def_QStateSearch_Reg

namespace QStateSearch

/-- The controlled oracle call `controlled-O` on `Reg D W = Fin 2 × Fin D × W`:
`|0, i, w⟩ ↦ |0, i, w⟩` and `|1, i, w⟩ ↦ ∑_j O j i |1, j, w⟩`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.1, p.8: "As in Aaronson and Kuperberg [3], controlled oracle calls are
allowed. This only strengthens the verifier."

**Formalization Note.** Every oracle call of the model is controlled. An uncontrolled call is
the case where a unitary step first sets the control to `|1⟩`. Entrywise, the matrix is
`(c, i, w), (c', i', w') ↦ [c = c' ∧ w = w'] · (if c = 0 then [i = i'] else O i i')`. -/
def ctrlQuery {D : ℕ} {W : Type} [DecidableEq W] (O : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Reg D W) (Reg D W) ℂ :=
  Matrix.of fun x y =>
    if x.1 = y.1 ∧ x.2.2 = y.2.2 then
      (if x.1 = 0 then (if x.2.1 = y.2.1 then 1 else 0) else O x.2.1 y.2.1)
    else 0

end QStateSearch


