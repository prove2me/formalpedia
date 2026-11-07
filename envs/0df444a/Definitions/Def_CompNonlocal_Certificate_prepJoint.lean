-- Prove2me | Definitions.Def_CompNonlocal_Certificate_prepJoint
-- name    : CompNonlocal_Certificate_prepJoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:47:07.205952+00:00
-- url     : https://prove2.me/theorems/a184a541-f1da-44b0-9725-ffa089be1390
-- title:
--   Joint state of $S$ and $Q$ given the transcript
-- statement:
--   The unnormalized joint state of the sender's register $S$ and the receiver's qubit $Q$ jointly with the transcript $T=(x,z)$ of the §8.1 preparation. Since the sender acts on its registers and the receiver on fresh ones given only $x$, its entries are products of those of the sender state and the prepared state.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §8.1, p.35 and Lemma 11, p.37

import Mathlib
import Definitions.Def_CompNonlocal_Certificate_senderState
import Definitions.Def_CompNonlocal_Certificate_prepared

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The joint state of the sender's register `S` and the receiver's qubit `Q` in the §8.1
preparation, jointly with the transcript `T = (x, z)`, unnormalized. Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), §8.1, p.35, and Lemma 11, p.37 ("Moreover, the sender's private state
and the prepared state are product conditioned on T = t").

**Formalization Note** The sender's question circuit acts on its own registers and the receiver's
preparation acts on fresh registers given only `x`, so the joint unnormalized operator at
`T = (x, z)` has entries `senderState(x)_{S S'} · prepared(x, z)_{q q'}`. Its trace is the transcript
probability `prepProb x z`. -/
noncomputable def Certificate.prepJoint (c : Certificate) (κ : ℕ) (x : Str)
    (z : Bits (c.A κ).width) :
    Matrix ((Bits (c.Qg κ).outC.length × Bits (c.Qg κ).outQ.length) × Bool)
      ((Bits (c.Qg κ).outC.length × Bits (c.Qg κ).outQ.length) × Bool) ℂ :=
  Matrix.of fun p p' => c.senderState κ x p.1 p'.1 * c.prepared κ x z p.2 p'.2

end CompNonlocal


