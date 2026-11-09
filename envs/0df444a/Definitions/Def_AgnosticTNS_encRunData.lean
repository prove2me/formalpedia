-- Prove2me | Definitions.Def_AgnosticTNS_encRunData
-- name    : AgnosticTNS_encRunData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:29.37006+00:00
-- url     : https://prove2.me/theorems/5f0e14b1-d26f-4269-ae79-cdaef6d6d831
-- title:
--   Data of a run used to build the output tensors
-- statement:
--   The data from which Proposition 3.8 constructs the output tensors: $d$, $n$, the learning sequence, the residual sets $R_i$, the entries of the compression unitaries $\tilde U_i$ and of the final residual vector $|\hat\varphi\rangle$, all as Gaussian rationals.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Proposition 3.8, p.24

import Mathlib
import Definitions.Def_AgnosticTNS_Run
import Definitions.Def_AgnosticTNS_encLS
import Definitions.Def_AgnosticTNS_encMat

namespace AgnosticTNS

/-- **The data from which the output tensors are built**, Proposition 3.8, p.24 ("The tensors can be
constructed from the compression unitaries and final residual vector") (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): `d`, `n` in unary,
the learning sequence, then per step the residual set `R_i` and the entries of `Ũ_i`, then the entries
of `φ̂`, all entries as Gaussian rationals in the order of `Fintype.equivFin`. -/
noncomputable def encRunData {d n : ℕ} {Ls : LearningSequence n} (run : Run d n Ls) :
    QAlgorithms.Complexity.Str :=
  QAlgorithms.Complexity.encNat d ++ QAlgorithms.Complexity.encNat n ++ encLS Ls ++
  ((List.finRange Ls.L).map fun i =>
    (List.finRange n).map (fun v => decide (v ∈ run.R i)) ++ encMat (run.U i)).flatten ++
  ((List.finRange (Fintype.card (↥(run.R Ls.root) → Fin d))).map fun t =>
    encC (run.φhat ((Fintype.equivFin _).symm t))).flatten

end AgnosticTNS


