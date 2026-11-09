-- Prove2me | Definitions.Def_AgnosticTNS_Run_Ucomp
-- name    : AgnosticTNS_Run_Ucomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:51.552858+00:00
-- url     : https://prove2.me/theorems/6dd85f5d-65b6-443e-a530-93b5c672a179
-- title:
--   Product of the compression unitaries $U_{\le c}$
-- statement:
--   $U_{\le c}=U_cU_{c-1}\cdots U_1$, the product of the embedded compression unitaries $\tilde U_j\otimes I$ over the compressing steps, later steps on the left.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Eq. (3.43), p.22

import Mathlib
import Definitions.Def_AgnosticTNS_Run
import Definitions.Def_AgnosticTNS_embedOp

namespace AgnosticTNS

/-- **The product of the compression unitaries `U_{≤c} = U_c ⋯ U_1`**, Eq. (3.43), p.22 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)), over
the compressing steps (`|M_j| > p_j`), later steps on the left, `U = Ũ_j ⊗ I`. -/
noncomputable def Run.Ucomp {d n : ℕ} {Ls : LearningSequence n} (run : Run d n Ls)
    (p : Fin Ls.L → ℕ) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ((List.finRange Ls.L).filter fun j => p j < (Mset Ls run.R j).card).foldl
    (fun U j => embedOp (Mset Ls run.R j) (run.U j) * U) 1

end AgnosticTNS


