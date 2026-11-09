-- Prove2me | Definitions.Def_AgnosticTNS_Run_Kupto
-- name    : AgnosticTNS_Run_Kupto
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:39.658497+00:00
-- url     : https://prove2.me/theorems/2bc8b3a9-c958-41fe-aa68-22a4e4850983
-- title:
--   Cumulative postselection map $K_{<i}$
-- statement:
--   For a run, $K_{<t}$ is the product $P_cU_c\cdots P_1U_1$ over the compressing steps $j<t$ (those with $|M_j|>p_j$), later steps on the left, with $U=\tilde U_j\otimes I$ and $P=|0\rangle\langle0|_{Q_j}\otimes I$ (Algorithm 1, lines 13–15). In particular $K_{<i}$ is the map constructed before step $i$ (Lemma 3.4) and $K_c=K_{<L+1}$ is the final map.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Algorithm 1 lines 13–15, p.19; Lemma 3.4, p.20

import Mathlib
import Definitions.Def_AgnosticTNS_Run
import Definitions.Def_AgnosticTNS_embedOp
import Definitions.Def_AgnosticTNS_zeroProj

namespace AgnosticTNS

/-- **The cumulative postselection map**, Algorithm 1 lines 13–15, p.19 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
`Run.Kupto run p t` is the product `P_c U_c ⋯ P_1 U_1` over the compressing steps `j` (those with
`|M_j| > p_j`) with index `j < t`, later steps on the left, where `U = Ũ_j ⊗ I` and
`P = |0⟩⟨0|_{Q_j} ⊗ I` with `Q_j = M_j ∖ R_j`. So `K_{<i} = Kupto run p i` (Lemma 3.4) and the final
`K_c = Kupto run p L`. -/
noncomputable def Run.Kupto {d n : ℕ} {Ls : LearningSequence n} (run : Run d n Ls)
    (p : Fin Ls.L → ℕ) (t : ℕ) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ((List.finRange Ls.L).filter fun j => j.val < t ∧ p j < (Mset Ls run.R j).card).foldl
    (fun K j => zeroProj (Mset Ls run.R j \ run.R j) * embedOp (Mset Ls run.R j) (run.U j) * K) 1

end AgnosticTNS


