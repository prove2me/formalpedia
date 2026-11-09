-- Prove2me | Definitions.Def_AgnosticTNS_Run
-- name    : AgnosticTNS_Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:19.187502+00:00
-- url     : https://prove2.me/theorems/3e700bd7-7a59-4ff7-bfe5-5f2571b253ea
-- title:
--   Choices of a run of Algorithm 1
-- statement:
--   A run of Algorithm 1 (AgnosticLearnTNSFromSequence) on a learning sequence that completes all tomography calls is described by the choices it makes: the residual sets $R_i$ (lines 5–9), the tomography estimates $\hat\sigma_i$ on $M_i$ (line 10), the local unitaries $\tilde U_i$ on $M_i$ (line 12), the final estimate $\hat\tau$ on $R_L$ (line 20) and the normalised top eigenvector $|\hat\varphi\rangle$ of $\hat\tau$ (line 21). All other objects of the algorithm ($M_i$, $Q_i=M_i\setminus R_i$, the maps $P$, $U$, $K$ and the output $|\hat\psi\rangle$) are computed from these.
--
--   **Formalization Note** Operators on $M_i$ are matrices indexed by the labels of the qudits of $M_i$. The estimates and unitaries of non-compressing steps are unused.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Algorithm 1, p.19

import Mathlib
import Definitions.Def_AgnosticTNS_Mset
import Definitions.Def_AgnosticTNS_LearningSequence_root

namespace AgnosticTNS

/-- **The choices made by one run of Algorithm 1** (AgnosticLearnTNSFromSequence), p.19 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)),
on a run that completes all tomography calls: the residual sets `R_i` (lines 5–9), the estimates
`σ̂_i` (line 10), the local unitaries `Ũ_i` (line 12), the final estimate `τ̂` (line 20) and the top
eigenvector `φ̂` (line 21). Everything else (`M_i`, `Q_i`, `P`, `U`, `K`, `ψ̂`) is computed from these
(`Run.Kupto`, `Run.Ucomp`, `Run.psiHat`); which choices are admissible is `Run.IsValid`.

**Formalization Note** Operators on `M_i` are matrices indexed by the labels of the qudits of `M_i`
(`↥(M_i) → Fin d`). The fields `σ̂_i, Ũ_i` of non-compressing steps (`|M_i| ≤ p_i`) are unused. -/
structure Run (d n : ℕ) (Ls : LearningSequence n) where
  /-- the residual sets `R_i` -/
  R : Fin Ls.L → Finset (Fin n)
  /-- the tomography estimates `σ̂_i` on `M_i` -/
  σhat : (i : Fin Ls.L) → Matrix (↥(Mset Ls R i) → Fin d) (↥(Mset Ls R i) → Fin d) ℂ
  /-- the local compression unitaries `Ũ_i` on `M_i` -/
  U : (i : Fin Ls.L) → Matrix (↥(Mset Ls R i) → Fin d) (↥(Mset Ls R i) → Fin d) ℂ
  /-- the final estimate `τ̂` on `R_L` -/
  τhat : Matrix (↥(R Ls.root) → Fin d) (↥(R Ls.root) → Fin d) ℂ
  /-- the final residual vector `φ̂` on `R_L` -/
  φhat : (↥(R Ls.root) → Fin d) → ℂ

end AgnosticTNS


