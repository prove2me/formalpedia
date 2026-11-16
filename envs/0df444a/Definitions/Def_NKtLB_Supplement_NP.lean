-- Prove2me | Definitions.Def_NKtLB_Supplement_NP
-- name    : NKtLB_Supplement_NP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:29:06.514499+00:00
-- url     : https://prove2.me/theorems/cda62b97-8717-454b-87c2-c77465993513
-- title:
--   $\mathsf{NP}$
-- statement:
--   $\mathsf{NP}=\bigcup_{k\in\mathbb N}\mathsf{NTIME}[n^k]$, with $\mathsf{NTIME}$ from the base mission. It is the oracle class in $\mathsf{BPP}^{\mathsf{NP}}$, $\mathsf{EXP}^{\|\mathsf{NP}}$, $\mathsf{BPEXP}^{\|\mathsf{NP}}$ and $\mathsf{pr}\text{-}\mathsf{BPTIME}[\cdot]^{\|\mathsf{NP}}$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 4, p.9 (oracle class)

import Mathlib
import Definitions.Def_NKtLB_NTIME

namespace NKtLB.Supplement

/-- **`NP`** (used in Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 4, p.9, as the oracle class of `BPP^{NP}`, `EXP^{∥NP}`, …):
`⋃_k NTIME[n^k]`, with the base `NTIME`. -/
def NP : Set (Set (List Bool)) := {L | ∃ k : ℕ, L ∈ NTIME (fun n => n ^ k)}

end NKtLB.Supplement


