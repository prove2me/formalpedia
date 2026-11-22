-- Prove2me | Definitions.Def_RandPurIso_Completion_isoQueryFin
-- name    : RandPurIso_Completion_isoQueryFin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:11.199828+00:00
-- url     : https://prove2.me/theorems/5bfdf9e8-dd3e-4be7-9778-f69338ea48af
-- title:
--   The query $\Phi^V$ and registers of Theorem 4.1
-- statement:
--   For $N\mid M$, $\mathcal H([M])=A\otimes B$ with $A=\mathcal H([N])$, $B=\mathcal H([M/N])$. `isoQueryFin V` is $\Phi^V$ for $V:A\to A\otimes B$ on $\lceil\log_2N\rceil+\lceil\log_2(M/N)\rceil+1$ qubits (binary labels, flag for $\perp$). `ctrlFinEncIn` and `ctrlFinEncOut` encode the simulator's query input $C\otimes A$ and output $C\otimes A\otimes B$ on the data qubits; strings with the flag set or a label out of range read as $\perp$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 4.1, p. 26

import Mathlib
import Definitions.Def_RandPurIso_Completion_isoQuery
open Matrix

namespace RandPurIso.Completion

open ShiShallow

/-- **The query `Φ^V` of Theorem 4.1** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 26) for `V : H([N]) → H([M]) = A ⊗ B`,
`A = H([N])`, `B = H([M/N])`, on `⌈log₂N⌉ + ⌈log₂(M/N)⌉ + 1` qubits (binary labels, flag for `⊥`). -/
noncomputable def isoQueryFin {N B : ℕ} (V : Matrix (Fin N × Fin B) (Fin N) ℂ) :
    Matrix (Bits (Nat.clog 2 N + Nat.clog 2 B + 1)) (Bits (Nat.clog 2 N + Nat.clog 2 B + 1)) ℂ →
      Matrix (Bits (Nat.clog 2 N + Nat.clog 2 B + 1)) (Bits (Nat.clog 2 N + Nat.clog 2 B + 1)) ℂ :=
  qubitChannel V (fun x => apEnc (finBin x) (zeroBits _) false)
    (fun xb => apEnc (finBin xb.1) (finBin xb.2) false) (apEnc (zeroBits _) (zeroBits _) true)

/-- Encoding of the simulator's query input `C ⊗ A` (Theorem 4.1): control qubit, `bin x`, `B` and
flag zero. -/
def ctrlFinEncIn {N B : ℕ} (cx : Bool × Fin N) : Bits (1 + (Nat.clog 2 N + Nat.clog 2 B + 1)) :=
  Fin.append (fun _ => cx.1) (apEnc (finBin cx.2) (zeroBits (Nat.clog 2 B)) false)

/-- Encoding of the simulator's query output `C ⊗ A ⊗ B` (Theorem 4.1, "Output CAB"); strings with
the flag set, or with a label out of range, read as `⊥`. -/
def ctrlFinEncOut {N B : ℕ} (cxb : Bool × (Fin N × Fin B)) :
    Bits (1 + (Nat.clog 2 N + Nat.clog 2 B + 1)) :=
  Fin.append (fun _ => cxb.1) (apEnc (finBin cxb.2.1) (finBin cxb.2.2) false)

end RandPurIso.Completion


