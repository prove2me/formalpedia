-- Prove2me | Definitions.Def_RandPurIso_Completion_prRegEnc
-- name    : RandPurIso_Completion_prRegEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:20.291647+00:00
-- url     : https://prove2.me/theorems/07d9944b-ad08-4a09-926c-7c01060d2c7f
-- title:
--   Natural qubit encoding of $\mathcal H([N])\otimes\mathbf{St}$
-- statement:
--   The recording register $\mathbf{St}=\bigoplus_{t\le T}\mathcal R_t$ is encoded by a length register of $\lceil\log_2(T+1)\rceil$ qubits followed by $T$ input slots and $T$ output slots of $\lceil\log_2N\rceil$ qubits each, holding the words in binary (unused slots $|0\rangle$); $\mathcal H([N])$ is $\mathrm{bin}\,x$ on $\lceil\log_2N\rceil$ qubits in front. This is the encoding in which Lemma 3.15's gate bound is stated; fixing it keeps the bound from being trivialized by an exotic encoding.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Lemma 3.15, p. 24

import Mathlib
import Definitions.Def_RandPurIso_Completion_PRSt
import Definitions.Def_RandPurIso_Completion_QInstr
open Matrix

namespace RandPurIso.Completion

open ShiShallow

/-- `T` slots of `⌈log₂N⌉` qubits holding a word of length `t ≤ T` (unused slots `|0⟩`). -/
def slotsEnc {N T t : ℕ} (xs : Fin t → Fin N) : Bits (T * Nat.clog 2 N) := fun i =>
  let jl := finProdFinEquiv.symm i
  if h : jl.1.val < t then binEnc (Nat.clog 2 N) (xs ⟨jl.1.val, h⟩).val jl.2 else false

/-- **Natural qubit encoding of the recording register** `St = ⊕_{t≤T} R_t` (used for Lemma 3.15,
Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 24): a length register of `⌈log₂(T+1)⌉` qubits, then `T` input slots and `T` output slots
of `⌈log₂N⌉` qubits each, unused slots `|0⟩`. -/
def prStEnc {N T : ℕ} (r : PRSt N T) :
    Bits (Nat.clog 2 (T + 1) + T * Nat.clog 2 N + T * Nat.clog 2 N) :=
  Fin.append (Fin.append (binEnc (Nat.clog 2 (T + 1)) r.1.val) (slotsEnc (T := T) r.2.1))
    (slotsEnc (T := T) r.2.2)

/-- Width of the encoded `H([N]) ⊗ St`. -/
def prRegWidth (N T : ℕ) : ℕ :=
  Nat.clog 2 N + (Nat.clog 2 (T + 1) + T * Nat.clog 2 N + T * Nat.clog 2 N)

/-- Encoding of `H([N]) ⊗ St`: `bin x` on `⌈log₂N⌉` qubits followed by `prStEnc`. -/
def prRegEnc {N T : ℕ} (p : Fin N × PRSt N T) : Bits (prRegWidth N T) :=
  Fin.append (finBin p.1) (prStEnc p.2)

end RandPurIso.Completion


