-- Prove2me | Definitions.Def_RandPurIso_Completion_Supplement_searchEnc
-- name    : RandPurIso_Completion_Supplement_searchEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:52:40.006574+00:00
-- url     : https://prove2.me/theorems/44a047f4-b75d-4e63-9be7-0e5864f3c9a9
-- title:
--   Qubit encodings of $\mathcal C_z$'s dilation queries and switch queries
-- statement:
--   Encodings that let a Clifford+T circuit query a dilation of $\mathcal C_z$ or the self-switch $\mathrm{Sw}[\mathcal C_z,\mathcal C_z]$ (Theorem 7.10):
--
--   1. a basis state $|i\rangle|v\rangle$ of $\mathcal H([m])\otimes\mathbf{In}$ gets the index $i(Ld+1)+\iota(v)$, where $\iota(|s\rangle)=0$ and $\iota(|x,y\rangle)=1+xd+y$, written in binary on $w=\lceil\log_2(m(Ld+1))\rceil$ qubits;
--   2. a query to an isometry $W:\mathcal H([m])\otimes\mathbf{In}\to(\mathcal H([m])\otimes\mathbf{In})\otimes\mathcal H([e])$ acts on $w+\lceil\log_2 e\rceil+1$ qubits: input $|\mathrm{bin}(p)\rangle|0\cdots0\rangle|0\rangle$, output $|\mathrm{bin}(p')\rangle|\mathrm{bin}(j)\rangle|0\rangle$ with amplitude $W_{(p',j),p}$; every other string fails to $|0\cdots0\rangle|0\cdots0\rangle|1\rangle$;
--   3. a switch query applies $\mathrm{Sw}[\mathcal C_z,\mathcal C_z]$ on $1+w+1$ qubits (control, index string, failure flag), every other string failing to $|0\rangle|0\cdots0\rangle|1\rangle$.
--
--   **Formalization Note** The layouts follow the base mission's `isoQuery` (failure flag as the last qubit) and `qubitChannel`. Both encodings are injective and the failure strings lie outside their ranges.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 7.10, p. 58

import Mathlib
import Definitions.Def_RandPurIso_Completion_isoQuery
import Definitions.Def_RandPurIso_Completion_Supplement_qswitch
import Definitions.Def_RandPurIso_Completion_Supplement_searchChannel
import Definitions.Def_RandPurIso_Completion_Supplement_chanQubit
open Matrix

namespace RandPurIso.Completion.Supplement

open ShiShallow RandPurIso.Completion

/-- Index of a basis state of `In = Span(|s⟩) ⊕ H([L]) ⊗ H([d])`: `|s⟩ ↦ 0`, `|x, y⟩ ↦ 1 + x·d + y`
(a bijection onto `[Ld + 1]`). -/
def inIdx {L d : ℕ} : InSp L d → ℕ
  | none => 0
  | some (x, y) => 1 + x.val * d + y.val

/-- Index of a basis state `|i⟩|v⟩` of `H([m]) ⊗ In`: `i·(Ld + 1) + inIdx v` (a bijection onto
`[m(Ld + 1)]`). -/
def cIdx {m L d : ℕ} (p : Fin m × InSp L d) : ℕ := p.1.val * (L * d + 1) + inIdx p.2

/-- Number of qubits of the `H([m]) ⊗ In` register: `⌈log₂(m(Ld + 1))⌉`. -/
def cw (m L d : ℕ) : ℕ := Nat.clog 2 (m * (L * d + 1))

/-- Little-endian binary encoding of `H([m]) ⊗ In` on `cw m L d` qubits. -/
def cEnc {m L d : ℕ} (p : Fin m × InSp L d) : Bits (cw m L d) := binEnc (cw m L d) (cIdx p)

/-- **Forward query to an isometry dilation `W : H([m]) ⊗ In → (H([m]) ⊗ In) ⊗ H([e])` of `C_z`**
on `cw + ⌈log₂ e⌉ + 1` qubits (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Theorem 7.10, p. 58; layout of the base mission's `isoQuery`):
input `|cEnc p⟩|0…0⟩|0⟩`, output `|cEnc p'⟩|bin j⟩|0⟩` with amplitude `W_{(p', j), p}`, every other input
string failing to `⊥ = |0…0⟩|0…0⟩|1⟩` (the last qubit is the failure flag). -/
noncomputable def dilQuery {m L d e : ℕ}
    (W : Matrix ((Fin m × InSp L d) × Fin e) (Fin m × InSp L d) ℂ) :
    Matrix (Bits (cw m L d + Nat.clog 2 e + 1)) (Bits (cw m L d + Nat.clog 2 e + 1)) ℂ →
      Matrix (Bits (cw m L d + Nat.clog 2 e + 1)) (Bits (cw m L d + Nat.clog 2 e + 1)) ℂ :=
  qubitChannel W (fun p => apEnc (cEnc p) (zeroBits (Nat.clog 2 e)) false)
    (fun pj => apEnc (cEnc pj.1) (binEnc (Nat.clog 2 e) pj.2.val) false)
    (apEnc (zeroBits (cw m L d)) (zeroBits (Nat.clog 2 e)) true)

/-- Encoding of `C ⊗ H([m]) ⊗ In` on `1 + cw + 1` qubits: control qubit, the `cEnc` string, and a
failure flag `0`. -/
def swEnc {m L d : ℕ} (p : Bool × (Fin m × InSp L d)) : Bits (1 + cw m L d + 1) :=
  Fin.append (Fin.append (fun _ : Fin 1 => p.1) (cEnc p.2)) (fun _ : Fin 1 => false)

/-- The failure string `|0⟩|0…0⟩|1⟩` of `swEnc`. -/
def swBot (m L d : ℕ) : Bits (1 + cw m L d + 1) :=
  Fin.append (Fin.append (fun _ : Fin 1 => false) (zeroBits (cw m L d))) (fun _ : Fin 1 => true)

/-- **One application of the self-switch `Sw[C_z, C_z]`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Theorem 7.10, p. 58) as a channel on
`1 + cw + 1` qubits: `Sw[C_z, C_z]` (built from the Kraus family `searchKraus z U`) on strings
`swEnc`, every other string failing to `swBot`. -/
noncomputable def swQuery {m L d : ℕ} (z : Fin m → Bool)
    (U : Fin m → Fin L → Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Bits (1 + cw m L d + 1)) (Bits (1 + cw m L d + 1)) ℂ →
      Matrix (Bits (1 + cw m L d + 1)) (Bits (1 + cw m L d + 1)) ℂ :=
  chanQubit (qswitch (searchKraus z U) (searchKraus z U)) swEnc (swBot m L d)

end RandPurIso.Completion.Supplement


