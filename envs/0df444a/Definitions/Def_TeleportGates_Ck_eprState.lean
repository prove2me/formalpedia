-- Prove2me | Definitions.Def_TeleportGates_Ck_eprState
-- name    : TeleportGates_Ck_eprState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:23.546993+00:00
-- url     : https://prove2.me/theorems/719d8537-afc9-40e1-9349-a9236032d81d
-- title:
--   $2n$-qubit Bell state $|\Psi^n\rangle=(|00\rangle+|11\rangle)^{\otimes n}$, upper qubits first
-- statement:
--   The state $|\Psi^n\rangle$ consists of $n$ EPR pairs, rearranged so that the first $n$ qubits are the upper halves and the last $n$ the lower halves:
--
--   $$|\Psi^n\rangle(b,c)=\prod_{i=1}^n \Psi(b_i,c_i)=\begin{cases}2^{-n/2}, & b=c,\\ 0,& b\ne c,\end{cases}\qquad b,c\in\{0,1\}^n .$$
--
--   The $i$-th EPR pair consists of upper qubit $i$ and lower qubit $i$.
--
--   **Formalization Note** Normalized; the paper suppresses normalizations.
-- source:
--   Gottesman, Chuang, Quantum teleportation is a universal computational primitive, arXiv:quant-ph/9908010v1, §II, unnumbered, p. 2 (definition of |Ψn⟩)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_TeleportGates_Ck_epr1

namespace TeleportGates.Ck

open QAlgorithms

/-- **The 2n-qubit Bell state `|Ψⁿ⟩ = (|00⟩ + |11⟩)^{⊗n}`, upper qubits first.**
Gottesman, Chuang, *Quantum teleportation is a universal computational primitive*,
arXiv:quant-ph/9908010v1, §II, unnumbered, p. 2: "Let |Ψn⟩ be the
2n-(encoded) qubit Bell state (|00⟩ + |11⟩)⊗n (normalizations suppressed for clarity), rearranged
so that the first n labels represent half of the EPR pairs (the upper qubits), and the last n the
other half (the lower qubits)."

`eprState n (b, c) = ∏ᵢ epr1 (b i, c i)`, i.e. `2^{−n/2}` if `b = c` and `0` otherwise: the
`i`-th EPR pair consists of upper qubit `i` and lower qubit `i`.

**Formalization Note.** The first component `b : Qubits n` of the index is the upper register,
the second `c` the lower register. Normalized (the paper suppresses normalizations). -/
noncomputable def eprState (n : ℕ) : EuclideanSpace ℂ (Qubits n × Qubits n) :=
  WithLp.toLp 2 fun p => ∏ i : Fin n, epr1 (p.1 i, p.2 i)

end TeleportGates.Ck


