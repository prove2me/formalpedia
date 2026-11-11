-- Prove2me | Definitions.Def_DepthOptQC_Synth_CleanlyComputes
-- name    : DepthOptQC_Synth_CleanlyComputes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:13:57.584764+00:00
-- url     : https://prove2.me/theorems/9e060173-3251-4483-94c5-3c99d31865db
-- title:
--   Clean reversible computation of a Boolean function: $|\vec x\rangle|b\rangle|0^a\rangle\mapsto|\vec x\rangle|b\oplus f(\vec x)\rangle|0^a\rangle$
-- statement:
--   A layered circuit $C$ on $m+1+a$ qubits **cleanly computes** $f:\{0,1\}^m\to\{0,1\}$ if for every $\vec x\in\{0,1\}^m$ and $b\in\{0,1\}$
--   $$
--   C\,|\vec x\rangle|b\rangle|0^a\rangle = |\vec x\rangle|b\oplus f(\vec x)\rangle|0^a\rangle .
--   $$
--   The input is unchanged, the output bit is XORed with $f(\vec x)$ and all $a$ ancillas return exactly to $|0\rangle$. By linearity the circuit computes $f$ coherently on superpositions of inputs.
--
--   **Formalization Note** The input occupies wires $0,\dots,m-1$, the output bit wire $m$, and the ancillas the remaining $a$ wires.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, §3.2, Eq. (33), p.16

import Definitions.Def_DepthOptQC_Synth_LayeredCircuit

namespace DepthOptQC.Synth

open QAlgorithms

/-- The basis index `|x⟩|b⟩|0^a⟩` of an `(m + 1 + a)`-qubit register: the input `x` on wires
`0, …, m−1`, the output bit `b` on wire `m`, and `a` zero ancillas on the remaining wires
(Vasconcelos, *Depth-Optimal Quantum Compilation*, arXiv:2609.34659, Eq. (33), p.16). -/
def threshIdx {m a : ℕ} (x : Qubits m) (b : Bool) : Qubits (m + 1 + a) :=
  Fin.append (Fin.append x (fun _ : Fin 1 => b)) (fun _ : Fin a => false)

/-- **Clean computation of a Boolean function** (Vasconcelos, arXiv:2609.34659, Eq. (33), p.16):
the layered circuit `c` on `m + 1 + a` wires cleanly computes `f : {0,1}^m → {0,1}` if for every
`x ∈ {0,1}^m` and `b ∈ {0,1}` it implements `|x⟩|b⟩|0^a⟩ ↦ |x⟩|b ⊕ f(x)⟩|0^a⟩` exactly.

**Formalization Note.** The input register comes first, then the output bit, then the ancillas
(`threshIdx`). By linearity this determines the action on all superpositions of such inputs. -/
def CleanlyComputes {S : Set Gate} {m a : ℕ} (c : LayeredCircuit S (m + 1 + a))
    (f : Qubits m → Bool) : Prop :=
  ∀ (x : Qubits m) (b : Bool),
    act c.unitary (ket (threshIdx (a := a) x b)) = ket (threshIdx (a := a) x (xor b (f x)))

end DepthOptQC.Synth


