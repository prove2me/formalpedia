-- Prove2me | Definitions.Def_RegevRecon_DecoderCircuit
-- name    : RegevRecon_DecoderCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:43.499974+00:00
-- url     : https://prove2.me/theorems/5218af6f-8644-42a8-85a7-12cc188bf6a5
-- title:
--   The block error of a decoder circuit over $\{H,T,\mathrm{CNOT}\}$
-- statement:
--   A **decoder circuit** has wires for the received word ($mb$ wires, $b=\lceil\log_2p\rceil$), the estimate (the next $mb$ wires) and work. Its input for a codeword $d$ is $|v_d\rangle\otimes|0\rangle\otimes|0\rangle$ for the channel with every target set equal to $S$. Its **block error** is the average over $d\in C^\perp$ of the probability that the estimate wires do not read $d$.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), Proposition 2, p.15; p.16

import Mathlib
import Definitions.Def_RegevRecon_GibbsPreparable
import Definitions.Def_RegevRecon_RegevPipeline

namespace RegevRecon

open Finset QAlgorithms

variable {p m n : ℕ} [Fact p.Prime]

/-- The basis pattern `|r⟩_received |0⟩_estimate |0⟩_work` on `N` wires: wires `0 ≤ w < m b` hold the bits of
`r` (wire `j b + i` is bit `i` of `(r j).val`), the estimate register `m b ≤ w < 2 m b` and the work wires are `0`. -/
def receivedBasis (p N : ℕ) [Fact p.Prime] (r : Fin m → ZMod p) : Qubits N := fun w =>
  if h : w.val < m * regBits p then
    (r ⟨w.val / regBits p, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)⟩).val.testBit
      (w.val % regBits p)
  else false

/-- The vector `|v_d⟩ ⊗ |0⟩_estimate ⊗ |0⟩_work` on the wires of a decoder circuit. -/
noncomputable def decoderCircInput (N : ℕ) (S : Finset (ZMod p)) (β : ℝ) (d : Fin m → ZMod p) :
    EuclideanSpace ℂ (Qubits N) :=
  ∑ r : Fin m → ZMod p, (receivedState S β d r) • ket (receivedBasis p N r)

/-- The estimate register `m b ≤ w < 2 m b` of a basis pattern reads `d` (wire `m b + j b + i` is bit `i` of
`(d j).val`). -/
def estimateReads (p : ℕ) [Fact p.Prime] {N : ℕ} (y : Qubits N) (d : Fin m → ZMod p) : Prop :=
  ∀ w : Fin N, ∀ (j : Fin m) (i : ℕ), i < regBits p → w.val = m * regBits p + j.val * regBits p + i →
    y w = (d j).val.testBit i

open Classical in
/-- **The block error of a decoder circuit** on a uniformly chosen codeword of `C^⊥ = ker Bᵀ`, Proposition 2,
p.15, for the channel with every target set equal to `S`. -/
noncomputable def circBlockError (B : Matrix (Fin m) (Fin n) (ZMod p)) (S : Finset (ZMod p)) (β : ℝ)
    (c : Circ) : ℝ :=
  ((dualCode B).card : ℝ)⁻¹ * ∑ d ∈ dualCode B,
    (1 - ∑ y : Qubits c.wires,
      if estimateReads p y d then ‖act c.unitary (decoderCircInput c.wires S β d) y‖ ^ 2 else 0)

end RegevRecon


