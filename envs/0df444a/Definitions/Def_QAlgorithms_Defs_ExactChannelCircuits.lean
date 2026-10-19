-- Prove2me | Definitions.Def_QAlgorithms_Defs_ExactChannelCircuits
-- name    : QAlgorithms_Defs_ExactChannelCircuits
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:19.712978+00:00
-- url     : https://prove2.me/theorems/894b2acf-e387-491e-82a5-45ebbe8f1bda
-- title:
--   ExactChannelCircuits
-- statement:
--   ExactChannelCircuits
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ExactChannelCircuits.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- Operational helper ChannelCircuit for the source construction. Source: arxiv-2405.06051v6 PDF p.4; arxiv-2405.06051v6 PDF p.11; arxiv-2405.06051v6 PDF p.12; arxiv-2405.06051v6 PDF p.25. -/
structure ChannelCircuit (din dout : ℕ) where
  added : ℕ
  garbage : ℕ
  wireCount : Nat.clog 2 din + added = Nat.clog 2 dout + garbage
  order : Fin (Nat.clog 2 dout + garbage) ≃ Fin (Nat.clog 2 din + added)
  circuit : Circuit oneTwoQubitGateSet (Nat.clog 2 din + added)

/-- Encode input, append specified zero ancillas, conjugate by Circuit.unitary, permute to retained/discarded wire factors and trace discarded wires. Source: arxiv-2405.06051v6 PDF p.4; arxiv-2601.18773v1 PDF p.9. -/
def channelCircuitOutput {din dout : ℕ} (C : ChannelCircuit din dout)
    (X : Matrix (Fin din) (Fin din) ℂ) :
    Matrix (Qubits (Nat.clog 2 dout)) (Qubits (Nat.clog 2 dout)) ℂ :=
  let J := finiteRegisterEmbedding din
  let encoded := withZeroAncillas (J * X * Jᴴ) C.added
  let Y := conjSuperop C.circuit.unitary encoded
  traceRight (Y.submatrix
    (fun p => Fin.append p.1 p.2 ∘ C.order.symm)
    (fun p => Fin.append p.1 p.2 ∘ C.order.symm))

/-- A circuit of arbitrary one- and two-qubit unitaries realizes a channel by appending normalized |0> ancillas, applying its unitary, and discarding named garbage wires. Source: arxiv-2405.06051v6 PDF p.4; arxiv-2405.06051v6 PDF p.11; arxiv-2405.06051v6 PDF p.12; arxiv-2405.06051v6 PDF p.25. -/
def ExactChannelRealization {din dout : ℕ} (Phi : Superop (Fin din) (Fin dout))
    (C : ChannelCircuit din dout) : Prop :=
  0 < din ∧ 0 < dout ∧ ∀ X,
    channelCircuitOutput C X = finiteRegisterEmbedding dout * Phi X * (finiteRegisterEmbedding dout)ᴴ

/-- The minimum total number of arbitrary single- and two-qubit unitary gates implementing T, allowing ancillas polynomial in the number of qubits (p.4). Source: arxiv-2405.06051v6 PDF p.4; arxiv-2405.06051v6 PDF p.12; arxiv-2405.06051v6 PDF p.25. -/
def circuitComplexity {din dout : ℕ} (budget : ℕ) (Phi : Superop (Fin din) (Fin dout)) : ℕ∞ :=
  ⨅ (C : ChannelCircuit din dout) (_ : ExactChannelRealization Phi C ∧ C.added ≤ budget),
    (C.circuit.size : ℕ∞)

/-- Sanity test. Source: arxiv-2405.06051v6 PDF p.4; arxiv-2405.06051v6 PDF p.11; arxiv-2405.06051v6 PDF p.12; arxiv-2405.06051v6 PDF p.25. -/
example {din dout : ℕ} (Phi : Superop (Fin din) (Fin dout)) (budget : ℕ)
    (h : ∀ C : ChannelCircuit din dout, ¬ (ExactChannelRealization Phi C ∧ C.added ≤ budget)) :
    circuitComplexity budget Phi = ⊤ := by
  simp [circuitComplexity, h]

/-- No gates or added wires realize the identity channel, retaining padded output support.
Source: arxiv-2405.06051v6 PDF p.4. -/
example (din : ℕ) (h : 0 < din) :
    ExactChannelRealization (din := din) (dout := din) (fun X => X)
      { added := 0, garbage := 0, wireCount := rfl, order := Equiv.refl _, circuit := [] } := by
  refine ⟨h, h, ?_⟩
  intro X
  ext y z
  have hz : ∀ a : Qubits 0, a = fun _ => false := fun _ => Subsingleton.elim _ _
  have hApp (u : Qubits (Nat.clog 2 din)) :
      (fun i => Fin.addCases u (fun _ : Fin 0 => false) i) = u := by
    change Fin.append u (fun _ : Fin 0 => false) = u
    simpa using Fin.append_right_nil u (fun _ : Fin 0 => false) rfl
  simp [channelCircuitOutput, Circuit.unitary, conjSuperop, withZeroAncillas, traceRight,
    qubitsAppendEquiv, hz, Function.comp_def, Fin.append, hApp]

end QAlgorithms


