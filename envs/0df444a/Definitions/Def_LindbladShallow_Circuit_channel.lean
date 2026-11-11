-- Prove2me | Definitions.Def_LindbladShallow_Circuit_channel
-- name    : LindbladShallow_Circuit_channel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:20:53.582225+00:00
-- url     : https://prove2.me/theorems/5149a2a9-ec2a-4a9a-af91-4d9fc5c406a7
-- title:
--   The channel of a segmented circuit description
-- statement:
--   Each segment $s$ acts on the system qubits and its auxiliary qubits. Its unitary $U_s$ is the product of its layers (in order), each the product of its gates. Its channel is
--   $$\Psi_s(\rho)=\mathrm{Tr}_{\mathrm{aux}}\big[U_s(\rho\otimes|0\cdots0\rangle\langle0\cdots0|_{\mathrm{aux}})U_s^\dagger\big],$$
--   and the circuit implements $\widetilde\Phi=\Psi_{s_{\mathrm{last}}}\circ\cdots\circ\Psi_{s_{\mathrm{first}}}$.
--
--   This is Eq. (47): auxiliaries are initialized afresh at the start of each segment and discarded at its end.
--
--   **Formalization Note** Gates act on the wire found at their position; a well-formed circuit always finds one.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Eq. (47), p.50; p.10

import Mathlib
import Definitions.Def_LindbladShallow_Circuit

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- The wires of segment `s`: the system qubits `(j, k)` and the segment's auxiliary qubits. -/
abbrev SegWire {P : Params} (I : Instance P) (s : Segment P.D) :=
  (Fin I.n × Fin P.d0) ⊕ Fin s.aux.length

/-- The position of a wire. -/
def SegWire.pos {P : Params} {I : Instance P} (c : Circuit P) {s : Segment P.D} :
    SegWire I s → (Fin P.D → ℤ)
  | .inl q => sysPos I c q.1 q.2
  | .inr a => s.aux.get a

/-- The wire at a position, if any. -/
noncomputable def wireAt {P : Params} (I : Instance P) (c : Circuit P) (s : Segment P.D)
    (p : Fin P.D → ℤ) : Option (SegWire I s) :=
  open Classical in
  if h : ∃ w : SegWire I s, w.pos c = p then some h.choose else none

/-- `|0⟩ ↦ 0`, `|1⟩ ↦ 1`. -/
def bitIdx (b : Bool) : Fin 2 := if b then 1 else 0

/-- A one-qubit matrix acting on wire `w` of a register with basis `W → Bool`, identity elsewhere. -/
noncomputable def oneOn {W : Type*} [DecidableEq W] (G : Matrix (Fin 2) (Fin 2) ℂ) (w : W) :
    Matrix (W → Bool) (W → Bool) ℂ :=
  open Classical in
  Matrix.of fun σ' σ => if ∀ v, v ≠ w → σ' v = σ v then G (bitIdx (σ' w)) (bitIdx (σ w)) else 0

/-- The ordered CNOT with control wire `a` and target wire `b`: `|x⟩ ↦ |x with x_b ↦ x_b ⊕ x_a⟩`. -/
noncomputable def cxOn {W : Type*} [DecidableEq W] (a b : W) : Matrix (W → Bool) (W → Bool) ℂ :=
  open Classical in
  Matrix.of fun σ' σ => if σ' = Function.update σ b (xor (σ b) (σ a)) then 1 else 0

/-- The unitary of one gate in segment `s` (identity if a position is not a wire, which a
well-formed circuit excludes). -/
noncomputable def gateMat {P : Params} (I : Instance P) (c : Circuit P) (s : Segment P.D) :
    Gate P.D → Matrix (SegWire I s → Bool) (SegWire I s → Bool) ℂ
  | .one g p =>
    match wireAt I c s p with
    | some w => oneOn g.mat w
    | none => 1
  | .cx a b =>
    match wireAt I c s a, wireAt I c s b with
    | some wa, some wb => cxOn wa wb
    | _, _ => 1

/-- The unitary of a segment: the product of its layers in order, each layer the product of its
gates (which act on disjoint wires and commute), head first. -/
noncomputable def segUnitary {P : Params} (I : Instance P) (c : Circuit P) (s : Segment P.D) :
    Matrix (SegWire I s → Bool) (SegWire I s → Bool) ℂ :=
  orderedProd (s.layers.map fun L => orderedProd (L.map (gateMat I c s)))

/-- The segment unitary written on system ⊗ auxiliaries, `(W → Bool) ≃ Sys × (aux → Bool)`. -/
noncomputable def segUnitarySA {P : Params} (I : Instance P) (c : Circuit P) (s : Segment P.D) :
    Matrix (Sys I × (Fin s.aux.length → Bool)) (Sys I × (Fin s.aux.length → Bool)) ℂ :=
  Matrix.reindex (Equiv.sumArrowEquivProdArrow _ _ _) (Equiv.sumArrowEquivProdArrow _ _ _)
    (segUnitary I c s)

/-- The channel of one segment (arXiv:2610.05362, Eq. (47), p.50):
`Ψ_s(ρ) := Tr_aux[ U_s (ρ ⊗ |0⟩⟨0|_aux) U_s† ]` — fresh auxiliaries in `|0…0⟩`, the segment unitary,
then the auxiliaries are discarded. -/
noncomputable def segChannel {P : Params} (I : Instance P) (c : Circuit P) (s : Segment P.D) :
    QAlgorithms.Superop (Sys I) (Sys I) :=
  isoChannel (segUnitarySA I c s * vacIso (fun _ => false))

/-- The channel `Φ̃` implemented by a circuit description: the composition of its segment channels,
first segment first (arXiv:2610.05362, Eq. (47), p.50: `Φ̃_T := Ψ̂_τ^{N₀}`; the model allows
distinct segments). -/
noncomputable def Circuit.channel {P : Params} (I : Instance P) (c : Circuit P) :
    QAlgorithms.Superop (Sys I) (Sys I) :=
  c.segs.foldl (fun Φ s => segChannel I c s ∘ Φ) id

end LindbladShallow


