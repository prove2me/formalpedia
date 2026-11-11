-- Prove2me | Definitions.Def_LindbladShallow_routing
-- name    : LindbladShallow_routing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:21:58.204743+00:00
-- url     : https://prove2.me/theorems/06dbbd87-6571-40e8-a55b-6ce5681e502f
-- title:
--   Host circuits and the grid graph for routing
-- statement:
--   The **grid graph** of $\mathbb Z^D$ joins positions at $\ell^1$ distance $1$. A **host** is a finite set of positions, one qubit each. A host circuit is a list of gates, each an arbitrary one-qubit matrix at a position or an arbitrary two-qubit matrix on an ordered pair of positions; its unitary on the host register is the ordered product, each gate tensored with the identity on the other wires.
--
--   These are the objects of Lemma 5.8.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), §5.6, p.48; Eq. (68), p.70

import Mathlib
import Definitions.Def_LindbladShallow_Circuit
import Definitions.Def_LindbladShallow_Circuit_channel

open scoped Matrix

namespace LindbladShallow

/-- The grid graph of `ℤ^D`: positions at ℓ¹ distance `1` are adjacent (arXiv:2610.05362, held
version sha256 8f4637ef…, §5.6, p.48; nearest neighbours of the lattice refinement). -/
def gridGraph (D : ℕ) : SimpleGraph (Fin D → ℤ) := SimpleGraph.fromRel fun p q => l1dist p q = 1

/-- A gate of a host circuit: an arbitrary one-qubit matrix at a position, or an arbitrary
two-qubit matrix on an ordered pair of positions (Lemma 5.8, p.48). The two-qubit matrix is
indexed by `(first qubit, second qubit)`. -/
inductive HGate (D : ℕ)
  | one (U : Matrix (Fin 2) (Fin 2) ℂ) (p : Fin D → ℤ)
  | two (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (p q : Fin D → ℤ)

/-- The positions a host gate acts on. -/
def HGate.wires {D : ℕ} : HGate D → List (Fin D → ℤ)
  | .one _ p => [p]
  | .two _ p q => [p, q]

/-- The matrix of the ordered CNOT `CX|a, b⟩ = |a, a ⊕ b⟩` (Eq. (68), p.70). -/
def cxMat : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => if p = (q.1, q.1 + q.2) then 1 else 0

/-- A two-qubit matrix acting on host wires `a ≠ b` (first qubit `a`), identity elsewhere. -/
noncomputable def twoOn {W : Type*} [DecidableEq W] (G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (a b : W) : Matrix (W → Bool) (W → Bool) ℂ :=
  open Classical in
  Matrix.of fun σ' σ => if ∀ v, v ≠ a → v ≠ b → σ' v = σ v then
    G (bitIdx (σ' a), bitIdx (σ' b)) (bitIdx (σ a), bitIdx (σ b)) else 0

/-- The unitary of a host gate on the host register (basis `host → Bool`); identity if a position
is outside the host. -/
noncomputable def HGate.mat {D : ℕ} (Hs : Finset (Fin D → ℤ)) :
    HGate D → Matrix ({x // x ∈ Hs} → Bool) ({x // x ∈ Hs} → Bool) ℂ
  | .one U p => if h : p ∈ Hs then oneOn U ⟨p, h⟩ else 1
  | .two U p q => if h : p ∈ Hs ∧ q ∈ Hs then twoOn U ⟨p, h.1⟩ ⟨q, h.2⟩ else 1

/-- The unitary of a gate sequence, head first. -/
noncomputable def hostU {D : ℕ} (Hs : Finset (Fin D → ℤ)) (gs : List (HGate D)) :
    Matrix ({x // x ∈ Hs} → Bool) ({x // x ∈ Hs} → Bool) ℂ :=
  orderedProd (gs.map (HGate.mat Hs))

end LindbladShallow


