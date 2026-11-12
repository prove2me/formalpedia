-- Prove2me | Definitions.Def_TorchFire_Model_basisMat
-- name    : TorchFire_Model_basisMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:56.873271+00:00
-- url     : https://prove2.me/theorems/101a772e-dcdc-451e-87b9-48c8df14604a
-- title:
--   Reversible classical gates, Hadamard transforms and controlled gates as matrices
-- statement:
--   Gate-level building blocks for the explicit oracle circuits of the paper.
--
--   1. For a map $g$ on basis labels, $\mathrm{basisMat}(g)$ sends $|s\rangle$ to $|g(s)\rangle$. For a bijection this is the permutation unitary of a reversible classical gate (an XOR oracle query, a coherent copy, a controlled swap); for an injection it is the isometry that appends fresh registers in a fixed basis state.
--   2. $\mathrm{liftOn}$ applies an operator $M$ to one register of a composite system, as $M\otimes I$ on the remaining registers ("each operation acts as the identity on registers not listed", p.81).
--   3. $\mathrm{ctrlOn}$ is a classically controlled gate in coherent form: $M$ where a predicate on unchanged control registers holds, the identity elsewhere (the deferred-measurement form of Fact 3.1).
--   4. The Hadamard transform $H^{\otimes m}$ with $\langle x|H^{\otimes m}|y\rangle = 2^{-m/2}(-1)^{x\cdot y}$, and its application to one register.
--   5. The XOR update of a register by a function of the other registers, $|x,z\rangle\mapsto|x,z\oplus f(x)\rangle$.
--
--   Every honest procedure of the mission (Constructions 4.6, 4.7, 4.22, 7.4, the tag circuit (95), the affine query (97)) is a product of these gates.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), §3 p.17 (oracle unitaries, linearity), Fact 3.1 p.18; App. A.1 p.81

import Mathlib
import Definitions.Def_TorchFire_Model_Bits

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix

namespace TorchFire.Model

/-- **The matrix of a classical map on basis states.** `basisMat g` sends the basis vector `|s⟩` to
`|g s⟩`: its entry at `(s', s)` is `1` if `s' = g s` and `0` otherwise. For a bijection `g` it is the
permutation unitary of a reversible classical gate (an XOR oracle query, a CNOT copy, a controlled
swap); for an injection it is the isometry appending fresh registers in a fixed basis state
(the map `J` of (64) appending `|0⟩_W`).

Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593 (held
version, sha256 4e43d2f2…afd593), §3, p.17 ("The action on arbitrary superposition of states is
determined by linearity") and Fact 3.1, p.18 (reversible computation). -/
def basisMat {S T : Type} [DecidableEq T] (g : S → T) : Matrix T S ℂ :=
  Matrix.of fun t s => if t = g s then 1 else 0

/-- **A gate on a sub-register.** If `view : S → A × B` is a bijection exhibiting the state space
`S` as a register `A` together with the remaining registers `B`, then `liftOn view M` is the
operator `M ⊗ I_B` on `S` ("Each operation acts as the identity on registers not listed", p.81). -/
def liftOn {S A B : Type} [DecidableEq B] (view : S → A × B) (M : Matrix A A ℂ) : Matrix S S ℂ :=
  Matrix.of fun s' s => if (view s').2 = (view s).2 then M (view s').1 (view s).1 else 0

/-- **A classically controlled gate**, coherently: `M` where the predicate `ctrl` (on control
registers that `M` does not change) holds, and the identity elsewhere. This is the Fact 3.1 (p.18)
form of "if the measured value satisfies `ctrl`, apply `M`". -/
def ctrlOn {S : Type} [DecidableEq S] (ctrl : S → Prop) [DecidablePred ctrl]
    (M : Matrix S S ℂ) : Matrix S S ℂ :=
  Matrix.of fun s' s => if ctrl s then M s' s else if s' = s then 1 else 0

/-- **The Hadamard transform `H^{⊗m}`** on an `m`-qubit register:
`⟨x|H^{⊗m}|y⟩ = 2^{−m/2} (−1)^{x·y}` (Construction 4.6, p.20; Lemma 4.8, p.21). -/
noncomputable def hadamard (m : ℕ) : Matrix (Bits m) (Bits m) ℂ :=
  Matrix.of fun x y =>
    (((Real.sqrt 2 : ℝ) : ℂ) ^ m)⁻¹ * (if (∑ i, x i * y i) = 0 then 1 else -1)

/-- `H^{⊗m}` applied to the register selected by `view` (the identity on the other registers). -/
noncomputable def hadOn {S B : Type} [DecidableEq B] {m : ℕ} (view : S → Bits m × B) :
    Matrix S S ℂ :=
  liftOn view (hadamard m)

/-- **The XOR update of a register** by a function of the other registers: the basis map
`s ↦ s` with the register `get` replaced by `get s + f s`, written back by `set`. With `f` not
depending on that register this is an involution, i.e. the unitary `|x, z⟩ ↦ |x, z ⊕ f(x)⟩` of an
oracle query or of a coherent classical computation (p.17, Fact 3.1). -/
def xorInto {S κ : Type} [DecidableEq S] [Add κ] (get : S → κ) (set : S → κ → S)
    (f : S → κ) : Matrix S S ℂ :=
  basisMat fun s => set s (get s + f s)

end TorchFire.Model


