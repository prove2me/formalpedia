-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
-- name    : QMAPerfectCompleteness_Main_BlockEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:45.304246+00:00
-- url     : https://prove2.me/theorems/7f70144c-d9d5-4c08-a7ad-e1dd0683730f
-- title:
--   The gadgets $W_T$, $W_{R_z}$, the unitary $U_{z,a,b}$ of (7), and valid certificates
-- statement:
--   Fix a verifier $V$ with output qubit, and add a flag qubit $f$ and a $k$-qubit index register $J$ with $M=2^k$ basis states. Let $S|t\rangle=|t+1 \bmod (\ell+1)\rangle$ be the cyclic shift on the clock. The gadget $W_T$ applies $V$, flips $f$ if the clock is below $\ell$ and the output qubit is $1$, applies $V^\dagger$, and then applies $S$. The gadget $W_{R_z}$ flips $f$ if the history register is in state $|\ell\rangle\otimes|z\rangle$, and then applies $S$.
--
--   For $z\in\{0,1\}^m$ and nonnegative integers $a,b$ with $3a+b\le M$,
--
--   $$
--   U_{z,a,b}=(H^{\otimes k}\otimes I)\Big(\sum_{j=0}^{M-1}|j\rangle\langle j|\otimes U_j\Big)(H^{\otimes k}\otimes I),
--   \qquad
--   U_j=\begin{cases}X_f& j<a,\\ -W_T& a\le j<3a,\\ -W_{R_z}& 3a\le j<3a+b,\\ I& j\ge 3a+b.\end{cases}
--   $$
--
--   Its ancilla register is $Z=JYf$, initialized to $|\eta\rangle=|0\rangle_J|0\rangle_Y|1\rangle_f$.
--
--   For a verifier over $\mathcal G_2$ with $g$ gates $H\otimes H$ and $h=2g$, let $k$ be the least even integer with $k\ge(h+1)\ell+4$. A **valid certificate** is a triple $(z,a,b)$ with $z\in\{0,1\}^m$ and positive integers $a,b$ representable by $k$ bits satisfying
--
--   $$
--   M/8\le a\le M/4,\qquad 2b\le a.
--   $$
--
--   **Formalization Note** The index basis is `Fin (2^k)`, and bit $i$ of $j$ is qubit $i$. The matrix `zEmbed` with flag value `true` is $|\eta\rangle\otimes I$, and the adjoint of `zEmbed` with flag value `false` is $\langle 0|_Z\otimes I$. Validity is stated without division, as $M\le 8a$ and $4a\le M$. The function `blockUnitary` is total in $a,b$; the case $3a+b\le M$ of the source is the one valid certificates give.
-- source:
--   Sabee Grewal, Dorian Rudolph, QMA has perfect completeness, STOC 2027 submission #490 (October 2026), §3.3, pp. 9–10, Figure 2, Definition 3.5, Eq. (7), valid certificate p. 10

import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic

open Matrix
open scoped Kronecker

/-!
# The gadgets `W_T`, `W_{R_z}`, the block unitary `U_{z,a,b}` and valid certificates

Sabee Grewal, Dorian Rudolph, *QMA has perfect completeness*, STOC 2027 submission #490
(October 2026), §3.3, pp. 9–10, Figure 2, Definition 3.5, Eq. (7).
-/

namespace QMAPerfectCompleteness.Main

/-- `H^{⊗k}` on the index register, whose basis `Fin (2^k)` reads bit `i` of `j` as qubit `i`:
`⟨j'|H^{⊗k}|j⟩ = (-1)^{#{i < k : j'_i = j_i = 1}} / 2^{k/2}`. -/
noncomputable def indexHadamard (k : ℕ) : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ :=
  Matrix.of fun j' j =>
    (-1) ^ ((Finset.range k).filter fun i => (j' : ℕ).testBit i && (j : ℕ).testBit i).card /
      ((Real.sqrt 2 : ℝ) : ℂ) ^ k

namespace Verifier

variable {G : GateSet} (V : Verifier G)

/-- The basis of clock, proof and ancilla wires, and flag `f`. -/
abbrev Body := Clock V.proofQubits × V.Wire × Bool

/-- The basis of the `k`-qubit index register `J`, with `M = 2^k` values, and the body. -/
abbrev BlockReg (k : ℕ) := Fin (2 ^ k) × V.Body

/-- The operator flipping the flag exactly on the basis states selected by `P`. -/
def flipIf (P : Clock V.proofQubits → V.Wire → Bool) : Matrix V.Body V.Body ℂ :=
  Matrix.of fun y x => if y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ y.2.2 = xor x.2.2 (P x.1 x.2.1) then 1 else 0

/-- The cyclic clock shift `S|t⟩ = |t + 1 mod (ℓ + 1)⟩`, acting on the body. -/
def shift : Matrix V.Body V.Body ℂ :=
  (Matrix.of fun t' t : Clock V.proofQubits => if t' = t + 1 then (1 : ℂ) else 0) ⊗ₖ
    (1 : Matrix (V.Wire × Bool) (V.Wire × Bool) ℂ)

/-- A matrix on proof and ancilla wires, acting on the body. -/
def onWires (M : Matrix V.Wire V.Wire ℂ) : Matrix V.Body V.Body ℂ :=
  (1 : Matrix (Clock V.proofQubits) (Clock V.proofQubits) ℂ) ⊗ₖ
    (M ⊗ₖ (1 : Matrix Bool Bool ℂ))

/-- `X_f`: flip the flag unconditionally. -/
def flagX : Matrix V.Body V.Body ℂ := V.flipIf fun _ _ => true

/-- `W_T` (Figure 2(a)): apply `V`, flip `f` if the clock is below `ℓ` and the output qubit is `1`,
apply `V†`, then the clock shift `S`. -/
noncomputable def gadgetT : Matrix V.Body V.Body ℂ :=
  V.shift * V.onWires V.unitaryᴴ *
    V.flipIf (fun t w => decide ((t : ℕ) < ell V.proofQubits) && w V.output) * V.onWires V.unitary

/-- `W_{R_z}` (Figure 2(b)): flip `f` if the history register is in state `|ℓ⟩ ⊗ |z⟩`, then
apply `S`. -/
def gadgetR (z : V.Proof) : Matrix V.Body V.Body ℂ :=
  V.shift * V.flipIf fun t w => decide ((t : ℕ) = ell V.proofQubits) && decide (V.proofPart w = z)

/-- The branch `U_j` of Eq. (7). -/
noncomputable def branch (z : V.Proof) (a b j : ℕ) : Matrix V.Body V.Body ℂ :=
  if j < a then V.flagX
  else if j < 3 * a then -V.gadgetT
  else if j < 3 * a + b then -V.gadgetR z
  else 1

/-- `U_{z,a,b}`, Eq. (7): `(H^{⊗k} ⊗ I)(∑_{j<M} |j⟩⟨j| ⊗ U_j)(H^{⊗k} ⊗ I)`. Definition 3.5 assumes
nonnegative integers `a, b` with `3a + b ≤ M = 2^k`; a valid certificate has this property. -/
noncomputable def blockUnitary (k : ℕ) (z : V.Proof) (a b : ℕ) :
    Matrix (V.BlockReg k) (V.BlockReg k) ℂ :=
  (indexHadamard k ⊗ₖ (1 : Matrix V.Body V.Body ℂ)) *
    (∑ j : Fin (2 ^ k), Matrix.single j j (1 : ℂ) ⊗ₖ V.branch z a b j) *
    (indexHadamard k ⊗ₖ (1 : Matrix V.Body V.Body ℂ))

/-- The isometry from the history space into the full register with `Z = J Y f` in the state
`|0⟩_J |0⟩_Y |f⟩_f`. With `f = true` this is `|η⟩ ⊗ I`; the adjoint of the case `f = false` is
`⟨0|_Z ⊗ I`. -/
def zEmbed (k : ℕ) (f : Bool) : Matrix (V.BlockReg k) (History V) ℂ :=
  Matrix.of fun y x =>
    if y.1 = 0 ∧ y.2.1 = x.1 ∧ y.2.2.1 = V.initialState x.2 ∧ y.2.2.2 = f then 1 else 0

end Verifier

/-- The least even integer `k` with `k ≥ (h + 1)ℓ + 4` (p. 10), `h = 2g`. -/
def indexQubits (V : Verifier gatesG2) : ℕ :=
  let n := (2 * hhCount V + 1) * ell V.proofQubits + 4
  n + n % 2

/-- A valid certificate (p. 10): `z ∈ {0,1}^m` and positive integers `a, b` representable by `k`
bits with `M/8 ≤ a ≤ M/4` and `2b ≤ a`, where `M = 2^k`. Arithmetic is exact, without rounding. -/
def IsValidCertificate (V : Verifier gatesG2) (a b : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ a < 2 ^ indexQubits V ∧ b < 2 ^ indexQubits V ∧
    2 ^ indexQubits V ≤ 8 * a ∧ 4 * a ≤ 2 ^ indexQubits V ∧ 2 * b ≤ a

end QMAPerfectCompleteness.Main


