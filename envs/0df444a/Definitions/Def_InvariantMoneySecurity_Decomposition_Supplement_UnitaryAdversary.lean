-- Prove2me | Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_UnitaryAdversary
-- name    : InvariantMoneySecurity_Decomposition_Supplement_UnitaryAdversary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:31:46.69503+00:00
-- url     : https://prove2.me/theorems/061ca6db-5747-44fc-a444-29630d99053c
-- title:
--   Adversaries as block unitaries, their winning probability, and the adversary $F^*$
-- statement:
--   In §6.4 an adversary $A$ for the unforgeability game is accessed only through a unitary
--   $$U_A=\sum_{p'}|p'\rangle\langle p'|\otimes U_{A,p'}$$
--   on a serial-number register, an $n$-qubit challenge register $R_1$ and further registers; it is block diagonal in the serial number. The further registers have $n+e(n)$ qubits, the first $n$ of which form the second output register $R_2$. No circuit, uniformity or efficiency is required.
--
--   Its **winning probability** is the probability of Definition 2.4's game: with $p$ drawn by the mint, apply $U_A$ to $|p\rangle\otimes|\$_p\rangle\otimes|0\rangle$, take the reduced state $\rho_{12}$ of $(R_1,R_2)$, and run the actual finite-round verifier $\mathrm{Ver}(p,\cdot)$ on both registers;
--   $$\mathrm{win}_A(n)=\mathbb E_p\big[\Pr[\mathrm{Ver}(p,\rho_1)\text{ and }\mathrm{Ver}(p,\rho_2)\text{ both accept}]\big],$$
--   the joint Born probability of the two accepting effects. For a quantum polynomial-time forger this is the published winning probability.
--
--   Given unitaries $\mathrm{Syn}_{p'}$ on one $n$-qubit register, the adversary $F^*$ is implemented by
--   $$U^*=\sum_{p'}|p'\rangle\langle p'|\otimes\Big(\Pi_1^{(p')}\otimes\mathrm{Syn}_{p'}+\big(I-\Pi_1^{(p')}\big)\otimes I\Big)$$
--   on (serial number, challenge, $R_2$), extended by the identity on the remaining $e(n)$ qubits. Here $\Pi_1^{(p')}$ is the projector onto the span of all orbit states with serial number $p'$ (the published accepted projector).
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), p. 9, Definition 2.4; p. 29, Definition 6.8 and Theorem 6.9

import Definitions.Def_InvariantMoneySecurity_Decomposition_MintVerifier
set_option autoImplicit false
noncomputable section

namespace InvariantMoneySecurity.Decomposition.Supplement

open InvariantMoneySecurity.Decomposition

/-! Register layout of an adversary unitary on `s + n + (n + e)` qubits: the serial-number
register (`s` qubits), the challenge register `R₁` (`n` qubits), and further registers whose
first `n` qubits are the second output register `R₂` and whose last `e` qubits are workspace. -/

/-- Serial-number register. -/
def advSerial {s n e : ℕ} (a : Bits (s + n + (n + e))) : Bits s :=
  fun j => a (Fin.castAdd (n + e) (Fin.castAdd n j))

/-- Challenge register `R₁`. -/
def advChallenge {s n e : ℕ} (a : Bits (s + n + (n + e))) : Bits n :=
  fun j => a (Fin.castAdd (n + e) (Fin.natAdd s j))

/-- Second output register `R₂`, the first `n` further qubits. -/
def advSecond {s n e : ℕ} (a : Bits (s + n + (n + e))) : Bits n :=
  fun j => a (Fin.natAdd (s + n) (Fin.castAdd e j))

/-- Remaining workspace qubits. -/
def advWork {s n e : ℕ} (a : Bits (s + n + (n + e))) : Bits e :=
  fun j => a (Fin.natAdd (s + n) (Fin.natAdd n j))

/-- Number of qubits an adversary unitary acts on at security parameter `n`. -/
abbrev advWidth (D : Scheme) (e : ℕ → ℕ) (n : ℕ) : ℕ := (D.data n).serialBits + n + (n + e n)

/-- Definition 6.8: an adversary is accessed only through a unitary
`U_A = Σ_{p'} |p'⟩⟨p'| ⊗ U_{A,p'}` — unitary, and block diagonal in the serial-number register.
No circuit, uniformity or efficiency is required. -/
def IsAdversary (D : Scheme) (e : ℕ → ℕ)
    (U : ∀ n, Matrix (Bits (advWidth D e n)) (Bits (advWidth D e n)) ℂ) : Prop :=
  ∀ n, (U n).conjTranspose * U n = 1 ∧
    ∀ a b, advSerial a ≠ advSerial b → U n a b = 0

/-- The game's input `|p⟩ ⊗ |$_p⟩ ⊗ |0⟩` (serial, challenge holding the banknote, all further
registers zero). -/
def gameInput (D : Scheme) (e : ℕ → ℕ) (n : ℕ) (p : Bits (D.data n).serialBits) :
    Bits (advWidth D e n) → ℂ :=
  fun a => (if advSerial a = p then 1 else 0) * (D.data n).banknote p (advChallenge a) *
    (if (advSecond a = fun _ => false) ∧ (advWork a = fun _ => false) then 1 else 0)

/-- The reduced state on `(R₁, R₂)` of `U (|p⟩⟨p| ⊗ |$_p⟩⟨$_p| ⊗ |0⟩⟨0|) U†`, with `R₁` the
first `n` qubits of the result. -/
def gameOutput (D : Scheme) (e : ℕ → ℕ)
    (U : ∀ n, Matrix (Bits (advWidth D e n)) (Bits (advWidth D e n)) ℂ) (n : ℕ)
    (p : Bits (D.data n).serialBits) : Matrix (Bits (n + n)) (Bits (n + n)) ℂ :=
  let v := (U n).mulVec (gameInput D e n p)
  fun c d => ∑ a, ∑ b,
    if advSerial a = advSerial b ∧ advWork a = advWork b ∧
        appendBits (advChallenge a) (advSecond a) = c ∧
        appendBits (advChallenge b) (advSecond b) = d
    then v a * star (v b) else 0

/-- Definition 2.4's winning probability for an arbitrary (possibly inefficient) adversary
unitary: both output registers accepted by the actual finite-round verifier at `p`, averaged over
the actual mint law. -/
def advWin (D : Scheme) (e : ℕ → ℕ)
    (U : ∀ n, Matrix (Bits (advWidth D e n)) (Bits (advWidth D e n)) ℂ) (n : ℕ) : ℝ :=
  (D.data n).mintAverage fun p _ =>
    (D.data n).jointAcceptance p (D.rounds n) (gameOutput D e U n p)

/-- Theorem 6.9's adversary `F*`:
`U* = Σ_{p'} |p'⟩⟨p'| ⊗ (Π₁^{(p')} ⊗ Syn_{p'} + (I − Π₁^{(p')}) ⊗ I)` on (serial, challenge,
second output register), extended by the identity on the workspace. `Π₁^{(p')}` is the published
`acceptedProjector p'` (all orbit states with serial `p'`). -/
def starUnitary (D : Scheme) (e : ℕ → ℕ)
    (Syn : ∀ n, Bits (D.data n).serialBits → Matrix (Bits n) (Bits n) ℂ) (n : ℕ) :
    Matrix (Bits (advWidth D e n)) (Bits (advWidth D e n)) ℂ :=
  fun a b =>
    if advSerial a = advSerial b ∧ advWork a = advWork b then
      (D.data n).acceptedProjector (advSerial b) (advChallenge a) (advChallenge b) *
          Syn n (advSerial b) (advSecond a) (advSecond b) +
        (1 - (D.data n).acceptedProjector (advSerial b)) (advChallenge a) (advChallenge b) *
          (if advSecond a = advSecond b then 1 else 0)
    else 0

end InvariantMoneySecurity.Decomposition.Supplement


