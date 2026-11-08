-- Prove2me | Definitions.Def_EntangledPIR_PrivateAgainstA
-- name    : EntangledPIR_PrivateAgainstA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:13:35.349525+00:00
-- url     : https://prove2.me/theorems/36f00f1b-317c-4bc8-a756-f3d12d1cde7e
-- title:
--   Privacy (Definition 2.1), correctness and communication of the honest execution
-- statement:
--   **Definition 2.1.** Fix the public parameters and the database, and let $\varepsilon\ge0$. Protocol 1 is $\varepsilon$-private against A if, for every initial state of the servers, every strategy of A, every round and all indices $x,x'$, with B and the client following the protocol, the views after that round satisfy
--
--   $$D\bigl(\mathrm{View}_{\mathsf A}(x),\mathrm{View}_{\mathsf A}(x')\bigr)\le\varepsilon.$$
--
--   Privacy against B exchanges the roles. Privacy is the guarantee that the state of a malicious server is nearly independent of the index.
--
--   The module also defines the probability that the client outputs $F(x)$ in the honest execution, from the Bell pairs, and the bits sent by the servers and by the client on a branch.
--
--   **Formalization Note** An initial state is any density matrix on the registers of the malicious server, the copies of the honest server, and any finite register that the honest server leaves untouched. The strategy and the state are chosen before the two indices, and one strategy is compared on both.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Definition 2.1, p.11; §2.1, p.10

import Definitions.Def_EntangledPIR_honest
import Definitions.Def_EntangledPIR_execState
import Definitions.Def_DimFreeShadow_traceDistance

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), Definition 2.1,
p.11: privacy, correctness and the honest execution of Protocol 1.
-/

open Matrix
open scoped ComplexOrder

namespace EntangledPIR

section
variable {n m : ℕ} (lam : ℕ) (F : Bits n → Bits m)

/-- The condition of Definition 2.1, p.11, for one round `r`: for every initial state of the servers
and every strategy of A, with B and the client following the protocol, and all indices `x, x′`, the
views after round `r` satisfy `D(View_A(x), View_A(x′)) ≤ ε`.

**Formalization Note.** The initial state is any density matrix on the registers of A and those of the
honest B; `RB0` is any finite register that B leaves untouched, as initial states may be entangled
with anything. The strategy and the state are fixed before the indices, and one strategy is compared on
both indices. -/
def RoundPrivateAgainstA (r : ℕ) (ε : ℝ) : Prop :=
  ∀ (SA : Strategy (msgBound n m lam)) (RB0 : Type) [Fintype RB0] [DecidableEq RB0]
    (ρ₀ : Matrix (SA.Reg 0 × (Copies n m lam × RB0)) (SA.Reg 0 × (Copies n m lam × RB0)) ℂ),
    ρ₀.PosSemidef → ρ₀.trace = 1 → ∀ x x' : Bits n,
      DimFreeShadow.traceDistance
        (viewA (n := n) (m := m) (lam := lam) SA (honestB lam F RB0) ρ₀ r x)
        (viewA (n := n) (m := m) (lam := lam) SA (honestB lam F RB0) ρ₀ r x') ≤ ε

/-- The same with the roles of A and B exchanged. -/
def RoundPrivateAgainstB (r : ℕ) (ε : ℝ) : Prop :=
  ∀ (SB : Strategy (msgBound n m lam)) (RA0 : Type) [Fintype RA0] [DecidableEq RA0]
    (ρ₀ : Matrix ((Copies n m lam × RA0) × SB.Reg 0) ((Copies n m lam × RA0) × SB.Reg 0) ℂ),
    ρ₀.PosSemidef → ρ₀.trace = 1 → ∀ x x' : Bits n,
      DimFreeShadow.traceDistance
        (viewB (n := n) (m := m) (lam := lam) (honestA lam F RA0) SB ρ₀ r x)
        (viewB (n := n) (m := m) (lam := lam) (honestA lam F RA0) SB ρ₀ r x') ≤ ε

/-- **Definition 2.1 (Privacy)**, p.11: Protocol 1 is `ε`-private against A for the database `F`: the
condition holds at every round of the schedule. -/
def PrivateAgainstA (ε : ℝ) : Prop :=
  ∀ r, r ≤ numRounds → RoundPrivateAgainstA lam F r ε

/-- **Definition 2.1 (Privacy)**, p.11, with the roles of A and B exchanged. -/
def PrivateAgainstB (ε : ℝ) : Prop :=
  ∀ r, r ≤ numRounds → RoundPrivateAgainstB lam F r ε

/-- The initial state of the honest execution, p.10: the density matrix of the Bell pairs of Protocol 1.
Each server's extra register is trivial. -/
noncomputable def bellState (n m lam : ℕ) :
    Matrix ((Copies n m lam × Unit) × (Copies n m lam × Unit))
      ((Copies n m lam × Unit) × (Copies n m lam × Unit)) ℂ :=
  Matrix.vecMulVec (fun p => bellVector n m lam (p.1.1, p.2.1))
    (star fun p => bellVector n m lam (p.1.1, p.2.1))

/-- The subnormalized state of the honest execution after `r` rounds on the branch `τ`, for index
list `x` and random string `tape`, p.10. -/
noncomputable def honestState (x tape : List Bool) (r : ℕ)
    (τ : Transcript (msgBound n m lam) r) :
    Matrix ((Copies n m lam × Unit) × (Copies n m lam × Unit))
      ((Copies n m lam × Unit) × (Copies n m lam × Unit)) ℂ :=
  execState n m lam x tape (honestA lam F Unit) (honestB lam F Unit) (bellState n m lam) r τ

/-- The probability that the client outputs the record `F(x)` in the honest execution, p.10, over the
random string and all measurement outcomes. The client's output is read after the last round. -/
noncomputable def successProb (x : Bits n) : ℝ :=
  ((2 : ℝ) ^ tapeLen n lam)⁻¹ * ∑ tape : Bits (tapeLen n lam),
    ∑ τ : Transcript (msgBound n m lam) numRounds,
      if (clientAt n m lam (List.ofFn x) (List.ofFn tape) (Transcript.toSrv τ)).out =
          some (List.ofFn (F x)) then
        (Matrix.trace (honestState lam F (List.ofFn x) (List.ofFn tape) numRounds τ)).re
      else 0

end

/-- The bits sent by the servers in a run with server messages `τ` (p.10, "the answer length"). -/
def serverBits {L r : ℕ} (τ : Transcript L r) : ℕ :=
  ∑ s, ((τ s).1.1.length + (τ s).2.1.length)

/-- The bits sent by the client to the two servers in a run with server messages `τ`. -/
noncomputable def clientBits (n m lam : ℕ) (x tape : List Bool) {L r : ℕ} (τ : Transcript L r) : ℕ :=
  ∑ s : Fin r,
    ((clientAt n m lam x tape ((Transcript.toSrv τ).take s)).toA.length +
      (clientAt n m lam x tape ((Transcript.toSrv τ).take s)).toB.length)

/-- The communication of a run, p.10: the classical bits sent in both directions. -/
noncomputable def commBits (n m lam : ℕ) (x tape : List Bool) {L r : ℕ} (τ : Transcript L r) : ℕ :=
  serverBits τ + clientBits n m lam x tape τ

end EntangledPIR


