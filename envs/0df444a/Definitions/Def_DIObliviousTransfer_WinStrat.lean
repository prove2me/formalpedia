-- Prove2me | Definitions.Def_DIObliviousTransfer_WinStrat
-- name    : DIObliviousTransfer_WinStrat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:03:17.768535+00:00
-- url     : https://prove2.me/theorems/6df9b6c4-340d-454d-9648-c93598b92ce4
-- title:
--   Two-laboratory leakage windows and their cost
-- statement:
--   A **window strategy** describes the communication between two laboratories, each holding a port of $P$ qubits and a private register, next to an untouched reference. It runs for at most $T$ steps. At each step the active laboratory applies an instrument whose outcome is a control symbol and a classical string. The control symbol gives the classical length, the quantum length, and which side acts next (or stop).
--
--   A control symbol is either **scheduled** (fixed in advance and free) or **adaptive**. The classical message is the first $\ell_c$ bits of the string. The quantum message is the first $\ell_q$ port qubits of the sender, moved into the receiver's port; the receiver's old content is discarded and the sender's port is reset to $|0\rangle$.
--
--   A branch's **classical cost** is $\sum_t\ell_{c,t}+\sum_{\text{adaptive }t}|\mathrm{enc}(c_t)|$, where $\mathrm{enc}$ is Elias-$\gamma$ on each field plus two bits. Its **quantum cost** is $\sum_t\ell_{q,t}$. A strategy has **no communication** if all its control symbols are scheduled with zero lengths.
--
--   **Formalization Note** This is decision D5 for Definition 3. Instruments are Kraus families with a separate completeness condition.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Definition 3, pp.16–17; Lemma 3, p.15

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_DIObliviousTransfer_pGuess
import Definitions.Def_DIObliviousTransfer_Negligible

namespace DIObliviousTransfer

open Matrix QAlgorithms
open scoped Kronecker ComplexOrder

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), Definition 3
(pp.16–17) and Lemma 3 (p.15): bounded interactive communication between two laboratories
within one window, and its accounting.

"From the instant the first Magic Square input is supplied until all outputs in the complete block
batch have been collected, the laboratories may exchange arbitrary adaptive, bidirectional quantum
messages of total cost at most `ℓ` qubits … Classical bits count as computational-basis qubits.
Every adaptive control symbol, including direction, routing, message length, continuation, and
stopping, is encoded in a self-delimiting classical transcript and charged to the same budget; only
a fixed public communication schedule is free." (Definition 3 (i)–(ii))

**Formalization Note** (decision D5). A window is a sequence of at most `T` steps. At each step the
active laboratory applies an instrument to its register (a port of `P` qubits and a private part)
whose outcome is a control symbol `c = (classical length, quantum length, next)` (`next = none`:
stop; `some true`: laboratory A acts next) and a classical string. The control symbol of step `t`
is either *scheduled* (fixed in advance by `sched t`, free) or *adaptive* (the measured one,
charged `|enc(c)|` bits, `enc` the Elias-γ code of each field plus two bits for `next`). The first
`lc` delivered bits of the string are the classical message (padded with zeros); the quantum
message is the first `lq` port qubits of the sender, moved into the receiver's port (whose old
content is discarded) and replaced by `|0⟩` at the sender (at most `P` qubits move; `lq` is
charged). A branch's classical cost is `Σ_t lc_t + Σ_{adaptive t} |enc(c_t)|` and its quantum
cost `Σ_t lq_t`. The reference `R` is never acted on.
-/

/-- A finite family of Kraus operators on the register `H`, grouped by outcomes in `α`; it is an
instrument when `Instr.Complete` holds. -/
structure Instr (H α : Type) [Fintype H] [DecidableEq H] [DecidableEq α] where
  outs : Finset α
  kraus : α → List (Matrix H H ℂ)

/-- The completeness relation `Σ_o Σ_K K†K = I` (trace preservation). -/
def Instr.Complete {H α : Type} [Fintype H] [DecidableEq H] [DecidableEq α] (I : Instr H α) :
    Prop :=
  ∑ o ∈ I.outs, ((I.kraus o).map fun K => Kᴴ * K).sum = 1

/-- The (unnormalized) post-measurement map of outcome `o`: `ρ ↦ Σ_K K ρ K†`. -/
def Instr.apply {H α : Type} [Fintype H] [DecidableEq H] [DecidableEq α] (I : Instr H α) (o : α)
    (ρ : Matrix H H ℂ) : Matrix H H ℂ :=
  ((I.kraus o).map fun K => K * ρ * Kᴴ).sum

/-- A window control symbol: classical length, quantum length, and who acts next
(`none` = stop). -/
structure Ctl where
  lc : ℕ
  lq : ℕ
  next : Option Bool
  deriving DecidableEq

/-- `|enc(c)|`: Elias-γ codes of `lc + 1` and `lq + 1`, and two bits for `next`. -/
def Ctl.encLen (c : Ctl) : ℕ := eliasGammaLen (c.lc + 1) + eliasGammaLen (c.lq + 1) + 2

/-- The delivered classical message: the first `lc` bits, padded with zeros. -/
def padTo (lc : ℕ) (m : Bits) : Bits := (m.take lc) ++ List.replicate (lc - m.length) false

/-- A laboratory register: a port of `P` qubits and a private part `H`. -/
abbrev LabReg (P : ℕ) (H : Type) := Qubits P × H

/-- The port after moving its first `l` qubits out (they become `|0⟩`). -/
def clearPrefix {P : ℕ} (l : ℕ) (x : Qubits P) : Qubits P := fun i => if i.val < l then false else x i

/-- The receiver's port after receiving the first `l` qubits of the sender's port `x`. -/
def recvPrefix {P : ℕ} (l : ℕ) (x y : Qubits P) : Qubits P := fun i => if i.val < l then x i else y i

/-- Kraus operator `z` of the move of the first `l` port qubits from the left laboratory to the
right one: the right port's old prefix `z` is discarded. -/
def moveKraus {P : ℕ} {H H' : Type} [DecidableEq H] [DecidableEq H'] (l : ℕ) (z : Qubits P) :
    Matrix (LabReg P H × LabReg P H') (LabReg P H × LabReg P H') ℂ :=
  Matrix.of fun out inp =>
    if (∀ i : Fin P, i.val < l → inp.2.1 i = z i) ∧
        out.1 = (clearPrefix l inp.1.1, inp.1.2) ∧ out.2 = (recvPrefix l inp.1.1 inp.2.1, inp.2.2)
    then 1 else 0

/-- Swap the two laboratories of a joint index. -/
def swapLabs {X Y : Type} (p : X × Y) : Y × X := (p.2, p.1)

/-- The channel moving the first `l` port qubits from laboratory A (`fromA = true`) to B, or
from B to A, tensored with the identity on the reference `R`. -/
def moveMap {P : ℕ} {HA HB HR : Type} [Fintype HA] [Fintype HB] [Fintype HR] [DecidableEq HA]
    [DecidableEq HB] [DecidableEq HR] (fromA : Bool) (l : ℕ)
    (ρ : Matrix ((LabReg P HA × LabReg P HB) × HR) ((LabReg P HA × LabReg P HB) × HR) ℂ) :
    Matrix ((LabReg P HA × LabReg P HB) × HR) ((LabReg P HA × LabReg P HB) × HR) ℂ :=
  ∑ z : Qubits P,
    let K : Matrix (LabReg P HA × LabReg P HB) (LabReg P HA × LabReg P HB) ℂ :=
      if fromA then moveKraus l z
      else (moveKraus (H := HB) (H' := HA) l z).submatrix swapLabs swapLabs
    (K ⊗ₖ (1 : Matrix HR HR ℂ)) * ρ * (K ⊗ₖ (1 : Matrix HR HR ℂ))ᴴ

/-- A two-laboratory window strategy (decision D5): laboratories `A` and `B` with registers
`Qubits P × HA` and `Qubits P × HB`, at most `T` steps, the public schedule `sched`, the first
active laboratory, and each laboratory's instrument as a function of the delivered classical
history (one control symbol and message per step). -/
structure WinStrat (P : ℕ) (HA HB : Type) [Fintype HA] [Fintype HB] [DecidableEq HA]
    [DecidableEq HB] where
  T : ℕ
  sched : ℕ → Option Ctl
  first : Bool
  instA : List (Ctl × Bits) → Instr (LabReg P HA) (Ctl × Bits)
  instB : List (Ctl × Bits) → Instr (LabReg P HB) (Ctl × Bits)
  completeA : ∀ h, (instA h).Complete
  completeB : ∀ h, (instB h).Complete

namespace WinStrat

variable {P : ℕ} {HA HB HR : Type} [Fintype HA] [Fintype HB] [Fintype HR] [DecidableEq HA]
  [DecidableEq HB] [DecidableEq HR]

/-- The joint register `(A, B, R)`. -/
abbrev Glob (P : ℕ) (HA HB HR : Type) := (LabReg P HA × LabReg P HB) × HR

/-- The branches of the window from step `t` with `fuel` steps left, active laboratory `s`
(`true` = A), delivered history `h`: each branch is its complete history and its subnormalized
state on `(A, B, R)`. -/
noncomputable def run (S : WinStrat P HA HB) :
    ℕ → ℕ → Bool → List (Ctl × Bits) → Matrix (Glob P HA HB HR) (Glob P HA HB HR) ℂ →
      List (List (Ctl × Bits) × Matrix (Glob P HA HB HR) (Glob P HA HB HR) ℂ)
  | _, 0, _, h, ρ => [(h, ρ)]
  | t, fuel + 1, s, h, ρ =>
    let outs : List (Ctl × Bits) := if s then (S.instA h).outs.toList else (S.instB h).outs.toList
    outs.flatMap fun o =>
      let ρ₁ : Matrix (Glob P HA HB HR) (Glob P HA HB HR) ℂ :=
        if s then (((S.instA h).kraus o).map fun K =>
            ((K ⊗ₖ (1 : Matrix (LabReg P HB) (LabReg P HB) ℂ)) ⊗ₖ (1 : Matrix HR HR ℂ)) * ρ *
            ((K ⊗ₖ (1 : Matrix (LabReg P HB) (LabReg P HB) ℂ)) ⊗ₖ (1 : Matrix HR HR ℂ))ᴴ).sum
        else (((S.instB h).kraus o).map fun K =>
            (((1 : Matrix (LabReg P HA) (LabReg P HA) ℂ) ⊗ₖ K) ⊗ₖ (1 : Matrix HR HR ℂ)) * ρ *
            (((1 : Matrix (LabReg P HA) (LabReg P HA) ℂ) ⊗ₖ K) ⊗ₖ (1 : Matrix HR HR ℂ))ᴴ).sum
      let c : Ctl := (S.sched t).getD o.1
      let h' := h ++ [(c, padTo c.lc o.2)]
      let ρ₂ := moveMap s (min c.lq P) ρ₁
      match c.next with
      | none => [(h', ρ₂)]
      | some s' => run S (t + 1) fuel s' h' ρ₂

/-- All branches of the complete window from the initial state `ρ`. -/
noncomputable def branches (S : WinStrat P HA HB)
    (ρ : Matrix (Glob P HA HB HR) (Glob P HA HB HR) ℂ) :
    List (List (Ctl × Bits) × Matrix (Glob P HA HB HR) (Glob P HA HB HR) ℂ) :=
  S.run 0 S.T S.first [] ρ

/-- The final state on `(A, B, R)`: the sum of all branches (the transcript is discarded; the
laboratories may keep copies in their registers). -/
noncomputable def final (S : WinStrat P HA HB)
    (ρ : Matrix (Glob P HA HB HR) (Glob P HA HB HR) ℂ) :
    Matrix (Glob P HA HB HR) (Glob P HA HB HR) ℂ :=
  ((S.branches ρ).map Prod.snd).sum

/-- The classical cost of a branch: delivered classical bits plus the encodings of its adaptive
control symbols. Step `i` of the history is step `i` of the window. -/
def classCost (S : WinStrat P HA HB) (h : List (Ctl × Bits)) : ℕ :=
  ((List.range h.length).zip h |>.map fun p =>
    p.2.1.lc + if S.sched p.1 = none then p.2.1.encLen else 0).sum

/-- The quantum cost of a branch: the number of qubits sent. -/
def quantCost (h : List (Ctl × Bits)) : ℕ := (h.map fun p => p.1.lq).sum

/-- A strategy without communication: every control symbol is scheduled with zero classical and
quantum length, so nothing is exchanged and the order of local activations is fixed. -/
def NoComm (S : WinStrat P HA HB) : Prop :=
  ∀ t, ∃ c : Ctl, S.sched t = some c ∧ c.lc = 0 ∧ c.lq = 0

end WinStrat

/-- The initial state of a strategy whose laboratories hold additional registers `XA`, `XB`
(shared entanglement and randomness), prepared in `ω`, next to the original state `ρ`. -/
def withResource {P : ℕ} {HA HB HR XA XB : Type}
    (ρ : Matrix ((LabReg P HA × LabReg P HB) × HR) ((LabReg P HA × LabReg P HB) × HR) ℂ)
    (ω : Matrix (XA × XB) (XA × XB) ℂ) :
    Matrix ((LabReg P (HA × XA) × LabReg P (HB × XB)) × HR)
      ((LabReg P (HA × XA) × LabReg P (HB × XB)) × HR) ℂ :=
  Matrix.of fun i j =>
    ρ (((i.1.1.1, i.1.1.2.1), (i.1.2.1, i.1.2.2.1)), i.2)
      (((j.1.1.1, j.1.1.2.1), (j.1.2.1, j.1.2.2.1)), j.2) *
    ω (i.1.1.2.2, i.1.2.2.2) (j.1.1.2.2, j.1.2.2.2)

/-- The part of a state of the extended laboratories on which both flags `fA = fB = 1` (the
designated flag registers `Bool` inside the additional registers), traced over the additional
registers: an operator on the original `(A, B, R)`. -/
def flaggedPart {P : ℕ} {HA HB HR YA YB : Type} [Fintype YA] [Fintype YB]
    (σ : Matrix ((LabReg P (HA × (Bool × YA)) × LabReg P (HB × (Bool × YB))) × HR)
      ((LabReg P (HA × (Bool × YA)) × LabReg P (HB × (Bool × YB))) × HR) ℂ) :
    Matrix ((LabReg P HA × LabReg P HB) × HR) ((LabReg P HA × LabReg P HB) × HR) ℂ :=
  Matrix.of fun i j => ∑ ya : YA, ∑ yb : YB,
    σ (((i.1.1.1, (i.1.1.2, (true, ya))), (i.1.2.1, (i.1.2.2, (true, yb)))), i.2)
      (((j.1.1.1, (j.1.1.2, (true, ya))), (j.1.2.1, (j.1.2.2, (true, yb)))), j.2)

/-- The partial trace over the additional registers. -/
def traceResource {P : ℕ} {HA HB HR XA XB : Type} [Fintype XA] [Fintype XB]
    (σ : Matrix ((LabReg P (HA × XA) × LabReg P (HB × XB)) × HR)
      ((LabReg P (HA × XA) × LabReg P (HB × XB)) × HR) ℂ) :
    Matrix ((LabReg P HA × LabReg P HB) × HR) ((LabReg P HA × LabReg P HB) × HR) ℂ :=
  Matrix.of fun i j => ∑ xa : XA, ∑ xb : XB,
    σ (((i.1.1.1, (i.1.1.2, xa)), (i.1.2.1, (i.1.2.2, xb))), i.2)
      (((j.1.1.1, (j.1.1.2, xa)), (j.1.2.1, (j.1.2.2, xb))), j.2)

end DIObliviousTransfer


