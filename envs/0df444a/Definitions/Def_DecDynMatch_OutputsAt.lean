-- Prove2me | Definitions.Def_DecDynMatch_OutputsAt
-- name    : DecDynMatch_OutputsAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:59:24.049408+00:00
-- url     : https://prove2.me/theorems/a0dffea9-1759-46bc-9706-915fc266b4c9
-- title:
--   Work entries, Sweep entries, outputs and replay lengths in an execution
-- statement:
--   In an execution of SC-DA:
--
--   1. player $i$ **outputs** in round $t$ if it is active and its round-start state is in Work with $h=J-1$; the output arm is its proposal in that round;
--   2. player $i$ **enters Work** in round $t$ if it is active and a pending Work entry is applied at the start of round $t$;
--   3. player $i$ **enters Sweep** in round $t$ if it is active and, after applying its pending mode change and the expiration check, it is in Seek with $\rho=J$;
--   4. two outputs of $i$ in rounds $t_1<t_2$ are **consecutive** if $i$ makes no output strictly between them;
--   5. the **replay length** stored in a state is $L=q-\ell$; the global replay deadline of player $i$ is $b_i+q$, since its local clock in round $t$ is $t-b_i$.
--
--   These notions are used by all timing milestones.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), §3.1, pp.7–8; Algorithm 1, p.6; App. A, pp.14–18

import Mathlib
import Definitions.Def_DecDynMatch_exec

namespace DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- **Work entries, Sweep entries and outputs in an execution.** J. Chen, M. Gao, Z. Zhang,
*Decentralized Dynamic Stable Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…),
§3.1, pp.7–8, and Algorithm 1, p.6.

`OutputsAt F I t i`: player `i` is active and makes a Work output in round `t`, i.e. its
round-start mode is Work with `h = J − 1` ("In the final Work round, regardless of the feedback z,
the player records its proposed arm as the output y", p.7). The output arm is `prop F I t i`. -/
def OutputsAt (F : ℕ → ℕ) (I : Instance K ι) (t : ℕ) (i : ι) : Prop :=
  i ∈ active I t ∧ (cur F I t i).m = .work ∧ (cur F I t i).h = J K - 1

/-- `EntersWork F I t i`: player `i` is active and starts Work in round `t`, i.e. a pending Work
entry (`ν = Work`) is applied at the start of round `t`. -/
def EntersWork (F : ℕ → ℕ) (I : Instance K ι) (t : ℕ) (i : ι) : Prop :=
  i ∈ active I t ∧ (pre F I t i).ν = some .work

/-- `QualifiesAt F I t i`: player `i` is active and enters Sweep in round `t`: after applying the
pending change and the expiration check it is in Seek with `ρ = J`, so the sweep qualification
(Algorithm 1, lines 16–17) fires. -/
def QualifiesAt (F : ℕ → ℕ) (I : Instance K ι) (t : ℕ) (i : ι) : Prop :=
  i ∈ active I t ∧ (expire (applyPending (pre F I t i))).m = .seek ∧
    (expire (applyPending (pre F I t i))).ρ = J K

/-- Player `i` makes no output in the rounds strictly between `t₁` and `t₂` (its outputs at `t₁`
and `t₂`, if any, are consecutive in its actual output history). -/
def NoOutputBetween (F : ℕ → ℕ) (I : Instance K ι) (i : ι) (t₁ t₂ : ℕ) : Prop :=
  ∀ t, t₁ < t → t < t₂ → ¬ OutputsAt F I t i

/-- The replay length `L = q − ℓ` stored in a state (after an output, `q = a + L` and `ℓ = a`). The
global replay deadline of player `i` is `bᵢ + q`, since its local clock in round `t` is `t − bᵢ`. -/
def replayLen (st : LState K) : ℕ := st.q - st.l

end DecDynMatch


