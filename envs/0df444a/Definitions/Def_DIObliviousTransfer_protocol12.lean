-- Prove2me | Definitions.Def_DIObliviousTransfer_protocol12
-- name    : DIObliviousTransfer_protocol12
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:14:40.005236+00:00
-- url     : https://prove2.me/theorems/88d4c416-b0ca-439e-804e-c986e8387f43
-- title:
--   Protocol 12: complete DI OT in three device windows
-- statement:
--   Protocol 12 is Protocol 2 with every commit-and-prove operation implemented by Protocol 5. The two banks have capacity $q_{\mathrm{bank}}=10L_0$, and each is preprocessed by Protocol 7 on its own batch (Alice's first, then Bob's). The transfer uses the third batch. The three batches have sizes $L_{\mathrm{pre}},L_{\mathrm{pre}},L_0$ (26) and share one leakage budget group. The variant `protocol12'` takes an arbitrary source commitment (Corollary 11), with separate budget groups.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), (26) and Protocol 12, p.56

import Mathlib
import Definitions.Def_DIObliviousTransfer_protocol5
import Definitions.Def_DIObliviousTransfer_protocol7

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), (26) and
Protocol 12, p.56: complete DI OT in three device windows, including preprocessing.

"Alice holds (S₀, S₁) ∈ {0, 1}² and Bob holds D ∈ {0, 1}. Public parameters are (26). Use three
distinct batches satisfying Definition 11; every rejection causes global abort. 1. Alice (first
preprocessing). Sample a uniform length-q_bank mask string and complete Step 1 of Protocol 5 with
Bob, using Protocol 7 on the first batch. Save the private bank state and the shared public
transcript. 2. Bob (second preprocessing). Complete the same operation with the roles reversed and
fresh uniform masks, using the second batch. Save the bank for Bob-owned records. 3. Alice and Bob
(transfer). Run Protocol 2 on the third batch. Implement every CP record, projection, and joint
predicate by Steps 2–5 of Protocol 5, using the corresponding owner's bank. On delivery or abort,
discard all private call-local state as in Definition 11."

**Formalization Note** (decisions D10, D14, D15, D16, D19, D22). Protocol 12 is Protocol 5 with
source Protocol 7 of capacity `q_bank = 10L₀` (whose length `Next(max{100q_bank, 100ℓ, s_λ})` is
`m_pre = Next(100q_bank)` of (26)), the predicate language and schedule of Protocol 2, and caller
Protocol 2 (length `m₀`). Batches: `0` Alice's source, `1` Bob's source, `2` the transfer batch;
all three windows share the one budget group `0` (D19). The source of `Protocol5`/`Corollary 11`
with an arbitrary string commitment uses `protocol12'`, with each source batch in its own group
and the transfer batch in a third.
-/

/-- `q_bank = 10L₀` as a function of `λ`. -/
noncomputable def qbankFn (N₀ : ℕ) (ell : ℕ → ℕ) : ℕ → ℕ := fun lam => qBank N₀ lam (ell lam)

/-- The predicate language of Protocol 2 as a family over `λ`. -/
noncomputable def L2fam (C : CodeFamily) (N₀ : ℕ) (ell : ℕ → ℕ) : ℕ → PredLang :=
  fun lam => L2 C N₀ (mOT lam (ell lam))

/-- Protocol 2 with Protocol 5 on two preprocessing commitments of an arbitrary source `S` of
capacity `q_bank` (Corollary 11); batch groups: Alice's source batches, Bob's source batches, and
the transfer batch in group `2·S.ng`. -/
noncomputable def protocol12' (S : StrCom) (C : CodeFamily)
    (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol) (N₀ : ℕ) (ηMS : ℝ) (ell : ℕ → ℕ) :
    Protocol :=
  protocol5 S ZK (L2fam C N₀ ell) sched2 (qbankFn N₀ ell) (protocol2 C N₀ ηMS ell)
    (fun lam b => if b < S.nb lam then S.group lam b
      else if b < 2 * S.nb lam then S.ng lam + S.group lam (b - S.nb lam) else 2 * S.ng lam)
    (fun lam => 2 * S.ng lam + 1)

/-- **Protocol 12**: the complete OT; three batches `[L_pre, L_pre, L₀]` in one shared budget
group. -/
noncomputable def protocol12 (C : CodeFamily) (Com : BitCom)
    (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol) (N₀ : ℕ) (ηMS : ℝ) (ell : ℕ → ℕ) :
    Protocol :=
  protocol5 (protocol7 C Com ZK N₀ ηMS ell (qbankFn N₀ ell)) ZK (L2fam C N₀ ell) sched2
    (qbankFn N₀ ell) (protocol2 C N₀ ηMS ell) (fun _ _ => 0) (fun _ => 1)

end DIObliviousTransfer


