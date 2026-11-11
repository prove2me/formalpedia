-- Prove2me | Definitions.Def_TrapdoorHCF_CCA2_Games
-- name    : TrapdoorHCF_CCA2_Games
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T19:35:40.676207+00:00
-- url     : https://prove2.me/theorems/0ad38ad0-1e35-4db8-b154-6435e7972df7
-- title:
--   Perfect PKE correctness and the classical IND-CCA2 and ATDHF games
-- statement:
--   For a public-key encryption scheme $P$ over $\{0,1\}^{n(\lambda)}$, perfect correctness requires decryption of every encryption to return its message for every generated key and every encryption tape. Its **IND-CCA2 experiment** gives stage 1 unrestricted decryption access, validates both challenge messages, encrypts the selected message, and gives stage 2 decryption access with only the exact challenge ciphertext excluded. Invalid messages or exhaustion return 0 in both experiments.
--
--   The **ATDHF experiment** gives stage 1 unrestricted partial-inversion access. It samples a fresh input $x$, reveals $y=\operatorname{Eval}(pk,x)$ and either its designated value or an independent uniform $l(\lambda)$-bit string, and gives stage 2 partial-inversion access excluding exactly $y$. For either experiment, with $E^0$ real and $E^1$ random or message-one respectively, advantage is
--
--   $$\left|\Pr[E^0=1]-\Pr[E^1=1]\right|.$$
--
--   IND-CCA2 security quantifies negligible advantage over all uniform PPT adversaries and contains no correctness clause. ATDHF security includes perfect correctness, as Definition 11 presupposes it. A pair of stages is encoded by one published reactive machine carrying state across the challenge, with one polynomial budget of coins, state, output and activations. Queries and termination have distinct tuple tags. The retained query list is observational data for the hidden-candidate experiment and is never given to the adversary. These games use sampler laws and exact string equality, including when challenge messages coincide.
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Definition 1, p.10; Definition 2 and experiment, p.11; Definition 11 and experiment, pp.17–18

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_TDHF
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2

/-- Definition 1, p.10. Perfect correctness is separate from security. -/
def PKE.PerfectlyCorrect (n : ℕ → ℕ) (P : RestrictedDec.PKE) : Prop :=
  ∀ lam (r : Fin (P.keyCoins lam) → Bool) (m : Str)
    (rho : Fin (P.encCoins lam) → Bool), m.length = n lam →
    P.dec lam (P.keyGen lam r).2 (P.enc lam (P.keyGen lam r).1 m rho) = some m

/-- Output of one stage; none marks exhaustion. Queries are retained for Lemma 4.
One budget is shared across both stages. -/
structure StageResult where
  state : Str
  output : Option Str
  fuel : ℕ
  queries : List Str

/-- Local move protocol: tup [[false], y] queries y; every other tag terminates
with the second field as payload. The state is the state returned by activate.
This parser does not use RestrictedDec's functional-decryption moves. -/
noncomputable def runStage (A : RestrictedDec.Adversary) (lam : ℕ)
    (oracle : Str → Option Str) : ℕ → Str → Str → PMF StageResult
  | 0, s, _ => pure ⟨s, none, 0, []⟩
  | fuel + 1, s, input => do
      let a ← A.activate lam s input
      let fields := BeyondDS.untup a.2
      if fields.getD 0 [] = [false] then
        let y := fields.getD 1 []
        let rest ← runStage A lam oracle fuel a.1 (RestrictedDec.encOpt (oracle y))
        pure { rest with queries := y :: rest.queries }
      else
        pure ⟨a.1, some (fields.getD 1 []), fuel, []⟩

/-- Exact string equality is the only post-challenge exclusion. -/
def exclude (oracle : Str → Option Str) (challenge : Str) (query : Str) : Option Str :=
  if query = challenge then none else oracle query

/-- Probability of output 1; PMFs are normalized even on timeout or malformed input. -/
noncomputable def prOne (law : PMF Bool) : ℝ := (law true).toReal

noncomputable def advantage (real random : ℕ → PMF Bool) (lam : ℕ) : ℝ :=
  |prOne (real lam) - prOne (random lam)|

/-- Definition 2, p.11. Stage 1 outputs tup [m0,m1] and keeps st as machine state.
Invalid messages and exhausted stages output 0 in both b experiments. Stage 2
receives tup [ct*,st]; its output's first bit is its guess. -/
noncomputable def expCCA2 (n : ℕ → ℕ) (P : RestrictedDec.PKE)
    (A : RestrictedDec.Adversary) (b : Bool) (lam : ℕ) : PMF Bool := do
  let keys ← P.keyLaw lam
  let pre ← runStage A lam (P.dec lam keys.2) (A.p.eval lam + 1) []
    (BeyondDS.tup [encNat lam, keys.1])
  match pre.output with
  | none => pure false
  | some out =>
      let ms := BeyondDS.untup out
      let m0 := ms.getD 0 []
      let m1 := ms.getD 1 []
      if m0.length = n lam ∧ m1.length = n lam ∧ m0.length = m1.length then
        let ct ← P.encLaw lam keys.1 (if b then m1 else m0)
        let post ← runStage A lam (exclude (P.dec lam keys.2) ct) pre.fuel pre.state
          (BeyondDS.tup [ct, pre.state])
        pure ((post.output.getD []).headD false)
      else pure false

noncomputable def advCCA2 (n : ℕ → ℕ) (P : RestrictedDec.PKE)
    (A : RestrictedDec.Adversary) : ℕ → ℝ :=
  advantage (expCCA2 n P A false) (expCCA2 n P A true)

/-- Definition 2 has no correctness clause. PPT is uniform with no advice. -/
def INDCCA2 (n : ℕ → ℕ) (P : RestrictedDec.PKE) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid → NoisyOWMPC.Negligible (advCCA2 n P A)

/-- The pp.17–18 experiment, real for b=false and random for b=true.
Stage 1 outputs sigma as its payload; its internal state also survives. -/
noncomputable def expATDHF (l : ℕ → ℕ) (T : TDHF)
    (A : RestrictedDec.Adversary) (b : Bool) (lam : ℕ) : PMF Bool := do
  let keys ← T.keyLaw lam
  let pre ← runStage A lam (T.pInv lam keys.2) (A.p.eval lam + 1) []
    (BeyondDS.tup [encNat lam, keys.1])
  match pre.output with
  | none => pure false
  | some sigma =>
      let x ← T.inputLaw lam
      let u ← coinsLaw (l lam)
      let y := T.eval lam keys.1 x
      let z := if b then List.ofFn u else T.hEval lam keys.1 x
      let post ← runStage A lam (exclude (T.pInv lam keys.2) y) pre.fuel pre.state
        (BeyondDS.tup [encNat lam, keys.1, sigma, y, z])
      pure ((post.output.getD []).headD false)

noncomputable def advATDHF (l : ℕ → ℕ) (T : TDHF)
    (A : RestrictedDec.Adversary) : ℕ → ℝ :=
  advantage (expATDHF l T A false) (expATDHF l T A true)

/-- Definition 11, p.18, explicitly presupposes Definition 9 correctness. -/
def IsATDHF (l : ℕ → ℕ) (T : TDHF) : Prop :=
  T.PerfectlyCorrect ∧
    ∀ A : RestrictedDec.Adversary, A.Valid → NoisyOWMPC.Negligible (advATDHF l T A)

end TrapdoorHCF.CCA2


