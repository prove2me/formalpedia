-- Prove2me | Definitions.Def_BeyondDS_Sig
-- name    : BeyondDS_Sig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:00.92806+00:00
-- url     : https://prove2.me/theorems/b785d50d-961e-4a32-8e13-d643688f4100
-- title:
--   Parameters, signature schemes and perfect correctness
-- statement:
--   **Parameters.** An execution has a computational security parameter $\kappa$, a corruption budget $t$, a statistical parameter $\lambda$, and a designated sender among the $n=2t+1$ identities $\{0,\dots,n-1\}$.
--
--   **Signature scheme.** A scheme $\Sigma$ for one value of $\kappa$ has a number of coins, a public signature-length bound $\ell$, and three maps on bit strings: key generation $\mathrm{gen}$ (coins $\mapsto$ (public key, secret key)), signing $\mathrm{sign}(sk,m,\text{coins})$, and a deterministic verifier $\mathrm{verify}(pk,m,s)\in\{0,1\}$. A verifier **accepts** $(pk,m,s)$ when $|s|\le\ell$ and $\mathrm{verify}(pk,m,s)=1$: "longer encodings are rejected even if the underlying verifier would accept padding".
--
--   **Perfect correctness.** $\Sigma$ is correct when for all key coins, signing coins and messages, the honest signature has length at most $\ell$ and verifies under the matching public key.
--
--   The module also defines the uniform coin law, independent signing of a batch, and honest key generation for $n$ identities with independent coins: "authenticated public verification keys", so a corruption discloses an honest key and never replaces it.
--
--   **Formalization Note** $\lambda$ is a natural number, so the protocol can read it in unary; a real $\lambda\ge C\log(n+1)\ge C\log 2$ changes by at most a constant factor under rounding. The paper names no unforgeability game; this structure is the syntax, `Sig.Correct` is perfect correctness (Proposition A.1, p.63, makes the same assumption), and the game is `BeyondDS.EUFCMA`.
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §1.1, p.3 (PDF p.4); §4.2, p.12 (PDF p.13); §5.2, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability

set_option autoImplicit false

open QAlgorithms.Complexity

namespace BeyondDS

/-- Parameters of one execution of Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript
sha256 c84cf9c9…), §1.1, p.3: `n = 2t + 1` players, computational parameter `κ`, statistical parameter
`λ` (`lam`), and the designated sender.

**Formalization Note.** `λ` is a natural number, which the protocol can read in unary; the real
`λ ≥ C log(n + 1) ≥ C log 2` changes by at most a constant factor under rounding. `t = 0` is allowed
("a sole player decides locally", §4.1, p.11). -/
structure Params where
  /-- Computational security parameter. -/
  κ : ℕ
  /-- Corruption budget. -/
  t : ℕ
  /-- Statistical parameter `λ`. -/
  lam : ℕ
  /-- The designated sender of broadcast. -/
  sender : Fin (2 * t + 1)

/-- The population `n = 2t + 1`. -/
abbrev Params.n (P : Params) : ℕ := 2 * P.t + 1

/-- A digital signature scheme for one value of the security parameter (§4.2, p.12; §5.2, p.15).
Keys and signatures are bit strings. `gen` and `sign` read uniform coins, and `verify` is
deterministic. `sigLen` is the public bound of p.15: "Signatures have a specified efficiently
verifiable encoding with a public polynomial length bound; longer encodings are rejected even if the
underlying verifier would accept padding."

**Formalization Note.** The paper names no game; the standard reading is used here, as `paper.md`
decision 7 records: this structure carries the syntax, `Sig.Correct` is perfect correctness, and the
game is `BeyondDS.EUFCMA`. -/
structure Sig where
  /-- Number of coins of `gen` and of `sign`. -/
  coinLen : ℕ
  /-- The public bound on the length of a signature. -/
  sigLen : ℕ
  /-- Key generation: coins to `(public key, secret key)`. -/
  gen : (Fin coinLen → Bool) → Str × Str
  /-- Signing: secret key, message, coins. -/
  sign : Str → Str → (Fin coinLen → Bool) → Str
  /-- Verification: public key, message, signature. -/
  verify : Str → Str → Str → Bool

/-- Perfect correctness: for all coins and all messages, an honest signature has length at most
`sigLen` and verifies. Proposition A.1 (p.63) makes the same assumption ("Assume perfectly correct
signatures"). -/
def Sig.Correct (S : Sig) : Prop :=
  ∀ (c r : Fin S.coinLen → Bool) (m : Str),
    (S.sign (S.gen c).2 m r).length ≤ S.sigLen ∧
      S.verify (S.gen c).1 m (S.sign (S.gen c).2 m r) = true

/-- What a verifier accepts: the length check of p.15 and then `verify`. -/
def Sig.accepts (S : Sig) (pk m s : Str) : Bool :=
  decide (s.length ≤ S.sigLen) && S.verify pk m s

/-- Uniform coins of the scheme. -/
noncomputable def Sig.coinLaw (S : Sig) : PMF (Fin S.coinLen → Bool) :=
  PMF.uniformOfFintype _

/-- Independent uniform coins for a batch of signatures. -/
noncomputable def Sig.signBatch (S : Sig) (sk : Str) : List Str → PMF (List Str)
  | [] => PMF.pure []
  | m :: ms =>
    S.coinLaw.bind fun r =>
      (Sig.signBatch S sk ms).map fun ss => S.sign sk m r :: ss

/-- Honest key generation for `n` identities with independent coins (§4.2, p.12: "authenticated
public verification keys"). A corruption discloses an honest key and never replaces it. -/
noncomputable def Sig.keysLaw (S : Sig) (n : ℕ) : PMF ((Fin n → Str) × (Fin n → Str)) :=
  (PMF.uniformOfFintype (Fin n → Fin S.coinLen → Bool)).map fun c =>
    (fun i => (S.gen (c i)).1, fun i => (S.gen (c i)).2)

end BeyondDS


