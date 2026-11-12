-- Prove2me | Definitions.Def_QSampVerif_indcpaAdvantage
-- name    : QSampVerif_indcpaAdvantage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:36:56.979993+00:00
-- url     : https://prove2.me/theorems/5d18d36c-44d3-4098-8e52-0eae305f480d
-- title:
--   The IND-CPA game and advantage (Definition 3.20 item 2)
-- statement:
--   The **IND-CPA game** for a QFHE scheme at $(\kappa,L)$ with secret bit $b$ is played between a classical challenger and an adversary in the prover model (a quantum circuit with classical advice). The challenger draws $(\mathsf{sk},\mathsf{ek})\leftarrow\mathsf{Gen}(1^\kappa,1^L)$ and sends $\mathsf{ek}$. Thereafter it answers each adversary message:
--
--   1. $0\,x$ (an encryption query) with a fresh $\mathsf{Enc}_{\mathsf{sk}}(x)$, before and after the challenge;
--   2. the first message $1\,w$ with $|w|$ even (the challenge $(m_0,m_1)$, the two halves of $w$, so $|m_0|=|m_1|$) with a fresh $\mathsf{Enc}_{\mathsf{sk}}(m_b)$;
--   3. anything else (an odd-length or repeated challenge, an empty message) with the empty string $\bot$.
--
--   The adversary's guess is the first bit of its last message. The **IND-CPA advantage** is
--
--   $$\mathrm{Adv}^{\mathrm{ind\text{-}cpa}}(A)=\bigl|\Pr[A\to1\mid b=0]-\Pr[A\to1\mid b=1]\bigr| .$$
--
--   **Formalization Note** Encoding the challenge as halves of one string makes unequal-length challenges impossible rather than answered, so no length information leaks.
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Definition 3.20 item 2, p.24 (PDF 25); paper.md decision 12

import Definitions.Def_QSampVerif_QFHEScheme
import Definitions.Def_QSampVerif_ClassicalParty

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms QAlgorithms.Complexity

/-- The message of the IND-CPA challenger with secret bit `b`, keys `(sk, ek)` and fresh coin
string `e`, after transcript `tr`:
* first round: the evaluation key `ek`;
* after an adversary message `0 x` (an encryption query): a fresh encryption `Enc_sk(x)`;
* after the first adversary message `1 w` with `|w|` even (the challenge `(m₀, m₁)`, the two
  halves of `w`, so `|m₀| = |m₁|`): a fresh encryption `Enc_sk(m_b)`;
* otherwise (an odd-length challenge, a second challenge, an empty message): the empty string
  `⊥`. -/
def cpaMsg (S : QFHEScheme) (κ : ℕ) (sk ek : Str) (b : Bool) (tr : List (Str × Str)) (e : Str) :
    Str :=
  match tr.getLast? with
  | none => ek
  | some (_, false :: x) => S.enc κ sk x e
  | some (_, true :: w) =>
      if (tr.dropLast.any fun p => p.2.head? == some true) || w.length % 2 == 1 then []
      else S.enc κ sk (if b then w.drop (w.length / 2) else w.take (w.length / 2)) e
  | some (_, []) => []

/-- The number of fresh coins the challenger draws after transcript `tr` (those of the
encryption it is about to send, `0` if it sends no encryption). -/
def cpaCoins (S : QFHEScheme) (κ : ℕ) (tr : List (Str × Str)) : ℕ :=
  match tr.getLast? with
  | none => 0
  | some (_, false :: x) => S.encCoins κ x.length
  | some (_, true :: w) =>
      if (tr.dropLast.any fun p => p.2.head? == some true) || w.length % 2 == 1 then 0
      else S.encCoins κ (w.length / 2)
  | some (_, []) => 0

/-- The IND-CPA challenger with keys `(sk, ek)` and secret bit `b` as a classical party. Its
output is the adversary's guess: the first bit of the adversary's last message. -/
def cpaChallenger (S : QFHEScheme) (κ : ℕ) (sk ek : Str) (b : Bool) : ClassicalParty where
  coins := cpaCoins S κ
  msg := fun tr e => cpaMsg S κ sk ek b tr (List.ofFn e)
  out := fun tr => some [((tr.getLast?).bind fun p => p.2.head?).getD false]

/-- `Pr[A outputs 1 | b]`: keys from `Gen(1^κ, 1^L)`, then one round per step of `A`. -/
noncomputable def cpaAccept (S : QFHEScheme) (κ L : ℕ) (A : Prover) (b : Bool) : ℝ :=
  ((2 : ℝ) ^ S.genCoins κ L)⁻¹ * ∑ g : Qubits (S.genCoins κ L),
    runParty (cpaChallenger S κ (S.gen κ L (List.ofFn g)).1 (S.gen κ L (List.ofFn g)).2 b) A
      A.steps.length (some [true])

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Definition 3.20 item 2 (Security), p.24 (PDF 25): "encryptions of equal-length messages are
computationally indistinguishable, even given the evaluation key and access to a classical
encryption oracle". The IND-CPA advantage `|Pr[1 | b = 0] − Pr[1 | b = 1]|` of the adversary `A`
(a quantum circuit with classical advice, in the prover model) against the scheme at `(κ, L)`.

**Formalization Note.** The challenge `(m₀, m₁)` is sent as one string `1 m₀ m₁` and split into
halves, so the two messages always have equal length; an odd-length challenge is answered by `⊥`
and never by an encryption, so the message length leaks nothing. Encryption queries are
answered before and after the challenge. -/
noncomputable def indcpaAdvantage (S : QFHEScheme) (κ L : ℕ) (A : Prover) : ℝ :=
  |cpaAccept S κ L A false - cpaAccept S κ L A true|

end QSampVerif


