-- Prove2me | Definitions.Def_GPTIP632_Classical_IP
-- name    : GPTIP632_Classical_IP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:12.331201+00:00
-- url     : https://prove2.me/theorems/9351ff98-2197-43d7-be91-db83e4b42e53
-- title:
--   Classical interactive proofs: the class $\mathsf{IP}$ of promise problems, randomised provers, public-coin verifiers
-- statement:
--   A **classical interactive proof system** has a probabilistic polynomial-time verifier $V$ with $c(n)$ random coins. On input $x$ of length $n$ and coins $r$, in each of $R(n)$ rounds the verifier sends an $\ell(n)$-bit message computed from $(x,r,\text{conversation so far})$, and the prover replies with an $\ell(n)$-bit message; afterwards the verifier accepts or rejects as a function of $(x,r,\text{conversation})$. Here $c$, $R$, $\ell$ are polynomials and the verifier is a clocked deterministic machine.
--
--   A **prover** is an arbitrary, possibly randomised, function of the conversation so far: a family of conditional distributions of its next message. $\Pr[(V,P)(x)\text{ accepts}]$ averages over uniform coins and over the prover's choices.
--
--   The class $\mathsf{IP}$ consists of the promise problems $L$ with a verifier such that for every $x\in L_{\rm yes}$ some prover gives
--
--   $$
--   \Pr[(V,P)(x)\text{ accepts}]\ge\tfrac23,
--   $$
--
--   and for every $x\in L_{\rm no}$ every prover gives acceptance probability at most $\tfrac13$. A verifier is **public-coin** if its messages are its coins: $c=R\cdot\ell$ and the round-$j$ message is the $j$-th block of $\ell$ coins.
--
--   This is the classical model of Fact A.2, the lower-bound ingredient of Theorem E.5.
--
--   **Formalization Note** The machine model is the published `QAdvFew.PoQOracle.OTM` with the empty oracle, clocked by a polynomial, its output read off the work tape; messages are padded to length $\ell(n)$.
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.12 (PDF p.14), Definition A.1 and Fact A.2

import Mathlib
import Definitions.Def_GPTIP632_Classical_Protocol

/-!
# Classical interactive proofs (Definition A.1) and public-coin systems

Kishor Bharti, *Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical
Theories*, STOC 2027 submission #632 (October 2026), Definition A.1 and Fact A.2 (p.12, PDF p.14).

A verifier is a deterministic machine clocked by a polynomial, with `coins(n)` random bits. In
round `j < R(n)` it sends the `ℓ(n)`-bit message computed from `(x, r, transcript so far)`, the
prover replies with an `ℓ(n)`-bit message, and after the last round the verifier outputs the first
bit computed from `(x, r, whole transcript)`. A prover is an arbitrary randomised function of the
conversation so far: a conditional distribution of its next message.
-/

noncomputable section

namespace GPTIP632.Classical

open QAlgorithms.Complexity QAdvFew.PoQOracle

attribute [local instance] _root_.Classical.propDecidable

/-- **Definition A.1**: a probabilistic polynomial-time verifier with polynomially many rounds and
messages of polynomial length. -/
structure IPVerifier where
  M : OTM
  clock : Polynomial ℕ
  coins : Polynomial ℕ
  R : Polynomial ℕ
  ℓ : Polynomial ℕ

namespace IPVerifier

variable (V : IPVerifier)

/-- Pad or truncate a string to length `m`. -/
def fitTo (m : ℕ) (s : Str) : Str := (s ++ List.replicate m false).take m

/-- The messages of a transcript, in order. -/
def flat (τ : List (Str × Str)) : List Str := τ.flatMap fun p => [p.1, p.2]

/-- The verifier machine's output on `(x, r, τ)`. -/
def run (x r : Str) (τ : List (Str × Str)) : Str :=
  V.M.output O₀ (tup (x :: r :: flat τ)) (V.clock.eval (tup (x :: r :: flat τ)).length)

/-- The verifier's message after the transcript `τ`. -/
def msg (x r : Str) (τ : List (Str × Str)) : Str := fitTo (V.ℓ.eval x.length) (V.run x r τ)

/-- The verifier's decision on the whole transcript. -/
def dec (x r : Str) (τ : List (Str × Str)) : Bool := (V.run x r τ).headD false

/-- A **randomised prover** for `V` on `x` (Definition A.1: "an arbitrary, possibly randomised,
function from the conversation so far to the next message"): `π τ v p` is the probability of the
reply `p` after the conversation `τ` and the verifier's message `v`; a distribution on the
`ℓ(|x|)`-bit strings. -/
def IsProver (x : Str) (π : List (Str × Str) → Str → Str → ℝ) : Prop :=
  (∀ τ v p, 0 ≤ π τ v p) ∧ (∀ τ v, ∑ p ∈ strings (V.ℓ.eval x.length), π τ v p = 1) ∧
  (∀ τ v p, p.length ≠ V.ℓ.eval x.length → π τ v p = 0)

/-- The acceptance probability with coins `r`, `k` rounds still to play after the transcript `τ`. -/
def accFrom (x : Str) (π : List (Str × Str) → Str → Str → ℝ) (r : Str) :
    ℕ → List (Str × Str) → ℝ
  | 0, τ => if V.dec x r τ then 1 else 0
  | k + 1, τ => ∑ p ∈ strings (V.ℓ.eval x.length),
      π τ (V.msg x r τ) p * accFrom x π r k (τ ++ [(V.msg x r τ, p)])

/-- `Pr[(V, P)(x) accepts]`, the coins `r` uniform on `{0,1}^{coins(|x|)}`. -/
def acc (x : Str) (π : List (Str × Str) → Str → Str → ℝ) : ℝ :=
  (∑ r ∈ strings (V.coins.eval x.length), V.accFrom x π r (V.R.eval x.length) []) /
    2 ^ V.coins.eval x.length

/-- **Public coin** (Fact A.2): the verifier's coins are exactly its messages: `coins = R · ℓ`, and
the message of round `j` is the `j`-th block of `ℓ(|x|)` coins, on every input. -/
def PublicCoin : Prop :=
  V.coins = V.R * V.ℓ ∧
  ∀ (x r : Str) (τ : List (Str × Str)), τ.length < V.R.eval x.length →
    r.length = V.coins.eval x.length →
    V.msg x r τ = (r.drop (τ.length * V.ℓ.eval x.length)).take (V.ℓ.eval x.length)

end IPVerifier

/-- **IP** (Definition A.1, p.12), as a class of promise problems: `L` has a verifier `V` such that
for every `x ∈ L_yes` some prover makes `V` accept with probability at least `2/3`, and for every
`x ∈ L_no` every prover makes it accept with probability at most `1/3`. -/
def IP : Set KTUnitary.Synth.PromiseProblem :=
  {L | ∃ V : IPVerifier, ∀ x : Str,
    (x ∈ L.1 → ∃ π, V.IsProver x π ∧ (2 : ℝ) / 3 ≤ V.acc x π) ∧
    (x ∈ L.2 → ∀ π, V.IsProver x π → V.acc x π ≤ 1 / 3)}

end GPTIP632.Classical

end


