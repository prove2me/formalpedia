-- Prove2me | Definitions.Def_NoisyOWMPC_Supplement_WiretapScheme
-- name    : NoisyOWMPC_Supplement_WiretapScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:57:23.71469+00:00
-- url     : https://prove2.me/theorems/ce7d62b9-1e12-4793-a366-bc05f741f691
-- title:
--   Computational wiretap coding schemes (Definition C.1 and its $\ell$-bit extension)
-- statement:
--   A **wiretap coding scheme** for channels $B : \mathcal X \to \mathcal Y$ (Bob) and $E : \mathcal X \to \mathcal Z$ (Eve) on a common input alphabet, for messages of length $\ell(\lambda)$, consists of an encoding length $N(\lambda)$ and two algorithms:
--
--   1. a randomized encoder $\mathrm{Enc}(1^\lambda, m) \to \hat x \in \mathcal X^N$ on messages $m \in \{0,1\}^{\ell(\lambda)}$;
--   2. a deterministic decoder $\mathrm{Dec}(1^\lambda, \hat y) \to \hat m \in \{0,1\}^{\ell(\lambda)} \cup \{\mathsf{fail}\}$ on Bob's observation $\hat y \in \mathcal Y^N$.
--
--   The scheme is **efficient** if $N$ and the number of encoder coins are polynomially bounded and both algorithms run in polynomial time. It is **correct** over $B$ if there is a negligible $\varepsilon$ with
--   $$
--   \Pr\big[\mathrm{Dec}(1^\lambda, B^N(\mathrm{Enc}(1^\lambda, m))) = m\big] \ge 1 - \varepsilon(\lambda)
--   $$
--   for every $\lambda$ and every message $m$. For one-bit messages it is **computationally secure** against $E$ if for every nonuniform polynomial-size adversary $A$ there is a negligible $\nu_A$ with
--   $$
--   \Pr\big[A(1^\lambda, E^N(\mathrm{Enc}(1^\lambda, b))) = b\big] \le \tfrac12 + \nu_A(\lambda)
--   $$
--   for a uniform bit $b$. For $\ell$-bit messages, security asks that every two messages $m_0, m_1$ give Eve's views that $A$ distinguishes with advantage at most $\nu_A(\lambda)$, uniformly over the pair.
--
--   These notions are the objects of Theorem C.2 (universal computational wiretap coding).
--
--   **Formalization Note** Definition C.1 is the case $\ell = 1$. The encoder's coins are uniform; adversaries are the published polynomial-size circuit families, given $(1^\lambda, \hat z)$ by the tuple encoding.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition C.1, p.55; extension to messages of polynomial length, p.57

import Mathlib
import Definitions.Def_NoisyOWMPC_DMC
import Definitions.Def_NoisyOWMPC_CoinAlg
import Definitions.Def_NoisyOWMPC_Distinguisher
import Definitions.Def_NoisyOWMPC_symEnc

namespace NoisyOWMPC.Supplement

open LaconicBarrier

/-- The probability `∏_p D(y_p | x_p)` that `N` independent uses of a DMC `D` turn the word `x` into
the word `y` (Ishai, Lu, Zafar, *Non-Interactive Cryptography over Noisy Channels from
Indistinguishability Obfuscation*, STOC 2027 submission (manuscript sha256 3a9569fa…),
Definition 4.1, p.18: "`C^N(x̂) = (C(x₁), …, C(x_N))`, where the channel calls use independent
randomness"). -/
noncomputable def chanW {X Y : Type} [Fintype Y] (D : DMC X Y) {n : ℕ} (x : Fin n → X)
    (y : Fin n → Y) : ℝ :=
  ∏ p, D.P (x p) (y p)

/-- A **wiretap coding scheme** for messages of length `ℓ(λ)` over channels with input alphabet `X`
and Bob's output alphabet `Y` (STOC 2027 submission (manuscript sha256 3a9569fa…), Definition C.1,
p.55, and its extension to longer messages, p.57): an encoding length `N(λ)`,
* `Enc(1^λ, m; ρ) → x̂ ∈ X^N`, a randomized encoder with `coins λ` uniform coins `ρ`, on messages
  `m ∈ {0,1}^{ℓ(λ)}`;
* `Dec(1^λ, ŷ) → m̂ ∈ {0,1}^{ℓ(λ)} ∪ {fail}`, a deterministic decoder on `ŷ ∈ Y^N` (`none` is
  `fail`).

**Formalization Note** Definition C.1 is the case `ℓ = 1` (a message `m ∈ {0,1}` is a one-bit
string). The encoder's coins are uniform. -/
structure WiretapScheme (X Y : Type) (ℓ : ℕ → ℕ) where
  /-- the encoding length `N(λ)` -/
  N : ℕ → ℕ
  /-- the number of coins of `Enc` -/
  coins : ℕ → ℕ
  /-- the encoder `Enc(1^λ, m; ρ)` -/
  enc : (lam : ℕ) → (Fin (ℓ lam) → Bool) → (Fin (coins lam) → Bool) → Fin (N lam) → X
  /-- the decoder `Dec(1^λ, ŷ)` -/
  dec : (lam : ℕ) → (Fin (N lam) → Y) → Option (Fin (ℓ lam) → Bool)

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] {ℓ : ℕ → ℕ}

/-- The scheme's algorithms are **efficient** (§3, p.15: "all algorithms and simulators run in
probabilistic polynomial time"; Definition C.1, p.55: "encoding length `N = N(λ)`"): `N` and the
number of coins are polynomially bounded, `Enc` computes `x̂` from `(1^λ, m, ρ)` and `Dec` computes
`m̂` from `(1^λ, ŷ)` in polynomial time. -/
def WiretapScheme.IsEfficient (W : WiretapScheme X Y ℓ) : Prop :=
  PolyBounded W.N ∧ PolyBounded W.coins ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (ℓ lam) → Bool) × (Fin (W.coins lam) → Bool))
    (fun z => [unary z.1, bits z.2.1, bits z.2.2]) (fun z => wordEnc X (W.enc z.1 z.2.1 z.2.2)) ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (W.N lam) → Y))
    (fun z => [unary z.1, wordEnc Y z.2]) (fun z => optEnc (W.dec z.1 z.2))

/-- **Correctness** over Bob's channel `B` (Definition C.1, p.55: "There is a negligible `ε` such
that, for every `λ` and every `m ∈ {0,1}`, `Pr[Dec(1^λ, B^N(Enc(1^λ, m))) = m] ≥ 1 − ε(λ)`"), for
every message `m ∈ {0,1}^{ℓ(λ)}`. -/
def WiretapScheme.Correct (W : WiretapScheme X Y ℓ) (B : DMC X Y) : Prop :=
  ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ (lam : ℕ) (m : Fin (ℓ lam) → Bool),
    1 - ε lam ≤ wprob (fun ω : (Fin (W.coins lam) → Bool) × (Fin (W.N lam) → Y) =>
        (1 / 2 : ℝ) ^ (W.coins lam) * chanW B (W.enc lam m ω.1) ω.2)
      (fun ω => W.dec lam ω.2 = some m)

/-- **Computational security** of a one-bit scheme against Eve's channel `E` (Definition C.1, p.55:
"For every adversary `A`, there is a negligible `ν_A` such that, for every `λ`,
`Pr[A(1^λ, E^N(Enc(1^λ, b))) = b] ≤ 1/2 + ν_A(λ)`, where `b` is uniform in `{0,1}`").

**Formalization Note** Adversaries are nonuniform polynomial-size circuit families (§3, p.15),
given `(1^λ, ẑ)` by the tuple encoding; the bit `b` is the one-bit message. -/
def WiretapScheme.SecureBit (W : WiretapScheme X Y (fun _ => 1)) (E : DMC X Z) : Prop :=
  ∀ A : Distinguisher, A.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam : ℕ,
    wprob (fun ω : Bool × (Fin (W.coins lam) → Bool) × (Fin (W.N lam) → Z) =>
        (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (W.coins lam) * chanW E (W.enc lam (fun _ => ω.1) ω.2.1) ω.2.2)
      (fun ω => A.acc lam (QAdvFew.PoQOracle.tup [unary lam, wordEnc Z ω.2.2]) = ω.1) ≤
      1 / 2 + ν lam

/-- **Computational security for `ℓ`-bit messages** against Eve's channel `E` (STOC 2027 submission
(manuscript sha256 3a9569fa…), p.57: "for longer messages any two messages are indistinguishable by
the same argument"): for every nonuniform polynomial-size adversary `A` there is a negligible `ν_A`
such that for every `λ` and all messages `m₀, m₁ ∈ {0,1}^{ℓ(λ)}`,
`|Pr[A(1^λ, E^N(Enc(1^λ, m₀))) = 1] − Pr[A(1^λ, E^N(Enc(1^λ, m₁))) = 1]| ≤ ν_A(λ)`.

**Formalization Note** `ν_A` is chosen before `λ` and the message pair (uniformity over the
prescribed inputs, §3, p.15). -/
def WiretapScheme.SecureMsg (W : WiretapScheme X Y ℓ) (E : DMC X Z) : Prop :=
  ∀ A : Distinguisher, A.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧
    ∀ (lam : ℕ) (m₀ m₁ : Fin (ℓ lam) → Bool),
      |A.accProb lam (fun ω : (Fin (W.coins lam) → Bool) × (Fin (W.N lam) → Z) =>
            (1 / 2 : ℝ) ^ (W.coins lam) * chanW E (W.enc lam m₀ ω.1) ω.2)
          (fun ω => QAdvFew.PoQOracle.tup [unary lam, wordEnc Z ω.2]) -
        A.accProb lam (fun ω : (Fin (W.coins lam) → Bool) × (Fin (W.N lam) → Z) =>
            (1 / 2 : ℝ) ^ (W.coins lam) * chanW E (W.enc lam m₁ ω.1) ω.2)
          (fun ω => QAdvFew.PoQOracle.tup [unary lam, wordEnc Z ω.2])| ≤ ν lam

end NoisyOWMPC.Supplement


