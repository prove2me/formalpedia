-- Prove2me | Definitions.Def_DistVerif_Simulation_Protocol
-- name    : DistVerif_Simulation_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:13.112673+00:00
-- url     : https://prove2.me/theorems/6328c200-6918-4e2d-bf97-3f6a2e65d05a
-- title:
--   Public-coin two-party protocols with one bit per round (§2.2, pp. 1243–1244)
-- statement:
--   In the **communication complexity model** two parties, Alice and Bob, are joined by a link. Alice receives $x\in\{0,1\}^b$ and Bob $y\in\{0,1\}^b$; both want to know $f(x,y)$ for a Boolean function $f:\{0,1\}^b\times\{0,1\}^b\to\{0,1\}$. One bit is sent per round, so the running time equals the number of bits exchanged.
--
--   A **deterministic protocol** specifies, as a function of the transcript $\tau\in\{0,1\}^*$ of bits exchanged so far, which party sends the next bit; the bit Alice sends, as a function of $x$ and $\tau$; the bit Bob sends, as a function of $y$ and $\tau$; and the final outputs of Alice (a function of $x$ and the transcript) and of Bob (a function of $y$ and the transcript). The transcript after $k$ rounds is obtained by starting from the empty word and appending, $k$ times, the bit of the designated speaker.
--
--   A **public-coin protocol** is a random string $\omega\sim\mu$ known to both parties together with a deterministic protocol for each $\omega$. It **computes $f$ with $\epsilon$-error using $k$ bits** if, for every $(x,y)$, the probability over $\omega$ that Alice or Bob, after $k$ rounds, does not output $f(x,y)$ is at most $\epsilon$.
--
--   These are the objects of $R^{cc-pub}_\epsilon(f)$, the minimum worst-case running time (number of bits) of an $\epsilon$-error public-coin protocol for $f$.
--
--   **Formalization Note** Every run of the protocol has exactly $k$ rounds; a protocol that needs fewer bits on some inputs can pad with dummy bits, so "exactly $k$" and "at most $k$" give the same complexity. Alice's bits and output read only $x$, the transcript and $\omega$; Bob's read only $y$, the transcript and $\omega$. The randomness is a `PMF` on an arbitrary type `Ω`.
-- source:
--   Das Sarma, Holzer, Kor, Korman, Nanongkai, Pandurangan, Peleg, Wattenhofer, Distributed Verification and Hardness of Distributed Approximation, SIAM J. Comput. 41 (2012), pp. 1243–1244, §2.2 (the communication complexity model, R^{cc−pub}_ε(f))

import Mathlib

namespace DistVerif.Simulation

/-- A deterministic two-party protocol in the communication complexity model (§2.2,
pp. 1243–1244) on `b`-bit inputs, sending one bit per round. Alice holds `x`, Bob holds `y`.
* `aliceSpeaks τ` says, from the transcript `τ` so far, whether Alice (`true`) or Bob (`false`)
  sends the next bit;
* `aliceBit x τ` / `bobBit y τ` is the bit sent: Alice's reads only `x` and `τ`, Bob's only `y`
  and `τ`;
* `outA x τ` / `outB y τ` is the final output of Alice / Bob. -/
structure DetProtocol (b : ℕ) where
  aliceSpeaks : List Bool → Bool
  aliceBit : (Fin b → Bool) → List Bool → Bool
  bobBit : (Fin b → Bool) → List Bool → Bool
  outA : (Fin b → Bool) → List Bool → Bool
  outB : (Fin b → Bool) → List Bool → Bool

/-- The transcript after `k` rounds (`k` bits) of the protocol on inputs `x, y`. -/
def DetProtocol.transcript {b : ℕ} (P : DetProtocol b) (x y : Fin b → Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 =>
      let τ := P.transcript x y k
      τ ++ [if P.aliceSpeaks τ then P.aliceBit x τ else P.bobBit y τ]

/-- A public-coin randomized two-party protocol: a shared random string `ω ∼ μ` on `Ω`
known to both parties, and a deterministic protocol for each `ω`. -/
structure PubProtocol (b : ℕ) where
  Ω : Type
  μ : PMF Ω
  prot : Ω → DetProtocol b

/-- The public-coin protocol `P`, run for exactly `k` bits of communication, computes `f` with
`ε`-error: for every `(x, y)`, the probability that Alice or Bob fails to output `f(x, y)` is at
most `ε`. -/
def PubProtocol.ComputesWithin {b : ℕ} (P : PubProtocol b) (k : ℕ)
    (f : (Fin b → Bool) → (Fin b → Bool) → Bool) (ε : ℝ) : Prop :=
  ∀ x y : Fin b → Bool,
    P.μ.toOuterMeasure
        {ω | ¬ ((P.prot ω).outA x ((P.prot ω).transcript x y k) = f x y ∧
                (P.prot ω).outB y ((P.prot ω).transcript x y k) = f x y)}
      ≤ ENNReal.ofReal ε

end DistVerif.Simulation


