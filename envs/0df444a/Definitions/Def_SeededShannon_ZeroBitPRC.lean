-- Prove2me | Definitions.Def_SeededShannon_ZeroBitPRC
-- name    : SeededShannon_ZeroBitPRC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:44:55.272203+00:00
-- url     : https://prove2.me/theorems/9708b6db-fe8e-47e5-bd2e-8b79f4ce265a
-- title:
--   Zero-bit public-key pseudorandom code and its properties (Definition 3.5)
-- statement:
--   A **zero-bit public-key pseudorandom code** $\Pi_{\mathrm{PRC}}$ on codeword space $\{0,1\}^{n}$, $n=n(\lambda)$, consists of three algorithms:
--
--   1. $\mathrm{Setup}(1^\lambda)\to(pk,sk)$, randomized;
--   2. $\mathrm{Encode}(pk)\to c\in\{0,1\}^n$, randomized; $\mathrm{Encode}(pk;r)$ denotes the codeword under encoding coins $r$;
--   3. $\mathrm{Decode}(sk,c')\to b\in\{0,1\}$, deterministic.
--
--   The module defines the following properties.
--
--   - **Efficiency**: polynomially many coins, and one polynomial-time machine for each algorithm.
--   - **Strong $p$-robustness**: there is a negligible $\nu$ such that for every $\lambda$, with probability at least $1-\nu(\lambda)$ over $(pk,sk)\leftarrow\mathrm{Setup}(1^\lambda)$,
--   $$\forall r,\ \forall c'\in\{0,1\}^n:\quad \delta(\mathrm{Encode}(pk;r),c')\le p\ \Longrightarrow\ \mathrm{Decode}(sk,c')=1 .$$
--   - **Pseudorandomness**: $(pk,\mathrm{Encode}(pk))$ and $(pk,U)$, with $U$ uniform on $\{0,1\}^n$, are computationally indistinguishable.
--   - **$\rho$-soundness**: for every $\lambda$ and every fixed $c'\in\{0,1\}^n$, $\Pr[\mathrm{Decode}(sk,c')=1]\le\rho(\lambda)$ over the setup randomness; **negligible soundness** means $\rho$-soundness for some negligible $\rho$.
--
--   This is the hypothesis of the goal theorem and of Theorem 4.13, the inner code of the puncturable pseudorandom code.
--
--   **Formalization Note** Randomized algorithms take explicit coin strings and keys and codewords are fixed-length bit strings. $\delta\le p$ is written $\Delta\le p\cdot n$. Pseudorandomness is the published `NoisyOWMPC.CompClose` (nonuniform polynomial-size distinguishers). Efficiency asks polynomial running time on all inputs of the right lengths; polynomial key lengths follow from it.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definition 3.5, pp.17–18 (PDF pp.20–21)

import Mathlib
import Definitions.Def_NoisyOWMPC_CompClose
import Definitions.Def_NoisyOWMPC_wprob

set_option autoImplicit false

namespace SeededShannon

open LaconicBarrier NoisyOWMPC

/-- A **zero-bit public-key pseudorandom code** `Π_PRC` on codeword space `{0,1}^{n(λ)}` (Dujmovic,
Lu, Silbak, Wichs, *Shannon Rate Seeded Codes from Indistinguishability Obfuscation*, STOC 2027
submission (manuscript sha256 52f4b606…a769709), Definition 3.5, pp.17–18):
`Setup(1^λ) → (pk, sk)`, a randomized `Encode(pk) → c ∈ {0,1}^n`, and a deterministic
`Decode(sk, c′) → b ∈ {0,1}`.

**Formalization Note** The randomized algorithms take explicit coin strings: `setup λ ρ` is the key
pair under setup coins `ρ ∈ {0,1}^{setupCoins λ}`, `encode λ pk r` the codeword `Encode(pk; r)`
under encoding coins `r ∈ {0,1}^{encCoins λ}`. Keys and codewords are fixed-length bit strings, so
the paper's "returns 0 on a malformed input" has no instance. -/
structure ZeroBitPRC where
  /-- the codeword length `n(λ)` (written `ℓprc` in §4) -/
  n : ℕ → ℕ
  /-- the number of coins of `Setup(1^λ)` -/
  setupCoins : ℕ → ℕ
  /-- the public-key length -/
  pkLen : ℕ → ℕ
  /-- the secret-key length -/
  skLen : ℕ → ℕ
  /-- `Setup(1^λ; ρ) = (pk, sk)` -/
  setup : (lam : ℕ) → (Fin (setupCoins lam) → Bool) →
    (Fin (pkLen lam) → Bool) × (Fin (skLen lam) → Bool)
  /-- the number of coins of `Encode(pk)` -/
  encCoins : ℕ → ℕ
  /-- `Encode(pk; r) ∈ {0,1}^{n(λ)}` -/
  encode : (lam : ℕ) → (Fin (pkLen lam) → Bool) → (Fin (encCoins lam) → Bool) → Fin (n lam) → Bool
  /-- `Decode(sk, c′) ∈ {0,1}` (deterministic) -/
  decode : (lam : ℕ) → (Fin (skLen lam) → Bool) → (Fin (n lam) → Bool) → Bool

/-- The algorithms of `Π_PRC` are **efficient** (Definition 3.5, p.17: "a tuple of efficient
algorithms"): polynomially many coins, and one polynomial-time machine each for `Setup`,
`Encode` and `Decode`.

**Formalization Note** Each algorithm is one uniform machine of the published
`LaconicBarrier.PolyTimeOn` model, run on its inputs and its coin string. Polynomial key lengths
follow from the polynomial running time of `Setup`. -/
def ZeroBitPRC.IsEfficient (P : ZeroBitPRC) : Prop :=
  PolyBounded P.setupCoins ∧ PolyBounded P.encCoins ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (P.setupCoins lam) → Bool)) (fun i => [unary i.1, bits i.2])
    (fun i => QAdvFew.PoQOracle.tup [bits (P.setup i.1 i.2).1, bits (P.setup i.1 i.2).2]) ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (P.pkLen lam) → Bool) × (Fin (P.encCoins lam) → Bool))
    (fun i => [unary i.1, bits i.2.1, bits i.2.2]) (fun i => bits (P.encode i.1 i.2.1 i.2.2)) ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (P.skLen lam) → Bool) × (Fin (P.n lam) → Bool))
    (fun i => [unary i.1, bits i.2.1, bits i.2.2]) (fun i => [P.decode i.1 i.2.1 i.2.2])

/-- **Strong `p`-robustness** (Definition 3.5, p.18): there is a negligible `ν` such that for every
`λ`, with probability at least `1 − ν(λ)` over `(pk, sk) ← Setup(1^λ)`, for **all** encoding coins
`r` and all `c′ ∈ {0,1}^n` with `δ(Encode(pk; r), c′) ≤ p`, `Decode(sk, c′) = 1`.

**Formalization Note** The relative distance condition `δ ≤ p` is written `Δ ≤ p · n` (the same
for `n ≥ 1`; at `n = 0` both hold). The failure event is the complement of the paper's event, so
"probability `1 − negl`" becomes "failure probability `≤ ν(λ)`". -/
def ZeroBitPRC.StronglyRobust (P : ZeroBitPRC) (p : ℝ) : Prop :=
  ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
    wprob (unifW (Fin (P.setupCoins lam) → Bool)) (fun ρ =>
      ¬ ∀ (r : Fin (P.encCoins lam) → Bool) (c' : Fin (P.n lam) → Bool),
        (hammingDist (P.encode lam (P.setup lam ρ).1 r) c' : ℝ) ≤ p * P.n lam →
          P.decode lam (P.setup lam ρ).2 c' = true) ≤ ν lam

/-- **Pseudorandomness** (Definition 3.5, p.18): `(pk, Encode(pk)) ≈^c (pk, U)` for
`(pk, sk) ← Setup(1^λ)` and an independent uniform `U ∈ {0,1}^n`, against every nonuniform
polynomial-size distinguisher.

**Formalization Note** This is the published `NoisyOWMPC.CompClose` with error `0`; the
distinguisher receives the tuple encoding of `(pk, c)`. -/
def ZeroBitPRC.Pseudorandom (P : ZeroBitPRC) : Prop :=
  CompClose (I := fun _ => Unit)
    (Ω₀ := fun lam => (Fin (P.setupCoins lam) → Bool) × (Fin (P.encCoins lam) → Bool))
    (Ω₁ := fun lam => (Fin (P.setupCoins lam) → Bool) × (Fin (P.n lam) → Bool))
    (fun _ _ => unifW _)
    (fun lam _ ω => QAdvFew.PoQOracle.tup
      [bits (P.setup lam ω.1).1, bits (P.encode lam (P.setup lam ω.1).1 ω.2)])
    (fun _ _ => unifW _)
    (fun lam _ ω => QAdvFew.PoQOracle.tup [bits (P.setup lam ω.1).1, bits ω.2])
    (fun _ => 0)

/-- **`ρ`-soundness** (Definition 3.5, p.18): for every `λ` and every fixed `c′ ∈ {0,1}^n`,
`Pr[Decode(sk, c′) = 1 : (pk, sk) ← Setup(1^λ)] ≤ ρ(λ)`. -/
def ZeroBitPRC.IsSound (P : ZeroBitPRC) (ρ : ℕ → ℝ) : Prop :=
  ∀ (lam : ℕ) (c' : Fin (P.n lam) → Bool),
    wprob (unifW (Fin (P.setupCoins lam) → Bool))
      (fun s => P.decode lam (P.setup lam s).2 c' = true) ≤ ρ lam

/-- **Negligible soundness error** (Definition 3.5, p.18: "We omit parameterization of
`ρ`-soundness if `ρ` is simply negligible"): `Π_PRC` is `ρ`-sound for a negligible `ρ`, chosen
before `λ` and `c′`. -/
def ZeroBitPRC.NegligiblySound (P : ZeroBitPRC) : Prop :=
  ∃ ρ : ℕ → ℝ, Negligible ρ ∧ P.IsSound ρ

end SeededShannon


