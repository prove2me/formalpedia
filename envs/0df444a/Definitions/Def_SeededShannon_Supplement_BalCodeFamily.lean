-- Prove2me | Definitions.Def_SeededShannon_Supplement_BalCodeFamily
-- name    : SeededShannon_Supplement_BalCodeFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:36:35.322351+00:00
-- url     : https://prove2.me/theorems/2ec3421f-1d2e-43c2-9d17-65329269d8f4
-- title:
--   A block-length-indexed binary code family with the guarantees of Theorem 3.14
-- statement:
--   A **code family indexed by the block length** consists, for every $n$, of an encoder $\mathrm{Encode}_n:\{0,1\}^{k_{\mathrm{bal}}(n)}\to\{0,1\}^n$, a list decoder $\mathrm{ListDec}_n$ and a list bound $L_{\mathrm{bal}}(n)$.
--
--   The family **has the guarantees of Theorem 3.14** at block size $b$, radius $\tau$, imbalance $\gamma$ and slack $\zeta$, from the length $n_0$ on, if:
--   1. for every $n\ge n_0$ divisible by $b$, $\mathrm{Encode}_n$ is injective and binary-linear, has rate $k_{\mathrm{bal}}(n)/n\ge 1-H(\tau)-\zeta$, and $(\mathrm{ListDec}_n,L_{\mathrm{bal}}(n))$ list-decodes $(b,\tau,\gamma)$-balanced errors (Definition 3.13);
--   2. $L_{\mathrm{bal}}(n)=\mathrm{poly}(n)$;
--   3. construction ($1^n\mapsto 1^{k_{\mathrm{bal}}(n)}$), encoding and list decoding are deterministic and run in time $\mathrm{poly}(n)$.
--
--   This is the balanced code $\Pi_{\mathrm{code}}$ that Construction 6.1 takes as an ingredient: the conclusion of the published Theorem 3.14 for one family.
--
--   **Formalization Note** $H$ is the binary entropy in bits.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Construction 6.1, p.37 (PDF p.40); Theorem 3.14, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_SeededShannon_balP

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier NoisyOWMPC SeededShannon

/-- A **family of binary codes indexed by the block length** `n`, with message length `k_bal(n)`,
encoder `Encode_n : {0,1}^{k_bal(n)} → {0,1}^n`, list decoder `ListDec_n` and list bound
`L_bal(n)` (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission (manuscript sha256 52f4b606…a769709),
Construction 6.1, p.37: "For each sufficiently large multiple `N` of `b`, let `Π_code` be the
`(b, τ, γ)`-balanced code of Theorem 3.14 … with message length `k_bal(N)` and list bound
`L_bal(N)`"). -/
structure BalCodeFamily where
  /-- the message length `k_bal(n)` -/
  kbal : ℕ → ℕ
  /-- the list bound `L_bal(n)` -/
  Lbal : ℕ → ℕ
  /-- `Encode_n` -/
  enc : (n : ℕ) → (Fin (kbal n) → Bool) → Fin n → Bool
  /-- `ListDec_n` -/
  dec : (n : ℕ) → (Fin n → Bool) → List (Fin (kbal n) → Bool)

/-- The family has **the guarantees of Theorem 3.14** at block size `b`, radius `τ`, imbalance `γ`
and rate slack `ζ`, from the length `n₀` on (Theorem 3.14, p.21, as published in
`SeededShannon.theorem_3_14`): for every `n ≥ n₀` divisible by `b`, `Encode_n` is injective and
binary-linear, has rate at least `1 − H(τ) − ζ`, and `(ListDec_n, L_bal(n))` list-decodes
`(b, τ, γ)`-balanced errors; `L_bal(n) = poly(n)`; construction (`1^n ↦ 1^{k_bal(n)}`), encoding and
list decoding are deterministic and run in time `poly(n)`.

**Formalization Note** This is the conclusion of the published `SeededShannon.theorem_3_14` for one
code family, so that Construction 6.1 can take "the balanced code of Theorem 3.14" as an
ingredient. `H` is the binary entropy in bits. -/
def BalCodeFamily.IsBalancedCode (F : BalCodeFamily) (b : ℕ) (τ γ ζ : ℝ) (n₀ : ℕ) : Prop :=
  PolyBounded F.Lbal ∧
  (∀ n ≥ n₀, b ∣ n →
    Function.Injective (F.enc n) ∧
    (∀ x y : Fin (F.kbal n) → Bool,
      F.enc n (fun i => xor (x i) (y i)) = fun j => xor (F.enc n x j) (F.enc n y j)) ∧
    1 - WildeQIT.binaryEntropy τ - ζ ≤ (F.kbal n : ℝ) / n ∧
    BalancedListDecodable b τ γ (F.enc n) (F.dec n) (F.Lbal n)) ∧
  PolyTimeOn (ι := {n : ℕ // n₀ ≤ n ∧ b ∣ n}) (fun n => [unary n.1]) (fun n => unary (F.kbal n.1)) ∧
  PolyTimeOn (ι := (n : {n : ℕ // n₀ ≤ n ∧ b ∣ n}) × (Fin (F.kbal n.1) → Bool))
    (fun i => [unary i.1.1, bits i.2]) (fun i => bits (F.enc i.1.1 i.2)) ∧
  PolyTimeOn (ι := (n : {n : ℕ // n₀ ≤ n ∧ b ∣ n}) × (Fin n.1 → Bool))
    (fun i => [unary i.1.1, bits i.2])
    (fun i => QAdvFew.PoQOracle.tup ((F.dec i.1.1 i.2).map bits))

end SeededShannon.Supplement


