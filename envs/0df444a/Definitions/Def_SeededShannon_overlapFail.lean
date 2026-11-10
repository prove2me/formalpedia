-- Prove2me | Definitions.Def_SeededShannon_overlapFail
-- name    : SeededShannon_overlapFail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:57.916254+00:00
-- url     : https://prove2.me/theorems/7a0ba9b4-ac61-4582-acf6-99bc66292ee1
-- title:
--   Decoding-overlap failure probability over $q$ keys (Lemma 3.8)
-- statement:
--   Let $\Pi_{\mathrm{PRC}}$ be a zero-bit public-key PRC with codeword length $\ell_{\mathrm{prc}}$. For $q=q(\lambda)$ independent key pairs $(pk_j,sk_j)\leftarrow\mathrm{Setup}(1^\lambda)$, $j\in[q]$, and $\ell_0\in\mathbb N$, the **overlap failure probability** is
--   $$\Pr\Big[\exists w\in\{0,1\}^{\ell_{\mathrm{prc}}}:\ \big|\{j\in[q]:\mathrm{Decode}(sk_j,w)=1\}\big|>\ell_0\Big].$$
--   $\Pi_{\mathrm{PRC}}$ has **$\ell_0$-bounded decoding overlap over $q$ keys** when this probability is negligible: with overwhelming probability no word is accepted by more than $\ell_0$ of the keys.
--
--   It is the quantity bounded by Lemma 3.8 and used to bound the symbol lists of the puncturable pseudorandom code.
--
--   **Formalization Note** The $q$ independent setups use $q$ independent uniform coin strings.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Lemma 3.8, p.19 (PDF p.22)

import Mathlib
import Definitions.Def_SeededShannon_ZeroBitPRC

set_option autoImplicit false

namespace SeededShannon

open NoisyOWMPC

open Classical in
/-- The **decoding-overlap failure probability** of a zero-bit PRC over `q` keys (Dujmovic, Lu,
Silbak, Wichs, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Lemma 3.8, p.19): for
`q = q(λ)` independent key pairs `(pk_j, sk_j) ← Setup(1^λ)`, `j ∈ [q]`, the probability that some
word `w ∈ {0,1}^{ℓprc}` is accepted by more than `ℓ0` of the keys,
`Pr[∃ w : |{j ∈ [q] : Decode(sk_j, w) = 1}| > ℓ0]`.

`Π_PRC` has `ℓ0`-bounded decoding overlap over `q` keys when this probability is negligible.

**Formalization Note** The `q` independent setups use `q` independent uniform coin strings. -/
noncomputable def overlapFail (P : ZeroBitPRC) (q : ℕ → ℕ) (ℓ0 lam : ℕ) : ℝ :=
  wprob (unifW (Fin (q lam) → Fin (P.setupCoins lam) → Bool)) (fun ω =>
    ∃ w : Fin (P.n lam) → Bool,
      ℓ0 < (Finset.univ.filter (fun j => P.decode lam (P.setup lam (ω j)).2 w = true)).card)

end SeededShannon


