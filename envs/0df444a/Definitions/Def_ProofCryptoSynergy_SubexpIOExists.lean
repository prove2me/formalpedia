-- Prove2me | Definitions.Def_ProofCryptoSynergy_SubexpIOExists
-- name    : ProofCryptoSynergy_SubexpIOExists
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:05:44.821912+00:00
-- url     : https://prove2.me/theorems/60f52961-7cbe-4c09-a4a2-3cd805d76548
-- title:
--   Subexponentially secure indistinguishability obfuscation
-- statement:
--   A **subexponentially secure indistinguishability obfuscator** is a randomized polynomial-time algorithm $i\mathcal O$ that, given a circuit $C:\{0,1\}^n\to\{0,1\}$ and $1^\lambda$, outputs a functionally equivalent circuit, for all coins, such that for every polynomial $p$ there is $\delta>0$ with the following property: for all large $\lambda$ and functionally equivalent $C_1,C_2$ with $|C_1|=|C_2|\le p(\lambda)$,
--   $$i\mathcal O(C_1,1^\lambda)\approx_{2^{-\lambda^\delta}} i\mathcal O(C_2,1^\lambda).$$
--
--   **Formalization Note** "Inverse subexponential $\varepsilon(\lambda)$" is read as the form the paper's proofs use (some $2^{-\lambda^\delta}$). The syntax is the published `LaconicBarrier.IOScheme`; its `IsIO` is not used, since that has negligible-error correctness and no security clause.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 12, p.19 (PDF 21)

import Mathlib
import Definitions.Def_LaconicBarrier_IOScheme
import Definitions.Def_ProofCryptoSynergy_Indist

open KarpLiptonOM LaconicBarrier

namespace ProofCryptoSynergy

/-- The distribution `iO(C, 1^λ)` of the code of the obfuscated circuit. -/
def obfSampler (O : IOScheme) (lam : ℕ) {n : ℕ} (C : Circuit n) : Sampler where
  coins := O.coins lam n C.gates.length
  out r := circCode (O.obf lam n C.gates.length C (fun i => r.getD i false))

/-- **Subexponentially secure indistinguishability obfuscator** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 12, p.19 (PDF 21)): a
polynomial-time randomized algorithm `iO` that, given a circuit `C : {0,1}ⁿ → {0,1}` and `1^λ`, outputs a
functionally equivalent circuit, such that for all sufficiently large `λ` and functionally equivalent
`C₁, C₂` with `|C₁| = |C₂| ≤ poly(λ)`, `iO(C₁, 1^λ) ≈_{ε(λ)} iO(C₂, 1^λ)`.

**Formalization Note**
1. Correctness is perfect: the printed "outputs a functionally equivalent circuit" holds for all coins.
2. "Inverse subexponential `ε(λ)`" is read as the form the paper's proofs use (Definition 14, Definition 18,
   Lemma 22, Lemma 32): for each polynomial size bound `p` there is `δ > 0` with security `2^{-λ^δ}` against
   circuits of size `2^{λ^δ}`, for all large `λ`. `δ` may depend on `p`.
3. `|C|` is the number of gates; the number `n` of inputs is not bounded separately. -/
def IsSubexpIO (O : IOScheme) : Prop :=
  (∃ c : ℕ, ∀ lam n s, O.coins lam n s ≤ (lam + n + s + 2) ^ c) ∧
  PolyTimeOn (ι := (lam : ℕ) × (n : ℕ) × (C : Circuit n) ×
      (Fin (O.coins lam n C.gates.length) → Bool))
    (fun i => [unary i.1, circCode i.2.2.1, bits i.2.2.2])
    (fun i => circCode (O.obf i.1 i.2.1 i.2.2.1.gates.length i.2.2.1 i.2.2.2)) ∧
  (∀ (lam n : ℕ) (C : Circuit n) (ρ : Fin (O.coins lam n C.gates.length) → Bool) (u : List Bool),
    u.length = n → (O.obf lam n C.gates.length C ρ).eval u = C.eval u) ∧
  ∀ p : Polynomial ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ lam : ℕ in Filter.atTop,
    ∀ (n : ℕ) (C₁ C₂ : Circuit n), (∀ u : List Bool, u.length = n → C₁.eval u = C₂.eval u) →
      C₁.gates.length = C₂.gates.length → C₁.gates.length ≤ p.eval lam →
      Indist ((2 : ℝ) ^ (-((lam : ℝ) ^ δ))) (obfSampler O lam C₁) (obfSampler O lam C₂)

/-- **There exists a subexponentially secure iO** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Corollary 45, assumption 1, p.38 (PDF 40)). -/
def SubexpIOExists : Prop := ∃ O : IOScheme, IsSubexpIO O

end ProofCryptoSynergy


