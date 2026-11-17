-- Prove2me | Definitions.Def_ProofCryptoSynergy_Supplement_PolyIOExists
-- name    : ProofCryptoSynergy_Supplement_PolyIOExists
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:48:33.90701+00:00
-- url     : https://prove2.me/theorems/940083ec-4a9d-4159-bb42-7b2502d27816
-- title:
--   Polynomially secure indistinguishability obfuscation
-- statement:
--   A **polynomially secure indistinguishability obfuscator** is a randomized polynomial-time algorithm $i\mathcal O$ that, given a circuit $C:\{0,1\}^n\to\{0,1\}$ and $1^\lambda$, outputs a functionally equivalent circuit, such that for every polynomial size bound $p$ and every inverse polynomial $\varepsilon(\lambda)=\lambda^{-c}$, for all sufficiently large $\lambda$ and functionally equivalent $C_1,C_2$ with $|C_1|=|C_2|\le p(\lambda)$,
--   $$i\mathcal O(C_1,1^\lambda)\approx_{\varepsilon(\lambda)} i\mathcal O(C_2,1^\lambda).$$
--
--   "iO exists" in Theorem 78 refers to this polynomial regime.
--
--   **Formalization Note** The data, the efficiency clauses and perfect correctness are those of the published `IsSubexpIO`; indistinguishability is the published nonuniform `Indist`.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 12, p.19 (PDF 21); Theorem 78, p.57 (PDF 59)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_SubexpIOExists

open KarpLiptonOM LaconicBarrier

namespace ProofCryptoSynergy.Supplement

/-- A **polynomially secure indistinguishability obfuscator** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 12, p.19 (PDF 21)): a
polynomial-time randomized algorithm `iO` that, given a circuit `C : {0,1}ⁿ → {0,1}` and `1^λ`, outputs a
functionally equivalent circuit, such that for all sufficiently large `λ`, functionally equivalent `C₁, C₂`
with `|C₁| = |C₂| ≤ poly(λ)`, and inverse polynomial `ε(λ)`, `iO(C₁, 1^λ) ≈_{ε(λ)} iO(C₂, 1^λ)`.

**Formalization Note** The data, the polynomial-time and polynomial-coins clauses and perfect correctness
are those of the published `IsSubexpIO`; only security differs: for every size polynomial `p` and every
`c ≥ 1`, for all large `λ`, the two obfuscations are `λ^{-c}`-indistinguishable (published `Indist`,
nonuniform adversaries of size at most `λ^c`). -/
def IsPolyIO (O : IOScheme) : Prop :=
  (∃ c : ℕ, ∀ lam n s, O.coins lam n s ≤ (lam + n + s + 2) ^ c) ∧
  PolyTimeOn (ι := (lam : ℕ) × (n : ℕ) × (C : Circuit n) ×
      (Fin (O.coins lam n C.gates.length) → Bool))
    (fun i => [unary i.1, circCode i.2.2.1, bits i.2.2.2])
    (fun i => circCode (O.obf i.1 i.2.1 i.2.2.1.gates.length i.2.2.1 i.2.2.2)) ∧
  (∀ (lam n : ℕ) (C : Circuit n) (ρ : Fin (O.coins lam n C.gates.length) → Bool) (u : List Bool),
    u.length = n → (O.obf lam n C.gates.length C ρ).eval u = C.eval u) ∧
  ∀ p : Polynomial ℕ, ∀ c : ℕ, 1 ≤ c → ∀ᶠ lam : ℕ in Filter.atTop,
    ∀ (n : ℕ) (C₁ C₂ : Circuit n), (∀ u : List Bool, u.length = n → C₁.eval u = C₂.eval u) →
      C₁.gates.length = C₂.gates.length → C₁.gates.length ≤ p.eval lam →
      Indist (((lam : ℝ) ^ c)⁻¹) (obfSampler O lam C₁) (obfSampler O lam C₂)

/-- **iO exists** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 78, first item, p.57 (PDF 59)): Section 6 is the polynomial regime, so
the obfuscator is polynomially secure. -/
def PolyIOExists : Prop := ∃ O : IOScheme, IsPolyIO O

end ProofCryptoSynergy.Supplement


