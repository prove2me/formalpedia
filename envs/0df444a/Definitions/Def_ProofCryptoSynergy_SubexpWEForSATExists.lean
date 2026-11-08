-- Prove2me | Definitions.Def_ProofCryptoSynergy_SubexpWEForSATExists
-- name    : ProofCryptoSynergy_SubexpWEForSATExists
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:06:39.693288+00:00
-- url     : https://prove2.me/theorems/d137112c-8879-4e7c-a140-36822d537afb
-- title:
--   Subexponentially secure witness encryption for $\mathrm{SAT}$
-- statement:
--   A **subexponentially secure witness encryption scheme for SAT** is a pair of uniform polynomial-time algorithms: $\mathrm{Enc}(x,b;r)$ outputs a ciphertext of length $\ell(|x|)$ and $\mathrm{Dec}(x,w,c)\in\{0,1,\bot\}$, such that for all large $n$: if $x\in\{0,1\}^n$ and $x(w)=1$ then $\mathrm{Dec}(x,w,\mathrm{Enc}(x,b;r))=b$ for all $b,r$; and for some $\delta>0$, if $x\in\{0,1\}^n\setminus\mathrm{SAT}$ then
--   $$(x,\mathrm{Enc}(x,1;r))\approx_{2^{-n^\delta}}(x,\mathrm{Enc}(x,0;r)).$$
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 13, p.20 (PDF 22)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_TAUT
import Definitions.Def_ProofCryptoSynergy_Indist

open LaconicBarrier

namespace ProofCryptoSynergy

/-- The data of a witness encryption scheme for SAT: `Enc(x, b; r)` with `coins(|x|)` coins and ciphertext
length `ell(|x|)`, and the deterministic `Dec(x, w, c) ∈ {0, 1, ⊥}` (`none` is `⊥`). -/
structure WEForSAT where
  /-- the ciphertext length -/
  ell : ℕ → ℕ
  /-- the number of coins of `Enc` -/
  coins : ℕ → ℕ
  /-- the encryptor -/
  enc : List Bool → Bool → List Bool → List Bool
  /-- the decryptor -/
  dec : List Bool → List Bool → List Bool → Option Bool

/-- **Subexponentially secure witness encryption for SAT** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 13, p.20 (PDF 22)): uniform
polynomial-time `Enc`, `Dec`; correctness: for all large `n`, all `b`, `x ∈ {0,1}ⁿ ∩ SAT`, and `w` with `φ(w) = 1`,
`Pr_r[Dec(x, w, Enc(x, b; r)) = b] = 1`; security: for all large `n` and `x ∈ {0,1}ⁿ \ SAT`,
`(x, Enc(x, 1; r)) ≈_ε (x, Enc(x, 0; r))`.

**Formalization Note** The pair `(x, c)` is the concatenation, since `|x| = n` is public. "Inverse subexponential
`ε`" is read as `∃ δ > 0`, `ε(n) = 2^{-n^δ}`, as in `IsSubexpIO`. The published `LaconicBarrier.WEScheme` is not reused:
its `Enc` takes a separate `1^λ`, its `Dec` is randomized, and its correctness has negligible error. -/
def IsSubexpWE (E : WEForSAT) : Prop :=
  (∃ c : ℕ, ∀ n, E.coins n ≤ (n + 2) ^ c) ∧
  PolyTimeOn (ι := {i : List Bool × Bool × List Bool // i.2.2.length = E.coins i.1.length})
    (fun i => [i.1.1, [i.1.2.1], i.1.2.2]) (fun i => E.enc i.1.1 i.1.2.1 i.1.2.2) ∧
  PolyTimeOn (ι := List Bool × List Bool × List Bool)
    (fun i => [i.1, i.2.1, i.2.2]) (fun i => (E.dec i.1 i.2.1 i.2.2).toList) ∧
  (∀ (x : List Bool) (b : Bool) (r : List Bool), r.length = E.coins x.length →
    (E.enc x b r).length = E.ell x.length) ∧
  (∀ᶠ n : ℕ in Filter.atTop, ∀ (b : Bool) (x w r : List Bool), x.length = n → holds x w →
    r.length = E.coins n → E.dec x w (E.enc x b r) = some b) ∧
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ x : List Bool, x.length = n → x ∉ SAT →
    Indist ((2 : ℝ) ^ (-((n : ℝ) ^ δ)))
      ⟨E.coins n, fun r => x ++ E.enc x true r⟩ ⟨E.coins n, fun r => x ++ E.enc x false r⟩

/-- **Subexponentially secure WE exists for SAT** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 35, hypothesis 1, p.31 (PDF 33)). -/
def SubexpWEForSATExists : Prop := ∃ E : WEForSAT, IsSubexpWE E

end ProofCryptoSynergy


