-- Prove2me | Definitions.Def_ProofCryptoSynergy_SubexpRandNIWIExists
-- name    : ProofCryptoSynergy_SubexpRandNIWIExists
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:06:32.687287+00:00
-- url     : https://prove2.me/theorems/aa5f726e-6397-4ab6-b950-5601417dc7cd
-- title:
--   NIWIs with randomized verifiers and negligible soundness error
-- statement:
--   A pair of randomized polynomial-time algorithms $(P,V)$ with completeness with probability $1$ over both, a negligible $\mu$ with $\Pr_V[V(\varphi,\pi,1^\lambda)=1]\le\mu(\lambda)$ for all $\lambda$, unsatisfiable $\varphi$ with $|\varphi|\le\lambda$, and $\pi$, and witness indistinguishability as for a NIWI.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 16, p.21 (PDF 23)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_TAUT
import Definitions.Def_ProofCryptoSynergy_Indist

open LaconicBarrier

namespace ProofCryptoSynergy

/-- A negligible function: eventually below every inverse polynomial. -/
def IsNegligible (μ : ℕ → ℝ) : Prop :=
  ∀ e : ℕ, ∀ᶠ lam : ℕ in Filter.atTop, μ lam ≤ (((lam : ℝ) + 2) ^ e)⁻¹

/-- The data of a NIWI with a randomized verifier: `P(φ, w, 1^λ; r)` and `V(φ, π, 1^λ; r')`. -/
structure RandNIWIScheme where
  /-- the number of coins of the prover at `(|φ|, |w|, λ)` -/
  pcoins : ℕ → ℕ → ℕ → ℕ
  /-- the prover -/
  P : List Bool → List Bool → ℕ → List Bool → List Bool
  /-- the number of coins of the verifier at `(|φ|, |π|, λ)` -/
  vcoins : ℕ → ℕ → ℕ → ℕ
  /-- the verifier -/
  V : List Bool → List Bool → ℕ → List Bool → Bool

/-- **Subexponentially secure NIWI with a randomized verifier and negligible soundness error** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 16,
p.21 (PDF 23)): a pair of randomized polynomial-time algorithms; completeness with probability `1` over both;
negligible `µ` with `Pr_V[V(φ, π, 1^λ) = 1] ≤ µ(λ)` for all `λ`, unsatisfiable `φ` with `|φ| ≤ λ`, and `π`; and witness
indistinguishability as in Definition 14.

**Formalization Note** Witness indistinguishability as in `IsSubexpNIWI`. -/
def IsSubexpRandNIWI (N : RandNIWIScheme) : Prop :=
  (∃ c : ℕ, ∀ a b l, N.pcoins a b l ≤ (a + b + l + 2) ^ c) ∧
  (∃ c : ℕ, ∀ a b l, N.vcoins a b l ≤ (a + b + l + 2) ^ c) ∧
  PolyTimeOn (ι := {i : List Bool × List Bool × ℕ × List Bool //
      i.2.2.2.length = N.pcoins i.1.length i.2.1.length i.2.2.1})
    (fun i => [i.1.1, i.1.2.1, unary i.1.2.2.1, i.1.2.2.2])
    (fun i => N.P i.1.1 i.1.2.1 i.1.2.2.1 i.1.2.2.2) ∧
  PolyTimeOn (ι := {i : List Bool × List Bool × ℕ × List Bool //
      i.2.2.2.length = N.vcoins i.1.length i.2.1.length i.2.2.1})
    (fun i => [i.1.1, i.1.2.1, unary i.1.2.2.1, i.1.2.2.2])
    (fun i => [N.V i.1.1 i.1.2.1 i.1.2.2.1 i.1.2.2.2]) ∧
  (∀ (φ w : List Bool) (lam : ℕ) (r : List Bool), holds φ w →
    r.length = N.pcoins φ.length w.length lam → ∀ r' : List Bool,
      r'.length = N.vcoins φ.length (N.P φ w lam r).length lam →
      N.V φ (N.P φ w lam r) lam r' = true) ∧
  (∃ μ : ℕ → ℝ, IsNegligible μ ∧ ∀ (lam : ℕ) (φ π : List Bool), φ ∉ SAT → φ.length ≤ lam →
    coinAvg (N.vcoins φ.length π.length lam)
      (fun ρ => if N.V φ π lam (bits ρ) = true then 1 else 0) ≤ μ lam) ∧
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ lam : ℕ in Filter.atTop, ∀ φ w w' : List Bool, holds φ w → holds φ w' →
    Indist ((2 : ℝ) ^ (-((lam : ℝ) ^ δ)))
      ⟨N.pcoins φ.length w.length lam, N.P φ w lam⟩
      ⟨N.pcoins φ.length w'.length lam, N.P φ w' lam⟩

/-- There exist subexponentially secure NIWIs with randomized verifiers and negligible soundness error
(Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 16, p.21 (PDF 23)). -/
def SubexpRandNIWIExists : Prop := ∃ N : RandNIWIScheme, IsSubexpRandNIWI N

end ProofCryptoSynergy


