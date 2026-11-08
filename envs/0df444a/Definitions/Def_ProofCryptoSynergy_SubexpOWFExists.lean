-- Prove2me | Definitions.Def_ProofCryptoSynergy_SubexpOWFExists
-- name    : ProofCryptoSynergy_SubexpOWFExists
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:04:10.273982+00:00
-- url     : https://prove2.me/theorems/2a23fdc2-e740-4e82-bab4-6ef346848d69
-- title:
--   Subexponentially secure one-way functions
-- statement:
--   A polynomial-time $f$ such that for some $\delta>0$ and all large $n$, every circuit of size at most $2^{n^\delta}$ finds a preimage of $f(x)$, for uniform $x\in\{0,1\}^n$, with probability at most $2^{-n^\delta}$.
--
--   **Formalization Note** The paper uses this without defining it; the definition follows the format of its Definition 18.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 36, p.33 (PDF 35)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_LaconicBarrier_coinAvg

open LaconicBarrier

namespace ProofCryptoSynergy

/-- `f` is a **subexponentially secure one-way function** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 36, p.33 (PDF 35)): computable in polynomial time, and
there is `δ > 0` such that for all large `n`, every circuit of size at most `2^{n^δ}` inverts `f` on `x ∈ {0,1}ⁿ` with probability at
most `2^{-n^δ}`.

**Formalization Note** The paper uses this without defining it; the definition follows the format of Definition 18 (`∃ δ > 0`,
nonuniform adversaries). The adversary is any multi-output circuit; it reads `f(x)` through `padIn` and succeeds when its output is a
preimage of `f(x)`. -/
def IsSubexpOWF (f : List Bool → List Bool) : Prop :=
  PolyTimeOn (ι := List Bool) (fun x => [x]) f ∧
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ (m : ℕ) (C : MCircuit m),
    (C.size : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ δ) →
    coinAvg n (fun ρ => if f (C.eval (padIn m (f (bits ρ)))) = f (bits ρ) then 1 else 0) ≤
      (2 : ℝ) ^ (-((n : ℝ) ^ δ))

/-- **Subexponentially secure one-way functions exist** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 36, p.33 (PDF 35)). -/
def SubexpOWFExists : Prop := ∃ f, IsSubexpOWF f

end ProofCryptoSynergy


