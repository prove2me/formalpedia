-- Prove2me | Definitions.Def_ProofCryptoSynergy_Indist
-- name    : ProofCryptoSynergy_Indist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:04:34.581116+00:00
-- url     : https://prove2.me/theorems/d95ea870-62c6-4204-bf80-de8adb817fa3
-- title:
--   Nonuniform computational indistinguishability $\mathcal D\approx_\varepsilon\mathcal D'$
-- statement:
--   A distribution over $\{0,1\}^*$ is given by a sampler, the image of uniform coins. Two distributions are **$\varepsilon$-indistinguishable** if every boolean circuit $A$ of size at most $\varepsilon^{-1}$ has
--   $$\bigl|\Pr_{x\sim\mathcal D}[A(x)=1]-\Pr_{x\sim\mathcal D'}[A(x)=1]\bigr|<\varepsilon.$$
--
--   **Formalization Note** A circuit with $k$ inputs reads $x$ through the published padding $x10\cdots0$ cut to length $k$, for every $k$. Size is the number of gates.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 11, p.19 (PDF 21)

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit_eval
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_LaconicBarrier_coinAvg

open KarpLiptonOM LaconicBarrier

namespace ProofCryptoSynergy

/-- A distribution over `{0,1}*` given by a sampler: the image of uniform coins of length `coins`
under `out`. -/
structure Sampler where
  /-- the number of coins -/
  coins : ℕ
  /-- the output on a coin string of length `coins` -/
  out : List Bool → List Bool

/-- `Pr_{x∼D}[A(x) = 1]`, for a circuit with `k` inputs reading the string through `padIn k`. -/
noncomputable def Sampler.acc (D : Sampler) {k : ℕ} (A : Circuit k) : ℝ :=
  coinAvg D.coins fun ρ => if A.eval (padIn k (D.out (bits ρ))) = true then 1 else 0

/-- **Nonuniform computational indistinguishability** `D ≈_ε D'` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 11, p.19 (PDF 21)): for
every boolean circuit `A` of size at most `s = ε⁻¹`, `|Pr_{x∼D}[A(x) = 1] − Pr_{x∼D'}[A(x) = 1]| < ε`.

**Formalization Note** The distributions are over `{0,1}*` and a circuit has a fixed number of inputs, so
`A` has any number `k` of inputs and reads `padIn k x`; size is the number of gates. Probabilities are
averages over coins (`coinAvg`). Adversaries are nonuniform, as p.19 says throughout. -/
def Indist (ε : ℝ) (D D' : Sampler) : Prop :=
  ∀ (k : ℕ) (A : Circuit k), (A.gates.length : ℝ) ≤ ε⁻¹ → |D.acc A - D'.acc A| < ε

end ProofCryptoSynergy


