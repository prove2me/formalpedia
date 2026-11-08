-- Prove2me | Definitions.Def_ProofCryptoSynergy_HasSimulator
-- name    : ProofCryptoSynergy_HasSimulator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:06:49.822198+00:00
-- url     : https://prove2.me/theorems/1fd88441-67a6-4cb2-b0f3-438afc73bc65
-- title:
--   $s$-size $\varepsilon$-indistinguishable simulators
-- statement:
--   A randomized prover $P(\varphi,w,1^\lambda)$ has an **$s$-size $\varepsilon$-indistinguishable simulator on $\lambda$** if there is a size-$s$ randomized circuit $S_\lambda$ such that for all satisfiable $\varphi$ of size at most $\lambda$ and any satisfying assignment $w$,
--   $$S_\lambda(\varphi)\approx_\varepsilon P(\varphi,w,1^\lambda).$$
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 17, p.21 (PDF 23)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_TAUT
import Definitions.Def_ProofCryptoSynergy_Indist

open LaconicBarrier

namespace ProofCryptoSynergy

/-- The prover `P` has an **`s`-size `ε`-indistinguishable simulator on `λ`** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 17, p.21 (PDF 23)):
there is a size-`s` randomized circuit `S_λ` such that for all satisfiable `φ` of size at most `λ` and any satisfying
assignment `w` for `φ`, `S_λ(φ) ≈_ε P(φ, w, 1^λ)`.

**Formalization Note** A randomized circuit is a multi-output circuit on `(φ, r)` with `n` inputs for `φ`, read through
`padIn n`, and `m` for coins; its fixed-length output is read as a string by `unpadOut`. The prover is any family of
distributions indexed by `(φ, w, λ)`. -/
def HasSimulator (P : List Bool → List Bool → ℕ → Sampler) (lam s : ℕ) (ε : ℝ) : Prop :=
  ∃ (n m : ℕ) (S : MCircuit (n + m)), S.size ≤ s ∧
    ∀ φ w : List Bool, φ.length ≤ lam → holds φ w →
      Indist ε ⟨m, fun r => unpadOut (S.eval (padIn n φ ++ r))⟩ (P φ w lam)

end ProofCryptoSynergy


