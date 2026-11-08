-- Prove2me | Definitions.Def_ProofCryptoSynergy_NIWIScheme
-- name    : ProofCryptoSynergy_NIWIScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:06:16.319642+00:00
-- url     : https://prove2.me/theorems/65460718-d87a-4a4d-8a62-e4fe24b28143
-- title:
--   Non-interactive witness indistinguishable proof systems
-- statement:
--   A **NIWI proof system** is a pair $(P,V)$ of uniform algorithms, $P$ randomized polynomial-time and $V$ deterministic, with:
--   1. **completeness**: if $\varphi(w)=1$ then $V(\varphi,P(\varphi,w,1^\lambda),1^\lambda)=1$ for all $\lambda$ and all coins;
--   2. **perfect soundness**: for all $\lambda$, unsatisfiable $\varphi$ with $|\varphi|\le\lambda$ and all $\pi$, $V(\varphi,\pi,1^\lambda)=0$;
--   3. **witness indistinguishability**: for some $\delta>0$ and all large $\lambda$, if $\varphi(w)=\varphi(w')=1$ then $P(\varphi,w,1^\lambda)\approx_{2^{-\lambda^\delta}}P(\varphi,w',1^\lambda)$.
--
--   **Formalization Note** The verifier's time bound is a parameter: polynomial in Definition 14, quasipolynomial in the second paragraph of the proof of Corollary 45.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 14, p.20 (PDF 22); proof of Corollary 45, p.38 (PDF 40)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_TAUT
import Definitions.Def_ProofCryptoSynergy_Indist

open LaconicBarrier

namespace ProofCryptoSynergy

/-- The data of a non-interactive proof system: the randomized prover `P(φ, w, 1^λ; r)` with
`coins(|φ|, |w|, λ)` coins and the deterministic verifier `V(φ, π, 1^λ)`. -/
structure NIWIScheme where
  /-- the number of coins of the prover at `(|φ|, |w|, λ)` -/
  coins : ℕ → ℕ → ℕ → ℕ
  /-- the prover -/
  P : List Bool → List Bool → ℕ → List Bool → List Bool
  /-- the verifier -/
  V : List Bool → List Bool → ℕ → Bool

/-- The distribution `P(φ, w, 1^λ)`. -/
def NIWIScheme.prover (N : NIWIScheme) (φ w : List Bool) (lam : ℕ) : Sampler :=
  ⟨N.coins φ.length w.length lam, N.P φ w lam⟩

/-- **Subexponentially secure NIWI** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 14, p.20 (PDF 22)), with verifier step bound `T` in the
length of the encoded input: uniform algorithms, the prover randomized polynomial-time, the verifier deterministic;
**completeness**: for all satisfiable `φ`, `w` with `φ(w) = 1`, and all `λ`, `Pr_P[V(φ, P(φ, w, 1^λ), 1^λ) = 1] = 1`;
**perfect soundness**: for all `λ`, unsatisfiable `φ` with `|φ| ≤ λ`, and `π`, `V(φ, π, 1^λ) = 0`; **witness
indistinguishability**: for some `ε(λ) = 2^{-λ^{Ω(1)}}`, for all satisfiable `φ` and `w, w'` with `φ(w) = φ(w') = 1`, and
all `λ`, `P(φ, w, 1^λ) ≈_{ε(λ)} P(φ, w', 1^λ)`.

**Formalization Note** Witness indistinguishability is written as `∃ δ > 0`, for all large `λ`: `2^{-λ^{Ω(1)}}` is
asymptotic, and at finitely many small `λ` the function `ε` may be at least `1`, where `≈_ε` says nothing. `φ` is not
bounded in that clause, as printed. The time bound `T` is a parameter because the proof of Corollary 45 (p.38) also uses
a deterministic quasipolynomial-time verifier. -/
def IsSubexpNIWI (N : NIWIScheme) (T : ℕ → ℕ) : Prop :=
  (∃ c : ℕ, ∀ a b l, N.coins a b l ≤ (a + b + l + 2) ^ c) ∧
  PolyTimeOn (ι := {i : List Bool × List Bool × ℕ × List Bool //
      i.2.2.2.length = N.coins i.1.length i.2.1.length i.2.2.1})
    (fun i => [i.1.1, i.1.2.1, unary i.1.2.2.1, i.1.2.2.2])
    (fun i => N.P i.1.1 i.1.2.1 i.1.2.2.1 i.1.2.2.2) ∧
  TimeOn (ι := List Bool × List Bool × ℕ)
    (fun i => [i.1, i.2.1, unary i.2.2]) (fun i => [N.V i.1 i.2.1 i.2.2])
    (fun i => T (KarpLiptonOM.tupleEnc [i.1, i.2.1, unary i.2.2]).length) ∧
  (∀ (φ w : List Bool) (lam : ℕ) (r : List Bool), holds φ w →
    r.length = N.coins φ.length w.length lam → N.V φ (N.P φ w lam r) lam = true) ∧
  (∀ (lam : ℕ) (φ π : List Bool), φ ∉ SAT → φ.length ≤ lam → N.V φ π lam = false) ∧
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ lam : ℕ in Filter.atTop, ∀ φ w w' : List Bool, holds φ w → holds φ w' →
    Indist ((2 : ℝ) ^ (-((lam : ℝ) ^ δ))) (N.prover φ w lam) (N.prover φ w' lam)

/-- **There exists a subexponentially secure NIWI** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 39, assumption 1, p.34 (PDF 36)):
deterministic polynomial-time verifier. -/
def SubexpNIWIExists : Prop := ∃ (N : NIWIScheme) (c : ℕ), IsSubexpNIWI N (fun n => (n + 2) ^ c)

/-- A subexponentially secure NIWI with a deterministic quasipolynomial-time verifier (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), proof of
Corollary 45, second paragraph, p.38 (PDF 40)). -/
def SubexpQuasiNIWIExists : Prop :=
  ∃ (N : NIWIScheme) (k : ℕ), IsSubexpNIWI N (fun n => 2 ^ (Nat.log 2 (n + 2)) ^ k)

end ProofCryptoSynergy


