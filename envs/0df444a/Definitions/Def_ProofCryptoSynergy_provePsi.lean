-- Prove2me | Definitions.Def_ProofCryptoSynergy_provePsi
-- name    : ProofCryptoSynergy_provePsi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:07:32.83649+00:00
-- url     : https://prove2.me/theorems/4109898d-62e2-4f0a-8f8a-3cbcdb6482f5
-- title:
--   The proof system $(P[\Psi],V[\Psi])$ (corrected: NIWI security parameter)
-- statement:
--   Given a NIWI $(P_{\mathrm{NIWI}},V_{\mathrm{NIWI}})$ and a sequence $\Psi=\{\psi_\lambda\}$: $P[\Psi](\varphi,w,1^\lambda)$ rejects if $|\varphi|>\lambda$ or $\varphi(w)=0$, and otherwise runs $P_{\mathrm{NIWI}}$ on $\varphi\vee\psi_\lambda$ and $w$; $V[\Psi](\varphi,\pi,1^\lambda)$ runs $V_{\mathrm{NIWI}}$ on $\varphi\vee\psi_\lambda$ and $\pi$.
--
--   **Formalization Note** The security parameter given to the NIWI is $\lambda'=\max(\lambda,|\varphi\vee\psi_\lambda|)$, where the paper prints $1^\lambda$. Definition 14's soundness covers only formulas of size at most the security parameter, and $|\psi_\lambda|=\lambda$ for the families used, so with $1^\lambda$ the soundness clause of Lemma 32 fails: a NIWI whose verifier also accepts every $\varphi$ with $|\varphi|>\lambda$ still satisfies Definition 14, and then all proofs are accepted for unsatisfiable $\varphi,\psi_\lambda$. The change is polynomial and only strengthens the indistinguishability used. For $|\varphi\vee\psi_\lambda|\le\lambda$ it is the printed construction.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 31, p.29 (PDF 31); Lemma 32, p.29 (PDF 31); Lemma 33, p.30 (PDF 32)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_NIWIScheme

open LaconicBarrier

namespace ProofCryptoSynergy

/-- The security parameter handed to the NIWI at `(φ, ψ, λ)`: the larger of `λ` and `|φ ∨ ψ|`.

**Formalization Note (correction of Definition 31)** Definition 31 prints `1^λ` here. Definition 14's soundness covers only
`|φ ∨ ψ_λ| ≤ λ`, while `|ψ_λ| = λ` for the families the paper uses, so with `1^λ` the clause never applies and Lemma 32, item 2
fails: replace a NIWI's verifier by one that also accepts every `φ` with `|φ| > λ`; Definition 14 still holds, and every proof
for unsatisfiable `φ`, `ψ_λ` is accepted. Raising the parameter to `|φ ∨ ψ_λ|` keeps polynomial efficiency and only strengthens
the indistinguishability used. For `|φ ∨ ψ_λ| ≤ λ` it is the printed construction. -/
def secParam (φ ψ : List Bool) (lam : ℕ) : ℕ := max lam (orStr φ ψ).length

/-- The number of coins of `P[Ψ]` at `(φ, w, λ)`. -/
def psiCoins (N : NIWIScheme) (Ψ : ℕ → List Bool) (φ w : List Bool) (lam : ℕ) : ℕ :=
  N.coins (orStr φ (Ψ lam)).length w.length (secParam φ (Ψ lam) lam)

open Classical in
/-- The **prover** `P[Ψ]` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 31, p.29 (PDF 31)): `P[Ψ](φ, w, 1^λ)` rejects if `|φ| > λ` or `φ(w) = 0`, and
otherwise outputs `P_NIWI(φ ∨ ψ_λ, w, 1^λ)`.

**Formalization Note** Rejection is the empty string. See `secParam` for the security parameter. -/
noncomputable def provePsi (N : NIWIScheme) (Ψ : ℕ → List Bool) (φ w : List Bool) (lam : ℕ)
    (r : List Bool) : List Bool :=
  if lam < φ.length ∨ ¬ holds φ w then [] else N.P (orStr φ (Ψ lam)) w (secParam φ (Ψ lam) lam) r

/-- The **verifier** `V[Ψ](φ, π, 1^λ) := V_NIWI(φ ∨ ψ_λ, π, 1^λ)` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 31, p.29 (PDF 31)); security
parameter as in `secParam`. -/
def verifyPsi (N : NIWIScheme) (Ψ : ℕ → List Bool) (φ π : List Bool) (lam : ℕ) : Bool :=
  N.V (orStr φ (Ψ lam)) π (secParam φ (Ψ lam) lam)

/-- The distribution `P[Ψ](φ, w, 1^λ)`. -/
noncomputable def psiProver (N : NIWIScheme) (Ψ : ℕ → List Bool) (φ w : List Bool) (lam : ℕ) :
    Sampler :=
  ⟨psiCoins N Ψ φ w lam, provePsi N Ψ φ w lam⟩

/-- **Perfect completeness** of `(P[Ψ], V[Ψ])` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 32, item 1, p.29 (PDF 31)): every proof the prover does
not reject is accepted. -/
def PsiComplete (N : NIWIScheme) (Ψ : ℕ → List Bool) : Prop :=
  ∀ (lam : ℕ) (φ w r : List Bool), φ.length ≤ lam → holds φ w →
    r.length = psiCoins N Ψ φ w lam → verifyPsi N Ψ φ (provePsi N Ψ φ w lam r) lam = true

/-- **Perfect soundness on security parameter `λ`** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 32, item 2, p.29 (PDF 31)), in the format of Definition 14:
for unsatisfiable `φ` with `|φ| ≤ λ` and all `π`, `V[Ψ](φ, π, 1^λ) = 0`. -/
def PsiSoundAt (N : NIWIScheme) (Ψ : ℕ → List Bool) (lam : ℕ) : Prop :=
  ∀ φ π : List Bool, φ ∉ SAT → φ.length ≤ lam → verifyPsi N Ψ φ π lam = false

/-- `(P[Ψ], V[Ψ])` is **uniformly efficiently computable** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 31 and Lemma 33, p.29–30 (PDF 31–32)):
polynomially many coins, and one polynomial-time machine for each of `P[Ψ]` and `V[Ψ]`. -/
def PsiEfficient (N : NIWIScheme) (Ψ : ℕ → List Bool) : Prop :=
  (∃ c : ℕ, ∀ (φ w : List Bool) (lam : ℕ),
    psiCoins N Ψ φ w lam ≤ (φ.length + w.length + lam + 2) ^ c) ∧
  PolyTimeOn (ι := {i : List Bool × List Bool × ℕ × List Bool //
      i.2.2.2.length = psiCoins N Ψ i.1 i.2.1 i.2.2.1})
    (fun i => [i.1.1, i.1.2.1, unary i.1.2.2.1, i.1.2.2.2])
    (fun i => provePsi N Ψ i.1.1 i.1.2.1 i.1.2.2.1 i.1.2.2.2) ∧
  PolyTimeOn (ι := List Bool × List Bool × ℕ)
    (fun i => [i.1, i.2.1, unary i.2.2]) (fun i => [verifyPsi N Ψ i.1 i.2.1 i.2.2])

end ProofCryptoSynergy


