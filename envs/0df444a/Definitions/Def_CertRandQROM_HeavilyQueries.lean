-- Prove2me | Definitions.Def_CertRandQROM_HeavilyQueries
-- name    : CertRandQROM_HeavilyQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:33:20.510648+00:00
-- url     : https://prove2.me/theorems/fd4c7120-c447-425c-9b4d-ee66fa822205
-- title:
--   Heavy querying of a string
-- statement:
--   An algorithm $\mathcal A^h$ **heavily queries** $x\in\Sigma^n$ at level $\eta$ if there is a set $I_1\subseteq[n]$ with $|I_1|\ge\sqrt n/5$ such that
--
--   $$
--   \tilde w_{i,x_i}(h)\ge\eta\qquad\text{for all } i\in I_1 .
--   $$
--
--   The paper uses $\eta=\alpha/(256Q^2n^3)$ in the proof of Lemma 7.4 and in Claim 7.5.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), §7.2, p.42 (PDF p.44), definition of "heavily queries" above Claim 7.5

import Mathlib
import Definitions.Def_CertRandQROM_queryNorm

namespace CertRandQROM

/-- **Heavy querying** (§7.2, p.42 of Coladangelo et al., arXiv:2608.31112, sha256 b75095a2…):
`A^h` heavily queries `x ∈ Σ^n` at level `η` if there is a set `I₁ ⊆ [n]` with
`|I₁| ≥ √n/5` such that `w̃_{i, x_i}(h) ≥ η` for all `i ∈ I₁`. The paper uses
`η = α/(256 Q² n³)`. -/
def HeavilyQueries {n : ℕ} {S W O : Type} [Fintype S] [DecidableEq S] [Fintype W]
    [DecidableEq W] [Fintype O] {Q : ℕ} (A : QueryAlg (Fin n × S) W O Q)
    (h : Fin n × S → Bool) (x : Fin n → S) (η : ℝ) : Prop :=
  ∃ I₁ : Finset (Fin n), Real.sqrt n / 5 ≤ (I₁.card : ℝ) ∧ ∀ i ∈ I₁, η ≤ totalQueryNorm A h (i, x i)

end CertRandQROM


