-- Prove2me | Definitions.Def_CertRandQROM_IsCorrect
-- name    : CertRandQROM_IsCorrect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:27.058617+00:00
-- url     : https://prove2.me/theorems/2fb6a076-6bef-46f0-9aff-22838d7098fe
-- title:
--   Correct strings (Verify of Construction 6.2)
-- statement:
--   For a code $C\subseteq\Sigma^n$ and an oracle $h:[n]\times\Sigma\to\{0,1\}$, a string $x=(x_1,\dots,x_n)\in\Sigma^n$ is **correct** if
--
--   $$
--   x\in C\quad\text{and}\quad h(i,x_i)=0\ \text{ for all } i\in[n].
--   $$
--
--   Verify of Construction 6.2 outputs $x$ exactly when the proof parses as a correct $x$, and $\bot$ otherwise.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Construction 6.2, Verify, steps 1–2, p.29 (PDF p.31)

import Mathlib

namespace CertRandQROM

/-- **Correctness of a string** (Construction 6.2, Verify, step 2, p.29 of Coladangelo et al.,
arXiv:2608.31112, sha256 b75095a2…): `x = (x_1, …, x_n) ∈ Σ^n` is correct for the oracle
`h : [n] × Σ → {0,1}` when `x ∈ C` and `H_i(x_i) = h(i, x_i) = 0` for every `i ∈ [n]`
(`false` is the value `0`). Verify outputs `x` exactly when `x` is correct, else `⊥`. -/
def IsCorrect {n : ℕ} {S : Type} (C : Finset (Fin n → S)) (h : Fin n × S → Bool)
    (x : Fin n → S) : Prop :=
  x ∈ C ∧ ∀ i, h (i, x i) = false

end CertRandQROM


