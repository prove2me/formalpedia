-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_stayProb
-- name    : TwoFoldOPI_Supplement_stayProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:50:42.167198+00:00
-- url     : https://prove2.me/theorems/456f3e99-7ed2-4ed7-861c-cbda3f6fbf33
-- title:
--   The one-step stay probability $\Pr[X'\in\mathcal T]$ of the coordinate-replacement walk
-- statement:
--   Let $\mathcal T\subseteq[n]^m$ be nonempty, let $X$ be uniform on $\mathcal T$, and obtain $X'$ by replacing a uniformly chosen coordinate of $X$ by an independent uniform symbol of $[n]$. Then
--   $$\Pr[X'\in\mathcal T]=\frac{1}{|\mathcal T|}\sum_{x\in\mathcal T}\frac1m\sum_{i=1}^m\frac1n\sum_{a\in[n]}\mathbf 1[x^{(i\to a)}\in\mathcal T],$$
--   where $x^{(i\to a)}$ is $x$ with coordinate $i$ set to $a$.
--
--   This is the quantity estimated in Theorem 10.11.
--
--   **Formalization Note** Meaningful for $\mathcal T\ne\emptyset$, $m,n\ge1$, which hold in every use (large $n$).
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.2, Theorem 10.11, p. 56

import Mathlib

namespace TwoFoldOPI

namespace Supplement

open Classical in
/-- **The one-step stay probability of the coordinate-replacement walk on a set `T ⊆ [n]^m`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.2, Theorem 10.11, p.56: "Let X be uniform on T, and obtain X′ by replacing a uniformly
chosen coordinate of X by an independent uniform symbol in [n]. … Then Pr[X′ ∈ T] = …".

`stayProb T = (1/|T|) Σ_{x ∈ T} (1/m) Σ_{i} (1/n) Σ_{a ∈ [n]} 1[x with coordinate i set to a ∈ T]`
`= Pr[X′ ∈ T]`.

**Formalization Note.** Meaningful for `T ≠ ∅`, `m ≥ 1`, `n ≥ 1`; statements using it are for
large `n`, where these hold. -/
noncomputable def stayProb {m n : ℕ} (T : Finset (Fin m → Fin n)) : ℝ :=
  (T.card : ℝ)⁻¹ * ∑ x ∈ T, ((m : ℝ)⁻¹ * ∑ i : Fin m, ((n : ℝ)⁻¹ * ∑ a : Fin n,
    if Function.update x i a ∈ T then (1 : ℝ) else 0))

end Supplement

end TwoFoldOPI


