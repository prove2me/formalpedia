-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_momentObs
-- name    : OptimalSpectrum_Entangled_momentObs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:03.684452+00:00
-- url     : https://prove2.me/theorems/1907af7a-b526-4c8a-9dcb-08fefff41fab
-- title:
--   Moment observables $M_m$ on $n$ copies
-- statement:
--   Let $\overline\Pi$ be the small-bucket projector on $\mathbb C^d$ and $\overline\Pi_i$ its action on copy $i$. For $1\le m\le n$,
--
--   $$M_m=\frac1{n^{\downarrow m}}\sum_{\substack{i_1,\dots,i_m\in[n]\\ \text{all distinct}}}\overline\Pi_{i_1}\cdots\overline\Pi_{i_m}\,R_{(i_1\cdots i_m)},\qquad M_0=d\,I,$$
--
--   where $R_{(i_1\cdots i_m)}$ cyclically permutes the copies $i_1\to i_2\to\cdots\to i_m\to i_1$ and fixes the others, and $n^{\downarrow m}=n(n-1)\cdots(n-m+1)$. The expectation of $M_m$ in $\tau^{\otimes n}$ is the $m$-th moment $\mathrm{tr}((\overline\Pi\tau\overline\Pi)^m)$ (Eq. (38)), which is how the entangled scheme estimates moments of the small-bucket state.
--
--   **Formalization Note** Ordered tuples of distinct indices are embeddings `Fin m ↪ Fin n`, and the cycle is `List.formPerm` of the tuple.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.1.2, p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_permOp
import Definitions.Def_OptimalSpectrum_Entangled_copyOp

namespace OptimalSpectrum.Entangled

/-- **Moment observables `M_m`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.1.2, printed p. 21 (PDF p. 23): "Define the following observables on the space (C^d)^⊗n
of all n input copies by M_m := (1/n^↓m) ∑_(i₁,…,i_m ∈ [n] all distinct) Π̄_(i₁) ⋯ Π̄_(i_m)
R_(i₁⋯i_m), 1 ⩽ m ⩽ K, and set M₀ := dI."

Here `Π̄` is the small-bucket projector, `Π̄_i` is `Π̄` on copy `i`, `R_(i₁⋯i_m)` is the permutation
operator of the cycle `i₁ ↦ i₂ ↦ ⋯ ↦ i_m ↦ i₁` (identity on the other copies), and
`n^↓m = n(n−1)⋯(n−m+1)` is the falling factorial.

**Formalization Note.** `Pbar` is the matrix `Π̄` (the overlined projector of the page; the text
layer prints it without the bar). An ordered tuple of distinct indices is an embedding
`Fin m ↪ Fin n`, and its cycle is `List.formPerm` of the tuple, which maps each entry to the next and
the last to the first. The product `Π̄_(i₁) ⋯ Π̄_(i_m)` is taken in tuple order (the factors commute).
The paper uses `M_m` for `m ≤ K ≤ n`; for `m > n` the formula has an empty sum. -/
noncomputable def momentObs (d n : ℕ) (Pbar : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  if m = 0 then (d : ℂ) • (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)
  else ((n.descFactorial m : ℂ))⁻¹ • ∑ t : Fin m ↪ Fin n,
    (List.ofFn fun j => copyOp (t j) Pbar).prod * permOp (List.ofFn ⇑t).formPerm

end OptimalSpectrum.Entangled


