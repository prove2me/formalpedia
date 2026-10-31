-- Prove2me | Definitions.Def_KallMayerSLP_RecourseBounds_emPartitionBound
-- name    : KallMayerSLP_RecourseBounds_emPartitionBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:05.307294+00:00
-- url     : https://prove2.me/theorems/36fd133b-dc73-435a-90fb-66bd5d69f258
-- title:
--   E–M upper bound of a partition, $\int\varphi\,d\mathbb Q_{\eta_{\mathcal X}}$
-- statement:
--   For a partition $\mathcal X=\{\Xi_k\}$ of the support box, let $\mathbb Q_k$ be the generalized Edmundson–Madansky distribution of the conditional law of $\xi$ given $\xi\in\Xi_k$, on the vertices of the (closed) cell $\Xi_k$, and $\pi_k=\mathbb P_\xi(\Xi_k)$. The E–M distribution of the partition is $\mathbb Q_{\eta_{\mathcal X}}=\sum_k\pi_k\mathbb Q_k$, and the E–M upper bound is
--   $$
--   \int_\Xi\varphi(\eta)\,\mathbb Q_{\eta_{\mathcal X}}(d\eta)=\sum_{k=1}^K\pi_k\int_{\Xi_k}\varphi(\eta)\,\mathbb Q_k(d\eta).
--   $$
--   For convex $\varphi$ it is an upper bound for $\mathbb E_\xi[\varphi(\xi)]$ by (2.40).
--
--   **Formalization Note** The $k$-th term is the generalized E–M bound (2.31) of the restricted measure $\mathbb P_\xi|_{\Xi_k}$ on the vertices of the closed box $[\mathrm{lo}_k,\mathrm{hi}_k]$, which equals $\pi_k\int\varphi\,d\mathbb Q_k$; a cell with $\pi_k=0$ contributes $0$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, after Lemma 2.8, p.223 (PDF 232)

import Mathlib
import Definitions.Def_KallMayerSLP_RecourseBounds_genEMBound

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **The E–M upper bound of a partition, `∫_Ξ φ(η) Q_{η_X}(dη)`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, after Lemma 2.8, printed p.223
(PDF 232): `Q_{η_X} = Σ_{k=1}^K πₖ Q_k`, where `Q_k` is the generalized E–M distribution of the
conditional law of `ξ` given `ξ ∈ Ξₖ` on the vertices of the cell `Ξₖ`; so
`∫_Ξ φ(η) Q_{η_X}(dη) = Σ_k πₖ ∫_{Ξₖ} φ(η) Q_k(dη)`, the middle term of (2.40).

**Formalization Note.** The `k`-th term is `genEMBound (μ.restrict (cell k)) (lo k) (hi k) φ`, the
E–M bound (2.31) of the restricted measure on the vertices of the closed box `[lo k, hi k]`; it
equals `πₖ ∫ φ dQ_k` and is `0` when `πₖ = 0` (the book's conditional quantities are then undefined,
and the cell contributes nothing). -/
noncomputable def emPartitionBound {r K : ℕ} (μ : Measure (Fin r → ℝ))
    (lo hi : Fin K → Fin r → ℝ) (cell : Fin K → Set (Fin r → ℝ)) (φ : (Fin r → ℝ) → ℝ) : ℝ :=
  ∑ k, genEMBound (μ.restrict (cell k)) (lo k) (hi k) φ

end KallMayerSLP.RecourseBounds


