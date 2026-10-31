-- Prove2me | Definitions.Def_KallMayerSLP_RecourseBounds_jensenPartitionBound
-- name    : KallMayerSLP_RecourseBounds_jensenPartitionBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:45.202866+00:00
-- url     : https://prove2.me/theorems/1cf745a3-40aa-4b9a-9b7f-1fc56cb9eb1f
-- title:
--   Jensen lower bound of a partition, $\int\varphi\,d\mathbb P_{\eta_{\mathcal X}}$
-- statement:
--   For a partition $\mathcal X=\{\Xi_k\}$ of the support box and $\pi_k=\mathbb P_\xi(\Xi_k)$, the **Jensen distribution** $\mathbb P_{\eta_{\mathcal X}}$ puts mass $\pi_k$ on the conditional mean $\mathbb E_\xi[\xi\mid\xi\in\Xi_k]$ of each cell, and the Jensen lower bound is
--   $$
--   \int_\Xi\varphi(\eta)\,\mathbb P_{\eta_{\mathcal X}}(d\eta)=\sum_{k=1}^K\pi_k\,\varphi\big(\mathbb E_\xi[\xi\mid\xi\in\Xi_k]\big).
--   $$
--   For convex $\varphi$ it is a lower bound for $\mathbb E_\xi[\varphi(\xi)]$ by (2.39).
--
--   **Formalization Note** $\pi_k$ is `μ.real (cell k)` and the conditional mean is the set average `⨍ x in cell k, x ∂μ`; a cell with $\pi_k=0$ (where the conditional mean is undefined) contributes $0$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, after Lemma 2.8, p.223 (PDF 232)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **The Jensen lower bound of a partition, `∫_Ξ φ(η) IP_{η_X}(dη)`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, after Lemma 2.8, printed p.223
(PDF 232): `IP_{η_X}` is the discrete distribution with mass `πₖ = IP_ξ(Ξₖ)` at the conditional mean
`IE_ξ[ξ | ξ ∈ Ξₖ]`, so `∫_Ξ φ(η) IP_{η_X}(dη) = Σ_{k=1}^K πₖ φ(IE_ξ[ξ | ξ ∈ Ξₖ])`, the middle term of
(2.39).

**Formalization Note.** `πₖ` is `μ.real (cell k)` and the conditional mean is the set average
`⨍ x in cell k, x ∂μ`. A cell with `πₖ = 0` (conditional mean undefined) contributes `0`, as the
product with `πₖ = 0` makes the average's value irrelevant. -/
noncomputable def jensenPartitionBound {r K : ℕ} (μ : Measure (Fin r → ℝ))
    (cell : Fin K → Set (Fin r → ℝ)) (φ : (Fin r → ℝ) → ℝ) : ℝ :=
  ∑ k, μ.real (cell k) * φ (⨍ x in cell k, x ∂μ)

end KallMayerSLP.RecourseBounds


