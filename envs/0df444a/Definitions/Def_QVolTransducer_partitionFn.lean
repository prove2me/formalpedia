-- Prove2me | Definitions.Def_QVolTransducer_partitionFn
-- name    : QVolTransducer_partitionFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:10.011334+00:00
-- url     : https://prove2.me/theorems/d24894d6-55df-4acf-8d66-b30d508091f9
-- title:
--   Partition function $Z(\beta)$, Gibbs distribution $\pi_\beta$ on $K$, its moments and quantiles
-- statement:
--   Let $K\subseteq\mathbb R^d$ be a convex body and $\beta\in\mathbb R$ an inverse temperature. The **partition function** and the **Gibbs distribution** $\pi_\beta$ on $K$ are
--
--   $$
--   Z(\beta):=\int_K e^{-\beta\|x\|^2}\,dx,
--   \qquad
--   \pi_\beta(x)=\frac{e^{-\beta\|x\|^2}\,\mathbb 1_{x\in K}}{Z(\beta)} .
--   $$
--
--   For a real function $f$ the module defines $\mathbb E_{x\sim\pi_\beta}[f(x)]$, $\mathrm{Var}_{x\sim\pi_\beta}[f(x)]=\mathbb E_{\pi_\beta}[(f-\mathbb E_{\pi_\beta}f)^2]$, the probability $\mathbb P_{x\sim\pi_\beta}[x\in S]$ of a set $S$, and, for $X$ with values in $[0,M]$, the quantile
--
--   $$
--   Q_X(p):=\inf\{t\in[0,M]:\ \mathbb P_{x\sim\pi_\beta}[X(x)\le t]\ge p\}.
--   $$
--
--   With $K\cap rB_d$ in place of $K$ these are the objects of the clipped distribution $\pi_{\beta,r}$ (Definition 9.15). Since $Z(0)=\mathrm{Vol}(K)$, the volume is a partition function, which is the basis of the cooling algorithm.
--
--   **Formalization Note** $\beta$ is real (the paper's value $\beta=\infty$ is not used by any statement). Integrals are Lebesgue integrals over $K\subseteq\mathbb R^d$ (`EuclideanSpace ℝ (Fin d)`). The quantile is used for $p\le1$, where $t=M$ belongs to the set.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Definition 5.1, p.36; Definition 9.15, p.61; Theorem 10.3, p.69 (PDF pp.38, 63, 71)

import Mathlib

namespace QVolTransducer

open MeasureTheory

/-- The partition function (Cornelissen, Apers, Gribling, *Improved quantum volume estimation with
transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3, 2026, sha256
40d7b52d…), Definition 5.1, p.36): `Z(β) := ∫_K exp(−β‖x‖²) dx` for a body `K ⊆ ℝ^d` and a real
inverse temperature `β`. With `K ∩ rB_d` in place of `K` it is the partition function of the
Gibbs distribution clipped at radius `r` (Definition 9.15, p.61).

**Formalization Note** `β` ranges over `ℝ`; the paper's value `β = ∞` is never used by the
statements of this mission. The integral is the Lebesgue integral over `K` in
`EuclideanSpace ℝ (Fin d)`. -/
noncomputable def partitionFn {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β : ℝ) : ℝ :=
  ∫ x in K, Real.exp (-β * ‖x‖ ^ 2)

/-- The expectation `E_{x∼π_β}[f(x)] = Z(β)⁻¹ ∫_K f(x) exp(−β‖x‖²) dx` of a real function `f`
under the Gibbs distribution `π_β` on `K`, whose density is proportional to `exp(−β‖x‖²)` on `K`
(arXiv:2609.40217, Definition 5.1, p.36). -/
noncomputable def gibbsMean {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  (∫ x in K, f x * Real.exp (-β * ‖x‖ ^ 2)) / partitionFn K β

/-- The variance `Var_{x∼π_β}[f(x)] = E_{x∼π_β}[(f(x) − E_{π_β}[f])²]` under the Gibbs
distribution `π_β` on `K` (arXiv:2609.40217, Definition 5.1, p.36). -/
noncomputable def gibbsVar {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  gibbsMean K β fun x => (f x - gibbsMean K β f) ^ 2

/-- The probability `P_{x∼π_β}[x ∈ S]` of a set `S` under the Gibbs distribution `π_β` on `K`
(arXiv:2609.40217, Definition 5.1, p.36). -/
noncomputable def gibbsProb {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β : ℝ)
    (S : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  gibbsMean K β (S.indicator fun _ => 1)

/-- The density of the Gibbs distribution `π_β` on `K` (arXiv:2609.40217, Definition 5.1, p.36):
`x ↦ exp(−β‖x‖²) 1_{x ∈ K} / Z(β)`, a function on all of `ℝ^d`. -/
noncomputable def gibbsDensity {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  K.indicator (fun y => Real.exp (-β * ‖y‖ ^ 2)) x / partitionFn K β

/-- The quantile `Q_X(p) := inf{t ∈ [0, M] : P_{x∼π_β}[X(x) ≤ t] ≥ p}` of a random variable
`X` with values in `[0, M]` under the Gibbs distribution `π_β` on `K` (arXiv:2609.40217,
Theorem 10.3, p.69, there for the clipped distribution `π_{β,r}`, i.e. with `K ∩ rB_d` in place of
`K`). For `p ≤ 1` the set contains `t = M`, so the infimum is over a nonempty set bounded below. -/
noncomputable def gibbsQuantile {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β : ℝ)
    (X : EuclideanSpace ℝ (Fin d) → ℝ) (M p : ℝ) : ℝ :=
  sInf {t : ℝ | t ∈ Set.Icc 0 M ∧ p ≤ gibbsProb K β {x | X x ≤ t}}

end QVolTransducer


