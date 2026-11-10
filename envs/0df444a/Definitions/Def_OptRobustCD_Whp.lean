-- Prove2me | Definitions.Def_OptRobustCD_Whp
-- name    : OptRobustCD_Whp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:50:09.135093+00:00
-- url     : https://prove2.me/theorems/2a83e0c3-4146-4393-af37-5ed21c29faa7
-- title:
--   SBM$(n,d,\lambda)$ through $a=d(1+\lambda)$, $b=d(1-\lambda)$, and "with high probability"
-- statement:
--   In the symmetric two-community stochastic block model $\mathrm{SBM}(n,d,\lambda)$ the hidden labels $\sigma^\star\in\{\pm1\}^n$ are independent and uniform, and conditionally on them each unordered pair $\{u,v\}$ of distinct vertices is an edge independently with probability
--   $$\frac dn\bigl(1+\lambda\sigma^\star_u\sigma^\star_v\bigr).$$
--   This is the published law $\mathcal G(n,a/n,b/n)$ of `SBMThreshold_Main_Setting` with
--   $$a=d(1+\lambda),\qquad b=d(1-\lambda),$$
--   since its edge probability is $a/n$ for equal labels and $b/n$ otherwise.
--
--   An event $E_n(\sigma^\star,G)$ holds **with high probability** if $\Pr[E_n]\to1$ as $n\to\infty$ under $\mathrm{SBM}(n,d,\lambda)$.
--
--   **Formalization Note** For $n<d(1+|\lambda|)$ the numbers $a/n,b/n$ are not probabilities; every statement of the mission is asymptotic in $n$. At $\lambda=\pm1$ one of $a,b$ is $0$, which is a genuine law.
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), §1 p.1 (pdf p.3); §3.1 p.12 (pdf p.14)

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting

namespace OptRobustCD

/-!
# SBM(n, d, λ), "with high probability", and the overlap

Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…), §1 (p.1, pdf p.3) and §3.1
(p.12, pdf p.14): "the hidden labels σ⋆ ∈ {±1}^n are independent and uniform. Conditional on the
labels, each unordered pair of distinct vertices is joined independently with probability
(d/n)(1 + λσ⋆_uσ⋆_v)"; `ov(σ̂, σ⋆) = (1/n)|⟨σ̂, σ⋆⟩|`.

**Formalization Note.**
* The law is the published `SBMThreshold.Main.sbmWeight n a b` with `a = d(1+λ)`, `b = d(1−λ)`
  (`sbmA`, `sbmB`): its edge probability is `a/n` for equal labels and `b/n` otherwise, which is
  `(d/n)(1 + λσ_uσ_v)`. Labels are `Fin n → Bool` (`true ↦ +1`). For `n < d(1+|λ|)` the numbers
  are not probabilities; every statement of the mission is asymptotic in `n`, so only large `n`
  matters. At `λ = ±1` one of `a, b` is `0`, which is a genuine law.
* An event `E n σ G` holds **with high probability** (`Whp d λ E`) when its SBM(n, d, λ)
  probability tends to `1` as `n → ∞`.
* The overlap is the published `SBMThreshold.Main.overlap`.
-/

/-- `a = d(1 + λ)`: `a/n` is the within-community edge probability. -/
def sbmA (d lam : ℝ) : ℝ := d * (1 + lam)

/-- `b = d(1 − λ)`: `b/n` is the across-community edge probability. -/
def sbmB (d lam : ℝ) : ℝ := d * (1 - lam)

/-- The event `E` holds with high probability under `(σ⋆, G) ∼ SBM(n, d, λ)`:
`Pr[E n σ⋆ G] → 1` as `n → ∞`. -/
def Whp (d lam : ℝ) (E : ∀ n : ℕ, (Fin n → Bool) → SimpleGraph (Fin n) → Prop) : Prop :=
  Filter.Tendsto (fun n => SBMThreshold.Main.sbmProb n (sbmA d lam) (sbmB d lam) (E n))
    Filter.atTop (nhds 1)

end OptRobustCD


