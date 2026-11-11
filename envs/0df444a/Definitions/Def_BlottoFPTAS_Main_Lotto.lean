-- Prove2me | Definitions.Def_BlottoFPTAS_Main_Lotto
-- name    : BlottoFPTAS_Main_Lotto
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:40:01.18965+00:00
-- url     : https://prove2.me/theorems/2e08acf6-d9ad-40ad-a6ad-7a7454157acd
-- title:
--   Uniform and atom-plus-uniform laws, coordinate marginals, and mixtures of uniform laws on segments
-- statement:
--   $\mathrm{Unif}[0,\ell]$ is Lebesgue measure on $[0,\ell]$ scaled by $1/\ell$; `atomUnif p ℓ` is $(1-p)\delta_0+p\,\mathrm{Unif}[0,\ell]$. The General Lotto marginals (6) are $X_i\sim\mathrm{Unif}[0,\ell_i]$ and $Y_i\sim(1-b)\delta_0+b\,\mathrm{Unif}[0,\ell_i]$ with $\ell_i=2v_i$. The marginal of $\mu$ at coordinate $i$ is the law of $x_i$ for $x\sim\mu$. A segment $PQ$ is sampled as $(1-U)P+UQ$ with $U\sim\mathrm{Unif}[0,1]$ (`segLaw P Q`), and a segment mixture chooses segment $i$ with probability $\alpha_i$ (`segMixture α P Q`).
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 13, §4.1.1, Eq. (6); p. 15, §4.1.3

import Mathlib

open MeasureTheory

namespace BlottoFPTAS.Main

/-!
# General Lotto marginals (6) and segment mixtures (§4.1.1, p. 13; §4.1.3, p. 15)

* `unifOn l` is `Unif[0, l]` for `l > 0`: Lebesgue measure on `[0, l]` scaled by `1/l`.
* `atomUnif p l` is `(1 − p)δ₀ + p Unif[0, l]`.
* The Lotto marginals (6) for values `v` and budget ratio `b` are `X_i ∼ Unif[0, ℓ_i]` and
  `Y_i ∼ (1 − b)δ₀ + b Unif[0, ℓ_i]`, with `ℓ_i = 2v_i`.
* A segment `PQ` is sampled as `(1 − U)P + UQ`, `U ∼ Unif[0, 1]` (`segLaw P Q`); a mixture
  chooses segment `i` with probability `α_i` (`segMixture`).
* `marginal μ i` is the law of coordinate `i` under `μ`.
-/

/-- `Unif[0, l]`. -/
noncomputable def unifOn (l : ℝ) : Measure ℝ :=
  (ENNReal.ofReal l)⁻¹ • volume.restrict (Set.Icc 0 l)

/-- `(1 − p)δ₀ + p Unif[0, l]`. -/
noncomputable def atomUnif (p l : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac 0 + ENNReal.ofReal p • unifOn l

/-- The law of coordinate `i` of an allocation drawn from `μ`. -/
noncomputable def marginal {ι : Type*} (μ : Measure (ι → ℝ)) (i : ι) : Measure ℝ :=
  μ.map fun x => x i

/-- The uniform law on the segment `PQ`: the law of `(1 − U)P + UQ`, `U ∼ Unif[0, 1]`. -/
noncomputable def segLaw {ι : Type*} (P Q : ι → ℝ) : Measure (ι → ℝ) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).map fun u => (1 - u) • P + u • Q

/-- The mixture choosing segment `i` with probability `α i`. -/
noncomputable def segMixture {ι : Type*} {s : ℕ} (α : Fin s → ℝ) (P Q : Fin s → ι → ℝ) :
    Measure (ι → ℝ) :=
  ∑ i, ENNReal.ofReal (α i) • segLaw (P i) (Q i)

end BlottoFPTAS.Main


