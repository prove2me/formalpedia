-- Prove2me | Definitions.Def_GeoRobustLearn_Supplement_BoundaryVolumeMu
-- name    : GeoRobustLearn_Supplement_BoundaryVolumeMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:38:33.775686+00:00
-- url     : https://prove2.me/theorems/070d5e7c-450a-499b-a7d5-7a46202e3c7d
-- title:
--   Boundary volume $\mathrm{Bdry}_{r,\mu}$, the class $\mathcal C_{K,\mu}$, $\mathrm{opt}_{K,\mu}$, and Gaussian-drawing programs
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^d$ and $D$ a distribution on $\mathbb R^d\times\{0,1\}$.
--
--   1. The **$r$-boundary volume under $\mu$** of $f:\mathbb R^d\to\{0,1\}$ is
--   $$\mathrm{Bdry}_{r,\mu}(f)=\Pr_{x\sim\mu}\big[\exists z:\ \|z\|_2\le r,\ f(x)\ne f(x+z)\big].$$
--   2. $\mathcal C_{K,\mu}$ is the class of Boolean $f$ with $\mathrm{Bdry}_{u,\mu}(f)\le Ku$ for every $u>0$ (empty when $K<0$).
--   3. $\mathrm{opt}_{K,\mu}=\inf_{f\in\mathcal C_{K,\mu}}\Pr_{(x,y)\sim D}[f(x)\ne y]$.
--   4. A program of the real RAM is **arithmetic with Gaussian draws** if each instruction is an exact arithmetic or comparison instruction, a load/store/pointer instruction, a pointer-to-real cast, a request for a labeled example, a standard Gaussian draw, or halt; square roots, exponentials, logarithms and the inverse Gaussian CDF are excluded.
--
--   These are the paper's Gaussian objects with $\mu$ in place of $\gamma$, and the instruction set of the learner of Theorem A.2, which samples its smoothed distributions from examples and independent Gaussian variables.
--
--   **Formalization Note** Probabilities of sets that may fail to be measurable are outer measures, and no measurability is required of $f$, exactly as in the published Gaussian versions `GeoRobustLearn.bdry`, `InCK`, `optK`.
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Appendix A, pp.43–44 (PDF pp.43–44): Bdry_{r,µ}, C_{K,µ} (p.43), opt_{K,µ} (Theorem A.2, p.44), sampling of ν_j (p.44)

import Definitions.Def_GeoRobustLearn_BoundaryVolume
import Definitions.Def_GeoRobustLearn_ArithmeticOnly

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn.Supplement

open GeoLipLearn.Agnostic

/-!
# Boundary volume, `C_{K,μ}` and `opt_{K,μ}` under a general marginal `μ`; Gaussian-drawing programs

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…), Appendix A, pp.43–44: "Write `Bdry_{r,μ}` and `C_{K,μ}` for boundary volume and
the boundary-profile class defined using `μ` in place of `γ`", and `opt_{K,μ}` (Theorem A.2, p.44);
p.44: the distributions `ν_j` "can be sampled using examples from D and independent Gaussian
variables".

**Formalization Note.** The published `GeoRobustLearn.bdry`, `InCK`, `optK` with `μ` in place of
`γ`, verbatim otherwise: outer measures, no measurability of `f`, and the conjunct `0 ≤ K` (so the
class is empty for `K < 0`, as on the page). `ArithmeticGauss` is the published `ArithmeticOnly`
instruction set plus the machine's standard-Gaussian draw `gauss`; it still excludes `√`, `exp`,
`log` and `Φ⁻¹`.
-/

/-- `Bdry_{r,μ}(f) = Pr_{x∼μ}[∃ z : ‖z‖₂ ≤ r, f(x) ≠ f(x + z)]` (outer measure). -/
noncomputable def bdryMu {d : ℕ} (μ : Measure (Space d)) (r : ℝ) (f : Space d → ℝ) : ℝ≥0∞ :=
  μ {x | ∃ z : Space d, ‖z‖ ≤ r ∧ f x ≠ f (x + z)}

/-- `f ∈ C_{K,μ}`: `f` is Boolean and `Bdry_{u,μ}(f) ≤ K u` for every `u > 0`. -/
def InCKMu {d : ℕ} (μ : Measure (Space d)) (K : ℝ) (f : Space d → ℝ) : Prop :=
  IsBoolean f ∧ 0 ≤ K ∧ ∀ u : ℝ, 0 < u → bdryMu μ u f ≤ ENNReal.ofReal (K * u)

/-- `opt_{K,μ} = inf_{f ∈ C_{K,μ}} Pr_{(x,y)∼D}[f(x) ≠ y]`, over all of `C_{K,μ}`, with outer
`D`-measures. -/
noncomputable def optKMu {d : ℕ} (μ : Measure (Space d)) (K : ℝ) (D : Measure (Space d × ℝ)) :
    ℝ≥0∞ :=
  ⨅ f : {f : Space d → ℝ // InCKMu μ K f}, D {z | f.1 z.1 ≠ z.2}

/-- Every instruction is a core real-RAM instruction, a pointer-to-real cast, `sample`, a
standard-Gaussian draw `gauss`, or `halt`. -/
def ArithmeticGauss (P : Program) : Prop :=
  ∀ i ∈ P, (∃ c, i = .core c) ∨ (∃ a b, i = .pointerReal a b) ∨ (∃ a, i = .sample a) ∨
    (∃ a, i = .gauss a) ∨ (∃ a, i = .halt a)

end GeoRobustLearn.Supplement


