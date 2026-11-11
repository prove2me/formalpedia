-- Prove2me | Definitions.Def_GaussDiffSVP_InClassC
-- name    : GaussDiffSVP_InClassC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:51.799292+00:00
-- url     : https://prove2.me/theorems/ef5db0e2-4daf-4856-86fd-3758d34d361d
-- title:
--   The class $\mathcal C(\nu,\varepsilon)$ of factorial moment bounds
-- statement:
--   For a reference $\nu\ge0$ and $\varepsilon\ge 0$, a random record list $\Xi$ lies in $\mathcal C(\nu,\varepsilon)$ if, pointwise,
--   $$e^{-\varepsilon}\nu \le m_\Xi \le e^{\varepsilon}\nu,\qquad S_\Xi \le e^{\varepsilon}\nu^{\otimes 2}.$$
--   The reference specifies the expected number of records at each point; one error parameter controls both these expected counts and pairs of distinct records. Conditional versions $\mathcal C_H$ fix retained information $H$.
--
--   **Formalization Note** The law is the (conditional) law of the list given the retained information; a statement for every such law covers every value of $H$.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Definition 4.2, p.23

import Mathlib
import Definitions.Def_GaussDiffSVP_intensity
import Definitions.Def_GaussDiffSVP_factMoment

open scoped ENNReal

namespace GaussDiffSVP

/-- The class `C(ν, ε)` of Definition 4.2 (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.23): "Write `Ξ ∈ C_H(ν, ε)` if, almost surely,
its conditional moments satisfy `e^{−ε}ν ≤ m_Ξ ≤ e^{ε}ν`, `S_Ξ ≤ e^{ε}ν^{⊗2}` (24). The comparisons
are pointwise on the countable underlying space." Here `ν ≥ 0` is the reference and `ε ≥ 0`.

**Formalization Note.** The law `μ` is the conditional law of the list given the retained
information `H` (fixed); the class for a given `H` is the statement for every value of `H`,
i.e. for every such law. The reference takes values in `ℝ≥0∞` and the comparisons are pointwise
in `ℝ≥0∞`. -/
def InClassC {α : Type*} (μ : PMF (List α)) (ν : α → ℝ≥0∞) (ε : ℝ) : Prop :=
  0 ≤ ε ∧
    (∀ x, ENNReal.ofReal (Real.exp (-ε)) * ν x ≤ intensity μ x ∧
      intensity μ x ≤ ENNReal.ofReal (Real.exp ε) * ν x) ∧
    ∀ x y, factMoment μ x y ≤ ENNReal.ofReal (Real.exp ε) * (ν x * ν y)

end GaussDiffSVP


