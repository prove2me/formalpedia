-- Prove2me | Definitions.Def_ARGFContract_Hardness_RankConstruction
-- name    : ARGFContract_Hardness_RankConstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:18.612332+00:00
-- url     : https://prove2.me/theorems/909cac58-f159-4526-9af6-c1852efe1222
-- title:
--   Rank competencies and perturbed graph gain (3.1)
-- statement:
--   For zero-based labels $i\in\{0,\ldots,n-1\}$ define
--
--   $$p_i=\frac{n-i}{2n^2},\qquad \varepsilon_n=\frac1{4n^2},\qquad f_G(S)=\sum_{i\in S}p_i+\varepsilon_n h_G(S).$$
--
--   The source uses labels $1,\ldots,n$, so its numerator $n-i+1$ becomes $n-i$ under this bijection. All values are rational; for $n=0$, $\varepsilon_0=0$ and the only gain value is zero. This is the actual construction in equation (3.1), independent of the approximation factor.
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, Optimal Contract Design for Rank Ordered Gain Functions with Modular Costs, STOC 2027 submission #348 (October 2026), proof of Theorem 1, equation (3.1), p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/348.pdf

import Definitions.Def_ARGFContract_Hardness_IndependentGain
import Definitions.Def_ARGFContract_Hardness_ARGF

namespace ARGFContract.Hardness

/-- The 1-based source coefficient (n-i+1)/(2n²), p. 8, in zero-based Fin n. -/
def rankCompetency {n : ℕ} (i : Fin n) : ℚ :=
  ((n : ℚ) - (i.val : ℚ)) / (2 * (n : ℚ)^2)

/-- The perturbation epsilon = 1/(4n²), p. 8. At n=0 it is 0. -/
def epsilon (n : ℕ) : ℚ := 1 / (4 * (n : ℚ)^2)

/-- Equation (3.1), p. 8. -/
noncomputable def graphGain {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℚ :=
  (∑ i ∈ S, rankCompetency i) + epsilon n * independentGain G S

end ARGFContract.Hardness


