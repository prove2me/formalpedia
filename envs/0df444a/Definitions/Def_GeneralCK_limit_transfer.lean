-- Prove2me | Definitions.Def_GeneralCK_limit_transfer
-- name    : GeneralCK_limit_transfer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T22:20:57.134219+00:00
-- url     : https://prove2.me/theorems/a05bd47f-3144-453d-b3ca-845b69d761d6
-- title:
--   Regularized posterior entropy and the limit-transfer premise
-- statement:
--   Let $r_{f,p}(y)$ be the posterior probability that a Boolean function $f$ equals true given the noisy observation $y$, and let $m_f$ be the uniform mean of its indicator. Define $r^\varepsilon_{f,p}(y)=\varepsilon+(1-2\varepsilon)r_{f,p}(y)$ and $m_f^\varepsilon=\varepsilon+(1-2\varepsilon)m_f$. RegularizedEntropyBound states that for all dimensions and Boolean functions and all $\varepsilon,p\in(0,1/2)$, $$H(\varepsilon+p-2\varepsilon p)\le\mathbb E_yH(r^\varepsilon_{f,p}(y))+1-H(m_f^\varepsilon).$$ The separate transfer theorem takes the limit $\varepsilon\to0$ and handles the channel endpoints.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/LimitTransfer.lean#L6-L17

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_information
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
namespace GeneralCK.LimitTransfer
open scoped BigOperators

noncomputable def regularizedPosterior {n : ℕ} (f : Cube n → Bool) (p eps : ℝ)
    (y : Cube n) : ℝ := eps + (1 - 2 * eps) * Information.posterior f p y

noncomputable def regularizedMean {n : ℕ} (f : Cube n → Bool) (eps : ℝ) : ℝ :=
  eps + (1 - 2 * eps) * Information.meanIndicator f

def RegularizedEntropyBound : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (eps p : ℝ),
    0 < eps → eps < 1 / 2 → 0 < p → p < 1 / 2 →
      H (eps + p - 2 * eps * p) ≤
        Information.cubeWeight n * (∑ y, H (regularizedPosterior f p eps y)) +
          1 - H (regularizedMean f eps)



end GeneralCK.LimitTransfer


