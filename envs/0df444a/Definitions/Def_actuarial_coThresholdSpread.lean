-- Prove2me | Definitions.Def_actuarial_coThresholdSpread
-- name    : actuarial_coThresholdSpread
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:59:10.039312+00:00
-- url     : https://prove2.me/theorems/f4cbef62-9852-41a7-84f7-bbc3f3a9ddcb
-- title:
--   Independent and dependent upper-tail co-exceedance: coThresholdSpread
-- statement:
--   Excess two-line joint ruin-tail probability over independent losses. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \Pr(U>u,V>v)=1-u-v+C(u,v)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 4. Sklar (1959), Fonctions de répartition à n dimensions et leurs marges, Publications de l'Institut de Statistique de l'Université de Paris; actuarial copula dependence in risk, https://www.mdpi.com/1911-8074/12/2/65; dependent insurance exposures, https://doi.org/10.1007/s13385-022-00326-0. Parent topic: Bivariate copula margins, rectangle 2-increasing criterion, Fréchet-Hoeffding bounds, FGM mixtures and insurance tail co-exceedance. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.mdpi.com/1911-8074/12/2/65

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coInd
import Definitions.Def_actuarial_coTailJoint

namespace ActuarialValuation

noncomputable def coThresholdSpread (C : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ := coTailJoint C u v-coTailJoint coInd u v

end ActuarialValuation


