-- Prove2me | Definitions.Def_actuarial_coTailJoint
-- name    : actuarial_coTailJoint
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:58:32.666577+00:00
-- url     : https://prove2.me/theorems/16991a17-967b-40e5-b69d-e0a358d9075c
-- title:
--   Independent and dependent upper-tail co-exceedance: coTailJoint
-- statement:
--   Joint capital tail probability implied by bivariate uniform loss percentiles. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

namespace ActuarialValuation

noncomputable def coTailJoint (C : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ := 1-u-v+C u v

end ActuarialValuation


