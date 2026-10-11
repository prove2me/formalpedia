-- Prove2me | Definitions.Def_actuarial_coInd
-- name    : actuarial_coInd
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:57:34.465813+00:00
-- url     : https://prove2.me/theorems/428c84a7-577a-49c0-a228-e251582dda9c
-- title:
--   Bivariate joint distribution and boundary constraints: coInd
-- statement:
--   Independent uniform marginals have product joint cdf. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   C(u,0)=0,\quad C(1,v)=v,\quad C(u,1)=u
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 4. Sklar (1959), Fonctions de répartition à n dimensions et leurs marges, Publications de l'Institut de Statistique de l'Université de Paris; actuarial copula dependence in risk, https://www.mdpi.com/1911-8074/12/2/65; dependent insurance exposures, https://doi.org/10.1007/s13385-022-00326-0. Parent topic: Bivariate copula margins, rectangle 2-increasing criterion, Fréchet-Hoeffding bounds, FGM mixtures and insurance tail co-exceedance. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.mdpi.com/1911-8074/12/2/65

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def coInd (u v : ℝ) : ℝ := u*v

end ActuarialValuation


