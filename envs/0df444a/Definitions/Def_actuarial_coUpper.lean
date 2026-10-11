-- Prove2me | Definitions.Def_actuarial_coUpper
-- name    : actuarial_coUpper
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:57:42.912691+00:00
-- url     : https://prove2.me/theorems/023c79f6-2c12-4cf7-bf51-a02adb6916bc
-- title:
--   Bivariate joint distribution and boundary constraints: coUpper
-- statement:
--   Comonotonic upper Fréchet dependence coupling. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

noncomputable def coUpper (u v : ℝ) : ℝ := min u v

end ActuarialValuation


