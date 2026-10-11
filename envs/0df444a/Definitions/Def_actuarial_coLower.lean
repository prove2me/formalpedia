-- Prove2me | Definitions.Def_actuarial_coLower
-- name    : actuarial_coLower
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:57:52.11799+00:00
-- url     : https://prove2.me/theorems/61b3bcd9-3d67-4c72-8def-dd295406861e
-- title:
--   Bivariate joint distribution and boundary constraints: coLower
-- statement:
--   Countermonotonic lower Fréchet dependence coupling. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

noncomputable def coLower (u v : ℝ) : ℝ := max 0 (u+v-1)

end ActuarialValuation


