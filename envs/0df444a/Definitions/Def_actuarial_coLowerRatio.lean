-- Prove2me | Definitions.Def_actuarial_coLowerRatio
-- name    : actuarial_coLowerRatio
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:58:41.661288+00:00
-- url     : https://prove2.me/theorems/37c57221-21dd-4016-be8f-8f2fb3de8d61
-- title:
--   Independent and dependent upper-tail co-exceedance: coLowerRatio
-- statement:
--   Conditional lower-tail exceedance ratio at common low quantile. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

noncomputable def coLowerRatio (C : ℝ → ℝ → ℝ) (u : ℝ) : ℝ := C u u/u

end ActuarialValuation


