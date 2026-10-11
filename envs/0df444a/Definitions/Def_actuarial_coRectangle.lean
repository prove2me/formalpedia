-- Prove2me | Definitions.Def_actuarial_coRectangle
-- name    : actuarial_coRectangle
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:58:14.432952+00:00
-- url     : https://prove2.me/theorems/2df75e9e-0ff3-41a4-9264-0c8ba323e8b1
-- title:
--   Rectangle probability, Fréchet bounds and copula construction: coRectangle
-- statement:
--   Probability mass of an axis-aligned rectangle in the joint distribution. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \max(0,u+v-1)\le C(u,v)\le\min(u,v)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 4. Sklar (1959), Fonctions de répartition à n dimensions et leurs marges, Publications de l'Institut de Statistique de l'Université de Paris; actuarial copula dependence in risk, https://www.mdpi.com/1911-8074/12/2/65; dependent insurance exposures, https://doi.org/10.1007/s13385-022-00326-0. Parent topic: Bivariate copula margins, rectangle 2-increasing criterion, Fréchet-Hoeffding bounds, FGM mixtures and insurance tail co-exceedance. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.mdpi.com/1911-8074/12/2/65

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def coRectangle (C : ℝ → ℝ → ℝ) (u1 u2 v1 v2 : ℝ) : ℝ := C u2 v2-C u1 v2-C u2 v1+C u1 v1

end ActuarialValuation


