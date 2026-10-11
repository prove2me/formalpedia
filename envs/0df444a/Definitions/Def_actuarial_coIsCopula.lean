-- Prove2me | Definitions.Def_actuarial_coIsCopula
-- name    : actuarial_coIsCopula
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:58:25.774715+00:00
-- url     : https://prove2.me/theorems/d99e957c-2a3e-4cc7-9b8a-0ff9dd35f5fe
-- title:
--   Rectangle probability, Fréchet bounds and copula construction: coIsCopula
-- statement:
--   Copula constraints of grounded margins and nonnegative rectangle probability. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_coRectangle

namespace ActuarialValuation

noncomputable def coIsCopula (C : ℝ → ℝ → ℝ) : Prop := (∀ u, 0≤u → u≤1 → C u 0=0 ∧ C 0 u=0 ∧ C u 1=u ∧ C 1 u=u) ∧ (∀ u1 u2 v1 v2, 0≤u1 → u1≤u2 → u2≤1 → 0≤v1 → v1≤v2 → v2≤1 → 0≤coRectangle C u1 u2 v1 v2)

end ActuarialValuation


