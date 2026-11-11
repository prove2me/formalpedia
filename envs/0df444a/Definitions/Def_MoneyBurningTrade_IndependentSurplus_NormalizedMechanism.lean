-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_NormalizedMechanism
-- name    : MoneyBurningTrade_IndependentSurplus_NormalizedMechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:55.474842+00:00
-- url     : https://prove2.me/theorems/40401c5d-89d2-4b06-9169-29b24866720f
-- title:
--   Appendix A.2 — normalized payment mechanism
-- statement:
--   The concrete mechanism has the allocation $x$ from equation (18). Its payments are zero when $x(s,b)=0$, and otherwise are
--
--   $$p_B(s,b)=b x(s,b)-\int_s^b x(s,z)\,dz,\qquad p_S(s,b)=s x(s,b)+\int_s^b x(z,b)\,dz.$$
--
--   These are the source's actual expected payment rules, with oriented Lebesgue interval integrals. The slice functions are bounded finite step functions on the relevant intervals. DSIC, IR, WBB and transfer bounds remain theorem conclusions; no validity or surplus inequality is stored as construction data.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Appendix A.2, normalized payments and equation (30), printed p. 41 (PDF p. 42); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Model
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Allocation

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- The actual normalized mechanism, Lemma 4.3 and Appendix A.2 p.41.
All validity and performance claims are left to theorems. The integrals are
oriented Lebesgue interval integrals. On the zero-allocation branch both payments
are zero. In the stated domain the slice functions are bounded finite step functions. -/
noncomputable def normalizedMechanism (G : Grid) (τ : ℝ) : SecondBestBT.Mechanism where
  x := gridAllocation G τ
  pB := fun p => if gridAllocation G τ p = 0 then 0 else
    p.2 * gridAllocation G τ p - ∫ z in p.1..p.2, gridAllocation G τ (p.1, z)
  pS := fun p => if gridAllocation G τ p = 0 then 0 else
    p.1 * gridAllocation G τ p + ∫ z in p.1..p.2, gridAllocation G τ (z, p.2)

end MoneyBurningTrade.IndependentSurplus


