-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_Model
-- name    : MoneyBurningTrade_IndependentSurplus_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:31.887893+00:00
-- url     : https://prove2.me/theorems/d8721b4a-d164-4ea2-896e-459172deb191
-- title:
--   Common report domain and measurable randomized mechanisms
-- statement:
--   Let $T\subseteq\mathbb R$ be the common seller and buyer report set, and let $M=(x,p_B,p_S)$ be the published raw mechanism triple, with seller first. The mechanism predicate requires the three rules restricted to $T\times T$ to be Borel measurable and
--
--   $$0\le x(s,b)\le1\qquad(s,b\in T).$$
--
--   The witness report interval is $T=[0,1]$. Payments remain signed real expected transfers. This interface adds neither incentives nor budget constraints, and permits arbitrary internal randomization. Global extensions outside $T$ are irrelevant.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), §3.1, printed p. 13 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_SecondBestBT_Mechanism

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- The common report interval used by the witnesses in §4.1–4.2. -/
def reportInterval : Set ℝ := Set.Icc 0 1

/-- A randomized direct mechanism on an arbitrary common report set, §3.1 p.13.
Only restrictions to the actual report domain must be Borel measurable.
The three real functions are expected allocation and transfers, with seller first. -/
def IsMechanism (T : Set ℝ) (M : SecondBestBT.Mechanism) : Prop :=
  Measurable (fun p : T × T => M.x (p.1, p.2)) ∧
  Measurable (fun p : T × T => M.pB (p.1, p.2)) ∧
  Measurable (fun p : T × T => M.pS (p.1, p.2)) ∧
  ∀ s ∈ T, ∀ b ∈ T, 0 ≤ M.x (s, b) ∧ M.x (s, b) ≤ 1

end MoneyBurningTrade.IndependentSurplus


