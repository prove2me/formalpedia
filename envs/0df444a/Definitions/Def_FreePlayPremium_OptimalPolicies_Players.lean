-- Prove2me | Definitions.Def_FreePlayPremium_OptimalPolicies_Players
-- name    : FreePlayPremium_OptimalPolicies_Players
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:27:11.856777+00:00
-- url     : https://prove2.me/theorems/88bb0be4-1e58-4a3c-8e7a-c0db763d558a
-- title:
--   Player utilities, strict stability, preferred equilibrium and printed response
-- statement:
--   Let $v$ be base utility and $d=\alpha_d,u=\alpha_u$ the two social-comparison parameters. Valid parameters satisfy $0<d<v$ and $0<u<v$. Premium-minus-free utility, after cancelling the common friction $1/n$, is $D(s,p)=d-p-(d-u)s$. Stability is exactly the disjunction
--   $$[s=0\land D(0,p)<0]\ \lor\ [s=1\land D(1,p)>0]\ \lor\ [0<s<1\land D(s,p)=0\land u<d].$$
--   Average utility excluding the common friction is $B(s,p)=v+s(1-s)(d-u)-sp$. A selected stable share maximizes $B$ among all stable shares. At endpoints this uses the class actually present; at an interior equilibrium both classes have equal utility.
--   Separately define $\bar s(p)=(d-p)/(d-u)$ and the printed response $S(p)$. If $u<d$, it equals $1$ for $p<u$, $\bar s(p)$ for $u\le p\le d$, and $0$ for $p>d$. If $d<u$, it equals $1$ for $p\le d$ and $0$ for $p>d$. The unused equality regime is totalized with the latter branch. No definition asserts that this response is stable. The separate predicates make the printed equilibrium lemmas substantive claims.
-- source:
--   Mai and Hu (2022), Optimizing Free-to-Play Multiplayer Games with Premium Subscription, Management Science, https://doi.org/10.1287/mnsc.2022.4510, §3, Definition 1 and Lemmas 1–2, printed pp. 6–8 (PDF pp. 6–8)

import Mathlib

open Set

namespace FreePlayPremium.OptimalPolicies

structure PlayerParameters where
  v : ℝ
  down : ℝ
  up : ℝ

/-- Standing assumptions, p. 7; the two unequal regimes are specified by the theorems. -/
def PlayerParameters.Valid (P : PlayerParameters) : Prop :=
  0 < P.down ∧ P.down < P.v ∧ 0 < P.up ∧ P.up < P.v

/-- Premium-minus-free utility after cancellation of the common friction cost. -/
def utilityDifference (P : PlayerParameters) (s p : ℝ) : ℝ :=
  P.down - p - (P.down - P.up) * s

/-- Definition 1, with its strict endpoint tests unchanged. -/
def Stable (P : PlayerParameters) (p s : ℝ) : Prop :=
  (s = 0 ∧ utilityDifference P 0 p < 0) ∨
  (s = 1 ∧ 0 < utilityDifference P 1 p) ∨
  (0 < s ∧ s < 1 ∧ utilityDifference P s p = 0 ∧ P.up < P.down)

/-- Population-average utility with the common term -1/n removed; at stable
interior shares both class utilities agree, and at endpoints only the present class counts. -/
def averageUtilityWithoutFriction (P : PlayerParameters) (s p : ℝ) : ℝ :=
  P.v + s * (1 - s) * (P.down - P.up) - s * p

/-- Player preference selects the highest-utility stable equilibrium, p. 8. -/
def SelectedStable (P : PlayerParameters) (p s : ℝ) : Prop :=
  Stable P p s ∧ ∀ z : ℝ, Stable P p z →
    averageUtilityWithoutFriction P z p ≤ averageUtilityWithoutFriction P s p

noncomputable def interiorShare (P : PlayerParameters) (p : ℝ) : ℝ :=
  (P.down - p) / (P.down - P.up)

/-- The response stipulated in Problem (3), independent of the claim of stability.
The equality regime is unused; the last branch makes the function total. -/
noncomputable def premiumShare (P : PlayerParameters) (p : ℝ) : ℝ :=
  if P.up < P.down then
    if p < P.up then 1 else if p ≤ P.down then interiorShare P p else 0
  else if p ≤ P.down then 1 else 0

end FreePlayPremium.OptimalPolicies


