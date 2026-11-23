-- Prove2me | Definitions.Def_LinearChoresCLS_EncodedMarket
-- name    : LinearChoresCLS_EncodedMarket
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:40:57.048314+00:00
-- url     : https://prove2.me/theorems/788fbcbc-89fa-48b3-bbad-a68c22ff2bc7
-- title:
--   The completed market as a `Fin`-indexed rational market
-- statement:
--   For the completed market $f(I)$ of Section 7.1, every entry is evaluated directly in $\mathbb Q$ rather than merely asserted to have a rational representative. The disutilities, earning requirements and supplies are exactly those of the market specification on p.31, with $t=2^{-L}$ and $L$ from (7.1). The agents are indexed by $0,\dots,n$ followed by the gadget agents $(\pi,k,r)$, and the chores by $0,\dots,n$ followed by the output chores $(\pi,k,\sigma)$, via `agentFinEquiv` and `choreFinEquiv`. The resulting `completedRatMarket` is the public `Fin`-indexed rational representation needed by `encChores`.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Section 7.1 (i)–(iv), p.31, and the polynomial-time construction statement p.32.

import Mathlib
import Definitions.Def_LinearChoresCLS_PriceFamily
import Definitions.Def_LinearChoresCLS_ChoresSearch

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

variable {n : ℕ}

/-- Rational form of the scale `lam`, with exactly the same formula. -/
noncomputable def lamRat (P : Quadratic n) : ℚ :=
  1 / (2 * (n + 1) * (1 + ∑ i, ∑ j, |P.Q i j| + ∑ i, |P.c i|))

/-- Rational form of the dyadic parameter `tParam`. -/
noncomputable def tRat (P : Quadratic n) (ε : ℚ) : ℚ :=
  ((1 : ℚ) / 2) ^ chainLength P ε

/-- Rational form of `alpha`. -/
noncomputable def alphaRat (P : Quadratic n) (t : ℚ) : ℚ := lamRat P * t ^ 2

/-- Rational form of `cExt`. -/
noncomputable def cExtRat (P : Quadratic n) : Fin (n + 1) → ℚ :=
  Fin.cons (-∑ i, P.c i) P.c

/-- Rational form of `wgt`. -/
noncomputable def wgtRat (P : Quadratic n) (j j' : Fin (n + 1)) : ℚ :=
  if hj : j = 0 then
    (if hj' : j' = 0 then 0 else 1 / (n + 1) - lamRat P * ∑ k, P.Q (j'.pred hj') k)
  else
    (if hj' : j' = 0 then 0 else 1 / (n + 1) + lamRat P * P.Q (j.pred hj) (j'.pred hj'))

/-- Rational form of `pairWeight`. -/
noncomputable def pairWeightRat (P : Quadratic n) (π : Pair n) : ℚ :=
  wgtRat P π.1.1 π.1.2

/-- Rational form of `qPar`. -/
noncomputable def qParRat (t : ℚ) (k : ℕ) : ℚ := 1 + t / 4 * (1 / 2 - 4 * t) ^ k

/-- Rational form of `gadgetEarn`. -/
noncomputable def gadgetEarnRat (P : Quadratic n) (t : ℚ) (π : Pair n) (k : ℕ) : ℚ :=
  pairWeightRat P π * t * (1 / 2 - 4 * t) ^ k

/-- Rational form of `gadgetSupply`. -/
noncomputable def gadgetSupplyRat (P : Quadratic n) (t : ℚ) (π : Pair n) (k : ℕ) : ℚ :=
  (1 - 4 * t) * gadgetEarnRat P t π k

/-- The disutilities of the completed market, evaluated in `ℚ`. -/
noncomputable def ratDisutil (P : Quadratic n) (ε : ℚ) :
    Agent n (chainLength P ε) → Chore n (chainLength P ε) → ℚ
  | Sum.inl j, Sum.inl j'' => if j'' = 0 ∨ j'' = j then 1 else 1 + tRat P ε
  | Sum.inl _, Sum.inr _ => (1 + tRat P ε) ^ 2
  | Sum.inr (π, k, r), ℓ =>
      if r = 0 then
        (if ℓ = firstIn π k ∨ ℓ = secondIn π k then qParRat (tRat P ε) k.val
          else if ℓ = Sum.inr (π, k, true) then 1 else (1 + tRat P ε) ^ 2)
      else if r = 1 then
        (if ℓ = firstIn π k then 1 / qParRat (tRat P ε) k.val
          else if ℓ = Sum.inr (π, k, false) then 1 else (1 + tRat P ε) ^ 2)
      else
        (if ℓ = secondIn π k then 1 / qParRat (tRat P ε) k.val
          else if ℓ = Sum.inr (π, k, false) then 1 else (1 + tRat P ε) ^ 2)

/-- The earning requirements of the completed market, evaluated in `ℚ`. -/
noncomputable def ratEarn (P : Quadratic n) (ε : ℚ) :
    Agent n (chainLength P ε) → ℚ
  | Sum.inl j => 1 - 3 / 2 * ∑ k : Fin (chainLength P ε), ∑ π ∈ incident j,
      gadgetEarnRat P (tRat P ε) π k.val - alphaRat P (tRat P ε) / tRat P ε * cExtRat P j
  | Sum.inr (π, k, _) => gadgetEarnRat P (tRat P ε) π k.val

/-- The supplies of the completed market, evaluated in `ℚ`. -/
noncomputable def ratSupply (P : Quadratic n) (ε : ℚ) :
    Chore n (chainLength P ε) → ℚ
  | Sum.inl j => 1 - ∑ k : Fin (chainLength P ε), ∑ π ∈ incident j,
      gadgetSupplyRat P (tRat P ε) π k.val
  | Sum.inr (π, k, _) => gadgetSupplyRat P (tRat P ε) π k.val

/-- Number of auxiliary (gadget) agents. -/
abbrev auxAgentCount (n L : ℕ) : ℕ := Fintype.card (Pair n × Fin L × Fin 3)

/-- Number of auxiliary (output) chores. -/
abbrev auxChoreCount (n L : ℕ) : ℕ := Fintype.card (Pair n × Fin L × Bool)

/-- The canonical indexing of agents: basic agents first, then gadget agents. -/
noncomputable def agentFinEquiv (n L : ℕ) : Agent n L ≃ Fin (n + 1 + auxAgentCount n L) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin _)).trans finSumFinEquiv

/-- The canonical indexing of chores: basic chores first, then output chores. -/
noncomputable def choreFinEquiv (n L : ℕ) : Chore n L ≃ Fin (n + 1 + auxChoreCount n L) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin _)).trans finSumFinEquiv

/-- The completed market in the public `Fin`-indexed rational representation. -/
noncomputable def completedRatMarket (P : Quadratic n) (ε : ℚ) :
    RatChoresMarket (n + 1 + auxAgentCount n (chainLength P ε))
      (n + 1 + auxChoreCount n (chainLength P ε)) where
  disutil i j := ratDisutil P ε ((agentFinEquiv n (chainLength P ε)).symm i)
    ((choreFinEquiv n (chainLength P ε)).symm j)
  earn i := ratEarn P ε ((agentFinEquiv n (chainLength P ε)).symm i)
  supply j := ratSupply P ε ((choreFinEquiv n (chainLength P ε)).symm j)

end LinearChoresCLS


