-- Prove2me | Definitions.Def_LocalOccupancyIS_Glauber_GoalInterface
-- name    : LocalOccupancyIS_Glauber_GoalInterface
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:01:08.014143+00:00
-- url     : https://prove2.me/theorems/9a5f0d14-5dfe-4550-99fd-4db99a407f5c
-- title:
--   Full finite, asymptotic and implementation conclusions
-- statement:
--   These predicates organize the conclusions of the single goal theorem; they are not hypotheses of its algorithm. The exact conclusion contains the complete finite certificate and expected-size assertions, the asymptotic output guarantee, the counted runtime bound and the identity connecting a Boolean proposal to the single-site heat-bath law. The target size is
--
--   $$\left(1-A\frac{\log D}{D}\right)\frac{nD}{\Delta}.$$
--
--   For fixed $t$, $A$ is chosen before $b$ and the graph; in growing families it is $A_0t$ for one absolute $A_0$. The bit conclusion requires the first terminating preprocessing stage, the enclosure and $q\in[x,x+2]$, $q\le\Delta+2$, the rounded relative error, and the entire finite conclusion with recomputed parameters at $\widehat\lambda=1/q$. It also requires normalization, equality of the fair-bit output to the specified independent-run law, success at least $1-e^{-m}$, and an expected bit bound polynomial in $n$, the rational input length, $m$ and the length of $t$. A separate predicate expresses the leading-constant-one specializations. Finally, $K_{1,t,t}$-freeness means no non-induced $K_{t,t}$ copy in any open neighborhood. Every predicate has an explicit mathematical body.
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), Corollary 4, Remark 1 and proof, p. 6–20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf#page=6

import Definitions.Def_LocalOccupancyIS_Glauber_BitExecution

open scoped BigOperators

namespace LocalOccupancyIS.Glauber
noncomputable section

/-- Conclusions about the specified procedure; no guarantee is an input to that procedure. -/
def ExactConclusion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℝ) (w : Fin n → List (Fin n)) (A B : ℝ) (k : ℕ) : Prop :=
  let lam := fugacity Δ t b
  let c := correction Δ t b
  let d := D Δ t b
  FiniteConclusion G Δ lam c w ∧
  |Gamma Δ lam c * d / Δ - 1| ≤ A * Real.log d / d ∧
  (∀ I : State G, ∀ δ : ℝ, 0 < δ → δ < 1 →
    MarkovMixing.IsDist (algorithm G Δ t b (1/d) δ I) ∧
    success G (algorithm G Δ t b (1/d) δ I) ((1-A*Real.log d/d)*n*d/Δ) ≥ 1-δ ∧
    (algorithmCost n Δ t b (1/d) δ : ℝ) ≤ B*(n+1)^k*(1+Real.log (1/δ))^k) ∧
  (∀ ε : ℝ, 0 < ε → ε < 1 → (horizon n Δ lam c ε : ℝ) ≤
    B*(1+n*(Δ:ℝ)^4*(Real.log (scale t b)+t*Real.log d)/(ε^2*d^2))) ∧
  (∀ I J : State G, ∀ u : Fin n,
    MarkovMixing.IsHardcore G (updateSpin G I.val u false) ∧
    MarkovMixing.IsHardcore G (updateSpin G I.val u true) ∧
    P G lam u I J =
      (if J.val = updateSpin G I.val u true then p lam else 0) +
      (if J.val = updateSpin G I.val u false then 1-p lam else 0))

/-- Full bit implementation clause: actual first terminating preprocessing stage, rounded
fugacity, the recomputed certificate, output law, failure bound and expected bit cost. -/
def BitConclusion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (w : Fin n → List (Fin n)) (A B : ℝ) (k : ℕ) : Prop :=
  let d := D Δ t (b:ℝ)
  let x := scale t (b:ℝ) * d^(2*t-1)
  let c := correction Δ t (b:ℝ)
  ∃ h q : ℕ, ∃ l u : ℚ,
    1 ≤ h ∧ (∀ j : ℕ, 1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1 = none) ∧
    ((parameterStage Δ t b h).run 0).1 = some (q,l,u) ∧
    (l:ℝ) ≤ x ∧ x ≤ (u:ℝ) ∧ (u-l:ℚ) ≤ 1/2 ∧
    |(((l+u)/2:ℚ):ℝ)-x| ≤ 1/4 ∧ x ≤ q ∧ (q:ℝ) ≤ x+2 ∧ 1 ≤ q ∧ q ≤ Δ+2 ∧
    let lam := 1/(q:ℝ)
    |lam/fugacity Δ t (b:ℝ)-1| ≤ B/d ∧
    FiniteConclusion G Δ lam c w ∧
    |Gamma Δ lam c*d/Δ-1| ≤ A*Real.log d/d ∧
    (∀ I : State G, ∀ m : ℕ, 1 ≤ m →
      (∑ σ : Fin n → Bool, bitLaw G Δ t b I.val m σ) = 1 ∧
      MarkovMixing.IsDist (bitOutput G Δ t b I m) ∧
      bitOutput G Δ t b I m = amplifiedLaw G lam I (bitHorizon n) (bitRepeats n m) ∧
      success G (bitOutput G Δ t b I m) ((1-A*Real.log d/d)*n*d/Δ) ≥ 1-Real.exp (-(m:ℝ)) ∧
      expectedBitCost G Δ t b I m ≤ ENNReal.ofReal (B*(n+ratBits b+m+bits t+1)^k))

/-- K_{1,t,t}-free in the source's non-induced sense. -/
def ApexFree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ) : Prop :=
  ∀ u : Fin n, bicliques (G.induce (↑(G.neighborFinset u) : Set (Fin n))) t = ∅

/-- A form used for both stated leading-constant-one specializations. -/
def LeadingOne {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b ζ B : ℝ) (k : ℕ) : Prop :=
  ∀ I : State G, ∀ δ : ℝ, 0 < δ → δ < 1 →
    success G (algorithm G Δ t b (1/D Δ t b) δ I) ((1-ζ)*n*Real.log Δ/Δ) ≥ 1-δ ∧
    (algorithmCost n Δ t b (1/D Δ t b) δ : ℝ) ≤ B*(n+1)^k*(1+Real.log (1/δ))^k

end
end LocalOccupancyIS.Glauber


