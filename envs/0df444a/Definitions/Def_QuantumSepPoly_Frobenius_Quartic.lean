-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_Quartic
-- name    : QuantumSepPoly_Frobenius_Quartic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:00.982088+00:00
-- url     : https://prove2.me/theorems/ac57bdac-adb1-4321-ba02-4d10e1b37b5a
-- title:
--   Quartic objectives and dimension-independent parameters
-- statement:
--   Under the Section 4 assumptions, put
--   $$Q_M(x,y)=d^{-2}\operatorname{Re}((x\otimes y)^*M(x\otimes y)),\quad \Lambda_M(x,y)=Q_M(x,y)-\lambda(\|x\|_2^2/d-1)^2-\lambda(\|y\|_2^2/d-1)^2.$$
--   The sphere constraint is $\|x\|_2^2=\|y\|_2^2=d$. The flat-input predicate records Hermiticity, both zero partial traces, and $d^2\|M\|_{\max}\le\gamma$. The displayed choices of $\sigma,t,\kappa,\Delta$ on pp.15–16 and $\lambda,\varepsilon$ on p.17 are computed functions; the zero-$\gamma$ branch takes $t=1/2$. Supremum definitions range only over the stated feasible vectors, with attainment a separate theorem obligation.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 13 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_PartialTraces
import Definitions.Def_QuantumSepPoly_Frobenius_SeparableStates

noncomputable section

namespace QuantumSepPoly.Frobenius

/-- §4, pp.13,16: the source's sqrt(d)-normalized quartic and penalty. -/
def Q {d : ℕ} (M : Bip d) (x y : Vec d) : ℝ := productValue M x y / (d : ℝ)^2

def penalty {d : ℕ} (M : Bip d) (lam : ℝ) (x y : Vec d) : ℝ :=
  Q M x y - lam * (vecSq x / d - 1)^2 - lam * (vecSq y / d - 1)^2

def AmplitudeBound {d : ℕ} (κ : ℝ) (x : Vec d) : Prop := ∀ i, ‖x i‖ ≤ κ

def CloseCoordinates {d : ℕ} (ε : ℝ) (x w : Vec d) : Prop := ∀ i, ‖x i - w i‖ ≤ ε

def FlatInput {d : ℕ} (M : Bip d) (γ : ℝ) : Prop :=
  M.IsHermitian ∧ trace0 M = 0 ∧ trace1 M = 0 ∧ (d : ℝ)^2 * maxEntry M ≤ γ

def sphereValue {d : ℕ} (M : Bip d) : ℝ :=
  sSup {v | ∃ x y : Vec d, vecSq x = d ∧ vecSq y = d ∧ v = Q M x y}

def boundedSphereValue {d : ℕ} (M : Bip d) (κ : ℝ) : ℝ :=
  sSup {v | ∃ x y : Vec d, vecSq x = d ∧ vecSq y = d ∧
    AmplitudeBound κ x ∧ AmplitudeBound κ y ∧ v = Q M x y}

/-- Quantitative parameter choices in the proof of Lemma 4.1, pp.15–16.
The gamma=0 branch is total and dimension independent. -/
def sigmaParam (γ η : ℝ) : ℝ := max 1 (12 * γ / η)
def tParam (γ η : ℝ) : ℝ := if γ = 0 then 1/2 else
  min (1/2) (η / (24 * γ * (sigmaParam γ η + 1)^4))
def kappaParam (γ η : ℝ) : ℝ := Real.sqrt 2 * (sigmaParam γ η + 1)
def deltaParam (γ η : ℝ) : ℝ := max (16 / (tParam γ η)^2)
  (96 * γ * (sigmaParam γ η + 1)^4 / (η * (tParam γ η)^2))

/-- Lemma 4.4 uses Lemma 4.1 with accuracy eta/4. -/
def discKappa (γ η : ℝ) : ℝ := kappaParam γ (η / 4)
def discDelta (γ η : ℝ) : ℝ := deltaParam γ (η / 4)
def discLambda (γ η : ℝ) : ℝ := 1 + (γ^2 + γ^2 * (discKappa γ η)^4) / η
def discEpsilon (γ η : ℝ) : ℝ := η /
  (16 * γ * (discKappa γ η)^3 +
    32 * discLambda γ η * discKappa γ η * ((discKappa γ η)^2 + 1))

end QuantumSepPoly.Frobenius


