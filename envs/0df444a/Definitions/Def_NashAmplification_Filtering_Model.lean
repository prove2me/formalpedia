-- Prove2me | Definitions.Def_NashAmplification_Filtering_Model
-- name    : NashAmplification_Filtering_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:14:48.173826+00:00
-- url     : https://prove2.me/theorems/b3fc7b13-89f8-4f4b-9d86-68378dd03fc2
-- title:
--   Finite game scores and symmetry
-- statement:
--   Let $G$ have $k$ players, action sets $A_r=\operatorname{Fin}(n_r)$, and real payoffs $u_r$. A lottery is a nonnegative function with sum one, as in the referenced finite-game vocabulary. For a joint distribution $Q$ on $A=\prod_r A_r$, write $x_r$ for its marginal. Define
--   $$V_Q(a)=\frac1k\sum_r u_r(a_r,x_{-r}),\qquad V_Q^*=\max_{a\in A}V_Q(a).$$
--   Opponents play independently under their marginals, even when $Q$ is correlated. The score-test mass is $Q\{a:V_Q^*-V_Q(a)\le\Delta\}$. Nonempty action sets and $k\ge2$ are explicit in the theorems. Symmetry means $U_{\pi(i)}(y\circ\pi^{-1})=U_i(y)$ for every player permutation. Binary payoffs mean each pure payoff equals zero or one. The mixed-radix tuple rank fixes the coordinate ordering used throughout.
--
--   These definitions supply the shared game interface and the score in (2.2)–(2.4).
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, §2 and (2.2)–(2.4), PDF pp. 6–7 (printed pp. 5–6); Lemma 2.4, PDF p. 10 (printed p. 9)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_RubinsteinNash_WeakNash_ApproxEquilibria

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Source §2, PDF 6–7: nonempty action counts are imposed by each statement. -/
abbrev Tuple {k : ℕ} (n : Fin k → ℕ) := (r : Fin k) → Fin (n r)
abbrev Mixed {k : ℕ} (n : Fin k → ℕ) := (r : Fin k) → Fin (n r) → ℝ
abbrev Utility {k : ℕ} (n : Fin k → ℕ) := Fin k → Tuple n → ℝ
abbrev Seq {k : ℕ} (n : Fin k → ℕ) (t : ℕ) := Fin t → Tuple n

def BoundedGame {k : ℕ} {n : Fin k → ℕ} (u : Utility n) : Prop :=
  ∀ r a, u r a ∈ Set.Icc (0 : ℝ) 1

def marginal {k : ℕ} {n : Fin k → ℕ} (Q : Tuple n → ℝ) : Mixed n :=
  fun r b => ∑ a : Tuple n, if a r = b then Q a else 0

/-- (2.2); purePayoff uses the independent product of the marginals. -/
def score {k : ℕ} {n : Fin k → ℕ} (u : Utility n) (Q : Tuple n → ℝ)
    (a : Tuple n) : ℝ :=
  (∑ r, DGPNash.NashMap.purePayoff u (marginal Q) r (a r)) / k

def maxScore {k : ℕ} {n : Fin k → ℕ} (u : Utility n) (Q : Tuple n → ℝ) : ℝ :=
  sSup (Set.range (score u Q))

def scoreMass {k : ℕ} {n : Fin k → ℕ} (u : Utility n) (Q : Tuple n → ℝ)
    (Δ : ℝ) : ℝ :=
  ∑ a, if maxScore u Q - score u Q a ≤ Δ then Q a else 0

/-- Explicit mixed-radix rank, with the first player's coordinate most significant. -/
def tupleRank {k : ℕ} {n : Fin k → ℕ} (a : Tuple n) : ℕ :=
  ((List.finRange k).map fun r => (n r, (a r).val)).foldl (fun z p => z * p.1 + p.2) 0

def IsSymmetric {C : ℕ} {Z : Type} (u : Fin C → (Fin C → Z) → ℝ) : Prop :=
  ∀ (π : Equiv.Perm (Fin C)) i y, u (π i) (y ∘ π.symm) = u i y

def IsBinary {C : ℕ} {Z : Type} (u : Fin C → (Fin C → Z) → ℝ) : Prop :=
  ∀ i y, u i y = 0 ∨ u i y = 1
end NashAmplification.Filtering


