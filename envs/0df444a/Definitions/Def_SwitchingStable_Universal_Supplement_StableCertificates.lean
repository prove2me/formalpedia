-- Prove2me | Definitions.Def_SwitchingStable_Universal_Supplement_StableCertificates
-- name    : SwitchingStable_Universal_Supplement_StableCertificates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:35:43.202198+00:00
-- url     : https://prove2.me/theorems/00e080dc-4631-47c8-877a-c5eba9a71b79
-- title:
--   Exact stable-edge witnesses, rotations, private pools and side costs
-- statement:
--   Let $I$ be a complete strict market with $n$ agents on each side, and let $\mu$ be a stable perfect matching. For an agent $u$, write $d_u$ for the number of stable partners, listed in that agent's own order, and $\operatorname{idx}_u(\mu)$ for the zero-based index of its partner. For $1\le j<d_u$, the exact witness set is
--
--   $$W^\mu_{u,j}=\{p\ne u:\ \forall\nu\in\operatorname{Stab}(I),\ \nu(p)=\mu(p)\Rightarrow(\operatorname{idx}_u(\nu)\ge j\iff\operatorname{idx}_u(\mu)\ge j)\}.$$
--
--   For $q=\operatorname{idx}_u(\mu)$, the canonical witness is $\mu^{-1}(v_{j-1})$ when $j\le q$ and $\mu^{-1}(v_j)$ otherwise. A transition rotation is an actual exposed rotation whose elimination takes the partner index of $u$ from $j-1$ to $j$. Participation of a man or woman means occurrence in its cyclic list. Existence and uniqueness are conclusions of Lemma 19; no arbitrary rotation is selected in this definition.
--
--   The stable certificate family contains the index vectors of all stable matchings. Its witness predicate uses equality of coordinate indices; the equality with the exact fixed-edge witness set above is asserted in Theorem 3. This makes the generic certificate endpoints apply directly. A valid subset family chooses subsets of these exact witnesses, and `ContainsCanonical` means that every canonical witness remains.
--
--   A fixed subset $A$ is $r$-private if, for every stable $\mu$ and every $u\in A$, it is possible to choose sets $Q^\mu_{u,j}\subseteq W^\mu_{u,j}$ with at least $r$ elements, pairwise disjoint over $j$. Choices can depend on $\mu,u$, and precede all priorities. There is no disjointness requirement across different agents or matchings.
--
--   Let $T$ be the published independent uniform priorities, independent of the uniform choice of $\mu$ from the whole stable set, and $P_u=\{p:T_p<T_u\}$. Define
--
--   $$K_S=\mathbb E_{\mu,T}\sum_{u\in S}\log(R_u^\mu(P_u)-L_u^\mu(P_u)).$$
--
--   The uniform expectation over matchings is the finite sum divided by their actual number; the reveal expectation uses the published product law. The sides $U,V$ use $I$ and the reversed market respectively, with matchings inverted on $V$. This introduces no assumption on the original preferences. The same expression with an explicit witness-subset family defines its cost.
--
--   **Formalization Note** Interval lengths use real subtraction. Nonzero stable count, positivity and integrability are established in Theorem 3 rather than postulated. Published exposed rotations use the first acceptable woman below the current partner, not an arbitrary stable cycle.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), pp. 35–37, PDF pp. 36–38, Appendix H, exact witnesses, transition rotations, private subsets and side expectations

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Supplement_Certificate
import Definitions.Def_SwitchingStable_Universal_Model
import Definitions.Def_SwitchingStable_Universal_Reveal
import Definitions.Def_StableCount_Rotation

namespace SwitchingStable.Universal.Supplement

open StableMatching MeasureTheory
variable {n : ℕ}

/-- Side reversal exchanges the two rank families; matchings are then inverted. -/
def reverse (I : Instance n) : Instance n := ⟨I.womanRank, I.manRank⟩
inductive Side where | U | V deriving DecidableEq

def onSide (I : Instance n) : Side → Instance n | .U => I | .V => reverse I

def indexVector (I : Instance n) (μ : Matching n) : Fin n → ℕ := idx I μ

noncomputable def exactWitness (I : Instance n) (μ : Matching n)
    (u : Fin n) (j : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun p => p ≠ u ∧
    ∀ ν : Matching n, I.IsStable ν → ν p = μ p → (j ≤ idx I ν u ↔ j ≤ idx I μ u)

noncomputable def canonical (I : Instance n) (μ : Matching n) (u : Fin n) (j : ℕ) : Fin n :=
  μ.symm (atPartner I μ u (if j ≤ idx I μ u then (j : ℤ) - 1 else j))

/-- Actual exposure and elimination at the adjacent stable-partner transition. -/
def Transition (I : Instance n) (u : Fin n) (j : ℕ) (ρ : StableCount.Rot n) : Prop :=
  ∃ α β : Matching n, I.IsStable α ∧ I.IsStable β ∧
    StableCount.IsExposed I α ρ ∧ StableCount.IsElim α ρ β ∧
    idx I α u + 1 = j ∧ idx I β u = j

def manParticipates (ρ : StableCount.Rot n) (p : Fin n) : Prop :=
  ∃ l : List (Fin n × Fin n), (l : Cycle (Fin n × Fin n)) = ρ ∧ p ∈ l.map Prod.fst

def womanParticipates (ρ : StableCount.Rot n) (v : Fin n) : Prop :=
  ∃ l : List (Fin n × Fin n), (l : Cycle (Fin n × Fin n)) = ρ ∧ v ∈ l.map Prod.snd

/-- The entire stable-index family; the certificate uses all valid coordinate witnesses. -/
noncomputable def stableCertificate (I : Instance n) : Certificate n where
  d := degree I
  family := (Finset.univ.filter fun μ : Matching n => I.IsStable μ).image (indexVector I)
  witnesses z u j := by
    classical
    exact Finset.univ.filter fun p => p ≠ u ∧
      ∀ ν : Matching n, I.IsStable ν → idx I ν p = z p → (j ≤ idx I ν u ↔ j ≤ z u)

abbrev WitnessFamily (n : ℕ) := (Fin n → ℕ) → Fin n → ℕ → Finset (Fin n)

noncomputable def withWitnesses (I : Instance n) (H : WitnessFamily n) : Certificate n :=
  { stableCertificate I with witnesses := H }

def IsSubsetFamily (I : Instance n) (H : WitnessFamily n) : Prop :=
  ∀ z ∈ (stableCertificate I).family, ∀ u j, 1 ≤ j → j < degree I u →
    H z u j ⊆ (stableCertificate I).witnesses z u j

def ContainsCanonical (I : Instance n) (H : WitnessFamily n) : Prop :=
  ∀ μ : Matching n, I.IsStable μ → ∀ u j, 1 ≤ j → j < degree I u →
    canonical I μ u j ∈ H (indexVector I μ) u j

/-- Pool choices precede reveal priorities and are disjoint only for fixed (μ,u). -/
def PrivateOn (I : Instance n) (A : Finset (Fin n)) (r : ℕ) : Prop :=
  ∀ μ : Matching n, I.IsStable μ → ∀ u ∈ A,
    ∃ Q : ℕ → Finset (Fin n),
      (∀ j, 1 ≤ j → j < degree I u → Q j ⊆ exactWitness I μ u j ∧ r ≤ (Q j).card) ∧
      ∀ j k, 1 ≤ j → j < degree I u → 1 ≤ k → k < degree I u →
        j ≠ k → Disjoint (Q j) (Q k)

noncomputable def logLengthSum (B : Certificate n) (z : Fin n → ℕ) (t : Sample n) : ℝ :=
  ∑ u : Fin n, Real.log (B.length z u (predecessors u t))

/-- Uniform average over every stable matching, independent of all reveal priorities. -/
noncomputable def certificateCost (I : Instance n) (B : Certificate n) : ℝ :=
  (∑ μ : StableSet I, ∫ t, logLengthSum B (indexVector I μ.val) t ∂revealLaw n) /
    (StableCount.numStable I : ℝ)

noncomputable def sideCost (I : Instance n) (s : Side) : ℝ :=
  certificateCost (onSide I s) (stableCertificate (onSide I s))

end SwitchingStable.Universal.Supplement


