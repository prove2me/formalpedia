-- Prove2me | Definitions.Def_StrategicPolicy_MonotoneBinary_Setting
-- name    : StrategicPolicy_MonotoneBinary_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:07.737617+00:00
-- url     : https://prove2.me/theorems/40ac4cc5-6006-4742-b227-c1df1ab0558b
-- title:
--   §§2–4, pp. 3–6 — strategic policy model and outcome monotonic costs
-- statement:
--   An individual begins at one of $m\ge1$ feature values $x_1,\ldots,x_m$. The initial mass at $x_i$ is $p_i=P(x_i)$, its positive-outcome probability is $q_i=P(y=1\mid x_i)$, and the decision maker pays $\gamma\in(0,1)$ per positive decision. A policy $\pi$ gives a positive decision with probability $\pi_i\in[0,1]$. The benefit of occupying $x_i$ is $\pi_i$; changing from $x_i$ to $x_j$ costs $c_{ij}$. Staying costs zero. A change to a distinct value with weakly higher outcome has positive cost. Outcomes are distinct and indexed from highest to lowest.
--
--   Each individual chooses a value maximizing $\pi_j-c_{ij}$. Among tied maximizers, she chooses the value with highest $q_j$; a remaining tie is resolved by the lowest index. If $r_\pi(i)$ is that choice, the decision maker's utility and the meaning of optimality are
--
--   $$
--   u(\pi,\gamma)=\sum_{i=1}^{m}p_i(q_{r_\pi(i)}-\gamma)\pi_{r_\pi(i)},\qquad
--   \pi^*\in[0,1]^m,\quad u(\pi^*,\gamma)\ge u(\rho,\gamma)\ \text{for all }\rho\in[0,1]^m.
--   $$
--
--   An outcome monotonic policy satisfies $\pi_i<\pi_j\Rightarrow q_i<q_j$. An outcome monotonic cost has the two equivalences printed in §4 for distinct indices: strict outcome improvement along a triple corresponds to the two stated strict cost comparisons, and worsening outcome between distinct values corresponds to zero cost. Additivity means $c_{ij}+c_{jk}=c_{ik}$ along a strictly outcome increasing chain. A binary policy satisfies (9) at each value above $\gamma$ and is outcome monotonic.
--
--   These definitions supply the common model for Proposition 2, Theorem 3, and the Appendix A.3 milestones.
--
--   **Formalization Note** The paper's strict biconditional in (1) conflicts with equal policy values allowed by (9); this model uses the monotonic implication described above. The cost equivalences exclude equal indices, staying is free, additivity is restricted to increasing outcome chains, and outcomes are distinct. These are the disclosed readings of printed slips 1–4. $x_1$ is Lean index $0$.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, pp. 3–6, (1), (2), (4), (5), (7), (9), and §4 cost definitions

import Mathlib

namespace StrategicPolicy.MonotoneBinary

variable {m : ℕ}

def Policies (m : ℕ) : Set (Fin m → ℝ) :=
  {π | ∀ i, π i ∈ Set.Icc (0 : ℝ) 1}

/-- The possible maximizers of individual benefit minus change cost. -/
noncomputable def argmax (c : Fin m → Fin m → ℝ) (π : Fin m → ℝ) (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun k => ∀ l, π l - c i l ≤ π k - c i k)

/-- Among benefit maximizers, retain those with the highest outcome. -/
noncomputable def bestOutcome (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ) (i : Fin m) :
    Finset (Fin m) :=
  (argmax c π i).filter (fun k => ∀ l ∈ argmax c π i, q l ≤ q k)

/-- The least index resolves any remaining tie in outcomes. -/
noncomputable def br [NeZero m] (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ) (i : Fin m) : Fin m := by
  have hM : (argmax c π i).Nonempty := by
    obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
      (fun k : Fin m => π k - c i k) Finset.univ_nonempty
    refine ⟨k, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_univ _, fun l => hk l (Finset.mem_univ _)⟩
  have hB : (bestOutcome c q π i).Nonempty := by
    obtain ⟨k, hkM, hk⟩ := Finset.exists_max_image (argmax c π i) q hM
    refine ⟨k, Finset.mem_filter.mpr ?_⟩
    exact ⟨hkM, fun l hl => hk l hl⟩
  exact (bestOutcome c q π i).min' hB

noncomputable def u [NeZero m] (p q : Fin m → ℝ) (γ : ℝ)
    (c : Fin m → Fin m → ℝ) (π : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, p i * (q (br c q π i) - γ) * π (br c q π i)

def Optimal [NeZero m] (p q : Fin m → ℝ) (γ : ℝ)
    (c : Fin m → Fin m → ℝ) (π : Fin m → ℝ) : Prop :=
  π ∈ Policies m ∧ IsMaxOn (u p q γ c) (Policies m) π

structure Standing [NeZero m] (p q : Fin m → ℝ) (γ : ℝ)
    (c : Fin m → Fin m → ℝ) : Prop where
  p_nonneg : ∀ i, 0 ≤ p i
  p_sum : ∑ i : Fin m, p i = 1
  q_range : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1
  gamma_pos : 0 < γ
  gamma_lt_one : γ < 1
  cost_self : ∀ i, c i i = 0
  positive_improvement : ∀ i j, i ≠ j → q i ≤ q j → 0 < c i j
  outcome_order : StrictAnti q

def OMPolicy (q π : Fin m → ℝ) : Prop :=
  ∀ i j, π i < π j → q i < q j

def OMCost (q : Fin m → ℝ) (c : Fin m → Fin m → ℝ) : Prop :=
  (∀ i j k, i ≠ j → j ≠ k → i ≠ k →
    (q i < q j ∧ q j < q k ↔ c i j < c i k ∧ c j k < c i k)) ∧
  (∀ i j, i ≠ j → (q j < q i ↔ c i j = 0))

def AdditiveCost (q : Fin m → ℝ) (c : Fin m → Fin m → ℝ) : Prop :=
  ∀ i j k, q i < q j → q j < q k → c i j + c j k = c i k

def BinaryProperty (q : Fin m → ℝ) (γ : ℝ)
    (c : Fin m → Fin m → ℝ) (π : Fin m → ℝ) : Prop :=
  ∀ i j : Fin m, j.val + 1 = i.val → γ < q i →
    (π i = π j ∨ π i = max 0 (π j - c i j))

def OMBinary (q : Fin m → ℝ) (γ : ℝ)
    (c : Fin m → Fin m → ℝ) (π : Fin m → ℝ) : Prop :=
  OMPolicy q π ∧ BinaryProperty q γ c π

def Violator (γ : ℝ) (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ)
    (i j : Fin m) : Prop :=
  j.val + 1 = i.val ∧ γ < q i ∧
    ((π j - c i j < π i ∧ π i < π j) ∨ π i < π j - c i j)

def HighestViolator (γ : ℝ) (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ)
    (i : Fin m) : Prop :=
  ∀ i' j' : Fin m, i'.val < i.val → ¬ Violator γ c q π i' j'

end StrategicPolicy.MonotoneBinary


