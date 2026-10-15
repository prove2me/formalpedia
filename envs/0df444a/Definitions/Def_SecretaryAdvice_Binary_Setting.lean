-- Prove2me | Definitions.Def_SecretaryAdvice_Binary_Setting
-- name    : SecretaryAdvice_Binary_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:13.10944+00:00
-- url     : https://prove2.me/theorems/63698526-5bf4-4b94-95c4-22db93b1e268
-- title:
--   Example 5 and §2 — binary-classifier secretary model, information, policies, and success probability
-- statement:
--   Fix $n$ secretaries with distinct ranks, arriving in uniformly random order. Each arrival receives a binary signal $Y$ or $N$. The unique highest-ranked secretary receives $Y$ with probability $p$; every other secretary receives $N$ with probability $p'$. Conditional on the rank order, all signals are independent. The parameters $p,p'$ lie in $[1/2,1]$ in the theorems using this model.
--
--   At round $i$, a stopping policy observes the signals so far and every relative comparison among the first $i$ arrivals. It assigns a stopping probability in $[0,1]$ to this information. Its winning probability is the sum, over outcomes and rounds, of the probability of that outcome times the probability of reaching round $i$, stopping there, and selecting the unique highest-ranked secretary. A threshold policy starts accepting best-so-far arrivals at signal-dependent rounds $t_Y$ and $t_N$.
--
--   These definitions provide a common probability model for the conditional-probability claims, the LP coefficients, and the optimal-policy theorem.
--
--   **Formalization Note** Lean uses zero-based `Fin n` rounds, so paper round $i$ is Lean index $i-1$. The finite outcome weight is $1/n!$ times the product of signal likelihoods. Policies cannot inspect absolute ranks or future observations. The product over earlier continuation probabilities enforces at most one stop.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, pp. 6–9, §2, Example 5, equation (1), and §3

import Mathlib

namespace SecretaryAdvice.Binary

/-- The paper's probability space: a rank permutation and one classifier signal per arrival. -/
abbrev Outcome (n : ℕ) := Equiv.Perm (Fin n) × (Fin n → Bool)

/-- `true` is `Y`; `false` is `N`. -/
def signalLaw (n : ℕ) (p p' : ℝ) (rank : Fin n) (s : Bool) : ℝ :=
  if rank.val + 1 = n then (if s then p else 1 - p)
  else (if s then 1 - p' else p')

/-- Uniform ranks, and conditionally independent signals with the laws of Example 5. -/
noncomputable def weight (n : ℕ) (p p' : ℝ) (ω : Outcome n) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∏ i : Fin n, signalLaw n p p' (ω.1 i) (ω.2 i)

/-- Information at round `i`: every relative comparison among arrivals through `i`, and
their signals. `i` is zero-based while the paper numbers rounds from one. -/
abbrev Info (n : ℕ) (i : Fin n) :=
  (Fin (i.val + 1) → Fin (i.val + 1) → Bool) × (Fin (i.val + 1) → Bool)

/-- The information induced by an outcome, without access to absolute ranks or future signals. -/
def info {n : ℕ} (i : Fin n) (ω : Outcome n) : Info n i :=
  (fun j k => decide (ω.1 ⟨j.val, by omega⟩ ≤ ω.1 ⟨k.val, by omega⟩),
   fun j => ω.2 ⟨j.val, by omega⟩)

/-- The last observed arrival is at least as good as every preceding arrival. -/
def bestSoFar {n : ℕ} (i : Fin n) (x : Info n i) : Prop :=
  ∀ j : Fin (i.val + 1), x.1 j (Fin.last i.val) = true

/-- A randomized stopping policy sees only the information available at each round. -/
abbrev Policy (n : ℕ) := (i : Fin n) → Info n i → ℝ

def ValidPolicy {n : ℕ} (q : Policy n) : Prop :=
  ∀ i x, 0 ≤ q i x ∧ q i x ≤ 1

/-- The unique top rank in a permutation of `Fin n`. -/
def isTop {n : ℕ} (ω : Outcome n) (i : Fin n) : Prop :=
  (ω.1 i).val + 1 = n

/-- The exact winning probability, including the probability of reaching each round. -/
noncomputable def win {n : ℕ} (p p' : ℝ) (q : Policy n) : ℝ := by
  classical
  exact ∑ ω : Outcome n, weight n p p' ω *
    ∑ i : Fin n, (if isTop ω i then (1 : ℝ) else 0) * q i (info i ω) *
      ∏ j ∈ (Finset.univ.filter (fun j : Fin n => j.val < i.val)),
        (1 - q j (info j ω))

/-- Select the first best-so-far secretary at or after the threshold for its signal. -/
noncomputable def thresholdPolicy (n tY tN : ℕ) : Policy n := by
  classical
  exact fun i x => if bestSoFar i x ∧ (if x.2 (Fin.last i.val) then tY else tN) ≤ i.val + 1
    then 1 else 0

/-- Finite event mass, used to state conditional probabilities without a `0/0` convention. -/
noncomputable def mass {n : ℕ} (p p' : ℝ) (A : Outcome n → Prop) : ℝ := by
  classical
  exact ∑ ω : Outcome n, if A ω then weight n p p' ω else 0

end SecretaryAdvice.Binary


