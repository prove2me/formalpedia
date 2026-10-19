-- Prove2me | Definitions.Def_UnknownProphet_NoSamples_Model
-- name    : UnknownProphet_NoSamples_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:11.407484+00:00
-- url     : https://prove2.me/theorems/39e4be6c-f709-40bc-a07e-b91621fdeb64
-- title:
--   §2 and §3, pp. 5–8 — stopping rules, guarantees, obliviousness, hard instance and record rule
-- statement:
--   A **$(k,n)$ stopping rule** observes $k$ independent samples from a nonnegative law $F$, followed by $n$ independent values $X_1,\ldots,X_n$. At time $i$, its value $r_i$ is the conditional probability of stopping given the samples, values through $X_i$, and survival through time $i-1$. Each $r_i$ lies in $[0,1]$. Conditional on a complete history, the probability of stopping at $i$ is
--
--   $$
--   \Pr(\tau=i\mid s,x)=\left(\prod_{j<i}(1-r_j(s,x_1,\ldots,x_j))\right)r_i(s,x_1,\ldots,x_i).
--   $$
--
--   The selected payoff is $X_\tau$, with $X_\infty=0$, and the benchmark is $\max_i X_i$. A rule has **guarantee** $\alpha$ if $\mathbb E_F[X_\tau]\ge\alpha\mathbb E_F[\max_i X_i]$ for every finite nonnegative law $F$.
--
--   Definition 1 says that a rule is **$\varepsilon$ value oblivious** on $V\subseteq\mathbb N$ if each time $i$ has a constant $q_i\in[0,1]$ such that $r_i$ belongs to $[q_i-\varepsilon,q_i+\varepsilon)$ whenever the samples and observed values are pairwise distinct members of $V$ and the current value exceeds all earlier values and samples. Definition 2 says a zero-sample rule is **order oblivious** when permuting distinct nonnegative past values leaves its current stop probability unchanged.
--
--   The hard law of p. 7 has $n^3$ small distinct atoms $v_j$, each of mass $n^{-3}(1-n^{-2})$, and one atom $u$ of mass $n^{-2}$, with $u\ge n^3v_j$. The coupled rule $\hat r$ stops only on records, with probability $q_i$ on the $i$th record. Its success probability is averaged over all $n!$ relative-rank permutations.
--
--   These shared definitions support the six milestone statements and the main impossibility theorem.
--
--   **Formalization Note** Lean uses zero-based indices, so $X_1$ and $r_1$ have index $0$. Rule inputs are real vectors and stop values are in $[0,1]$; only the law is supported on nonnegative reals. $V:\mathrm{Set}\;\mathbb N$ can contain $0$, unlike the paper's positive-integer convention; on infinite sets this makes no difference. The printed $r_i$ in Definition 2 is read as $r_j$, its current time. A rule “never selects” time $i$ when its conditional stopping probability there is zero on every history. The maximum for $n=0$ is Lean's default $0$; the substantive statements use positive $n$ or are trivial at $n=0$.
-- source:
--   Correa, Dütting, Fischer & Schewior, Prophet Inequalities for I.I.D. Random Variables from an Unknown Distribution, arXiv:1811.06114v2, p. 5, §2; p. 6, Definition 1; p. 7, proof of Theorem 2; p. 8, Definition 2 and proof of Theorem 2

import Mathlib
import Definitions.Def_UnknownProphet_NoSamples_FinDist

namespace UnknownProphet.NoSamples

open Finset

/-- A randomized `(k,n)` stopping rule. `r i s x` is the conditional probability
of stopping on the `(i+1)`st observed value, given the samples and the prefix. -/
structure StoppingRule (k n : ℕ) where
  r : (i : Fin n) → (Fin k → ℝ) → (Fin (i.val + 1) → ℝ) → ℝ
  r_mem : ∀ i s x, r i s x ∈ Set.Icc (0 : ℝ) 1

/-- Conditional probability of stopping at index `i`, given all samples and draws. -/
noncomputable def stopProb {k n : ℕ} (R : StoppingRule k n)
    (s : Fin k → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (∏ j ∈ Finset.Iio i,
    (1 - R.r j s (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt)))) *
    R.r i s (x ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt))

/-- Expected value selected by a rule, with the payoff on never stopping equal to zero. -/
noncomputable def expStop {k n : ℕ} (F : FinDist) (R : StoppingRule k n) : ℝ :=
  ∑ s ∈ Fintype.piFinset (fun _ : Fin k => F.supp),
    ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
      iidWeight F s * iidWeight F x * ∑ i, stopProb R s x i * x i

/-- Expected maximum of `n` independent draws. -/
noncomputable def expMax (F : FinDist) (n : ℕ) : ℝ :=
  ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
    iidWeight F x * ⨆ i, x i

/-- Uniform approximation guarantee over all finitely supported laws. -/
def HasGuarantee {k n : ℕ} (R : StoppingRule k n) (α : ℝ) : Prop :=
  ∀ F : FinDist, α * expMax F n ≤ expStop F R

/-- The constants witnessing value obliviousness in Definition 1. -/
def ValueObliviousWith {k n : ℕ} (ε : ℝ) (R : StoppingRule k n)
    (V : Set ℕ) (q : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, q i ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ (s : Fin k → ℕ) (v : Fin (i.val + 1) → ℕ),
      (∀ j, s j ∈ V) → (∀ j, v j ∈ V) →
      Function.Injective (Fin.append s v) →
      (∀ j, s j < v (Fin.last i.val)) →
      (∀ j, j ≠ Fin.last i.val → v j < v (Fin.last i.val)) →
      R.r i (fun j => (s j : ℝ)) (fun j => (v j : ℝ)) ∈
        Set.Ico (q i - ε) (q i + ε)

/-- Definition 1: `ε` value obliviousness on `V`. -/
def ValueOblivious {k n : ℕ} (ε : ℝ) (R : StoppingRule k n)
    (V : Set ℕ) : Prop :=
  ∃ q : Fin n → ℝ, ValueObliviousWith ε R V q

/-- Definition 2: permuting previous distinct nonnegative values cannot change
the current conditional stop probability. The final coordinate is fixed. -/
def OrderOblivious {n : ℕ} (R : StoppingRule 0 n) : Prop :=
  ∀ (i : Fin n) (v : Fin (i.val + 1) → ℝ),
    Function.Injective v → (∀ j, 0 ≤ v j) →
    ∀ π : Equiv.Perm (Fin (i.val + 1)),
      π (Fin.last i.val) = Fin.last i.val →
      R.r i ![] (v ∘ π) = R.r i ![] v

/-- The rule has zero probability of selecting index `i` on every
nonnegative history in the paper's domain. -/
def NeverSelects {k n : ℕ} (R : StoppingRule k n) (i : Fin n) : Prop :=
  ∀ s x, (∀ j, 0 ≤ s j) → (∀ j, 0 ≤ x j) → stopProb R s x i = 0

/-- The coupled record rule of p. 8. -/
noncomputable def hatRule {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) : StoppingRule 0 n where
  r i _ x := if ∀ j, j ≠ Fin.last i.val → x j < x (Fin.last i.val) then q i else 0
  r_mem := by
    intro i s x
    split_ifs
    · exact hq i
    · exact ⟨le_refl 0, by norm_num⟩

/-- Conditional probability of selecting an index attaining the maximum. -/
noncomputable def pickMaxProb {n : ℕ} (R : StoppingRule 0 n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, if ∀ j, x j ≤ x i then stopProb R ![] x i else 0

/-- Success probability of the record rule under uniformly random relative ranks. -/
noncomputable def recordRuleSuccess {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) : ℝ :=
  (1 / (n.factorial : ℝ)) *
    ∑ σ : Equiv.Perm (Fin n),
      pickMaxProb (hatRule q hq) (fun i => ((σ i : ℕ) : ℝ))

/-- The heavy atom and `n^3` small atoms of the hard law on p. 7. -/
def IsHardInstance (n : ℕ) (F : FinDist) (v : Fin (n ^ 3) → ℝ)
    (u : ℝ) : Prop :=
  Function.Injective v ∧ (∀ j, 0 ≤ v j) ∧ (∀ j, v j ≠ u) ∧
  (∀ j, (n : ℝ) ^ 3 * v j ≤ u) ∧
  F.supp = insert u (Finset.univ.image v) ∧
  (∀ j, F.w (v j) = 1 / (n : ℝ) ^ 3 * (1 - 1 / (n : ℝ) ^ 2)) ∧
  F.w u = 1 / (n : ℝ) ^ 2

/-- Probability that the largest of `n` draws is `u`. -/
noncomputable def probMaxEq (F : FinDist) (n : ℕ) (u : ℝ) : ℝ :=
  ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
    if (⨆ i, x i) = u then iidWeight F x else 0

end UnknownProphet.NoSamples


