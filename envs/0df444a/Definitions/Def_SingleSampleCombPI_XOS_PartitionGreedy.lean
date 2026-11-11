-- Prove2me | Definitions.Def_SingleSampleCombPI_XOS_PartitionGreedy
-- name    : SingleSampleCombPI_XOS_PartitionGreedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T09:08:33.61583+00:00
-- url     : https://prove2.me/theorems/5885f8d6-de42-4dfe-86cd-97f60dae4d29
-- title:
--   Online greedy over a simple partition matroid with random order and random retention
-- statement:
--   A finite ground set $N$ is **partitioned** into nonempty pairwise disjoint parts $P_1,\dots,P_\ell$ covering $N$. A set $S\subseteq N$ is feasible if $|S\cap P_i|\le1$ for every $i$, and $\max_{S\text{ feasible}}f(S)$ is the offline optimum. The marginal value is $f(u\mid A)=f(A\cup\{u\})-f(A)$.
--
--   Parts arrive one at a time; an **online selection rule** maps the list of parts processed so far and the arriving part to an element of that part, so the chosen set after a list of parts is determined. The rule is **$\delta$-approximately greedy** if, from every history, its choice $u$ in the arriving part $P_i$ satisfies $f(u\mid A)\ge f(u'\mid A)-\delta$ for every $u'\in P_i$, where $A$ is the current chosen set; $\delta=0$ is exact greedy with arbitrary tie-breaking that may depend on the whole history.
--
--   For a retention vector $R$ and an order $\pi$, the rule processes the retained parts in the order of $\pi$. The quantity $\mathbb E[f(A)]$ averages over independent Bernoulli$(q)$ retention and a uniformly random order.
--
--   **Formalization Note** Validity of a rule is required at all histories; any history-dependent greedy tie-breaking extends to such a rule because parts are nonempty.
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, Theorem 4.3 (PDF p. 20) and Lemma D.1 (PDF p. 41)

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Model

namespace SingleSampleCombPI.XOS

/-! # Online greedy over a simple partition matroid (Theorem 4.3, Lemma D.1)

Chawla–Dang, STOC 2027 submission #30, PDF pp. 20 and 41.  A finite ground set `N` is
partitioned into parts `P_1, …, P_ℓ`; parts arrive one at a time and the algorithm irrevocably
picks one element of each arriving part. -/

variable {N : Type*} [DecidableEq N] {ℓ : ℕ}

/-- `P_1, …, P_ℓ` are nonempty, pairwise disjoint and cover `N`. -/
def IsPartition (P : Fin ℓ → Finset N) : Prop :=
  (∀ i, (P i).Nonempty) ∧ (∀ i i', i ≠ i' → Disjoint (P i) (P i')) ∧ ∀ e, ∃ i, e ∈ P i

/-- Monotonicity of a set function. -/
def SetMonotone (f : Finset N → ℝ) : Prop := ∀ S T, S ⊆ T → f S ≤ f T

/-- Feasibility in the simple partition matroid: `|S ∩ P_i| ≤ 1` for every part. -/
def PartFeasible (P : Fin ℓ → Finset N) (S : Finset N) : Prop := ∀ i, (S ∩ P i).card ≤ 1

/-- `max_{S ⊆ N, |S ∩ P_i| ≤ 1} f(S)` (the empty set is feasible). -/
noncomputable def optVal [Fintype N] (f : Finset N → ℝ) (P : Fin ℓ → Finset N) : ℝ := by
  classical
  exact ((Finset.univ : Finset (Finset N)).filter (PartFeasible P)).sup'
    ⟨∅, by simp [PartFeasible]⟩ f

/-- The marginal value `f(u | A) = f(A ∪ {u}) - f(A)`. -/
def marg (f : Finset N → ℝ) (A : Finset N) (u : N) : ℝ := f (insert u A) - f A

/-- The set chosen by an online selection rule after processing the parts listed in `L`, in
order.  The rule maps the list of previously processed parts and the current part to the
chosen element, so its tie-breaking may use the entire history but never the future. -/
def chosen (rule : List (Fin ℓ) → Fin ℓ → N) (L : List (Fin ℓ)) : Finset N :=
  (L.foldl (fun st i => (st.1 ++ [i], insert (rule st.1 i) st.2))
    (([] : List (Fin ℓ)), (∅ : Finset N))).2

/-- A `δ`-approximately greedy rule: from every history it picks an element of the arriving
part whose marginal value on the current set is within additive `δ` of the best one.
`δ = 0` is exact greedy with arbitrary (history-dependent) tie-breaking. -/
def IsApproxGreedyRule (f : Finset N → ℝ) (P : Fin ℓ → Finset N) (δ : ℝ)
    (rule : List (Fin ℓ) → Fin ℓ → N) : Prop :=
  ∀ hist i, rule hist i ∈ P i ∧
    ∀ u ∈ P i, marg f (chosen rule hist) u - δ ≤ marg f (chosen rule hist) (rule hist i)

/-- The retained parts (`R i = true`) in the order of the permutation `π` (`π t` arrives at
time `t`). -/
def arrivalList (R : Fin ℓ → Bool) (π : Equiv.Perm (Fin ℓ)) : List (Fin ℓ) :=
  ((List.finRange ℓ).map π).filter (fun i => R i)

/-- `E[f(A)]` when each part is retained independently with probability `q` and the retained
parts are processed by `rule` in uniformly random (relative) order. -/
noncomputable def retainedGreedyExp (f : Finset N → ℝ) (q : ℝ)
    (rule : List (Fin ℓ) → Fin ℓ → N) : ℝ :=
  bernExpR q (fun R : Fin ℓ → Bool =>
    avgR (fun π : Equiv.Perm (Fin ℓ) => f (chosen rule (arrivalList R π))))

end SingleSampleCombPI.XOS


