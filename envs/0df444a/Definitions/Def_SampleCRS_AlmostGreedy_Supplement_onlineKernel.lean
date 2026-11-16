-- Prove2me | Definitions.Def_SampleCRS_AlmostGreedy_Supplement_onlineKernel
-- name    : SampleCRS_AlmostGreedy_Supplement_onlineKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:32:55.831322+00:00
-- url     : https://prove2.me/theorems/460f3a99-29b3-49d4-8a06-6260dff458b4
-- title:
--   Randomized online kernels and the independent activation experiment
-- statement:
--   Fix a ground-set size $n$ and capacity $k$. An online kernel assigns an arbitrary real acceptance bias in $[0,1]$ to each complete past activation/action history and the current activation. Arrival labels are positions in a fixed, advance-known order. The kernel has no activation-probability argument; all feasible randomized policies are represented through conditional probabilities on the finite observation tree.
--
--   For online vector $X$ and action vector $D$, its sequential path probability is
--   $$w(D\mid X)=\prod_i q_i^{D_i}(1-q_i)^{1-D_i},$$
--   where $q_i$ is the kernel bias before capacity is exhausted and on an active arrival, and is zero otherwise. Online activations use the published independent product law. This defines acceptance probabilities, prefix counts and instance balancedness $\Pr[A_i]\ge c p_i$. The history retains rejected arrivals and past decisions, so arbitrary state and private randomness are allowed.
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §2, pp.5–6

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_activationLaw

namespace SampleCRS.AlmostGreedy.Supplement

/-- A behavioral randomized online policy in a fixed, known arrival order, relabelled
as `0,…,n-1`. The history contains every past activation and every past decision.
Arbitrary real transition probabilities represent arbitrary private randomness; there
is no computational or finite-random-bit restriction. -/
structure OnlineKernel (n : ℕ) where
  bias : List (Bool × Bool) → Bool → ℝ
  valid : ∀ h x, bias h x ∈ Set.Icc (0 : ℝ) 1

def ValidProb {n : ℕ} (p : Fin n → ℝ) : Prop :=
  ∀ i, p i ∈ Set.Icc (0 : ℝ) 1

def history {n : ℕ} (X D : Fin n → Bool) (t : ℕ) : List (Bool × Bool) :=
  (List.ofFn (fun i => (X i, D i))).take t

def prefixCount {n : ℕ} (D : Fin n → Bool) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => i.val < t ∧ D i = true)).card

/-- The actual sequential kernel law. Inactive elements and arrivals after capacity
is exhausted are rejected with probability one. Decisions are irrevocable. -/
noncomputable def pathWeight {n : ℕ} (k : ℕ) (π : OnlineKernel n)
    (X D : Fin n → Bool) : ℝ :=
  ∏ i, let q := if X i = true ∧ prefixCount D i.val < k then
      π.bias (history X D i.val) (X i) else 0
    if D i = true then q else 1 - q

noncomputable def policyE {n : ℕ} (k : ℕ) (π : OnlineKernel n) (p : Fin n → ℝ)
    (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ X, activationWeight p X * ∑ D, pathWeight k π X D * f D

noncomputable def policyAccept {n : ℕ} (k : ℕ) (π : OnlineKernel n)
    (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  policyE k π p (fun D => if D i = true then 1 else 0)

def BalancedInstance {n : ℕ} (k : ℕ) (c : ℝ) (π : OnlineKernel n)
    (p : Fin n → ℝ) : Prop :=
  ∀ i, 0 < p i → c * p i ≤ policyAccept k π p i

end SampleCRS.AlmostGreedy.Supplement


