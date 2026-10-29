-- Prove2me | Definitions.Def_XuDRMDP_Finite_Returns
-- name    : XuDRMDP_Finite_Returns
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:28:40.938145+00:00
-- url     : https://prove2.me/theorems/15003b79-a88a-40fa-9221-58a03f7c85bf
-- title:
--   Independent trajectory probabilities and expected returns
-- statement:
--   For a history $h$ at stage $t$ (zero-based), let $k=T-1-t$ be its remaining nonterminal decisions. A suffix is $k$ state/action pairs together with a terminal state. Its trajectory probability is zero unless it starts at the current state and visits the prescribed successive stages. For a zero-length suffix, the final state must equal the current state; its probability is one there and zero elsewhere. Otherwise it is the product, over the suffix, of the policy's action probability at the history prefixed by the previous suffix pairs and the transition probability to the next suffix state (or to the final state at the last decision).
--
--   The suffix reward is $\sum_{i=0}^{k-1}\gamma^i r(s_i,a_i)$. The subproblem return $u(\pi,x,h)$ is the finite sum of trajectory probability times suffix reward over all suffixes and final states. Terminal reward is zero and is omitted from this sum. Thus $T=1$ and every terminal subproblem have return zero. This defines the actual subproblem even at a history of probability zero, with discount reset, as in the paper's footnote 1.
--
--   Define $w(\pi,\nu,h)=\int u(\pi,x,h)\,d\nu(x)$ and $W(\pi,\nu)=w(\pi,\nu,(s^{ini}))$. The nominal total return uses the same finite path sum at the initial history. The one-step averaged expression is $B_h(x_s)=\sum_a\pi_h(a)[r_{x_s}(a)+\gamma\sum_{j\in S_{t+1}}p_{x_s}(j\mid a)w(\pi,\nu,(h,a,j))]$. None of these quantities is defined through optimal values or mean parameters. The Bochner integrals are integrable for admissible laws by compact support and continuity of each finite path polynomial.
-- source:
--   Xu and Mannor (2012), Distributionally Robust Markov Decision Processes, Mathematics of Operations Research 37(2), 288–300, DOI:10.1287/moor.1120.0540. Published basis; printed page = PDF page + 287. Sections 2–3, printed pp. 289–293 (PDF pp. 2–6).

import Definitions.Def_XuDRMDP_Finite_Policies
import Definitions.Def_XuDRMDP_Finite_Ambiguity
open MeasureTheory
open scoped BigOperators

namespace XuDRMDP.Finite

/-- A suffix has k state/action pairs and one final state. -/
abbrev Suffix {n : ℕ} (a : Fin n → ℕ) (k : ℕ) := Fin k → Sigma fun s => Fin (a s)

def suffixHistory {n k : ℕ} {a : Fin n → ℕ} (h : History a)
    (z : Suffix a k) (t : Fin k) : History a :=
  ⟨h.past ++ (List.ofFn z).take t.val, (z t).1⟩

def successorState {n k : ℕ} {a : Fin n → ℕ} (z : Suffix a k)
    (j : Fin n) (t : Fin k) : Fin n :=
  if ht : t.val + 1 < k then (z ⟨t.val + 1, ht⟩).1 else j

/-- The explicit finite trajectory probability. No reward or parameter is observed by the policy. -/
noncomputable def trajectoryProbability {n k : ℕ} {a : Fin n → ℕ}
    (G : Setup n a) (π : Policy a) (x : Parameters n a) (h : History a)
    (z : Suffix a k) (j : Fin n) : ℝ :=
  if (∀ t : Fin k, G.stage (z t).1 = G.stage h.state + t.val) ∧
     (∀ t : Fin k, t.val = 0 → (z t).1 = h.state) ∧
     G.stage j = G.stage h.state + k ∧
     (k = 0 → j = h.state) then
    ∏ t : Fin k, (π (suffixHistory h z t)).val (z t).2 *
      (x (z t).1).1 (z t).2 (successorState z j t)
  else 0

/-- Discount reset at the current history. The terminal reward is identically zero. -/
noncomputable def trajectoryReward {n k : ℕ} {a : Fin n → ℕ}
    (G : Setup n a) (x : Parameters n a) (z : Suffix a k) : ℝ :=
  ∑ t : Fin k, G.discount ^ t.val * (x (z t).1).2 (z t).2

/-- Source u at any history: finite path sum, independent of every optimization. -/
noncomputable def returnFrom {n : ℕ} {a : Fin n → ℕ}
    (G : Setup n a) (π : Policy a) (x : Parameters n a) (h : History a) : ℝ :=
  ∑ z : Suffix a (G.horizon - 1 - G.stage h.state), ∑ j : Fin n,
    trajectoryProbability G π x h z j * trajectoryReward G x z

noncomputable def expectedFrom {n : ℕ} {a : Fin n → ℕ}
    (G : Setup n a) (π : Policy a) (ν : Measure (Parameters n a)) (h : History a) : ℝ :=
  ∫ x, returnFrom G π x h ∂ν

noncomputable def totalReturn {n : ℕ} {a : Fin n → ℕ}
    (G : Setup n a) (π : Policy a) (x : Parameters n a) : ℝ :=
  returnFrom G π x (initialHistory G)

noncomputable def performance {n : ℕ} {a : Fin n → ℕ}
    (G : Setup n a) (π : Policy a) (ν : Measure (Parameters n a)) : ℝ :=
  expectedFrom G π ν (initialHistory G)

/-- Lemma 3.1 integrand, with impossible next-stage continuations omitted. -/
noncomputable def averagedStep {n : ℕ} {a : Fin n → ℕ}
    (G : Setup n a) (π : Policy a) (ν : Measure (Parameters n a))
    (h : History a) (x : Local n a h.state) : ℝ :=
  ∑ b : Fin (a h.state), (π h).val b *
    (x.2 b + G.discount * ∑ j : Fin n,
      if G.stage j = G.stage h.state + 1 then
        x.1 b j * expectedFrom G π ν (h.extend b j) else 0)

end XuDRMDP.Finite


