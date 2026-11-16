-- Prove2me | Definitions.Def_PooledTestingAdaptivity_Gap_Supplement_Greedy
-- name    : PooledTestingAdaptivity_Gap_Supplement_Greedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:36:18.235295+00:00
-- url     : https://prove2.me/theorems/2ba02955-2e71-4a77-8c42-e3fe1412f0ac
-- title:
--   Standard family $\mathcal F_{B,G}$, histories, exact posteriors, conditional gains and DynamicGreedy policies
-- statement:
--   Fix a pooled-testing instance $J$ (population $[n]$, independent health bits $X_i\sim\mathrm{Bernoulli}(q_i)$ with one meaning healthy, utilities $u_i\ge0$, pool cap $G$) and a budget $B$.
--
--   1. The **standard family** $\mathcal F_{B,G}$ consists of the ordered allocations with at most $B$ pools, each a nonempty set of at most $G$ individuals; pools may overlap or repeat. It contains the empty allocation.
--   2. A **history** $H=((t_1,r_1),\dots,(t_b,r_b))$ lists tested pools with their outcomes (negative or positive). A profile $x$ is consistent with $H$ when every recorded outcome is the outcome of $t_j$ under $x$; the cleared set is $C(H)=\bigcup_{j:\,r_j=-}t_j$, and the probability of $H$ is $P(H)=\sum_{x\text{ consistent}}\mu_J(x)$.
--   3. For a set $A$, the exact joint posterior is
--   $$P(X_A=1\mid H)=\frac{\sum_{x\text{ consistent with }H,\ x_A=1}\mu_J(x)}{P(H)},$$
--   used only when $P(H)>0$.
--   4. The **conditional gain** of a set $t$ is
--   $$g(t\mid H)=P(X_U=1\mid H)\sum_{i\in U}u_i,\qquad U=t\setminus C(H),$$
--   so $g(\emptyset\mid H)=0$, and $\max_{|s|\le G}g(s\mid H)$ ranges over all sets of at most $G$ individuals.
--   5. A policy tree $\pi$ is a **DynamicGreedy policy** for $(J,B)$ when it is feasible for $\mathcal F_{B,G}$ and, at every node whose history $H$ (pools on the path with their branch outcomes) has $P(H)>0$: if fewer than $B$ tests have been made and the maximum gain is positive, the node tests a pool of maximum gain; otherwise the node is a leaf. Ties among maximizers may be broken arbitrarily, and nodes reached with probability zero are only required to be feasible.
--
--   These objects are the conditional-greedy setting of §§3.2 and 6.2 of the paper.
--
--   **Formalization Note.** The model `Instance`, `Policy`, `Feasible`, `optStatic`, `optDynamic` is reused from the published base mission. Outcome `true` records a negative test, and the subtree `k true` is the negative child, as in the published `run`. The posterior is a ratio of finite sums of the product-prior mass; Lean's `x/0=0` is never used because every statement assumes or implies $P(H)>0$.
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), §2 and §2.1, printed pp. 4–5, PDF pp. 5–6; §3.2, printed p. 10, PDF p. 11; §6.2 Eq. (18), printed p. 20, PDF p. 21

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_Policies

namespace PooledTestingAdaptivity.Gap.Supplement

open Classical

/-- §2.1: the standard family `F_{B,G}`: at most `B` tests, each a nonempty pool of at most
`G = J.cap` individuals; pools may overlap or repeat. -/
def standardFamily {n : ℕ} (J : Instance n) (B : ℕ) : FeasibleFamily J B where
  allocations := {T | T.length ≤ B ∧ ∀ t ∈ T, t.Nonempty ∧ t.card ≤ J.cap}
  nonempty := ⟨[], by simp⟩
  admissible := fun _ hT => hT

/-- §2: a history is the ordered list of tested pools with their outcomes;
`true` records a negative outcome (all members healthy), `false` a positive one. -/
abbrev History (n : ℕ) := List (Pool n × Bool)

/-- The profile `x` produces every recorded outcome of `H`. -/
def Consistent {n : ℕ} (H : History n) (x : Profile n) : Prop :=
  ∀ p ∈ H, negative p.1.val x = p.2

/-- `C(H)`: the union of the pools recorded negative. -/
def histCleared {n : ℕ} : History n → Finset (Fin n)
  | [] => ∅
  | p :: H => (if p.2 then p.1.val else ∅) ∪ histCleared H

/-- `P(H)`: product-prior mass of the profiles consistent with `H`. -/
noncomputable def histMass {n : ℕ} (J : Instance n) (H : History n) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => Consistent H x), profileMass J x

/-- `P(X_A = 1 | H)`: exact joint posterior that every member of `A` is healthy.
Only used at histories with `0 < histMass J H`. -/
noncomputable def condHealthy {n : ℕ} (J : Instance n) (H : History n) (A : Finset (Fin n)) : ℝ :=
  (∑ x ∈ Finset.univ.filter (fun x => Consistent H x ∧ ∀ i ∈ A, x i = true), profileMass J x)
    / histMass J H

/-- Eq. (18): `g(t | H) = P(X_U = 1 | H) · Σ_{i ∈ U} u_i` with `U = t \ C(H)`;
`g(∅ | H) = 0` holds automatically. -/
noncomputable def gain {n : ℕ} (J : Instance n) (H : History n) (t : Finset (Fin n)) : ℝ :=
  condHealthy J H (t \ histCleared H) * ∑ i ∈ t \ histCleared H, J.u i

/-- All sets of at most `G` individuals (the empty set included). -/
def capSets {n : ℕ} (J : Instance n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun s => s.card ≤ J.cap

theorem capSets_nonempty {n : ℕ} (J : Instance n) : (capSets J).Nonempty :=
  ⟨∅, by simp [capSets]⟩

/-- `max_{|s| ≤ G} g(s | H)` over all sets of at most `G` individuals. -/
noncomputable def maxGain {n : ℕ} (J : Instance n) (H : History n) : ℝ :=
  (capSets J).sup' (capSets_nonempty J) (gain J H)

/-- The greedy rule at every node of a policy tree, `H` being the history reached at the node
(pools on the path with their branch outcomes; `k true` is the negative child).
At a node whose history has positive probability: if fewer than `B` tests were made and the
maximum gain is positive, the node tests a pool of maximum gain; otherwise it is a leaf.
Nodes with zero-probability histories are unconstrained here. -/
def greedyAt {n : ℕ} (J : Instance n) (B : ℕ) : Policy n → History n → Prop
  | .leaf _, H => 0 < histMass J H → H.length < B → maxGain J H = 0
  | .query t k, H =>
      (0 < histMass J H → H.length < B ∧ 0 < maxGain J H ∧ gain J H t.val = maxGain J H) ∧
        greedyAt J B (k true) (H ++ [(t, true)]) ∧ greedyAt J B (k false) (H ++ [(t, false)])

/-- §3.2, §6.2: `π` is a DynamicGreedy policy for `(J, B)` (any tie-breaking among maximizers):
it is feasible for `F_{B,G}` and follows the greedy rule from the empty history. -/
def DynamicGreedy {n : ℕ} (J : Instance n) (B : ℕ) (π : Policy n) : Prop :=
  Feasible (standardFamily J B) π ∧ greedyAt J B π []

end PooledTestingAdaptivity.Gap.Supplement


