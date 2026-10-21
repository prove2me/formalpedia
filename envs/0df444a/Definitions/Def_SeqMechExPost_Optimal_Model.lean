-- Prove2me | Definitions.Def_SeqMechExPost_Optimal_Model
-- name    : SeqMechExPost_Optimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:16:37.467976+00:00
-- url     : https://prove2.me/theorems/a0199d56-a451-4da0-9b3c-2c6df6c536ca
-- title:
--   §2–§3, (1)–(3), (6)–(13), pp. 5–8 — k-day sequential mechanisms: PIC (1), ex-post IR (2), revenue (3); the adjusted problem (11)–(13) and the changes of variables (7), (9)
-- statement:
--   The model of Ashlagi, Daskalakis and Haghpanah: a seller sells $k$ items to one buyer, one item per day, and the buyer learns his value for the day's item only at the start of that day.
--
--   1. **Instance.** For each day $i \in [1:k]$ there is a type interval $[\underline v_i, \bar v_i]$ with $0 \le \underline v_i \le \bar v_i$ and a probability law $\mu_i$ on $\mathbb R$ carried by it. The values $v = (v_1,\dots,v_k)$ are independent across days, so their joint law is $\mu_1 \otimes \dots \otimes \mu_k$. A *type profile* is a vector with $v_j \in [\underline v_j, \bar v_j]$ for every $j$. We write $v_{\le i} = (v_1,\dots,v_i)$ and $v_{<i}$ for the history before day $i$.
--
--   2. **Mechanisms.** A sequential direct mechanism consists of allocation probabilities $x_i(v_{\le i})$ and payments $p_i(v_{\le i})$, $i \in [1:k]$. It is *admissible* if day $i$'s rules depend only on $v_{\le i}$, all rules are measurable, $x_i \in [0,1]$ on type profiles, every $p_i$ is integrable, and every conditional expectation of a future payment given a history (as used below) exists.
--
--   3. **Future utility (6)** and **periodic incentive compatibility (1).** Let
--   $$U_i(v_{\le i}) = \mathbf E_{v_{i+1},\dots,v_k}\Big[\sum_{j>i} x_j(v_{\le j})\,v_j - p_j(v_{\le j})\Big].$$
--   The mechanism is PIC if for every day $i$, every type profile $v$ and every misreport $v_i' \in [\underline v_i, \bar v_i]$,
--   $$v_i x_i(v_{\le i}) - p_i(v_{\le i}) + U_i(v_{\le i}) \;\ge\; v_i x_i(v_{<i}, v_i') - p_i(v_{<i}, v_i') + U_i(v_{<i}, v_i'),$$
--   where in $U_i(v_{<i}, v_i')$ the later days are reported truthfully, the true later values enter as values and the misreport $v_i'$ enters every later rule.
--
--   4. **Ex-post individual rationality (2)**: $v_i x_i(v_{\le i}) - p_i(v_{\le i}) \ge 0$ for every day and every type profile. **Revenue (3)**: $\mathbf E[\sum_i p_i(v_{\le i})]$. A mechanism is *feasible* for the original problem if it is admissible, PIC and ex-post IR, and *optimal* if it is feasible and its revenue is at least that of every feasible mechanism.
--
--   5. **The adjusted problem.** An adjusted mechanism $(x, \hat p)$ has allocations $x_i$ and adjusted payments $\hat p_i$, with the same admissibility conditions. Write $\hat U_i(v_{\le i}) = \mathbf E_{v_{i+1}}[x_{i+1}(v_{\le i+1})v_{i+1} - \hat p_{i+1}(v_{\le i+1})]$, with $\hat U_k = 0$ (the paper's $x_{k+1} = \hat p_{k+1} = 0$). The adjusted problem is
--   $$\max_{x,\hat p}\ \mathbf E\Big[\hat p_1(v_1) + \sum_{i=2}^k x_i(v_{\le i})\,v_i\Big] \quad (11)$$
--   subject to (12) $v_i x_i(v_{\le i}) - \hat p_i(v_{\le i}) \ge v_i x_i(v_{<i}, v_i') - \hat p_i(v_{<i}, v_i')$ and (13) $v_i x_i(v_{\le i}) - \hat p_i(v_{\le i}) \ge \hat U_i(v_{\le i})$, for all $i$, type profiles and misreports.
--
--   6. **Changes of variables.** (7) $\hat p_i = p_i - U_i$ maps a mechanism to an adjusted one; (9) $p_i = \hat p_i + \hat U_i$ maps back.
--
--   These are the objects in which Lemma 3, Lemma 4 and Theorem 7 are stated.
--
--   **Formalization Note** Days are `Fin k`, 0-based: Lean day $i$ is the paper's day $i+1$. A history is a full vector `v : Fin k → ℝ`; non-anticipation is a separate condition, and the conditional expectation over the future is the integral of `splice i v w` (keep $v_j$ for $j \le i$, take $w_j$ for $j > i$) against the product law. The constraints (1), (2), (12), (13) are imposed pointwise on all type profiles, as on the page ("for all $v_{\le i}$ and $v_i'$"). The paper works with densities but states that its results also apply to discrete support; the formalization takes general probability laws on the type intervals. Measurability and integrability (admissibility) are added so that every expectation the page writes is defined. Two printed slips in (1) are read as corrected: $p_j(v_{\le i})$ on the left is $p_j(v_{\le j})$, and $x_i(v_{\le i}, v_i')$ on the right is $x_i(v_{<i}, v_i')$, as in (12). The adjusted objective (11) is written as the sum over Lean days of $\hat p_0$ on day $0$ and $v_i x_i$ on the others.
-- source:
--   Ashlagi, Daskalakis, Haghpanah, Sequential Mechanisms with ex-post Participation Guarantees, arXiv:1603.07229v2, pp. 5–8 (PDF 6–9), §2 (1)–(3), §3 (6)–(13)

import Mathlib

namespace SeqMechExPost.Optimal

open MeasureTheory

/-- The standing data of §2 (Ashlagi–Daskalakis–Haghpanah, p. 5): `k` days (Lean day `i : Fin k` is
the paper's day `i + 1`); on each day a probability law `μ i` of the buyer's value, carried by the type
interval `[lo i, hi i]` (the paper's `[v̲_i, v̄_i]`), with `0 ≤ lo i`. Values on different days are
independent (the joint law is `Measure.pi μ`, see `Instance.law`). -/
structure Instance (k : ℕ) where
  /-- the law of the day-`i` value -/
  μ : Fin k → Measure ℝ
  isProb : ∀ i, IsProbabilityMeasure (μ i)
  /-- lower end `v̲_i` of the type interval -/
  lo : Fin k → ℝ
  /-- upper end `v̄_i` of the type interval -/
  hi : Fin k → ℝ
  lo_nonneg : ∀ i, 0 ≤ lo i
  lo_le_hi : ∀ i, lo i ≤ hi i
  support : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0

attribute [instance] Instance.isProb

variable {k : ℕ}

/-- The joint law of `v = (v_1, …, v_k)`: the product of the daily laws (independence across days). -/
noncomputable def Instance.law (I : Instance k) : Measure (Fin k → ℝ) := Measure.pi I.μ

/-- `v` is a type profile: every coordinate lies in its type interval `[lo j, hi j]`. -/
def Instance.InBox (I : Instance k) (v : Fin k → ℝ) : Prop :=
  ∀ j, v j ∈ Set.Icc (I.lo j) (I.hi j)

/-- Keep the history `v_{≤ i}` of `v` and take the future days `j > i` from `w`. -/
def splice (i : Fin k) (v w : Fin k → ℝ) : Fin k → ℝ :=
  fun j => if j ≤ i then v j else w j

/-- A sequential direct mechanism (§2, p. 5): allocation probabilities `x i v` and payments `p i v`
for every day `i`, as functions of the whole report vector (non-anticipation is a separate
condition). -/
structure SeqMech (k : ℕ) where
  /-- allocation probability `x_i(v_{≤ i})` -/
  x : Fin k → (Fin k → ℝ) → ℝ
  /-- payment `p_i(v_{≤ i})` -/
  p : Fin k → (Fin k → ℝ) → ℝ

/-- Day `i`'s rules read only the reports of days `j ≤ i`. -/
def SeqMech.NonAnticipative (M : SeqMech k) : Prop :=
  ∀ i v w, (∀ j, j ≤ i → v j = w j) → M.x i v = M.x i w ∧ M.p i v = M.p i w

/-- Admissible mechanisms: non-anticipative, measurable, `x_i ∈ [0, 1]` on type profiles, payments
integrable, and every conditional expectation of a future payment given a history (as in (1), (6))
exists. -/
def SeqMech.Admissible (I : Instance k) (M : SeqMech k) : Prop :=
  M.NonAnticipative ∧
  (∀ i, Measurable (M.x i) ∧ Measurable (M.p i)) ∧
  (∀ i v, I.InBox v → M.x i v ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ i, Integrable (M.p i) I.law) ∧
  (∀ i j v, I.InBox v → Integrable (fun w => M.p j (splice i v w)) I.law)

/-- (6): expected utility from the transactions of the days after `i`, given the reports `v_{≤ i}`
and truthful reports `w_j` on the later days. -/
noncomputable def SeqMech.U (I : Instance k) (M : SeqMech k) (i : Fin k) (v : Fin k → ℝ) : ℝ :=
  ∫ w, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      ((splice i v w) j * M.x j (splice i v w) - M.p j (splice i v w)) ∂I.law

/-- (1), periodic incentive compatibility: on every day `i`, for every true history `v_{≤ i}` and
every misreport `a` of `v_i`, reporting truthfully today (and on all later days) is at least as good
as reporting `a` today and truthfully afterwards. -/
def SeqMech.PIC (I : Instance k) (M : SeqMech k) : Prop :=
  ∀ i v, I.InBox v → ∀ a ∈ Set.Icc (I.lo i) (I.hi i),
    v i * M.x i (Function.update v i a) - M.p i (Function.update v i a)
        + M.U I i (Function.update v i a)
      ≤ v i * M.x i v - M.p i v + M.U I i v

/-- (2), ex-post individual rationality: the stage utility is non-negative on every day and every
history. -/
def SeqMech.ExPostIR (I : Instance k) (M : SeqMech k) : Prop :=
  ∀ i v, I.InBox v → 0 ≤ v i * M.x i v - M.p i v

/-- (3), the expected revenue `E[∑_i p_i(v_{≤ i})]`. -/
noncomputable def SeqMech.revenue (I : Instance k) (M : SeqMech k) : ℝ :=
  ∫ v, ∑ i, M.p i v ∂I.law

/-- Feasible for the original problem: admissible, PIC (1) and ex-post IR (2). -/
def SeqMech.Feasible (I : Instance k) (M : SeqMech k) : Prop :=
  M.Admissible I ∧ M.PIC I ∧ M.ExPostIR I

/-- Optimal for the original problem: feasible, with revenue (3) at least that of every feasible
mechanism. -/
def SeqMech.IsOptimal (I : Instance k) (M : SeqMech k) : Prop :=
  M.Feasible I ∧ ∀ M' : SeqMech k, M'.Feasible I → M'.revenue I ≤ M.revenue I

/-- A mechanism of the adjusted problem (§3, p. 8): allocations `x i` and adjusted payments
`pHat i` (the paper's `p̂_i`). -/
structure AdjMech (k : ℕ) where
  /-- allocation probability `x_i(v_{≤ i})` -/
  x : Fin k → (Fin k → ℝ) → ℝ
  /-- adjusted payment `p̂_i(v_{≤ i})` -/
  pHat : Fin k → (Fin k → ℝ) → ℝ

/-- Non-anticipation for adjusted mechanisms. -/
def AdjMech.NonAnticipative (A : AdjMech k) : Prop :=
  ∀ i v w, (∀ j, j ≤ i → v j = w j) → A.x i v = A.x i w ∧ A.pHat i v = A.pHat i w

/-- Admissible adjusted mechanisms (same regularity as `SeqMech.Admissible`). -/
def AdjMech.Admissible (I : Instance k) (A : AdjMech k) : Prop :=
  A.NonAnticipative ∧
  (∀ i, Measurable (A.x i) ∧ Measurable (A.pHat i)) ∧
  (∀ i v, I.InBox v → A.x i v ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ i, Integrable (A.pHat i) I.law) ∧
  (∀ i j v, I.InBox v → Integrable (fun w => A.pHat j (splice i v w)) I.law)

/-- The right-hand side of (8)/(13): `E_{v_{i+1}}[x_{i+1}(v_{≤ i+1}) v_{i+1} − p̂_{i+1}(v_{≤ i+1})]`
given the history `v_{≤ i}`; it is `0` on the last day (the paper's `x_{k+1} = p̂_{k+1} = 0`). -/
noncomputable def AdjMech.nextU (I : Instance k) (A : AdjMech k) (i : Fin k)
    (v : Fin k → ℝ) : ℝ :=
  if h : i.val + 1 < k then
    ∫ w, ((splice i v w) ⟨i.val + 1, h⟩ * A.x ⟨i.val + 1, h⟩ (splice i v w)
        - A.pHat ⟨i.val + 1, h⟩ (splice i v w)) ∂I.law
  else 0

/-- (12): for each history `v_{< i}`, the day-`i` mechanism is incentive compatible in isolation. -/
def AdjMech.IC (I : Instance k) (A : AdjMech k) : Prop :=
  ∀ i v, I.InBox v → ∀ a ∈ Set.Icc (I.lo i) (I.hi i),
    v i * A.x i (Function.update v i a) - A.pHat i (Function.update v i a)
      ≤ v i * A.x i v - A.pHat i v

/-- (13): the utility bounds `v_i x_i − p̂_i ≥ E_{v_{i+1}}[x_{i+1} v_{i+1} − p̂_{i+1}]`; on the last
day this reads `v_k x_k − p̂_k ≥ 0`. -/
def AdjMech.UtilityBound (I : Instance k) (A : AdjMech k) : Prop :=
  ∀ i v, I.InBox v → A.nextU I i v ≤ v i * A.x i v - A.pHat i v

/-- (11), the adjusted objective `E[p̂_1(v_1) + ∑_{i=2}^k x_i(v_{≤ i}) v_i]` (Lean day `0` is the
paper's day 1). -/
noncomputable def AdjMech.adjObj (I : Instance k) (A : AdjMech k) : ℝ :=
  ∫ v, ∑ i, (if i.val = 0 then A.pHat i v else v i * A.x i v) ∂I.law

/-- Feasible for the adjusted problem: admissible, (12) and (13). -/
def AdjMech.AdjFeasible (I : Instance k) (A : AdjMech k) : Prop :=
  A.Admissible I ∧ A.IC I ∧ A.UtilityBound I

/-- Optimal for the adjusted problem (11)–(13). -/
def AdjMech.AdjOptimal (I : Instance k) (A : AdjMech k) : Prop :=
  A.AdjFeasible I ∧ ∀ A' : AdjMech k, A'.AdjFeasible I → A'.adjObj I ≤ A.adjObj I

/-- (7): the adjusted payment `p̂_i := p_i − U_i`. -/
noncomputable def adjust (I : Instance k) (M : SeqMech k) : AdjMech k where
  x := M.x
  pHat i v := M.p i v - M.U I i v

/-- (9): `p_i = p̂_i + E_{v_{i+1}}[x_{i+1} v_{i+1} − p̂_{i+1}]`. -/
noncomputable def unadjust (I : Instance k) (A : AdjMech k) : SeqMech k where
  x := A.x
  p i v := A.pHat i v + A.nextU I i v

end SeqMechExPost.Optimal


