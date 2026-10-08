-- Prove2me | Definitions.Def_ModPolicyIter_Conv_Model
-- name    : ModPolicyIter_Conv_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:12:35.052054+00:00
-- url     : https://prove2.me/theorems/98422cc5-91be-4170-bea4-b9aaff890be2
-- title:
--   §2, pp. 1127–1128 — the discounted Markov decision problem: transition operators, rewards, V, B of (1), ‖P − Q‖
-- statement:
--   The discounted Markov decision problem of Puterman and Shin, §2.
--
--   Let $S$ be a set of states carrying a $\sigma$-algebra. A **model** consists of a family $\mathcal P$ of policies, indexed by a type $\iota$; policy $i$ has a **transition operator** $P_i$, a Markov kernel on $S$ (a probability distribution $P_i(s,\cdot)$ on $S$ for each state $s$, measurable in $s$), and a measurable **one-period reward** $c_i:S\to\mathbb R$. Rewards are uniformly bounded and the discount rate $\lambda$ is in $[0,1)$:
--
--   $$\sup_{i}\sup_{s\in S}|c_i(s)|\le M<+\infty,\qquad 0\le\lambda<1.$$
--
--   The file also defines:
--
--   1. $V$, the bounded measurable functions $v:S\to\mathbb R$, with the norm $\|v\|=\sup_{s}|v(s)|$;
--   2. the action of $P_i$ on a function, $(P_iv)(s)=\int_S v(t)\,P_i(s,dt)$;
--   3. the operator of the optimality equation (1),
--   $$Bv=\max_{i}\{c_i+(\lambda P_i-I)v\},$$
--   the maximum taken pointwise as a supremum over policies;
--   4. the statement that policy $i$ attains this maximum at $v$ simultaneously at every state, $c_i+\lambda P_iv\ge c_j+\lambda P_jv$ for all $j$ (such an $i$ is a $P_v$), and the paper's standing assumption that a maximizer exists for every $v\in V$;
--   5. the operator norm $\|P_i-P_j\|=\sup\{\|(P_i-P_j)x\|:x\in V,\ \|x\|\le 1\}$ on $V$.
--
--   These are the objects of every statement of the paper.
--
--   **Formalization Note** The paper writes $\mathcal P=\prod_{s}\mathcal P_s$; here $\mathcal P$ is an arbitrary index type, a mild generalization (the product structure only serves to make the maximum in (1) attainable, which is assumed). Kernels make $P$ map $V$ into $V$, and measurability of $c_i$ is the paper's implicit requirement that $c_P\in V$. The norm $\sup_s|v(s)|$ and the suprema in $B$ are real suprema, used only where they are bounded above. The operator norm is a supremum over the unit ball of $V$, which equals $\sup_{x\in V}\|Ax\|/\|x\|$ for the linear operator $A=P_i-P_j$.
-- source:
--   Puterman and Shin, Modified policy iteration algorithms for discounted Markov decision problems, Management Science 24 (1978), DOI 10.1287/mnsc.24.11.1127, pp. 1127–1128, §2, (1) and the definitions of V and ‖A‖

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ModPolicyIter.Conv

/-- The discounted Markov decision problem of Puterman–Shin (1978), §2, pp. 1127–1128.
`S` is the state set (with a σ-algebra, since `V` consists of bounded *measurable* functions).
The family `𝒫` of transition operators is indexed by `ι`: policy `i` has the Markov kernel `P i`
(a probability distribution on `S` for each state, measurable in the state) and the one-period
reward `c i`, measurable and bounded by `M` uniformly in `i` and `s`. The discount rate `lam`
satisfies `0 ≤ lam < 1`. -/
structure Model (S : Type*) [MeasurableSpace S] (ι : Type*) where
  /-- Transition operator of policy `i`. -/
  P : ι → Kernel S S
  /-- Each `P i s` is a probability distribution on `S`. -/
  isMarkov : ∀ i, IsMarkovKernel (P i)
  /-- One-period reward `c_P` of policy `i`. -/
  c : ι → S → ℝ
  c_meas : ∀ i, Measurable (c i)
  /-- The uniform reward bound `sup_P sup_s |c_P(s)| ≤ M < +∞`. -/
  M : ℝ
  c_bdd : ∀ i s, |c i s| ≤ M
  /-- The discount rate `λ`. -/
  lam : ℝ
  lam_nonneg : 0 ≤ lam
  lam_lt_one : lam < 1

variable {S : Type*} [MeasurableSpace S] {ι : Type*}

/-- `v ∈ V`: `v` is a bounded measurable real function on `S`. -/
def IsBM (v : S → ℝ) : Prop := Measurable v ∧ ∃ C : ℝ, ∀ s, |v s| ≤ C

/-- The sup norm `‖v‖ = sup_s |v(s)|` (used only on bounded functions). -/
noncomputable def supNorm (v : S → ℝ) : ℝ := ⨆ s, |v s|

/-- The transition operator of policy `i` acting on a function: `(P v)(s) = ∫ v(t) P(s, dt)`
(used only on bounded measurable functions). -/
noncomputable def Pop (m : Model S ι) (i : ι) (v : S → ℝ) : S → ℝ :=
  fun s => ∫ t, v t ∂(m.P i s)

/-- Policy `i` attains the maximum in (1) at `v`, simultaneously at every state:
`c_{P_i} + λ P_i v ≥ c_{P_j} + λ P_j v` for every `j`. Such an `i` is a `P_v`. -/
def Attains (m : Model S ι) (v : S → ℝ) (i : ι) : Prop :=
  ∀ j s, m.c j s + m.lam * Pop m j v s ≤ m.c i s + m.lam * Pop m i v s

/-- The standing assumption of the paper (p. 1128): the maximum in (1) is attained for every
`v ∈ V`. -/
def MaxAttained (m : Model S ι) : Prop := ∀ v : S → ℝ, IsBM v → ∃ i, Attains m v i

/-- The operator `B` of (1): `Bv = Max_P {c_P + (λP − I)v}`, the maximum taken pointwise as a
supremum over policies. -/
noncomputable def B (m : Model S ι) (v : S → ℝ) : S → ℝ :=
  fun s => (⨆ i, (m.c i s + m.lam * Pop m i v s)) - v s

/-- The operator norm `‖P_i − P_j‖ = sup_{x ∈ V, ‖x‖ ≤ 1} ‖(P_i − P_j)x‖` on `V`. -/
noncomputable def opNormDiff (m : Model S ι) (i j : ι) : ℝ :=
  ⨆ x : {x : S → ℝ // IsBM x ∧ supNorm x ≤ 1}, supNorm (Pop m i x.1 - Pop m j x.1)

end ModPolicyIter.Conv


