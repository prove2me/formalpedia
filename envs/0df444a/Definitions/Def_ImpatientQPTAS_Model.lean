-- Prove2me | Definitions.Def_ImpatientQPTAS_Model
-- name    : ImpatientQPTAS_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:56.545513+00:00
-- url     : https://prove2.me/theorems/8906a3bd-fc2c-4451-838f-c5907123fd7f
-- title:
--   §1.1, pp.2–3 — customers, adaptive service policies and the expected reward $R(S)$
-- statement:
--   There are $n$ customers. Customer $i$ has a non-negative reward $r_i$ and a departure probability $p_i\in[0,1]$. An **adaptive service policy** maps a state $(t,A)$, a stage $t$ and the set $A$ of available customers, to a customer of $A$ to serve when $A\neq\emptyset$; an **extended policy** may instead serve no one, written $\bot$.
--
--   In stage $t$ the policy serves $S(t,A)$ and collects its reward. Each other available customer then departs independently, $i$ with probability $p_i$, and the survivors form the next state. The expected reward satisfies, for $S(t,A)=i$,
--   $$
--   R_S(t,A)=r_i+\mathbb E\big[R_S\big(t+1,\,A\setminus(\{i\}\cup D_t)\big)\big],\qquad R_S(t,\emptyset)=0,
--   $$
--   and $R(S)=R_S(1,[n])$. The **optimal value** of a set is $V(\emptyset)=0$ and $V(A)=\max_{i\in A}\big(r_i+\mathbb E[V(\text{survivors of }A\setminus\{i\})]\big)$.
--
--   This is the model of the whole mission.
--
--   **Formalization Note** Customers are `Fin n`, stages are natural numbers starting at $1$, and `none` is $\bot$. `thin p C f` is the finite expectation of $f$ at the survivors of $C$. The reward is a recursion on a stage budget, read at budget $2n$, the stages in which the paper's policies operate; for a policy that never idles this is the whole reward. `V` is a recursion read at depth $|A|$.
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, §1.1, pp.2–3, eq. (1); §2.1, p.8 (⊥); §1.2, p.3 (dynamic program (1))

import Mathlib

namespace ImpatientQPTAS

/-- **An instance of serving impatient customers.** Segev, arXiv:2209.13878v1, §1.1, p.2.

Customer `i` has a reward `r i` and a departure probability `p i`.

**Formalization Note.** Customers are `Fin n`, so the paper's customer `i ∈ [n]` is a 0-based
index. `n = 0` is allowed and trivial. -/
structure Instance (n : ℕ) where
  r : Fin n → ℝ
  p : Fin n → ℝ

/-- The standing assumptions of §1.1, p.2: rewards are non-negative and departure probabilities
lie in `[0, 1]`. The endpoints `p i = 0` and `p i = 1` are allowed: the paper excludes neither. -/
def Instance.Standing {n : ℕ} (I : Instance n) : Prop :=
  ∀ i, 0 ≤ I.r i ∧ 0 ≤ I.p i ∧ I.p i ≤ 1

/-- The expectation of `f` at the survivors of `C`: each customer of `C` departs independently, `i`
with probability `p i`, and `f` is evaluated at those who stay. The summation variable `D` is the
random set of departing customers of §1.1, p.2. -/
noncomputable def thin {n : ℕ} (p : Fin n → ℝ) (C : Finset (Fin n)) (f : Finset (Fin n) → ℝ) : ℝ :=
  ∑ D ∈ C.powerset, (∏ i ∈ D, p i) * (∏ i ∈ C \ D, (1 - p i)) * f (C \ D)

/-- A (possibly idling) adaptive service policy: a function of the state `(t, A)`. Segev,
arXiv:2209.13878v1, §1.1, p.2, and the extended policies of §2.1, p.8.

**Formalization Note.** `none` is the paper's `⊥`, "the policy does not serve any customer". Stages
are natural numbers starting at `1`; the value at stage `0` is never read. -/
abbrev Policy (n : ℕ) := ℕ → Finset (Fin n) → Option (Fin n)

/-- An extended policy, §2.1, p.8: whenever it serves a customer, that customer is available. -/
def IsExtPolicy {n : ℕ} (S : Policy n) : Prop :=
  ∀ t A i, S t A = some i → i ∈ A

/-- An adaptive service policy, §1.1, p.2: on every state with `A ≠ ∅` it serves one customer picked
out of `A`. It is not constrained at `A = ∅`. -/
def IsPolicy {n : ℕ} (S : Policy n) : Prop :=
  IsExtPolicy S ∧ ∀ t A, A.Nonempty → (S t A).isSome

/-- The expected reward `R_S(t, A)` of eq. (1), Segev, arXiv:2209.13878v1, §1.1, p.2, over the next
`T` stages at most.

**Formalization Note.** The recursion runs on the stage budget `T`. At `A = ∅` the value is `0`,
as on p.3. When the policy serves `i`, the departures are drawn from `A \ {i}`; when it idles, from
all of `A`. For a policy that never idles the budget stops mattering once `T ≥ |A|`, since each
stage serves a customer. -/
noncomputable def Rh {n : ℕ} (I : Instance n) (S : Policy n) : ℕ → ℕ → Finset (Fin n) → ℝ
  | 0, _, _ => 0
  | T + 1, t, A =>
    if A = ∅ then 0
    else
      match S t A with
      | some i => I.r i + thin I.p (A.erase i) (Rh I S T (t + 1))
      | none => thin I.p A (Rh I S T (t + 1))

/-- The expected reward of `S` from the start set `B` at stage `1`.

**Formalization Note.** The budget is `2n`: the stages `1, …, 2n` in which the paper's policies
operate (Appendix A.2, p.31). For a policy that never idles this is the whole of `R_S(1, B)`. -/
noncomputable def Instance.Rfrom {n : ℕ} (I : Instance n) (S : Policy n)
    (B : Finset (Fin n)) : ℝ :=
  Rh I S (2 * n) 1 B

/-- `R(S) = R_S(1, A₁)` with `A₁ = [n]`, Segev, arXiv:2209.13878v1, §1.1, p.3. -/
noncomputable def Instance.R {n : ℕ} (I : Instance n) (S : Policy n) : ℝ :=
  I.Rfrom S Finset.univ

/-- The maximum of `f` on `s`, and `0` on the empty set. -/
noncomputable def maxOn {ι : Type} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  if h : s.Nonempty then s.sup' h f else 0

/-- `r_max = max_i r_i`, §2.2, p.9, and `0` when there are no customers. -/
noncomputable def rmax {n : ℕ} (r : Fin n → ℝ) : ℝ :=
  maxOn Finset.univ r

/-- The optimality recursion with a depth budget; see `V`. -/
noncomputable def Vb {n : ℕ} (r p : Fin n → ℝ) : ℕ → Finset (Fin n) → ℝ
  | 0, _ => 0
  | k + 1, A => maxOn A fun i => r i + thin p (A.erase i) (Vb r p k)

/-- The optimal value of the set `A` of available customers with rewards `r` and departure
probabilities `p`: `V(∅) = 0` and `V(A) = max_{i ∈ A} (r_i + E[V(survivors of A \ {i})])`. This is the
"dynamic program (1)", §1.2, p.3.

**Formalization Note.** The depth budget `|A|` is exact, since every survivor set of `A \ {i}` has
fewer customers than `A`; the verification file proves the recursion at `V` itself, that `V`
dominates every policy and that a greedy policy attains it. -/
noncomputable def V {n : ℕ} (r p : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  Vb r p A.card A

end ImpatientQPTAS


