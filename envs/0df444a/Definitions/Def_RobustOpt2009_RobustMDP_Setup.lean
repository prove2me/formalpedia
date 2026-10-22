-- Prove2me | Definitions.Def_RobustOpt2009_RobustMDP_Setup
-- name    : RobustOpt2009_RobustMDP_Setup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:40.903486+00:00
-- url     : https://prove2.me/theorems/cc5a2ecd-3362-4000-8fed-fac84b1681be
-- title:
--   Finite-horizon costs, time-dependent rectangular uncertainty, and Bellman recursions
-- statement:
--   Let $X$ and $A$ be finite state and action sets, and let $T=\{0,\ldots,N-1\}$. A deterministic Markov policy assigns an action $u_t(i)$ to every time and state. A raw transition collection is a real array; the nominal theorems require each row $p_{ti}^a$ to be a probability vector, and robust nature policies enforce this through row-set membership. The data specify arbitrary real stage costs $c_t(i,a)$ and terminal costs $c_N(i)$.
--
--   Starting from distribution $q$ at time $s$, the forward distributions obey $q_s=q$ and $q_{t+1}(j)=\sum_i q_t(i)p_{ti}^{u_t(i)}(j)$. Define the expected remaining cost independently of any optimization by
--   $$C_{s,q}(u,p)=\sum_{t=s}^{N-1}\sum_i q_t(i)c_t(i,u_t(i))+\sum_iq_N(i)c_N(i).$$
--   The nominal backward values are $v_N=c_N$ and $v_t(i)=\min_a[c_t(i,a)+\sum_j p_{ti}^a(j)v_{t+1}(j)]$.
--
--   A robust model also specifies nonempty closed sets $P_{ti}^a\subseteq\Delta(X)$. Nature's policies form their entire direct product. Write $H_t(i,a,w)=c_t(i,a)+\sup_{p\in P_{ti}^a}\sum_jp(j)w(j)$. The robust recursion is $v_N=c_N$, $v_t(i)=\min_a H_t(i,a,v_{t+1})$; fixed-policy evaluation is $v_N^u=c_N$, $v_t^u(i)=H_t(i,u_t(i),v_{t+1}^u)$. The independent worst cost is $\sup_p C_{s,q}(u,p)$. Greedy controller policies minimize $H_t(i,a,v_{t+1})$ at every state and time; maximizing nature rows attain the corresponding linear maxima. These definitions provide the finite-dimensional objects used by the chapter's statements; they do not assert that recursions equal game values.
--
--   **Formalization Note** States and actions use `Fin n` and `Fin m`, decision times `Fin N`. The raw definitions permit empty types, but all theorem items require nonempty states and actions and normalized initial distributions. Distribution propagation holds $q$ fixed before $s$ and freezes after $N$; only $s\le t\le N$ is used. Values at $t\ge N$ are terminal costs. Real suprema or infima on empty or unbounded domains take Lean's default values; theorem hypotheses exclude those cases. To keep drafts independently compilable without importing unpublished items, theorem modules include the needed concrete definitions in disjoint local namespaces.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Sections 13.1–13.3, printed pp. 343–351 (PDF pp. 369–377).

import Mathlib

namespace RobustOpt2009.RobustMDP
namespace Setup

abbrev Control (n m N : ℕ) := Fin N → Fin n → Fin m
abbrev Transition (n m N : ℕ) := Fin N → Fin n → Fin m → Fin n → ℝ

structure Data (n m N : ℕ) where
  cost : Fin N → Fin n → Fin m → ℝ
  terminal : Fin n → ℝ

/-- Forward state distribution from distribution q at stage s. Stages before s
hold q fixed; after N the distribution is held fixed. Only s ≤ t ≤ N is used. -/
noncomputable def dist {n m N : ℕ} (u : Control n m N) (P : Transition n m N)
    (s : ℕ) (q : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => q
  | t + 1 => if h : t < N then
      if s ≤ t then fun j => ∑ i, dist u P s q t i * P ⟨t, h⟩ i (u ⟨t, h⟩ i) j
      else q
    else dist u P s q t

/-- Expected cost from s through N, defined by forward distributions, not Bellman values. -/
noncomputable def costFrom {n m N : ℕ} (D : Data n m N) (u : Control n m N)
    (P : Transition n m N) (s : ℕ) (q : Fin n → ℝ) : ℝ :=
  (∑ t : Fin N, if s ≤ t.val then
    ∑ i, dist u P s q t.val i * D.cost t i (u t i) else 0) +
  ∑ i, dist u P s q N i * D.terminal i

def pointMass {n : ℕ} (i : Fin n) : Fin n → ℝ := fun j => if j = i then 1 else 0

/-- Nominal recursion (13.1.8), with terminal value c_N. -/
noncomputable def nominalValue {n m N : ℕ} (D : Data n m N)
    (P : Transition n m N) (t : ℕ) : Fin n → ℝ :=
  if h : t < N then fun i =>
    ⨅ a : Fin m, D.cost ⟨t, h⟩ i a + ∑ j, P ⟨t, h⟩ i a j * nominalValue D P (t + 1) j
  else D.terminal
termination_by N - t

/-- The action selection rule (13.1.7), evaluated at the recursive value function. -/
def NominalGreedy {n m N : ℕ} (D : Data n m N) (P : Transition n m N)
    (u : Control n m N) : Prop :=
  ∀ (t : Fin N) (i : Fin n) (a : Fin m),
    D.cost t i (u t i) + ∑ j, P t i (u t i) j * nominalValue D P (t.val + 1) j ≤
    D.cost t i a + ∑ j, P t i a j * nominalValue D P (t.val + 1) j

/-- Time-dependent rectangular uncertainty; no convexity or sign condition on costs. -/
structure Model (n m N : ℕ) extends Data n m N where
  rows : Fin N → Fin n → Fin m → Set (Fin n → ℝ)
  rows_nonempty : ∀ t i a, (rows t i a).Nonempty
  rows_closed : ∀ t i a, IsClosed (rows t i a)
  rows_simplex : ∀ t i a, rows t i a ⊆ stdSimplex ℝ (Fin n)

abbrev Nature {n m N : ℕ} (M : Model n m N) :=
  {P : Transition n m N // ∀ t i a, P t i a ∈ M.rows t i a}

/-- The expression inside the minimum in (13.3.1). -/
noncomputable def actionValue {n m N : ℕ} (M : Model n m N)
    (t : Fin N) (i : Fin n) (a : Fin m) (v : Fin n → ℝ) : ℝ :=
  M.cost t i a + sSup ((fun p : Fin n → ℝ => ∑ j, p j * v j) '' M.rows t i a)

/-- Backward recursion (13.3.1). The theorem identifies it with the independent game value. -/
noncomputable def robustValue {n m N : ℕ} (M : Model n m N) (t : ℕ) : Fin n → ℝ :=
  if h : t < N then fun i => ⨅ a : Fin m, actionValue M ⟨t, h⟩ i a (robustValue M (t + 1))
  else M.terminal
termination_by N - t

/-- Fixed-policy backward recursion (13.3.4). -/
noncomputable def policyValue {n m N : ℕ} (M : Model n m N)
    (u : Control n m N) (t : ℕ) : Fin n → ℝ :=
  if h : t < N then fun i => actionValue M ⟨t, h⟩ i (u ⟨t, h⟩ i) (policyValue M u (t + 1))
  else M.terminal
termination_by N - t

/-- Worst cost over the full product of admissible nature rows. -/
noncomputable def worstCost {n m N : ℕ} (M : Model n m N) (u : Control n m N)
    (s : ℕ) (q : Fin n → ℝ) : ℝ :=
  sSup (Set.range fun P : Nature M => costFrom M.toData u P.val s q)

/-- Rule (13.3.2). -/
def Greedy {n m N : ℕ} (M : Model n m N) (u : Control n m N) : Prop :=
  ∀ (t : Fin N) (i : Fin n) (a : Fin m),
    actionValue M t i (u t i) (robustValue M (t.val + 1)) ≤
      actionValue M t i a (robustValue M (t.val + 1))

/-- Rule (13.3.3): every selected row actually attains the row maximum. -/
def WorstRows {n m N : ℕ} (M : Model n m N) (P : Nature M) : Prop :=
  ∀ (t : Fin N) (i : Fin n) (a : Fin m),
    IsGreatest ((fun p : Fin n → ℝ => ∑ j, p j * robustValue M (t.val + 1) j) '' M.rows t i a)
      (∑ j, P.val t i a j * robustValue M (t.val + 1) j)

end Setup


end RobustOpt2009.RobustMDP


