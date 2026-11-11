-- Prove2me | Definitions.Def_OneTrap_Core_Search
-- name    : OneTrap_Core_Search
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:44:57.519599+00:00
-- url     : https://prove2.me/theorems/f5be3b59-4dba-45d2-9b41-49aa2612bfa2
-- title:
--   Policies with recall and the null output, payoffs $U_A$, $P_A$, the principal-favored value $V_P(w\mid A)$, Bellman values $U(R,x,h)$, $P(R,x,h)$ and the robust guarantee $G_K(w)$
-- statement:
--   Fix a contract $w$ and a technology $A$. The agent opens boxes one at a time (each at most once), pays their costs, observes their outputs, and finally stops and submits one **available outcome**: the null output $Y_0=0$ (wage $w(0)$, residual $-w(0)$) or an output already observed (recall). Output $y$ pays wage $w(y)$ and leaves residual $y-w(y)$ to the principal. A **policy** may be randomized and history dependent, and is measurable. With $O_\pi$ the opened set, $Y^{\mathrm{fin}}_\pi$ the submitted output and $C_\pi=\sum_{i\in O_\pi}c_i$,
--   $$U_A(w,\pi)=\mathbb E_\pi[w(Y^{\mathrm{fin}}_\pi)-C_\pi],\qquad P_A(w,\pi)=\mathbb E_\pi[Y^{\mathrm{fin}}_\pi-w(Y^{\mathrm{fin}}_\pi)]$$
--   in the extended reals. $\Sigma^\star(w,A)=\arg\max_\pi U_A(w,\pi)$ and the **principal-favored value** is $V_P(w\mid A)=\max_{\pi\in\Sigma^\star(w,A)}P_A(w,\pi)$ (Definition 2.2). $V_P(w\mid A;x,h)$ is the same with an extra outcome of wage $x$ and residual $h$ available from the start (§3.2). At a **state** $(R,x,h)$ — unopened boxes $R$, incumbent wage $x$ and residual $h$ — $U(R,x,h)$ is the agent's optimal expected terminal wage minus the costs of boxes opened afterwards, and $P(R,x,h)$ the best expected terminal residual among the policies attaining it (Lemma B.1). The **robust guarantee** of $w$ for a known technology $K$ is $G_K(w)=\inf_{A\in E_f(K)}V_P(w\mid A)$, the infimum over all finite independent extensions $A\supseteq K$, $A=K$ included (§2.2).
--
--   **Formalization Note** A search problem is a technology `T : ι → Box`, a set `R` of openable boxes and initial outcomes `init : κ → ℝ × ℝ` (wage, residual). All outputs `y : ι → ℝ` are drawn from the product law together with one seed `u` uniform on $[0,1]$ (`jointLaw`). A `Policy κ R` is a rule `rule S y u : Choice κ R S` — open some `i ∈ R \ S` or stop and submit `Sum.inl k` (initial outcome) or `Sum.inr j`, `j ∈ S` — that reads `y` only on `S` and is measurable; `run` executes it (each box at most once, so it ends). `agentValue`/`principalValue` are `eexp` of the realized payoffs; `agentOptimal` is $\Sigma^\star$; `pfValue` is the `EReal` `sSup` of `principalValue` over `agentOptimal` (attainment is Fact A.1; `⊥` if that set were empty, which Fact A.1 excludes). `VP w T` uses `R = univ` and the null pair `(w 0, 0 − w 0)`; `VPat` adds `(x, h)`. `Ubell w T R x h` is the supremum of the agent value and `Pbell w T R x h` the `pfValue` of the problem with openable set `R` and the single initial outcome `(x, h)` — optimal values, not the recursion (17). `robustGuarantee w K = ⨅ n (N : Fin n → Box), VP w (Sum.elim K N)` in `EReal` (possibly `⊥`); `withTrap w K y t hy ht` is `K` plus one trap on `κ ⊕ Unit`. A policy is `IsDeterministic` if its rule ignores the seed.
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), §2.1, pp. 4–5 (PDF 5–6); Definition 2.2, p. 5 (PDF 6); §2.2, p. 5 (PDF 6); §3.2, p. 6 (PDF 7); Lemma B.1, p. 22 (PDF 23)

import Mathlib
import Definitions.Def_OneTrap_Core_Model

/-!
# Search: histories, policies, payoffs, the principal-favored value and the robust guarantee

Feldman, Fu, Peng, Tang (2026), held STOC 2027 submission, §2.1 (pp. 4–5), Definition 2.2
(p. 5), §2.2 (p. 5), §3.2 (p. 6), §B.1.1 (p. 22).

**Search problem.** A technology `T : ι → Box` over a finite index type, a finite set `R` of
boxes that may be opened, and a finite family `init : κ → ℝ × ℝ` of outcomes available from the
start, each given by its (wage, residual) pair. The agent opens boxes of `R` one at a time, pays
their costs, observes their outputs, and finally stops and submits one available outcome: one of
`init` or an output already observed (recall). For the plain problem `κ = Unit` and the only
initial outcome is the null output `Y₀ = 0`, with pair `(w 0, 0 − w 0)`.

**Policies (encoding).** All outputs `y : ι → ℝ` are drawn at the start from the product law
(independence, Assumption 2.1), together with one independent seed `u` uniform on `[0, 1]`.
A policy is a rule that, given the set `S` of boxes already opened, the outputs and the seed,
either opens a box of `R \ S` or stops and submits an available outcome. It is
*non-anticipating* (it reads `y` only on `S`) and measurable. Since the order in which `S` was
opened is itself a function of the rule, the outputs on `S` and the seed, this is the same as a
rule on ordered histories; one uniform seed generates the independent randomizations of a
randomized (kernel) policy at every step, and conversely, so the set of laws of (opened set,
submitted outcome) is the paper's.
-/

noncomputable section

open MeasureTheory

namespace OneTrap.Core

variable {κ ι : Type*}

/-- A decision at opened set `S`: open a box `i ∈ R \ S`, or stop and submit an initially
available outcome (`Sum.inl k`) or the output of an opened box (`Sum.inr j`, `j ∈ S`). -/
inductive Choice (κ : Type*) {ι : Type*} (R S : Finset ι) : Type _ where
  | openBox (i : ι) (hR : i ∈ R) (hS : i ∉ S) : Choice κ R S
  | stop (s : κ ⊕ S) : Choice κ R S

/-- The box opened by a decision, if any. -/
def Choice.box? {R S : Finset ι} : Choice κ R S → Option ι
  | .openBox i _ _ => some i
  | .stop _ => none

/-- A (randomized, history-dependent, measurable, non-anticipating) policy for a search problem
in which the boxes of `R` may be opened and the outcomes indexed by `κ` are available from the
start. `rule S y u` is the decision when the boxes of `S` have been opened, `y` are the outputs
and `u` the seed. -/
structure Policy (κ : Type*) {ι : Type*} (R : Finset ι) where
  /-- The decision rule. -/
  rule : (S : Finset ι) → (ι → ℝ) → ℝ → Choice κ R S
  /-- Decisions use only outputs already observed (and the seed). -/
  nonanticipating : ∀ (S : Finset ι) (y y' : ι → ℝ) (u : ℝ),
    (∀ i ∈ S, y i = y' i) → rule S y u = rule S y' u
  /-- Decisions are Borel measurable in the outputs and the seed. -/
  measurable : ∀ (S : Finset ι) (d : Choice κ R S),
    MeasurableSet {p : (ι → ℝ) × ℝ | rule S p.1 p.2 = d}

/-- A deterministic policy: its decisions do not depend on the seed. -/
def Policy.IsDeterministic {R : Finset ι} (π : Policy κ R) : Prop :=
  ∀ (S : Finset ι) (y : ι → ℝ) (u u' : ℝ), π.rule S y u = π.rule S y u'

variable [DecidableEq ι]

/-- Running a policy from the opened set `S`: the final opened set and the submitted outcome
(`Sum.inl k` an initial outcome, `Sum.inr j` the output of box `j`). Each box is opened at most
once, so the run ends after at most `|R \ S|` openings. -/
def Policy.runFrom {R : Finset ι} (π : Policy κ R) (y : ι → ℝ) (u : ℝ) (S : Finset ι) :
    Finset ι × (κ ⊕ ι) :=
  match π.rule S y u with
  | .openBox i hR hS => π.runFrom y u (insert i S)
  | .stop s => (S, s.map id Subtype.val)
termination_by (R \ S).card
decreasing_by
  rw [Finset.sdiff_insert]
  exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨hR, hS⟩)

/-- The run of a policy from the start: the random set `O_π` of opened boxes and the submitted
outcome. -/
def Policy.run {R : Finset ι} (π : Policy κ R) (y : ι → ℝ) (u : ℝ) : Finset ι × (κ ⊕ ι) :=
  π.runFrom y u ∅

/-- The (wage, residual) pair of an available outcome: an initial outcome carries its own pair;
the output `y j` of box `j` pays wage `w(y j)` and leaves residual `y j − w(y j)`. -/
def outcomePair (w : ℝ → ℝ) (init : κ → ℝ × ℝ) (y : ι → ℝ) : κ ⊕ ι → ℝ × ℝ
  | .inl k => init k
  | .inr j => (w (y j), y j - w (y j))

variable [Fintype ι]

/-- The uniform law of the randomization seed on `[0, 1]`. -/
def seedLaw : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The joint law of all outputs (independent, product measure) and the seed. -/
def jointLaw (T : ι → Box) : Measure ((ι → ℝ) × ℝ) :=
  (Measure.pi fun i => ((T i).out.law : Measure ℝ)).prod seedLaw

/-- The product law of the outputs alone. -/
def outputLaw (T : ι → Box) : Measure (ι → ℝ) :=
  Measure.pi fun i => ((T i).out.law : Measure ℝ)

/-- Realized agent payoff `w(Y^fin) − C_π`. -/
def agentPay (w : ℝ → ℝ) (T : ι → Box) {R : Finset ι} (init : κ → ℝ × ℝ) (π : Policy κ R)
    (ω : (ι → ℝ) × ℝ) : ℝ :=
  (outcomePair w init ω.1 (π.run ω.1 ω.2).2).1 - ∑ i ∈ (π.run ω.1 ω.2).1, (T i).cost

/-- Realized principal payoff `Y^fin − w(Y^fin)`. -/
def principalPay (w : ℝ → ℝ) {R : Finset ι} (init : κ → ℝ × ℝ) (π : Policy κ R)
    (ω : (ι → ℝ) × ℝ) : ℝ :=
  (outcomePair w init ω.1 (π.run ω.1 ω.2).2).2


/-- `U(π) = E_π[w(Y^fin) − C_π]`, an extended-real expectation. -/
def agentValue (w : ℝ → ℝ) (T : ι → Box) {R : Finset ι} (init : κ → ℝ × ℝ)
    (π : Policy κ R) : EReal :=
  eexp (jointLaw T) fun ω => (agentPay w T init π ω : EReal)

/-- `P(π) = E_π[Y^fin − w(Y^fin)]`, an extended-real expectation. -/
def principalValue (w : ℝ → ℝ) (T : ι → Box) {R : Finset ι} (init : κ → ℝ × ℝ)
    (π : Policy κ R) : EReal :=
  eexp (jointLaw T) fun ω => (principalPay w init π ω : EReal)

/-- The agent-optimal policies `Σ⋆ = argmax_π U(π)` (possibly empty as a definition; Fact A.1
shows it is not). -/
def agentOptimal (w : ℝ → ℝ) (T : ι → Box) (R : Finset ι) (init : κ → ℝ × ℝ) :
    Set (Policy κ R) :=
  {π | ∀ π' : Policy κ R, agentValue w T init π' ≤ agentValue w T init π}

/-- The principal-favored value of a search problem: the supremum of `P(π)` over the
agent-optimal policies (`⊥` if there are none). Attainment is Fact A.1, not part of the
definition. -/
def pfValue (w : ℝ → ℝ) (T : ι → Box) (R : Finset ι) (init : κ → ℝ × ℝ) : EReal :=
  sSup (principalValue w T init '' agentOptimal w T R init)

/-- The null output `Y₀ = 0`: wage `w(0)`, residual `0 − w(0)`. -/
def nullPair (w : ℝ → ℝ) : Unit → ℝ × ℝ := fun _ => (w 0, 0 - w 0)

/-- `V_P(w | A)` (Definition 2.2, p. 5): every box of `A` may be opened and the null output is
available from the start. -/
def VP (w : ℝ → ℝ) (T : ι → Box) : EReal :=
  pfValue w T Finset.univ (nullPair w)

/-- `V_P(w | A; x, h)` (§3.2, p. 6): besides the null output, an outcome with wage `x` and
residual `h` is available from the start. -/
def VPat (w : ℝ → ℝ) (T : ι → Box) (x h : ℝ) : EReal :=
  pfValue w T Finset.univ (fun b : Bool => if b then (x, h) else (w 0, 0 - w 0))

/-- The Bellman agent value `U(R, x, h)` (Lemma B.1, p. 22): the agent's optimal expected
terminal wage minus the costs of boxes opened after the state, when the boxes of `R` are
unopened and the incumbent outcome has wage `x` and residual `h`. Defined as an optimal value
(a supremum over all policies), not by the recursion (17). -/
def Ubell (w : ℝ → ℝ) (T : ι → Box) (R : Finset ι) (x h : ℝ) : EReal :=
  ⨆ π : Policy Unit R, agentValue w T (fun _ : Unit => (x, h)) π

/-- The Bellman principal value `P(R, x, h)` (Lemma B.1, p. 22): the best expected terminal
residual among the policies attaining `U(R, x, h)`. -/
def Pbell (w : ℝ → ℝ) (T : ι → Box) (R : Finset ι) (x h : ℝ) : EReal :=
  pfValue w T R (fun _ : Unit => (x, h))

end OneTrap.Core

namespace OneTrap.Core

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The robust guarantee `G_K(w) = inf_{A ∈ E_f(K)} V_P(w | A)` (§2.2, p. 5), an extended-real
infimum. An admissible extension `A ⊇ K` is `K ⊕ N` with `N : Fin n → Box` any finite family of
new boxes with fresh labels (any laws and costs, duplicates of known boxes allowed; `n = 0` is
`A = K`). -/
def robustGuarantee (w : ℝ → ℝ) (K : κ → Box) : EReal :=
  ⨅ (n : ℕ) (N : Fin n → Box), VP w (Sum.elim K N)

/-- `K ∪ {trap(y, t)}`: the known technology with one fresh trap box. -/
def withTrap (w : ℝ → ℝ) (K : κ → Box) (y t : ℝ) (hy : 0 ≤ y) (ht : t ≤ w y) :
    κ ⊕ Unit → Box :=
  Sum.elim K fun _ => trap w y t hy ht

end OneTrap.Core


