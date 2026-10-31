-- Prove2me | Definitions.Def_MultiwaySoS_Model
-- name    : MultiwaySoS_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:09.115556+00:00
-- url     : https://prove2.me/theorems/44505df4-1f17-488e-a301-5c52a63f7af7
-- title:
--   §4 — multiway matching instance, the static planning LP $\mathrm{SPP}(\lambda)$, $\mathrm{OPT}$, the dual, and the General Position Gap
-- statement:
--   This module fixes the model of §4 (p.15), the static planning linear program of p.3, its dual of p.16, the total variation ball of p.7 and Definition 2 (pp.15–16).
--
--   1. **Instance.** There are $n$ resource types and $d$ matching configurations. Each type $i$ is offline ($\mathcal I^{\rm off}$), online-queueable ($\mathcal I^{\rm on\text{-}q}$) or online-nonqueueable ($\mathcal I^{\rm on\text{-}nq}$). Configuration $m$ uses one unit of each type in a set $\mathcal I(m)$, so the matching matrix is $M_{im}=\mathbb 1\{i\in\mathcal I(m)\}$, and a match of type $m$ earns a reward $r_m\in\mathbb R$. Every configuration contains at most one online-nonqueueable type, and for every type $i$ there is a configuration with consumption vector $e_i$ and reward $0$ (discarding).
--   2. **Static planning LP.** For $v\in\mathbb R^n$,
--   $$\mathrm{SPP}(v):\quad\max\sum_m r_mx_m\quad\text{s.t.}\quad\sum_m M_{im}x_m=v_i\ (i\in[n]),\ x\ge0,$$
--   and $\mathrm{OPT}(v)$ is its optimal value (the supremum of the objective over the feasible set).
--   3. **Dual.** $\mathrm{DSPP}(v)$: minimize $\sum_i v_i\alpha_i$ subject to $\sum_i M_{im}\alpha_i\ge r_m$ for every $m$.
--   4. **Total variation.** $\|p-q\|_{TV}=\tfrac12\sum_i|p_i-q_i|$; $\mathcal B_{\epsilon,TV}(p)$ is the set of probability distributions $q$ with $\|p-q\|_{TV}\le\epsilon$.
--   5. **General Position Gap (Definition 2).** A distribution $\lambda$ satisfies GPG$_\epsilon$ with optimal basic feasible solution $x^*$ and basis $\mathcal M_+$ if $x^*$ is optimal for $\mathrm{SPP}(\lambda)$, $\mathcal M_+=\{m: x^*_m\neq0\}$, the columns $(M_m)_{m\in\mathcal M_+}$ are linearly independent, and for every $\hat\lambda\in\mathcal B_{\epsilon,TV}(\lambda)$ there is a unique optimal solution of $\mathrm{SPP}(\hat\lambda)$ whose non-zero components are exactly $\mathcal M_+$.
--
--   These objects are the benchmark $\mathrm{OPT}(A^t)$ of Theorem 2 and the condition under which the Sum-of-Squares algorithm, which only uses configurations of $\mathcal M_+$, has bounded regret.
--
--   **Formalization Note** Types are `Fin n`, configurations `Fin d`, and the interval partition of the paper is a labelling `kind`. Several configurations may share a consumption vector and rewards may be negative, as in the paper. $\mathrm{OPT}$ is `sSup` of the objective values; for $v\ge0$ the feasible set is nonempty and, under GPG, bounded above by weak duality, so it is the LP value (both proved in the mission's verification file). Clause 1 of Definition 2 ("$x^*$ is the unique optimal solution with basis $\mathcal M_+$") is not written: it follows from the linear independence of the basic columns.
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, §4 "Resource types and matching configurations", p.15; (SPP(λ)) and OPT(λ), p.3; (DSPP(λ)), p.16; Notation (total variation ball), p.7; Definition 2, pp.15–16

import Mathlib

namespace MultiwaySoS

/-! # The multiway matching instance, the static planning LP and the General Position Gap

Gupta, *Greedy Algorithm for Multiway Matching with Bounded Regret*, arXiv:2112.04622v3:
§4 "Resource types and matching configurations" (p.15), (SPP(λ)) and OPT(λ) (p.3),
(DSPP(λ)) (p.16), total variation and its ball (Notation, p.7), Definition 2 (pp.15–16).

**Formalization Note.** Resource types are `Fin n`, configurations `Fin d`. The paper's matching
matrix `M ∈ {0,1}^{n×d}` (the case the paper focuses on, §4 p.15) is stored as the set
`conf m = I(m)` of resources participating in `m`; `M i m` is its indicator. The partition of
`I = [n]` into the intervals `I^off`, `I^on-q`, `I^on-nq` is a labelling `kind : Fin n → Kind`
(any labelling is an interval partition after renumbering the types). -/

/-- The three kinds of resource types (§4, p.15): offline (`I^off`), online-queueable
(`I^on-q`) and online-nonqueueable (`I^on-nq`). -/
inductive Kind
  | off
  | onQ
  | onNQ
  deriving DecidableEq

/-- A multiway matching instance with `n` resource types and `d` configurations
(arXiv:2112.04622v3, §4, p.15; p.2 "a matching configuration can have at most one item from
I^on-nq"; p.17 "an (exactly one) online-nonqueueable resource unit").

* `kind i` — whether type `i` is offline, online-queueable or online-nonqueueable;
* `conf m` — the set `I(m)` of resource types participating in configuration `m`
  (`M_im = 1` iff `i ∈ conf m`);
* `r m` — the reward `r_m` of a match of type `m` (any real number);
* `nq_le_one` — every configuration contains at most one online-nonqueueable type;
* `discard` — for each `i` there is a configuration with consumption vector `e_i` and reward `0`.

**Formalization Note.** Several configurations may have the same consumption vector; nothing
forbids it in the source. Rewards are not assumed bounded or nonnegative. -/
structure Instance (n d : ℕ) where
  kind : Fin n → Kind
  conf : Fin d → Finset (Fin n)
  r : Fin d → ℝ
  nq_le_one : ∀ m, ((conf m).filter (fun i => kind i = Kind.onNQ)).card ≤ 1
  discard : ∀ i, ∃ m, conf m = {i} ∧ r m = 0

variable {n d : ℕ}

/-- The matching matrix entry `M_im ∈ {0,1}` (§4, p.15), as a real number. -/
noncomputable def Instance.M (I : Instance n d) (i : Fin n) (m : Fin d) : ℝ :=
  if i ∈ I.conf m then 1 else 0

/-- The matching matrix entry `M_im ∈ {0,1}` as an integer (used for queue lengths). -/
def Instance.Mz (I : Instance n d) (i : Fin n) (m : Fin d) : ℤ :=
  if i ∈ I.conf m then 1 else 0

/-- Feasibility for (SPP(v)) (p.3) with right-hand side `v`: `∑_m M_im x_m = v_i` for every
`i`, and `x ≥ 0`. -/
def SPPFeasible (I : Instance n d) (v : Fin n → ℝ) (x : Fin d → ℝ) : Prop :=
  (∀ i, ∑ m, I.M i m * x m = v i) ∧ ∀ m, 0 ≤ x m

/-- The objective `∑_m r_m x_m` of (SPP) (p.3). -/
def sppObjective (I : Instance n d) (x : Fin d → ℝ) : ℝ :=
  ∑ m, I.r m * x m

/-- `x` is an optimal solution of (SPP(v)) (p.3). -/
def IsSPPOptimal (I : Instance n d) (v : Fin n → ℝ) (x : Fin d → ℝ) : Prop :=
  SPPFeasible I v x ∧ ∀ y, SPPFeasible I v y → sppObjective I y ≤ sppObjective I x

/-- `OPT(v)`, the optimal value of (SPP(v)) (p.3, "We denote the optimal value of SPP(λ) by
OPT(λ)").

**Formalization Note.** Defined as `sSup` of the objective over the feasible set. For `v ≥ 0` the
feasible set is nonempty (the zero-reward singletons of `discard`), and under the General Position
Gap it is bounded above by weak duality, so the value is the LP's (both facts are proved in the
mission's verification file). -/
noncomputable def OPT (I : Instance n d) (v : Fin n → ℝ) : ℝ :=
  sSup (sppObjective I '' {x | SPPFeasible I v x})

/-- Feasibility for the dual (DSPP) (p.16): `∑_i M_im α_i ≥ r_m` for every configuration `m`. -/
def DSPPFeasible (I : Instance n d) (α : Fin n → ℝ) : Prop :=
  ∀ m, I.r m ≤ ∑ i, I.M i m * α i

/-- `α` is an optimal solution of (DSPP(v)) (p.16): it is dual feasible and minimizes
`∑_i v_i α_i` among dual feasible vectors. -/
def IsDSPPOptimal (I : Instance n d) (v : Fin n → ℝ) (α : Fin n → ℝ) : Prop :=
  DSPPFeasible I α ∧ ∀ β, DSPPFeasible I β → ∑ i, v i * α i ≤ ∑ i, v i * β i

/-- `p` is a probability distribution on the resource types. -/
def IsDist (p : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- The total variation distance `‖p − q‖_TV = ½ |p − q|₁` (Notation, p.7). -/
noncomputable def tvDist (p q : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ i, |p i - q i|

/-- `q ∈ B_{ε,TV}(p)`: `q` is a probability distribution with `‖p − q‖_TV ≤ ε` (Notation, p.7;
the elements of the ball are distributions, p.8, p.11). -/
def InTVBall (ε : ℝ) (p q : Fin n → ℝ) : Prop :=
  IsDist q ∧ tvDist p q ≤ ε

/-- The General Position Gap condition `GPG_ε` (Definition 2, pp.15–16) for the distribution `lam`,
with the optimal basic feasible solution `xStar` of (SPP(lam)) and its basis `B = M₊`:

1. `lam` is a distribution;
2. `xStar` is an optimal solution of (SPP(lam));
3. `B = M₊ = {m | x*_m > 0}`, the basic activities (the nonzero components, p.4);
4. `xStar` is a *basic* feasible solution: the columns `(M_m)_{m ∈ B}` are linearly independent;
5. for every `λ̂ ∈ B_{ε,TV}(lam)` there is a unique optimal solution of (SPP(λ̂)) whose basic
   activities are exactly `B`.

**Formalization Note.** Clause 1 of Definition 2 ("x* is the unique optimal solution with basis
M₊") is not written: a solution supported on linearly independent columns is determined by them,
so it follows from items 2–4. "With `M₊` as the basic activities" is read as: the set of nonzero
components equals `B` (p.4, "(non-zero components)"). -/
def IsGPG (I : Instance n d) (lam : Fin n → ℝ) (ε : ℝ) (xStar : Fin d → ℝ)
    (B : Finset (Fin d)) : Prop :=
  IsDist lam ∧
  IsSPPOptimal I lam xStar ∧
  (∀ m, xStar m ≠ 0 ↔ m ∈ B) ∧
  LinearIndependent ℝ (fun m : B => fun i : Fin n => I.M i m) ∧
  ∀ q, InTVBall ε lam q → ∃! x, IsSPPOptimal I q x ∧ ∀ m, x m ≠ 0 ↔ m ∈ B

end MultiwaySoS


