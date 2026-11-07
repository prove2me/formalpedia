-- Prove2me | Definitions.Def_SamplingLLL_ExecAnalysis
-- name    : SamplingLLL_ExecAnalysis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:57:35.292942+00:00
-- url     : https://prove2.me/theorems/389bd437-c361-4a5e-8bb4-5a9e758629eb
-- title:
--   Separation, local exactness, conditions (D), (W), (L–R) and the response matrix
-- statement:
--   The hypotheses of Theorem 5.1 on a system of tasks. A task is reachable if it is a root task of the sequential insertion order or a child of a positive-mass transcript of a reachable task. A positive-mass transcript is separated if its active event is $E_t\cap\{\text{every constraint in }R_t\text{ is satisfied}\}$, where $E_t$ depends only on $W_t$, every constraint in $R_t\subseteq S$ avoids $W_t$, and the restoration list enumerates $D_t=S\setminus R_t$. The exact local operation accepts with a mark equal to $y$ on $W_t$ with mass $\lambda(E_t\cap\{X=y\text{ on }W_t\})/[B_iq_i(t)\prod_{j\in C_t}s_j]$. Further,
--   $$
--   L_i(t)=\frac{\bar a_t}{q_i(t)}\prod_j s_j^{-m_j(C_t)},\qquad R_i(t)=\frac1{h_i}\sum_j m_j(C_t)h_j,\qquad M_{ij}=\frac2{s_i}\sum_t m_j(C_t)\bar a_t\prod_{r\in C_t}s_r^{-1},
--   $$
--   with condition (D) $\bar a_t\le B_iq_i(t)\prod_{j\in C_t}s_j$ and condition (W) $\frac2{s_i}\sum_t q_i(t)L_i(t)R_i(t)\le\rho$.
--
--   **Formalization Note** A zero-mass transcript is discarded: $a_t$ is set to $0$ there (p.14). `PrimitiveBound W` states the "uniformly polynomial" hypothesis quantitatively: $W$ bounds $n$, $m$, the fixed charges, the bits of each budget, and the expected ticks of each coordinate draw, proposal and local operation. `typeWeight j` makes the call counter count type $j$.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), §5.1, pp.14–15; Appendix A.3, p.20; eq. (12), p.24

import Mathlib
import Definitions.Def_SamplingLLL_ExecData

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL

open Proc

variable {n m : ℕ}

/-- The transcript `t` of the task `(S, c)` has positive mass. -/
def Pos (P : ProductCSP n m) (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : Prop :=
  0 < P.leafMass (insert c S) t

namespace ExecData

variable {P : ProductCSP n m} (D : ExecData P)

/-- Reachable tasks (p.15): a root task of the sequential insertion order, or a child of a positive-mass
transcript of a reachable task (zero-mass transcripts are discarded, p.14). -/
inductive Reachable : Finset (Fin m) → Fin m → Prop
  | root (i : Fin m) : Reachable (rootSet i) i
  | child {S : Finset (Fin m)} {c : Fin m} {t : Leaf m} {A : Finset (Fin m)} {d : Fin m} :
      Reachable S c → t ∈ D.leavesOf S c → Pos P S c t →
      (A, d) ∈ D.children S c t → Reachable A d

/-- `a_t = λ(E_t)` on a positive-mass transcript, and `0` on a discarded one (p.14). -/
noncomputable def at_ (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : ℝ :=
  open Classical in if Pos P S c t then ((P.prob (D.event S c t) : ℚ) : ℝ) else 0

/-- `s_i = 1 - B_i`. -/
def s (S : Finset (Fin m)) (c : Fin m) : ℝ := 1 - (D.budget S c : ℝ)

/-- `∏_{j∈C_t} s_j`. -/
def sProd (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : ℝ :=
  ((D.children S c t).map fun j => D.s j.1 j.2).prod

/-- The proposal probability `q_i(t)`, the mass of the proposal on `t`. -/
noncomputable def q (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : ℝ :=
  (probOf (D.propose S c) fun o => ∃ r, o = some (t, r)).toReal

/-- A positive-mass transcript is separated (Appendix A.3, p.20; §5.1, p.14): its active event is
`E_t ∩ {every constraint in R_t is satisfied}`, `E_t` depends only on `W_t`, every constraint of
`R_t ⊆ S` avoids `W_t`, and the restoration list enumerates `D_t = S ∖ R_t` without repetition. -/
def Separated (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : Prop :=
  D.rest S c t ⊆ S ∧
  (∀ a ∈ D.rest S c t, Disjoint (P.vbl a) (D.vars S c t)) ∧
  (∀ x y : P.Config, (∀ v ∈ D.vars S c t, x v = y v) → D.event S c t x = D.event S c t y) ∧
  (∀ x : P.Config, P.active (insert c S) t x = (D.event S c t x && P.sat (D.rest S c t) x)) ∧
  (D.restore S c t).Nodup ∧ (D.restore S c t).toFinset = S \ D.rest S c t

/-- The exact local operation (§5.1, p.15): at a transcript of proposal probability `r`, the mass of
acceptance with a mark equal to `y` on `W_t` is `λ(E_t ∩ {X = y on W_t}) / [B_i q_i(t) ∏_{j∈C_t} s_j]`,
that is, the thinning decision of bias `a_t/[B_i q_i(t) ∏ s_j]` jointly with a draw from
`λ_{W_t}(· | E_t)`; acceptance has mass `0` on a discarded transcript. -/
def LocalExact (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) (r : ℚ) : Prop :=
  ∀ y : P.Config,
    probOf (D.localOp S c t r)
        (fun o => ∃ mk : P.Config, o = some mk ∧ ∀ v ∈ D.vars S c t, mk v = y v) =
      open Classical in ENNReal.ofReal
        ((if Pos P S c t then
            ((P.prob fun x => decide (∀ v ∈ D.vars S c t, x v = y v) && D.event S c t x : ℚ) : ℝ)
          else 0) / ((D.budget S c : ℝ) * (r : ℝ) * D.sProd S c t))

/-- The executable proposal of §5.1, p.14: total mass one with the null outcome, supported on terminal
transcripts, and each outcome carries the exact proposal probability of its transcript. -/
def ProposalExact (S : Finset (Fin m)) (c : Fin m) : Prop :=
  mass (D.propose S c) = 1 ∧
  ∀ t r u, D.propose S c (some (t, r), u) ≠ 0 → t ∈ D.leavesOf S c ∧ (r : ℝ) = D.q S c t

/-- The standing hypotheses of Theorem 5.1 on a task, with domination masses `abar`: a finite
separated search, a budget in `(0,1)`, `ā_t ≥ a_t`, an executable proposal with `q_i(t) > 0`
whenever `ā_t > 0`, exact local operations, and (D) in its product form. -/
structure TaskOK (abar : Finset (Fin m) → Fin m → Leaf m → ℝ) (S : Finset (Fin m)) (c : Fin m) :
    Prop where
  explore : IsExploration (insert c S) c (D.next S c)
  notMem : c ∉ S
  separated : ∀ t ∈ D.leavesOf S c, Pos P S c t → D.Separated S c t
  budget_pos : 0 < D.budget S c
  budget_lt : D.budget S c < 1
  dominates : ∀ t ∈ D.leavesOf S c, D.at_ S c t ≤ abar S c t
  proposal : D.ProposalExact S c
  proposal_pos : ∀ t ∈ D.leavesOf S c, 0 < abar S c t → 0 < D.q S c t
  localExact : ∀ t r u, D.propose S c (some (t, r), u) ≠ 0 → D.LocalExact S c t r
  /-- Condition (D), p.15. -/
  envelope : ∀ t ∈ D.leavesOf S c,
    abar S c t ≤ (D.budget S c : ℝ) * D.q S c t * D.sProd S c t

/-- `L_i(t)` of (L–R), p.15. -/
noncomputable def likelihood (abar : Finset (Fin m) → Fin m → Leaf m → ℝ)
    (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : ℝ :=
  abar S c t / D.q S c t * ((D.children S c t).map fun j => (D.s j.1 j.2)⁻¹).prod

/-- `R_i(t)` of (L–R), p.15. -/
noncomputable def load (h : Finset (Fin m) × Fin m → ℝ)
    (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : ℝ :=
  (h (S, c))⁻¹ * ((D.children S c t).map h).sum

/-- Condition (W), p.15, on the task `(S, c)`. -/
def WeightCond (abar : Finset (Fin m) → Fin m → Leaf m → ℝ) (h : Finset (Fin m) × Fin m → ℝ)
    (ρ : ℝ) (S : Finset (Fin m)) (c : Fin m) : Prop :=
  2 / D.s S c * ∑ t ∈ D.leavesOf S c, D.q S c t * D.likelihood abar S c t * D.load h S c t ≤ ρ

/-- The dominating response matrix (12), p.24: `M_ij = (2/s_i) Σ_t m_j(C_t) ā_t ∏_{r∈C_t} s_r⁻¹`. -/
noncomputable def respM (abar : Finset (Fin m) → Fin m → Leaf m → ℝ)
    (i j : Finset (Fin m) × Fin m) : ℝ :=
  2 / D.s i.1 i.2 * ∑ t ∈ D.leavesOf i.1 i.2,
    ((D.children i.1 i.2 t).count j : ℝ) * abar i.1 i.2 t *
      ((D.children i.1 i.2 t).map fun r => (D.s r.1 r.2)⁻¹).prod

/-- The quantitative form of the "uniformly polynomial" hypothesis of Theorem 5.1, p.15: `W` bounds
the size parameters, the fixed charges, the bit length of every budget, and the expected ticks of
each coordinate draw, of each proposal, and of each local operation. -/
structure PrimitiveBound (W : ℝ) : Prop where
  n_le : (n : ℝ) ≤ W
  m_le : (m : ℝ) ≤ W
  step_le : (D.stepCost : ℝ) ≤ W
  test_le : (D.testCost : ℝ) ≤ W
  move_le : (D.moveCost : ℝ) ≤ W
  draw_le : ∀ v, expTicks (P.drawCoord v) ≤ ENNReal.ofReal W
  budget_bits : ∀ S c, D.Reachable S c → (bits (D.budget S c) : ℝ) ≤ W
  budget_cost : ∀ S c, D.Reachable S c → (D.budgetCost S c : ℝ) ≤ W
  propose_le : ∀ S c, D.Reachable S c → expTicks (D.propose S c) ≤ ENNReal.ofReal W
  local_le : ∀ S c t r u, D.Reachable S c → D.propose S c (some (t, r), u) ≠ 0 →
    expTicks (D.localOp S c t r) ≤ ENNReal.ofReal W

/-- `1` on the task `j`, `0` elsewhere: run with this weight, the call counter counts the
invocations of type `j` alone. -/
def typeWeight (j : Finset (Fin m) × Fin m) (S : Finset (Fin m)) (c : Fin m) : ℕ :=
  if (S, c) = j then 1 else 0

/-- The probability of the positive minus the negative outcomes, the normalized value of the signed
experiment: `E[Y_i] = B_i · signedMass`. -/
noncomputable def signedMass (p : Proc (Option (Leaf m × P.Config))) : ℝ :=
  (probOf p fun o => ∃ t mk, o = some (t, mk) ∧ sign t = 1).toReal -
    (probOf p fun o => ∃ t mk, o = some (t, mk) ∧ sign t = -1).toReal

end ExecData

end SamplingLLL


