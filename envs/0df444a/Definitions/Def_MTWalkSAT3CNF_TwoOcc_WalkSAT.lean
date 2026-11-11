-- Prove2me | Definitions.Def_MTWalkSAT3CNF_TwoOcc_WalkSAT
-- name    : MTWalkSAT3CNF_TwoOcc_WalkSAT
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:45.712079+00:00
-- url     : https://prove2.me/theorems/1e7f4fec-3675-4cb2-9fc1-c54a39d039b9
-- title:
--   The WalkSAT process on a 3-CNF formula
-- statement:
--   Let $F=(C_1,\dots,C_m)$ be a 3-CNF formula over $V$. **WalkSAT** starts from an initial assignment $X_0$ drawn from a law $\mu_0$ on $\{0,1\}^V$ (a point mass for a fixed initial assignment, the product of fair bits for the uniform one). At time $t$, if $\mathrm{Bad}_F(X_t)=\emptyset$ the process stops (the assignment is frozen). Otherwise the clause-selection rule chooses $i_t\in\mathrm{Bad}_F(X_t)$, a position $p$ of $C_{i_t}$ is chosen uniformly (probability $1/3$ each), and the variable $\mathrm{var}(C_{i_t},p)$ is flipped. The running time is
--
--   $$T_{WS}=\inf\{t\ge0:\ \mathrm{Bad}_F(X_t)=\emptyset\},$$
--
--   the number of flips, and $\mathbb E[T_{WS}]$ is its expectation over the initialization and all random choices. The uniform clause-selection rule chooses each index of $\mathrm{Bad}_F(X_t)$ with probability $1/|\mathrm{Bad}_F(X_t)|$.
--
--   **Formalization Note** A state is the assignment together with the record $(i,p)$ of the last flip, so that rules may read all past choices. The trajectory law is `ProbabilityTheory.Kernel.trajMeasure` of the step kernels, $T_{WS}$ is `ℕ∞`-valued and $\mathbb E[T_{WS}]$ is a `lintegral` in `ℝ≥0∞`.
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), Definition 2.1 and Algorithm 1, p. 9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Formula
import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Process

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The WalkSAT process on a 3-CNF formula

Gao–He–Jiang, STOC 2027 submission #914 (October 2026), Definition 2.1 and Algorithm 1 (p. 9).

Conventions.
* A state is the current assignment together with the record of the last update
  `(i, p) ∈ Fin m × Fin 3` (clause index and literal position), `none` at time `0` and once the
  assignment satisfies `F`.
* Step from a history with current assignment `σ`: if `Bad_F(σ) = ∅` the assignment is frozen;
  otherwise the rule chooses `i ∈ Bad_F(σ)`, a position `p` is drawn uniformly from the three
  positions of `C_i` (probability `1/3` each), and the variable `var(C_i, p)` is flipped.
* The initial assignment is drawn from a law `μ₀` on `{0,1}^V` (a Dirac mass for a fixed
  initial assignment, `uniformAssignment V` for the uniform one).
* `T_WS` is the hitting time of `Bad_F = ∅` (the number of flips), and `E[T_WS]` is its
  `lintegral` in `ℝ≥0∞`.
-/

namespace MTWalkSAT3CNF.TwoOcc

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

/-- A state of WalkSAT: the assignment and the record of the last flip (clause, position). -/
abbrev WSState (V : Type*) (m : ℕ) : Type _ := (V → Bool) × Choice (Fin m × Fin 3)

/-- An adaptive clause-selection rule for WalkSAT on `F`: it selects an index in `Bad_F(X_t)`. -/
abbrev WSRule (F : Formula V m) : Type _ :=
  AdaptiveRule (WSState V m) (Fin m) (fun s => (bad F s.1 : Set (Fin m)))

/-- The flip kernel: from the assignment `σ` and a chosen clause `c = some i`, choose a position
`p` of `C_i` uniformly and flip `var(C_i, p)`, recording `(i, p)`; with `c = none`, keep `σ`. -/
noncomputable def wsMove (F : Formula V m) : Kernel ((V → Bool) × Choice (Fin m)) (WSState V m) where
  toFun sc := sc.2.elim (Measure.dirac (sc.1, Choice.none)) (fun i =>
    (PMF.uniformOfFintype (Fin 3)).toMeasure.map
      (fun p => (flip sc.1 ((F i).var p), Choice.some (i, p))))
  measurable' := measurable_of_countable _

instance (F : Formula V m) : IsMarkovKernel (wsMove F) := ⟨fun sc => by
  rcases sc with ⟨σ, c⟩
  cases c with
  | none =>
    show IsProbabilityMeasure (Measure.dirac ((σ, Choice.none) : WSState V m))
    infer_instance
  | some i =>
    exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩

lemma measurable_ws_cur_fst (t : ℕ) : Measurable (fun h : Hist (WSState V m) t => h.cur.1) :=
  measurable_of_countable _

open Classical in
/-- The `t`-th step kernel of WalkSAT on `F` under the rule `R`. -/
noncomputable def wsStep (F : Formula V m) (R : WSRule F) (t : ℕ) :
    Kernel (Hist (WSState V m) t) (WSState V m) :=
  Kernel.piecewise ((Set.to_countable {h : Hist (WSState V m) t | (bad F h.cur.1).Nonempty}).measurableSet)
    (wsMove F ∘ₖ (Kernel.deterministic (fun h => h.cur.1) (measurable_ws_cur_fst t) ×ₖ R.pick t))
    (Kernel.deterministic (fun h => (h.cur.1, Choice.none)) (measurable_of_countable _))

instance (F : Formula V m) (R : WSRule F) (t : ℕ) : IsMarkovKernel (wsStep F R t) := by
  unfold wsStep; infer_instance

/-- The law of the WalkSAT trajectory on `F` under the rule `R`, with initial assignment drawn
from `μ₀`. -/
noncomputable def wsLaw (F : Formula V m) (R : WSRule F) (μ₀ : Measure (V → Bool)) :
    Measure (ℕ → WSState V m) :=
  Kernel.trajMeasure (μ₀.map (fun σ => (σ, Choice.none))) (wsStep F R)

/-- `T_WS`: the first time the assignment satisfies `F` (`⊤` if never). -/
noncomputable def wsTimeOf (F : Formula V m) (ω : ℕ → WSState V m) : ℕ∞ :=
  hitTime (fun s : WSState V m => bad F s.1 = ∅) ω

/-- `E[T_WS]` on `F` under the rule `R` from the initial law `μ₀`. -/
noncomputable def wsExpectedTime (F : Formula V m) (R : WSRule F) (μ₀ : Measure (V → Bool)) :
    ℝ≥0∞ :=
  ∫⁻ ω, (wsTimeOf F ω : ℝ≥0∞) ∂(wsLaw F R μ₀)

/-- The uniform clause-selection rule for WalkSAT on `F`. -/
noncomputable def uniformRuleWS (F : Formula V m) : WSRule F :=
  uniformRule (fun s : WSState V m => (bad F s.1 : Set (Fin m))) (fun s => bad F s.1)
    (fun _ => rfl)

end MTWalkSAT3CNF.TwoOcc


