-- Prove2me | Definitions.Def_BrownSharedSignals_Fluid_FluidLP
-- name    : BrownSharedSignals_Fluid_FluidLP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:50:54.011247+00:00
-- url     : https://prove2.me/theorems/d6398541-dff7-42d1-b67c-6ae4c895d867
-- title:
--   The fluid Bellman LP (EC-2) and its explicit dual (EC-3)
-- statement:
--   Given finite affine representations of all next-period fluid values, LP (EC-2) has explicit variables for the current control, next fluid vector and one continuation value for each next signal. It imposes the resource bound, state-mass equations, fluid transition equations, and one affine upper bound per next-signal affine piece. Only control variables are constrained to be nonnegative. Its objective is current reward plus expected continuation value. The actual coefficient matrix is constructed by evaluating these linear expressions on coordinate basis vectors and reindexing the finite coordinates into the published general-form LP API; its minimization objective is the negative of the source maximization objective.
--
--   The explicit dual (EC-3) contains a free mass-constraint vector, a nonnegative resource multiplier, and nonnegative continuation multipliers summing to one for each next signal. Its local action inequalities and objective are written directly as in the appendix. Optimality means feasible and no larger objective than any other feasible dual point. No supergradient or strong-duality claim is assumed in these definitions.
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), Appendix EC2, equations (EC-2)–(EC-3), printed EC-3–EC-4 / PDF 41–42

import Definitions.Def_BrownSharedSignals_Fluid_FluidControl
import Definitions.Def_LinearOptimization_DualLP

open scoped BigOperators
noncomputable section

namespace BrownSharedSignals.Fluid
variable {N T : ℕ}

abbrev MassIndex (M : Model N T) := (i : Fin N) × Fin (M.stateSize i+1)
abbrev ControlIndex (M : Model N T) (t : ℕ) (z : Signal M) :=
  (i : Fin N) × (s : Fin (M.stateSize i+1)) × Action M t i s z
abbrev EC2Variable (M : Model N T) (t : ℕ) (z : Signal M) :=
  ControlIndex M t z ⊕ (MassIndex M ⊕ Signal M)
abbrev EC2Row (M : Model N T) (K : Signal M → AffinePieces M) :=
  Unit ⊕ (MassIndex M ⊕ (MassIndex M ⊕ ((z : Signal M) × Fin ((K z).count+1))))

def EC2Control (M : Model N T) (t : ℕ) (z : Signal M)
    (x : EC2Variable M t z → ℝ) : Control M t z :=
  fun i s a => x (.inl ⟨i,s,a⟩)
def EC2Next (M : Model N T) (t : ℕ) (z : Signal M)
    (x : EC2Variable M t z → ℝ) : FluidVector M :=
  fun i s => x (.inr (.inl ⟨i,s⟩))
def EC2Objective (M : Model N T) (t : ℕ) (z : Signal M)
    (x : EC2Variable M t z → ℝ) : ℝ :=
  fluidReward M t z (EC2Control M t z x) + ∑ z', M.signal t z z' * x (.inr (.inr z'))

def EC2LHS (M : Model N T) (t : ℕ) (z : Signal M)
    (K : Signal M → AffinePieces M) (x : EC2Variable M t z → ℝ) : EC2Row M K → ℝ
  | .inl _ => ∑ i, ∑ s, ∑ a, M.consumption t i s z a.val * EC2Control M t z x i s a
  | .inr (.inl ⟨i,s⟩) => ∑ a, EC2Control M t z x i s a
  | .inr (.inr (.inl ⟨i,s⟩)) => EC2Next M t z x i s - fluidNext M t z (EC2Control M t z x) i s
  | .inr (.inr (.inr ⟨z',k⟩)) => x (.inr (.inr z')) - fluidDot M ((K z').slope k) (EC2Next M t z x)

def EC2RHS (M : Model N T) (t : ℕ) (f : FluidVector M) (z : Signal M)
    (K : Signal M → AffinePieces M) : EC2Row M K → ℝ
  | .inl _ => M.budget t z
  | .inr (.inl ⟨i,s⟩) => f i s
  | .inr (.inr (.inl _)) => 0
  | .inr (.inr (.inr ⟨z',k⟩)) => (K z').intercept k

def EC2Relation (M : Model N T) (K : Signal M → AffinePieces M) : EC2Row M K → LinearOptimization.ConstraintRel
  | .inl _ => .le
  | .inr (.inl _) => .eq
  | .inr (.inr (.inl _)) => .eq
  | .inr (.inr (.inr _)) => .le

/-- Actual LP (EC-2), reindexed to the published general LP API. Its minimization
objective is the negative of the source's maximization objective. `f'` and each
continuation value V(z') are explicit variables; no fluid state is discretized. -/
def EC2LP (M : Model N T) (t : ℕ) (f : FluidVector M) (z : Signal M)
    (K : Signal M → AffinePieces M) :
    LinearOptimization.GeneralFormLP (Fintype.card (EC2Row M K)) (Fintype.card (EC2Variable M t z)) := by
  classical
  let er := (Fintype.equivFin (EC2Row M K)).symm
  let ev := (Fintype.equivFin (EC2Variable M t z)).symm
  exact {
    A := fun r v => EC2LHS M t z K (fun j => if j = ev v then 1 else 0) (er r)
    b := fun r => EC2RHS M t f z K (er r)
    c := fun v => -EC2Objective M t z (fun j => if j = ev v then 1 else 0)
    rowRel := fun r => EC2Relation M K (er r)
    colSign := fun v => match ev v with | .inl _ => .nonneg | .inr _ => .free }

def EC2Value (M : Model N T) (t : ℕ) (f : FluidVector M) (z : Signal M)
    (K : Signal M → AffinePieces M) : ℝ :=
  let P := EC2LP M t f z K;
  -sInf {v | ∃ x, x ∈ LinearOptimization.generalFeasibleSet P ∧ v = ∑ j, P.c j * x j}

/-- The mass-constraint vector, resource multiplier and normalized continuation
multipliers in the explicit source dual (EC-3). -/
structure EC3Point (M : Model N T) (K : Signal M → AffinePieces M) where
  theta : FluidVector M
  zeta : ℝ
  eta : (z : Signal M) → Fin ((K z).count+1) → ℝ

def EC3Feasible (M : Model N T) (t : ℕ) (z : Signal M)
    (K : Signal M → AffinePieces M) (d : EC3Point M K) : Prop :=
  0 ≤ d.zeta ∧ (∀ z' k, 0 ≤ d.eta z' k) ∧ (∀ z', ∑ k, d.eta z' k = 1) ∧
  ∀ i s (a : Action M t i s z),
    (M.project i).reward t s z a.val - d.zeta * M.consumption t i s z a.val +
      (∑ z', ∑ s', M.signal t z z' * (M.project i).transition t s z a.val s' *
        ∑ k, (K z').slope k i s' * d.eta z' k) ≤ d.theta i s

def EC3Objective (M : Model N T) (t : ℕ) (f : FluidVector M) (z : Signal M)
    (K : Signal M → AffinePieces M) (d : EC3Point M K) : ℝ :=
  fluidDot M d.theta f + d.zeta * M.budget t z +
    ∑ z', ∑ k, M.signal t z z' * (K z').intercept k * d.eta z' k

def EC3Optimal (M : Model N T) (t : ℕ) (f : FluidVector M) (z : Signal M)
    (K : Signal M → AffinePieces M) (d : EC3Point M K) : Prop :=
  EC3Feasible M t z K d ∧ ∀ e, EC3Feasible M t z K e → EC3Objective M t f z K d ≤ EC3Objective M t f z K e

end BrownSharedSignals.Fluid


