-- Prove2me | Definitions.Def_QAlgorithms_Defs_WorldModelExperiments
-- name    : QAlgorithms_Defs_WorldModelExperiments
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:38:04.432977+00:00
-- url     : https://prove2.me/theorems/33afbda1-3a7d-48d3-a1da-037fc652fd31
-- title:
--   WorldModelExperiments
-- statement:
--   WorldModelExperiments
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\WorldModelExperiments.lean

import Definitions.Def_QAlgorithms_Defs_WorldModelGeometry
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.IntrinsicLearning

/-- A fresh preparation, chronological finite dynamics word, and final measurement;
one tuple counts as one experiment (2204.13691 p.13, Definition A.2). -/
structure Experiment (X Y Z : Type*) where
  prepare : X
  dynamics : List Y
  measure : Z

/-- State after the actual dynamics word, executed head first (2204.13691 p.13, A.2). -/
def experimentDensity {d : ℕ} {X Y Z B : Type*} [Fintype B]
    (W : WorldModel d X Y Z B) (E : Experiment X Y Z) : Matrix (Fin d) (Fin d) ℂ :=
  E.dynamics.foldl (fun rho y => W.channel y rho) (W.rho E.prepare)

/-- Real Born weights of the actual fresh experiment; quantum legality, rather than
ad hoc normalization, determines the weights (2204.13691 p.13, A.2). -/
def experimentLaw {d : ℕ} {X Y Z B : Type*} [Fintype B]
    (W : WorldModel d X Y Z B) (E : Experiment X Y Z) (b : B) : ℝ :=
  effectProb (W.measurement E.measure b) (experimentDensity W E)

/-- Finite classical adaptive experimental tree with lawful internal finite random draws.
It is chosen before the hidden world, and accesses only sampled outcomes
(2204.13691 pp.3,20-21, C.5 and D.1). -/
inductive ExperimentProgram (X Y Z B A : Type) where
  | output (a : A)
  | experiment (E : Experiment X Y Z) (next : B → ExperimentProgram X Y Z B A)
  | random (size : ℕ) (weights : PMF (Fin size)) (next : Fin size → ExperimentProgram X Y Z B A)

/-- Output Born weights computed recursively from experiments and independent internal
draws, without oracle access to exact experiment probabilities
(2204.13691 pp.13,20-21). -/
def programLaw {d : ℕ} {X Y Z B A : Type} [Fintype B] [DecidableEq A]
    (W : WorldModel d X Y Z B) : ExperimentProgram X Y Z B A → A → ℝ
  | .output a, b => if a = b then 1 else 0
  | .experiment E next, a => ∑ b, experimentLaw W E b*programLaw W (next b) a
  | .random _ weights next, a => ∑ i, (weights i).toReal*programLaw W (next i) a

/-- Worst-case number of fresh experiments, counting an entire dynamics word once
(2204.13691 p.20, C.5). -/
def experimentCount {X Y Z B A : Type} [Fintype B] : ExperimentProgram X Y Z B A → ℕ
  | .output _ => 0
  | .experiment _ next => 1+Finset.univ.sup (fun b => experimentCount (next b))
  | .random _ _ next => Finset.univ.sup (fun i => experimentCount (next i))

example {d : ℕ} {X Y Z B : Type*} [Fintype B] (W : WorldModel d X Y Z B) (x : X) (z : Z) :
    experimentDensity W ⟨x,[],z⟩ = W.rho x := rfl

example {d : ℕ} {X Y Z B A : Type} [Fintype B] [DecidableEq A]
    (W V : WorldModel d X Y Z B) (a b : A) :
    programLaw W (.output a : ExperimentProgram X Y Z B A) b =
      programLaw V (.output a : ExperimentProgram X Y Z B A) b := rfl


/-- Event probabilities computed over the finite execution tree, even for an infinite report
space (2204.13691 p.20, Definition C.5). -/
def programEventLaw {d : ℕ} {X Y Z B A : Type} [Fintype B]
    (W : WorldModel d X Y Z B) (event : A → Prop) :
    ExperimentProgram X Y Z B A → ℝ
  | .output a => if event a then 1 else 0
  | .experiment E next => ∑ b, experimentLaw W E b*programEventLaw W event (next b)
  | .random _ weights next => ∑ i, (weights i).toReal*programEventLaw W event (next i)

end QAlgorithms.IntrinsicLearning


