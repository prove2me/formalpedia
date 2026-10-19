-- Prove2me | Definitions.Def_QAlgorithms_Defs_WorldModelGeometry
-- name    : QAlgorithms_Defs_WorldModelGeometry
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:28.787297+00:00
-- url     : https://prove2.me/theorems/49266d03-5f0a-48d8-ade0-c17a5f757a98
-- title:
--   WorldModelGeometry
-- statement:
--   WorldModelGeometry
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\WorldModelGeometry.lean

import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
noncomputable section

open scoped Matrix

namespace QAlgorithms.IntrinsicLearning

/-- Lawful world tables, with no accuracy or learnability fields
(2204.13691 p.13, Definition A.1). -/
structure WorldModel (d : ℕ) (X Y Z B : Type*) [Fintype B] where
  dimension_pos : 0 < d
  rho : X → Matrix (Fin d) (Fin d) ℂ
  channel : Y → Superop (Fin d) (Fin d)
  measurement : Z → B → Matrix (Fin d) (Fin d) ℂ
  states : ∀ x, IsDensityMatrix (rho x)
  channels : ∀ y, IsChannel (channel y)
  measurements : ∀ z, IsPOVM (measurement z)

/-- One shared unitary or antiunitary gauge; true enables entrywise conjugation
(2204.13691 p.16, Theorem A.8). -/
structure Gauge (d : ℕ) where
  unitary : Matrix.unitaryGroup (Fin d) ℂ
  conjugate : Bool

/-- Common action on states and effects; entrywise conjugation is not adjoint
(2204.13691 p.16, Eqs.(A17),(A19)). -/
def Gauge.apply {d : ℕ} (G : Gauge d) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  let Y := if G.conjugate then X.map (starRingEnd ℂ) else X
  (G.unitary : Matrix _ _ ℂ)*Y*(G.unitary : Matrix _ _ ℂ)ᴴ

/-- Explicit inverse: conjugate(U dagger X U) for the antiunitary case
(2204.13691 p.16, Eq.(A18)). -/
def gaugeInverse {d : ℕ} (G : Gauge d) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  let Y := (G.unitary : Matrix _ _ ℂ)ᴴ*X*(G.unitary : Matrix _ _ ℂ)
  if G.conjugate then Y.map (starRingEnd ℂ) else Y

/-- Hidden universality witnesses: pure preparation, unitary actions generating a dense
SU(d) subgroup, and a nonscalar effect (2204.13691 p.4, Definition 1; p.21, D.1). -/
def IsUniversalWorld {d : ℕ} {X Y Z B : Type*} [Fintype B] (W : WorldModel d X Y Z B) : Prop :=
  (∃ x psi, IsState psi ∧ W.rho x = pureDensity psi) ∧
  (∃ k : ℕ, ∃ y : Fin k → Y, ∃ U : Fin k → Matrix.specialUnitaryGroup (Fin d) ℂ,
    (∀ i, W.channel (y i) = conjSuperop (U i : Matrix _ _ ℂ)) ∧
      Dense (Subgroup.closure (Set.range U) : Set (Matrix.specialUnitaryGroup (Fin d) ℂ))) ∧
  ∃ z b, ¬ ∃ c : ℂ, W.measurement z b = c • 1

example {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    Gauge.apply (⟨1,false⟩ : Gauge d) X = X := by simp [Gauge.apply]

example {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    gaugeInverse (⟨1,true⟩ : Gauge d) X = X.map (starRingEnd ℂ) := by
  simp [gaugeInverse]

end QAlgorithms.IntrinsicLearning


