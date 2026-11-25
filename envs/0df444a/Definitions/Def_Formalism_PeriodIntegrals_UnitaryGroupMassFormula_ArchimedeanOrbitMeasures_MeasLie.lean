-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_MeasLie
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_MeasLie
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:58:39.742888+00:00
-- url     : https://prove2.me/theorems/4a7b32f6-a202-5104-bc8a-f7b418217bf3
-- title:
--   Meas Lie
-- statement:
--   Definitions and structural lemmas for Meas Lie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/MeasLie.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_IsInfEmb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace HcS.L2.Fam.SG.Tau
open NumberField IsDedekindDomain HcS.BasicNotions HcS.MainNotions HcS.MainNotions.StandardLattice HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix MeasureTheory Filter
open scoped TensorProduct Topology ENNReal NNReal
section Defs
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Loc
variable (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
def LieU : AddSubgroup (Matrix (Fin M) (Fin M) (R ⊗[F] E)) where
  carrier := {X | HcS.UG.cT (sigR R σ) X * JR R J + JR R J * X = 0}
  zero_mem' := by
    show HcS.UG.cT (sigR R σ) 0 * JR R J + JR R J * 0 = 0
    simp [HcS.UG.cT]
  add_mem' := by
    intro X Y hX hY
    have e : HcS.UG.cT (sigR R σ) (X + Y) = HcS.UG.cT (sigR R σ) X + HcS.UG.cT (sigR R σ) Y := by
      ext i j; simp [HcS.UG.cT]
    show HcS.UG.cT (sigR R σ) (X + Y) * JR R J + JR R J * (X + Y) = 0
    have h1 : HcS.UG.cT (sigR R σ) X * JR R J + JR R J * X = 0 := hX
    have h2 : HcS.UG.cT (sigR R σ) Y * JR R J + JR R J * Y = 0 := hY
    rw [e, add_mul, mul_add, add_add_add_comm, h1, h2, add_zero]
  neg_mem' := by
    intro X hX
    have e : HcS.UG.cT (sigR R σ) (-X) = -HcS.UG.cT (sigR R σ) X := by
      ext i j; simp [HcS.UG.cT]
    show HcS.UG.cT (sigR R σ) (-X) * JR R J + JR R J * (-X) = 0
    have h1 : HcS.UG.cT (sigR R σ) X * JR R J + JR R J * X = 0 := hX
    rw [e, neg_mul, mul_neg, ← neg_add, h1, neg_zero]
instance measLie [TopologicalSpace R] : MeasurableSpace (LieU R σ J) := borel _
def trF (X Y : LieU R σ J) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (Matrix.trace (X.1 * Y.1))
def cay (U : Set (LieU R σ J)) : Set (HA R σ J) :=
  {g | ∃ X ∈ U, Units.val (HA.mat R σ J g) * ((1 + 1) - X.1) = (1 + 1) + X.1}
def LocTam [TopologicalSpace R] (ψR : R → ℂ) (μ : Measure (HA R σ J)) : Prop :=
  μ.IsHaarMeasure ∧ ∃ ν : Measure (LieU R σ J), SelfDual ν (fun X Y => ψR (trF R σ J X Y)) ∧
    ∀ ε : ℝ≥0, 0 < ε → ∃ V ∈ 𝓝 (0 : LieU R σ J), ∀ U ⊆ V, MeasurableSet U →
      μ (cay R σ J U) ≤ (1 + ε) * ν U ∧ ν U ≤ (1 + ε) * μ (cay R σ J U)
variable {J} {J' : Matrix (Fin M) (Fin M) E} (g : GL (Fin M) (R ⊗[F] E))
variable [TopologicalSpace R] [IsTopologicalRing R]
end Loc
end Defs
section Gaps
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
end Gaps
end HcS.L2.Fam.SG.Tau
end


