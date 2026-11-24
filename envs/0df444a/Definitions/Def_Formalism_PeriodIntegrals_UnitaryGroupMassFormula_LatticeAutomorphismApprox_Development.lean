-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:33:05.597812+00:00
-- url     : https://prove2.me/theorems/d9520cb8-1c83-462a-9ae9-6bf997ecfc18
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/Development.lean

import Definitions.Def_Formalism_PeriodIntegrals_ScXuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
def Hyps (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Prop :=
  1 ≤ g ∧
  (∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2) ∧
  I.n = 2 * r + k + 1 ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) ∧
  (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧
    Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) ∧
  (∃ t : ℕ, t ≡ 1 [MOD g] ∧ Formalism.UG.hform (starRingEnd I.E) I.J z z = -(t : I.E)) ∧
  (∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a))) ∧
  InAt I g 1 (incl I z)
def LocConcl (I : AutInst) (g r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (z0 : Fin I.n → I.E ⊗[I.F] Af I.F) (v : HeightOneSpectrum (𝓞 I.F)) : Prop :=
  ∃ y : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E),
    y ∈ PI.UnitaryGroupMassFormula.AdIndexEq.Uv I v ∧ y ∈ PI.UnitaryGroupMassFormula.AdIndexEq.Kv I v ∧
    (∀ a, (y : Matrix (Fin I.n) (Fin I.n) _) *ᵥ PI.FinKW.vecV I v (incl I (e a)) =
        PI.FinKW.vecV I v (incl I (e a)) ∧
      (y : Matrix (Fin I.n) (Fin I.n) _) *ᵥ PI.FinKW.vecV I v (incl I (f a)) =
        PI.FinKW.vecV I v (incl I (f a))) ∧
    ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      ((y⁻¹ : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) *ᵥ PI.FinKW.vecV I v (incl I z) -
          PI.FinKW.vecV I v z0 = ((g : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) • w
def LocXu : Prop :=
  ∀ (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f), Hyps I g r k e f z →
    ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal → LocConcl I g r e f z Rf.z0 v
def Glue : Prop := LocXu → _root_.PI.ScXuExists.Target
def LocIdem : Prop :=
  ∀ (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (Rf : RefData I g r k e f),
    1 ≤ g → I.n = 2 * r + k + 1 →
    ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      PI.FinKW.psiV I v Rf.ew + PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) = 1
def LocCore : Prop :=
  ∀ (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f), Hyps I g r k e f z →
    ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      PI.FinKW.psiV I v Rf.ew + PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) = 1 →
      LocConcl I g r e f z Rf.z0 v
end PI.UnitaryGroupMassFormula.ScXuExists


