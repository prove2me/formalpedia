-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_OnePerPlace
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_OnePerPlace
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:05:52.659101+00:00
-- url     : https://prove2.me/theorems/db62688e-7952-4811-90f5-9227fed1102e
-- title:
--   One Per Place
-- statement:
--   Definitions and structural lemmas for One Per Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/OnePerPlace.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_MeasLie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace HcS.L2.Fam.SG.Tau.InfCmpCut
open NumberField IsDedekindDomain HcS.BasicNotions HcS.MainNotions HcS.MainNotions.StandardLattice HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes HcS.L2.Fam.SG.Tau Matrix
  MeasureTheory Filter
open scoped TensorProduct Topology ENNReal NNReal
def OnePerPlace {F E : Type} [Field F] [Field E] [Algebra F E] {T : Type} (emb : T → (E →+* ℂ)) : Prop :=
  Function.Bijective fun ρ : T => (emb ρ).comp (algebraMap F E)
def InfCmpG (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (T : Type) [Fintype T] (emb : T → (E →+* ℂ)) (cd : CDHaar) : Prop :=
  OnePerPlace (F := F) emb →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ a : ℕ → ℝ, (∀ M, 0 < a M) ∧
  ∀ (W : HSpace E) (P Q : ℕ), P + Q = W.rank →
  ∀ θ : T → (Ainf F ⊗[F] E →+* ℂ), (∀ ρ, IsInfEmb (emb ρ) (θ ρ)) →
  ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ,
    (∀ ρ, (A ρ).conjTranspose * HcS.UG.Jpq P Q * A ρ = W.gram.map (emb ρ)) →
  ∃ μ : Measure (HA (Ainf F) hc.sig W.gram), LocTam (Ainf F) hc.sig W.gram (psiInf F ψ) μ ∧
  ∀ B : T → Set (UpqT P Q), (∀ ρ, MeasurableSet (B ρ)) →
    let S : Set (HA (Ainf F) hc.sig W.gram) := {b | ∀ ρ, ∃ x ∈ B ρ, UpqT.mat x * A ρ = A ρ *
      (Units.val (HA.mat (Ainf F) hc.sig W.gram b)).map (θ ρ)}
    MeasurableSet S ∧ μ S = ENNReal.ofReal (a W.rank) * ∏ ρ, cd.cd P Q (B ρ)
end HcS.L2.Fam.SG.Tau.InfCmpCut


