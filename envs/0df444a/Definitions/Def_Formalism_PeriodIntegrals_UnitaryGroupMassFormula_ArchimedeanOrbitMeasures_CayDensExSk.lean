-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExSk
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExSk
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T09:34:18.874567+00:00
-- url     : https://prove2.me/theorems/3ded2a14-d531-54f0-9207-362f88a6c67d
-- title:
--   Cay Dens Ex Sk
-- statement:
--   Definitions and structural lemmas for Cay Dens Ex Sk, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExSk.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_OnePerPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace HcInf
open NumberField IsDedekindDomain HcS.BasicNotions HcS.MainNotions HcS.MainNotions.StandardLattice HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes HcS.L2.Fam.SG.Tau
  HcS.L2.Fam.SG.Tau.InfCmpCut Matrix MeasureTheory Filter
open scoped TensorProduct Topology ENNReal NNReal
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (T : Type) [Fintype T] (emb : T → (E →+* ℂ)) (cd : CDHaar)
def Rel {W : HSpace E} {P Q : ℕ} (θ : T → (Ainf F ⊗[F] E →+* ℂ))
    (A : T → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ) (b : HA (Ainf F) hc.sig W.gram) (ρ : T)
    (x : UpqT P Q) : Prop :=
  UpqT.mat x * A ρ = A ρ * (Units.val (HA.mat (Ainf F) hc.sig W.gram b)).map (θ ρ)
def CdFin : Prop := ∀ P Q : ℕ, SigmaFinite (cd.cd P Q)
def ArchSplit : Prop :=
  OnePerPlace (F := F) emb → ∀ (W : HSpace E) (P Q : ℕ), P + Q = W.rank →
  ∀ θ : T → (Ainf F ⊗[F] E →+* ℂ), (∀ ρ, IsInfEmb (emb ρ) (θ ρ)) →
  ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ,
    (∀ ρ, (A ρ).conjTranspose * HcS.UG.Jpq P Q * A ρ = W.gram.map (emb ρ)) →
  ∃ Φ : HA (Ainf F) hc.sig W.gram ≃ᵐ (T → UpqT P Q),
    (∀ b c, Φ (b * c) = Φ b * Φ c) ∧ Continuous Φ ∧ Continuous Φ.symm ∧
    ∀ b ρ x, (Rel F E hc T θ A b ρ x ↔ x = Φ b ρ)
def LocTamExists : Prop :=
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ W : HSpace E,
    ∃ μ : Measure (HA (Ainf F) hc.sig W.gram), LocTam (Ainf F) hc.sig W.gram (psiInf F ψ) μ
def HaarUnique : Prop :=
  ∀ (W : HSpace E) (P Q : ℕ) (Φ : HA (Ainf F) hc.sig W.gram ≃ᵐ (T → UpqT P Q)),
    (∀ b c, Φ (b * c) = Φ b * Φ c) → Continuous Φ → Continuous Φ.symm →
    ∀ μ : Measure (HA (Ainf F) hc.sig W.gram), μ.IsHaarMeasure →
      ∃ k : ℝ≥0∞, μ.map Φ = k • Measure.pi (fun _ : T => cd.cd P Q)
def DensityConst : Prop :=
  OnePerPlace (F := F) emb → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∃ a : ℕ → ℝ, (∀ M, 0 < a M) ∧
  ∀ (W : HSpace E) (P Q : ℕ), P + Q = W.rank →
  ∀ θ : T → (Ainf F ⊗[F] E →+* ℂ), (∀ ρ, IsInfEmb (emb ρ) (θ ρ)) →
  ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ,
    (∀ ρ, (A ρ).conjTranspose * HcS.UG.Jpq P Q * A ρ = W.gram.map (emb ρ)) →
  ∀ Φ : HA (Ainf F) hc.sig W.gram ≃ᵐ (T → UpqT P Q),
    (∀ b c, Φ (b * c) = Φ b * Φ c) → Continuous Φ → Continuous Φ.symm →
    (∀ b ρ x, (Rel F E hc T θ A b ρ x ↔ x = Φ b ρ)) →
  ∀ (μ : Measure (HA (Ainf F) hc.sig W.gram)) (k : ℝ≥0∞),
    LocTam (Ainf F) hc.sig W.gram (psiInf F ψ) μ →
    μ.map Φ = k • Measure.pi (fun _ : T => cd.cd P Q) → k = ENNReal.ofReal (a W.rank)
variable {F E hc T emb cd}
end HcInf


