-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:41:33.325219+00:00
-- url     : https://prove2.me/theorems/ed3150bb-b896-4144-a74d-f841f88caca4
-- title:
--   Inst Decomp
-- statement:
--   Definitions and structural lemmas for Inst Decomp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstDecomp.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
namespace PI.ScMuExists.UnitaryGroupMassFormula
section Gen
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
def haarSub (K : Subgroup G) (hK : IsClosed (K : Set G)) : Measure G :=
  haveI : LocallyCompactSpace K := hK.isClosedEmbedding_subtypeVal.locallyCompactSpace
  (Measure.haar : Measure K).map Subtype.val
def mulMeas (μ μ' : Measure G) : Measure G := (μ.prod μ').map (fun p : G × G => p.1 * p.2)
end Gen
def GenHaarSub : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (K : Subgroup G) (hK : IsClosed (K : Set G)),
    SigmaFinite (haarSub K hK) ∧ haarSub K hK ≠ 0 ∧ haarSub K hK (K : Set G)ᶜ = 0 ∧
    (∀ s ∈ K, (haarSub K hK).map (fun x => s * x) = haarSub K hK) ∧
    (∀ C : Set G, IsCompact C → haarSub K hK C < ⊤) ∧
    (∀ U : Set G, IsOpen U → (1 : G) ∈ U → 0 < haarSub K hK U)
def GenSemi : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (N H : Subgroup G)
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G)),
    (∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) →
    (∀ h ∈ H, (haarSub N hN).map (fun x => h * x * h⁻¹) = haarSub N hN) →
    (∀ C : Set G, IsCompact C → IsCompact {p : G × G | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C}) →
    SFinite (mulMeas (haarSub N hN) (haarSub H hH)) ∧
    MeasurableSet ((N : Set G) * (H : Set G)) ∧
    mulMeas (haarSub N hN) (haarSub H hH) ((N : Set G) * (H : Set G))ᶜ = 0 ∧
    (∀ t ∈ (N : Set G) * (H : Set G),
      (mulMeas (haarSub N hN) (haarSub H hH)).map (fun x => t * x) = mulMeas (haarSub N hN) (haarSub H hH)) ∧
    (∀ U : Set G, IsOpen U → (1 : G) ∈ U → 0 < mulMeas (haarSub N hN) (haarSub H hH) U) ∧
    (∀ C : Set G, IsCompact C → mulMeas (haarSub N hN) (haarSub H hH) C < ⊤)
def GenWeil : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μG μS : Measure G) [SFinite μG]
    [μG.IsMulLeftInvariant] [SFinite μS] (S : Set G), MeasurableSet S → μS Sᶜ = 0 →
    (∀ t ∈ S, μS.map (fun x => t * x) = μS) →
    (∀ U : Set G, IsOpen U → (1 : G) ∈ U → 0 < μS U) →
    (∀ C : Set G, IsCompact C → μS C < ⊤) →
    ∃ ν : Measure G, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν
def IsFrame (I : Formalism.MainNotions.S.AutInst) {r : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Prop :=
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) ∧
  (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) ∧
  Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0
def frameSet (I : Formalism.MainNotions.S.AutInst) {r : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) :
    Set (Fin I.n → I.E) :=
  Set.range e ∪ Set.range f ∪ {z}
def SubFacts : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    ∃ N H : Subgroup I.Ginf, (N : Set I.Ginf) = Ninf I e z ∧ (H : Set I.Ginf) = Hset I (frameSet I e f z) ∧
      IsClosed (N : Set I.Ginf) ∧ IsClosed (H : Set I.Ginf) ∧ ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N
def InstConj : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E), IsFrame I e f z →
    ∀ (N H : Subgroup I.Ginf) (hN : IsClosed (N : Set I.Ginf)), (N : Set I.Ginf) = Ninf I e z →
      (H : Set I.Ginf) = Hset I (frameSet I e f z) →
      ∀ h ∈ H, (haarSub N hN).map (fun x => h * x * h⁻¹) = haarSub N hN
def GenModOne : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (N H : Subgroup G)
    (hN : IsClosed (N : Set G)),
    (∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) →
    (∀ h ∈ H, ∃ k ∈ H, ∃ p ∈ H, ∃ σ ∈ H, h = k * p ∧ σ * p * σ⁻¹ = p⁻¹ ∧
      ∃ C : Set G, IsCompact C ∧ (1 : G) ∈ interior C ∧ ∀ x, k * x * k⁻¹ ∈ C ↔ x ∈ C) →
    ∀ h ∈ H, (haarSub N hN).map (fun x => h * x * h⁻¹) = haarSub N hN
def InstDecomp : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E), IsFrame I e f z →
    ∀ h ∈ Hset I (frameSet I e f z), ∃ k ∈ Hset I (frameSet I e f z), ∃ p ∈ Hset I (frameSet I e f z),
      ∃ σ ∈ Hset I (frameSet I e f z), h = k * p ∧ σ * p * σ⁻¹ = p⁻¹ ∧
      ∃ C : Set I.Ginf, IsCompact C ∧ (1 : I.Ginf) ∈ interior C ∧ ∀ x, k * x * k⁻¹ ∈ C ↔ x ∈ C
def InstProper : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E), IsFrame I e f z →
    ∀ (N H : Subgroup I.Ginf), (N : Set I.Ginf) = Ninf I e z → (H : Set I.Ginf) = Hset I (frameSet I e f z) →
      ∀ C : Set I.Ginf, IsCompact C → IsCompact {p : I.Ginf × I.Ginf | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C}
end PI.ScMuExists.UnitaryGroupMassFormula


