-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:05.273398+00:00
-- url     : https://prove2.me/theorems/34e5f7f8-209c-4b66-a432-44f911480de6
-- title:
--   Restr Prod St
-- statement:
--   Definitions and structural lemmas for Restr Prod St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/RestrProdSt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMeas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
def RPAbs : Prop :=
  ∀ (ι : Type) [Countable ι] (W : ι → Type) [∀ i, MeasurableSpace (W i)]
    (m : ∀ i, Measure (W i)) [∀ i, SigmaFinite (m i)] (L : ∀ i, Set (W i)),
    (∀ i, MeasurableSet (L i)) → (∀ i, m i (L i) ≠ ⊤) →
    (∀ S : Finset ι, ∃ c : ENNReal, c ≠ ⊤ ∧ HasProd (fun i : {i // i ∉ S} => m i.1 (L i.1)) c) →
    ∃ ρ : Measure (∀ i, W i), SFinite ρ ∧
      ρ {x | ¬ ∀ᶠ i in Filter.cofinite, x i ∈ L i} = 0 ∧
      (∀ i (C : Set (W i)), MeasurableSet C → m i Cᶜ = 0 → ρ {x | x i ∉ C} = 0) ∧
      ∀ f : ∀ i, W i → ℂ, (∀ i, Integrable (f i) (m i)) →
        (∀ᶠ i in Filter.cofinite, f i = (L i).indicator 1) →
        Integrable (fun x => ∏ᶠ i, f i (x i)) ρ ∧
        HasProd (fun i => ∫ w, f i w ∂(m i)) (∫ x, ∏ᶠ i, f i (x i) ∂ρ)
def RPFib : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  (∀ (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a))
      (fib : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E)),
    IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib →
    SigmaFinite (fib (hermOf (Ainf F) σ (gramE σ J X0) hT)) ∧
    ∀ Φ : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
  ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a))
      (fib : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib →
    SigmaFinite (fib (hermOf (Fv F v) σ (gramE σ J X0) hT)) ∧
    ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf (Fv F v) σ (gramE σ J X0) hT))
def RPGlue : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (M a d : ℕ) (b : Module.Basis (Fin d) F E),
  ∃ Γ : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) →
      (Fin a → Fin M → AF F ⊗[F] E),
    Measurable Γ ∧ ∀ p, (∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v) →
      projInf (Γ p) = p.1 ∧ ∀ v, projV v (projFin (Γ p)) = p.2 v
def RPGram : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (T : Matrix (Fin a) (Fin a) E),
  MeasurableSet {X : Fin a → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X ≠ T.map (inclR (AF F))} ∧
  MeasurableSet {X : Fin a → Fin M → Ainf F ⊗[F] E |
    gramR (Ainf F) σ J X = T.map (inclR (Ainf F))} ∧
  (∀ v : HeightOneSpectrum (𝓞 F), MeasurableSet {X : Fin a → Fin M → Fv F v ⊗[F] E |
    gramR (Fv F v) σ J X = T.map (inclR (Fv F v))}) ∧
  ∀ X : Fin a → Fin M → AF F ⊗[F] E, gramR (Ainf F) σ J (projInf X) = T.map (inclR (Ainf F)) →
    (∀ v, gramR (Fv F v) σ J (projV v (projFin X)) = T.map (inclR (Fv F v))) →
    gramR (AF F) σ J X = T.map (inclR (AF F))
def RPTail : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a →
      Measure (Fin a → Fin M → Fv F v ⊗[F] E)) (d : ℕ) (b : Module.Basis (Fin d) F E),
    (∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ →
      Integrable Φ (fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) →
    (∀ (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))) →
    (∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ →
      ∫ X, Φ X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) = 0) ∨
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ENNReal, c ≠ ⊤ ∧
      HasProd (fun v : {v // v ∉ S} =>
        fibV v.1 (hermOf (Fv F v.1) σ (gramE σ J X0) hT) (latV b v.1)) c
def LatCofin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a M d d' : ℕ)
    (b : Module.Basis (Fin d) F E) (b' : Module.Basis (Fin d') F E),
    ∀ᶠ v in Filter.cofinite, latV (M := M) (n := a) b v = latV b' v
end PI.VolStabW


