-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:42.37711+00:00
-- url     : https://prove2.me/theorems/fd0e9f3e-5f1c-4224-8df7-aba335188fc2
-- title:
--   Exists Unique Hchar Of Finite Order
-- statement:
--   Definitions and structural lemmas for Exists Unique Hchar Of Finite Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
namespace GlobalTheory.HeckeGal
section Defs
variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
abbrev Gab : Type := TopologicalAbelianization (G E Ω)
def toAb : G E Ω →* Gab E Ω := QuotientGroup.mk' _
def infConn : Subgroup (Ideles E) :=
  (Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ).map
    (Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)))
variable {E Ω}
structure IsGlobalArtin (art : Ideles E →* Gab E Ω) : Prop where

  quot : IsOpenQuotientMap art

  ker : art.ker = ((diagUnits E).range ⊔ infConn E).topologicalClosure

  ine : ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ g : Gab E Ω,
    (∃ x, IsUnitAt v x ∧ art (localIdele E v x) = g) ↔ ∃ σ ∈ Ine (F := E) A, toAb E Ω σ = g

  frob : ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ g : Gab E Ω,
    (∃ x, IsUnifAt v x ∧ art (localIdele E v x) = g) ↔
      ∃ σ : G E Ω, IsFrob (F := E) A (normV v) σ ∧ toAb E Ω σ⁻¹ = g

  dec : ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v →
    (art.comp (localIdele E v)).range.topologicalClosure = (Dec (F := E) A).map (toAb E Ω)
def IsAlgPos (χ : HChar E) (n : (E →+* ℂ) → ℤ) : Prop :=
  ∀ k : Eˣ, (∀ φ : E →+* ℝ, 0 < φ (k : E)) → ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, φ (k : E) ^ n φ
def infPow (n : (E →+* ℂ) → ℤ) (x : Ideles E) : ℂ :=
  ∏ w : InfinitePlace E, ∏ᶠ i : {i : w.Completion →+* ℂ // Continuous i},
    i.1 ((x : AdeleRing (𝓞 E) E).1 w) ^ n (i.1.comp (algebraMap E w.Completion))
variable {l : ℕ} [Fact l.Prime]
def locPow (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (v : HeightOneSpectrum (𝓞 E)) (y : v.adicCompletion E) : Qbar l :=
  ∏ᶠ j : {j : v.adicCompletion E →+* Qbar l // Continuous j},
    j.1 y ^ n ((ι.toRingHom.comp j.1).comp (algebraMap E (v.adicCompletion E)))
def lPow (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (x : Ideles E) : Qbar l :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 E), locPow ι n v ((x : AdeleRing (𝓞 E) E).2 v)
def IsLAdicOf (art : Ideles E →* Gab E Ω) (ι : Qbar l ≃+* ℂ) (χ : HChar E) (n : (E →+* ℂ) → ℤ)
    (r : G E Ω →* (Qbar l)ˣ) : Prop :=
  ∀ (x : Ideles E) (σ : G E Ω), art x = toAb E Ω σ →
    ((r σ : (Qbar l)ˣ) : Qbar l) = ι.symm (((χ.1 x : ℂˣ) : ℂ) * (infPow n x)⁻¹) * lPow ι n x
end Defs
end GlobalTheory.HeckeGal
namespace GlobalTheory.Published
open GlobalTheory.HeckeGal
def GlobalArtinReciprocity : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    ∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art
def HeckeLAdicCharacter : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    ∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art ∧
      ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (χ : HChar E) (n : (E →+* ℂ) → ℤ), IsAlgPos χ n →
        ∃! r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ IsLAdicOf art ι χ n r
end GlobalTheory.Published
namespace GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
theorem locPow_one (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (v : HeightOneSpectrum (𝓞 E)) :
    locPow ι n v 1 = 1 := by
  simp [locPow]
theorem infPow_localIdele (n : (E →+* ℂ) → ℤ) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    infPow n (localIdele E v x) = 1 := by
  refine Finset.prod_eq_one fun w _ => ?_
  have : ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).1 w = 1 := rfl
  simp [this]
theorem lPow_localIdele (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (v : HeightOneSpectrum (𝓞 E))
    (x : (v.adicCompletion E)ˣ) : lPow ι n (localIdele E v x) = locPow ι n v x := by
  classical
  unfold lPow
  rw [finprod_eq_single _ v]
  · congr 1
    exact Function.update_self v (x : v.adicCompletion E) (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E))
  · intro w hw
    have : ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 :=
      Function.update_of_ne hw (x : v.adicCompletion E) (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E))
    rw [this, locPow_one]
section Local
variable {art : Ideles E →* Gab E Ω} {ι : Qbar l ≃+* ℂ} {χ : HChar E} {n : (E →+* ℂ) → ℤ}
  {r : G E Ω →* (Qbar l)ˣ} {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
theorem IsLAdicOf.loc (h : IsLAdicOf art ι χ n r) (x : (v.adicCompletion E)ˣ) (σ : G E Ω)
    (hx : art (localIdele E v x) = toAb E Ω σ) :
    ((r σ : (Qbar l)ˣ) : Qbar l) = ι.symm ((χ.loc v x : ℂˣ) : ℂ) * locPow ι n v x := by
  rw [h _ σ hx, infPow_localIdele, inv_one, mul_one, lPow_localIdele]
  rfl
end Local
def liftAb {B : Type} [CommGroup B] [TopologicalSpace B] [T1Space B] (φ : G E Ω →* B) (hφ : Continuous φ) :
    Gab E Ω →* B :=
  QuotientGroup.lift _ φ fun _ hσ =>
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker φ)
      (isClosed_singleton.preimage hφ) hσ
end GlobalTheory.HeckeGal
namespace GlobalTheory.Published
open GlobalTheory.HeckeGal
end GlobalTheory.Published
end


