-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
-- name    : Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:48.043912+00:00
-- url     : https://prove2.me/theorems/219fd2d1-b674-46c1-8285-fc29e76df295
-- title:
--   Ka Rule K
-- statement:
--   Definitions and structural lemmas for Ka Rule K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/KeyFormula/KaRuleK.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.KeyKa
open GlobalTheory.KeyPow
def KaRule (g c M : ℕ) : Prop :=
  ∃ ka : ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K], KeyIn K → Kˣ,
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (Mx : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (Mx i) v (v' i)) →
      a ^ (8 * c) * (ka K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = Mx.det ^ (4 * c) * ka K ⟨P, hg, rig, hr, th, hth, v, hv⟩) ∧
    (∀ (K K' : Type) [Field K] [CharZero K] [IsAlgClosed K] [Field K'] [CharZero K'] [IsAlgClosed K'] (f : K →+* K')
      (x : KeyIn K) (x' : KeyIn K'), x.P.g = g → KeyPB x' x f → (ka K' x' : K') = f (ka K x)) ∧
    (∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (x : KeyIn R), x.P.g = g → IsUnit (M : R) →
      ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (j : R →+* R') (u : R'ˣ),
        Function.Injective j ∧ IsLocalHom j ∧
        ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (f : R' →+* K) (xK : KeyIn K),
          KeyPB xK x (f.comp j) → (ka K xK : K) = f u) ∧
    ∀ a b : Fin g → ℂ, charHalf g a b → ∃ U : Matrix (Fin g) (Fin g) ℂ → ℂ, Key.IsHoloSiegel g U ∧
      ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 →
        (ka ℂ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm))
def KaSt : Prop := ∀ g p : ℕ, 1 ≤ g → p.Prime → ∃ c M : ℕ, 1 ≤ c ∧ 1 ≤ M ∧ ¬ p ∣ M ∧ KaRule g c M
def KeyDesc : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), ∃ (K₀ : Subfield K) (x₀ : KeyIn K₀), Countable K₀ ∧ KeyPB x x₀ K₀.subtype
def KaRuleK (g c M : ℕ) (ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ) : Prop :=
    (∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (Mx : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (Mx i) v (v' i)) →
      a ^ (8 * c) * (ka K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = Mx.det ^ (4 * c) * ka K ⟨P, hg, rig, hr, th, hth, v, hv⟩) ∧
    (∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K')
      (x : KeyIn K) (x' : KeyIn K'), x.P.g = g → KeyPB x' x f → (ka K' x' : K') = f (ka K x)) ∧
    (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (x : KeyIn R) (xK : KeyIn K), x.P.g = g → IsUnit (M : R) → KeyPB xK x (algebraMap R K) →
      ∃ u : Rˣ, (ka K xK : K) = algebraMap R K u ∧
        ∀ (k : Type) [Field k] [CharZero k] (r : R →+* k) (xk : KeyIn k), Function.Surjective r → KeyPB xk x r →
          (ka k xk : k) = r u) ∧
    ∀ a b : Fin g → ℂ, charHalf g a b → ∃ U : Matrix (Fin g) (Fin g) ℂ → ℂ, Key.IsHoloSiegel g U ∧
      ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 →
        (ka ℂ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm))
end GlobalTheory.KeyKa
end


