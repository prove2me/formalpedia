-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
-- name    : Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:40.009456+00:00
-- url     : https://prove2.me/theorems/11245eaf-b593-49e3-9b9e-2fd1201f7a8a
-- title:
--   Key Rule One Of Key Formula
-- statement:
--   Definitions and structural lemmas for Key Rule One Of Key Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/KeyFormula/KeyRuleOneOfKeyFormula.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
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
noncomputable section
namespace GlobalTheory.KeyPow
def IsKeyPow {R : Type} [CommRing R] (y x : KeyIn R) (j : ℕ) : Prop :=
  ∃ (p : Out.IsPowPolAV y.P x.P j) (hg : j * x.P.g = y.P.g),
    (haveI := y.P.isAb.comm; haveI := x.P.isAb.comm;
      LB.Gen.Maps (LB.linCombIso p.w (K := PUnit) (fun _ => eSec y.P.A) (fun _ => 1)) y.rig
        (Out.boxRig p.toIsPowGrp x.P.L x.rig)) ∧
    (∀ (jj : Fin j → x.P.L.ι) (b : y.P.L.ι)
      (h : ∀ i, (Out.boxLB x.P.L p.pr).U jj ⊓ y.P.L.U b ≤ (p.pr i).left ⁻¹ᵁ x.P.L.U (jj i)),
      ∏ i, ((p.pr i).left.appLE _ _ (h i)).hom (x.th.f (jj i)) =
        (show Γ(y.P.A.left, (Out.boxLB x.P.L p.pr).U jj ⊓ y.P.L.U b) from (p.w.s (jj, b)).val) *
          resG _ inf_le_right (y.th.f b)) ∧
    ∀ (i i' : Fin j) (k : Fin x.P.g),
      y.v ((finProdFinEquiv (i, k)).cast hg) ≫ p.pr i' = if i = i' then x.v k else 1
def NormalAt (x : KeyIn ℂ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ) : Prop :=
  ∃ u : HolUnif x.P.A x.P.L x.P.g,
    τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
    (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
    u.IsRig x.rig ∧ u.IsFn x.th (fun z => c * thetaChar τ a b z) ∧
    ∀ i, u.IsDiff ((2 * Real.pi * Complex.I)⁻¹ • M i) (x.v i)
def ClauseH (R : Type) [CommRing R] (N : ℕ → ℕ) (g₀ : ℕ) (κ : KeyIn R → Rˣ) : Prop :=
  ∀ (P : Out.PolAV (Sp R)) (hg rig hr th hth v hv th' hth' v' hv') (a : R)
      (M : Matrix (Fin P.g) (Fin P.g) R), g₀ ≤ P.g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (M i) v (v' i)) →
      a ^ (8 * N P.g) * (κ ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : R) =
        M.det ^ (4 * N P.g) * κ ⟨P, hg, rig, hr, th, hth, v, hv⟩
def KeyRule (N : ℕ → ℕ) (g₀ : ℕ) (S : ∀ g : ℕ, (Fin g → ℂ) → (Fin g → ℂ) → Prop) : Prop :=
  ∃ κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ,
    (∀ (K : Type) [Field K] [CharZero K], ClauseH K N g₀ (κ K)) ∧
    (∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K') (x : KeyIn K) (x' : KeyIn K'),
      g₀ ≤ x.P.g → KeyPB x' x f → (κ K' x' : K') = f (κ K x)) ∧
    (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (x : KeyIn R) (xK : KeyIn K), g₀ ≤ x.P.g → KeyPB xK x (algebraMap R K) →
      ∃ u : Rˣ, (κ K xK : K) = algebraMap R K u ∧
        ∀ (k : Type) [Field k] [CharZero k] (r : R →+* k) (xk : KeyIn k), Function.Surjective r → KeyPB xk x r →
          (κ k xk : k) = r u) ∧
    ∀ (x : KeyIn ℂ) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ), g₀ ≤ x.P.g → S x.P.g a b →
      NormalAt x τ 1 a b 1 → κ ℂ x = 1
def charZero' (g : ℕ) (a b : Fin g → ℂ) : Prop := a = 0 ∧ b = 0
def charHalf (g : ℕ) (a b : Fin g → ℂ) : Prop := (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ ∀ i, b i = 0 ∨ b i = 1 / 2
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in

def ThetaLaw (g : ℕ) (sp : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (n n' k k' : Fin g → ℤ) : Prop :=
  ∃ c : ℂ, c ^ 4 = 1 ∧ ∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ,
    theta (halfVec k) (halfVec k') (zAct sp τ z) (spAct sp τ) ^ 2 =
      c * (jAut sp τ).det * eC (expArg sp τ z) * theta (halfVec n) (halfVec n') z τ ^ 2
example : charHalf 1 (fun _ => 1 / 2) (fun _ => 1 / 2) ∧ ¬ charZero' 1 (fun _ => 1 / 2) (fun _ => 1 / 2) :=
  ⟨⟨fun _ => Or.inr rfl, fun _ => Or.inr rfl⟩, fun h => by simpa using congrFun h.1 0⟩
end GlobalTheory.KeyPow
end


