-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRootOfKeyFormula
-- name    : Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRootOfKeyFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:43.468285+00:00
-- url     : https://prove2.me/theorems/8d5d59c4-2baa-4dfb-9596-d19373ff2f63
-- title:
--   Key Root Of Key Formula
-- statement:
--   Definitions and structural lemmas for Key Root Of Key Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/KeyFormula/KeyRootOfKeyFormula.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KeyCl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
abbrev Rule : Type 1 := ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ
def Homog (N : ℕ → ℕ) (κ : Rule) : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
    (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
    (∀ i, IsLieComb (M i) v (v' i)) →
    a ^ (8 * N P.g) * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) =
      M.det ^ (4 * N P.g) * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩
def Funct (κ : Rule) : Prop :=
  ∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K') (x : KeyIn K) (x' : KeyIn K'),
    KeyPB x' x f → (κ K' x' : K') = f (κ K x)
def UnitSp (κ : Rule) : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
    [IsFractionRing R K] (x : KeyIn R) (xK : KeyIn K), KeyPB xK x (algebraMap R K) →
    ∃ u : Rˣ, (κ K xK : K) = algebraMap R K u ∧
      ∀ (k : Type) [Field k] [CharZero k] (r : R →+* k) (xk : KeyIn k), Function.Surjective r → KeyPB xk x r →
        (κ k xk : k) = r u
def ThetaOne (κ : Rule) : Prop :=
  ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) →
    (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    u.IsRig x.rig → u.IsFn x.th (thetaChar τ a b) →
    (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i)) → κ ℂ x = 1
def ArchNorm (N : ℕ → ℕ) (κ : Rule) : Prop :=
  ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (nth nη : ℝ),
    u.IsAH Hm χ → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) →
    IsAddFundamentalDomain u.Λ Fd volume →
    nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal →
    nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2) →
    ‖(κ ℂ x : ℂ)‖ * nth ^ (4 * N x.P.g) * nη ^ (2 * N x.P.g) = (2 * Real.pi) ^ (2 * x.P.g * N x.P.g)
def IsValue (κ : Rule) {S : Type} [CommRing S] (y : KeyIn S) (u : S) : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f : S →+* K) (x : KeyIn K), KeyPB x y f → (κ K x : K) = f u
def FamUnit (κ : Rule) : Prop :=
  ∀ (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [CharZero S] (y : KeyIn S),
    ∃ u : Sˣ, IsValue κ y (u : S)
def FamHomog (N : ℕ → ℕ) (κ : Rule) : Prop :=
  ∀ (S : Type) [CommRing S] [IsDomain S] [CharZero S] (P : Out.PolAV (Sp S)) (hg rig hr th hth v hv th' hth' v' hv') (a : S)
    (M : Matrix (Fin P.g) (Fin P.g) S) (u u' : S), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
    (∀ i, IsLieComb (M i) v (v' i)) →
    IsValue κ ⟨P, hg, rig, hr, th, hth, v, hv⟩ u → IsValue κ ⟨P, hg, rig, hr, th', hth', v', hv'⟩ u' →
    a ^ (8 * N P.g) * u' = M.det ^ (4 * N P.g) * u
def ValUnit (κ : Rule) : Prop :=
  ∀ (S V K : Type) [CommRing S] [IsNoetherianRing S] [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field K] [CharZero K]
    [Algebra V K] [IsFractionRing V K] (g : S →+* V) (y : KeyIn S) (x : KeyIn K),
    KeyPB x y ((algebraMap V K).comp g) → ∃ u : Vˣ, (κ K x : K) = algebraMap V K u
def KeyRoot : Prop := ∃ κ : Rule, Homog (fun _ => 1) κ ∧ Funct κ ∧ UnitSp κ ∧ ArchNorm (fun _ => 1) κ
def KeyFam (N : ℕ → ℕ) : Prop :=
  ∃ κ : Rule, Homog N κ ∧ Funct κ ∧ UnitSp κ ∧ ThetaOne κ ∧ ArchNorm N κ ∧ FamUnit κ ∧ FamHomog N κ ∧ ValUnit κ
end GlobalTheory.KeyCl


