-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
-- name    : Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:29.601485+00:00
-- url     : https://prove2.me/theorems/93320ea7-dc89-45de-8b08-7a65a4654947
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/StatementB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_DetIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.LamCM
open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder
def KeyIntegral (R : Type) [CommRing R] {K' : Type} [Field K'] [Algebra R K'] (x : KeyIn K') (a d : K') : Prop :=
  ∃ (th' : x.P.L.Sec) (hth' : ∀ s : Sp K', ∃ y : x.P.A.left, x.P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th')
    (v' : Fin x.P.g → (epsR K' ⟶ x.P.A)) (hv' : IsLieBasis v') (M : Matrix (Fin x.P.g) (Fin x.P.g) K') (xR : KeyIn R),
    (∀ i, LB.Sec.f th' i = constFn x.P.A.hom _ a * LB.Sec.f x.th i) ∧ (∀ i, IsLieComb (M i) x.v (v' i)) ∧ M.det = d ∧
    KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', hth', v', hv'⟩ xR (algebraMap R K')
def KeyLocAt {K : Type} [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (p : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : CharZero K') (R : Type) (_ : CommRing R) (_ : IsDomain R)
    (_ : IsDiscreteValuationRing R) (_ : Algebra R K') (_ : IsFractionRing R K') (f : K →+* K') (x' : KeyIn K')
    (a d : K') (ca cd : K) (ua ud : Rˣ),
    KeyPB x' x f ∧ KeyIntegral R x' a d ∧
    (∀ y : K, f y ∈ Set.range (algebraMap R K') ↔ p.valuation K y ≤ 1) ∧
    a = f ca * algebraMap R K' ua ∧ d = f cd * algebraMap R K' ud ∧ IsLocGen p ca T.I ∧ IsLocGen p cd abelian₂.I
def KeyArchAt {K : Type} [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (σ : K →+* ℂ) : Prop :=
  ∃ (xσ : KeyIn ℂ) (u : HolUnif xσ.P.A xσ.P.L xσ.P.g) (Hm W : Matrix (Fin xσ.P.g) (Fin xσ.P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin xσ.P.g → ℂ) → ℂ) (Fd : Set (Fin xσ.P.g → ℂ)),
    KeyPB xσ x σ ∧ u.IsAH Hm χ ∧ u.IsRig xσ.rig ∧ u.IsFn xσ.th θ ∧ (∀ i, u.IsDiff (W i) (xσ.v i)) ∧
    IsAddFundamentalDomain u.Λ Fd volume ∧
    T.n σ ^ 2 = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal ∧
    abelian₂.n σ ^ 2 = Real.pi ^ xσ.P.g * ‖W.det‖ ^ 2 / (volume Fd).toReal
def KeyDeg : Prop :=
  KeyFormula → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K), T.Good → abelian₂.Good →
    (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) →
    T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi)
end Formalism.L2.LamCM


