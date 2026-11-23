-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_HadamardLoc0
-- name    : Formalism_LocalToGlobal_CMDeterminantIdeals_HadamardLoc0
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:06:06.424807+00:00
-- url     : https://prove2.me/theorems/569c73d0-274f-41b9-ada2-e69a7244d6af
-- title:
--   Hadamard Loc0
-- statement:
--   Definitions and structural lemmas for Hadamard Loc0, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/HadamardLoc0.lean

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
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
def KeyCore : Prop :=
  ∃ κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ,
    (∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (M i) v (v' i)) →
      a ^ 8 * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ 4 * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩) ∧
    (∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K') (x : KeyIn K) (x' : KeyIn K'),
      KeyPB x' x f → (κ K' x' : K') = f (κ K x)) ∧
    (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (x : KeyIn R) (xK : KeyIn K), KeyPB xK x (algebraMap R K) →
      ∃ u : Rˣ, (κ K xK : K) = algebraMap R K u) ∧
    ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (nth nη : ℝ),
      u.IsAH Hm χ → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) →
      IsAddFundamentalDomain u.Λ Fd volume →
      nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal →
      nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2) →
      ‖(κ ℂ x : ℂ)‖ * nth ^ 4 * nη ^ 2 = (2 * Real.pi) ^ (2 * x.P.g)
def KeyCoreLink : Prop := KeyFormula → KeyCore
def KeyDegCore : Prop :=
  KeyCore → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K), T.Good → abelian₂.Good →
    (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) →
    T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi)
def UnimodVol : Prop :=
  ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (Λ : Submodule ℤ (Fin g → ℂ)) (Fd : Set (Fin g → ℂ))
    (Ef : LinearMap.BilinForm ℤ Λ), Hm.PosDef → DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    IsAddFundamentalDomain Λ Fd volume →
    (∀ a b : Λ, (Ef a b : ℝ) = ((a : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (b : Fin g → ℂ))).im) → Function.Bijective Ef →
    Hm.det.re * (volume Fd).toReal = 1
def lieGram {g : ℕ} (Hm W : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun i j => (Real.pi : ℂ) * (W j ⬝ᵥ Hm.mulVec (star (W i)))
def LieGramDet : Prop :=
  ∀ (g : ℕ) (Hm W : Matrix (Fin g) (Fin g) ℂ), Hm.PosDef → W.det ≠ 0 →
    (lieGram Hm W).PosDef ∧ (lieGram Hm W).det.re = Real.pi ^ g * ‖W.det‖ ^ 2 * Hm.det.re ∧
    ∀ x : Fin g → ℂ, ReciprocityTheory.MultiplicativeHeights.hq (lieGram Hm W) x =
      Real.pi * ((W.vecMul x) ⬝ᵥ Hm.mulVec (star (W.vecMul x))).re
def HadamardLoc0 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (U : Matrix (Fin g) (Fin g) K)
    (H : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (La : ℝ),
    abelian₂.I ≠ 0 → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 0 < La → (∀ σ, (H σ).PosDef) →
    (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) →
    (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧
      p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) →
    (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) →
    ∑ j, (ℓ j).deg - (g : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log La ≤ abelian₂.deg
def LamKey : Prop :=
  KeyCore → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (ℓ : Fin x.P.g → MLine K)
    (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (H : (K →+* ℂ) → Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (La logOm : ℝ)
    (V : Type) [Fintype V] (c : V → Fin x.P.g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ),
    T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) →
    (∀ j, (ℓ j).Good) → U.det ≠ 0 → 1 ≤ La → (∀ σ, (H σ).PosDef) → (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) →
    (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin x.P.g → K), IsLocGen p cd abelian₂.I ∧
      (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) →
    (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) →
    (∀ j, (ℓ j).ndeg = logOm / 2) →
    MvPolynomial.coeff μ G ≠ 0 → MvPolynomial.coeff μ G ∈ (lineNN T.dual ℓ c μ n).I → (∀ σ, 0 < S σ) → 0 < Rr →
    (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) →
      ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) →
    - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (x.P.g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤
      (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)
end Formalism.L2.LamCM


