-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Birational
-- name    : Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Birational
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:32.545896+00:00
-- url     : https://prove2.me/theorems/11fbc0ea-913a-46ce-8df2-bb30f4d8e0d9
-- title:
--   Birational
-- statement:
--   Definitions and structural lemmas for Birational, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/DivisibilityTowers/Birational.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_CompactGapsGE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
namespace GlobalTheory.CompanionTheory.Ar.Top
structure RootModel (Ψ : Type) [Fintype Ψ] (N : ℕ) where

  K : Type
  [finK : Fintype K]

  ι : K → Type
  [finι : ∀ k, Fintype (ι k)]

  Ω : Type
  [fieldΩ : Field Ω]

  y : (Σ k, ι k) → Ω
  arith : IsArithVar (mCoordIdeal y) (dimFl Ψ N + 1)
  birational : Birational y

  xdeg : Ψ × Fin N → K → ℤ

  x : ℝ → Ψ × Fin N → HermLine ι
  x_deg : ∀ t r, (x t r).a = xdeg r
  x_smooth : ∀ t r, IsSmoothHerm (x t r)
  x_conj : ∀ t r, IsConjInvariantH (x t r)

  kA : ℕ
  kA_pos : 0 < kA

  A : HermLine ι
  A_smooth : IsSmoothHerm A
  A_conj : IsConjInvariantH A

  δ : ℕ
  δ_pos : 0 < δ
attribute [instance] RootModel.finK RootModel.finι RootModel.fieldΩ
def trivLine {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι where
  a := 0
  h _ := 1
  pos _ _ := one_pos
  smul _ _ _ := by simp
def monoLines {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} (ℓ : J → HermLine ι)
    (m : J →₀ ℕ) (d : ℕ) : Fin d → HermLine ι := fun k =>
  if h : (k : ℕ) < (Finsupp.toMultiset m).toList.length then ℓ ((Finsupp.toMultiset m).toList.get ⟨k, h⟩)
  else trivLine ι
def combLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) : HermLine ι where
  a := ∑ j, n j • (ℓ j).a
  h z := ∏ j, (ℓ j).h z ^ n j
  pos z hz := Finset.prod_pos fun j _ => zpow_pos ((ℓ j).pos z hz) _
  smul c z hc := by
    have h1 : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have h2 : ∀ k, ‖c k‖ ^ (∑ j, n j • (ℓ j).a) k = ∏ j, (‖c k‖ ^ (ℓ j).a k) ^ n j := by
      intro k
      rw [Finset.sum_apply]
      classical
      induction (Finset.univ : Finset J) using Finset.induction_on with
      | empty => simp
      | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add₀ (h1 k), ih, ← zpow_mul]
        simp [mul_comm]
    simp only [(ℓ _).smul c z hc, mul_zpow, Finset.prod_mul_distrib, h2]
    rw [Finset.prod_comm]
    simp only [Finset.prod_zpow]
namespace RootModel
variable {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N)
def P : Ideal (MRing M.ι) := mCoordIdeal M.y
def line (t : ℝ) : Option (Ψ × Fin N) → HermLine M.ι
  | some r => M.x t r
  | none => M.A
def coef (lam : Wt Ψ N) (s : ℝ) : Option (Ψ × Fin N) → ℝ
  | some r => -lam r.1 r.2
  | none => s / M.kA
def arMono (II : IntersectionSystem) (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) : ℝ :=
  if m.degree = dimFl Ψ N + 1 then
    II M.K M.ι M.P (dimFl Ψ N + 1) (monoLines (M.line t) m (dimFl Ψ N + 1)) / ((M.δ : ℝ) * (M.kA : ℝ) ^ m none)
  else 0
def arFun (II : IntersectionSystem) (t : ℝ) : RPA Ψ N →ₗ[ℝ] ℝ :=
  (basisMonomials (Option (Ψ × Fin N)) ℝ).constr ℝ (M.arMono II t)
def Converges (II : IntersectionSystem) : Prop :=
  ∀ m, ∃ L, Tendsto (fun t => M.arMono II t m) (𝓝[>] 0) (𝓝 L)
def PP (II : IntersectionSystem) : RPA Ψ N →ₗ[ℝ] ℝ :=
  (basisMonomials (Option (Ψ × Fin N)) ℝ).constr ℝ fun m => limUnder (𝓝[>] 0) fun t => M.arMono II t m
def geoMono (m : Option (Ψ × Fin N) →₀ ℕ) : ℝ :=
  if m.degree = dimFl Ψ N then
    ptsIntegral (e := dimFl Ψ N) M.P (fun k z => Real.log ((monoLines (M.line 1) m (dimFl Ψ N) k).h z)) (fun _ => 1) /
      ((M.δ : ℝ) * (M.kA : ℝ) ^ m none)
  else 0
def geoFun : RPA Ψ N →ₗ[ℝ] ℝ := (basisMonomials (Option (Ψ × Fin N)) ℝ).constr ℝ M.geoMono
def ht (II : IntersectionSystem) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (W : Ideal (MRing M.ι)) : ℝ :=
  (∑ j, M.coef lam s j * II M.K M.ι W 1 ![M.line t j]) / (degC W : ℝ)
def IsPt (W : Ideal (MRing M.ι)) : Prop := IsArithVar W 1 ∧ M.P ≤ W
def IsCurveAt (p : ℕ) (W : Ideal (MRing M.ι)) : Prop :=
  IsMultiProjPrime W ∧ M.P ≤ W ∧ charOf W = p ∧
    ringKrullDim (MRing M.ι ⧸ W) = ((1 + Fintype.card M.K : ℕ) : WithBot ℕ∞)
def curveDeg (lam : Wt Ψ N) (s : ℝ) (W : Ideal (MRing M.ι)) : ℝ :=
  ∑ j, M.coef lam s j * (geoNum 1 W (fun _ => (M.line 1 j).a) : ℝ)
def NefAt (p : ℕ) (lam : Wt Ψ N) (s : ℝ) : Prop := ∀ W, M.IsCurveAt p W → 0 ≤ M.curveDeg lam s W
def NefFib (lam : Wt Ψ N) (s : ℝ) : Prop := ∀ p : ℕ, p.Prime → M.NefAt p lam s
def NefGen (lam : Wt Ψ N) (s : ℝ) : Prop :=
  ∀ W : Ideal (MRing M.ι), IsArithVar W 2 → M.P ≤ W → 0 ≤ ∑ j, M.coef lam s j * geomDeg W (M.line 1 j) 1
def weight (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (z : (Σ k, M.ι k) → ℂ) : ℝ :=
  ∑ j, M.coef lam s j * Real.log ((M.line t j).h z)
def Semipos (t : ℝ) (lam : Wt Ψ N) (s : ℝ) : Prop :=
  ∀ z ∈ mcPts M.P, ∀ w, IsConeTangent (Int.castRingHom ℂ) M.P z w → 0 ≤ leviForm (M.weight t lam s) z w
def EffDiff (nu : Wt Ψ N) : Prop :=
  ∃ (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), 0 < q ∧ (∀ j, (n j : ℝ) = q * M.coef nu (-1) j) ∧
    ∃ s : M.Ω, s ≠ 0 ∧ s ∈ chartLatNm M.y (combLine (M.line 1) n).a 1
end RootModel
end GlobalTheory.CompanionTheory.Ar.Top


