-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:55.864835+00:00
-- url     : https://prove2.me/theorems/0728fd59-5b17-4848-a37b-7905eb03dfa0
-- title:
--   Hodge IPIff Hodge Form Conj
-- statement:
--   Definitions and structural lemmas for Hodge IPIff Hodge Form Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/HodgeIPIffHodgeFormConj.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
def HodgeForm (G : Over X) [GrpObj G] (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ G)
    (c : ℂ) : Prop :=
  L.IsLB ∧ IsTanAt G z v ∧ IsTanAt G z w ∧
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ G.left) (g : ℕ) (u : HolUnif A (L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (v' w' : epsR ℂ ⟶ A) (a b : Fin g → ℂ),
    IsGrpPullback A G z φ ∧ u.IsAH Hm χ ∧ v'.left ≫ φ = v.left ∧ w'.left ≫ φ = w.left ∧
      u.IsDiff a v' ∧ u.IsDiff b w' ∧ c = Real.pi * hermForm Hm a b
def HodgeIP (G : Over X) [GrpObj G] (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ G)
    (c : ℂ) : Prop :=
  L.IsLB ∧ IsTanAt G z v ∧ IsTanAt G z w ∧
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ G.left) (g : ℕ) (u : HolUnif A (L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (v' w' : epsR ℂ ⟶ A) (a b : Fin g → ℂ),
    IsGrpPullback A G z φ ∧ u.IsAH Hm χ ∧ v'.left ≫ φ = v.left ∧ w'.left ≫ φ = w.left ∧
      u.IsDiff a v' ∧ u.IsDiff b w' ∧ c = Real.pi * (b ⬝ᵥ Hm.mulVec (star a))
def LieModel.GramAt (M : LieModel G ξ E) (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) {r : ℕ}
    (b : Fin r → E) (Γ : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∃ v : Fin r → (epsAt z ⟶ G), (∀ i, M.ValAt z (b i) (v i)) ∧ ∀ p q, HodgeIP G L z (v p) (v q) (Γ p q)
def LieModel.FormGramAt (M : LieModel G ξ E) (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) {r : ℕ}
    (b : Fin r → E) (Γ : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∃ v : Fin r → (epsAt z ⟶ G), (∀ i, M.ValAt z (b i) (v i)) ∧ ∀ p q, HodgeForm G L z (v p) (v q) (Γ p q)
def leadMinor {r : ℕ} (Γ : Matrix (Fin r) (Fin r) ℂ) (s : ℕ) : ℝ :=
  if h : s ≤ r then (Γ.submatrix (Fin.castLE h) (Fin.castLE h)).det.re else 0
def LieModel.IsGrNorm (M : LieModel G ξ E) (L : LB G.left) (V : Lat ξ E) {r : ℕ} (b₀ : Fin r → E) (i : Fin r)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (t : Ω) (ν : ℝ) : Prop :=
  ∃ (h : genPt ξ ⤳ centre z) (b : Fin r → E) (Γ : Matrix (Fin r) (Fin r) ℂ),
    (∀ s, flagStep Ω b s = flagStep Ω b₀ s) ∧ V.IsFrameAt b ⟨centre z, h⟩ ∧ b i - t • b₀ i ∈ flagStep Ω b₀ i ∧
      M.GramAt L z b Γ ∧ Γ.PosDef ∧ ν = Real.sqrt (leadMinor Γ (i + 1) / leadMinor Γ i)
def SecNorm (ξ : Spec (CommRingCat.of Ω) ⟶ X) {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (A : HermLine J) (e₀ : Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ)
    (t : Ω) (ν : ℝ) : Prop :=
  e₀ ≠ 0 ∧ CoordsAt ξ y z w ∧
  ∀ c : (k : K) → J k, (∀ k, w ⟨k, c k⟩ ≠ 0) → ∃ u : ℂ, ValAt ξ z (t / ((∏ k, y ⟨k, c k⟩ ^ A.a k) * e₀)) u ∧
    ν * A.h w = ‖u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ A.a k
section Form
variable {L : LB G.left} {z : Spec (CommRingCat.of ℂ) ⟶ X} {v w : epsAt z ⟶ G} {c : ℂ}
end Form
section Minor
variable {r : ℕ} {Γ : Matrix (Fin r) (Fin r) ℂ}
theorem leadMinor_size_one (Γ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : leadMinor Γ 1 = (Γ 0 0).re := by
  simp [leadMinor]
example (a d : ℝ) (ha : a ≠ 0) (b : ℂ) :
    leadMinor !![(a : ℂ), b; (starRingEnd ℂ) b, d] 2 / leadMinor !![(a : ℂ), b; (starRingEnd ℂ) b, d] 1 =
      d - Complex.normSq b / a := by
  rw [leadMinor_size_one]
  simp [leadMinor, Matrix.det_fin_two, Complex.normSq_apply]
  field_simp
example {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (p q : Fin g) :
    hermForm Hm (Pi.single p 1) (Pi.single q 1) = Hm p q := by
  simp [hermForm, ← Pi.single_star]
end Minor
section Gr
variable {M : LieModel G ξ E} {L : LB G.left} {V : Lat ξ E} {r : ℕ} {b₀ : Fin r → E} {i : Fin r}
  {z : Spec (CommRingCat.of ℂ) ⟶ X} {t : Ω} {ν : ℝ}
end Gr
section Sec
variable {z : Spec (CommRingCat.of ℂ) ⟶ X}
namespace CxVal
theorem mul {a b : Ω} {r s : ℂ} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨_, y, rfl, rfl⟩ := h'
  exact ⟨h, x * y, map_mul _ _ _, map_mul _ _ _⟩
theorem aeval {σ : Type} {a : σ → Ω} {r : σ → ℂ} (hz : genPt ξ ⤳ centre z) (h : ∀ p, ValAt ξ z (a p) (r p))
    (s : MvPolynomial σ ℤ) : ValAt ξ z (MvPolynomial.aeval a s) (MvPolynomial.aeval r s) := by
  induction s using MvPolynomial.induction_on with
  | C n => exact ⟨hz, n, by simp, (map_intCast (Scheme.stalkClosedPointTo z).hom n).trans (by simp)⟩
  | add p q hp hq =>
    obtain ⟨_, x, hx, hx'⟩ := hp
    obtain ⟨_, y, hy, hy'⟩ := hq
    exact ⟨hz, x + y, by rw [map_add, map_add, hx, hy],
      (map_add (Scheme.stalkClosedPointTo z).hom x y).trans (by rw [map_add, ← hx', ← hy']; rfl)⟩
  | mul_X p i hp => simpa using mul hp (h i)
end CxVal
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {A : HermLine J} {e₀ : Ω}
  {w : (Σ k, J k) → ℂ} {t : Ω} {ν ν' : ℝ}
theorem SecNorm.exists_chart (h : SecNorm ξ y A e₀ z w t ν) : ∃ c : (k : K) → J k, ∀ k, w ⟨k, c k⟩ ≠ 0 := by
  choose c hc using h.2.1.1
  exact ⟨c, fun k => (hc k).ne_zero⟩
example (k : K) (hk : ∀ i, w ⟨k, i⟩ = 0) : ¬ SecNorm ξ y A e₀ z w t ν ∧ ¬ SecNorm ξ y A 0 z w t ν :=
  ⟨fun h => let ⟨c, hc⟩ := h.exists_chart; hc k (hk (c k)), fun h => h.1 rfl⟩
end Sec
end GlobalTheory.CompanionTheory.Ar


