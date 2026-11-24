-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:21.088803+00:00
-- url     : https://prove2.me/theorems/be7b0fda-2e89-4b72-bfa4-43d3fd2f29b3
-- title:
--   Inter Res
-- statement:
--   Definitions and structural lemmas for Inter Res, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRes.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def SameOrbit (z z' : (Σ k, ι k) → ℂ) : Prop :=
  ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = fun p => c p.1 * z' p
def affCoord (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => z q / z ⟨q.1, p q.1⟩
structure AnLogRes (P J : Ideal (MRing ι)) (e : ℕ) where

  homog : IsMultiHomogIdeal J

  nondeg : ¬ J ≤ P

  X : Type
  [top : TopologicalSpace X]
  [compact : CompactSpace X]
  [t2 : T2Space X]

  A : FinHolAtlas e X

  U : X → Set X
  isOpen_U : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x

  lift : X → X → (Σ k, ι k) → ℂ
  holo : ∀ x p, A.HoloOn (U x) (fun y => lift x y p)
  mem : ∀ x, ∀ y ∈ U x, lift x y ∈ mcPts P

  compat : ∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lift x y) (lift x' y)

  surj : ∀ z ∈ mcPts P, z ∉ mcPts J → ∃ x, SameOrbit (lift x x) z

  inj : ∀ x x', lift x x ∉ mcPts J → SameOrbit (lift x x) (lift x' x') → x = x'

  immersion : ∀ x, lift x x ∉ mcPts J → ∀ p : (k : K) → ι k, (∀ k, lift x x ⟨k, p k⟩ ≠ 0) →
    ∀ j, x ∈ (A.chart j).source →
      (fderiv ℂ (fun y => affCoord p (lift x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥

  snc : ∀ (f : MRing ι) (a : K → ℕ), f ∉ P → IsMultiHomog f a →
    (∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) f) = 0 → z ∈ mcPts J) →
    ∃ (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set X),
      IsSNC A ⟨U, isOpen_U, mem_U, fun _ _ => 0⟩
        (fun x y => eval (lift x y) (map (Int.castRingHom ℂ) f)) m W

  null : ∀ j, MeasureTheory.volume
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' {x | lift x x ∈ mcPts J}) = 0
attribute [instance] AnLogRes.top AnLogRes.compact AnLogRes.t2
def potOf {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (L : HermLine ι) : LocPot R.X where
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  φ x y := Real.log (L.h (R.lift x y))
def ResExistsStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ P →
    ∃ J' : Ideal (MRing ι), J' ≤ J ∧ IsMultiHomogIdeal J' ∧ ¬ J' ≤ P ∧ Nonempty (AnLogRes P J' e)
def ResBridgeStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ)
    (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    ptsIntegralAt P Ψ (pot L) (logNorm A s) =
      mInt R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x))
def ResInhabitStatement : Prop :=
  Nonempty (AnLogRes (⊥ : Ideal (MRing (PBlk 2))) (Ideal.span {Xc 2 0}) 1)
end ReciprocityTheory.ChartRestriction.G.Geo


