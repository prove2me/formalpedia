-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ConjugateHermitianLineIsometries
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ConjugateHermitianLineIsometries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:38:37.021837+00:00
-- url     : https://prove2.me/theorems/45ade906-744d-4817-8688-b2ef4a4b3e35
-- title:
--   Conjugate Hermitian Line Isometries
-- statement:
--   Definitions and structural lemmas for Conjugate Hermitian Line Isometries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ConjugateHermitianLineIsometries.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def evC (z : (Σ k, ι k) → ℂ) (f : MRing ι) : ℂ := eval z (map (Int.castRingHom ℂ) f)
def conjPt (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun p => starRingEnd ℂ (z p)
def conjLine (A : HermLine ι) : HermLine ι where
  a := A.a
  h z := A.h (conjPt z)
  pos z hz := A.pos _ fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact ⟨i, by simpa [conjPt] using hi⟩
  smul c z hc := by
    have h := A.smul (fun k => starRingEnd ℂ (c k)) (conjPt z) (fun k => by simpa using hc k)
    have e : conjPt (fun p => c p.1 * z p) = fun p => starRingEnd ℂ (c p.1) * conjPt z p := by
      funext p
      simp [conjPt]
    rw [e, h]
    simp
def UnitRatio (P : Ideal (MRing ι)) (f g : MRing ι) : Prop :=
  f ∉ P ∧ g ∉ P ∧ ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
    ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P
def IsLineIso (P : Ideal (MRing ι)) (a b : K → ℤ) (f g : MRing ι) : Prop :=
  (∃ α γ : K → ℕ, IsMultiHomog f α ∧ IsMultiHomog g γ ∧ ∀ k, (α k : ℤ) - γ k = a k - b k) ∧ UnitRatio P f g
def IsDefectOn (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)) (f g : MRing ι) (A B : HermLine ι)
    (w : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∀ z ∈ Xo, ∀ u v : MRing ι, u * f - v * g ∈ P → evC z u ≠ 0 →
    w z = Real.log (‖evC z v‖ / ‖evC z u‖ * B.h z / A.h z)
def IsoLineOn (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)) (A B : HermLine ι) : Prop :=
  ∃ f g : MRing ι, IsLineIso P A.a B.a f g ∧ IsDefectOn P Xo f g A B fun _ => 0
section Join
variable {K₁ K₂ : Type} (ι₁ : K₁ → Type) (ι₂ : K₂ → Type)
def joinIdx : K₁ ⊕ K₂ → Type := Sum.elim ι₁ ι₂
instance instFintypeJoinIdx [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] : ∀ k, Fintype (joinIdx ι₁ ι₂ k)
  | Sum.inl k => inferInstanceAs (Fintype (ι₁ k))
  | Sum.inr k => inferInstanceAs (Fintype (ι₂ k))
def joinInl : (Σ k, ι₁ k) → Σ k, joinIdx ι₁ ι₂ k := fun p => ⟨Sum.inl p.1, p.2⟩
def joinInr : (Σ k, ι₂ k) → Σ k, joinIdx ι₁ ι₂ k := fun p => ⟨Sum.inr p.1, p.2⟩
variable {ι₁ ι₂}
def joinVec {Ω : Type} (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) : (Σ k, joinIdx ι₁ ι₂ k) → Ω
  | ⟨Sum.inl k, i⟩ => y₁ ⟨k, i⟩
  | ⟨Sum.inr k, i⟩ => y₂ ⟨k, i⟩
end Join
def numOn (II : IntersectionSystem) {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (d : ℕ)
    (L : Fin d → HermLine ι) : ℝ :=
  (Module.finrank (blockFnField y) Ω : ℝ) * II K ι (mCoordIdeal y) d L
end GlobalTheory.CompanionTheory.Ar.Cmp


