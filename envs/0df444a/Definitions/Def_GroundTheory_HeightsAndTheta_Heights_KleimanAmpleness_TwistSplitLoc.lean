-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitLoc
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitLoc
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:29:14.012334+00:00
-- url     : https://prove2.me/theorems/4bff2d64-cc61-49b8-8727-5b532fe57ed8
-- title:
--   Twist Split Loc
-- statement:
--   Definitions and structural lemmas for Twist Split Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Pointwise AddMonoidAlgebra
noncomputable section
universe u w
section Loc
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)
theorem eval_ne_zero_of_subset {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) {s : Poly S N}
    (hs : s ∈ monos I) : aeval x s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [aeval_X]
    exact (mem_support x).mp (hI hi)
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_ne_zero ha hb
theorem xyHom_of_mem_monos {I : Finset (Fin (N + 1))} {s : Poly (MvPolynomial (Fin (r + 1)) S) N}
    (hs : s ∈ monos I) : ∃ s₀ ∈ monos (S := S) I, ∃ e : ℕ, s₀.IsHomogeneous e ∧
      s = MvPolynomial.map (C : S →+* MvPolynomial (Fin (r + 1)) S) s₀ ∧
      xyHom S x η s = single ((0 : ℤ), (e : ℤ)) (aeval x s₀) := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨X i, X_mem_monos hi, 1, isHomogeneous_X S i, (map_X _ _).symm,
      by rw [xyHom_X, aeval_X, Nat.cast_one]⟩
  | one =>
    exact ⟨1, one_mem _, 0, isHomogeneous_one _ _, (map_one _).symm,
      by rw [map_one, map_one, AddMonoidAlgebra.one_def]; rfl⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a₀, ha₀, ea, hae, rfl, hxa⟩ := ha
    obtain ⟨b₀, hb₀, eb, hbe, rfl, hxb⟩ := hb
    refine ⟨a₀ * b₀, mul_mem ha₀ hb₀, ea + eb, hae.mul hbe, (map_mul _ _ _).symm, ?_⟩
    rw [map_mul, hxa, hxb, single_mul_single, map_mul]
    congr 1
theorem isUnit_xyHom {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    {s : Poly (MvPolynomial (Fin (r + 1)) S) N} (hs : s ∈ monos I) : IsUnit (xyHom S x η s) := by
  obtain ⟨s₀, hs₀, e, -, -, h⟩ := xyHom_of_mem_monos η hs
  rw [h]
  have hv := eval_ne_zero_of_subset hI hs₀
  refine isUnit_iff_exists_inv.mpr ⟨single ((0 : ℤ), -(e : ℤ)) (aeval x s₀)⁻¹, ?_⟩
  rw [single_mul_single, mul_inv_cancel₀ hv, AddMonoidAlgebra.one_def]
  congr 1
  ext <;> simp
variable (M₀ : FinGradedSub (S := S) (x := x) Ω)
theorem locEmb_isUnit {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    (s : monos (S := MvPolynomial (Fin (r + 1)) S) I) :
    IsUnit (algebraMap (Poly (MvPolynomial (Fin (r + 1)) S) N)
      (Module.End (Poly (MvPolynomial (Fin (r + 1)) S) N) (UT x η)) (s : Poly _ N)) := by
  rw [Module.End.isUnit_iff]
  have hu : IsUnit (UT.ofL (x := x) (η := η) (xyHom S x η s)) := isUnit_xyHom η hI s.2
  have : ⇑(algebraMap (Poly (MvPolynomial (Fin (r + 1)) S) N)
      (Module.End (Poly (MvPolynomial (Fin (r + 1)) S) N) (UT x η)) (s : Poly _ N)) =
      fun v => UT.ofL (x := x) (η := η) (xyHom S x η s) * v := by
    funext v; rfl
  rw [this]
  exact hu.unit.mulLeft_bijective
def locEmb (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I →ₗ[Poly (MvPolynomial (Fin (r + 1)) S) N] UT x η :=
  LocalizedModule.lift (monos I) (twSub η M₀).subtype (locEmb_isUnit η hI)
def LocGood (c : ℤ) (I : Finset (Fin (N + 1))) (W : LaurUT Ω) : Prop :=
  ∀ b : ℤ, W.coeff (b, c) ∈ twLocPart η M₀ b c I
end Loc
end
end GroundTheory.Heights₂.Heights.Kleiman


