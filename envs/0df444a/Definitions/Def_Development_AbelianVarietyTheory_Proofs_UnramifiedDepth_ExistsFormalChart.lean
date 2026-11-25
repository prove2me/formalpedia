-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:36:45.804893+00:00
-- url     : https://prove2.me/theorems/4b609345-8cff-4aa7-984b-d60f53b28d3f
-- title:
--   Exists Formal Chart
-- statement:
--   Definitions and structural lemmas for Exists Formal Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFormalChart.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Theorems.Thm_ReciprocityTheory_PGsh_LHom_sqZero_of_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.FormalChartOf
variable {R₀ : Type} [CommRing R₀]
theorem dual_local [IsLocalRing R₀] : IsLocalRing (DualNumber R₀) := by
  haveI : Nontrivial (DualNumber R₀) := TrivSqZeroExt.inl_injective.nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst
abbrev dualL (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] : LAlg R₀ :=
  @LAlg.mk R₀ _ (DualNumber R₀) _ _ dual_local
abbrev baseL (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] : LAlg R₀ :=
  @LAlg.mk R₀ _ R₀ _ _ _
def dualProj (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] : LHom (dualL R₀) (baseL R₀) :=
  ⟨TrivSqZeroExt.fstHom R₀ R₀ R₀, ⟨fun _ h => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 h⟩⟩
theorem dualProj_ker [IsLocalRing R₀] :
    RingHom.ker (dualProj R₀).1 = Ideal.span {(DualNumber.eps : DualNumber R₀)} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton']
  constructor
  · intro h
    have h' : TrivSqZeroExt.fst a = 0 := h
    refine ⟨TrivSqZeroExt.inl (TrivSqZeroExt.snd a), ?_⟩
    ext <;> simp [h']
  · rintro ⟨b, rfl⟩
    change TrivSqZeroExt.fst (b * DualNumber.eps) = 0
    simp
theorem dualProj_sqZero [IsLocalRing R₀] : (dualProj R₀).SqZero :=
  LHom.sqZero_of_span _ (DualNumber.eps : DualNumber R₀)
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) dualProj_ker DualNumber.eps_mul_eps
def epsK (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] : (dualProj R₀).ker :=
  ⟨(DualNumber.eps : DualNumber R₀), (rfl : TrivSqZeroExt.fst (DualNumber.eps : DualNumber R₀) = 0)⟩
def dualTo {S : Type} [CommRing S] [Algebra R₀ S] (i : S) (hi : i * i = 0) : DualNumber R₀ →ₐ[R₀] S :=
  DualNumber.lift ⟨(Algebra.ofId R₀ S, i), hi, fun _ => Commute.all _ _⟩
theorem dualTo_apply {S : Type} [CommRing S] [Algebra R₀ S] (i : S) (hi : i * i = 0)
    (a : DualNumber R₀) : dualTo i hi a = algebraMap R₀ S a.fst + a.snd • i := by
  rw [dualTo, DualNumber.lift_apply_apply, Algebra.smul_def]
  rfl
def dualToL [IsLocalRing R₀] (S : LAlg R₀) (hS : IsLocalHom (algebraMap R₀ (S : Type)))
    (i : (S : Type)) (hi : i * i = 0) : LHom (dualL R₀) S :=
  ⟨dualTo i hi, ⟨fun a h => by
    have h' : IsUnit (dualTo i hi a) := h
    rw [dualTo_apply] at h'
    have hn : IsNilpotent (-(TrivSqZeroExt.snd a • i)) :=
      (IsNilpotent.smul ⟨2, by rw [pow_two, hi]⟩ _).neg
    have h2 := hn.isUnit_add_left_of_commute h' (Commute.all _ _)
    rw [add_neg_cancel_right] at h2
    exact TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (hS.map_nonunit _ h2)⟩⟩
section Coord
variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {g : ℕ}
  (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G))
  (h0 : ∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1)
  (hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') (a : Fin g → S),
    (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i)))
  (hinj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b)
  (hsurj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
    (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
    ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)
variable [IsLocalRing R₀] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G))
  (he : ∀ R, Function.Bijective (e R)) (hadd : ∀ R x y, e R (x + y) = e R x * e R y)
  (hen : ∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x)
end Coord
end GlobalTheory.FormalChartOf


