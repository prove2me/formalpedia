-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:48.4007+00:00
-- url     : https://prove2.me/theorems/bccf0232-8885-47e6-9e19-cad52a7d1cb1
-- title:
--   Universal Derivation
-- statement:
--   Definitions and structural lemmas for Universal Derivation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Theorems.Thm_GlobalTheory_SquareZeroLeibnizPoint_sqzOfLeibniz_fst
import Theorems.Thm_GlobalTheory_SquareZeroLeibnizPoint_sqzOfLeibniz_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_fst
attribute [local simp] GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_snd


set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory.CotUniv
section Ring
variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
def SqExt : Type := TrivSqZeroExt O M
instance : CommRing (SqExt O M) :=
  letI : Module Oᵐᵒᵖ M := Module.compHom M ((RingHom.id O).fromOpposite mul_comm)
  haveI : IsCentralScalar O M := ⟨fun _ _ => rfl⟩
  inferInstanceAs (CommRing (TrivSqZeroExt O M))
variable {O M}
def SqExt.mk (a : O) (m : M) : SqExt O M := (a, m)
def SqExt.fst (x : SqExt O M) : O := TrivSqZeroExt.fst x
def SqExt.snd (x : SqExt O M) : M := TrivSqZeroExt.snd x
namespace SqExt
omit [CommRing O] [AddCommGroup M] [Module O M] in
lemma ext {x y : SqExt O M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.ext h1 h2
omit [CommRing O] [AddCommGroup M] [Module O M] in
@[simp] lemma fst_mk (a : O) (m : M) : (mk a m).fst = a := rfl
omit [CommRing O] [AddCommGroup M] [Module O M] in
@[simp] lemma snd_mk (a : O) (m : M) : (mk a m).snd = m := rfl
@[simp] lemma fst_add (x y : SqExt O M) : (x + y).fst = x.fst + y.fst := rfl
@[simp] lemma snd_add (x y : SqExt O M) : (x + y).snd = x.snd + y.snd := rfl
@[simp] lemma fst_zero : (0 : SqExt O M).fst = 0 := rfl
@[simp] lemma snd_zero : (0 : SqExt O M).snd = 0 := rfl
@[simp] lemma fst_one : (1 : SqExt O M).fst = 1 := rfl
@[simp] lemma snd_one : (1 : SqExt O M).snd = 0 := rfl
@[simp] lemma fst_mul (x y : SqExt O M) : (x * y).fst = x.fst * y.fst := rfl
@[simp] lemma snd_mul (x y : SqExt O M) : (x * y).snd = x.fst • y.snd + y.fst • x.snd := rfl
lemma isUnit_iff (x : SqExt O M) : IsUnit x ↔ IsUnit x.fst := by
  letI : Module Oᵐᵒᵖ M := Module.compHom M ((RingHom.id O).fromOpposite mul_comm)
  haveI : IsCentralScalar O M := ⟨fun _ _ => rfl⟩
  exact TrivSqZeroExt.isUnit_iff_isUnit_fst (R := O) (M := M)
def sndHom : SqExt O M →+ M := ⟨⟨snd, rfl⟩, fun _ _ => rfl⟩
def fstHom : SqExt O M →+* O where
  toFun := fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
def lift {A : Type} [CommRing A] (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) : A →+* SqExt O M :=
  letI : Module Oᵐᵒᵖ M := Module.compHom M ((RingHom.id O).fromOpposite mul_comm)
  haveI : IsCentralScalar O M := ⟨fun _ _ => rfl⟩
  GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz ε d hd
instance [IsLocalRing O] : IsLocalRing (SqExt O M) := by
  haveI : Nontrivial (SqExt O M) := (fstHom (O := O) (M := M)).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add ?_
  intro a b h
  rw [isUnit_iff, fst_add] at h
  rw [isUnit_iff, isUnit_iff]
  exact IsLocalRing.isUnit_or_isUnit_of_isUnit_add h
end SqExt
end Ring
section Alg
variable {R₀ : Type} [CommRing R₀] (O : LAlg R₀)
  (M : Type) [AddCommGroup M] [Module (O : Type) M]
def sqAlg : LAlg R₀ :=
  letI : Algebra R₀ (SqExt (O : Type) M) :=
    (SqExt.lift (algebraMap R₀ (O : Type)) 0 (by simp)).toAlgebra
  { carrier := SqExt (O : Type) M }
def sqProj : LHom (sqAlg O M) O :=
  ⟨{ (SqExt.fstHom : SqExt (O : Type) M →+* O) with commutes' := fun _ => rfl },
    ⟨fun a h => (SqExt.isUnit_iff a).2 h⟩⟩
variable {O M}
def sqLift {A : LAlg R₀} (ε : LHom A O) (d : (A : Type) →+ M)
    (hd : ∀ f f', d (f * f') = ε.1 f • d f' + ε.1 f' • d f)
    (h0 : ∀ r, d (algebraMap R₀ (A : Type) r) = 0) : LHom A (sqAlg O M) :=
  ⟨{ (SqExt.lift (ε.1 : (A : Type) →+* O) d hd : (A : Type) →+* SqExt (O : Type) M) with
      commutes' := fun r => SqExt.ext (ε.1.commutes r) (h0 r) },
    ⟨fun a h => ε.2.map_nonunit a ((SqExt.isUnit_iff _).1 h)⟩⟩
variable (O M)
def sqIncl : LHom O (sqAlg O M) := sqLift (LHom.id O) 0 (by simp) (by simp)
lemma sqProj_sqZero : (sqProj O M).SqZero := by
  refine ⟨fun a => ⟨SqExt.mk a 0, rfl⟩, ?_⟩
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  have hr' : SqExt.fst (O := (O : Type)) (M := M) r = 0 := hr
  have hs' : SqExt.fst (O := (O : Type)) (M := M) s = 0 := hs
  rw [Ideal.mem_bot]
  refine SqExt.ext (O := (O : Type)) (M := M) ?_ ?_
  · exact (SqExt.fst_mul r s).trans (by rw [hr', zero_mul]; rfl)
  · exact (SqExt.snd_mul r s).trans (by rw [hr', hs', zero_smul, zero_smul, add_zero]; rfl)
variable {O M}
def sqKer : M →+ (sqProj O M).ker where
  toFun m := ⟨SqExt.mk 0 m, rfl⟩
  map_zero' := rfl
  map_add' _ _ := Subtype.ext (SqExt.ext (O := (O : Type)) (M := M) (add_zero _).symm rfl)
variable {M' : Type} [AddCommGroup M'] [Module (O : Type) M']
def sqMap (u : M →ₗ[(O : Type)] M') : LHom (sqAlg O M) (sqAlg O M') :=
  sqLift (sqProj O M) (u.toAddMonoidHom.comp SqExt.sndHom)
    (fun f f' => by
      refine (congrArg u (SqExt.snd_mul (O := (O : Type)) (M := M) f f')).trans ?_
      rw [map_add, map_smul, map_smul]; rfl)
    (fun _ => map_zero u)
end Alg
section Lie
variable {O : Type} [CommRing O] {p g : ℕ} {M : Type} [AddCommGroup M] [Module O M]
def lieBasis (O : Type) [CommRing O] (p g : ℕ) (k : Fin g) : LieDualModP p O g :=
  Submodule.Quotient.mk (Pi.single k 1)
def lieLift (O : Type) [CommRing O] [Module O M] (m : Fin g → M) (hm : ∀ k, p • m k = 0) : LieDualModP p O g →ₗ[O] M :=
  Submodule.liftQ _ (Fintype.linearCombination O m) (by
    refine Submodule.smul_le.2 fun r hr l _ => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [LinearMap.mem_ker, map_smul, mul_smul, Fintype.linearCombination_apply, Finset.smul_sum,
      Finset.sum_eq_zero, smul_zero]
    intro k _
    rw [smul_comm, Nat.cast_smul_eq_nsmul, hm, smul_zero])
end Lie
section Core
variable {R₀ : Type} [CommRing R₀] {B : BX R₀} {O A : LAlg R₀} {p g : ℕ}
  {sO : LHom O A} {ε : LHom A O} {y : B.G A} {w : Fin g → B.gg}
abbrev tgPt (B : BX R₀) (O : LAlg R₀) (w : Fin g → B.gg) {M : Type} [AddCommGroup M]
    [Module (O : Type) M] (m : Fin g → M) : B.G (sqAlg O M) :=
  B.tg (sqProj O M) (sqProj_sqZero O M) (∑ k, w k ⊗ₜ[R₀] sqKer (m k))
variable {M : Type} [AddCommGroup M] [Module (O : Type) M]
variable {M' : Type} [AddCommGroup M'] [Module (O : Type) M']
end Core
end GlobalTheory.CotUniv


