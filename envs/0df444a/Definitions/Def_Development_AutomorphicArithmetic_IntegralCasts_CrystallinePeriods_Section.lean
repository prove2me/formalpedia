-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:57:17.396854+00:00
-- url     : https://prove2.me/theorems/20d43e08-e8b1-45fc-af2e-57211113e6c0
-- title:
--   Section
-- statement:
--   Definitions and structural lemmas for Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
namespace Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
section Witt
variable {k : Type w} [CommRing k] [CharP k p] [PerfectRing k p]
def Tilt.ofPerfect (f : k →+* R ⧸ span {(p : R)}) : k →+* Tilt p R :=
  Perfection.lift p k (ModP R p) f
def Ainf.ofWitt (f : k →+* R ⧸ span {(p : R)}) : WittVector p k →+* Ainf p R :=
  WittVector.map (Tilt.ofPerfect p f)
omit [Fact ¬IsUnit (p : R)] in

def wittResidueMap (g : WittVector p k →+* R) : k →+* R ⧸ span {(p : R)} :=
  (Ideal.quotientMap _ g (span_natCast_le_comap p g)).comp
    (WittVector.quotientPEquiv (p := p) (k := k)).symm.toRingHom
def Ainf.liftWitt (g : WittVector p k →+* R) : WittVector p k →+* Ainf p R :=
  Ainf.ofWitt p (wittResidueMap p g)
end Witt
section FracWitt
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]
def fracWittLift {B : Type*} [CommRing B] (f : WittVector p k →+* B) (h : IsUnit (p : B)) :
    FractionRing (WittVector p k) →+* B :=
  IsLocalization.lift (M := nonZeroDivisors (WittVector p k)) (g := f) (by
    rintro ⟨x, hx⟩
    obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' x (nonZeroDivisors.ne_zero hx)
    change IsUnit (f _)
    rw [map_mul, map_pow, map_natCast]
    exact (h.pow _).mul ((Units.isUnit _).map f))
def AinfInv.liftFracWitt (g : WittVector p k →+* R) :
    FractionRing (WittVector p k) →+* AinfInv p R :=
  fracWittLift p ((algebraMap (Ainf p R) (AinfInv p R)).comp (Ainf.liftWitt p g))
    (AinfInv.isUnit_p p)
end FracWitt
variable [IsAdicComplete (span {(p : R)}) R]
namespace BdRPlus
variable {p}
variable {F : Type v} {L : Type w} [CommRing F] [CommRing L] [Algebra F L]
theorem exists_section [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) :
    ∃ s : L →+* BdRPlus p R, (∀ x, theta p R (s x) = j x) ∧
      ∀ a : F, s (algebraMap F L a) = algebraMap (AinfInv p R) _ (ι a) := by
  letI : Algebra F (AinfInv p R) := ι.toAlgebra
  let e := RingHom.quotientKerEquivOfSurjective hθ
  let f : L →ₐ[F] AinfInv p R ⧸ AinfInv.kerTheta p R :=
    { e.symm.toRingHom.comp j with
      commutes' := fun a => by
        change e.symm (j (algebraMap F L a)) = Ideal.Quotient.mk _ (ι a)
        rw [RingEquiv.symm_apply_eq, hj]
        rfl }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq f
  refine ⟨g.toRingHom, fun x => ?_, fun a => g.commutes a⟩
  have h1 : AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) (g x) = e.symm (j x) :=
    AlgHom.congr_fun hg x
  change e (AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) (g x)) = j x
  rw [h1, RingEquiv.apply_symm_apply]
def «section» [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) : L →+* BdRPlus p R :=
  (exists_section hθ ι j hj).choose
end BdRPlus
end Reformulated.AutPerF


