-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ModPToValuationResidueFieldSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ModPToValuationResidueFieldSurjective
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T16:37:47.73255+00:00
-- url     : https://prove2.me/theorems/de6f319e-9781-558a-b268-8e84626c9c53
-- title:
--   Mod PTo Valuation Residue Field Surjective
-- statement:
--   Definitions and structural lemmas for Mod PTo Valuation Residue Field Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ModPToValuationResidueFieldSurjective.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_O_local
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_local_of_surj_sq
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_theta_surj
import Theorems.Thm_ReciprocityTheory_PGsh_a0

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
namespace GlobalTheory.WdAinf
open WittVector Ideal
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
abbrev WRing (ϖ : PreTilt O p) := Ainf.A p O ⧸ span {(p : Ainf.A p O) ^ 2, teichmuller p ϖ}
lemma mk_teich (ϖ : PreTilt O p) :
    Ideal.Quotient.mk (span {(p : Ainf.A p O) ^ 2, teichmuller p ϖ}) (teichmuller p ϖ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
lemma p_sq (ϖ : PreTilt O p) : (p : WRing p O ϖ) ^ 2 = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (span {(p : Ainf.A p O) ^ 2, teichmuller p ϖ})), ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
lemma modP_valuationIntegers_prime_eq_zero : (p : Ainf.Rn p O 0) = 0 := by
  have h := Ainf.hpRn p O 0
  exact (pow_one _).symm.trans h
def piW (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) : WRing p O ϖ →+* Ainf.Rn p O 0 :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk (span {(p : O) ^ (0 + 1)})).comp (fontaineTheta O p))
    (fun a ha => by
      obtain ⟨b, c, rfl⟩ := Ideal.mem_span_pair.1 ha
      simp only [RingHom.comp_apply, map_add, map_mul, map_pow, map_natCast,
        fontaineTheta_teichmuller, hϖ, modP_valuationIntegers_prime_eq_zero]
      simp)
lemma piW_mk (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) (a : Ainf.A p O) :
    piW p O ϖ hϖ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (fontaineTheta O p a) := rfl
lemma piW_surj (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) :
    Function.Surjective (piW p O ϖ hϖ) := by
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, rfl⟩ := Ainf.theta_surj p O hv b
  exact ⟨_, piW_mk p O ϖ hϖ a⟩
lemma ker_piW (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) :
    RingHom.ker (piW p O ϖ hϖ) = span {(p : WRing p O ϖ)} := by
  obtain ⟨-, -, hK, -, -, -⟩ := a0 p C v O hv
  have h3 := (hK ϖ hϖ).2.2
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · intro hx
    rw [RingHom.mem_ker, piW_mk, Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at hx
    have ha : a ∈ RingHom.ker ((Ideal.Quotient.mk (span {(p : O)})).comp (fontaineTheta O p)) := by
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]; exact hx
    rw [h3] at ha
    obtain ⟨b, c, rfl⟩ := Ideal.mem_span_pair.1 ha
    refine Ideal.mem_span_singleton'.2 ⟨Ideal.Quotient.mk _ b, ?_⟩
    simp only [map_add, map_mul, map_natCast, mk_teich, mul_zero, add_zero]
  · intro hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
    rw [RingHom.mem_ker, ← hy, map_mul, map_natCast, modP_valuationIntegers_prime_eq_zero, mul_zero]
lemma W_local (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) :
    IsLocalRing (WRing p O ϖ) := by
  haveI := Ainf.Rn_local p O hv 0
  refine Ainf.local_of_surj_sq (piW p O ϖ hϖ) (piW_surj p O hv ϖ hϖ) ?_
  intro k hk
  rw [ker_piW p O hv ϖ hϖ] at hk
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hk
  rw [show y * (p : WRing p O ϖ) * (y * p) = y * y * (p : WRing p O ϖ) ^ 2 by ring, p_sq, mul_zero]
abbrev ResK (hv : v.Integers O) : Type :=
  haveI := Ainf.O_local O hv
  ResidueField O
def resO (hv : v.Integers O) : O →+* ResK O hv :=
  haveI := Ainf.O_local O hv
  residue O
lemma resO_surj (hv : v.Integers O) : Function.Surjective (resO O hv) :=
  haveI := Ainf.O_local O hv
  residue_surjective
lemma resO_eq_zero (hv : v.Integers O) (x : O) : resO O hv x = 0 ↔ ¬IsUnit x :=
  haveI := Ainf.O_local O hv
  (residue_eq_zero_iff x).trans ((mem_maximalIdeal x).trans mem_nonunits_iff)
def rho1 (hv : v.Integers O) : Ainf.Rn p O 0 →+* ResK O hv :=
  Ideal.Quotient.lift _ (resO O hv) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [zero_add, pow_one, map_mul, (resO_eq_zero O hv (p : O)).2 Fact.out, mul_zero])
lemma modPToValuationResidueField_surjective (hv : v.Integers O) : Function.Surjective (rho1 p O hv) := by
  intro y
  obtain ⟨a, rfl⟩ := resO_surj O hv y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩
variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
  (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O))
include hv hε hϖ
lemma xi_img : ∃ u : (Ainf.A p O)ˣ,
    (Ideal.Quotient.mk _ (Ainf.xi p O ε) : WRing p O ϖ) =
      (p : WRing p O ϖ) * (Ideal.Quotient.mk _ (u : Ainf.A p O) : WRing p O ϖ) := by
  obtain ⟨-, -, -, hX, -, -⟩ := a0 p C v O hv
  obtain ⟨u, hu⟩ := ((hX ε hv hε).2.2.2 ϖ hϖ).2
  refine ⟨u, ?_⟩
  have hu' : Ainf.xi p O ε = u * ((p : Ainf.A p O) - teichmuller p ϖ) := hu
  rw [hu', map_mul, map_sub, map_natCast, mk_teich, sub_zero, mul_comm]
def toW : Ainf.R0 p O ε →+* WRing p O ϖ :=
  Ideal.Quotient.lift _ (Ideal.Quotient.mk _) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨u, hu⟩ := xi_img p O hv ε hε ϖ hϖ
    rw [map_mul, map_pow, hu, mul_pow, p_sq, zero_mul, mul_zero])
def psiW : Ainf.R'n p O ε 1 →+* WRing p O ϖ :=
  Ideal.Quotient.lift _ (toW p O hv ε hε ϖ hϖ) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, map_natCast, show (1 + 1 : ℕ) = 2 from rfl, p_sq, mul_zero])
lemma psiW_surj : Function.Surjective (psiW p O hv ε hε ϖ hϖ) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a), rfl⟩
def LW : LAlg (Ainf.R0 p O ε) :=
  { carrier := WRing p O ϖ, alg := (toW p O hv ε hε ϖ hϖ).toAlgebra, loc := W_local p O hv ϖ hϖ }
omit hϖ in

def LK : LAlg (Ainf.R0 p O ε) :=
  { carrier := ResK O hv, alg := ((resO O hv).comp (Ainf.thetaBar p O hv ε hε)).toAlgebra }
def piWL : LHom (LW p O hv ε hε ϖ hϖ) ((Ainf.ainfTowerL p O hv ε hε).R 0) :=
  ⟨{ toRingHom := piW p O ϖ hϖ
     commutes' := fun r => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      rfl },
    TowerExample.isLocalHom_of_surj _ (piW_surj p O hv ϖ hϖ)⟩
omit hϖ in

def rho1L : LHom ((Ainf.ainfTowerL p O hv ε hε).R 0) (LK p O hv ε hε) :=
  ⟨{ toRingHom := rho1 p O hv
     commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (modPToValuationResidueField_surjective p O hv)⟩
def psiL : LHom ((Ainf.ainfTowerL p O hv ε hε).R' 1) (LW p O hv ε hε ϖ hϖ) :=
  ⟨{ toRingHom := psiW p O hv ε hε ϖ hϖ
     commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (psiW_surj p O hv ε hε ϖ hϖ)⟩
end GlobalTheory.WdAinf
namespace GlobalTheory
end GlobalTheory


