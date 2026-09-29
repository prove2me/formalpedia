-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b3964521-ae15-5c75-a37a-c8a2a653e517

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_cechPushforward_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_coker
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

noncomputable section

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective IsProper Spec Scheme IsSeparated IsAffineOpen IsNoetherian tilde Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated OModulePresheaf.AffHom Scheme.OrderedAffineCover OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.cechPushforward OModulePresheaf.isCoherent_cechPushforward_of_isProper OModulePresheaf.isQuasicoherent_cechPushforward_of_isSeparated"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "Hom AffHom AffHom.naturality_apply AffHom.app_smul d IsCoherent IsQuasicoherent res mk module obj rec pow pow_res_apply zero ker im coker imCokerSES cechPushforward.chart cechPushforward.cocycles cechPushforward.mem_cocycles_iff cechPushforward cechPushforward.coe_smul cechPushforward.ext AffHom.affineChart AffHom.coe_cechPushforward_app isCoherent_cechPushforward_of_isProper isQuasicoherent_cechPushforward_of_isSeparated exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper isCoherent_coker isQuasicoherent_coker isQuasicoherent_pow"
namespace C2Head
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

def smulHom (H : OModulePresheaf q) {m : ℕ} (a : Fin m → A) : Hom (H.pow m) H where
  app U :=
    { toFun := fun x => ∑ l : Fin m, a l • x l
      map_add' := fun x y => by
        show ∑ l : Fin m, a l • (x l + y l) = (∑ l : Fin m, a l • x l) + ∑ l : Fin m, a l • y l
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => smul_add _ _ _
      map_smul' := fun r x => by
        show ∑ l : Fin m, a l • (r • x l) = r • ∑ l : Fin m, a l • x l
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _ }
  app_smul U s x := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
    show ∑ l : Fin m, a l • (s • x) l = s • ∑ l : Fin m, a l • x l
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    show a l • (s • x l) = s • (a l • x l)
    rw [smul_comm]
  naturality h := by
    refine LinearMap.ext fun x => ?_
    show ∑ l : Fin m, a l • ((H.pow m).res h x) l = H.res h (∑ l : Fin m, a l • x l)
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [LinearMap.map_smul, pow_res_apply]

theorem smulHom_app (H : OModulePresheaf q) {m : ℕ} (a : Fin m → A) (U : P.Opens) (x : (H.pow m).obj U) :
    (smulHom H a).app U x = ∑ l : Fin m, a l • x l := rfl

theorem range_smulHom_app (H : OModulePresheaf q) {m : ℕ} (a : Fin m → A) (U : P.Opens) :
    LinearMap.range ((smulHom H a).app U) = Ideal.span (Set.range a) • (⊤ : Submodule A (H.obj U)) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [smulHom_app]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem_smul (Ideal.subset_span ⟨l, rfl⟩) Submodule.mem_top
  · refine Submodule.smul_le.mpr ?_
    intro r hr y _
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨l, rfl⟩ := hr
      refine ⟨Pi.single l y, ?_⟩
      rw [smulHom_app, Finset.sum_eq_single l (fun l' _ h => by rw [Pi.single_eq_of_ne h, smul_zero])
        (fun h => absurd (Finset.mem_univ l) h)]
      rw [Pi.single_eq_same]
    | zero => exact ⟨0, by rw [map_zero, zero_smul]⟩
    | add r s _ _ hr hs =>
      obtain ⟨x, hx⟩ := hr; obtain ⟨x', hx'⟩ := hs
      exact ⟨x + x', by rw [map_add, hx, hx', add_smul]⟩
    | smul t r _ hr =>
      obtain ⟨x, hx⟩ := hr
      exact ⟨t • x, by rw [LinearMap.map_smul, hx, smul_eq_mul, mul_smul]⟩

theorem exists_span_eq_pow [IsNoetherianRing A] (I : Ideal A) (k : ℕ) :
    ∃ (m : ℕ) (a : Fin m → A), Ideal.span (Set.range a) = I ^ (k + 1) := by
  have hfg : (I ^ (k + 1)).FG := IsNoetherian.noetherian _
  obtain ⟨m, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  exact ⟨m, a, ha⟩

section Trunc

variable [IsNoetherianRing A] (I : Ideal A)

def genN (k : ℕ) : ℕ := (exists_span_eq_pow I k).choose

def gen (k : ℕ) : Fin (genN I k) → A := (exists_span_eq_pow I k).choose_spec.choose

theorem span_gen (k : ℕ) : Ideal.span (Set.range (gen I k)) = I ^ (k + 1) :=
  (exists_span_eq_pow I k).choose_spec.choose_spec

variable (H : OModulePresheaf q)

def trunc (k : ℕ) : OModulePresheaf q := coker (smulHom H (gen I k))

theorem range_smulHom_gen (k : ℕ) (U : P.Opens) :
    LinearMap.range ((smulHom H (gen I k)).app U) = I ^ (k + 1) • (⊤ : Submodule A (H.obj U)) := by
  rw [range_smulHom_app, span_gen]

def truncProj (k : ℕ) : Hom H (trunc I H k) := (imCokerSES (smulHom H (gen I k))).proj

theorem truncProj_app (k : ℕ) (U : P.Opens) (x : H.obj U) :
    (truncProj I H k).app U x = (show (trunc I H k).obj U from Submodule.Quotient.mk x) := rfl

theorem truncProj_surjective (k : ℕ) (U : P.Opens) : Function.Surjective ((truncProj I H k).app U) :=
  (imCokerSES (smulHom H (gen I k))).surjective U

theorem ker_truncProj (k : ℕ) (U : P.Opens) :
    LinearMap.ker ((truncProj I H k).app U) = I ^ (k + 1) • (⊤ : Submodule A (H.obj U)) := by
  show LinearMap.ker (Submodule.mkQ (LinearMap.range ((smulHom H (gen I k)).app U))) = _
  rw [Submodule.ker_mkQ, range_smulHom_gen]

theorem range_succ_le (k : ℕ) (U : P.Opens) :
    LinearMap.range ((smulHom H (gen I (k + 1))).app U) ≤ LinearMap.range ((smulHom H (gen I k)).app U) := by
  rw [range_smulHom_gen, range_smulHom_gen]
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ _))

def truncTrans (k : ℕ) : Hom (trunc I H (k + 1)) (trunc I H k) where
  app U := Submodule.mapQ _ _ LinearMap.id (range_succ_le I H k U)
  app_smul U a z := by
    induction z using Submodule.Quotient.induction_on with
    | H x => rfl
  naturality h := by
    refine LinearMap.ext fun z => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x => rfl

theorem truncTrans_mk (k : ℕ) (U : P.Opens) (x : H.obj U) :
    (truncTrans I H k).app U (show (trunc I H (k + 1)).obj U from Submodule.Quotient.mk x)
      = (show (trunc I H k).obj U from Submodule.Quotient.mk x) := rfl

theorem truncTrans_comp_truncProj (k : ℕ) (U : P.Opens) :
    (truncTrans I H k).app U ∘ₗ (truncProj I H (k + 1)).app U = (truncProj I H k).app U := rfl

theorem truncTrans_surjective (k : ℕ) (U : P.Opens) : Function.Surjective ((truncTrans I H k).app U) := by
  intro z
  obtain ⟨x, rfl⟩ := truncProj_surjective I H k U z
  exact ⟨(truncProj I H (k + 1)).app U x, rfl⟩

theorem smul_top_le_ker_truncProj (k : ℕ) (U : P.Opens) :
    I ^ (k + 1) • (⊤ : Submodule A (H.obj U)) ≤ LinearMap.ker ((truncProj I H k).app U) :=
  (ker_truncProj I H k U).ge

theorem ker_truncTrans (k : ℕ) (U : P.Opens) :
    LinearMap.ker ((truncTrans I H k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((trunc I H (k + 1)).obj U)) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ := truncProj_surjective I H (k + 1) U z
    have hx : x ∈ LinearMap.ker ((truncProj I H k).app U) := hz
    rw [ker_truncProj] at hx
    have : (truncProj I H (k + 1)).app U x ∈ (I ^ (k + 1) • (⊤ : Submodule A (H.obj U))).map ((truncProj I H (k + 1)).app U) :=
      Submodule.mem_map_of_mem hx
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  · refine Submodule.smul_le.mpr fun r hr z _ => ?_
    obtain ⟨x, rfl⟩ := truncProj_surjective I H (k + 1) U z
    show ((truncTrans I H k).app U ∘ₗ (truncProj I H (k + 1)).app U) (r • x) = 0
    rw [truncTrans_comp_truncProj]
    exact LinearMap.mem_ker.mp ((smul_top_le_ker_truncProj I H k U) (Submodule.smul_mem_smul hr Submodule.mem_top))

theorem isCoherent_trunc (hH : H.IsCoherent) (k : ℕ) : (trunc I H k).IsCoherent :=
  isCoherent_coker _ hH

theorem isQuasicoherent_trunc (hH : H.IsQuasicoherent) (k : ℕ) : (trunc I H k).IsQuasicoherent :=
  isQuasicoherent_coker _ hH (isQuasicoherent_pow _ hH)

end Trunc

section Nu

variable [IsNoetherianRing A] (I : Ideal A) [IsSeparated q]
  {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p] (K' : V'.OrderedAffineCover)
  (F' : ℕ → OModulePresheaf (p ≫ q)) (G' : OModulePresheaf (p ≫ q)) (ψ' : ∀ k, AffHom G' (F' k))
  (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
    LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))

include hψ'k

theorem cechPush_psi_smul_eq_zero (k : ℕ) (U : P.affineOpens) (r : A) (hr : r ∈ I ^ (k + 1))
    (x : (cechPushforward p q K' G').obj U.1) :
    ((ψ' k).cechPushforward p q K').app U (r • x) = 0 := by
  apply cechPushforward.ext; intro i
  rw [AffHom.coe_cechPushforward_app, cechPushforward.coe_smul]
  have hmem : r • x.1 i ∈ LinearMap.ker ((ψ' k).app (AffHom.affineChart p q K' U i)) := by
    rw [hψ'k]; exact Submodule.smul_mem_smul hr Submodule.mem_top
  exact LinearMap.mem_ker.mp hmem

theorem range_smulHom_le_ker (k : ℕ) (U : P.affineOpens) :
    LinearMap.range ((smulHom (cechPushforward p q K' G') (gen I k)).app U.1)
      ≤ LinearMap.ker (((ψ' k).cechPushforward p q K').app U) := by
  rw [range_smulHom_gen]
  exact Submodule.smul_le.mpr fun r hr x _ => cechPush_psi_smul_eq_zero I p K' F' G' ψ' hψ'k k U r hr x

def nu (k : ℕ) : AffHom (trunc I (cechPushforward p q K' G') k) (cechPushforward p q K' (F' k)) where
  app U := (LinearMap.range ((smulHom (cechPushforward p q K' G') (gen I k)).app U.1)).liftQ
    (((ψ' k).cechPushforward p q K').app U) (range_smulHom_le_ker I p K' F' G' ψ' hψ'k k U)
  app_smul U a z := by
    induction z using Submodule.Quotient.induction_on with
    | H x => exact ((ψ' k).cechPushforward p q K').app_smul U a x
  naturality {U U'} h := by
    refine LinearMap.ext fun z => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x => exact ((ψ' k).cechPushforward p q K').naturality_apply h x

theorem nu_mk (k : ℕ) (U : P.affineOpens) (x : (cechPushforward p q K' G').obj U.1) :
    (nu I p K' F' G' ψ' hψ'k k).app U
        (show (trunc I (cechPushforward p q K' G') k).obj U.1 from Submodule.Quotient.mk x)
      = ((ψ' k).cechPushforward p q K').app U x := rfl

theorem nu_comp_truncProj (k : ℕ) (U : P.affineOpens) :
    (nu I p K' F' G' ψ' hψ'k k).app U ∘ₗ (truncProj I (cechPushforward p q K' G') k).app U.1
      = ((ψ' k).cechPushforward p q K').app U := rfl

theorem nu_compat (φ' : ∀ k, AffHom (F' (k + 1)) (F' k))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)
    (k : ℕ) (U : P.affineOpens) :
    ((φ' k).cechPushforward p q K').app U ∘ₗ (nu I p K' F' G' ψ' hψ'k (k + 1)).app U
      = (nu I p K' F' G' ψ' hψ'k k).app U ∘ₗ (truncTrans I (cechPushforward p q K' G') k).app U.1 := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨x, rfl⟩ := truncProj_surjective I (cechPushforward p q K' G') (k + 1) U.1 z
  apply cechPushforward.ext; intro i
  show (((φ' k).cechPushforward p q K').app U (((ψ' (k + 1)).cechPushforward p q K').app U x)).1 i
    = (((ψ' k).cechPushforward p q K').app U x).1 i
  rw [AffHom.coe_cechPushforward_app, AffHom.coe_cechPushforward_app, AffHom.coe_cechPushforward_app]
  exact LinearMap.congr_fun (hψ'c k (AffHom.affineChart p q K' U i)) (x.1 i)

theorem nu_shift [IsProper q] [IsProper p] (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)
    (U : P.affineOpens) (k : ℕ) :
    ∃ c : ℕ, LinearMap.ker ((nu I p K' F' G' ψ' hψ'k (k + c)).app U)
      ≤ I ^ (k + 1) • (⊤ : Submodule A ((trunc I (cechPushforward p q K' G') (k + c)).obj U.1)) := by
  obtain ⟨c, hc⟩ :=
    exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper I q p G' hG'c hG'q K' U (k + 1)
  refine ⟨c, fun z hz => ?_⟩
  obtain ⟨n, rfl⟩ := truncProj_surjective I (cechPushforward p q K' G') (k + c) U.1 z
  have h0 : ((ψ' (k + c)).cechPushforward p q K').app U n = 0 := hz
  have hcomp : ∀ i : K'.ι, n.1 i ∈ I ^ (k + 1 + c) •
      (⊤ : Submodule A (G'.obj (K'.U i ⊓ p ⁻¹ᵁ (U : P.Opens)))) := fun i => by
    have hi : (ψ' (k + c)).app (AffHom.affineChart p q K' U i) (n.1 i) = 0 := by
      rw [← AffHom.coe_cechPushforward_app, h0]; rfl
    rw [← LinearMap.mem_ker, hψ'k, show k + c + 1 = k + 1 + c by omega] at hi
    exact hi
  obtain ⟨m, r, b, hr, hb, hn⟩ := hc n.1 ((cechPushforward.mem_cocycles_iff p q K' G' U.1 n.1).mp n.2) hcomp
  let b' : Fin m → (cechPushforward p q K' G').obj U.1 := fun l =>
    ⟨b l, (cechPushforward.mem_cocycles_iff p q K' G' U.1 (b l)).mpr (hb l)⟩
  have hn' : n = ∑ l, r l • b' l := by
    apply cechPushforward.ext; intro i
    have hsum : (∑ l, r l • b' l).1 = ∑ l, (r l • b' l).1 :=
      map_sum (cechPushforward.cocycles p q K' G' U.1).subtype _ _
    rw [hsum, hn]
    simp only [Finset.sum_apply]
    rfl
  show (truncProj I (cechPushforward p q K' G') (k + c)).app U.1 n ∈ _
  rw [hn', map_sum]
  exact Submodule.sum_mem _ fun l _ => by
    rw [LinearMap.map_smul]; exact Submodule.smul_mem_smul (hr l) Submodule.mem_top

end Nu

end AlgebraicGeometry.OModulePresheaf.C2Head

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective IsProper Spec Scheme IsSeparated IsAffineOpen IsNoetherian tilde Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated OModulePresheaf.AffHom Scheme.OrderedAffineCover OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.cechPushforward OModulePresheaf.isCoherent_cechPushforward_of_isProper OModulePresheaf.isQuasicoherent_cechPushforward_of_isSeparated"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "Hom AffHom AffHom.naturality_apply AffHom.app_smul d IsCoherent IsQuasicoherent res mk module obj rec pow pow_res_apply zero ker im coker imCokerSES cechPushforward.chart cechPushforward.cocycles cechPushforward.mem_cocycles_iff cechPushforward cechPushforward.coe_smul cechPushforward.ext AffHom.affineChart AffHom.coe_cechPushforward_app isCoherent_cechPushforward_of_isProper isQuasicoherent_cechPushforward_of_isSeparated exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper isCoherent_coker isQuasicoherent_coker isQuasicoherent_pow"
namespace C2Head
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

section Threads

variable (F : ℕ → OModulePresheaf q) (φ : ∀ k, AffHom (F (k + 1)) (F k))

def IsThread (U : P.affineOpens) (s : ∀ n, (F n).obj U.1) : Prop := ∀ n, (φ n).app U (s (n + 1)) = s n

def seq0 (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (y : (F 0).obj U.1) : ∀ m, (F m).obj U.1 :=
  fun m => @Nat.rec (fun m => (F m).obj U.1) y (fun m prev => Classical.choose (hφs m U prev)) m

def seqMod (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (n : ℕ) (x : ∀ m, (F m).obj U.1) (y : (F (n + 1)).obj U.1) : ∀ m, (F m).obj U.1 :=
  fun m => @Nat.rec (fun m => (F m).obj U.1) (x 0)
    (fun m prev => if m + 1 ≤ n then x (m + 1) else
      if h : m = n then (by subst h; exact y) else Classical.choose (hφs m U prev)) m

theorem seqMod_succ (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (n : ℕ) (x : ∀ m, (F m).obj U.1) (y : (F (n + 1)).obj U.1) (m : ℕ) :
    seqMod F φ hφs U n x y (m + 1) = (if m + 1 ≤ n then x (m + 1) else
      if h : m = n then (by subst h; exact y) else
        Classical.choose (hφs m U (seqMod F φ hφs U n x y m))) := rfl

theorem seqMod_of_le (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (n : ℕ) (x : ∀ m, (F m).obj U.1) (y : (F (n + 1)).obj U.1) :
    ∀ m, m ≤ n → seqMod F φ hφs U n x y m = x m
  | 0, _ => rfl
  | m + 1, hm => by rw [seqMod_succ, if_pos hm]

theorem seqMod_at (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (n : ℕ) (x : ∀ m, (F m).obj U.1) (y : (F (n + 1)).obj U.1) :
    seqMod F φ hφs U n x y (n + 1) = y := by
  rw [seqMod_succ, if_neg (Nat.not_succ_le_self n), dif_pos rfl]

theorem exists_isThread (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) : ∀ (k : ℕ) (y : (F k).obj U.1), ∃ s : ∀ n, (F n).obj U.1, IsThread F φ U s ∧ s k = y := by
  intro k
  induction k with
  | zero =>
    intro y
    exact ⟨seq0 F φ hφs U y, fun m => Classical.choose_spec (hφs m U (seq0 F φ hφs U y m)), rfl⟩
  | succ n ih =>
    intro y
    obtain ⟨x, hx, hxn⟩ := ih ((φ n).app U y)
    refine ⟨seqMod F φ hφs U n x y, fun m => ?_, seqMod_at F φ hφs U n x y⟩
    rw [seqMod_succ]
    split_ifs with h1 h2
    · rw [seqMod_of_le F φ hφs U n x y m (Nat.le_of_succ_le h1)]
      exact hx m
    · subst h2
      rw [seqMod_of_le F φ hφs U m x y m le_rfl, ← hxn]
    · exact Classical.choose_spec (hφs m U (seqMod F φ hφs U n x y m))

theorem IsThread.sub_mem (I : Ideal A)
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    {U : P.affineOpens} {s s' : ∀ n, (F n).obj U.1} (hs : IsThread F φ U s) (hs' : IsThread F φ U s')
    {k : ℕ} (h : s k = s' k) : ∀ n, k ≤ n → s n - s' n ∈ I ^ (k + 1) • (⊤ : Submodule A ((F n).obj U.1)) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rw [h, sub_self]; exact Submodule.zero_mem _
  | succ n hn ih =>

    have himg : (φ n).app U (s (n + 1) - s' (n + 1)) ∈
        Submodule.map ((φ n).app U) (I ^ (k + 1) • (⊤ : Submodule A ((F (n + 1)).obj U.1))) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hφs n U), map_sub, hs n, hs' n]
      exact ih
    obtain ⟨w, hw, hφw⟩ := himg
    have hker : s (n + 1) - s' (n + 1) - w ∈ LinearMap.ker ((φ n).app U) := by
      rw [LinearMap.mem_ker, map_sub, hφw, sub_self]
    rw [hφk] at hker
    have hle : I ^ (n + 1) • (⊤ : Submodule A ((F (n + 1)).obj U.1)) ≤ I ^ (k + 1) • ⊤ :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
    have := Submodule.add_mem _ (hle hker) hw
    rwa [sub_add_cancel] at this

end Threads

section Adapted

variable [IsSeparated q] {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p] (K' : V'.OrderedAffineCover)
  (F' : ℕ → OModulePresheaf (p ≫ q)) (G' : OModulePresheaf (p ≫ q)) (ψ' : ∀ k, AffHom G' (F' k))
  (F : ℕ → OModulePresheaf q) (v : ∀ k, AffHom (F k) (cechPushforward p q K' (F' k)))

def Adapted (U : P.affineOpens) (L : ℕ) (a : (cechPushforward p q K' G').obj U.1) (z : (F L).obj U.1) : Prop :=
  ((ψ' L).cechPushforward p q K').app U a = (v L).app U z

theorem psi_cechPushforward_compat (φ' : ∀ k, AffHom (F' (k + 1)) (F' k))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)
    (k : ℕ) (U : P.affineOpens) :
    ((φ' k).cechPushforward p q K').app U ∘ₗ ((ψ' (k + 1)).cechPushforward p q K').app U
      = ((ψ' k).cechPushforward p q K').app U := by
  refine LinearMap.ext fun x => cechPushforward.ext p q K' (F' k) fun i => ?_
  show (((φ' k).cechPushforward p q K').app U (((ψ' (k + 1)).cechPushforward p q K').app U x)).1 i = _
  rw [AffHom.coe_cechPushforward_app, AffHom.coe_cechPushforward_app, AffHom.coe_cechPushforward_app]
  exact LinearMap.congr_fun (hψ'c k (AffHom.affineChart p q K' U i)) (x.1 i)

theorem Adapted.down (φ' : ∀ k, AffHom (F' (k + 1)) (F' k)) (φ : ∀ k, AffHom (F (k + 1)) (F k))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)
    (hvc : ∀ (k : ℕ) (U : P.affineOpens),
      ((φ' k).cechPushforward p q K').app U ∘ₗ (v (k + 1)).app U = (v k).app U ∘ₗ (φ k).app U)
    {U : P.affineOpens} {L : ℕ} {a : (cechPushforward p q K' G').obj U.1} {s : ∀ n, (F n).obj U.1}
    (ha : Adapted p K' F' G' ψ' F v U (L + 1) a (s (L + 1))) (hs : IsThread F φ U s) :
    Adapted p K' F' G' ψ' F v U L a (s L) := by
  unfold Adapted at ha ⊢
  rw [← psi_cechPushforward_compat p K' F' G' ψ' φ' hψ'c L U, LinearMap.comp_apply, ha, ← hs L]
  exact LinearMap.congr_fun (hvc L U) (s (L + 1))

theorem psi_eq_of_thread (φ' : ∀ k, AffHom (F' (k + 1)) (F' k)) (φ : ∀ k, AffHom (F (k + 1)) (F k))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)
    (hvc : ∀ (k : ℕ) (U : P.affineOpens),
      ((φ' k).cechPushforward p q K').app U ∘ₗ (v (k + 1)).app U = (v k).app U ∘ₗ (φ k).app U)
    {U : P.affineOpens} {s : ∀ n, (F n).obj U.1} (hs : IsThread F φ U s) (i : K'.ι)
    (t : G'.obj (cechPushforward.chart p K' U.1 i)) {N : ℕ}
    (hN : (ψ' N).app (AffHom.affineChart p q K' U i) t = ((v N).app U (s N)).1 i) :
    ∀ (d n : ℕ), n + d = N → (ψ' n).app (AffHom.affineChart p q K' U i) t = ((v n).app U (s n)).1 i := by
  intro d
  induction d with
  | zero => intro n h; rw [Nat.add_zero] at h; subst h; exact hN
  | succ d ih =>
    intro n h
    have h' := ih (n + 1) (by omega)
    rw [← LinearMap.congr_fun (hψ'c n (AffHom.affineChart p q K' U i)) t, LinearMap.comp_apply, h',
      ← AffHom.coe_cechPushforward_app, ← LinearMap.comp_apply, hvc n U, LinearMap.comp_apply, hs n]

theorem exists_adapted (I : Ideal A) [IsNoetherianRing A] [IsProper q] [IsProper p]
    (φ' : ∀ k, AffHom (F' (k + 1)) (F' k)) (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)
    (hψ's : ∀ (k : ℕ) (V : V'.affineOpens), Function.Surjective ((ψ' k).app V))
    (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
      LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)
    (φ : ∀ k, AffHom (F (k + 1)) (F k))
    (hvc : ∀ (k : ℕ) (U : P.affineOpens),
      ((φ' k).cechPushforward p q K').app U ∘ₗ (v (k + 1)).app U = (v k).app U ∘ₗ (φ k).app U)
    (U : P.affineOpens) (L : ℕ) (s : ∀ n, (F n).obj U.1) (hs : IsThread F φ U s) :
    ∃ a : (cechPushforward p q K' G').obj U.1, Adapted p K' F' G' ψ' F v U L a (s L) := by
  classical
  haveI : IsSeparated (p ≫ q) := inferInstance
  obtain ⟨c, hc⟩ :=
    exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper
      I q p G' hG'c hG'q K' U (L + 1)

  have ht : ∀ i : K'.ι, ∃ t : G'.obj (cechPushforward.chart p K' U.1 i),
      (ψ' (L + c)).app (AffHom.affineChart p q K' U i) t = ((v (L + c)).app U (s (L + c))).1 i :=
    fun i => hψ's (L + c) (AffHom.affineChart p q K' U i) _
  choose t ht using ht

  have hCC : ∀ i j, IsAffineOpen (cechPushforward.chart p K' U.1 i ⊓ cechPushforward.chart p K' U.1 j) :=
    fun i j => Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated (p ≫ q)
      (AffHom.affineChart p q K' U i).2 (AffHom.affineChart p q K' U j).2
  have hdiff : ∀ i j : K'.ι,
      G'.res (U := (K'.U i ⊓ p ⁻¹ᵁ (U : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (U : P.Opens))) inf_le_left (t i)
        - G'.res (U := (K'.U i ⊓ p ⁻¹ᵁ (U : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (U : P.Opens))) inf_le_right (t j)
        ∈ I ^ (L + 1 + c) • (⊤ : Submodule A
          (G'.obj ((K'.U i ⊓ p ⁻¹ᵁ (U : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (U : P.Opens))))) := by
    intro i j
    have hw := (cechPushforward.mem_cocycles_iff p q K' (F' (L + c)) U.1 _).mp
      ((v (L + c)).app U (s (L + c))).2 i j
    have hker : G'.res (U := (K'.U i ⊓ p ⁻¹ᵁ (U : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (U : P.Opens))) inf_le_left (t i)
        - G'.res (U := (K'.U i ⊓ p ⁻¹ᵁ (U : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (U : P.Opens))) inf_le_right (t j)
        ∈ LinearMap.ker ((ψ' (L + c)).app ⟨_, hCC i j⟩) := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero,
        (ψ' (L + c)).naturality_apply (U := ⟨_, hCC i j⟩) (U' := AffHom.affineChart p q K' U i) inf_le_left,
        (ψ' (L + c)).naturality_apply (U := ⟨_, hCC i j⟩) (U' := AffHom.affineChart p q K' U j) inf_le_right,
        ht i, ht j]
      exact hw
    rw [hψ'k, show L + c + 1 = L + 1 + c by omega] at hker
    exact hker
  obtain ⟨a, ha, hta⟩ := hc t hdiff
  refine ⟨⟨a, (cechPushforward.mem_cocycles_iff p q K' G' U.1 a).mpr ha⟩, ?_⟩
  refine cechPushforward.ext p q K' (F' L) fun i => ?_
  rw [AffHom.coe_cechPushforward_app]

  have hat : (ψ' L).app (AffHom.affineChart p q K' U i) (t i - a i) = 0 := by
    rw [← LinearMap.mem_ker, hψ'k]
    exact hta i
  rw [map_sub, sub_eq_zero] at hat
  rw [← hat]
  exact psi_eq_of_thread p K' F' G' ψ' F v φ' φ hψ'c hvc hs i (t i) (ht i) c L rfl

end Adapted

end AlgebraicGeometry.OModulePresheaf.C2Head

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective IsProper Spec Scheme IsSeparated IsAffineOpen IsNoetherian tilde Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated OModulePresheaf.AffHom Scheme.OrderedAffineCover OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.cechPushforward OModulePresheaf.isCoherent_cechPushforward_of_isProper OModulePresheaf.isQuasicoherent_cechPushforward_of_isSeparated"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "Hom AffHom AffHom.naturality_apply AffHom.app_smul d IsCoherent IsQuasicoherent res mk module obj rec pow pow_res_apply zero ker im coker imCokerSES cechPushforward.chart cechPushforward.cocycles cechPushforward.mem_cocycles_iff cechPushforward cechPushforward.coe_smul cechPushforward.ext AffHom.affineChart AffHom.coe_cechPushforward_app isCoherent_cechPushforward_of_isProper isQuasicoherent_cechPushforward_of_isSeparated exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper isCoherent_coker isQuasicoherent_coker isQuasicoherent_pow"
namespace C2Head
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

section U

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
  {V' : Scheme.{u}} (p : V' ⟶ P) [IsProper p] (K' : V'.OrderedAffineCover)
  (F' : ℕ → OModulePresheaf (p ≫ q)) (φ' : ∀ k, AffHom (F' (k + 1)) (F' k))
  (G' : OModulePresheaf (p ≫ q))
  (ψ' : ∀ k, AffHom G' (F' k))
  (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
    LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))
  (F : ℕ → OModulePresheaf q) (φ : ∀ k, AffHom (F (k + 1)) (F k))
  (v : ∀ k, AffHom (F k) (cechPushforward p q K' (F' k)))

  (hPC : ∀ (k : ℕ) (U : P.affineOpens),
    ((φ' k).cechPushforward p q K').app U ∘ₗ ((ψ' (k + 1)).cechPushforward p q K').app U
      = ((ψ' k).cechPushforward p q K').app U)
  (hvc : ∀ (k : ℕ) (U : P.affineOpens),
    ((φ' k).cechPushforward p q K').app U ∘ₗ (v (k + 1)).app U = (v k).app U ∘ₗ (φ k).app U)

  (hT1 : ∀ (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1),
    ∃ s : ∀ n, (F n).obj U.1, (∀ n, (φ n).app U (s (n + 1)) = s n) ∧ s k = y)

  (hT2 : ∀ (U : P.affineOpens) (k : ℕ) (s s' : ∀ n, (F n).obj U.1),
    (∀ n, (φ n).app U (s (n + 1)) = s n) → (∀ n, (φ n).app U (s' (n + 1)) = s' n) → s k = s' k →
      ∀ n, k ≤ n → s n - s' n ∈ I ^ (k + 1) • (⊤ : Submodule A ((F n).obj U.1)))

  (hA2 : ∀ (U : P.affineOpens) (L : ℕ) (s : ∀ n, (F n).obj U.1), (∀ n, (φ n).app U (s (n + 1)) = s n) →
    ∃ a : (cechPushforward p q K' G').obj U.1, ((ψ' L).cechPushforward p q K').app U a = (v L).app U (s L))

def Good (U : P.affineOpens) (k L : ℕ) : Prop :=
  k ≤ L ∧ ∀ a : (cechPushforward p q K' G').obj U.1, ((ψ' L).cechPushforward p q K').app U a = 0 →
    a ∈ I ^ (k + 1) • (⊤ : Submodule A ((cechPushforward p q K' G').obj U.1))

theorem mem_smul_top_of_apply_mem {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (J : Ideal R) (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hker : LinearMap.ker f ≤ J • (⊤ : Submodule R M)) {x : M} (hx : f x ∈ J • (⊤ : Submodule R N)) :
    x ∈ J • (⊤ : Submodule R M) := by
  have htop : (⊤ : Submodule R N) = (⊤ : Submodule R M).map f := by
    rw [Submodule.map_top, LinearMap.range_eq_top.2 hf]
  rw [htop, ← Submodule.map_smul''] at hx
  obtain ⟨b, hb, hbx⟩ := hx
  have hk : x - b ∈ LinearMap.ker f := by rw [LinearMap.mem_ker, map_sub, hbx, sub_self]
  have := Submodule.add_mem _ hb (hker hk)
  rwa [add_sub_cancel] at this

include hψ'k in

theorem good_exists (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent) (U : P.affineOpens) (k : ℕ) :
    ∃ c, Good I p K' F' G' ψ' U k (k + c) := by
  obtain ⟨c, hc⟩ := nu_shift I p K' F' G' ψ' hψ'k hG'c hG'q U k
  refine ⟨c, Nat.le_add_right k c, fun a ha => ?_⟩
  refine mem_smul_top_of_apply_mem (I ^ (k + 1)) ((truncProj I (cechPushforward p q K' G') (k + c)).app U.1)
    (truncProj_surjective I _ (k + c) U.1) ?_ (hc ?_)
  · rw [ker_truncProj]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
  · rw [LinearMap.mem_ker]
    exact ha

include hPC in

theorem good_succ {U : P.affineOpens} {k L : ℕ} (h : Good I p K' F' G' ψ' U k L) :
    Good I p K' F' G' ψ' U k (L + 1) := by
  refine ⟨h.1.trans (Nat.le_succ L), fun a ha => h.2 a ?_⟩
  rw [← hPC L U, LinearMap.comp_apply, ha, map_zero]

include hPC in
theorem good_of_le {U : P.affineOpens} {k L L' : ℕ} (h : Good I p K' F' G' ψ' U k L) (hL : L ≤ L') :
    Good I p K' F' G' ψ' U k L' := by
  induction hL with
  | refl => exact h
  | step _ ih => exact good_succ I p K' F' φ' G' ψ' hPC ih

theorem good_of_succ_k {U : P.affineOpens} {k L : ℕ} (h : Good I p K' F' G' ψ' U (k + 1) L) :
    Good I p K' F' G' ψ' U k L :=
  ⟨(Nat.le_succ k).trans h.1, fun a ha => Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (h.2 a ha)⟩

include hPC hvc in

theorem adapted_pred (U : P.affineOpens) (s : ∀ n, (F n).obj U.1) (hs : ∀ n, (φ n).app U (s (n + 1)) = s n)
    (a : (cechPushforward p q K' G').obj U.1) (m : ℕ)
    (ha : ((ψ' (m + 1)).cechPushforward p q K').app U a = (v (m + 1)).app U (s (m + 1))) :
    ((ψ' m).cechPushforward p q K').app U a = (v m).app U (s m) := by
  rw [← hPC m U, LinearMap.comp_apply, ha, ← LinearMap.comp_apply, hvc m U, LinearMap.comp_apply, hs m]

include hPC hvc in
theorem adapted_of_le (U : P.affineOpens) (s : ∀ n, (F n).obj U.1) (hs : ∀ n, (φ n).app U (s (n + 1)) = s n)
    (a : (cechPushforward p q K' G').obj U.1) (d : ℕ) :
    ∀ n : ℕ, ((ψ' (n + d)).cechPushforward p q K').app U a = (v (n + d)).app U (s (n + d)) →
      ((ψ' n).cechPushforward p q K').app U a = (v n).app U (s n) := by
  induction d with
  | zero => intro n ha; exact ha
  | succ d ih => intro n ha; exact ih n (adapted_pred p K' F' φ' G' ψ' F φ v hPC hvc U s hs a (n + d) ha)

include hPC hvc in
theorem adapted_of_le' (U : P.affineOpens) (s : ∀ n, (F n).obj U.1) (hs : ∀ n, (φ n).app U (s (n + 1)) = s n)
    (a : (cechPushforward p q K' G').obj U.1) {n L : ℕ} (hnL : n ≤ L)
    (ha : ((ψ' L).cechPushforward p q K').app U a = (v L).app U (s L)) :
    ((ψ' n).cechPushforward p q K').app U a = (v n).app U (s n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnL
  exact adapted_of_le p K' F' φ' G' ψ' F φ v hPC hvc U s hs a d n ha

include hT1 hA2 in

theorem exists_adapted_of_mem_smul (U : P.affineOpens) (k L : ℕ) (d : (F L).obj U.1)
    (hd : d ∈ I ^ (k + 1) • (⊤ : Submodule A ((F L).obj U.1))) :
    ∃ m : (cechPushforward p q K' G').obj U.1,
      m ∈ I ^ (k + 1) • (⊤ : Submodule A ((cechPushforward p q K' G').obj U.1)) ∧
        ((ψ' L).cechPushforward p q K').app U m = (v L).app U d := by
  refine Submodule.smul_induction_on hd ?_ ?_
  · intro r hr w _
    obtain ⟨t, ht, htL⟩ := hT1 U L w
    obtain ⟨b, hb⟩ := hA2 U L t ht
    exact ⟨r • b, Submodule.smul_mem_smul hr Submodule.mem_top, by rw [LinearMap.map_smul, LinearMap.map_smul, hb, htL]⟩
  · intro x y ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩
    exact ⟨m₁ + m₂, Submodule.add_mem _ hm₁ hm₂, by rw [map_add, map_add, e₁, e₂]⟩

include hT1 hT2 hA2 in

theorem wit_unique {U : P.affineOpens} {k L : ℕ} (hgood : Good I p K' F' G' ψ' U k L)
    (s s' : ∀ n, (F n).obj U.1) (hs : ∀ n, (φ n).app U (s (n + 1)) = s n)
    (hs' : ∀ n, (φ n).app U (s' (n + 1)) = s' n) (hss' : s k = s' k)
    (a a' : (cechPushforward p q K' G').obj U.1)
    (ha : ((ψ' L).cechPushforward p q K').app U a = (v L).app U (s L))
    (ha' : ((ψ' L).cechPushforward p q K').app U a' = (v L).app U (s' L)) :
    (truncProj I (cechPushforward p q K' G') k).app U.1 a = (truncProj I (cechPushforward p q K' G') k).app U.1 a' := by
  have hd : s L - s' L ∈ I ^ (k + 1) • (⊤ : Submodule A ((F L).obj U.1)) := hT2 U k s s' hs hs' hss' L hgood.1
  obtain ⟨m, hm, hem⟩ := exists_adapted_of_mem_smul I p K' F' G' ψ' F φ v hT1 hA2 U k L _ hd
  have hz : ((ψ' L).cechPushforward p q K').app U (a - a' - m) = 0 := by
    rw [map_sub, map_sub, ha, ha', hem, map_sub, sub_self]
  have hmem := hgood.2 _ hz
  have hmem' : a - a' ∈ I ^ (k + 1) • (⊤ : Submodule A ((cechPushforward p q K' G').obj U.1)) := by
    have := Submodule.add_mem _ hmem hm
    rwa [sub_add_cancel] at this
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ker_truncProj]
  exact hmem'

include hPC hvc hT1 hT2 hA2 in

theorem wit_compare {U : P.affineOpens} {k L₁ L₂ : ℕ} (hg₁ : Good I p K' F' G' ψ' U k L₁)
    (hg₂ : Good I p K' F' G' ψ' U k L₂)
    (s₁ s₂ : ∀ n, (F n).obj U.1) (hs₁ : ∀ n, (φ n).app U (s₁ (n + 1)) = s₁ n)
    (hs₂ : ∀ n, (φ n).app U (s₂ (n + 1)) = s₂ n) (hk : s₁ k = s₂ k)
    (a₁ a₂ : (cechPushforward p q K' G').obj U.1)
    (ha₁ : ((ψ' L₁).cechPushforward p q K').app U a₁ = (v L₁).app U (s₁ L₁))
    (ha₂ : ((ψ' L₂).cechPushforward p q K').app U a₂ = (v L₂).app U (s₂ L₂)) :
    (truncProj I (cechPushforward p q K' G') k).app U.1 a₁ = (truncProj I (cechPushforward p q K' G') k).app U.1 a₂ := by
  obtain ⟨b₁, hb₁⟩ := hA2 U (L₁ + L₂) s₁ hs₁
  obtain ⟨b₂, hb₂⟩ := hA2 U (L₁ + L₂) s₂ hs₂
  have e₁ := wit_unique I p K' F' G' ψ' F φ v hT1 hT2 hA2 hg₁ s₁ s₁ hs₁ hs₁ rfl a₁ b₁ ha₁
    (adapted_of_le' p K' F' φ' G' ψ' F φ v hPC hvc U s₁ hs₁ b₁ (Nat.le_add_right L₁ L₂) hb₁)
  have e₂ := wit_unique I p K' F' G' ψ' F φ v hT1 hT2 hA2 hg₂ s₂ s₂ hs₂ hs₂ rfl a₂ b₂ ha₂
    (adapted_of_le' p K' F' φ' G' ψ' F φ v hPC hvc U s₂ hs₂ b₂ (Nat.le_add_left L₂ L₁) hb₂)
  have e₃ := wit_unique I p K' F' G' ψ' F φ v hT1 hT2 hA2
    (good_of_le I p K' F' φ' G' ψ' hPC hg₁ (Nat.le_add_right L₁ L₂)) s₁ s₂ hs₁ hs₂ hk b₁ b₂ hb₁ hb₂
  rw [e₁, e₃, ← e₂]

section Defu

variable (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)

include hψ'k hG'c hG'q in

def lvl (U : P.affineOpens) (k : ℕ) : ℕ := k + (good_exists I p K' F' G' ψ' hψ'k hG'c hG'q U k).choose

theorem good_lvl (U : P.affineOpens) (k : ℕ) :
    Good I p K' F' G' ψ' U k (lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) :=
  (good_exists I p K' F' G' ψ' hψ'k hG'c hG'q U k).choose_spec

def thr (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) : ∀ n, (F n).obj U.1 := (hT1 U k y).choose

theorem thr_thread (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) (n : ℕ) :
    (φ n).app U (thr F φ hT1 U k y (n + 1)) = thr F φ hT1 U k y n := (hT1 U k y).choose_spec.1 n

theorem thr_at (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) : thr F φ hT1 U k y k = y :=
  (hT1 U k y).choose_spec.2

def adp (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) : (cechPushforward p q K' G').obj U.1 :=
  (hA2 U (lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) (thr F φ hT1 U k y) (thr_thread F φ hT1 U k y)).choose

theorem adp_spec (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) :
    ((ψ' (lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k)).cechPushforward p q K').app U
        (adp I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y) =
      (v (lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k)).app U
        (thr F φ hT1 U k y (lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k)) :=
  (hA2 U (lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) (thr F φ hT1 U k y) (thr_thread F φ hT1 U k y)).choose_spec

def uFun (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) : (trunc I (cechPushforward p q K' G') k).obj U.1 :=
  (truncProj I (cechPushforward p q K' G') k).app U.1 (adp I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y)

include hPC hvc hT2 in

theorem uFun_eq {U : P.affineOpens} {k : ℕ} (y : (F k).obj U.1) {L : ℕ} (hg : Good I p K' F' G' ψ' U k L)
    (s : ∀ n, (F n).obj U.1) (hs : ∀ n, (φ n).app U (s (n + 1)) = s n) (hsk : s k = y)
    (a : (cechPushforward p q K' G').obj U.1)
    (ha : ((ψ' L).cechPushforward p q K').app U a = (v L).app U (s L)) :
    uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y =
      (truncProj I (cechPushforward p q K' G') k).app U.1 a :=
  wit_compare I p K' F' φ' G' ψ' F φ v hPC hvc hT1 hT2 hA2 (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) hg
    (thr F φ hT1 U k y) s (thr_thread F φ hT1 U k y) hs ((thr_at F φ hT1 U k y).trans hsk.symm)
    _ a (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y) ha

end Defu

section Algebra

omit hψ'k hPC hvc hT1 hT2 hA2

theorem thread_add {U : P.affineOpens} {s s' : ∀ n, (F n).obj U.1}
    (hs : ∀ n, (φ n).app U (s (n + 1)) = s n) (hs' : ∀ n, (φ n).app U (s' (n + 1)) = s' n) :
    ∀ n, (φ n).app U ((s + s') (n + 1)) = (s + s') n := fun n => by
  rw [Pi.add_apply, Pi.add_apply, map_add, hs, hs']

theorem thread_smul {U : P.affineOpens} {s : ∀ n, (F n).obj U.1}
    (hs : ∀ n, (φ n).app U (s (n + 1)) = s n) (r : A) :
    ∀ n, (φ n).app U ((r • s) (n + 1)) = (r • s) n := fun n => by
  rw [Pi.smul_apply, Pi.smul_apply, LinearMap.map_smul, hs]

theorem thread_smulΓ {U : P.affineOpens} {s : ∀ n, (F n).obj U.1}
    (hs : ∀ n, (φ n).app U (s (n + 1)) = s n) (g : Γ(P, U.1)) :
    ∀ n, (φ n).app U ((fun m => g • s m) (n + 1)) = (fun m => g • s m) n := fun n => by
  show (φ n).app U (g • s (n + 1)) = g • s n
  rw [(φ n).app_smul, hs]

theorem thread_res {U U' : P.affineOpens} (h : U.1 ≤ U'.1) {s : ∀ n, (F n).obj U'.1}
    (hs : ∀ n, (φ n).app U' (s (n + 1)) = s n) :
    ∀ n, (φ n).app U ((fun m => (F m).res h (s m)) (n + 1)) = (fun m => (F m).res h (s m)) n := fun n => by
  show (φ n).app U ((F (n + 1)).res h (s (n + 1))) = (F n).res h (s n)
  rw [(φ n).naturality_apply, hs]

theorem adapted_add {U : P.affineOpens} {L : ℕ} {a a' : (cechPushforward p q K' G').obj U.1} {z z' : (F L).obj U.1}
    (ha : ((ψ' L).cechPushforward p q K').app U a = (v L).app U z)
    (ha' : ((ψ' L).cechPushforward p q K').app U a' = (v L).app U z') :
    ((ψ' L).cechPushforward p q K').app U (a + a') = (v L).app U (z + z') := by
  rw [map_add, map_add, ha, ha']

theorem adapted_smul {U : P.affineOpens} {L : ℕ} {a : (cechPushforward p q K' G').obj U.1} {z : (F L).obj U.1}
    (ha : ((ψ' L).cechPushforward p q K').app U a = (v L).app U z) (r : A) :
    ((ψ' L).cechPushforward p q K').app U (r • a) = (v L).app U (r • z) := by
  rw [LinearMap.map_smul, LinearMap.map_smul, ha]

theorem adapted_smulΓ {U : P.affineOpens} {L : ℕ} {a : (cechPushforward p q K' G').obj U.1} {z : (F L).obj U.1}
    (ha : ((ψ' L).cechPushforward p q K').app U a = (v L).app U z) (g : Γ(P, U.1)) :
    ((ψ' L).cechPushforward p q K').app U (g • a) = (v L).app U (g • z) := by
  rw [AffHom.app_smul, AffHom.app_smul, ha]

theorem adapted_res {U U' : P.affineOpens} (h : U.1 ≤ U'.1) {L : ℕ} {a : (cechPushforward p q K' G').obj U'.1}
    {z : (F L).obj U'.1} (ha : ((ψ' L).cechPushforward p q K').app U' a = (v L).app U' z) :
    ((ψ' L).cechPushforward p q K').app U ((cechPushforward p q K' G').res h a) = (v L).app U ((F L).res h z) := by
  rw [AffHom.naturality_apply, AffHom.naturality_apply, ha]

end Algebra

section Props

variable (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)

include hPC hvc hT2 in
theorem uFun_add (U : P.affineOpens) (k : ℕ) (y₁ y₂ : (F k).obj U.1) :
    uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k (y₁ + y₂) =
      uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y₁ + uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y₂ := by
  rw [uFun_eq I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q (y₁ + y₂)
    (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) _
    (thread_add F φ (thr_thread F φ hT1 U k y₁) (thr_thread F φ hT1 U k y₂))
    (by rw [Pi.add_apply, thr_at, thr_at]) _
    (adapted_add p K' F' G' ψ' F v (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y₁)
      (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y₂))]
  exact map_add _ _ _

include hPC hvc hT2 in
theorem uFun_smul (U : P.affineOpens) (k : ℕ) (r : A) (y : (F k).obj U.1) :
    uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k (r • y) =
      r • uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y := by
  rw [uFun_eq I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q (r • y)
    (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) _
    (thread_smul F φ (thr_thread F φ hT1 U k y) r) (by rw [Pi.smul_apply, thr_at]) _
    (adapted_smul p K' F' G' ψ' F v (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y) r)]
  exact LinearMap.map_smul _ _ _

include hPC hvc hT2 in
theorem uFun_smulΓ (U : P.affineOpens) (k : ℕ) (g : Γ(P, U.1)) (y : (F k).obj U.1) :
    uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k (g • y) =
      g • uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y := by
  rw [uFun_eq I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q (g • y)
    (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) (fun m => g • thr F φ hT1 U k y m)
    (thread_smulΓ F φ (thr_thread F φ hT1 U k y) g) (by show g • thr F φ hT1 U k y k = g • y; rw [thr_at]) _
    (adapted_smulΓ p K' F' G' ψ' F v (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y) g)]
  exact (truncProj I (cechPushforward p q K' G') k).app_smul U.1 g _

include hPC hvc hT2 in

theorem uFun_res {U U' : P.affineOpens} (h : U.1 ≤ U'.1) (k : ℕ) (y : (F k).obj U'.1) :
    uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k ((F k).res h y) =
      (trunc I (cechPushforward p q K' G') k).res h (uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U' k y) := by

  set L := lvl I p K' F' G' ψ' hψ'k hG'c hG'q U' k + lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k with hL
  obtain ⟨b, hb⟩ := hA2 U' L (thr F φ hT1 U' k y) (thr_thread F φ hT1 U' k y)
  have e' : uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U' k y =
      (truncProj I (cechPushforward p q K' G') k).app U'.1 b :=
    uFun_eq I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q y
      (good_of_le I p K' F' φ' G' ψ' hPC (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U' k) (Nat.le_add_right _ _))
      _ (thr_thread F φ hT1 U' k y) (thr_at F φ hT1 U' k y) b hb
  have e : uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k ((F k).res h y) =
      (truncProj I (cechPushforward p q K' G') k).app U.1 ((cechPushforward p q K' G').res h b) :=
    uFun_eq I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q ((F k).res h y)
      (good_of_le I p K' F' φ' G' ψ' hPC (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k) (Nat.le_add_left _ _))
      (fun m => (F m).res h (thr F φ hT1 U' k y m)) (thread_res F φ h (thr_thread F φ hT1 U' k y))
      (by show (F k).res h (thr F φ hT1 U' k y k) = (F k).res h y; rw [thr_at]) _
      (adapted_res p K' F' G' ψ' F v h hb)
  rw [e, e', (truncProj I (cechPushforward p q K' G') k).naturality_apply h b]

include hPC hvc hT2 in

theorem uFun_compat (U : P.affineOpens) (k : ℕ) (y : (F (k + 1)).obj U.1) :
    (truncTrans I (cechPushforward p q K' G') k).app U.1 (uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U (k + 1) y) =
      uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k ((φ k).app U y) := by
  rw [uFun_eq I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q ((φ k).app U y)
    (good_of_succ_k I p K' F' G' ψ' (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U (k + 1)))
    (thr F φ hT1 U (k + 1) y) (thr_thread F φ hT1 U (k + 1) y) (by rw [← thr_thread F φ hT1 U (k + 1) y k, thr_at])
    _ (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U (k + 1) y)]
  exact LinearMap.congr_fun (truncTrans_comp_truncProj I (cechPushforward p q K' G') k U.1) _

include hPC hvc in

theorem uFun_pin (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) :
    (nu I p K' F' G' ψ' hψ'k k).app U (uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y) = (v k).app U y := by
  have h := adapted_of_le' p K' F' φ' G' ψ' F φ v hPC hvc U (thr F φ hT1 U k y) (thr_thread F φ hT1 U k y)
    (adp I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y)
    (good_lvl I p K' F' G' ψ' hψ'k hG'c hG'q U k).1 (adp_spec I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y)
  rw [thr_at] at h
  exact (LinearMap.congr_fun (nu_comp_truncProj I p K' F' G' ψ' hψ'k k U) _).trans h

def uHom (k : ℕ) : AffHom (F k) (trunc I (cechPushforward p q K' G') k) where
  app U :=
    { toFun := uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k
      map_add' := uFun_add I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q U k
      map_smul' := uFun_smul I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q U k }
  app_smul U g y := uFun_smulΓ I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q U k g y
  naturality h := LinearMap.ext fun y => uFun_res I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q h k y

theorem uHom_app (k : ℕ) (U : P.affineOpens) (y : (F k).obj U.1) :
    (uHom I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q k).app U y =
      uFun I p K' F' G' ψ' hψ'k F φ v hT1 hA2 hG'c hG'q U k y := rfl

theorem uHom_compat (k : ℕ) (U : P.affineOpens) :
    (truncTrans I (cechPushforward p q K' G') k).app U.1 ∘ₗ
        (uHom I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q (k + 1)).app U =
      (uHom I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q k).app U ∘ₗ (φ k).app U :=
  LinearMap.ext fun y => uFun_compat I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q U k y

theorem uHom_pin (k : ℕ) (U : P.affineOpens) :
    (nu I p K' F' G' ψ' hψ'k k).app U ∘ₗ (uHom I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hT2 hA2 hG'c hG'q k).app U =
      (v k).app U :=
  LinearMap.ext fun y => uFun_pin I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc hT1 hA2 hG'c hG'q U k y

end Props

end U

end AlgebraicGeometry.OModulePresheaf.C2Head

end

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper.AlgebraicGeometry"
open AlgebraicGeometry.OModulePresheaf.C2Head

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsProper p] (K' : V'.OrderedAffineCover)
    (F' : ℕ → OModulePresheaf (p ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (G' : OModulePresheaf (p ≫ q)) (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)
    (ψ' : ∀ k, OModulePresheaf.AffHom G' (F' k))
    (hψ's : ∀ (k : ℕ) (V : V'.affineOpens), Function.Surjective ((ψ' k).app V))
    (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
      LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)
    (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward p q K' (F' k)))
    (hvc : ∀ (k : ℕ) (U : P.affineOpens),
      ((φ' k).cechPushforward p q K').app U ∘ₗ (v (k + 1)).app U = (v k).app U ∘ₗ (φ k).app U) :
    (OModulePresheaf.cechPushforward p q K' G').IsCoherent ∧
    (OModulePresheaf.cechPushforward p q K' G').IsQuasicoherent ∧
    ∃ (Ps : ℕ → OModulePresheaf q) (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
      (ψP : ∀ k, OModulePresheaf.AffHom (OModulePresheaf.cechPushforward p q K' G') (Ps k))
      (ν : ∀ k, OModulePresheaf.AffHom (Ps k) (OModulePresheaf.cechPushforward p q K' (F' k)))
      (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k)),
      (∀ k, (Ps k).IsCoherent) ∧ (∀ k, (Ps k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψP k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψP k).app U)
          = I ^ (k + 1) • (⊤ : Submodule A ((OModulePresheaf.cechPushforward p q K' G').obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (ψP (k + 1)).app U = (ψP k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        ((φ' k).cechPushforward p q K').app U ∘ₗ (ν (k + 1)).app U = (ν k).app U ∘ₗ (π k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        (ν k).app U ∘ₗ (ψP k).app U = ((ψ' k).cechPushforward p q K').app U) ∧
      (∀ (U : P.affineOpens) (k : ℕ), ∃ c : ℕ,
        LinearMap.ker ((ν (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + c)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (φ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ν k).app U ∘ₗ (u k).app U = (v k).app U) := by
  have hGPc : (OModulePresheaf.cechPushforward p q K' G').IsCoherent :=
    AlgebraicGeometry.OModulePresheaf.isCoherent_cechPushforward_of_isProper q p K' G' hG'c hG'q
  have hGPq : (OModulePresheaf.cechPushforward p q K' G').IsQuasicoherent :=
    AlgebraicGeometry.OModulePresheaf.isQuasicoherent_cechPushforward_of_isSeparated q p K' G' hG'q
  have hPC := psi_cechPushforward_compat p K' F' G' ψ' φ' hψ'c
  refine ⟨hGPc, hGPq, fun k => trunc I (OModulePresheaf.cechPushforward p q K' G') k,
    fun k => (truncTrans I (OModulePresheaf.cechPushforward p q K' G') k).toAffHom,
    fun k => (truncProj I (OModulePresheaf.cechPushforward p q K' G') k).toAffHom,
    fun k => nu I p K' F' G' ψ' hψ'k k,
    fun k => uHom I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc
      (fun U k y => exists_isThread F φ hφs U k y)
      (fun U k s s' hs hs' h => IsThread.sub_mem F φ I hφs hφk hs hs' h)
      (fun U L s hs => exists_adapted p K' F' G' ψ' F v I φ' hG'c hG'q hψ's hψ'k hψ'c φ hvc U L s hs) hG'c hG'q k,
    fun k => isCoherent_trunc I _ hGPc k, fun k => isQuasicoherent_trunc I _ hGPq k,
    fun k U => truncTrans_surjective I _ k U.1, fun k U => ker_truncTrans I _ k U.1,
    fun k U => truncProj_surjective I _ k U.1, fun k U => ker_truncProj I _ k U.1,
    fun k U => truncTrans_comp_truncProj I _ k U.1,
    fun k U => nu_compat I p K' F' G' ψ' hψ'k φ' hψ'c k U,
    fun k U => nu_comp_truncProj I p K' F' G' ψ' hψ'k k U,
    fun U k => nu_shift I p K' F' G' ψ' hψ'k hG'c hG'q U k,
    fun k U => uHom_compat I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc _ _ _ hG'c hG'q k U,
    fun k U => uHom_pin I p K' F' φ' G' ψ' hψ'k F φ v hPC hvc _ _ _ hG'c hG'q k U⟩

end S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper (solution)
