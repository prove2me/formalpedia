-- Prove2me | Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
-- name    : ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:47.420341+00:00
-- url     : https://prove2.me/theorems/b547a023-ed10-4d63-8a98-1d05aca22d32
-- title:
--   Continuous Const SMul Quotient
-- statement:
--   Definitions and structural lemmas for Continuous Const SMul Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ContinuousConstSMulQuotient.lean

import Definitions.Def_ReciprocityTheory_GaloisValuations_SeparatedDvrSecondCohomologyMem
import Theorems.Thm_ReciprocityTheory_Gal_mem_riemannRochSpace_iff_regularAt_everywhere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Gal
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)
section Cup
variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  {P : Type*} [AddCommGroup P] [Module R P] [TopologicalSpace P]
  [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
  (rho' : Representation R G M') (rhoP : Representation R G P)
  (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
  (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
section CupZ11
include hb hbe
def cupCocycleZ1Z1 (hrho' : ContAction rho') : Z1 rho →ₗ[R] Z1 rho' →ₗ[R] Z2 rhoP :=
  LinearMap.mk₂ R
    (fun x y => ⟨fun p => b (x.1 p.1) (rho' p.1 (y.1 p.2)),
      hb.comp ((x.2.1.comp continuous_fst).prodMk
        (hrho'.comp (continuous_fst.prodMk (y.2.1.comp continuous_snd)))),
      fun g h k => by
        have hx := x.2.2 g h
        have hy := y.2.2 h k
        dsimp only
        rw [← hbe, hx, hy, map_mul, Module.End.mul_apply]
        simp only [map_add, LinearMap.add_apply]
        abel⟩)
    (fun x x' y => Subtype.ext (funext fun p => by simp))
    (fun r x y => Subtype.ext (funext fun p => by simp))
    (fun x y y' => Subtype.ext (funext fun p => by simp))
    (fun r x y => Subtype.ext (funext fun p => by simp))
@[simp] theorem cupCocycleZ1Z1_apply (hrho' : ContAction rho') (x : Z1 rho) (y : Z1 rho') (g h : G) :
    (cupCocycleZ1Z1 rho rho' rhoP b hb hbe hrho' x y).1 (g, h) = b (x.1 g) (rho' g (y.1 h)) := rfl
def cupProductH1H1 (hrho' : ContAction rho') : H1 rho →ₗ[R] H1 rho' →ₗ[R] H2 rhoP :=
  LinearMap.liftQ₂ _ _ ((cupCocycleZ1Z1 rho rho' rhoP b hb hbe hrho').compr₂ (Submodule.mkQ _))
    (fun x hx => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hx
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun y => ?_
      rw [LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun h => b m (y.1 h), hb.comp (continuous_const.prodMk y.2.1), ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      have e := hm g
      simp only [Submodule.coe_subtype] at e
      simp only [d1_apply, Submodule.coe_subtype, cupCocycleZ1Z1_apply, e, ← hbe, y.2.2 g h, map_add,
        map_sub, LinearMap.sub_apply]
      abel)
    (fun y hy => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 rho' _).1 hy
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.flip_apply, LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => -b (x.1 g) (rho' g m),
        (hb.comp (x.2.1.prodMk (hrho'.comp (continuous_id.prodMk continuous_const)))).neg, ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      have e := hm h
      simp only [Submodule.coe_subtype] at e
      simp only [d1_apply, Submodule.coe_subtype, cupCocycleZ1Z1_apply, e, map_neg, ← hbe, x.2.2 g h,
        map_mul, Module.End.mul_apply, map_add, map_sub, LinearMap.add_apply]
      abel)
end CupZ11
include hb hbe
def cupCocycleH0Z2 : H0 rho →ₗ[R] Z2 rho' →ₗ[R] Z2 rhoP :=
  LinearMap.mk₂ R
    (fun m f => ⟨fun p => b m.1 (f.1 p), hb.comp (continuous_const.prodMk f.2.1),
      fun g h k => by
        have e := congrArg (b m.1) (f.2.2 g h k)
        simp only [map_sub, map_add, map_zero] at e
        rw [← hbe, (mem_riemannRochSpace_iff_regularAt_everywhere rho m.1).1 m.2 g]
        exact e⟩)
    (fun m m' f => Subtype.ext (funext fun p => by simp))
    (fun r m f => Subtype.ext (funext fun p => by simp))
    (fun m f f' => Subtype.ext (funext fun p => by simp))
    (fun r m f => Subtype.ext (funext fun p => by simp))
@[simp] theorem cupCocycleH0Z2_apply (m : H0 rho) (f : Z2 rho') (p : G × G) :
    (cupCocycleH0Z2 rho rho' rhoP b hb hbe m f).1 p = b m.1 (f.1 p) := rfl
def cupProductH0H2 : H0 rho →ₗ[R] H2 rho' →ₗ[R] H2 rhoP :=
  (Submodule.liftQ _ ((cupCocycleH0Z2 rho rho' rhoP b hb hbe).compr₂ (Submodule.mkQ _)).flip
    (fun f hf => by
      obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho' _).1 hf
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun m => ?_
      rw [LinearMap.flip_apply, LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => b m.1 (c g), hb.comp (continuous_const.prodMk hc), ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      have e := congrFun hcf (g, h)
      simp only [Submodule.coe_subtype] at e
      simp only [d1_apply, Submodule.coe_subtype, cupCocycleH0Z2_apply, ← e, ← hbe,
        (mem_riemannRochSpace_iff_regularAt_everywhere rho m.1).1 m.2 g, map_add, map_sub])).flip
def cupCocycleZ2H0 : Z2 rho →ₗ[R] H0 rho' →ₗ[R] Z2 rhoP :=
  LinearMap.mk₂ R
    (fun f m => ⟨fun p => b (f.1 p) m.1, hb.comp (f.2.1.prodMk continuous_const),
      fun g h k => by
        have e := congrArg (b.flip m.1) (f.2.2 g h k)
        simp only [map_sub, map_add, map_zero, LinearMap.flip_apply] at e
        rw [← (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 g, hbe, (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 g] at e
        exact e⟩)
    (fun f f' m => Subtype.ext (funext fun p => by simp))
    (fun r f m => Subtype.ext (funext fun p => by simp))
    (fun f m m' => Subtype.ext (funext fun p => by simp))
    (fun r f m => Subtype.ext (funext fun p => by simp))
@[simp] theorem cupCocycleZ2H0_apply (f : Z2 rho) (m : H0 rho') (p : G × G) :
    (cupCocycleZ2H0 rho rho' rhoP b hb hbe f m).1 p = b (f.1 p) m.1 := rfl
def cupProductH2H0 : H2 rho →ₗ[R] H0 rho' →ₗ[R] H2 rhoP :=
  Submodule.liftQ _ ((cupCocycleZ2H0 rho rho' rhoP b hb hbe).compr₂ (Submodule.mkQ _))
    (fun f hf => by
      obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho _).1 hf
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun m => ?_
      rw [LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => b (c g) m.1, hb.comp (hc.prodMk continuous_const), ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      have e := congrFun hcf (g, h)
      simp only [Submodule.coe_subtype] at e
      have hm := (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 g
      simp only [d1_apply, Submodule.coe_subtype, cupCocycleZ2H0_apply, ← e, map_add, map_sub,
        LinearMap.add_apply, LinearMap.sub_apply]
      rw [← hbe, hm])
end Cup
section Local
variable {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (phi : ∀ i, D i →* G) (hphi : ∀ i, Continuous (phi i))
abbrev LocCond := ∀ i, Submodule R (H1 (rho.comp (phi i)))
def Sel (L : LocCond rho phi) : Submodule R (H1 rho) :=
  ⨅ i, (L i).comap (resH1 rho (phi i) (hphi i))
def Sha1 : Submodule R (H1 rho) := ⨅ i, LinearMap.ker (resH1 rho (phi i) (hphi i))
def Sha2 : Submodule R (H2 rho) := ⨅ i, LinearMap.ker (resH2 rho (phi i) (hphi i))
end Local
section Inertia
variable {D : Type*} [Group D] [TopologicalSpace D] (rhoD : Representation R D M)
  (J : Subgroup D)
def H1ur : Submodule R (H1 rhoD) :=
  LinearMap.ker (resH1 rhoD J.subtype continuous_subtype_val)
variable (Mplus : Submodule R M) (hMplus : ∀ g, Mplus ≤ Mplus.comap (rhoD g))
theorem continuous_mkQ : Continuous (Mplus.mkQ) := by
  first
  | exact continuous_quot_mk
  | exact continuous_coinduced_rng
instance continuousConstSMul_quotient (N : Submodule R M) : ContinuousConstSMul R (M ⧸ N) :=
  ⟨fun c => by
    rw [(Submodule.isQuotientMap_mkQ N).continuous_iff]
    exact (Submodule.isQuotientMap_mkQ N).continuous.comp (continuous_const_smul c)⟩
def toQuotientH1 : H1 rhoD →ₗ[R] H1 (rhoD.quotient Mplus hMplus) :=
  mapH1 rhoD (rhoD.quotient Mplus hMplus) Mplus.mkQ (continuous_mkQ Mplus) (fun _ _ => rfl)
def greenbergSelmer : Submodule R (H1 rhoD) :=
  LinearMap.ker ((resH1 (rhoD.quotient Mplus hMplus) J.subtype continuous_subtype_val).comp
    (toQuotientH1 rhoD Mplus hMplus))
def strictGreenbergSelmer : Submodule R (H1 rhoD) := LinearMap.ker (toQuotientH1 rhoD Mplus hMplus)
end Inertia
end
end ReciprocityTheory.Gal


