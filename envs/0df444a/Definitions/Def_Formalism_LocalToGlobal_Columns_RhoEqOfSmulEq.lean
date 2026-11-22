-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
-- name    : Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:51:47.845048+00:00
-- url     : https://prove2.me/theorems/ba01b342-d4a4-4f2c-b4cb-46865159cf63
-- title:
--   Rho Eq Of Smul Eq
-- statement:
--   Definitions and structural lemmas for Rho Eq Of Smul Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
structure GSD (K : Type) [Field K] [NumberField K] [StarRing K] where

  G : Type
  [grpG : Group G]

  D : Type
  [actD : MulAction G D]

  V : Type
  [addV : AddCommGroup V]
  [modV : Module K V]
  [modOV : Module (𝓞 K) V]
  [towV : IsScalarTower (𝓞 K) K V]

  ιV : Type
  [finιV : Fintype ιV]
  [decιV : DecidableEq ιV]
  bV : Basis ιV K V

  pair : V →ₗ⋆[K] V →ₗ[K] K

  ρ : G →* Module.End K V

  Nab : D → Submodule (𝓞 K) V

  Del : D → Submodule (𝓞 K) V
attribute [instance] GSD.grpG GSD.actD GSD.addV GSD.modV GSD.modOV GSD.towV GSD.finιV GSD.decιV
namespace GSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)
abbrev Cl : Type := MulAction.orbitRel.Quotient S.G S.D
def cls (d : S.D) : S.Cl := Quotient.mk (MulAction.orbitRel S.G S.D) d
structure Sec where
  rep : S.Cl → S.D
  spec : ∀ c, S.cls (rep c) = c
def outSec : S.Sec where
  rep := Quotient.out
  spec := fun c => Quotient.out_eq c
theorem cls_eq_iff (d e : S.D) : S.cls d = S.cls e ↔ ∃ g : S.G, g • e = d := by
  unfold cls
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
theorem cls_smul (g : S.G) (d : S.D) : S.cls (g • d) = S.cls d := by
  exact (S.cls_eq_iff _ _).2 ⟨g, rfl⟩
variable {S} in
theorem Sec.exists_mv (s : S.Sec) (d : S.D) : ∃ g : S.G, g • s.rep (S.cls d) = d := by
  exact (S.cls_eq_iff d (s.rep (S.cls d))).1 (s.spec _).symm
variable {S} in

def Sec.mv (s : S.Sec) (d : S.D) : S.G := (s.exists_mv d).choose
variable {S} in
theorem Sec.mv_smul (s : S.Sec) (d : S.D) : s.mv d • s.rep (S.cls d) = d := by
  exact (s.exists_mv d).choose_spec
structure Ok : Prop where
  fin_orb : Finite S.Cl
  fin_stab : ∀ d : S.D, Finite (MulAction.stabilizer S.G d)
  nab_smul : ∀ (g : S.G) (d : S.D), S.Nab (g • d) = (S.Nab d).map ((S.ρ g).restrictScalars (𝓞 K))
  del_smul : ∀ (g : S.G) (d : S.D), S.Del (g • d) = (S.Del d).map ((S.ρ g).restrictScalars (𝓞 K))
  inv : ∀ (g : S.G) (x y : S.V), S.pair (S.ρ g x) (S.ρ g y) = S.pair x y
variable {S} in

@[reducible] def Ok.fintypeCl (h : S.Ok) : Fintype S.Cl := @Fintype.ofFinite _ h.fin_orb
variable {S} in

@[reducible] def Ok.fintypeStab (h : S.Ok) (d : S.D) : Fintype (MulAction.stabilizer S.G d) :=
  @Fintype.ofFinite _ (h.fin_stab d)
def EqFun : Submodule K (S.D → S.V) where
  carrier := {φ | ∀ (g : S.G) (d : S.D), φ (g • d) = S.ρ g (φ d)}
  add_mem' := by
    intro φ ψ hφ hψ g d
    simp only [Pi.add_apply, map_add, hφ g d, hψ g d]
  zero_mem' := by
    intro g d
    simp
  smul_mem' := by
    intro a φ hφ g d
    simp only [Pi.smul_apply, map_smul, hφ g d]
theorem mem_EqFun (φ : S.D → S.V) : φ ∈ S.EqFun ↔ ∀ (g : S.G) (d : S.D), φ (g • d) = S.ρ g (φ d) := by
  exact Iff.rfl
def intOf (N : S.D → Submodule (𝓞 K) S.V) : Submodule (𝓞 K) S.EqFun where
  carrier := {φ | ∀ d, (φ : S.D → S.V) d ∈ N d}
  add_mem' := by
    intro φ ψ hφ hψ d
    exact (N d).add_mem (hφ d) (hψ d)
  zero_mem' := by
    intro d
    exact (N d).zero_mem
  smul_mem' := by
    intro a φ hφ d
    exact (N d).smul_mem a (hφ d)
def intNab : Submodule (𝓞 K) S.EqFun := S.intOf S.Nab
def intDel : Submodule (𝓞 K) S.EqFun := S.intOf S.Del
@[reducible] def toCSDOf (h : S.Ok) (s : S.Sec) : CSD K where
  Cl := S.Cl
  finCl := h.fintypeCl
  V := S.V
  ιV := S.ιV
  bV := S.bV
  pair := S.pair
  Gam := fun c => MulAction.stabilizer S.G (s.rep c)
  grpGam := fun _ => inferInstance
  finGam := fun c => h.fintypeStab (s.rep c)
  ρ := fun c => S.ρ.comp (MulAction.stabilizer S.G (s.rep c)).subtype
  Nab := fun c => S.Nab (s.rep c)
  Del := fun c => S.Del (s.rep c)
@[reducible] def toCSD (h : S.Ok) : CSD K := S.toCSDOf h S.outSec
theorem rho_eq_of_smul_eq (h : S.Ok) (s : S.Sec) (f : (S.toCSDOf h s).Forms) (c : S.Cl) (g₁ g₂ : S.G)
    (e : g₁ • s.rep c = g₂ • s.rep c) :
    S.ρ g₁ ((f.1 : S.Cl → S.V) c) = S.ρ g₂ ((f.1 : S.Cl → S.V) c) := by
  have hmem : g₂⁻¹ * g₁ ∈ MulAction.stabilizer S.G (s.rep c) := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, e, ← mul_smul, inv_mul_cancel, one_smul]
  have hf : S.ρ (g₂⁻¹ * g₁) ((f.1 : S.Cl → S.V) c) = (f.1 : S.Cl → S.V) c := f.2 c ⟨_, hmem⟩
  calc S.ρ g₁ ((f.1 : S.Cl → S.V) c) = S.ρ (g₂ * (g₂⁻¹ * g₁)) ((f.1 : S.Cl → S.V) c) := by
        rw [mul_inv_cancel_left]
    _ = S.ρ g₂ (S.ρ (g₂⁻¹ * g₁) ((f.1 : S.Cl → S.V) c)) := by
        rw [map_mul, Module.End.mul_apply]
    _ = S.ρ g₂ ((f.1 : S.Cl → S.V) c) := by rw [hf]
def resOf (h : S.Ok) (s : S.Sec) : S.EqFun ≃ₗ[K] (S.toCSDOf h s).Forms where
  toFun φ := ⟨fun c => (φ : S.D → S.V) (s.rep c), fun c γ => by
    have h1 := φ.2 ((γ : MulAction.stabilizer S.G (s.rep c)) : S.G) (s.rep c)
    have h2 : ((γ : MulAction.stabilizer S.G (s.rep c)) : S.G) • s.rep c = s.rep c :=
      (γ : MulAction.stabilizer S.G (s.rep c)).2
    rw [h2] at h1
    exact h1.symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨fun d => S.ρ (s.mv d) ((f.1 : S.Cl → S.V) (S.cls d)), fun g d => by
    show S.ρ (s.mv (g • d)) ((f.1 : S.Cl → S.V) (S.cls (g • d))) =
      S.ρ g (S.ρ (s.mv d) ((f.1 : S.Cl → S.V) (S.cls d)))
    have h0 := s.mv_smul (g • d)
    rw [S.cls_smul g d] at h0 ⊢
    rw [← Module.End.mul_apply, ← map_mul]
    refine S.rho_eq_of_smul_eq h s f _ _ _ ?_
    rw [h0, mul_smul, s.mv_smul d]⟩
  left_inv φ := by
    apply Subtype.ext
    funext d
    show S.ρ (s.mv d) ((φ : S.D → S.V) (s.rep (S.cls d))) = (φ : S.D → S.V) d
    rw [← φ.2, s.mv_smul]
  right_inv f := by
    apply Subtype.ext
    funext c
    show S.ρ (s.mv (s.rep c)) ((f.1 : S.Cl → S.V) (S.cls (s.rep c))) = (f.1 : S.Cl → S.V) c
    have h0 := s.mv_smul (s.rep c)
    rw [s.spec c] at h0 ⊢
    have h1 := S.rho_eq_of_smul_eq h s f c (s.mv (s.rep c)) 1 (by rw [h0, one_smul])
    rw [h1, map_one, Module.End.one_apply]
def res (h : S.Ok) : S.EqFun ≃ₗ[K] (S.toCSD h).Forms := S.resOf h S.outSec
def ipOf (h : S.Ok) (s : S.Sec) (φ ψ : S.D → S.V) : K :=
  (S.toCSDOf h s).csum (fun c => φ (s.rep c)) (fun c => ψ (s.rep c))
def ip (h : S.Ok) (φ ψ : S.D → S.V) : K := S.ipOf h S.outSec φ ψ
structure Good (s : ℕ) : Prop where
  ok : S.Ok
  symm : S.pair.IsSymm
  nondeg : S.pair.Nondegenerate
  nab_lat : ∀ d, Submodule.IsLattice K (S.Nab d)
  del_le : ∀ d, S.Del d ≤ S.Nab d
  s_pos : 0 < s
  dual_le : ∀ d, ∀ y ∈ Formalism.HermitianLatticesTheory.dual S.pair (S.Nab d), (s : 𝓞 K) • y ∈ S.Del d
  del_dual : ∀ d, ∀ y ∈ S.Del d, (s : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual S.pair (S.Nab d)
def gramV : Matrix S.ιV S.ιV K := Matrix.of fun i j => S.pair (S.bV i) (S.bV j)
structure Rat : Prop where
  pair_rat : ∀ i j, S.gramV i j ∈ cmMax K
  act_rat : ∀ (g : S.G) i j, S.bV.repr (S.ρ g (S.bV j)) i ∈ cmMax K
  pos : ∀ v : InfinitePlace K, (S.gramV.map v.embedding).PosDef
end GSD
variable {K : Type} [Field K] [NumberField K] [StarRing K]
structure LocOp (S S' : GSD K) where

  tr : S'.G →* S.G

  ker : S'.D → S.D →₀ (S.V →ₗ[K] S'.V)

  equiv : ∀ (g : S'.G) (d' : S'.D) (d : S.D),
    ker (g • d') (tr g • d) = (S'.ρ g) ∘ₗ (ker d' d) ∘ₗ (S.ρ (tr g)⁻¹)
namespace LocOp
variable {S S' : GSD K} (A : LocOp S S')
def app (φ : S.D → S.V) (d' : S'.D) : S'.V := (A.ker d').sum fun d k => k (φ d)
theorem ker_smul (g : S'.G) (d' : S'.D) :
    A.ker (g • d') = (Finsupp.equivMapDomain (MulAction.toPerm (A.tr g)) (A.ker d')).mapRange
      (fun k => (S'.ρ g) ∘ₗ k ∘ₗ (S.ρ (A.tr g)⁻¹)) (by simp) := by
  ext d : 1
  rw [Finsupp.mapRange_apply, Finsupp.equivMapDomain_apply]
  have h := A.equiv g d' ((MulAction.toPerm (A.tr g)).symm d)
  have hd : A.tr g • (MulAction.toPerm (A.tr g)).symm d = d :=
    (MulAction.toPerm (A.tr g)).apply_symm_apply d
  rw [hd] at h
  exact h
theorem app_mem (φ : S.EqFun) : A.app φ ∈ S'.EqFun := by
  rw [GSD.mem_EqFun]
  intro g d'
  show (A.ker (g • d')).sum (fun d k => k ((φ : S.D → S.V) d)) =
    S'.ρ g ((A.ker d').sum fun d k => k ((φ : S.D → S.V) d))
  rw [A.ker_smul, Finsupp.sum_mapRange_index (by simp), Finsupp.sum_equivMapDomain, map_finsuppSum]
  refine Finsupp.sum_congr fun d _ => ?_
  simp only [LinearMap.comp_apply, MulAction.toPerm_apply]
  rw [(S.mem_EqFun _).1 φ.2, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]
def op : S.EqFun →ₗ[K] S'.EqFun where
  toFun φ := ⟨A.app φ, A.app_mem φ⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext d'
    show (A.ker d').sum (fun d k => k ((φ : S.D → S.V) d + (ψ : S.D → S.V) d)) = _
    simp only [map_add]
    exact Finsupp.sum_add
  map_smul' a φ := by
    apply Subtype.ext
    funext d'
    show (A.ker d').sum (fun d k => k (a • (φ : S.D → S.V) d)) =
      a • (A.ker d').sum (fun d k => k ((φ : S.D → S.V) d))
    simp only [map_smul]
    exact Finsupp.smul_sum.symm
def ofMap (tr : S'.G →* S.G) (p : S'.D → S.D) (T : S.V →ₗ[K] S'.V)
    (hp : ∀ g d', p (g • d') = tr g • p d') (hT : ∀ g x, T (S.ρ (tr g) x) = S'.ρ g (T x)) : LocOp S S' where
  tr := tr
  ker := fun d' => Finsupp.single (p d') T
  equiv := by
    classical
    intro g d' d
    have hc : (S'.ρ g) ∘ₗ T ∘ₗ (S.ρ (tr g)⁻¹) = T := by
      ext x
      simp only [LinearMap.comp_apply]
      rw [← hT, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hp, Finsupp.single_apply, Finsupp.single_apply]
    by_cases e : p d' = d
    · rw [if_pos e, if_pos (by rw [e]), hc]
    · rw [if_neg e, if_neg (fun e' => e (MulAction.injective (tr g) e'))]
      simp
open Classical in

def ofNbr (tr : S'.G →* S.G) (nb : S'.D → Finset S.D) (T : S.V →ₗ[K] S'.V)
    (hn : ∀ g d' d, tr g • d ∈ nb (g • d') ↔ d ∈ nb d') (hT : ∀ g x, T (S.ρ (tr g) x) = S'.ρ g (T x)) :
    LocOp S S' where
  tr := tr
  ker := fun d' => Finsupp.indicator (nb d') (fun _ _ => T)
  equiv := by
    intro g d' d
    have hc : (S'.ρ g) ∘ₗ T ∘ₗ (S.ρ (tr g)⁻¹) = T := by
      ext x
      simp only [LinearMap.comp_apply]
      rw [← hT, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [Finsupp.indicator_apply, Finsupp.indicator_apply]
    by_cases e : d ∈ nb d'
    · rw [dif_pos e, dif_pos ((hn g d' d).mpr e), hc]
    · rw [dif_neg e, dif_neg (fun e' => e ((hn g d' d).mp e'))]
      simp
end LocOp
structure ClsKer (S S' : GSD K) where

  k : S.D → S'.D → (S.V →ₗ[K] S'.V)

  equiv : ∀ (g : S.G) (g' : S'.G) (d : S.D) (d' : S'.D),
    k (g • d) (g' • d') = (S'.ρ g') ∘ₗ (k d d') ∘ₗ (S.ρ g⁻¹)
namespace ClsKer
variable {S S' : GSD K} (A : ClsKer S S')
def appOf (h : S.Ok) (s : S.Sec) (φ : S.D → S.V) (d' : S'.D) : S'.V :=
  letI := h.fintypeCl
  ∑ c : S.Cl, (((S.toCSDOf h s).wt c : K))⁻¹ • A.k (s.rep c) d' (φ (s.rep c))
def opOf (h : S.Ok) (s : S.Sec) : S.EqFun →ₗ[K] S'.EqFun where
  toFun φ := ⟨A.appOf h s φ, fun g' d' => by
    unfold appOf
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 := A.equiv 1 g' (s.rep c) d'
    rw [one_smul, inv_one, map_one] at h1
    rw [h1, map_smul]
    rfl⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext d'
    show A.appOf h s (fun d => (φ : S.D → S.V) d + (ψ : S.D → S.V) d) d' = A.appOf h s φ d' + A.appOf h s ψ d'
    unfold appOf
    simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' a φ := by
    apply Subtype.ext
    funext d'
    show A.appOf h s (fun d => a • (φ : S.D → S.V) d) d' = a • A.appOf h s φ d'
    unfold appOf
    simp only [map_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_comm]
def op (h : S.Ok) : S.EqFun →ₗ[K] S'.EqFun := A.opOf h S.outSec
def atReps (s : S.Sec) (s' : S'.Sec) : S.Cl → S'.Cl → (S.V →ₗ[K] S'.V) := fun c c' => A.k (s.rep c) (s'.rep c')
end ClsKer
structure GSD.Iso (S S' : GSD K) where
  eG : S.G ≃* S'.G
  eD : S.D ≃ S'.D
  eV : S.V ≃ₗ[K] S'.V
  smul : ∀ (g : S.G) (d : S.D), eD (g • d) = eG g • eD d
  rho : ∀ (g : S.G) (x : S.V), eV (S.ρ g x) = S'.ρ (eG g) (eV x)
  pair : ∀ x y : S.V, S'.pair (eV x) (eV y) = S.pair x y
  nab : ∀ d : S.D, S'.Nab (eD d) = (S.Nab d).map ((eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K))
  del : ∀ d : S.D, S'.Del (eD d) = (S.Del d).map ((eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K))
  rat : ∀ i j, S'.bV.repr (eV (S.bV j)) i ∈ cmMax K
  rat_symm : ∀ i j, S.bV.repr (eV.symm (S'.bV j)) i ∈ cmMax K
namespace GSD.Iso
variable {S S' : GSD K} (e : GSD.Iso S S')
def onForms : S.EqFun ≃ₗ[K] S'.EqFun where
  toFun φ := ⟨fun d' => e.eV ((φ : S.D → S.V) (e.eD.symm d')), fun g' d' => by
    have h1 : e.eD.symm (g' • d') = e.eG.symm g' • e.eD.symm d' := by
      rw [Equiv.symm_apply_eq, e.smul, MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]
    show e.eV ((φ : S.D → S.V) (e.eD.symm (g' • d'))) = S'.ρ g' (e.eV ((φ : S.D → S.V) (e.eD.symm d')))
    rw [h1, φ.2, e.rho, MulEquiv.apply_symm_apply]⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext d'
    exact map_add e.eV _ _
  map_smul' a φ := by
    apply Subtype.ext
    funext d'
    exact map_smul e.eV _ _
  invFun ψ := ⟨fun d => e.eV.symm ((ψ : S'.D → S'.V) (e.eD d)), fun g d => by
    show e.eV.symm ((ψ : S'.D → S'.V) (e.eD (g • d))) = S.ρ g (e.eV.symm ((ψ : S'.D → S'.V) (e.eD d)))
    rw [e.smul, ψ.2, LinearEquiv.symm_apply_eq, e.rho, LinearEquiv.apply_symm_apply]⟩
  left_inv φ := by
    apply Subtype.ext
    funext d
    show e.eV.symm (e.eV ((φ : S.D → S.V) (e.eD.symm (e.eD d)))) = (φ : S.D → S.V) d
    rw [LinearEquiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv ψ := by
    apply Subtype.ext
    funext d'
    show e.eV (e.eV.symm ((ψ : S'.D → S'.V) (e.eD (e.eD.symm d')))) = (ψ : S'.D → S'.V) d'
    rw [LinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]
def onCl : S.Cl ≃ S'.Cl where
  toFun := Quotient.map' e.eD (by
    rintro a b ⟨g, rfl⟩
    exact ⟨e.eG g, (e.smul g b).symm⟩)
  invFun := Quotient.map' e.eD.symm (by
    rintro a b ⟨g, rfl⟩
    refine ⟨e.eG.symm g, ?_⟩
    show e.eG.symm g • e.eD.symm b = e.eD.symm (g • b)
    rw [Equiv.eq_symm_apply, e.smul, MulEquiv.apply_symm_apply, Equiv.apply_symm_apply])
  left_inv := by
    rintro ⟨a⟩
    show Quotient.mk'' (e.eD.symm (e.eD a)) = Quotient.mk'' a
    rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨a⟩
    show Quotient.mk'' (e.eD (e.eD.symm a)) = Quotient.mk'' a
    rw [Equiv.apply_symm_apply]
end GSD.Iso
@[reducible] def GSD.triv (K : Type) [Field K] [NumberField K] [StarRing K] (G D : Type) [Group G] [MulAction G D] : GSD K where
  G := G
  D := D
  V := K
  ιV := Unit
  bV := Basis.singleton Unit K
  pair := CSD.pairOne K
  ρ := 1
  Nab := fun _ => 1
  Del := fun _ => 1
namespace GSD
variable (K) (G D : Type) [Group G] [MulAction G D]
def trivOne : (triv K G D).EqFun := ⟨fun _ => (1 : K), fun _ _ => rfl⟩
end GSD
namespace GSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)
def csOf (h : S.Ok) (s : S.Sec) {M : Type} [AddCommGroup M] [Module K M] (F : S.D → M) : M :=
  letI := h.fintypeCl
  ∑ c : S.Cl, (((S.toCSDOf h s).wt c : K))⁻¹ • F (s.rep c)
end GSD
structure BiPair (S S' : GSD K) where

  tr : S'.G →* S.G

  p : S'.D → S.D

  B : S.V →ₗ[K] S'.V →ₗ[K] K
  hp : ∀ (g : S'.G) (d' : S'.D), p (g • d') = tr g • p d'
  inv : ∀ (g : S'.G) (x : S.V) (y : S'.V), B (S.ρ (tr g) x) (S'.ρ g y) = B x y
namespace BiPair
variable {S S' : GSD K} (P : BiPair S S')
def sumOf (h' : S'.Ok) (s' : S'.Sec) (φ : S.D → S.V) (ψ : S'.D → S'.V) : K :=
  S'.csOf h' s' fun d' => P.B (φ (P.p d')) (ψ d')
def formOf (h' : S'.Ok) (s' : S'.Sec) : S.EqFun →ₗ[K] S'.EqFun →ₗ[K] K :=
  LinearMap.mk₂ K (fun φ ψ => P.sumOf h' s' φ ψ)
    (by
      intro φ φ' ψ
      show S'.csOf h' s' (fun d' => P.B ((φ : S.D → S.V) (P.p d') + (φ' : S.D → S.V) (P.p d')) _) = _
      unfold sumOf GSD.csOf
      simp only [map_add, LinearMap.add_apply, smul_add, Finset.sum_add_distrib])
    (by
      intro a φ ψ
      show S'.csOf h' s' (fun d' => P.B (a • (φ : S.D → S.V) (P.p d')) _) = _
      unfold sumOf GSD.csOf
      simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum]
      exact Finset.sum_congr rfl fun c _ => smul_comm _ _ _)
    (by
      intro φ ψ ψ'
      show S'.csOf h' s' (fun d' => P.B _ ((ψ : S'.D → S'.V) d' + (ψ' : S'.D → S'.V) d')) = _
      unfold sumOf GSD.csOf
      simp only [map_add, smul_add, Finset.sum_add_distrib])
    (by
      intro a φ ψ
      show S'.csOf h' s' (fun d' => P.B _ (a • (ψ : S'.D → S'.V) d')) = _
      unfold sumOf GSD.csOf
      simp only [map_smul, Finset.smul_sum]
      exact Finset.sum_congr rfl fun c _ => smul_comm _ _ _)
end BiPair
structure GFam (K : Type) [Field K] [NumberField K] [StarRing K] where

  β : Type
  [finβ : Fintype β]
  [decβ : DecidableEq β]

  V : Type
  [addV : AddCommGroup V]
  [modV : Module K V]
  [modOV : Module (𝓞 K) V]
  [towV : IsScalarTower (𝓞 K) K V]
  ιV : Type
  [finιV : Fintype ιV]
  [decιV : DecidableEq ιV]
  bV : Basis ιV K V

  pair : V →ₗ⋆[K] V →ₗ[K] K

  G : β → Type
  [grpG : ∀ b, Group (G b)]

  D : β → Type
  [actD : ∀ b, MulAction (G b) (D b)]

  ρ : ∀ b, G b →* Module.End K V
  Nab : ∀ b, D b → Submodule (𝓞 K) V
  Del : ∀ b, D b → Submodule (𝓞 K) V
attribute [instance] GFam.finβ GFam.decβ GFam.addV GFam.modV GFam.modOV GFam.towV GFam.finιV GFam.decιV GFam.grpG
  GFam.actD
namespace GFam
variable (F : GFam K)
@[reducible] def mem (b : F.β) : GSD K where
  G := F.G b
  D := F.D b
  V := F.V
  ιV := F.ιV
  bV := F.bV
  pair := F.pair
  ρ := F.ρ b
  Nab := F.Nab b
  Del := F.Del b
def Ok : Prop := ∀ b, (F.mem b).Ok
abbrev Forms : Type := ∀ b, (F.mem b).EqFun
def intNab : Submodule (𝓞 K) F.Forms := Submodule.pi Set.univ fun b => (F.mem b).intNab
def intDel : Submodule (𝓞 K) F.Forms := Submodule.pi Set.univ fun b => (F.mem b).intDel
abbrev Cl : Type := Σ b, (F.mem b).Cl
variable {F} in

@[reducible] def Ok.fintypeCl (h : F.Ok) : Fintype F.Cl :=
  letI : ∀ b, Fintype (F.mem b).Cl := fun b => (h b).fintypeCl
  inferInstance
@[reducible] def toCSDOf (h : F.Ok) (s : ∀ b, (F.mem b).Sec) : CSD K where
  Cl := F.Cl
  finCl := h.fintypeCl
  V := F.V
  ιV := F.ιV
  bV := F.bV
  pair := F.pair
  Gam := fun c => MulAction.stabilizer (F.G c.1) ((s c.1).rep c.2)
  grpGam := fun _ => inferInstance
  finGam := fun c => (h c.1).fintypeStab ((s c.1).rep c.2)
  ρ := fun c => (F.ρ c.1).comp (MulAction.stabilizer (F.G c.1) ((s c.1).rep c.2)).subtype
  Nab := fun c => F.Nab c.1 ((s c.1).rep c.2)
  Del := fun c => F.Del c.1 ((s c.1).rep c.2)
@[reducible] def toCSD (h : F.Ok) : CSD K := F.toCSDOf h fun b => (F.mem b).outSec
def resOf (h : F.Ok) (s : ∀ b, (F.mem b).Sec) : F.Forms ≃ₗ[K] (F.toCSDOf h s).Forms :=
  (LinearEquiv.piCongrRight fun b => (F.mem b).resOf (h b) (s b)).trans
    { toFun := fun f => ⟨fun c => (f c.1).1 c.2, fun c γ => (f c.1).2 c.2 γ⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun f b => ⟨fun c => f.1 ⟨b, c⟩, fun c γ => f.2 ⟨b, c⟩ γ⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
def ipOf (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ ψ : F.Forms) : K :=
  ∑ b, (F.mem b).ipOf (h b) (s b) (φ b) (ψ b)
abbrev Mat (F F' : GFam K) : Type := ∀ (b : F.β) (b' : F'.β), ClsKer (F.mem b) (F'.mem b')
def Mat.opOf {F F' : GFam K} (M : Mat F F') (h : F.Ok) (s : ∀ b, (F.mem b).Sec) : F.Forms →ₗ[K] F'.Forms :=
  LinearMap.pi fun b' => ∑ b, ((M b b').opOf (h b) (s b)) ∘ₗ (LinearMap.proj b)
def Mat.atReps {F F' : GFam K} (M : Mat F F') (s : ∀ b, (F.mem b).Sec) (s' : ∀ b', (F'.mem b').Sec) :
    F.Cl → F'.Cl → (F.V →ₗ[K] F'.V) := fun c c' => (M c.1 c'.1).k ((s c.1).rep c.2) ((s' c'.1).rep c'.2)
end GFam
@[reducible] def GSD.toFam (S : GSD K) : GFam K where
  β := Unit
  V := S.V
  ιV := S.ιV
  bV := S.bV
  pair := S.pair
  G := fun _ => S.G
  D := fun _ => S.D
  ρ := fun _ => S.ρ
  Nab := fun _ => S.Nab
  Del := fun _ => S.Del
end Formalism.L2.Col


