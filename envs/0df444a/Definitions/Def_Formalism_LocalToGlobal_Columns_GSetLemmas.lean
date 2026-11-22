-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
-- name    : Formalism_LocalToGlobal_Columns_GSetLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:36.387931+00:00
-- url     : https://prove2.me/theorems/5cf47895-1f1c-4cdd-b396-611c75e7b17e
-- title:
--   GSet Lemmas
-- statement:
--   Definitions and structural lemmas for GSet Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Theorems.Thm_Formalism_L2_DIV_CSD_pairOne_apply

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GSD
variable (S : GSD K)
def coordOf (h : S.Ok) (s : S.Sec) : S.EqFun ≃ₗ[K] (Fin (S.toCSDOf h s).dim → K) :=
  (S.resOf h s).trans (S.toCSDOf h s).basis.equivFun
def chgSec (h : S.Ok) (s s' : S.Sec) : (S.toCSDOf h s).Forms ≃ₗ[K] (S.toCSDOf h s').Forms :=
  (S.resOf h s).symm.trans (S.resOf h s')
end GSD
namespace ClsKer
variable {S S' : GSD K} (A : ClsKer S S')
end ClsKer
namespace GSD
variable (S : GSD K)
def Free : Prop := ∀ (d : S.D) (g : S.G), g • d = d → g = 1
theorem forms_eq_top (h : S.Ok) (s : S.Sec) (hf : S.Free) : (S.toCSDOf h s).Forms = ⊤ := by
  refine eq_top_iff.mpr fun f _ => ?_
  intro c γ
  have hγ : ((γ : MulAction.stabilizer S.G (s.rep c)) : S.G) = 1 :=
    hf _ _ (MulAction.mem_stabilizer_iff.mp γ.2)
  show S.ρ ((γ : MulAction.stabilizer S.G (s.rep c)) : S.G) (f c) = f c
  rw [hγ, map_one, Module.End.one_apply]
def resFree (h : S.Ok) (s : S.Sec) (hf : S.Free) : S.EqFun ≃ₗ[K] (S.Cl → S.V) :=
  (S.resOf h s).trans (LinearEquiv.ofTop _ (S.forms_eq_top h s hf))
end GSD
namespace GSD.Iso
variable {S S' : GSD K} (e : GSD.Iso S S')
theorem symm_smul (g' : S'.G) (d' : S'.D) : e.eD.symm (g' • d') = e.eG.symm g' • e.eD.symm d' := by
  rw [Equiv.symm_apply_eq, e.smul, MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]
theorem onCl_cls (d : S.D) : e.onCl (S.cls d) = S'.cls (e.eD d) := rfl
def stabEquiv (d : S.D) : MulAction.stabilizer S.G d ≃ MulAction.stabilizer S'.G (e.eD d) :=
  Equiv.subtypeEquiv e.eG.toEquiv fun g => by
    show g ∈ MulAction.stabilizer S.G d ↔ e.eG g ∈ MulAction.stabilizer S'.G (e.eD d)
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← e.smul, e.eD.apply_eq_iff_eq]
theorem iso_integral_structure_equivariant (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hN : ∀ (g : S.G) (d : S.D), N (g • d) = (N d).map ((S.ρ g).restrictScalars (𝓞 K)))
    (hc : ∀ d : S.D, N' (e.eD d) = (N d).map ((e.eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K)))
    (g' : S'.G) (d' : S'.D) : N' (g' • d') = (N' d').map ((S'.ρ g').restrictScalars (𝓞 K)) := by
  obtain ⟨d, rfl⟩ := e.eD.surjective d'
  obtain ⟨g, rfl⟩ := e.eG.surjective g'
  rw [← e.smul, hc, hc, hN, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  exact e.rho g x
include e in

theorem ok (h : S.Ok) : S'.Ok where
  fin_orb := by
    have := h.fin_orb
    exact Finite.of_equiv _ e.onCl
  fin_stab := by
    intro d'
    obtain ⟨d, rfl⟩ := e.eD.surjective d'
    have := h.fin_stab d
    exact Finite.of_equiv _ (e.stabEquiv d)
  nab_smul := e.iso_integral_structure_equivariant S.Nab S'.Nab h.nab_smul e.nab
  del_smul := e.iso_integral_structure_equivariant S.Del S'.Del h.del_smul e.del
  inv := by
    intro g' x' y'
    obtain ⟨g, rfl⟩ := e.eG.surjective g'
    obtain ⟨x, rfl⟩ := e.eV.surjective x'
    obtain ⟨y, rfl⟩ := e.eV.surjective y'
    rw [← e.rho, ← e.rho, e.pair, e.pair, h.inv]
def mapSec (s : S.Sec) : S'.Sec where
  rep := fun c' => e.eD (s.rep (e.onCl.symm c'))
  spec := by
    intro c'
    rw [← e.onCl_cls, s.spec, Equiv.apply_symm_apply]
def coord (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) :
    (Fin (S.toCSDOf h s).dim → K) ≃ₗ[K] (Fin (S'.toCSDOf h' s').dim → K) :=
  ((S.coordOf h s).symm.trans e.onForms).trans (S'.coordOf h' s')
def refl (S : GSD K) : GSD.Iso S S where
  eG := MulEquiv.refl _
  eD := Equiv.refl _
  eV := LinearEquiv.refl _ _
  smul := fun _ _ => rfl
  rho := fun _ _ => rfl
  pair := fun _ _ => rfl
  nab := fun d => (Submodule.map_id (S.Nab d)).symm
  del := fun d => (Submodule.map_id (S.Del d)).symm
  rat := by
    intro i j
    show S.bV.repr (S.bV j) i ∈ cmMax K
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rat_symm := by
    intro i j
    show S.bV.repr (S.bV j) i ∈ cmMax K
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
theorem transpose_form_mul_involution (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hc : ∀ d : S.D, N' (e.eD d) = (N d).map ((e.eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K))) (d' : S'.D) :
    N (e.eD.symm d') = (N' d').map ((e.eV.symm : S'.V →ₗ[K] S.V).restrictScalars (𝓞 K)) := by
  have h2 := hc (e.eD.symm d')
  rw [Equiv.apply_symm_apply] at h2
  have hid : ((e.eV.symm : S'.V →ₗ[K] S.V).restrictScalars (𝓞 K)).comp
      ((e.eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K)) = LinearMap.id := by
    ext x
    simp
  rw [h2, ← Submodule.map_comp, hid, Submodule.map_id]
def symm : GSD.Iso S' S where
  eG := e.eG.symm
  eD := e.eD.symm
  eV := e.eV.symm
  smul := e.symm_smul
  rho := by
    intro g' x'
    rw [LinearEquiv.symm_apply_eq, e.rho, MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  pair := by
    intro x' y'
    rw [← e.pair, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  nab := e.transpose_form_mul_involution S.Nab S'.Nab e.nab
  del := e.transpose_form_mul_involution S.Del S'.Del e.del
  rat := e.rat_symm
  rat_symm := e.rat
theorem rat_comp {ι ι' ι'' V V' V'' : Type} [Fintype ι'] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] [AddCommGroup V''] [Module K V''] (b : Basis ι K V) (b' : Basis ι' K V') (b'' : Basis ι'' K V'')
    (f : V →ₗ[K] V') (f' : V' →ₗ[K] V'') (F : Subfield K) (h : ∀ i j, b'.repr (f (b j)) i ∈ F)
    (h' : ∀ i j, b''.repr (f' (b' j)) i ∈ F) (i : ι'') (j : ι) : b''.repr (f' (f (b j))) i ∈ F := by
  rw [← b'.sum_repr (f (b j))]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact sum_mem fun k _ => mul_mem (h k j) (h' i k)
def trans {S'' : GSD K} (e' : GSD.Iso S' S'') : GSD.Iso S S'' where
  eG := e.eG.trans e'.eG
  eD := e.eD.trans e'.eD
  eV := e.eV.trans e'.eV
  smul := by
    intro g d
    show e'.eD (e.eD (g • d)) = e'.eG (e.eG g) • e'.eD (e.eD d)
    rw [e.smul, e'.smul]
  rho := by
    intro g x
    show e'.eV (e.eV (S.ρ g x)) = S''.ρ (e'.eG (e.eG g)) (e'.eV (e.eV x))
    rw [e.rho, e'.rho]
  pair := by
    intro x y
    show S''.pair (e'.eV (e.eV x)) (e'.eV (e.eV y)) = _
    rw [e'.pair, e.pair]
  nab := by
    intro d
    show S''.Nab (e'.eD (e.eD d)) = _
    rw [e'.nab, e.nab, ← Submodule.map_comp]
    rfl
  del := by
    intro d
    show S''.Del (e'.eD (e.eD d)) = _
    rw [e'.del, e.del, ← Submodule.map_comp]
    rfl
  rat := rat_comp S.bV S'.bV S''.bV (e.eV : S.V →ₗ[K] S'.V) (e'.eV : S'.V →ₗ[K] S''.V) (cmMax K) e.rat e'.rat
  rat_symm := rat_comp S''.bV S'.bV S.bV (e'.eV.symm : S''.V →ₗ[K] S'.V) (e.eV.symm : S'.V →ₗ[K] S.V) (cmMax K)
    e'.rat_symm e.rat_symm
end GSD.Iso
namespace LocOp
variable {S S' : GSD K}
end LocOp
namespace GSD
variable (S : GSD K)
@[reducible] def restr (T : SubMulAction S.G S.D) : GSD K where
  G := S.G
  D := T
  V := S.V
  ιV := S.ιV
  bV := S.bV
  pair := S.pair
  ρ := S.ρ
  Nab := fun t => S.Nab (t : S.D)
  Del := fun t => S.Del (t : S.D)
theorem restr_cls_eq_iff (T : SubMulAction S.G S.D) (t t' : T) :
    (S.restr T).cls t = (S.restr T).cls t' ↔ S.cls (t : S.D) = S.cls (t' : S.D) := by
  rw [GSD.cls_eq_iff, GSD.cls_eq_iff]
  exact exists_congr fun g => ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩
theorem restr_ok (h : S.Ok) (T : SubMulAction S.G S.D) : (S.restr T).Ok where
  fin_orb := by
    have := h.fin_orb
    let f : (S.restr T).Cl → S.Cl := fun c => S.cls (((S.restr T).outSec.rep c : T) : S.D)
    refine Finite.of_injective f fun c c' hc => ?_
    have h1 := (S.restr_cls_eq_iff T _ _).mpr hc
    rwa [(S.restr T).outSec.spec, (S.restr T).outSec.spec] at h1
  fin_stab := by
    intro t
    have := h.fin_stab ((t : T) : S.D)
    have E : MulAction.stabilizer S.G (t : T) ≃ MulAction.stabilizer S.G ((t : T) : S.D) :=
      Equiv.subtypeEquiv (Equiv.refl S.G) fun (g : S.G) =>
        (⟨fun H => congrArg Subtype.val H, fun H => Subtype.ext H⟩ :
          g • (t : T) = t ↔ g • ((t : T) : S.D) = ((t : T) : S.D))
    exact Finite.of_equiv _ E.symm
  nab_smul := fun g t => h.nab_smul g ((t : T) : S.D)
  del_smul := fun g t => h.del_smul g ((t : T) : S.D)
  inv := h.inv
variable (A : Type) [Group A] [MulAction A S.D]
structure Slice where
  T : SubMulAction S.G S.D
  uniq : ∀ d : S.D, ∃! a : A, a • d ∈ T
def FreeOnCl : Prop := ∀ (a : A) (d : S.D), S.cls (a • d) = S.cls d → a = 1
namespace Slice
variable {S A} (σ : S.Slice A)
def a (d : S.D) : A := (σ.uniq d).choose
theorem a_mem (d : S.D) : σ.a d • d ∈ σ.T := by
  exact (σ.uniq d).choose_spec.1
theorem a_eq {d : S.D} {b : A} (hb : b • d ∈ σ.T) : σ.a d = b := by
  exact ((σ.uniq d).choose_spec.2 b hb).symm
def glue (F : A → (S.restr σ.T).EqFun) (d : S.D) : S.V :=
  ((F (σ.a d)⁻¹ : (S.restr σ.T).EqFun) : σ.T → S.V) ⟨σ.a d • d, σ.a_mem d⟩
theorem glue_eq (F : A → (S.restr σ.T).EqFun) (d : S.D) (b : A) (hb : b • d ∈ σ.T) :
    σ.glue F d = ((F b⁻¹ : (S.restr σ.T).EqFun) : σ.T → S.V) ⟨b • d, hb⟩ := by
  have e := σ.a_eq hb
  have aux : ∀ (c : A) (_ : b = c) (t' : σ.T) (_ : (t' : S.D) = b • d),
      ((F c⁻¹ : (S.restr σ.T).EqFun) : σ.T → S.V) t' = ((F b⁻¹ : (S.restr σ.T).EqFun) : σ.T → S.V) ⟨b • d, hb⟩ := by
    rintro _ rfl t' ht
    obtain rfl : t' = ⟨b • d, hb⟩ := Subtype.ext ht
    rfl
  exact aux _ e.symm _ (show σ.a d • d = b • d by rw [e])
variable [SMulCommClass A S.G S.D]
def split : S.EqFun ≃ₗ[K] (A → (S.restr σ.T).EqFun) where
  toFun φ b := ⟨fun t => (φ : S.D → S.V) (b • ((t : σ.T) : S.D)), fun (g : S.G) t => by
    show (φ : S.D → S.V) (b • g • ((t : σ.T) : S.D)) = S.ρ g ((φ : S.D → S.V) (b • ((t : σ.T) : S.D)))
    rw [smul_comm, φ.2]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun F := ⟨σ.glue F, fun g d => by
    have hb : σ.a d • g • d ∈ σ.T := by
      rw [smul_comm]
      exact σ.T.smul_mem g (σ.a_mem d)
    rw [σ.glue_eq F (g • d) (σ.a d) hb]
    have h1 := (F (σ.a d)⁻¹).2 g ⟨σ.a d • d, σ.a_mem d⟩
    have h2 : (⟨σ.a d • g • d, hb⟩ : σ.T) = g • (⟨σ.a d • d, σ.a_mem d⟩ : σ.T) :=
      Subtype.ext (smul_comm _ _ _)
    rw [h2]
    exact h1⟩
  left_inv φ := by
    apply Subtype.ext
    funext d
    show (φ : S.D → S.V) ((σ.a d)⁻¹ • σ.a d • d) = (φ : S.D → S.V) d
    rw [inv_smul_smul]
  right_inv F := by
    funext b
    apply Subtype.ext
    funext t
    have hb : b⁻¹ • b • ((t : σ.T) : S.D) ∈ σ.T := by
      rw [inv_smul_smul]
      exact (t : σ.T).2
    show σ.glue F (b • ((t : σ.T) : S.D)) = _
    rw [σ.glue_eq F _ b⁻¹ hb]
    have aux : ∀ (c : A) (_ : c = b) (t' : σ.T) (_ : t' = t),
        ((F c : (S.restr σ.T).EqFun) : σ.T → S.V) t' = ((F b : (S.restr σ.T).EqFun) : σ.T → S.V) t := by
      rintro _ rfl _ rfl
      rfl
    exact aux _ (inv_inv b) _ (Subtype.ext (inv_smul_smul _ _))
def dia (S : GSD K) {A : Type} [Group A] [MulAction A S.D] [SMulCommClass A S.G S.D] (b : A) : LocOp S S :=
  LocOp.ofMap (MonoidHom.id S.G) (fun d => b • d) LinearMap.id (fun g d => smul_comm b g d) (fun _ _ => rfl)
def clEquiv (sT : (S.restr σ.T).Sec) : A × (S.restr σ.T).Cl ≃ S.Cl :=
  Equiv.ofBijective (fun p => S.cls (p.1 • ((sT.rep p.2 : σ.T) : S.D))) (by
    have := SMulCommClass.symm A S.G S.D
    constructor
    · rintro ⟨b, c⟩ ⟨b', c'⟩ hp
      obtain ⟨g, hg⟩ := (S.cls_eq_iff _ _).mp hp
      have hg' : g • b' • ((sT.rep c' : σ.T) : S.D) = b • ((sT.rep c : σ.T) : S.D) := hg
      have h1 : (b⁻¹ * b') • (g • ((sT.rep c' : σ.T) : S.D)) ∈ σ.T := by
        rw [mul_smul, smul_comm b' g, hg', inv_smul_smul]
        exact (sT.rep c : σ.T).2
      have h2 : (1 : A) • (g • ((sT.rep c' : σ.T) : S.D)) ∈ σ.T := by
        rw [one_smul]
        exact σ.T.smul_mem g (sT.rep c' : σ.T).2
      have h3 : b⁻¹ * b' = 1 := (σ.a_eq h1).symm.trans (σ.a_eq h2)
      have h4 : b' = b := (inv_mul_eq_one.mp h3).symm
      subst h4
      rw [smul_comm] at hg'
      have h5 := MulAction.injective b' hg'
      have h6 : (S.restr σ.T).cls (sT.rep c) = (S.restr σ.T).cls (sT.rep c') :=
        (S.restr_cls_eq_iff σ.T _ _).mpr ((S.cls_eq_iff _ _).mpr ⟨g, h5⟩)
      rw [sT.spec, sT.spec] at h6
      rw [h6]
    · intro c
      obtain ⟨d, rfl⟩ : ∃ d, S.cls d = c := ⟨Quotient.out c, Quotient.out_eq c⟩
      let t : σ.T := ⟨σ.a d • d, σ.a_mem d⟩
      refine ⟨((σ.a d)⁻¹, (S.restr σ.T).cls t), ?_⟩
      obtain ⟨g, hg⟩ : ∃ g : S.G, g • (sT.rep ((S.restr σ.T).cls t) : σ.T) = t := sT.exists_mv t
      have hg' : g • ((sT.rep ((S.restr σ.T).cls t) : σ.T) : S.D) = σ.a d • d := congrArg Subtype.val hg
      show S.cls ((σ.a d)⁻¹ • ((sT.rep ((S.restr σ.T).cls t) : σ.T) : S.D)) = S.cls d
      rw [← S.cls_smul g, smul_comm, hg', inv_smul_smul])
def sec (sT : (S.restr σ.T).Sec) : S.Sec where
  rep := fun c => ((σ.clEquiv sT).symm c).1 • ((sT.rep ((σ.clEquiv sT).symm c).2 : σ.T) : S.D)
  spec := fun c => (σ.clEquiv sT).apply_symm_apply c
end Slice
end GSD
section Fib
variable {G D D₀ : Type} [Group G] [MulAction G D] [MulAction G D₀] (pr : D → D₀)
  (hpr : ∀ (g : G) (d : D), pr (g • d) = g • pr d)
def fibre (x : D₀) : SubMulAction (MulAction.stabilizer G x) D where
  carrier := {d | pr d = x}
  smul_mem' := by
    intro γ d hd
    show pr ((γ : G) • d) = x
    rw [hpr, show pr d = x from hd]
    exact γ.2
def orbitsFib (rep : MulAction.orbitRel.Quotient G D₀ → D₀)
    (hrep : ∀ c, (Quotient.mk'' (rep c) : MulAction.orbitRel.Quotient G D₀) = c) :
    (Σ c : MulAction.orbitRel.Quotient G D₀,
      MulAction.orbitRel.Quotient (MulAction.stabilizer G (rep c)) (fibre pr hpr (rep c))) ≃
      MulAction.orbitRel.Quotient G D :=
  Equiv.ofBijective
    (fun p => Quotient.map' (s₂ := MulAction.orbitRel G D) (fun y : fibre pr hpr (rep p.1) => (y : D))
      (by
        rintro y y' ⟨γ, hγ⟩
        exact ⟨(γ : G), congrArg Subtype.val hγ⟩) p.2)
    (by
      constructor
      · rintro ⟨c, q⟩ ⟨c', q'⟩ h
        induction q using Quotient.inductionOn' with
        | h y =>
        induction q' using Quotient.inductionOn' with
        | h y' =>
        obtain ⟨g, hg⟩ : ∃ g : G, g • (y' : D) = (y : D) := Quotient.exact' h
        have h1 : g • rep c' = rep c := by
          rw [← show pr (y' : D) = rep c' from y'.2, ← hpr, hg]
          exact y.2
        have hc : c = c' := by
          rw [← hrep c, ← hrep c']
          exact Quotient.sound' ⟨g, h1⟩
        subst hc
        refine congrArg (Sigma.mk c) (Quotient.sound' ⟨⟨g, h1⟩, Subtype.ext hg⟩)
      · intro q
        induction q using Quotient.inductionOn' with
        | h d =>
        obtain ⟨g, hg⟩ : ∃ g : G, g • pr d = rep (Quotient.mk'' (pr d)) := Quotient.exact' (hrep (Quotient.mk'' (pr d)))
        refine ⟨⟨Quotient.mk'' (pr d), Quotient.mk'' ⟨g • d, (hpr g d).trans hg⟩⟩, ?_⟩
        exact Quotient.sound' ⟨g, rfl⟩)
end Fib
namespace GSD
variable (S : GSD K)
end GSD
namespace BiPair
variable {S S' : GSD K} (P : BiPair S S')
end BiPair
namespace GFam
variable (F : GFam K)
def coordOf (h : F.Ok) (s : ∀ b, (F.mem b).Sec) : F.Forms ≃ₗ[K] (Fin (F.toCSDOf h s).dim → K) :=
  (F.resOf h s).trans (F.toCSDOf h s).basis.equivFun
def Good (n : ℕ) : Prop := ∀ b, (F.mem b).Good n
end GFam
namespace GSD
variable (K)
def twSgn : ℤˣ →* Module.End K K where
  toFun g := (((g : ℤ) : K)) • (1 : Module.End K K)
  map_one' := by simp
  map_mul' a b := by
    ext
    simp [mul_comm]
theorem twSgn_apply (g : ℤˣ) (x : K) : twSgn K g x = ((g : ℤ) : K) * x := by
  show (((g : ℤ) : K) • (1 : Module.End K K)) x = ((g : ℤ) : K) * x
  rw [LinearMap.smul_apply, Module.End.one_apply, smul_eq_mul]
abbrev tw : GSD K where
  G := ℤˣ
  D := Option ℤˣ
  V := K
  ιV := Unit
  bV := Basis.singleton Unit K
  pair := CSD.pairOne K
  ρ := twSgn K
  Nab := fun _ => 1
  Del := fun _ => 1
theorem map_twSgn (g : ℤˣ) :
    (1 : Submodule (𝓞 K) K) = (1 : Submodule (𝓞 K) K).map ((twSgn K g).restrictScalars (𝓞 K)) := by
  ext x
  simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, twSgn_apply]
  constructor
  · intro hx
    refine ⟨((g : ℤ) : K) * x, ?_, ?_⟩
    · obtain ⟨y, rfl⟩ := Submodule.mem_one.mp hx
      exact Submodule.mem_one.mpr ⟨((g : ℤ) : 𝓞 K) * y, by simp⟩
    · rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hy
    exact Submodule.mem_one.mpr ⟨((g : ℤ) : 𝓞 K) * z, by simp⟩
theorem tw_ok : (tw K).Ok where
  fin_orb := by
    show Finite (MulAction.orbitRel.Quotient ℤˣ (Option ℤˣ))
    exact Quotient.finite _
  fin_stab := by
    intro d
    show Finite (MulAction.stabilizer ℤˣ (d : Option ℤˣ))
    infer_instance
  nab_smul := fun g _ => map_twSgn K g
  del_smul := fun g _ => map_twSgn K g
  inv := by
    intro g x y
    show CSD.pairOne K (twSgn K g x) (twSgn K g y) = CSD.pairOne K x y
    rw [CSD.pairOne_apply, CSD.pairOne_apply]
    erw [twSgn_apply, twSgn_apply]
    rcases Int.units_eq_one_or g with rfl | rfl <;> simp
theorem tw_none (φ : (tw K).EqFun) : (φ.1 : Option ℤˣ → K) none = 0 := by
  have h2 : (φ.1 : Option ℤˣ → K) none = -(φ.1 : Option ℤˣ → K) none := by
    have h1 := φ.2 (-1) none
    rw [twSgn_apply] at h1
    convert h1 using 1 <;> first | rfl | simp
  have h3 : (2 : K) * (φ.1 : Option ℤˣ → K) none = 0 := by
    rw [two_mul]
    nth_rewrite 2 [h2]
    exact add_neg_cancel _
  exact (mul_eq_zero.mp h3).resolve_left two_ne_zero
def twForm : (tw K).EqFun := ⟨fun d => match d with
    | none => (0 : K)
    | some g => ((g : ℤ) : K), by
  intro g d
  cases d with
  | none =>
    show (0 : K) = twSgn K g 0
    simp
  | some e =>
    show (((g * e : ℤˣ) : ℤ) : K) = twSgn K g ((e : ℤ) : K)
    rw [twSgn_apply]
    simp⟩
def twEquiv : (tw K).EqFun ≃ₗ[K] K where
  toFun φ := (φ.1 : Option ℤˣ → K) (some 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun a := a • twForm K
  left_inv φ := by
    apply Subtype.ext
    funext d
    cases d with
    | none =>
      show (φ.1 : Option ℤˣ → K) (some 1) * 0 = (φ.1 : Option ℤˣ → K) none
      rw [tw_none, mul_zero]
    | some e =>
      show (φ.1 : Option ℤˣ → K) (some 1) * ((e : ℤ) : K) = (φ.1 : Option ℤˣ → K) (some e)
      have h := φ.2 e (some (1 : ℤˣ) : Option ℤˣ)
      have h1 : (φ.1 : Option ℤˣ → K) (some (e * 1)) = twSgn K e ((φ.1 : Option ℤˣ → K) (some 1)) := h
      rw [mul_one, twSgn_apply] at h1
      rw [h1, mul_comm]
  right_inv a := by
    show a * (((1 : ℤˣ) : ℤ) : K) = a
    simp
abbrev tv : GSD K := GSD.triv K ℤˣ (Option ℤˣ)
theorem tv_ok : (tv K).Ok := by
  refine ⟨inferInstance, fun _ => inferInstance, fun g _ => ?_, fun g _ => ?_, fun g x y => rfl⟩
  · rw [MonoidHom.one_apply]
    exact (Submodule.map_id _).symm
  · rw [MonoidHom.one_apply]
    exact (Submodule.map_id _).symm
def isS : (tv K).Cl → Bool := Quotient.lift Option.isSome (by
  rintro a b ⟨g, rfl⟩
  cases b <;> rfl)
def eCl : (tv K).Cl ≃ Bool := Equiv.ofBijective (isS K) ⟨by
  rintro ⟨a⟩ ⟨b⟩ h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y => exact absurd h (by simp [isS])
  | some x =>
    cases b with
    | none => exact absurd h (by simp [isS])
    | some y =>
      refine Quotient.sound ⟨x * y⁻¹, ?_⟩
      show some ((x * y⁻¹) * y) = some x
      rw [inv_mul_cancel_right], by
  intro b
  cases b
  · exact ⟨(tv K).cls none, rfl⟩
  · exact ⟨(tv K).cls (some 1), rfl⟩⟩
end GSD
end Formalism.L2.Col


