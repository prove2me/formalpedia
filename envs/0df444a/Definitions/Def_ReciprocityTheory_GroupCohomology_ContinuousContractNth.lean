-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
-- name    : ReciprocityTheory_GroupCohomology_ContinuousContractNth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:05.512253+00:00
-- url     : https://prove2.me/theorems/e032e47b-f402-4b47-9da4-f4e4f4e170e9
-- title:
--   Continuous Contract Nth
-- statement:
--   Definitions and structural lemmas for Continuous Contract Nth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ContinuousContractNth.lean

import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsTowerLim
import Theorems.Thm_ReciprocityTheory_Gal_dn_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal
noncomputable section
universe u
variable {R : Type u} [CommRing R]
structure TRep (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] where
  V : Type u
  [acg : AddCommGroup V]
  [mod : Module R V]
  [top : TopologicalSpace V]
  [tag : IsTopologicalAddGroup V]
  [ccs : ContinuousConstSMul R V]
  rho : Representation R G V
  cont : ContAction rho
attribute [instance] TRep.acg TRep.mod TRep.top TRep.tag TRep.ccs
variable {G G' G'' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  [Group G''] [TopologicalSpace G''] [IsTopologicalGroup G'']
theorem dn_dn {M : Type u} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (rho : Representation R G M) (n : ℕ) (f : (Fin n → G) → M) :
    dn rho (n + 1) (dn rho n f) = 0 := by
  have h := groupCohomology.inhomogeneousCochains.d_comp_d (Rep.of rho) (n := n)
  exact congrArg (fun φ => φ.hom f) h
theorem continuous_contractNth (n : ℕ) (j : Fin (n + 1)) :
    Continuous fun g : Fin (n + 1) → G => Fin.contractNth j (· * ·) g := by
  refine continuous_pi fun k => ?_
  unfold Fin.contractNth
  split_ifs <;> fun_prop
theorem continuous_dn (M : TRep R G) (n : ℕ) {f : (Fin n → G) → M.V} (hf : Continuous f) :
    Continuous (dn M.rho n f) := by
  have h1 : Continuous fun g : Fin (n + 1) → G => M.rho (g 0) (f fun i => g i.succ) :=
    M.cont.comp (f := fun g : Fin (n + 1) → G => (g 0, f fun i => g i.succ))
      ((continuous_apply 0).prodMk (hf.comp (continuous_pi fun i => continuous_apply _)))
  exact h1.add (continuous_finsetSum _ fun j _ => (hf.comp (continuous_contractNth n j)).const_smul _)
namespace TRep
def coch (M : TRep R G) : Cx R where
  X n := Cn M.rho n
  d n := (dn M.rho n).restrict fun _ hf => continuous_dn M n hf
  dd n x := Subtype.ext (dn_dn M.rho n x.1)
abbrev H (M : TRep R G) (n : ℕ) := M.coch.H n
def res (M : TRep R G) (φ : G' →* G) (hφ : Continuous φ) : TRep R G' where
  V := M.V
  rho := M.rho.comp φ
  cont := M.cont.comp (f := fun p : G' × M.V => (φ p.1, p.2))
    ((hφ.comp continuous_fst).prodMk continuous_snd)
abbrev resSub (M : TRep R G) (U : Subgroup G) : TRep R U := M.res U.subtype continuous_subtype_val
end TRep
structure Pair (M : TRep R G) (M' : TRep R G') where
  φ : G' →* G
  u : M.V →ₗ[R] M'.V
  φ_cont : Continuous φ
  u_cont : Continuous u
  equiv : ∀ g m, u (M.rho (φ g) m) = M'.rho g (u m)
theorem contractNth_map (φ : G' →* G) (n : ℕ) (j : Fin (n + 1)) (g : Fin (n + 1) → G') :
    (fun i => φ (Fin.contractNth j (· * ·) g i)) = Fin.contractNth j (· * ·) fun i => φ (g i) := by
  funext k
  unfold Fin.contractNth
  split_ifs <;> simp
def Pair.hom {M : TRep R G} {M' : TRep R G'} (P : Pair M M') : Cx.Hom M.coch M'.coch where
  f n :=
    { toFun := fun f => ⟨fun g => P.u (f.1 fun i => P.φ (g i)),
        P.u_cont.comp (Continuous.comp f.2 (continuous_pi fun i => P.φ_cont.comp (continuous_apply i)))⟩
      map_add' := fun f f' => Subtype.ext (funext fun g => map_add P.u _ _)
      map_smul' := fun r f => Subtype.ext (funext fun g => map_smul P.u _ _) }
  comm n f := by
    refine Subtype.ext (funext fun g => ?_)
    show P.u (dn M.rho n f.1 fun i => P.φ (g i)) = dn M'.rho n (fun g => P.u (f.1 fun i => P.φ (g i))) g
    simp only [dn_apply, map_add, map_sum, map_smul, P.equiv, contractNth_map]
def Pair.ofMap {M M' : TRep R G} (u : M.V →ₗ[R] M'.V) (hu : Continuous u)
    (he : ∀ g m, u (M.rho g m) = M'.rho g (u m)) : Pair M M' :=
  ⟨MonoidHom.id G, u, continuous_id, hu, he⟩
def Pair.res (M : TRep R G) (φ : G' →* G) (hφ : Continuous φ) : Pair M (M.res φ hφ) :=
  ⟨φ, LinearMap.id, hφ, continuous_id, fun _ _ => rfl⟩
structure admitted {A B C : TRep R G} (i : Pair A B) (p : Pair B C) : Prop where
  i_id : i.φ = MonoidHom.id G
  p_id : p.φ = MonoidHom.id G
  emb : Topology.IsEmbedding i.u
  exact : Function.Exact i.u p.u
  sec : ∃ s : C.V → B.V, Continuous s ∧ ∀ c, p.u (s c) = c
def IsInvRep (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M) : Prop :=
  P.φ = QuotientGroup.mk' N ∧ Topology.IsEmbedding P.u ∧
    ∀ m, m ∈ LinearMap.range P.u ↔ ∀ g ∈ N, M.rho g m = m
def rep (U : Subgroup G) (x : G) : G := (Quotient.mk (QuotientGroup.rightRel U) x).out
theorem mul_rep_inv_mem (U : Subgroup G) (x : G) : x * (rep U x)⁻¹ ∈ U :=
  QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel U) x)))
def retr (U : Subgroup G) (x : G) : U := ⟨x * (rep U x)⁻¹, mul_rep_inv_mem U x⟩
def corFun (M : TRep R G) (U : Subgroup G) (n : ℕ) (f : (Fin n → U) → M.V) (g : Fin n → G) : M.V :=
  ∑ᶠ c : Quotient (QuotientGroup.rightRel U), M.rho c.out⁻¹
    (f fun i => (retr U (c.out * Fin.partialProd g i.castSucc))⁻¹ * retr U (c.out * Fin.partialProd g i.succ))
def IsCor (M : TRep R G) (U : Subgroup G) (cor : Cx.Hom (M.resSub U).coch M.coch) : Prop :=
  ∀ n f, (cor.f n f).1 = corFun M U n f.1
structure Pairing (M N P : TRep R G) where
  β : M.V →ₗ[R] N.V →ₗ[R] P.V
  cont : Continuous fun x : M.V × N.V => β x.1 x.2
  equiv : ∀ g m n, β (M.rho g m) (N.rho g n) = P.rho g (β m n)
def cupFun {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) (f : (Fin p → G) → M.V)
    (f' : (Fin q → G) → N.V) (g : Fin (p + q) → G) : P.V :=
  b.β (f fun i => g (Fin.castAdd q i))
    (N.rho (List.ofFn fun i => g (Fin.castAdd q i)).prod (f' fun j => g (Fin.natAdd p j)))
def IsCup {M N P : TRep R G} (b : Pairing M N P)
    (cup : ∀ p q, M.H p →ₗ[R] N.H q →ₗ[R] P.H (p + q)) : Prop :=
  ∀ p q (x : M.coch.X p) (y : N.coch.X q) (hx : M.coch.d p x = 0) (hy : N.coch.d q y = 0),
    ∃ (z : P.coch.X (p + q)) (hz : P.coch.d (p + q) z = 0), z.1 = cupFun b p q x.1 y.1 ∧
      cup p q (M.coch.cls p x hx) (N.coch.cls q y hy) = P.coch.cls (p + q) z hz
def TRep.cast (M : TRep R G) {n m : ℕ} (h : n = m) : M.H n ≃ₗ[R] M.H m := h ▸ LinearEquiv.refl R _
def IsCoind (U : Subgroup G) (M : TRep R U) (C : TRep R G) (ev : Pair C M) : Prop :=
  ev.φ = U.subtype ∧ ∃ j : C.V → C(G, M.V), Topology.IsEmbedding j ∧
    (∀ c g, j c g = ev.u (C.rho g c)) ∧
    ∀ f : C(G, M.V), (∀ (x : U) g, f (x * g) = M.rho x (f g)) → f ∈ Set.range j
structure SelData (M : TRep R G) (ι : Type u) where
  D : ι → Type u
  [grp : ∀ v, Group (D v)]
  [top : ∀ v, TopologicalSpace (D v)]
  [tgrp : ∀ v, IsTopologicalGroup (D v)]
  φ : ∀ v, D v →* G
  φ_cont : ∀ v, Continuous (φ v)
  U : ι → Cx R
  j : ∀ v, Cx.Hom (U v) (M.res (φ v) (φ_cont v)).coch
attribute [instance] SelData.grp SelData.top SelData.tgrp
namespace SelData
variable {M : TRep R G} {ι : Type u} (S : SelData M ι)
abbrev loc (v : ι) : Cx R := (M.res (S.φ v) (S.φ_cont v)).coch
abbrev locHom (v : ι) : Cx.Hom M.coch (S.loc v) := (Pair.res M (S.φ v) (S.φ_cont v)).hom
def diff : Cx.Hom (Cx.prod M.coch (Cx.pi S.U)) (Cx.pi S.loc) where
  f n := LinearMap.pi fun v => ((S.locHom v).f n).comp (LinearMap.fst R _ _) -
    ((S.j v).f n).comp ((LinearMap.proj v).comp (LinearMap.snd R _ _))
  comm n x := funext fun v => by
    show (S.locHom v).f (n + 1) (M.coch.d n x.1) - (S.j v).f (n + 1) ((S.U v).d n (x.2 v)) =
      (S.loc v).d n ((S.locHom v).f n x.1 - (S.j v).f n (x.2 v))
    rw [map_sub, (S.locHom v).comm, (S.j v).comm]
def cx : Cx R := Cx.fib S.diff
def toGlob : Cx.Hom S.cx M.coch := (Cx.prodFst _ _).comp (Cx.fibFst S.diff)
def sel (n : ℕ) : Submodule R (M.H n) :=
  ⨅ v, (LinearMap.range ((S.j v).H n)).comap ((S.locHom v).H n)
end SelData
end
end ReciprocityTheory.Coh


