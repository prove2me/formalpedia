-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_DataForms
-- name    : Formalism_LocalRingCardinality_DataForms
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:28.318159+00:00
-- url     : https://prove2.me/theorems/e2c1f215-3b52-4ca7-a5a6-c9cbba809464
-- title:
--   Data Forms
-- statement:
--   Definitions and structural lemmas for Data Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataForms.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions
open NumberField
def intW {LL : Type} [Field LL] (Pl : Rows.Places LL) (w : Pl.Pl) : Subring LL where
  carrier := {x | (0 : WithTop ℤ) ≤ Pl.val w x}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, AddValuation.map_mul] at *
    exact add_nonneg hx hy
  one_mem' := by simp
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at *
    exact le_trans (le_min hx hy) (AddValuation.map_add _ _ _)
  zero_mem' := by simp
  neg_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq, AddValuation.map_neg] at *
    exact hx
def locW {LL : Type} [Field LL] [NumberField LL] (Pl : Rows.Places LL) (w : Pl.Pl)
    {V : Type} [AddCommGroup V] [Module LL V] [Module (𝓞 LL) V] (L : Submodule (𝓞 LL) V) :
    Submodule (intW Pl w) V :=
  Submodule.span (intW Pl w) (L : Set V)
theorem inj_of_li {K V M ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup M]
    [Module ℂ M] [Fintype ι] (σ : K →+* ℂ) (e : V →ₛₗ[σ] M) (b : Module.Basis ι K V)
    (h : LinearIndependent ℂ (fun i => e (b i))) : Function.Injective e := by
  intro x y hxy
  have key : ∀ z : V, e z = ∑ j, σ (b.repr z j) • e (b j) := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    rw [map_sum]
    simp only [LinearMap.map_smulₛₗ]
  have hsum : ∑ j, (σ (b.repr x j) - σ (b.repr y j)) • e (b j) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← key, hxy, sub_self]
  have hz := (Fintype.linearIndependent_iff.mp h) _ hsum
  apply b.ext_elem
  intro i
  exact σ.injective (sub_eq_zero.mp (hz i))
def descend {K V W M N : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {σ : K →+* ℂ}
    (e₁ : V →ₛₗ[σ] M) (e₂ : W →ₛₗ[σ] N) (hinj : Function.Injective e₂) (f : M →ₗ[ℂ] N)
    (h : ∀ x, ∃ y, e₂ y = f (e₁ x)) : V →ₗ[K] W where
  toFun x := Classical.choose (h x)
  map_add' x y := by
    apply hinj
    show e₂ (Classical.choose (h (x + y))) = e₂ (Classical.choose (h x) + Classical.choose (h y))
    have h1 := Classical.choose_spec (h (x + y))
    have h2 := Classical.choose_spec (h x)
    have h3 := Classical.choose_spec (h y)
    rw [map_add e₂, h1, h2, h3, map_add, map_add]
  map_smul' c x := by
    apply hinj
    show e₂ (Classical.choose (h (c • x))) = e₂ (c • Classical.choose (h x))
    have h1 := Classical.choose_spec (h (c • x))
    have h2 := Classical.choose_spec (h x)
    rw [h1, LinearMap.map_smulₛₗ e₂, h2, LinearMap.map_smulₛₗ e₁, LinearMap.map_smul]
namespace ColumnChain
variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)
def Klin (i : ℕ) : (C.cls i → C.Y i → ℂ) →ₗ[ℂ] (C.cls (i + 1) → C.Y (i + 1) → ℂ) where
  toFun := C.K i
  map_add' φ ψ := by
    funext L' y
    simp [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' a φ := by
    funext L' y
    simp [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, Finset.mul_sum, smul_eq_mul]
    refine Finset.sum_congr rfl (fun c _ => by ring)
end ColumnChain
theorem Ranks.N_pos (R : Ranks) (j : ℕ) : 0 < R.N j := by
  have h1 := R.two_le_m
  have h2 := R.m_add_three_le_k
  unfold Ranks.N
  omega
theorem Ranks.blk_lt (R : Ranks) {j : ℕ} (hj : j ≤ R.m) (i : Fin (R.N j)) (h : ¬ i.1 < R.k) :
    (i.1 - R.k) / (R.t + 1) < R.m := by
  have hi : i.1 < R.k + j * (R.t + 1) := i.2
  have hlt : i.1 - R.k < R.m * (R.t + 1) :=
    lt_of_lt_of_le (by omega) (Nat.mul_le_mul_right _ hj)
  exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr hlt
structure MemberForms {R : Ranks} (LL : Type) [Field LL] [NumberField LL] [StarRing LL]
    (embLL : LL →+* ℂ) (Pl : Rows.Places LL) (Tau : Type) [Fintype Tau] (hc : Tau → HCParam R)
    (C : ColumnChain R Tau hc) (A : ColumnsAtT R C) (P : PeriodMap R C) where

  lv : ∀ i, A.vT → C.cls i → Type
  [lvAcg : ∀ i v c, AddCommGroup (lv i v c)]
  [lvMod : ∀ i v c, Module (A.Fv v) (lv i v c)]

  lv_rank : ∀ i v c, Module.finrank (A.Fv v) (lv i v c) = R.N i

  fv : ∀ i v c, Module.Dual (A.Fv v) (lv i v c)

  fv_ne : ∀ i v c, fv i v c ≠ 0

  up : ∀ i v c, lv i v c → C.cls i

  upT : ∀ i v c, lv i v c → ((C.Y i → ℂ) ≃ₗ[ℂ] (C.Y i → ℂ))

  lk : ∀ i, A.vT → C.cls i → Type
  [lkAcg : ∀ i v c, AddCommGroup (lk i v c)]
  [lkMod : ∀ i v c, Module (A.Fv v) (lk i v c)]
  lk_rank : ∀ i v c, Module.finrank (A.Fv v) (lk i v c) = R.N i

  te : ∀ i v c, lk i v c

  te_ne : ∀ i v c, te i v c ≠ 0

  dn : ∀ i v c, Module.Dual (A.Fv v) (lk i v c) → C.cls i

  dnT : ∀ i v c, Module.Dual (A.Fv v) (lk i v c) → ((C.Y i → ℂ) ≃ₗ[ℂ] (C.Y i → ℂ))

  dil : ∀ i v, (A.Fv v)ˣ → C.cls i → C.cls i

  dilT : ∀ i v, (A.Fv v)ˣ → C.cls i → ((C.Y i → ℂ) ≃ₗ[ℂ] (C.Y i → ℂ))
  dil_one : ∀ i v c, dil i v 1 c = c
  dil_mul : ∀ i v a b c, dil i v (a * b) c = dil i v a (dil i v b c)

  dil_fv : ∀ i v a c, ∃ e : lv i v (dil i v a c) ≃ₗ[A.Fv v] lv i v c,
    fv i v (dil i v a c) = (a : A.Fv v) • (fv i v c).comp e.toLinearMap

  dil_stab : ∀ i v a c, Nat.card (C.stab i (dil i v a c)) = Nat.card (C.stab i c)

  rhoT_dil : ∀ v a (φ : C.cls 0 → C.Y 0 → ℂ) c, A.rhoT v a φ c = dilT 0 v a c (φ (dil 0 v a c))

  tauOf : Pl.Pl → (A.vT ≃ Tau)

  seenP : Pl.Pl → Bool

  lam : ∀ j, Tau → DomWeight (R.N j)

  lam_eq : ∀ j (hj : j ≤ R.m) τ (i : Fin (R.N j)), ((lam j τ).w i : ℚ) =
    if h : i.1 < R.k then hcToWeightQ (hc τ).u ⟨i.1, h⟩
    else -wG R ((hc τ).e ⟨(i.1 - R.k) / (R.t + 1), R.blk_lt hj i h⟩) ((i.1 - R.k) / (R.t + 1) + 1)

  sg : Tau → DomWeight (R.N R.m - 1)

  Fi : ∀ i, Submodule ℂ (C.cls i → C.Y i → ℂ)

  Fi_zero : Fi 0 = A.Mu0

  ipV : ∀ i, C.cls i → (C.Y i → ℂ) →ₗ⋆[ℂ] (C.Y i → ℂ) →ₗ[ℂ] ℂ

  lat : ℕ → HLat LL
  lat_good : ∀ i, (lat i).Good

  emb : ∀ i, (lat i).V →ₛₗ[embLL] (C.cls i → C.Y i → ℂ)
  emb_basis : ∀ i, LinearIndependent ℂ (fun a => emb i ((lat i).b a)) ∧
    Submodule.span ℂ (Set.range (fun a => emb i ((lat i).b a))) = Fi i

  emb_norm : ∀ i x, (Formalism.HermitianLatticesTheory.majAt (lat i).b (lat i).X (InfinitePlace.mk embLL) x x).re =
    (∑ c, C.wt i c * ipV i c (emb i x c) (emb i x c)).re

  rhoT_lat : ∀ v a x, x ∈ (lat 0).L → ∃ y ∈ (lat 0).L, emb 0 y = A.rhoT v a (emb 0 x)

  Bw : ∀ i (w : Pl.Pl), A.vT → Submodule (intW Pl w) (lat i).V

  Bw_span : ∀ i w v, Submodule.span LL (Bw i w v : Set (lat i).V) = ⊤

  clsP : Type
  [clsPFin : Fintype clsP]

  stabilizer₂ : clsP → Type
  [stabPGrp : ∀ c, Group (stabilizer₂ c)]
  [stabPFin : ∀ c, Finite (stabilizer₂ c)]

  til : clsP → C.cls R.m

  stabMap : ∀ c, stabilizer₂ c →* C.stab R.m (til c)
  stabMap_inj : ∀ c, Function.Injective (stabMap c)

  evz_til : ∀ φ ψ : C.cls R.m → C.Y R.m → ℂ, (∀ c, φ (til c) = ψ (til c)) → P.evz φ = P.evz ψ

  ptC : Submodule ℂ P.Wrow

  ipP : P.Wrow →ₗ⋆[ℂ] P.Wrow →ₗ[ℂ] ℂ

  ptLat : HLat LL
  ptLat_good : ptLat.Good
  ptEmb : ptLat.V →ₛₗ[embLL] P.Wrow
  ptEmb_basis : LinearIndependent ℂ (fun a => ptEmb (ptLat.b a)) ∧
    Submodule.span ℂ (Set.range (fun a => ptEmb (ptLat.b a))) = ptC
  ptEmb_norm : ∀ x, (Formalism.HermitianLatticesTheory.majAt ptLat.b ptLat.X (InfinitePlace.mk embLL) x x).re =
    (ipP (ptEmb x) (ptEmb x)).re

  beOn : Tau → ℝ
  beOn_nonneg : ∀ τ, 0 ≤ beOn τ

  thFree : ∀ i, (LL →+* ℂ) → C.cls i → C.cls (i + 1) → ℝ
  thFree_nonneg : ∀ i s L L', 0 ≤ thFree i s L L'
namespace MemberForms
attribute [instance] MemberForms.lvAcg MemberForms.lvMod MemberForms.lkAcg MemberForms.lkMod
  MemberForms.clsPFin MemberForms.stabPGrp MemberForms.stabPFin
variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
  (M : MemberForms LL embLL Pl Tau hc C A P)
def ipC (i : ℕ) (φ ψ : C.cls i → C.Y i → ℂ) : ℂ := ∑ c, C.wt i c * M.ipV i c (φ c) (ψ c)
theorem emb_inj (i : ℕ) : Function.Injective (M.emb i) :=
  inj_of_li embLL (M.emb i) (M.lat i).b (M.emb_basis i).1
theorem ptEmb_inj : Function.Injective M.ptEmb :=
  inj_of_li embLL M.ptEmb M.ptLat.b M.ptEmb_basis.1
def S (i : ℕ) (w : Pl.Pl) : Submodule (intW Pl w) (M.lat i).V := locW Pl w (M.lat i).L
def SP (w : Pl.Pl) : Submodule (intW Pl w) M.ptLat.V := locW Pl w M.ptLat.L
def ramSub : Submodule LL (M.lat 0).V := Submodule.comap (M.emb 0) A.Mram
def ramL : Submodule (𝓞 LL) (M.lat 0).V := (M.lat 0).L ⊓ M.ramSub.restrictScalars (𝓞 LL)
def ramLat : HLat LL := { M.lat 0 with L := M.ramL }
def aTop (τ : Tau) : ℤ := (M.lam 0 τ).w ⟨0, R.N_pos 0⟩
def bTop (τ : Tau) : ℤ := -(M.lam 0 τ).detShift
def deg (τ : Tau) : ℤ :=
  (∑ i, (M.lam R.m τ).w i) - (∑ i, (M.sg τ).w i) - ((R.m * (R.t + 1) / 2 : ℕ) : ℤ)
def KRat (i : ℕ) : Prop := ∀ x, ∃ y, M.emb (i + 1) y = C.K i (M.emb i x)
def KL (i : ℕ) (h : M.KRat i) : (M.lat i).V →ₗ[LL] (M.lat (i + 1)).V :=
  descend (M.emb i) (M.emb (i + 1)) (M.emb_inj (i + 1)) (C.Klin i) h
def KIntAt (i : ℕ) (h : M.KRat i) (w : Pl.Pl) : Prop :=
  ∀ x ∈ (M.lat i).L, M.KL i h x ∈ M.S (i + 1) w
def PRat : Prop := ∀ x, ∃ y, M.ptEmb y = P.lowerMap (P.evz (M.emb R.m x))
def PtL (h : M.PRat) : (M.lat R.m).V →ₗ[LL] M.ptLat.V :=
  descend (M.emb R.m) M.ptEmb M.ptEmb_inj (P.lowerMap ∘ₗ P.evz) h
def PtilIntegral (h : M.PRat) : Prop := ∀ x ∈ (M.lat R.m).L, M.PtL h x ∈ M.ptLat.L
def SgInterlace : Prop := ∀ τ (i : Fin (R.N R.m - 1)),
  (M.sg τ).w i ≤ (M.lam R.m τ).w ⟨i.1, by omega⟩ ∧
  (M.lam R.m τ).w ⟨i.1 + 1, by omega⟩ ≤ (M.sg τ).w i
def DnUp : Prop := ∀ i, i ≤ R.m → ∀ v c (x : M.lv i v c), M.fv i v c x = 1 →
  ∃ e : M.lk i v (M.up i v c x) ≃ₗ[A.Fv v] M.lv i v c,
    e (M.te i v (M.up i v c x)) = x ∧
      M.dn i v (M.up i v c x) ((M.fv i v c).comp e.toLinearMap) = c
def DnFv : Prop := ∀ i, i ≤ R.m → ∀ v c (g : Module.Dual (A.Fv v) (M.lk i v c)), g ≠ 0 →
  ∃ e : M.lv i v (M.dn i v c g) ≃ₗ[A.Fv v] M.lk i v c,
    M.fv i v (M.dn i v c g) = g.comp e.toLinearMap ∧
      (g (M.te i v c) = 1 → M.up i v (M.dn i v c g) (e.symm (M.te i v c)) = c)
end MemberForms
def topsOf {R : Ranks} (host : Host R) {Tau : Type} [Fintype Tau] (eTau : Tau ≃ R.Psi) :
    Finset Tau := by
  classical
  exact Finset.univ.filter (fun τ => ((eTau τ : R.Psi) : R.GG) ∈ host.topPlaces)
structure GlobalExtra (LL : Type) [Field LL] [NumberField LL] (Tau : Type) where

  Om : Tau → (LL →+* ℂ) → ℝ
  Om_pos : ∀ τ s, 0 < Om τ s

  thOne : (LL →+* ℂ) → ℝ
  thOne_pos : ∀ s, 0 < thOne s
namespace GlobalExtra
variable {LL : Type} [Field LL] [NumberField LL] {Tau : Type} (G : GlobalExtra LL Tau)
def logOmMean (τ : Tau) : ℝ :=
  (∑ s : LL →+* ℂ, Real.log (G.Om τ s)) / (Fintype.card (LL →+* ℂ) : ℝ)
def OmValue (v logDerivativeAtOne : ℝ) : Prop :=
  ∀ τ, G.logOmMean τ = Real.eulerMascheroniConstant + Real.log (Real.pi / v) - logDerivativeAtOne
end GlobalExtra
end Formalism.BasicNotions


