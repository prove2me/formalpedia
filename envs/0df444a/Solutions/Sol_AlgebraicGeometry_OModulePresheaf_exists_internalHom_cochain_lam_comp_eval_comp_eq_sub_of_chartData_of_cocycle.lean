-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2e6dd824-9043-5625-b8cb-3b13a727a17a

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq
import Theorems.Thm_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Y2bSol

p2m_open "AlgebraicGeometry.OModulePresheaf"

section General

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

theorem pi_mem_smul_top {ι : Type u} [Fintype ι] [DecidableEq ι] (N : ι → Type u)
    [∀ s, AddCommGroup (N s)] [∀ s, Module A (N s)] (J : Ideal A) (c : ∀ s, N s)
    (hc : ∀ s, c s ∈ J • (⊤ : Submodule A (N s))) : c ∈ J • (⊤ : Submodule A (∀ s, N s)) := by
  classical
  rw [← Finset.univ_sum_single c]
  refine Submodule.sum_mem _ fun s _ => ?_
  have : (LinearMap.single A N s) (c s) ∈ (J • (⊤ : Submodule A (N s))).map (LinearMap.single A N s) :=
    Submodule.mem_map_of_mem (hc s)
  rw [Submodule.map_smul''] at this
  simpa only [LinearMap.coe_single] using Submodule.smul_mono le_rfl le_top this

theorem mem_pow_smul_top_iff_of_isScalarTower {B : Type u} [CommRing B] [Algebra A B] (I : Ideal A) (n : ℕ)
    {N : Type u} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] (x : N) :
    x ∈ (I.map (algebraMap A B)) ^ n • (⊤ : Submodule B N) ↔ x ∈ I ^ n • (⊤ : Submodule A N) := by
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem A, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

variable (F G : OModulePresheaf q)

noncomputable def evalTop (U : P.affineOpens) :
    (internalHom F G).obj U.1 →ₗ[Γ(P, U.1)] (F.obj U.1 →ₗ[Γ(P, U.1)] G.obj U.1) where
  toFun φ :=
    { toFun := fun x => φ.1 ⟨U, le_rfl⟩ x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => φ.2.1 ⟨U, le_rfl⟩ a x }
  map_add' φ ψ := by ext x; rfl
  map_smul' b φ := by
    ext x
    change (b • φ).1 ⟨U, le_rfl⟩ x = b • φ.1 ⟨U, le_rfl⟩ x
    rw [internalHom_smul_apply]
    congr 1
    simp

theorem evalTop_apply (U : P.affineOpens) (φ : (internalHom F G).obj U.1) (x : F.obj U.1) :
    evalTop F G U φ x = φ.1 ⟨U, le_rfl⟩ x := rfl

variable {F G} [IsLocallyNoetherian P]

theorem evalTop_bijective (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (U : P.affineOpens) : Function.Bijective (evalTop F G U) := by
  obtain ⟨-, -, huniq⟩ := AlgebraicGeometry.OModulePresheaf.isCoherent_internalHom_and_existsUnique_eval_eq q F G hFc hFq hGc hGq
  refine ⟨fun φ ψ h => ?_, fun f => ?_⟩
  · exact (huniq U (evalTop F G U φ)).unique (fun x => rfl) (fun x => by rw [h]; rfl)
  · obtain ⟨φ, hφ, -⟩ := huniq U f
    exact ⟨φ, LinearMap.ext hφ⟩

noncomputable def topEquiv (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (U : P.affineOpens) : (internalHom F G).obj U.1 ≃ₗ[Γ(P, U.1)] (F.obj U.1 →ₗ[Γ(P, U.1)] G.obj U.1) :=
  LinearEquiv.ofBijective (evalTop F G U) (evalTop_bijective hFc hFq hGc hGq U)

theorem topEquiv_apply (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (U : P.affineOpens) (φ : (internalHom F G).obj U.1) (x : F.obj U.1) :
    topEquiv hFc hFq hGc hGq U φ x = φ.1 ⟨U, le_rfl⟩ x := rfl

theorem topEquiv_symm_top (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (U : P.affineOpens) (f : F.obj U.1 →ₗ[Γ(P, U.1)] G.obj U.1) (x : F.obj U.1) :
    ((topEquiv hFc hFq hGc hGq U).symm f).1 ⟨U, le_rfl⟩ x = f x := by
  rw [← topEquiv_apply hFc hFq hGc hGq U, LinearEquiv.apply_symm_apply]

theorem ext_of_top (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (U : P.affineOpens) (φ ψ : (internalHom F G).obj U.1)
    (h : ∀ x : F.obj U.1, φ.1 ⟨U, le_rfl⟩ x = ψ.1 ⟨U, le_rfl⟩ x) : φ = ψ :=
  (evalTop_bijective hFc hFq hGc hGq U).1 (LinearMap.ext h)

theorem mem_pow_smul_top_of_top (I : Ideal A) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hGc : G.IsCoherent)
    (hGq : G.IsQuasicoherent) (U : P.affineOpens) (n : ℕ) (φ : (internalHom F G).obj U.1)
    (h : letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1
      topEquiv hFc hFq hGc hGq U φ ∈ (I.map (algebraMap A Γ(P, U.1))) ^ n •
        (⊤ : Submodule Γ(P, U.1) (F.obj U.1 →ₗ[Γ(P, U.1)] G.obj U.1))) :
    φ ∈ I ^ n • (⊤ : Submodule A ((internalHom F G).obj U.1)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1
  haveI : IsScalarTower A Γ(P, U.1) ((internalHom F G).obj U.1) := (internalHom F G).isScalarTower U.1
  rw [← mem_pow_smul_top_iff_of_isScalarTower (B := Γ(P, U.1))]
  have := Submodule.mem_map_of_mem (f := (topEquiv hFc hFq hGc hGq U).symm.toLinearMap) h
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at this
  simpa using this

end General

section Cech

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

namespace Idx

variable (K : V.OrderedAffineCover)

def pair (a b : K.ι) (h : a < b) : K.Idx 1 :=
  ⟨![a, b], fun x y hxy => by
    fin_cases x <;> fin_cases y
    · exact absurd hxy (lt_irrefl _)
    · exact h
    · exact absurd hxy (by decide)
    · exact absurd hxy (lt_irrefl _)⟩

theorem le_inter_pair {a b : K.ι} (h : a < b) {W : V.Opens} (ha : W ≤ K.U a) (hb : W ≤ K.U b) :
    W ≤ K.inter (pair K a b h) :=
  le_iInf fun j => by
    fin_cases j
    · exact ha
    · exact hb

def triple (a b c : K.ι) (hab : a < b) (hbc : b < c) : K.Idx 2 :=
  ⟨![a, b, c], fun x y hxy => by
    fin_cases x <;> fin_cases y
    · exact absurd hxy (lt_irrefl _)
    · exact hab
    · exact hab.trans hbc
    · exact absurd hxy (by decide)
    · exact absurd hxy (lt_irrefl _)
    · exact hbc
    · exact absurd hxy (by decide)
    · exact absurd hxy (by decide)
    · exact absurd hxy (lt_irrefl _)⟩

theorem eq_triple (σ : K.Idx 2) :
    σ = triple K (σ.1 0) (σ.1 1) (σ.1 2) (σ.2 (by decide)) (σ.2 (by decide)) := by
  refine Subtype.ext (funext fun x => ?_)
  fin_cases x <;> rfl

theorem face_triple_zero (a b c : K.ι) (hab : a < b) (hbc : b < c) :
    K.face (triple K a b c hab hbc) 0 = pair K b c hbc := by
  refine Subtype.ext (funext fun x => ?_)
  fin_cases x <;> rfl

theorem face_triple_one (a b c : K.ι) (hab : a < b) (hbc : b < c) :
    K.face (triple K a b c hab hbc) 1 = pair K a c (hab.trans hbc) := by
  refine Subtype.ext (funext fun x => ?_)
  fin_cases x <;> rfl

theorem face_triple_two (a b c : K.ι) (hab : a < b) (hbc : b < c) :
    K.face (triple K a b c hab hbc) 2 = pair K a b hab := by
  refine Subtype.ext (funext fun x => ?_)
  fin_cases x <;> rfl

theorem le_inter_triple {a b c : K.ι} (hab : a < b) (hbc : b < c) {W : V.Opens} (ha : W ≤ K.U a)
    (hb : W ≤ K.U b) (hc : W ≤ K.U c) : W ≤ K.inter (triple K a b c hab hbc) :=
  le_iInf fun j => by
    fin_cases j
    · exact ha
    · exact hb
    · exact hc

end Idx

theorem d_one_apply (H : OModulePresheaf π) (K : V.OrderedAffineCover) (c : H.cochain K 1) (t : K.Idx 2) :
    H.d K 1 c t = H.res (K.inter_le_inter_face t 0) (c (K.face t 0)) -
      H.res (K.inter_le_inter_face t 1) (c (K.face t 1)) +
      H.res (K.inter_le_inter_face t 2) (c (K.face t 2)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_three]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, one_smul, Fin.val_two,
    neg_one_sq]
  rw [sub_eq_add_neg]

variable (F G : OModulePresheaf π)

theorem add_val_apply {U : V.Opens} (φ ψ : (internalHom F G).obj U) (W : AffBelow U) (x : F.obj W.1.1) :
    (φ + ψ).1 W x = φ.1 W x + ψ.1 W x := rfl

theorem sub_val_apply {U : V.Opens} (φ ψ : (internalHom F G).obj U) (W : AffBelow U) (x : F.obj W.1.1) :
    (φ - ψ).1 W x = φ.1 W x - ψ.1 W x := rfl

end Cech

section Frame

theorem isLocallyNoetherian_of_isProper {A : Type u} [CommRing A] [IsNoetherianRing A] {P : Scheme.{u}}
    (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] : IsLocallyNoetherian P :=
  LocallyOfFiniteType.isLocallyNoetherian q

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

noncomputable def phiIter (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (W : P.affineOpens) (n : ℕ) : ∀ C : ℕ, (F (n + C)).obj W.1 →ₗ[A] (F n).obj W.1
  | 0 => LinearMap.id
  | C + 1 => (phiIter F φ W n C).comp ((φ (n + C)).app W)

theorem phiIter_lam (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (GK : OModulePresheaf q) (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (W : P.affineOpens) (n : ℕ) : ∀ (C : ℕ) (x : GK.obj W.1),
      phiIter F φ W n C ((lam (n + C)).app W x) = (lam n).app W x
  | 0, _ => rfl
  | C + 1, x => by
    show phiIter F φ W n C ((φ (n + C)).app W ((lam (n + C + 1)).app W x)) = (lam n).app W x
    rw [← LinearMap.comp_apply ((φ (n + C)).app W), hlamc (n + C) W, phiIter_lam F φ GK lam hlamc W n C x]

theorem phiIter_θF (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (K : P.OrderedAffineCover) (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (n : ℕ) : ∀ (C : ℕ) (x : M i U),
      phiIter F φ U.1 n C (θF i (n + C) U x) = θF i n U x
  | 0, _ => rfl
  | C + 1, x => by
    show phiIter F φ U.1 n C ((φ (n + C)).app U.1 (θF i (n + C + 1) U x)) = θF i n U x
    rw [← LinearMap.comp_apply ((φ (n + C)).app U.1), hc1 i (n + C) U, phiIter_θF F φ K M θF hc1 i U n C x]

theorem lam_d_val_eq_zero (F : ℕ → OModulePresheaf q) (GE GK : OModulePresheaf q)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (K : P.OrderedAffineCover) (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
    (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    (hcocy : ∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u j l ⟨W.1, hj⟩ hl (u i j W hj x) = u i l W hl x)
    (T : (internalHom GE GK).cochain K 1) (k : ℕ)
    (H1 : ∀ (s : K.Idx 1) (W : AffBelow (K.inter s)) (x : M (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩),
      (lam k).app W.1 (internalHom.eval GE GK W.1 W.2 (T s) (θE (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x)) =
        θF (s.1 1) k ⟨W.1, W.2.trans (K.inter_le s 1)⟩
            (u (s.1 0) (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 1)) x) -
          θF (s.1 0) k ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x)
    {a b c : K.ι} (hab : a < b) (hbc : b < c) (W : P.affineOpens)
    (ha : W.1 ≤ K.U a) (hb : W.1 ≤ K.U b) (hc : W.1 ≤ K.U c) (e : GE.obj W.1) :
    (lam k).app W (((internalHom GE GK).d K 1 T (Idx.triple K a b c hab hbc)).1
      ⟨W, Idx.le_inter_triple K hab hbc ha hb hc⟩ e) = 0 := by
  obtain ⟨x, rfl⟩ := hsurj a ⟨W, ha⟩ e
  have key : ∀ (s : K.Idx 1) (i j : K.ι) (hij : i < j) (hs : s = Idx.pair K i j hij)
      (h : K.inter (Idx.triple K a b c hab hbc) ≤ K.inter s) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (v : GE.obj W.1),
      ((internalHom GE GK).res h (T s)).1 ⟨W, Idx.le_inter_triple K hab hbc ha hb hc⟩ v =
        (T (Idx.pair K i j hij)).1 ⟨W, Idx.le_inter_pair K hij hi hj⟩ v := by
    rintro s i j hij rfl h hi hj v; rfl
  have ebc : (lam k).app W ((T (Idx.pair K b c hbc)).1 ⟨W, Idx.le_inter_pair K hbc hb hc⟩ (θE a ⟨W, ha⟩ x)) =
      θF c k ⟨W, hc⟩ (u a c ⟨W, ha⟩ hc x) - θF b k ⟨W, hb⟩ (u a b ⟨W, ha⟩ hb x) := by
    have h : (lam k).app W ((T (Idx.pair K b c hbc)).1 ⟨W, Idx.le_inter_pair K hbc hb hc⟩
        (θE b ⟨W, hb⟩ (u a b ⟨W, ha⟩ hb x))) =
        θF c k ⟨W, hc⟩ (u b c ⟨W, hb⟩ hc (u a b ⟨W, ha⟩ hb x)) - θF b k ⟨W, hb⟩ (u a b ⟨W, ha⟩ hb x) :=
      H1 (Idx.pair K b c hbc) ⟨W, Idx.le_inter_pair K hbc hb hc⟩ (u a b ⟨W, ha⟩ hb x)
    rw [huθE a b ⟨W, ha⟩ hb x, hcocy a b c ⟨W, ha⟩ hb hc x] at h
    exact h
  have eac : (lam k).app W ((T (Idx.pair K a c (hab.trans hbc))).1
        ⟨W, Idx.le_inter_pair K (hab.trans hbc) ha hc⟩ (θE a ⟨W, ha⟩ x)) =
      θF c k ⟨W, hc⟩ (u a c ⟨W, ha⟩ hc x) - θF a k ⟨W, ha⟩ x :=
    H1 (Idx.pair K a c (hab.trans hbc)) ⟨W, Idx.le_inter_pair K (hab.trans hbc) ha hc⟩ x
  have eab : (lam k).app W ((T (Idx.pair K a b hab)).1 ⟨W, Idx.le_inter_pair K hab ha hb⟩ (θE a ⟨W, ha⟩ x)) =
      θF b k ⟨W, hb⟩ (u a b ⟨W, ha⟩ hb x) - θF a k ⟨W, ha⟩ x :=
    H1 (Idx.pair K a b hab) ⟨W, Idx.le_inter_pair K hab ha hb⟩ x
  rw [d_one_apply, add_val_apply, sub_val_apply,
    key _ b c hbc (Idx.face_triple_zero K a b c hab hbc) _ hb hc,
    key _ a c (hab.trans hbc) (Idx.face_triple_one K a b c hab hbc) _ ha hc,
    key _ a b hab (Idx.face_triple_two K a b c hab hbc) _ ha hb,
    map_add, map_sub, ebc, eac, eab]
  abel

theorem exists_shift_d_mem [IsNoetherianRing A] (I : Ideal A) [IsProper q]
    (F : ℕ → OModulePresheaf q) (GE GK : OModulePresheaf q)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (K : P.OrderedAffineCover) (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
    (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    (hcocy : ∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u j l ⟨W.1, hj⟩ hl (u i j W hj x) = u i l W hl x)
    (t : ℕ → (internalHom GE GK).cochain K 1)
    (H1 : ∀ (n : ℕ) (s : K.Idx 1) (W : AffBelow (K.inter s)) (x : M (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩),
      (lam n).app W.1 (internalHom.eval GE GK W.1 W.2 (t n s) (θE (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x)) =
        θF (s.1 1) n ⟨W.1, W.2.trans (K.inter_le s 1)⟩
            (u (s.1 0) (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 1)) x) -
          θF (s.1 0) n ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x)
    (σ : K.Idx 2) :
    ∃ cσ : ℕ, ∀ n : ℕ, (internalHom GE GK).d K 1 (t (n + cσ)) σ ∈
      I ^ (n + 1) • (⊤ : Submodule A ((internalHom GE GK).obj (K.inter σ))) := by
  haveI := isLocallyNoetherian_of_isProper q
  obtain ⟨a, b, c, hab, hbc, rfl⟩ :
      ∃ (a b c : K.ι) (hab : a < b) (hbc : b < c), σ = Idx.triple K a b c hab hbc :=
    ⟨_, _, _, _, _, Idx.eq_triple K σ⟩
  set U : P.affineOpens := K.affineInter q (Idx.triple K a b c hab hbc) with hUdef
  have hUa : U.1 ≤ K.U a := K.inter_le (Idx.triple K a b c hab hbc) 0
  have hUb : U.1 ≤ K.U b := K.inter_le (Idx.triple K a b c hab hbc) 1
  have hUc : U.1 ≤ K.U c := K.inter_le (Idx.triple K a b c hab hbc) 2
  letI alg : Algebra A Γ(P, U.1) := Scheme.TwoAffineOpenCover.algebraOfHom q U.1
  haveI : IsNoetherianRing Γ(P, U.1) := IsLocallyNoetherian.component_noetherian U
  haveI : Module.Finite Γ(P, U.1) (GK.obj U.1) := hGKc U
  haveI : Module.Finite Γ(P, U.1) (GE.obj U.1) := hGEc U
  obtain ⟨c0, hc0⟩ := hlami U
  obtain ⟨c1, hc1⟩ := LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul
    (I.map (algebraMap A Γ(P, U.1))) (M := GE.obj U.1) (N := GK.obj U.1)
  refine ⟨c1 + c0, fun n => ?_⟩
  rw [← Nat.add_assoc]
  apply mem_pow_smul_top_of_top I hGEc hGEq hGKc hGKq U (n + 1)
  apply hc1 (n + 1)
  intro y hy
  obtain ⟨e, rfl⟩ := LinearMap.mem_range.mp hy
  rw [topEquiv_apply, mem_pow_smul_top_iff_of_isScalarTower (A := A), show n + 1 + c1 = n + c1 + 1 from by omega]
  apply hc0 (n + c1)
  rw [LinearMap.mem_ker]
  exact lam_d_val_eq_zero F GE GK lam K M θE θF u hsurj huθE hcocy (t (n + c1 + c0)) (n + c1 + c0)
    (H1 (n + c1 + c0)) hab hbc U hUa hUb hUc e

end Frame

end Y2bSol

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q)
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (K : P.OrderedAffineCover)
    (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
    [iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U)]
    (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
    (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
    (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)

    (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
    (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    (hcocy : ∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u j l ⟨W.1, hj⟩ hl (u i j W hj x) = u i l W hl x)
    :
    ∃ t : ℕ → (OModulePresheaf.internalHom GE GK).cochain K 1,

      (∀ (n : ℕ) (s : K.Idx 1) (W : OModulePresheaf.AffBelow (K.inter s)) (x : M (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩),
        (lam n).app W.1 (OModulePresheaf.internalHom.eval GE GK W.1 W.2 (t n s) (θE (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x)) =
          θF (s.1 1) n ⟨W.1, W.2.trans (K.inter_le s 1)⟩ (u (s.1 0) (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 1)) x) - θF (s.1 0) n ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x) ∧

      (∀ n : ℕ, (OModulePresheaf.internalHom GE GK).d K 1 (t n) ∈
        I ^ (n + 1) • (⊤ : Submodule A ((OModulePresheaf.internalHom GE GK).cochain K 2))) ∧

      (∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A ((OModulePresheaf.internalHom GE GK).cochain K 1))) := by
  haveI := Y2bSol.isLocallyNoetherian_of_isProper q

  obtain ⟨t, ht1, ht3⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData I q F hFc hFq
      φ hφs hφk E ε GE hGEc hGEq ψE GK hGKc hGKq lam hlamc hlamr hlami K M res ϑ θE θF hϑs hθEs hθFs hθEn hθFn
      hexact hsurj hc1 hc2 hc3 u hus hun huϑ huθE

  have hσ := fun σ : K.Idx 2 =>
    Y2bSol.exists_shift_d_mem I F GE GK lam K M θE θF u hGEc hGEq hGKc hGKq hlami hsurj huθE hcocy t ht1 σ
  choose cσ hcσ using hσ
  refine ⟨fun n => t (n + Finset.univ.sup cσ), ?_, ?_, ?_⟩
  ·
    intro n s W x
    have h := congrArg (Y2bSol.phiIter F φ W.1 n (Finset.univ.sup cσ)) (ht1 (n + Finset.univ.sup cσ) s W x)
    rw [Y2bSol.phiIter_lam F φ GK lam hlamc, map_sub,
      Y2bSol.phiIter_θF F φ K M θF hc1 (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 1)⟩,
      Y2bSol.phiIter_θF F φ K M θF hc1 (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩] at h
    exact h
  ·
    intro n
    refine Y2bSol.pi_mem_smul_top (fun σ : K.Idx 2 => (OModulePresheaf.internalHom GE GK).obj (K.inter σ)) _ _ fun σ => ?_
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := cσ) (Finset.mem_univ σ))
    have h := hcσ σ (n + d)
    rw [show n + d + cσ σ = n + Finset.univ.sup cσ from by omega] at h
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) h
  ·
    intro n
    have h := ht3 (n + Finset.univ.sup cσ)
    rw [show n + Finset.univ.sup cσ + 1 = n + 1 + Finset.univ.sup cσ from by omega] at h
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) h

end S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle (solution)
