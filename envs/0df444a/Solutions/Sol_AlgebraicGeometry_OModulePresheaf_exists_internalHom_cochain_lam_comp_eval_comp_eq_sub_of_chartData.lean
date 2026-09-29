-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/175852ec-ea80-5999-b799-10e4e72dc2e2

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import Theorems.Thm_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Y2bSol

p2m_open "AlgebraicGeometry.OModulePresheaf"

theorem isLocallyNoetherian_of_isProper {A : Type u} [CommRing A] [IsNoetherianRing A] {P : Scheme.{u}}
    (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] : IsLocallyNoetherian P :=
  LocallyOfFiniteType.isLocallyNoetherian q

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

section Frame

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
  (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
  (E : ℕ → OModulePresheaf q) (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
  (GE : OModulePresheaf q) (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
  (GK : OModulePresheaf q) (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
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
  (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)

theorem pow_smul_top_eq_bot
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (k : ℕ) (U : P.affineOpens) : I ^ (k + 1) • (⊤ : Submodule A ((F k).obj U.1)) = ⊥ := by
  have htop : (⊤ : Submodule A ((F k).obj U.1)) = Submodule.map ((φ k).app U) ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr (hφs k U)]
  rw [htop, ← Submodule.map_smul'', ← hφk k U]
  exact Submodule.map_le_iff_le_comap.mpr (fun x hx => by simpa using hx) |>.antisymm bot_le

noncomputable def phiIter (W : P.affineOpens) (n : ℕ) : ∀ C : ℕ, (F (n + C)).obj W.1 →ₗ[A] (F n).obj W.1
  | 0 => LinearMap.id
  | C + 1 => (phiIter W n C).comp ((φ (n + C)).app W)

theorem phiIter_lam
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (W : P.affineOpens) (n : ℕ) : ∀ (C : ℕ) (x : GK.obj W.1),
      phiIter F φ W n C ((lam (n + C)).app W x) = (lam n).app W x
  | 0, x => rfl
  | C + 1, x => by
    show phiIter F φ W n C ((φ (n + C)).app W ((lam (n + C + 1)).app W x)) = (lam n).app W x
    rw [← LinearMap.comp_apply ((φ (n + C)).app W), hlamc (n + C) W, phiIter_lam hlamc W n C x]

theorem phiIter_θF
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (n : ℕ) : ∀ (C : ℕ) (x : M i U),
      phiIter F φ U.1 n C (θF i (n + C) U x) = θF i n U x
  | 0, x => rfl
  | C + 1, x => by
    show phiIter F φ U.1 n C ((φ (n + C)).app U.1 (θF i (n + C + 1) U x)) = θF i n U x
    rw [← LinearMap.comp_apply ((φ (n + C)).app U.1), hc1 i (n + C) U, phiIter_θF hc1 i U n C x]

theorem exists_top
    (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)
    (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    (s : K.Idx 1) :
    ∃ τ : ℕ → (OModulePresheaf.internalHom GE GK).obj (K.inter s),
      (∀ k, τ (k + 1) - τ k ∈ I ^ (k + 1) • (⊤ : Submodule A ((OModulePresheaf.internalHom GE GK).obj (K.inter s)))) ∧
      (∀ (k : ℕ) (x : M (s.1 0) ⟨K.affineInter q s, K.inter_le s 0⟩),
        (lam k).app (K.affineInter q s) ((τ k).1 ⟨K.affineInter q s, le_rfl⟩
            (θE (s.1 0) ⟨K.affineInter q s, K.inter_le s 0⟩ x)) =
          θF (s.1 1) k ⟨K.affineInter q s, K.inter_le s 1⟩
              (u (s.1 0) (s.1 1) ⟨K.affineInter q s, K.inter_le s 0⟩ (K.inter_le s 1) x) -
            θF (s.1 0) k ⟨K.affineInter q s, K.inter_le s 0⟩ x) := by
  haveI := isLocallyNoetherian_of_isProper q

  set U : P.affineOpens := K.affineInter q s with hUdef
  have hU0 : U.1 ≤ K.U (s.1 0) := K.inter_le s 0
  have hU1 : U.1 ≤ K.U (s.1 1) := K.inter_le s 1
  set i : K.ι := s.1 0 with hidef
  set j : K.ι := s.1 1 with hjdef
  let Ui : {U : P.affineOpens // U.1 ≤ K.U i} := ⟨U, hU0⟩
  let Uj : {U : P.affineOpens // U.1 ≤ K.U j} := ⟨U, hU1⟩
  letI alg : Algebra A Γ(P, U.1) := Scheme.TwoAffineOpenCover.algebraOfHom q U.1
  letI instMi : Module Γ(P, U.1) (M i Ui) := iΓ i Ui
  letI instMj : Module Γ(P, U.1) (M j Uj) := iΓ j Uj
  haveI : IsNoetherianRing Γ(P, U.1) := IsLocallyNoetherian.component_noetherian U
  haveI : Module.Finite Γ(P, U.1) (GK.obj U.1) := hGKc U
  haveI : Module.Finite Γ(P, U.1) (GE.obj U.1) := hGEc U

  let ϑB : GK.obj U.1 →ₗ[Γ(P, U.1)] M i Ui :=
    { toFun := fun x => ϑ i Ui x, map_add' := fun x y => map_add _ x y, map_smul' := fun a x => hϑs i Ui a x }
  let θEB : M i Ui →ₗ[Γ(P, U.1)] GE.obj U.1 :=
    { toFun := fun x => θE i Ui x, map_add' := fun x y => map_add _ x y, map_smul' := fun a x => hθEs i Ui a x }
  let θB : ∀ k : ℕ, M i Ui →ₗ[Γ(P, U.1)] (F k).obj U.1 := fun k =>
    { toFun := fun x => θF i k Ui x, map_add' := fun x y => map_add _ x y, map_smul' := fun a x => hθFs i k Ui a x }
  let θB' : ∀ k : ℕ, M i Ui →ₗ[Γ(P, U.1)] (F k).obj U.1 := fun k =>
    { toFun := fun x => θF j k Uj (u i j Ui hU1 x)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun a x => by
        show θF j k Uj (u i j Ui hU1 (a • x)) = a • θF j k Uj (u i j Ui hU1 x)
        rw [hus i j Ui hU1 a x]; exact hθFs j k Uj a _ }
  let IB : Ideal Γ(P, U.1) := I.map (algebraMap A Γ(P, U.1))
  have hFB : ∀ k, IB ^ (k + 1) • (⊤ : Submodule Γ(P, U.1) ((F k).obj U.1)) = ⊥ := fun k => by
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [mem_pow_smul_top_iff_of_isScalarTower (A := A), pow_smul_top_eq_bot I F φ hφs hφk k U] at hx
    exact hx
  have hlamcB : ∀ k, (φ k).appSections U ∘ₗ (lam (k + 1)).appSections U = (lam k).appSections U := fun k =>
    LinearMap.ext fun x => congrFun (congrArg DFunLike.coe (hlamc k U)) x
  obtain ⟨c0, hc0⟩ := hlami U
  have hlamiB : ∀ k, LinearMap.ker ((lam (k + c0)).appSections U) ≤ IB ^ (k + 1) • (⊤ : Submodule Γ(P, U.1) (GK.obj U.1)) :=
    fun k x hx => (mem_pow_smul_top_iff_of_isScalarTower (A := A) I (k + 1) x).mpr (hc0 k hx)
  have hlamrB : ∀ k, LinearMap.range ((lam k).appSections U) = LinearMap.ker ((ε k).appSections U) := fun k => by
    ext x
    have := SetLike.ext_iff.mp (hlamr k U) x
    simpa only [LinearMap.mem_range, LinearMap.mem_ker, AffHom.appSections_apply] using this
  have hexB : LinearMap.range ϑB = LinearMap.ker θEB := by
    ext x
    have := SetLike.ext_iff.mp (hexact i Ui) x
    simp only [LinearMap.mem_range, LinearMap.mem_ker] at this
    exact this
  have hθEBs : Function.Surjective θEB := hsurj i Ui
  have hθc : ∀ k, (φ k).appSections U ∘ₗ θB (k + 1) = θB k := fun k =>
    LinearMap.ext fun x => congrFun (congrArg DFunLike.coe (hc1 i k Ui)) x
  have hθ'c : ∀ k, (φ k).appSections U ∘ₗ θB' (k + 1) = θB' k := fun k =>
    LinearMap.ext fun x => congrFun (congrArg DFunLike.coe (hc1 j k Uj)) (u i j Ui hU1 x)
  have hθϑ : ∀ k, θB k ∘ₗ ϑB = (lam k).appSections U := fun k =>
    LinearMap.ext fun x => congrFun (congrArg DFunLike.coe (hc2 i k Ui)) x
  have hθ'ϑ : ∀ k, θB' k ∘ₗ ϑB = (lam k).appSections U := fun k => LinearMap.ext fun x => by
    show θF j k Uj (u i j Ui hU1 (ϑ i Ui x)) = (lam k).app U x
    rw [huϑ i j Ui hU1 x]
    exact congrFun (congrArg DFunLike.coe (hc2 j k Uj)) x
  have hθε : ∀ k, (ε k).appSections U ∘ₗ θB k = (ε k).appSections U ∘ₗ θB' k := fun k => LinearMap.ext fun x => by
    show (ε k).app U (θF i k Ui x) = (ε k).app U (θF j k Uj (u i j Ui hU1 x))
    have h1 := congrFun (congrArg DFunLike.coe (hc3 i k Ui)) x
    have h2 := congrFun (congrArg DFunLike.coe (hc3 j k Uj)) (u i j Ui hU1 x)
    simp only [LinearMap.comp_apply] at h1 h2
    rw [h1, h2, huθE i j Ui hU1 x]
  obtain ⟨g, hg1, hg2⟩ :=
    LinearMap.exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq
      IB ϑB θEB hexB hθEBs (fun k => (F k).obj U.1) (fun k => (φ k).appSections U) hFB
      (fun k => (lam k).appSections U) hlamcB c0 hlamiB (fun k => (E k).obj U.1) (fun k => (ε k).appSections U) hlamrB
      θB θB' hθc hθ'c hθϑ hθ'ϑ hθε
  refine ⟨fun k => (topEquiv hGEc hGEq hGKc hGKq U).symm (g k), fun k => ?_, fun k x => ?_⟩
  · apply mem_pow_smul_top_of_top I hGEc hGEq hGKc hGKq U (k + 1)
    rw [map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hg1 k
  · have h := congrFun (congrArg DFunLike.coe (hg2 k)) x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, AffHom.appSections_apply] at h
    rw [topEquiv_symm_top]
    exact h.symm

theorem evalId
    (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
    (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (s : K.Idx 1) (k : ℕ) (τk : (OModulePresheaf.internalHom GE GK).obj (K.inter s))
    (htop : ∀ x : M (s.1 0) ⟨K.affineInter q s, K.inter_le s 0⟩,
        (lam k).app (K.affineInter q s) (τk.1 ⟨K.affineInter q s, le_rfl⟩
            (θE (s.1 0) ⟨K.affineInter q s, K.inter_le s 0⟩ x)) =
          θF (s.1 1) k ⟨K.affineInter q s, K.inter_le s 1⟩
              (u (s.1 0) (s.1 1) ⟨K.affineInter q s, K.inter_le s 0⟩ (K.inter_le s 1) x) -
            θF (s.1 0) k ⟨K.affineInter q s, K.inter_le s 0⟩ x)
    (W : OModulePresheaf.AffBelow (K.inter s)) (x : M (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩) :
    (lam k).app W.1 (τk.1 W (θE (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x)) =
      θF (s.1 1) k ⟨W.1, W.2.trans (K.inter_le s 1)⟩
          (u (s.1 0) (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 1)) x) -
        θF (s.1 0) k ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x := by
  haveI := isLocallyNoetherian_of_isProper q

  let Wi : OModulePresheaf.AffBelow (K.inter s) → {U : P.affineOpens // U.1 ≤ K.U (s.1 0)} :=
    fun W => ⟨W.1, W.2.trans (K.inter_le s 0)⟩
  let Wj : OModulePresheaf.AffBelow (K.inter s) → {U : P.affineOpens // U.1 ≤ K.U (s.1 1)} :=
    fun W => ⟨W.1, W.2.trans (K.inter_le s 1)⟩

  let D : ∀ W : OModulePresheaf.AffBelow (K.inter s), M (s.1 0) (Wi W) →ₗ[A] (F k).obj W.1.1 := fun W =>
    (θF (s.1 1) k (Wj W)).comp (u (s.1 0) (s.1 1) (Wi W) (W.2.trans (K.inter_le s 1))) - θF (s.1 0) k (Wi W)
  have hD : ∀ (W : OModulePresheaf.AffBelow (K.inter s)) (y : M (s.1 0) (Wi W)),
      D W y = θF (s.1 1) k (Wj W) (u (s.1 0) (s.1 1) (Wi W) (W.2.trans (K.inter_le s 1)) y) - θF (s.1 0) k (Wi W) y :=
    fun W y => rfl
  have hDϑ : ∀ (W : OModulePresheaf.AffBelow (K.inter s)) (z : GK.obj W.1.1), D W (ϑ (s.1 0) (Wi W) z) = 0 := by
    intro W z
    have h1 := congrFun (congrArg DFunLike.coe (hc2 (s.1 1) k (Wj W))) z
    have h2 := congrFun (congrArg DFunLike.coe (hc2 (s.1 0) k (Wi W))) z
    simp only [LinearMap.comp_apply] at h1 h2
    rw [hD, huϑ, h1, h2]
    exact sub_self _
  have hker : ∀ W : OModulePresheaf.AffBelow (K.inter s),
      LinearMap.ker (θE (s.1 0) (Wi W)) ≤ LinearMap.ker (D W) := by
    intro W y hy
    rw [← hexact] at hy
    obtain ⟨z, rfl⟩ := hy
    exact hDϑ W z

  let δ : ∀ W : OModulePresheaf.AffBelow (K.inter s), GE.obj W.1.1 →ₗ[A] (F k).obj W.1.1 := fun W =>
    ((LinearMap.ker (θE (s.1 0) (Wi W))).liftQ (D W) (hker W)).comp
      ((θE (s.1 0) (Wi W)).quotKerEquivOfSurjective (hsurj (s.1 0) (Wi W))).symm.toLinearMap
  have hδ : ∀ (W : OModulePresheaf.AffBelow (K.inter s)) (y : M (s.1 0) (Wi W)),
      δ W (θE (s.1 0) (Wi W) y) = D W y := by
    intro W y
    have hq : ((θE (s.1 0) (Wi W)).quotKerEquivOfSurjective (hsurj (s.1 0) (Wi W))).symm (θE (s.1 0) (Wi W) y) =
        Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    show (LinearMap.ker (θE (s.1 0) (Wi W))).liftQ (D W) (hker W)
      (((θE (s.1 0) (Wi W)).quotKerEquivOfSurjective (hsurj (s.1 0) (Wi W))).symm (θE (s.1 0) (Wi W) y)) = D W y
    rw [hq, Submodule.liftQ_apply]

  let Φ2 : (OModulePresheaf.internalHom GE (F k)).obj (K.inter s) :=
    ⟨fun W => δ W, by
      refine ⟨fun W a y => ?_, fun W W' h y => ?_⟩
      · obtain ⟨x, rfl⟩ := hsurj (s.1 0) (Wi W) y
        change δ W (a • θE (s.1 0) (Wi W) x) = a • δ W (θE (s.1 0) (Wi W) x)
        rw [← hθEs (s.1 0) (Wi W) a x, hδ, hδ, hD, hD, hus (s.1 0) (s.1 1) (Wi W) (W.2.trans (K.inter_le s 1)) a x,
          hθFs (s.1 1) k (Wj W) a, hθFs (s.1 0) k (Wi W) a x, smul_sub]
      · obtain ⟨x, rfl⟩ := hsurj (s.1 0) (Wi W') y
        change δ W (GE.res h (θE (s.1 0) (Wi W') x)) = (F k).res h (δ W' (θE (s.1 0) (Wi W') x))
        rw [← hθEn (s.1 0) (Wi W') (Wi W) h x, hδ, hδ, hD, hD,
          hun (s.1 0) (s.1 1) (Wi W') (Wi W) (W'.2.trans (K.inter_le s 1)) h x,
          hθFn (s.1 1) k (Wj W') (Wj W) h, hθFn (s.1 0) k (Wi W') (Wi W) h x, map_sub]⟩
  let Φ1 : (OModulePresheaf.internalHom GE (F k)).obj (K.inter s) :=
    ⟨fun W => ((lam k).app W.1).comp (τk.1 W), by
      refine ⟨fun W a y => ?_, fun W W' h y => ?_⟩
      · show (lam k).app W.1 (τk.1 W (a • y)) = a • (lam k).app W.1 (τk.1 W y)
        rw [τk.2.1 W a y, (lam k).app_smul]
      · show (lam k).app W.1 (τk.1 W (GE.res h y)) = (F k).res h ((lam k).app W'.1 (τk.1 W' y))
        rw [τk.2.2 W W' h y, (lam k).naturality_apply]⟩
  have hΦ : Φ1 = Φ2 := by
    refine ext_of_top hGEc hGEq (hFc k) (hFq k) (K.affineInter q s) Φ1 Φ2 fun y => ?_
    obtain ⟨x, rfl⟩ := hsurj (s.1 0) (Wi ⟨K.affineInter q s, le_rfl⟩) y
    change (lam k).app (K.affineInter q s) (τk.1 ⟨K.affineInter q s, le_rfl⟩
        (θE (s.1 0) (Wi ⟨K.affineInter q s, le_rfl⟩) x)) =
      δ ⟨K.affineInter q s, le_rfl⟩ (θE (s.1 0) (Wi ⟨K.affineInter q s, le_rfl⟩) x)
    rw [hδ]
    exact htop x
  have hW : Φ1.1 W = Φ2.1 W := by rw [hΦ]
  have hWx := LinearMap.congr_fun hW (θE (s.1 0) (Wi W) x)
  change (lam k).app W.1 (τk.1 W (θE (s.1 0) (Wi W) x)) = δ W (θE (s.1 0) (Wi W) x) at hWx
  rw [hδ] at hWx
  exact hWx

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
    :
    ∃ t : ℕ → (OModulePresheaf.internalHom GE GK).cochain K 1,

      (∀ (n : ℕ) (s : K.Idx 1) (W : OModulePresheaf.AffBelow (K.inter s)) (x : M (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩),
        (lam n).app W.1 (OModulePresheaf.internalHom.eval GE GK W.1 W.2 (t n s) (θE (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x)) =
          θF (s.1 1) n ⟨W.1, W.2.trans (K.inter_le s 1)⟩ (u (s.1 0) (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 1)) x) - θF (s.1 0) n ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x) ∧

      (∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A ((OModulePresheaf.internalHom GE GK).cochain K 1))) := by
  haveI := Y2bSol.isLocallyNoetherian_of_isProper q
  choose τ hτc hτt using fun s : K.Idx 1 =>
    Y2bSol.exists_top (I := I) (F := F) (φ := φ) (E := E) (ε := ε) (GE := GE) (ψE := ψE) (GK := GK) (lam := lam) (K := K)
      (M := M) (ϑ := ϑ) (θE := θE) (θF := θF) (u := u) hFc hFq hφs hφk hGEc hGEq hGKc hGKq hlamc hlamr hlami
      hϑs hθEs hθFs hexact hsurj hc1 hc2 hc3 hus huϑ huθE s
  refine ⟨fun n s => τ s n, fun n s W x => ?_, fun n => ?_⟩
  · exact Y2bSol.evalId (F := F) (GE := GE) (GK := GK) (lam := lam) (K := K) (M := M) (res := res) (ϑ := ϑ)
      (θE := θE) (θF := θF) (u := u) hFc hFq hGEc hGEq hθEs hθFs hθEn hθFn hexact hsurj hc2 hus hun huϑ
      s n (τ s n) (hτt s n) W x
  · exact Y2bSol.pi_mem_smul_top _ (I ^ (n + 1)) _ (fun s => hτc s n)

end S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData (solution)
