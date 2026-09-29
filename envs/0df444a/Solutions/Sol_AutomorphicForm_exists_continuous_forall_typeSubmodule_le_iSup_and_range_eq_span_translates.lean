-- Prove2me | solution 1 for AutomorphicForm.exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5ce4b2f4-2806-5d5b-a022-9551c7305212

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Theorems.Thm_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective
import Theorems.Thm_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates

set_option autoImplicit false

open AutomorphicForm

namespace Ws49
namespace K1

section Translation

variable {K G : Type*} [Group K] [Group G]

def Rtr (ι : K →* G) (k : K) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun u y := u (y * ι k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Rtr_apply (ι : K →* G) (k : K) (u : G → ℂ) (y : G) : Rtr ι k u y = u (y * ι k) := rfl

def Rrep (ι : K →* G) (V : Submodule ℂ (G → ℂ)) (hV : ∀ k : K, ∀ u ∈ V, Rtr ι k u ∈ V) :
    Representation ℂ K V where
  toFun k := (Rtr ι k).restrict (hV k)
  map_one' := by
    refine LinearMap.ext fun u => Subtype.ext (funext fun y => ?_)
    show (u : G → ℂ) (y * ι 1) = (u : G → ℂ) y
    rw [map_one, mul_one]
  map_mul' a c := by
    refine LinearMap.ext fun u => Subtype.ext (funext fun y => ?_)
    show (u : G → ℂ) (y * ι (a * c)) = (u : G → ℂ) (y * ι a * ι c)
    rw [map_mul, mul_assoc]

theorem Rrep_apply (ι : K →* G) (V : Submodule ℂ (G → ℂ)) (hV : ∀ k : K, ∀ u ∈ V, Rtr ι k u ∈ V)
    (k : K) (u : V) (y : G) : (Rrep ι V hV k u : G → ℂ) y = (u : G → ℂ) (y * ι k) := rfl

def Py (ι : K →* G) (y : G) : (G → ℂ) →ₗ[ℂ] (K → ℂ) where
  toFun g k := g (y * ι k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Py_apply (ι : K →* G) (y : G) (g : G → ℂ) (k : K) : Py ι y g k = g (y * ι k) := rfl

theorem Py_mem_typeSubmodule {W : Type*} [AddCommGroup W] [Module ℂ W] (ι : K →* G)
    (ρ : Representation ℂ K W) (y : G) {f : G → ℂ} (hf : f ∈ typeSubmodule ι ρ) :
    Py ι y f ∈ typeSubmodule (MonoidHom.id K) ρ := by
  have hle : typeSubmodule ι ρ ≤ (typeSubmodule (MonoidHom.id K) ρ).comap (Py ι y) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨T, hT, v, rfl⟩
    let T' : W →ₗ[ℂ] (K → ℂ) := (Py ι y).comp T
    have hT' : IsRightEquivariant (MonoidHom.id K) ρ T' := by
      intro k w x
      show T (ρ k w) (y * ι x) = T w (y * ι (x * k))
      rw [hT k w (y * ι x), map_mul, mul_assoc]
    exact mem_typeSubmodule_of_isRightEquivariant hT' v
  exact hle hf

theorem Py_mem_iSup_typeSubmodule {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)]
    [∀ i, Module ℂ (W i)] (ι : K →* G) (ρ : ∀ i, Representation ℂ K (W i)) (y : G) {f : G → ℂ}
    (hf : f ∈ ⨆ i, typeSubmodule ι (ρ i)) :
    Py ι y f ∈ ⨆ i, typeSubmodule (MonoidHom.id K) (ρ i) := by
  have hle : (⨆ i, typeSubmodule ι (ρ i)) ≤
      (⨆ i, typeSubmodule (MonoidHom.id K) (ρ i)).comap (Py ι y) :=
    iSup_le fun i f hf => le_iSup (fun i => typeSubmodule (MonoidHom.id K) (ρ i)) i
      (Py_mem_typeSubmodule ι (ρ i) y hf)
  exact hle hf

end Translation

theorem exists_fin_forall_eq_zero {E V : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup V] [Module ℂ V] {Y : Type*} (L : Y → E →ₗ[ℂ] V)
    (h : ∀ v : E, (∀ y, L y v = 0) → v = 0) :
    ∃ (m : ℕ) (ys : Fin m → Y), ∀ v : E, (∀ j, L (ys j) v = 0) → v = 0 := by
  classical
  let N : Finset Y → Submodule ℂ E := fun s => ⨅ y ∈ s, LinearMap.ker (L y)
  have hN : ∀ (s : Finset Y) (v : E), v ∈ N s ↔ ∀ y ∈ s, L y v = 0 := by
    intro s v
    simp only [N, Submodule.mem_iInf, LinearMap.mem_ker]
  have hex : ∃ d, ∃ s : Finset Y, Module.finrank ℂ (N s) = d := ⟨_, ∅, rfl⟩
  obtain ⟨s0, hs0⟩ := Nat.find_spec hex
  have hmin : ∀ s : Finset Y, Module.finrank ℂ (N s0) ≤ Module.finrank ℂ (N s) := fun s => by
    rw [hs0]
    exact Nat.find_min' hex ⟨s, rfl⟩
  have hle : ∀ y, N s0 ≤ LinearMap.ker (L y) := by
    intro y v hv
    have h1 : N (insert y s0) ≤ N s0 := by
      intro w hw
      rw [hN] at hw ⊢
      exact fun y' hy' => hw y' (Finset.mem_insert_of_mem hy')
    have h2 : N (insert y s0) = N s0 := Submodule.eq_of_le_of_finrank_le h1 (hmin _)
    rw [← h2, hN] at hv
    exact hv y (Finset.mem_insert_self y s0)
  refine ⟨Fintype.card s0, fun j => ((Fintype.equivFin s0).symm j : s0), fun v hv => h v fun y => ?_⟩
  have hv0 : v ∈ N s0 := by
    rw [hN]
    intro y' hy'
    have := hv (Fintype.equivFin s0 ⟨y', hy'⟩)
    dsimp only at this
    rwa [Equiv.symm_apply_apply] at this
  exact hle y hv0

section Coeff

variable {K : Type*} [Group K]

def mcMap {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) :
    Module.Dual ℂ (W →ₗ[ℂ] W) →ₗ[ℂ] (K → ℂ) where
  toFun μ k := μ (ρ k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem typeSubmodule_id_le_range {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) :
    typeSubmodule (MonoidHom.id K) ρ ≤ LinearMap.range (mcMap ρ) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨T, hT, v, rfl⟩
  refine ⟨(LinearMap.proj (1 : K)).comp (T.comp (LinearMap.applyₗ v)), funext fun k => ?_⟩
  show T (ρ k v) 1 = T v k
  rw [hT k v 1, one_mul]
  rfl

scoped instance finiteDimensional_typeSubmodule_id {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] (ρ : Representation ℂ K W) :
    FiniteDimensional ℂ (typeSubmodule (MonoidHom.id K) ρ) :=
  Submodule.finiteDimensional_of_le (typeSubmodule_id_le_range ρ)

def contSubmodule (K : Type*) [TopologicalSpace K] : Submodule ℂ (K → ℂ) where
  carrier := {u | Continuous u}
  add_mem' hu hv := hu.add hv
  zero_mem' := continuous_const
  smul_mem' c u hu := by
    show Continuous fun x => c • u x
    exact hu.const_smul c

variable [TopologicalSpace K] [IsTopologicalGroup K]

theorem continuous_dual_Rrep (V : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ k : K, ∀ u ∈ V, Rtr (MonoidHom.id K) k u ∈ V) (hVc : ∀ u ∈ V, Continuous u)
    (φ : Module.Dual ℂ V) (u : V) :
    Continuous fun k => φ (Rrep (MonoidHom.id K) V hV k u) := by
  obtain ⟨m, xs, hxs⟩ := exists_fin_forall_eq_zero
    (fun x : K => (LinearMap.proj x).comp V.subtype) (fun v hv => Subtype.ext (funext fun x => hv x))
  let ev : V →ₗ[ℂ] (Fin m → ℂ) := LinearMap.pi fun j => (LinearMap.proj (xs j)).comp V.subtype
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hxs v fun j => congr_fun hv j
  obtain ⟨g, hg⟩ := ev.exists_leftInverse_of_injective hev
  have hφ : (fun k => φ (Rrep (MonoidHom.id K) V hV k u)) =
      (φ.comp g) ∘ fun k => ev (Rrep (MonoidHom.id K) V hV k u) := by
    funext k
    show φ _ = φ (g (ev _))
    rw [← LinearMap.comp_apply g ev, hg, LinearMap.id_apply]
  rw [hφ]
  refine (LinearMap.continuous_of_finiteDimensional _).comp (continuous_pi fun j => ?_)
  show Continuous fun k => (u : K → ℂ) (xs j * k)
  exact (hVc u u.2).comp (continuous_const.mul continuous_id)

end Coeff

section Mat

variable {K : Type*} [Group K] {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

noncomputable def matRep (b : Module.Basis (Fin n) ℂ V) (R : Representation ℂ K V) :
    K →* Matrix (Fin n) (Fin n) ℂ where
  toFun k := LinearMap.toMatrix b b (R k)
  map_one' := by
    rw [map_one]
    exact LinearMap.toMatrix_one b
  map_mul' a c := by
    rw [map_mul]
    exact LinearMap.toMatrix_mul b (R a) (R c)

theorem matRep_apply (b : Module.Basis (Fin n) ℂ V) (R : Representation ℂ K V) (k : K) :
    matRep b R k = LinearMap.toMatrix b b (R k) := rfl

theorem matRep_mulVec (b : Module.Basis (Fin n) ℂ V) (R : Representation ℂ K V) (k : K) (u : V) :
    (matRep b R k).mulVec (b.equivFun u) = b.equivFun (R k u) := by
  rw [b.equivFun_apply, b.equivFun_apply]
  exact LinearMap.toMatrix_mulVec_repr b b (R k) u

theorem equivFun_symm_mulVec (b : Module.Basis (Fin n) ℂ V) (R : Representation ℂ K V) (k : K)
    (x : Fin n → ℂ) : b.equivFun.symm ((matRep b R k).mulVec x) = R k (b.equivFun.symm x) := by
  rw [LinearEquiv.symm_apply_eq, ← matRep_mulVec, LinearEquiv.apply_symm_apply]

def piRep (m : ℕ) (R : Representation ℂ K V) : Representation ℂ K (Fin m → V) where
  toFun k :=
    { toFun := fun w j => R k (w j)
      map_add' := fun w w' => funext fun j => map_add _ _ _
      map_smul' := fun c w => funext fun j => map_smul _ _ _ }
  map_one' := by
    refine LinearMap.ext fun w => funext fun j => ?_
    show R 1 (w j) = w j
    rw [map_one]
    rfl
  map_mul' a c := by
    refine LinearMap.ext fun w => funext fun j => ?_
    show R (a * c) (w j) = R a (R c (w j))
    rw [map_mul]
    rfl

theorem piRep_apply (m : ℕ) (R : Representation ℂ K V) (k : K) (w : Fin m → V) (j : Fin m) :
    piRep m R k w j = R k (w j) := rfl

end Mat

end Ws49.K1
p2m_reactivate "P2MW.S_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates.Ws49 P2MW.S_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates.Ws49.K1"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates.Ws49"

open Ws49.K1 in
theorem solution
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    {I : Type*} [Finite I] {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, Module.Finite ℂ (W i)] (ρ : ∀ i, Representation ℂ K (W i)) :
    ∃ (n : ℕ) (ρc : K →* Matrix (Fin n) (Fin n) ℂ), Continuous ρc ∧
      ∀ (G : Type*) [Group G] (ι : K →* G), Function.Injective ι →
        (∀ (T : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ)),
          (∀ (k : K) (x : Fin n → ℂ), T ((ρc k).mulVec x) = fun y => T x (y * ι k)) →
          ∀ x : Fin n → ℂ, T x ∈ ⨆ i, typeSubmodule ι (ρ i)) ∧
        (∀ f ∈ ⨆ i, typeSubmodule ι (ρ i), (∀ y : G, Continuous fun k : K => f (y * ι k)) →
          ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] (G → ℂ)),
            (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun j => (ρc k).mulVec (x j)) = fun y => T x (y * ι k)) ∧
            LinearMap.range T = Submodule.span ℂ (Set.range fun k : K => fun y : G => f (y * ι k))) := by
  classical

  let M : Submodule ℂ (K → ℂ) := ⨆ i, typeSubmodule (MonoidHom.id K) (ρ i)
  let V : Submodule ℂ (K → ℂ) := M ⊓ contSubmodule K
  have hMst : ∀ k : K, ∀ u ∈ M, Rtr (MonoidHom.id K) k u ∈ M := by
    intro k u hu
    have hle : M ≤ M.comap (Rtr (MonoidHom.id K) k) :=
      iSup_le fun i u hu => le_iSup (fun i => typeSubmodule (MonoidHom.id K) (ρ i)) i
        (comp_mul_mem_typeSubmodule hu k)
    exact hle hu
  have hV : ∀ k : K, ∀ u ∈ V, Rtr (MonoidHom.id K) k u ∈ V := by
    intro k u hu
    refine ⟨hMst k u hu.1, ?_⟩
    show Continuous fun x => u (x * k)
    exact (show Continuous u from hu.2).comp (continuous_id.mul continuous_const)
  have hVc : ∀ u ∈ V, Continuous u := fun u hu => hu.2
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_left
  let R : Representation ℂ K V := Rrep (MonoidHom.id K) V hV
  have hRc : ∀ (φ : Module.Dual ℂ V) (u : V), Continuous fun k => φ (R k u) :=
    continuous_dual_Rrep V hV hVc

  let n := Module.finrank ℂ V
  let b : Module.Basis (Fin n) ℂ V := Module.finBasis ℂ V
  let ρc : K →* Matrix (Fin n) (Fin n) ℂ := matRep b R
  have hρc : Continuous ρc := by
    refine continuous_pi fun a => continuous_pi fun c => ?_
    show Continuous fun k => LinearMap.toMatrix b b (R k) a c
    simp only [LinearMap.toMatrix_apply]
    exact hRc (b.coord a) (b c)
  refine ⟨n, ρc, hρc, fun G _ ι hι => ⟨?_, ?_⟩⟩
  ·
    intro T hT x
    let A : V →ₗ[ℂ] (G → ℂ) := T.comp b.equivFun.toLinearMap
    have hA : ∀ (k : K) (u : V) (y : G),
        A ⟨fun κ => (u : K → ℂ) (κ * (MonoidHom.id K) k), hV k u u.2⟩ y = A u (y * ι k) := by
      intro k u y
      show T (b.equivFun (R k u)) y = T (b.equivFun u) (y * ι k)
      rw [← matRep_mulVec, hT]
    let u : V := b.equivFun.symm x
    have hmem := apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective (MonoidHom.id K) ι hι
      V (fun k u hu => hV k u hu) A hA ρ (u : K → ℂ) u.2 u.2.1
    have hAu : A ⟨(u : K → ℂ), u.2⟩ = T x := by
      show T (b.equivFun (b.equivFun.symm x)) = T x
      rw [LinearEquiv.apply_symm_apply]
    rwa [hAu] at hmem
  ·
    intro f hf hfc

    have hfy : ∀ y : G, Py ι y f ∈ V := fun y =>
      ⟨Py_mem_iSup_typeSubmodule ι ρ y hf, hfc y⟩
    let E : Submodule ℂ (G → ℂ) := Submodule.span ℂ (Set.range fun k : K => fun y : G => f (y * ι k))

    have hE : ∀ k : K, ∀ g ∈ E, Rtr ι k g ∈ E := by
      intro k g hg
      have hle : E.map (Rtr ι k) ≤ E := by
        refine (Submodule.map_span_le _ _ _).mpr ?_
        rintro _ ⟨k', rfl⟩
        refine Submodule.subset_span ⟨k * k', funext fun y => ?_⟩
        show f (y * ι (k * k')) = f (y * ι k * ι k')
        rw [map_mul, mul_assoc]
      exact hle (Submodule.mem_map_of_mem hg)

    have hEV : ∀ y : G, ∀ g ∈ E, Py ι y g ∈ V := by
      intro y
      have hle : E ≤ V.comap (Py ι y) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨k', rfl⟩
        have heq : Py ι y (fun y' : G => f (y' * ι k')) = Rtr (MonoidHom.id K) k' (Py ι y f) := by
          funext κ
          show f (y * ι κ * ι k') = f (y * ι (κ * k'))
          rw [map_mul, mul_assoc]
        show Py ι y _ ∈ V
        rw [heq]
        exact hV k' _ (hfy y)
      exact fun g hg => hle hg

    let Θ : Module.End ℂ V →ₗ[ℂ] (G → ℂ) :=
      { toFun := fun A y => ((A ⟨Py ι y f, hfy y⟩ : V) : K → ℂ) 1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hEΘ : E ≤ LinearMap.range Θ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      refine ⟨R k, funext fun y => ?_⟩
      show f (y * ι (1 * k)) = f (y * ι k)
      rw [one_mul]
    haveI : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le hEΘ

    let RE : Representation ℂ K E := Rrep ι E hE
    let L : G → E →ₗ[ℂ] V := fun y => (Py ι y).restrict (hEV y)
    have hL : ∀ g : E, (∀ y, L y g = 0) → g = 0 := by
      intro g hg
      refine Subtype.ext (funext fun y => ?_)
      have h1 := congr_fun (congrArg Subtype.val (hg y)) 1
      change (g : G → ℂ) (y * ι 1) = 0 at h1
      rw [map_one, mul_one] at h1
      exact h1
    obtain ⟨m, ys, hys⟩ := exists_fin_forall_eq_zero L hL
    let jm : E →ₗ[ℂ] (Fin m → V) := LinearMap.pi fun j => L (ys j)
    have hj : Function.Injective jm := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro g hg
      exact hys g fun j => congr_fun hg j

    let Rm : Representation ℂ K (Fin m → V) := piRep m R
    have hjeq : ∀ (k : K) (g : E), jm (RE k g) = Rm k (jm g) := by
      intro k g
      refine funext fun j => Subtype.ext (funext fun κ => ?_)
      show (g : G → ℂ) (ys j * ι κ * ι k) = (g : G → ℂ) (ys j * ι (κ * k))
      rw [map_mul, mul_assoc]

    have hRm : ∀ (ℓ : Module.Dual ℂ (Fin m → V)) (w : Fin m → V),
        Continuous fun k => ℓ (Rm k w) := by
      intro ℓ w
      have heq : (fun k => ℓ (Rm k w)) =
          fun k => ∑ j, (ℓ.comp (LinearMap.single ℂ (fun _ : Fin m => V) j)) (R k (w j)) := by
        funext k
        conv_lhs => rw [← Finset.univ_sum_single (Rm k w)]
        rw [map_sum]
        rfl
      rw [heq]
      exact continuous_finsetSum _ fun j _ => hRc _ _

    have hP : ∀ k : K, ∀ w ∈ LinearMap.range jm, Rm k w ∈ LinearMap.range jm := by
      rintro k _ ⟨g, rfl⟩
      exact ⟨RE k g, hjeq k g⟩
    obtain ⟨Pc, hc, hPc⟩ :=
      Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous Rm hRm
        (LinearMap.range jm) hP
    let lp : (Fin m → V) →ₗ[ℂ] E := LinearMap.linearProjOfIsCompl Pc jm hj hc
    have hlp : ∀ (k : K) (w : Fin m → V), lp (Rm k w) = RE k (lp w) := by
      intro k w
      have hcw : w - jm (lp w) ∈ Pc := by
        rw [← LinearMap.ker_linearProjOfIsCompl Pc jm hj hc, LinearMap.mem_ker, map_sub,
          LinearMap.linearProjOfIsCompl_apply_left, sub_self]
      have hw : w = jm (lp w) + (w - jm (lp w)) := by abel
      calc lp (Rm k w) = lp (Rm k (jm (lp w)) + Rm k (w - jm (lp w))) := by
            rw [← map_add, ← hw]
        _ = lp (jm (RE k (lp w))) + lp (Rm k (w - jm (lp w))) := by rw [map_add, hjeq]
        _ = RE k (lp w) := by
            rw [LinearMap.linearProjOfIsCompl_apply_left,
              LinearMap.linearProjOfIsCompl_apply_right' _ _ _ _ _ (hPc k _ hcw), add_zero]

    let Φ : (Fin m → (Fin n → ℂ)) ≃ₗ[ℂ] (Fin m → V) :=
      LinearEquiv.piCongrRight fun _ => b.equivFun.symm
    have hΦ : ∀ (k : K) (x : Fin m → (Fin n → ℂ)),
        Φ (fun j => (ρc k).mulVec (x j)) = Rm k (Φ x) := by
      intro k x
      funext j
      show b.equivFun.symm ((matRep b R k).mulVec (x j)) = R k (b.equivFun.symm (x j))
      exact equivFun_symm_mulVec b R k (x j)
    refine ⟨m, E.subtype.comp (lp.comp Φ.toLinearMap), ?_, ?_⟩
    · intro k x
      show ((lp (Φ (fun j => (ρc k).mulVec (x j))) : E) : G → ℂ) =
        fun y => ((lp (Φ x) : E) : G → ℂ) (y * ι k)
      rw [hΦ, hlp]
      rfl
    · have hlpr : LinearMap.range lp = ⊤ :=
        LinearMap.range_eq_top.mpr fun g => ⟨jm g, LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ g⟩
      have h1 : LinearMap.range (lp.comp Φ.toLinearMap) = ⊤ := by
        rw [LinearMap.range_comp_of_range_eq_top _ Φ.range, hlpr]
      rw [LinearMap.range_comp_of_range_eq_top _ h1, Submodule.range_subtype]

end S_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
end P2MW
export P2MW.S_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates (solution)
