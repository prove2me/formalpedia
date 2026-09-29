-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1fee736b-44bb-5b7a-ba76-7dce97198f23

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace FormalGAGAFiniteSepAux

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
variable (F : OModulePresheaf q) (K : P.OrderedAffineCover)

scoped instance : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
scoped instance : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))

lemma inter_zero (s : K.Idx 0) : K.inter s = K.U (s.1 0) := by
  simp only [Scheme.OrderedAffineCover.inter]
  exact iInf_unique (f := fun j : Fin (0 + 1) => K.U (s.1 j))

lemma isAffineOpen_inter_zero (s : K.Idx 0) : IsAffineOpen (K.inter s) := by
  rw [inter_zero]; exact K.isAffineOpen _

def vertex (i : K.ι) : K.Idx 0 := ⟨fun _ => i, fun a b h => absurd h (by simp [Subsingleton.elim a b])⟩

lemma idx0_ext {s t : K.Idx 0} (h : s.1 0 = t.1 0) : s = t := by
  apply Subtype.ext; funext k
  rw [Subsingleton.elim k 0]; exact h

def edge (i j : K.ι) (hij : i < j) : K.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr fun k => by fin_cases k; simpa using hij⟩

lemma face_edge_zero (i j : K.ι) (hij : i < j) : K.face (edge K i j hij) 0 = vertex K j := by
  apply idx0_ext; simp [Scheme.OrderedAffineCover.face_val, edge, vertex]

lemma face_edge_one (i j : K.ι) (hij : i < j) : K.face (edge K i j hij) 1 = vertex K i := by
  apply idx0_ext
  simp only [Scheme.OrderedAffineCover.face_val, edge, vertex, Function.comp_apply]
  rfl

lemma eq_vertex (s : K.Idx 0) : s = vertex K (s.1 0) := idx0_ext K rfl

lemma exists_edge {s t : K.Idx 0} (hst : s ≠ t) :
    ∃ σ : K.Idx 1, (K.face σ 0 = t ∧ K.face σ 1 = s) ∨ (K.face σ 0 = s ∧ K.face σ 1 = t) := by
  have hij : s.1 0 ≠ t.1 0 := fun h => hst (idx0_ext K h)
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨edge K _ _ h, Or.inl ⟨(face_edge_zero K _ _ h).trans (eq_vertex K t).symm,
      (face_edge_one K _ _ h).trans (eq_vertex K s).symm⟩⟩
  · exact ⟨edge K _ _ h, Or.inr ⟨(face_edge_zero K _ _ h).trans (eq_vertex K s).symm,
      (face_edge_one K _ _ h).trans (eq_vertex K t).symm⟩⟩

lemma inter_face_inf_le (σ : K.Idx 1) :
    K.inter (K.face σ 0) ⊓ K.inter (K.face σ 1) ≤ K.inter σ := by
  refine le_iInf fun k => ?_
  fin_cases k
  · refine inf_le_right.trans ((K.inter_le (K.face σ 1) 0).trans (le_of_eq ?_))
    simp [Scheme.OrderedAffineCover.face_val]
  · refine inf_le_left.trans ((K.inter_le (K.face σ 0) 0).trans (le_of_eq ?_))
    simp [Scheme.OrderedAffineCover.face_val]

lemma res_congr_idx {s₁ s₂ : K.Idx 0} (e : s₁ = s₂) {W : P.Opens} (h₁ : W ≤ K.inter s₁)
    (h₂ : W ≤ K.inter s₂) (z : F.cochain K 0) : F.res h₁ (z s₁) = F.res h₂ (z s₂) := by
  subst e; rfl

lemma res_face_eq_of_d_eq_zero (z : F.cochain K 0) (hz : F.d K 0 z = 0) (σ : K.Idx 1) :
    F.res (K.inter_le_inter_face σ 0) (z (K.face σ 0)) =
      F.res (K.inter_le_inter_face σ 1) (z (K.face σ 1)) := by
  have h := congrFun (congrArg (fun c : F.cochain K 1 => c) hz) σ
  simp only [Pi.zero_apply] at h
  rw [F.d_apply] at h
  rw [Fin.sum_univ_two] at h
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, one_smul] at h
  exact add_neg_eq_zero.mp h

lemma res_eq_res_of_d_eq_zero (z : F.cochain K 0) (hz : F.d K 0 z = 0) (s t : K.Idx 0)
    {W : P.Opens} (hs : W ≤ K.inter s) (ht : W ≤ K.inter t) :
    F.res hs (z s) = F.res ht (z t) := by
  by_cases hst : s = t
  · subst hst; rfl
  obtain ⟨σ, hσ⟩ := exists_edge K hst
  have key : ∀ (a b : K.Idx 0), K.face σ 0 = a → K.face σ 1 = b →
      ∀ (ha : W ≤ K.inter a) (hb : W ≤ K.inter b), F.res ha (z a) = F.res hb (z b) := by
    rintro a b rfl rfl ha hb
    have hW : W ≤ K.inter σ := (le_inf ha hb).trans (inter_face_inf_le K σ)
    rw [← F.res_res hW (K.inter_le_inter_face σ 0), ← F.res_res hW (K.inter_le_inter_face σ 1),
      res_face_eq_of_d_eq_zero F K z hz σ]
  rcases hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact (key t s h0 h1 ht hs).symm
  · exact key s t h0 h1 hs ht

lemma mem_basicOpen_iff_notMem {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (f : Γ(X, U)) : x.1 ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf x).asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, show PrimeSpectrum.basicOpen f =
    hU.fromSpec ⁻¹ᵁ X.basicOpen f from (hU.fromSpec_preimage_basicOpen f).symm]
  change _ ↔ hU.fromSpec (hU.primeIdealOf x) ∈ X.basicOpen f
  rw [hU.fromSpec_primeIdealOf]

lemma res_basicOpen_eq_zero_of_smul_eq_zero {U : P.Opens} (r : Γ(P, U)) (m : F.obj U)
    (h : r • m = 0) : F.res (P.basicOpen_le r) m = 0 := by
  have hu : IsUnit (P.presheaf.map (homOfLE (P.basicOpen_le r)).op r) :=
    RingedSpace.isUnit_res_basicOpen _ r
  have := congrArg (F.res (P.basicOpen_le r)) h
  rw [F.res_smul, map_zero] at this
  exact (hu.smul_left_cancel).mp (this.trans (smul_zero _).symm)

end FormalGAGAFiniteSepAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux"

open FormalGAGAFiniteSepAux in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hq : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (z : F.cochain K 0) (hz : F.d K 0 z = 0)
    (h : ∀ (k : ℕ) (s : K.Idx 0), z s ∈ I ^ k • (⊤ : Submodule A (F.obj (K.inter s)))) :
    z = 0 := by
  classical
  have hLN : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q

  letI alg : ∀ U : P.Opens, Algebra A Γ(P, U) := fun U => Scheme.TwoAffineOpenCover.algebraOfHom q U

  have step1 : ∀ s : K.Idx 0, ∃ r : Γ(P, K.inter s),
      r - 1 ∈ I.map (algebraMap A Γ(P, K.inter s)) ∧ r • z s = 0 := by
    intro s
    have hU := isAffineOpen_inter_zero K s
    haveI : IsNoetherianRing Γ(P, K.inter s) := hLN.component_noetherian ⟨_, hU⟩
    haveI : Module.Finite Γ(P, K.inter s) (F.obj (K.inter s)) := hc ⟨_, hU⟩
    set J : Ideal Γ(P, K.inter s) := I.map (algebraMap A Γ(P, K.inter s)) with hJ
    have hzJ : z s ∈ (⨅ i : ℕ, J ^ i • ⊤ : Submodule Γ(P, K.inter s) (F.obj (K.inter s))) := by
      refine (Submodule.mem_iInf _).mpr fun k => ?_
      have hle : (I ^ k • (⊤ : Submodule A (F.obj (K.inter s)))) ≤
          (J ^ k • (⊤ : Submodule Γ(P, K.inter s) (F.obj (K.inter s)))).restrictScalars A := by
        refine Submodule.smul_le.mpr fun a ha m _ => ?_
        rw [Submodule.restrictScalars_mem, ← algebraMap_smul Γ(P, K.inter s) a m]
        exact Submodule.smul_mem_smul (by rw [hJ, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha)
          Submodule.mem_top
      exact hle (h k s)
    obtain ⟨⟨r, hr⟩, hrz⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff J (z s)).mp hzJ
    refine ⟨1 - r, by simpa using J.neg_mem hr, ?_⟩
    rw [sub_smul, one_smul, hrz, sub_self]
  choose r hrJ hrz using step1

  let W : P.Opens := ⨆ t : K.Idx 0, ⨆ g : Γ(P, K.inter t),
    ⨆ (_ : F.res (P.basicOpen_le g) (z t) = 0), P.basicOpen g
  have memW : ∀ {x : P} (t : K.Idx 0) (g : Γ(P, K.inter t)),
      F.res (P.basicOpen_le g) (z t) = 0 → x ∈ P.basicOpen g → x ∈ W := by
    intro x t g hg hx
    refine Opens.mem_iSup.mpr ⟨t, Opens.mem_iSup.mpr ⟨g, Opens.mem_iSup.mpr ⟨hg, hx⟩⟩⟩

  have step3 : ∀ x : P, I ≤ (q x).asIdeal → x ∈ W := by
    intro x hxI
    obtain ⟨i, hxi⟩ : ∃ i, x ∈ K.U i := by
      have : x ∈ (⨆ i, K.U i) := by rw [K.iSup_eq_top]; trivial
      exact Opens.mem_iSup.mp this
    let s : K.Idx 0 := vertex K i
    have hxs : x ∈ K.inter s := by rw [inter_zero]; exact hxi
    have hU := isAffineOpen_inter_zero K s
    refine memW s (r s) (res_basicOpen_eq_zero_of_smul_eq_zero F (r s) (z s) (hrz s)) ?_
    rw [mem_basicOpen_iff_notMem hU ⟨x, hxs⟩]
    intro hrmem

    have hJle : I.map (algebraMap A Γ(P, K.inter s)) ≤ (hU.primeIdealOf ⟨x, hxs⟩).asIdeal := by
      refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
      have hax : a ∈ (q x).asIdeal := hxI ha

      have htop : IsAffineOpen (⊤ : (Spec (CommRingCat.of A)).Opens) := isAffineOpen_top _
      have hcomap := IsAffineOpen.comap_primeIdealOf_appLE (f := q) (x := x) ⊤ htop (K.inter s) hU
        le_top hxs
      have hqx : q x ∉ (Spec (CommRingCat.of A)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) := by
        rw [basicOpen_eq_of_affine]
        exact fun hh => (PrimeSpectrum.mem_basicOpen _ _).mp hh hax
      rw [mem_basicOpen_iff_notMem htop ⟨q x, trivial⟩, not_not, ← hcomap] at hqx
      exact hqx
    have h1 : (r s - 1) ∈ (hU.primeIdealOf ⟨x, hxs⟩).asIdeal := hJle (hrJ s)
    have : (1 : Γ(P, K.inter s)) ∈ (hU.primeIdealOf ⟨x, hxs⟩).asIdeal := by
      simpa using Ideal.sub_mem _ hrmem h1
    exact (hU.primeIdealOf ⟨x, hxs⟩).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)

  have step4 : W = ⊤ := by
    let Z : Set P := (W : Set P)ᶜ
    have hZ : IsClosed Z := W.isOpen.isClosed_compl
    have hqZ : IsClosed (q.base '' Z) := q.isClosedMap _ hZ
    let J' : Ideal A := PrimeSpectrum.vanishingIdeal (q.base '' Z)
    have hJ'Z : PrimeSpectrum.zeroLocus (J' : Set A) = q.base '' Z := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact hqZ.closure_eq
    have hsup : J' ⊔ I = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
      let y : PrimeSpectrum A := ⟨m, hm.isPrime⟩
      have hyZ : y ∈ q.base '' Z := by
        rw [← hJ'Z]; exact fun a ha => hle (Ideal.mem_sup_left ha)
      obtain ⟨x, hxZ, hxy⟩ := hyZ
      have hxW : x ∈ W := step3 x (fun a ha => by
        change a ∈ (q.base x).asIdeal
        rw [hxy]; exact hle (Ideal.mem_sup_right ha))
      exact hxZ hxW
    obtain ⟨j, hj, i, hi, hji⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hsup)
    have hju : IsUnit j := by
      refine Ideal.isUnit_of_sub_one_mem_jacobson_bot j ?_
      have : j - 1 = -i := by rw [← hji]; ring
      rw [this]
      exact Submodule.neg_mem _ (IsAdicComplete.le_jacobson_bot I hi)
    have hJ'top : J' = ⊤ := Ideal.eq_top_of_isUnit_mem _ hj hju
    have hZe : q.base '' Z = ∅ := by
      rw [← hJ'Z, hJ'top]
      exact PrimeSpectrum.zeroLocus_empty_of_one_mem (Submodule.mem_top : (1 : A) ∈ (⊤ : Ideal A))
    have : Z = ∅ := Set.image_eq_empty.mp hZe
    apply Opens.ext
    simpa [Z, Set.compl_empty_iff] using this

  funext s
  have hU := isAffineOpen_inter_zero K s
  have hloc : ∀ x : K.inter s, ∃ f : Γ(P, K.inter s),
      x.1 ∈ P.basicOpen f ∧ F.res (P.basicOpen_le f) (z s) = 0 := by
    rintro ⟨x, hxs⟩
    have hxW : x ∈ W := by rw [step4]; trivial
    obtain ⟨t, hxt⟩ := Opens.mem_iSup.mp hxW
    obtain ⟨g, hxg⟩ := Opens.mem_iSup.mp hxt
    obtain ⟨hg, hxg⟩ := Opens.mem_iSup.mp hxg
    have hUt := isAffineOpen_inter_zero K t
    obtain ⟨f, g', hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU (hUt.basicOpen g) x ⟨hxs, hxg⟩
    refine ⟨f, hxf, ?_⟩
    have hfg' : P.basicOpen f ≤ P.basicOpen g := hfg ▸ P.basicOpen_le g'
    have hft : P.basicOpen f ≤ K.inter t := hfg'.trans (P.basicOpen_le g)
    rw [res_eq_res_of_d_eq_zero F K z hz s t (P.basicOpen_le f) hft,
      ← F.res_res hfg' (P.basicOpen_le g), hg, map_zero]
  choose f hxf hfz using hloc
  obtain ⟨T, hT⟩ := hU.isCompact.elim_finite_subcover (fun x : K.inter s => (P.basicOpen (f x) : Set P))
    (fun x => (P.basicOpen (f x)).isOpen) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxf ⟨x, hx⟩⟩)
  have hcov : K.inter s ≤ ⨆ j : T, P.basicOpen (f j.1) := by
    intro x hx
    have := hT hx
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hyT, hy⟩ := this
    exact Opens.mem_iSup.mpr ⟨⟨y, hyT⟩, hy⟩
  exact AlgebraicGeometry.OModulePresheaf.eq_zero_of_forall_res_basicOpen_eq_zero hq ⟨_, hU⟩
    (fun j : T => f j.1) hcov (z s) (fun j => hfz j.1)

end S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper (solution)
