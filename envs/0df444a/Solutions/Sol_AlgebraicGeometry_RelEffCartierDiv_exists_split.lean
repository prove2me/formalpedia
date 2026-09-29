-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2696c7f4-0872-58dd-8929-f0f6aa6a56bf

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_graphOver_mul
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_split

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_split.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Hom.le_ker_comp SmoothOfRelativeDimension Scheme.Hom Scheme.IdealSheafData.map_ker IsFinite Scheme Smooth Scheme.IdealSheafData.le_map_iff_comap_le Scheme.IdealSheafData.comap_top Flat IsClosedImmersion IsSeparated IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Hom.one_le_finrank_iff_surjective LocallyOfFinitePresentation Scheme.Hom.finrank_eq_one_of_isIso Scheme.IdealSheafData prodKerGraph prodKerGraph_zero prodKerGraph_succ RelEffCartierDiv.I_eq_top_of_degree_zero graphOver graphOver_fst RelEffCartierDiv.ofPoint graphOver_snd_assoc RelEffCartierDiv mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd RelEffCartierDiv.pullbackAlong_comp RelEffCartierDiv.I RelEffCartierDiv.exists_I_eq_ker_graphOver_mul RelEffCartierDiv.isInvertible_I RelEffCartierDiv.pullbackAlong_ofPoint Scheme.IdealSheafData.comap_mul Scheme.Hom.finrank_comp_of_finrank_eq_const"
namespace RelEffCartierDiv
p2m_export "AlgebraicGeometry.RelEffCartierDiv" "I_eq_top_of_degree_zero ofPoint pullbackAlong pullbackAlong_comp I flat isFinite finrank_eq locallyOfFinitePresentation exists_I_eq_ker_graphOver_mul isInvertible_I pullbackAlong_ofPoint"
p2m_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}

@[reassoc]
lemma graphOver_comp_mapOnProdOver {T' : Scheme.{u}} {g' : T' ⟶ S} (q : T' ⟶ T)
    (hq : q ≫ g = g') (a : T' ⟶ 𝒞) (ha : a ≫ f = g') :
    graphOver f a ha ≫ mapOnProdOver f q hq =
      pullback.lift a q (by rw [ha, hq]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, mapOnProdOver_fst, graphOver_fst]
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, mapOnProdOver_snd, graphOver_snd_assoc]
    exact (pullback.lift_snd _ _ _).symm

private theorem _root_.AlgebraicGeometry.RelEffCartierDiv.pullbackAlong_I_le_ker_graphOver_iff (D : RelEffCartierDiv f r g) {T' : Scheme.{u}}
    {g' : T' ⟶ S} (q : T' ⟶ T) (hq : q ≫ g = g') (a : T' ⟶ 𝒞) (ha : a ≫ f = g') :
    (D.pullbackAlong q hq).I ≤ (graphOver f a ha).ker ↔
      ∃ s : T' ⟶ D.I.subscheme, s ≫ D.I.subschemeι = pullback.lift a q (by rw [ha, hq]) := by
  change D.I.comap (mapOnProdOver f q hq) ≤ _ ↔ _
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker,
    graphOver_comp_mapOnProdOver]
  constructor
  · intro H
    rw [← D.I.ker_subschemeι] at H
    exact ⟨IsClosedImmersion.lift _ _ H, IsClosedImmersion.lift_fac _ _ H⟩
  · rintro ⟨s, hs⟩
    rw [← hs]
    exact D.I.ker_subschemeι.symm.trans_le (Scheme.Hom.le_ker_comp _ _)

p2m_export "AlgebraicGeometry.RelEffCartierDiv" "pullbackAlong_I_le_ker_graphOver_iff"

private noncomputable def _root_.AlgebraicGeometry.RelEffCartierDiv.liftOfLE (D : RelEffCartierDiv f r g) {T' : Scheme.{u}} {g' : T' ⟶ S}
    (q : T' ⟶ T) (hq : q ≫ g = g') (a : T' ⟶ 𝒞) (ha : a ≫ f = g')
    (h : (D.pullbackAlong q hq).I ≤ (graphOver f a ha).ker) : T' ⟶ D.I.subscheme :=
  ((D.pullbackAlong_I_le_ker_graphOver_iff q hq a ha).1 h).choose

p2m_export "AlgebraicGeometry.RelEffCartierDiv" "liftOfLE"
@[reassoc (attr := simp)]
lemma liftOfLE_ι (D : RelEffCartierDiv f r g) {T' : Scheme.{u}} {g' : T' ⟶ S}
    (q : T' ⟶ T) (hq : q ≫ g = g') (a : T' ⟶ 𝒞) (ha : a ≫ f = g')
    (h : (D.pullbackAlong q hq).I ≤ (graphOver f a ha).ker) :
    D.liftOfLE q hq a ha h ≫ D.I.subschemeι = pullback.lift a q (by rw [ha, hq]) :=
  ((D.pullbackAlong_I_le_ker_graphOver_iff q hq a ha).1 h).choose_spec

@[reassoc (attr := simp)]
private lemma _root_.AlgebraicGeometry.RelEffCartierDiv.liftOfLE_ι_fst (D : RelEffCartierDiv f r g) {T' : Scheme.{u}} {g' : T' ⟶ S}
    (q : T' ⟶ T) (hq : q ≫ g = g') (a : T' ⟶ 𝒞) (ha : a ≫ f = g')
    (h : (D.pullbackAlong q hq).I ≤ (graphOver f a ha).ker) :
    D.liftOfLE q hq a ha h ≫ D.I.subschemeι ≫ pullback.fst f g = a := by
  rw [liftOfLE_ι_assoc, pullback.lift_fst]

p2m_export "AlgebraicGeometry.RelEffCartierDiv" "liftOfLE_ι_fst liftOfLE_ι_fst_assoc"
@[reassoc (attr := simp)]
private lemma _root_.AlgebraicGeometry.RelEffCartierDiv.liftOfLE_ι_snd (D : RelEffCartierDiv f r g) {T' : Scheme.{u}} {g' : T' ⟶ S}
    (q : T' ⟶ T) (hq : q ≫ g = g') (a : T' ⟶ 𝒞) (ha : a ≫ f = g')
    (h : (D.pullbackAlong q hq).I ≤ (graphOver f a ha).ker) :
    D.liftOfLE q hq a ha h ≫ D.I.subschemeι ≫ pullback.snd f g = q := by
  rw [liftOfLE_ι_assoc, pullback.lift_snd]

p2m_export "AlgebraicGeometry.RelEffCartierDiv" "liftOfLE_ι_snd liftOfLE_ι_snd_assoc"

private lemma _root_.AlgebraicGeometry.RelEffCartierDiv.hom_subscheme_ext (D : RelEffCartierDiv f r g) {T' : Scheme.{u}}
    {s s' : T' ⟶ D.I.subscheme}
    (h₁ : s ≫ D.I.subschemeι ≫ pullback.fst f g = s' ≫ D.I.subschemeι ≫ pullback.fst f g)
    (h₂ : s ≫ D.I.subschemeι ≫ pullback.snd f g = s' ≫ D.I.subschemeι ≫ pullback.snd f g) :
    s = s' := by
  rw [← cancel_mono D.I.subschemeι]
  apply pullback.hom_ext
  · simpa only [Category.assoc] using h₁
  · simpa only [Category.assoc] using h₂

p2m_export "AlgebraicGeometry.RelEffCartierDiv" "hom_subscheme_ext"

private lemma _root_.AlgebraicGeometry.RelEffCartierDiv.pullbackAlong_I_le_ker_graphOver_taut (D : RelEffCartierDiv f r g) {gZ : D.I.subscheme ⟶ S}
    (hgZ : (D.I.subschemeι ≫ pullback.snd f g) ≫ g = gZ) :
    (D.pullbackAlong (D.I.subschemeι ≫ pullback.snd f g) hgZ).I ≤
      (graphOver f (D.I.subschemeι ≫ pullback.fst f g)
        (by rw [← hgZ, Category.assoc, pullback.condition, Category.assoc])).ker :=
  (D.pullbackAlong_I_le_ker_graphOver_iff _ _ _ _).2 ⟨𝟙 _, by
    rw [Category.id_comp]
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).symm
    · exact (pullback.lift_snd _ _ _).symm⟩

p2m_export "AlgebraicGeometry.RelEffCartierDiv" "pullbackAlong_I_le_ker_graphOver_taut"
end AlgebraicGeometry.RelEffCartierDiv

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Hom.le_ker_comp SmoothOfRelativeDimension Scheme.Hom Scheme.IdealSheafData.map_ker IsFinite Scheme Smooth Scheme.IdealSheafData.le_map_iff_comap_le Scheme.IdealSheafData.comap_top Flat IsClosedImmersion IsSeparated IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Hom.one_le_finrank_iff_surjective LocallyOfFinitePresentation Scheme.Hom.finrank_eq_one_of_isIso Scheme.IdealSheafData prodKerGraph prodKerGraph_zero prodKerGraph_succ RelEffCartierDiv.I_eq_top_of_degree_zero graphOver graphOver_fst RelEffCartierDiv.ofPoint graphOver_snd_assoc RelEffCartierDiv mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd RelEffCartierDiv.pullbackAlong_comp RelEffCartierDiv.I RelEffCartierDiv.exists_I_eq_ker_graphOver_mul RelEffCartierDiv.isInvertible_I RelEffCartierDiv.pullbackAlong_ofPoint Scheme.IdealSheafData.comap_mul Scheme.Hom.finrank_comp_of_finrank_eq_const"
namespace RelEffCartierDiv
p2m_export "AlgebraicGeometry.RelEffCartierDiv" "I_eq_top_of_degree_zero ofPoint pullbackAlong pullbackAlong_comp I flat isFinite finrank_eq locallyOfFinitePresentation exists_I_eq_ker_graphOver_mul isInvertible_I pullbackAlong_ofPoint"
namespace SplitProof
p2m_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

p2m_open "AlgebraicGeometry.RelEffCartierDiv P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_split.AlgebraicGeometry.RelEffCartierDiv"

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S}

lemma pullbackAlong_congr {r : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    (D : RelEffCartierDiv f r g) {φ φ' : T' ⟶ T} (h : φ = φ') (hφ : φ ≫ g = g')
    (hφ' : φ' ≫ g = g') : D.pullbackAlong φ hφ = D.pullbackAlong φ' hφ' := by
  subst h
  rfl

lemma ker_graphOver_comap [IsSeparated f] {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) (q : T' ⟶ T) (hq : q ≫ g = g') :
    (graphOver f a ha).ker.comap (mapOnProdOver f q hq) =
      (graphOver f (q ≫ a) (by rw [Category.assoc, ha, hq])).ker := by
  have h := congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_ofPoint f a ha q hq)
  exact h

lemma graphOver_congr {T : Scheme.{u}} {g : T ⟶ S} {a a' : T ⟶ 𝒞} (h : a = a')
    (ha : a ≫ f = g) (ha' : a' ≫ f = g) : graphOver f a ha = graphOver f a' ha' := by
  subst h
  rfl

lemma prodKerGraph_cons {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (x : T ⟶ 𝒞) (hx : x ≫ f = g)
    (b : Fin r → (T ⟶ 𝒞)) (hb : ∀ i, b i ≫ f = g) :
    prodKerGraph f (Fin.cons x b) (Fin.cases hx hb) = (graphOver f x hx).ker * prodKerGraph f b hb := by
  rw [prodKerGraph_succ]
  rfl

lemma surjective_of_finrank_eq_succ {X Y : Scheme.{u}} (p : X ⟶ Y) [IsFinite p] [Flat p]
    {n : ℕ} (h : ∀ y, p.finrank y = n + 1) : Surjective p := by
  refine (Scheme.Hom.one_le_finrank_iff_surjective p).mp fun y => ?_
  show 1 ≤ p.finrank y
  rw [h y]
  exact Nat.succ_le_succ (Nat.zero_le n)

variable [IsSeparated f] [SmoothOfRelativeDimension 1 f]

theorem exists_split : ∀ (r : ℕ) {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g),
    ∃ (P : Scheme.{u}) (gP : P ⟶ S) (p : P ⟶ T) (hp : p ≫ g = gP)
      (b : Fin r → (P ⟶ 𝒞)) (hb : ∀ i, b i ≫ f = gP),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      (∀ t : T, p.finrank t = r.factorial) ∧
      (D.pullbackAlong p hp).I = prodKerGraph f b hb ∧
      ∀ ⦃T' : Scheme.{u}⦄ (g' : T' ⟶ S) (q : T' ⟶ T) (hq : q ≫ g = g')
        (b' : Fin r → (T' ⟶ 𝒞)) (hb' : ∀ i, b' i ≫ f = g'),
        (D.pullbackAlong q hq).I = prodKerGraph f b' hb' →
        ∃! u : T' ⟶ P, u ≫ p = q ∧ ∀ i, u ≫ b i = b' i
  | 0, T, g, D => by
    refine ⟨T, g, 𝟙 T, Category.id_comp g, Fin.elim0, fun i => i.elim0, inferInstance,
      inferInstance, inferInstance, inferInstance, fun t => ?_, ?_, ?_⟩
    · rw [Nat.factorial_zero, Scheme.Hom.finrank_eq_one_of_isIso (𝟙 T)]
      rfl
    · change D.I.comap _ = _
      rw [RelEffCartierDiv.I_eq_top_of_degree_zero D, Scheme.IdealSheafData.comap_top,
        prodKerGraph_zero]
    · intro T' g' q hq b' hb' _
      refine ⟨q, ⟨Category.comp_id q, fun i => i.elim0⟩, fun u hu => ?_⟩
      simpa only [Category.comp_id] using hu.1
  | r + 1, T, g, D => by
    have := D.isFinite
    have := D.flat
    have := D.locallyOfFinitePresentation

    let π : D.I.subscheme ⟶ T := D.I.subschemeι ≫ pullback.snd f g
    let gZ : D.I.subscheme ⟶ S := π ≫ g
    have hπ : π ≫ g = gZ := rfl
    let a : D.I.subscheme ⟶ 𝒞 := D.I.subschemeι ≫ pullback.fst f g
    have ha : a ≫ f = gZ := by
      simp only [a, gZ, π, Category.assoc, pullback.condition]
    haveI hπsurj : Surjective π := surjective_of_finrank_eq_succ π D.finrank_eq

    have htaut : (D.pullbackAlong π hπ).I ≤ (graphOver f a ha).ker :=
      D.pullbackAlong_I_le_ker_graphOver_taut hπ
    obtain ⟨E, hE⟩ := RelEffCartierDiv.exists_I_eq_ker_graphOver_mul (D.pullbackAlong π hπ) a ha htaut

    obtain ⟨P, gP, pE, hpE, bE, hbE, hfin, hflat, hlfp, hsurj, hrank, hsplit, huniv⟩ :=
      exists_split r E
    have hp : (pE ≫ π) ≫ g = gP := by rw [Category.assoc]; exact hpE
    have hb : ∀ i, (Fin.cons (pE ≫ a) bE : Fin (r + 1) → (P ⟶ 𝒞)) i ≫ f = gP :=
      Fin.cases (by rw [Fin.cons_zero, Category.assoc, ha]; exact hpE)
        (fun i => by rw [Fin.cons_succ]; exact hbE i)
    refine ⟨P, gP, pE ≫ π, hp, Fin.cons (pE ≫ a) bE, hb, inferInstance, inferInstance,
      inferInstance, inferInstance, fun t => ?_, ?_, ?_⟩
    ·
      rw [Scheme.Hom.finrank_comp_of_finrank_eq_const pE π r.factorial hrank t,
        show π.finrank t = r + 1 from D.finrank_eq t, Nat.factorial_succ, Nat.mul_comm]
    ·
      have hcomp : D.pullbackAlong (pE ≫ π) hp = (D.pullbackAlong π hπ).pullbackAlong pE hpE :=
        (RelEffCartierDiv.pullbackAlong_comp D π hπ pE hpE).symm
      rw [hcomp]
      change (D.pullbackAlong π hπ).I.comap (mapOnProdOver f pE hpE) = _
      rw [hE, Scheme.IdealSheafData.comap_mul, ker_graphOver_comap]
      change _ * (E.pullbackAlong pE hpE).I = _
      rw [hsplit]
      exact (prodKerGraph_cons (pE ≫ a) _ bE hbE).symm
    ·
      intro T' g' q hq b' hb' hsplit'

      have hle : (D.pullbackAlong q hq).I ≤ (graphOver f (b' 0) (hb' 0)).ker := by
        rw [hsplit', prodKerGraph_succ]
        exact mul_le_of_le_one_right bot_le le_top
      let z : T' ⟶ D.I.subscheme := D.liftOfLE q hq (b' 0) (hb' 0) hle
      have hzπ : z ≫ π = q := D.liftOfLE_ι_snd q hq (b' 0) (hb' 0) hle
      have hza : z ≫ a = b' 0 := D.liftOfLE_ι_fst q hq (b' 0) (hb' 0) hle
      have hz : z ≫ gZ = g' := by
        show z ≫ (π ≫ g) = g'
        rw [← Category.assoc, hzπ, hq]

      have hEz : (E.pullbackAlong z hz).I = prodKerGraph f (fun i => b' i.succ) (fun i => hb' i.succ) := by
        have h1 : ((D.pullbackAlong π hπ).pullbackAlong z hz).I =
            (graphOver f (b' 0) (hb' 0)).ker * (E.pullbackAlong z hz).I := by
          change (D.pullbackAlong π hπ).I.comap (mapOnProdOver f z hz) = _
          rw [hE, Scheme.IdealSheafData.comap_mul, ker_graphOver_comap,
            graphOver_congr hza _ (hb' 0)]
          rfl
        have h2 : ((D.pullbackAlong π hπ).pullbackAlong z hz).I =
            (graphOver f (b' 0) (hb' 0)).ker * prodKerGraph f (fun i => b' i.succ) (fun i => hb' i.succ) := by
          rw [RelEffCartierDiv.pullbackAlong_comp D π hπ z hz,
            pullbackAlong_congr D hzπ _ hq, hsplit', prodKerGraph_succ]
        have hinv : (graphOver f (b' 0) (hb' 0)).ker.IsInvertible :=
          RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint f (b' 0) (hb' 0))
        exact hinv.mul_left_cancel (h1.symm.trans h2)
      obtain ⟨u, ⟨hu1, hu2⟩, huniq⟩ := huniv g' z hz (fun i => b' i.succ) (fun i => hb' i.succ) hEz
      refine ⟨u, ⟨?_, ?_⟩, ?_⟩
      · rw [← Category.assoc, hu1, hzπ]
      · refine Fin.cases ?_ (fun i => ?_)
        · rw [Fin.cons_zero, ← Category.assoc, hu1, hza]
        · rw [Fin.cons_succ]
          exact hu2 i
      ·
        intro u' ⟨hu'1, hu'2⟩
        have hz' : u' ≫ pE = z := by
          apply D.hom_subscheme_ext
          · show (u' ≫ pE) ≫ a = z ≫ a
            rw [hza, Category.assoc]
            have := hu'2 0
            rwa [Fin.cons_zero] at this
          · show (u' ≫ pE) ≫ π = z ≫ π
            rw [hzπ, Category.assoc]
            exact hu'1
        exact huniq u' ⟨hz', fun i => by have := hu'2 i.succ; rwa [Fin.cons_succ] at this⟩

end AlgebraicGeometry.RelEffCartierDiv.SplitProof

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) :
    ∃ (P : Scheme.{u}) (gP : P ⟶ S) (p : P ⟶ T) (hp : p ≫ g = gP)
      (b : Fin r → (P ⟶ 𝒞)) (hb : ∀ i, b i ≫ f = gP),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      (∀ t : T, p.finrank t = r.factorial) ∧
      (D.pullbackAlong p hp).I = prodKerGraph f b hb ∧
      ∀ ⦃T' : Scheme.{u}⦄ (g' : T' ⟶ S) (q : T' ⟶ T) (hq : q ≫ g = g')
        (b' : Fin r → (T' ⟶ 𝒞)) (hb' : ∀ i, b' i ≫ f = g'),
        (D.pullbackAlong q hq).I = prodKerGraph f b' hb' →
        ∃! u : T' ⟶ P, u ≫ p = q ∧ ∀ i, u ≫ b i = b' i :=
  AlgebraicGeometry.RelEffCartierDiv.SplitProof.exists_split r D

end S_AlgebraicGeometry_RelEffCartierDiv_exists_split
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_split (solution)
