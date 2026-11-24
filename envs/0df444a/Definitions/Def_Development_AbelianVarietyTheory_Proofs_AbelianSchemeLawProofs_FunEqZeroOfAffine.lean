-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FunEqZeroOfAffine
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FunEqZeroOfAffine
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T18:08:10.069918+00:00
-- url     : https://prove2.me/theorems/36c92341-5430-44f2-abfb-6bb37ec5bf4a
-- title:
--   Fun Eq Zero Of Affine
-- statement:
--   Definitions and structural lemmas for Fun Eq Zero Of Affine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FunEqZeroOfAffine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SectionsGroupRank
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SectionsGroupRank_isPullSec_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_pullGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.VVCompare
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank
section General
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
theorem wchart_le_of_eq {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k)
    (j : K → L.ι) : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
def pullTo {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) : LB.Sec (LB.LinComb L φ' ε) where
  f j := (Y'.presheaf.map (homOfLE (wchart_le_of_eq h e j)).op).hom ((h.app _).hom (s.f j))
  compat := by
    obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
    exact (H1.SectionArithmetic.pullSec s h).compat
theorem sval_pullTo {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval (pullTo s h e) r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact H1.SectionArithmetic.sval_pullSec s h r z hJ
theorem exists_gen_pullTo {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J),
      Good L z J → val t' r z J = val t (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact ⟨LB.pullGen L φ ε t h, LB.isGen_pullGen L φ ε t ht h, fun Z r z J hJ => val_pull hJ t h r⟩
end General
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
omit [GrpObj A] in
theorem whisker_snd_left {T T' : Over S} (h : T' ⟶ T) :
    (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by
  rw [← Over.comp_left, whiskerRight_snd]
abbrev pullS (a : ℤ) {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) : LB.Sec (LPow A L a T') :=
  pullSec (A := A) (L := L) (a := a) h s
abbrev sv {a : ℤ} {T : Over S} (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : Z.presheaf.stalk z :=
  sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z J
theorem sv_pullS (a : ℤ) {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sv A (pullS A a h s) r z J = sv A s (r ≫ (h ▷ A).left) z J :=
  sval_pullTo (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (h ▷ A).left
    (fun _ => whisker_snd_left A h) r z hJ
section Twist
variable {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
theorem sv_of_isTwistPull {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L ψ m hm a b α s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sv A s' r z J = (val α r z J).val * sv A s (r ≫ ψ.left) z J := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  have hz := hJ.mem ![(snd T A).left, m.left] r
  have key : ∀ j : Fin 2 → L.ι, r z ∈ LB.wchart L ![(snd T A).left, m.left] j →
      gs r z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) =
        (gm r z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j)).val *
          gs (r ≫ ψ.left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1)) := fun j hz =>
    (gs_res r z _ hz _).symm.trans ((congrArg (gs r z _) (H j)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit r z _ hz _) ((gs_res r z _ hz _).trans
        (gs_pull r ψ.left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
          (chart_le_pull A L ψ m hm j hz) _)))))
  have e₁ := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J
    (fun _ => J (r ≫ m.left)) (fun _ => by rw [Category.assoc, e])
  exact (key _ hz).trans (congrArg _ e₁.symm)
theorem isTwistPull_of_sv (hL : L.IsLB) (hα : α.IsGen) {s : LB.Sec (LPow A L b T)}
    {s' : LB.Sec (LPow A L a T)}
    (H : ∀ y J, Good L y J → sv A s' (𝟙 _) y J = (val α (𝟙 _) y J).val * sv A s (𝟙 _ ≫ ψ.left) y J) :
    IsTwistPull A L ψ m hm a b α s s' := by
  intro j
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have h0 := chart_le_zero A L m j hy
  have h1 := chart_le_pull A L ψ m hm j hy
  refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ y _ hy _) ((gs_res _ y _ hy _).trans
      (gs_pull _ ψ.left y _ h1 _)))).symm)
  refine (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y h0
    (Good.mem hJ _ _)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val (gen_trans hα (𝟙 _) y hy (Good.mem hJ _ _)))
    (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y h1
    (Good.mem hJ _ _))).symm
  refine (congrArg _ (H y J hJ)).trans ?_
  rw [Units.val_mul]
  refine Eq.trans ?_ (_root_.mul_mul_mul_comm _ _ _ _)
  rw [← Units.val_mul]
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
  have e' : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, e]
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, zpow_neg]
  rw [e']
  exact (inv_mul_cancel_right _ _).symm
theorem exists_twist_pull (hL : L.IsLB) (hα : α.IsGen) {T' : Over S} (h : T' ⟶ T)
    {ψ' : T' ⊗ A ⟶ T' ⊗ A} {m' : T' ⊗ A ⟶ A} (hm' : ψ' ≫ snd T' A = m')
    (e : ψ' ≫ h ▷ A = h ▷ A ≫ ψ) :
    ∃ α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, m'.left] ![a, -b]), α'.IsGen ∧
      ∀ s s', IsTwistPull A L ψ m hm a b α s s' →
        IsTwistPull A L ψ' m' hm' a b α' (pullS A b h s) (pullS A a h s') := by
  obtain ⟨α', h₁, h₂⟩ := exists_gen_pullTo (φ' := ![(snd T' A).left, m'.left]) α hα (h ▷ A).left
    (fun k => by
      fin_cases k
      · exact whisker_snd_left A h
      · change (h ▷ A).left ≫ m.left = m'.left
        rw [← Over.comp_left, ← hm, ← hm', ← Category.assoc, ← e, Category.assoc, whiskerRight_snd])
  refine ⟨α', h₁, fun s s' H => isTwistPull_of_sv A hL h₁ fun y J hJ => ?_⟩
  rw [sv_pullS A a h s' _ y hJ, sv_pullS A b h s _ y hJ, h₂ _ _ y J hJ, sv_of_isTwistPull A H _ y hJ,
    Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, e]
end Twist
theorem exists_theta_pull (hL : L.IsLB) {k : ℤ} {T T' : Over S} (h : T' ⟶ T) (θ : ThetaGrp A L k T) :
    ∃ θ' : ThetaGrp A L k T', θ'.pt = h ≫ θ.pt ∧
      ∀ s s', IsActOf A L k θ s s' → IsActOf A L k θ' (pullS A k h s) (pullS A k h s') := by
  obtain ⟨α', h₁, h₂⟩ := exists_twist_pull A (ψ := translT A θ.pt) (hm := lift_snd _ _) hL θ.isGen h
    (ψ' := translT A (h ≫ θ.pt)) (m' := translPt A (h ≫ θ.pt)) (lift_snd _ _) (by
      ext1
      · simp [translT]
      · simp [translT, translPt, comp_lift_assoc])
  exact ⟨⟨h ≫ θ.pt, α', h₁⟩, rfl, h₂⟩
theorem mulT_comm {T T' : Over S} (h : T' ⟶ T) (n : ℕ) :
    mulT A T' n ≫ h ▷ A = h ▷ A ≫ mulT A T n := by
  ext1
  · simp [mulT]
  · simp [mulT, MonObj.comp_pow]
theorem isVVGen_pull (P : PolAV S) (N n : ℕ) {T T' : Over S} (h : T' ⟶ T)
    {t : LB.Sec (LPow P.A P.L N T)} (ht : IsVVGen P N n t) : IsVVGen P N n (pullS P.A N h t) := by
  obtain ⟨th, s1, α, U, hα, h₁, h₂⟩ := ht
  obtain ⟨α', k₁, k₂⟩ := exists_twist_pull P.A (ψ := mulT P.A T n) (hm := lift_snd _ _) (b := 1)
    P.isLB hα h (ψ' := mulT P.A T' n) (lift_snd _ _) (mulT_comm P.A h n)
  obtain ⟨U', -, k₃⟩ := exists_theta_pull P.A P.isLB h U
  exact ⟨_, _, α', U', k₁, k₂ _ _ h₁, k₃ _ _ h₂⟩
section Pull
variable {A} {a : ℤ} {T T' T'' : Over S}
theorem pullSec_comp (u' : T'' ⟶ T') (u : T' ⟶ T) (s : Secs A L a T) :
    pullSec u' (pullSec u s) = pullSec (u' ≫ u) s :=
  Secs.ext fun j => ev_ev (u' ▷ A).left (u ▷ A).left ((u' ≫ u) ▷ A).left
    (by rw [comp_whiskerRight, Over.comp_left]) _ _ _ (s.f j)
theorem pullSec_id (hL : L.IsLB) (s : Secs A L a T) : pullSec (𝟙 T) s = s :=
  Secs.ext (sec_ext_val hL fun y J hJ => by
    refine (sv_pullS A a _ _ _ y hJ).trans ?_
    rw [id_whiskerRight, Over.id_left, Category.comp_id])
theorem eq_pullSec {u : T' ⟶ T} {s : Secs A L a T} {s' : Secs A L a T'}
    (h : IsPullSec A L a (u ▷ A) (whiskerRight_snd _ _) s s') : s' = pullSec u s := Secs.ext h
def pullL (u : T' ⟶ T) : Secs A L a T →ₛₗ[u.left.appTop.hom] Secs A L a T' where
  toFun := pullSec u
  map_add' := pullSec_add u
  map_smul' := pullSec_smul u
theorem pullSec_sum {κ : Type} [Fintype κ] (u : T' ⟶ T) (c : κ → Γ(T.left, ⊤)) (b : κ → Secs A L a T) :
    pullSec u (∑ l, c l • b l) = ∑ l, u.left.appTop.hom (c l) • pullSec u (b l) :=
  (map_sum (pullL u) _ _).trans (Finset.sum_congr rfl fun l _ => pullSec_smul u (c l) (b l))
theorem sum_f {κ : Type} (F : Finset κ) (b : κ → Secs A L a T) (j) :
    LB.Sec.f (∑ l ∈ F, b l : Secs A L a T) j = ∑ l ∈ F, LB.Sec.f (b l) j :=
  map_sum (AddMonoidHom.mk' (fun s : Secs A L a T => LB.Sec.f s j) fun s t => add_f s t j) b F
def resHom (u : T' ⟶ T) (V : T.left.Opens) (V' : T'.left.Opens) (e : V' ≤ u.left ⁻¹ᵁ V) :
    overRes V' ⟶ overRes V :=
  Over.homMk (u.left.resLE V V' e) (by
    change u.left.resLE V V' e ≫ V.ι ≫ T.hom = V'.ι ≫ T'.hom
    rw [Scheme.Hom.resLE_comp_ι_assoc, Over.w u])
theorem resHom_ι (u : T' ⟶ T) (V : T.left.Opens) (V' : T'.left.Opens) (e : V' ≤ u.left ⁻¹ᵁ V) :
    resHom u V V' e ≫ overResι V = overResι V' ≫ u :=
  Over.OverMorphism.ext (Scheme.Hom.resLE_comp_ι u.left e)
end Pull
section VV
variable (P : PolAV S) (N m : ℕ) {T T' : Over S}
def genSpan (T : Over S) : Submodule Γ(T.left, ⊤) (Secs P.A P.L N T) :=
  Submodule.span Γ(T.left, ⊤) {t | IsVVGen P N m t}
theorem inVVOver_iff (s : Secs P.A P.L N T) : InVVOver P N m s ↔ s ∈ genSpan P N m T := by
  constructor
  · rintro ⟨n, r, t, ht, hs⟩
    have : s = ∑ l, r l • (show Secs P.A P.L N T from t l) :=
      Secs.ext fun j => (hs j).trans (sum_f _ (fun l => r l • (show Secs P.A P.L N T from t l)) j).symm
    rw [this]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span (ht l))
  · intro hs
    obtain ⟨n, r, t, rfl⟩ := Submodule.mem_span_set'.1 hs
    exact ⟨n, r, fun l => (t l).1, fun l => (t l).2, fun j => sum_f _ _ j⟩
theorem pullSec_mem_genSpan (u : T' ⟶ T) {s : Secs P.A P.L N T} (hs : s ∈ genSpan P N m T) :
    pullSec u s ∈ genSpan P N m T' := by
  obtain ⟨n, r, t, rfl⟩ := Submodule.mem_span_set'.1 hs
  rw [pullSec_sum]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
    (Submodule.subset_span (isVVGen_pull P N m u (t l).2))
theorem inVV_iff (s : Secs P.A P.L N T) : InVV P N m s ↔
    ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ pullSec (overResι V) s ∈ genSpan P N m (overRes V) := by
  refine forall_congr' fun p => exists_congr fun V => and_congr_right fun _ => ⟨?_, fun h => ?_⟩
  · rintro ⟨sV, h₁, h₂⟩
    rw [← eq_pullSec h₁]
    exact (inVVOver_iff P N m _).1 h₂
  · exact ⟨_, isPullSec_pullSec _ s, (inVVOver_iff P N m _).2 h⟩
theorem genSpan_res (u : T' ⟶ T) {V : T.left.Opens} {V' : T'.left.Opens} (e : V' ≤ u.left ⁻¹ᵁ V)
    {s : Secs P.A P.L N T} (hs : pullSec (overResι V) s ∈ genSpan P N m (overRes V)) :
    pullSec (overResι V') (pullSec u s) ∈ genSpan P N m (overRes V') := by
  rw [pullSec_comp, ← resHom_ι u V V' e, ← pullSec_comp]
  exact pullSec_mem_genSpan P N m _ hs
def locSpan (T : Over S) : Submodule Γ(T.left, ⊤) (Secs P.A P.L N T) where
  carrier := {s | InVV P N m s}
  zero_mem' := (inVV_iff P N m _).2 fun _ => ⟨⊤, trivial, by rw [pullSec_zero]; exact zero_mem _⟩
  add_mem' := fun {s t} hs ht => (inVV_iff P N m _).2 fun p => by
    obtain ⟨V, hV, h⟩ := (inVV_iff P N m s).1 hs p
    obtain ⟨V', hV', h'⟩ := (inVV_iff P N m t).1 ht p
    have k := genSpan_res P N m (𝟙 T) (V' := V ⊓ V') (fun _ hx => hx.1) h
    have k' := genSpan_res P N m (𝟙 T) (V' := V ⊓ V') (fun _ hx => hx.2) h'
    rw [pullSec_id P.isLB] at k k'
    exact ⟨V ⊓ V', ⟨hV, hV'⟩, by rw [pullSec_add]; exact add_mem k k'⟩
  smul_mem' := fun r s hs => (inVV_iff P N m _).2 fun p => by
    obtain ⟨V, hV, h⟩ := (inVV_iff P N m s).1 hs p
    exact ⟨V, hV, by rw [pullSec_smul]; exact Submodule.smul_mem _ _ h⟩
variable {κ : Type} [Fintype κ]
def IsVVBasis (b : κ → Secs P.A P.L N T) : Prop :=
  (∀ l, b l ∈ VV P N m T) ∧ (∀ c : κ → Γ(T.left, ⊤), ∑ l, c l • b l = 0 → ∀ l, c l = 0) ∧
    ∀ s ∈ VV P N m T, ∃ c : κ → Γ(T.left, ⊤), ∑ l, c l • b l = s
variable {P N m}
end VV
def secEquiv (L : LB A.left) (a : ℤ) (T : Over S) : SecM A L a T ≃ₗ[Γ(T.left, ⊤)] Secs A L a T where
  toFun := SecM.toSec A
  invFun := SecM.ofSec A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
def secIncl (L : LB A.left) (a : ℤ) (T : Over S) :
    Secs A L a T →ₗ[Γ(T.left, ⊤)] (∀ j, Γ((T ⊗ A).left, (LPow A L a T).U j)) :=
  (SecM A L a T).subtype ∘ₗ (secEquiv A L a T).symm.toLinearMap
theorem secIncl_injective (L : LB A.left) (a : ℤ) (T : Over S) : Function.Injective (secIncl A L a T) :=
  fun _ _ h => Secs.ext (congrFun h)
theorem span_eq_map (L : LB A.left) (a : ℤ) (T : Over S) (Q : LB.Sec (LPow A L a T) → Prop) :
    Submodule.span Γ(T.left, ⊤) {f | ∃ h : f ∈ SecM A L a T, Q (SecM.toSec A ⟨f, h⟩)} =
      (Submodule.span Γ(T.left, ⊤) {s : Secs A L a T | Q s}).map (secIncl A L a T) := by
  rw [Submodule.map_span]
  refine congrArg _ (Set.ext fun f => ⟨?_, ?_⟩)
  · rintro ⟨h, hQ⟩
    exact ⟨_, hQ, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.compat, hs⟩
variable (P : PolAV S) (N m : ℕ)
theorem vvSub_eq_map (T : Over S) : VVsub P N m T = (VV P N m T).map (secIncl P.A P.L N T) :=
  span_eq_map P.A P.L N T (InVV P N m)
def vvEquiv (T : Over S) : VV P N m T ≃ₗ[Γ(T.left, ⊤)] VVsub P N m T :=
  (Submodule.equivMapOfInjective _ (secIncl_injective P.A P.L N T) _).trans
    (LinearEquiv.ofEq _ _ (vvSub_eq_map P N m T).symm)
def deEquiv (T : Over S) : Out.de P T ≃ₗ[Γ(T.left, ⊤)] SectionsGroupRank.de P T :=
  (secEquiv P.A P.L 1 T).symm.dualMap
def RestrictsBases (T : Over S) : Prop :=
  ∀ W : T.left.Opens, IsAffineOpen W → ∀ (n : ℕ) (β : Module.Basis (Fin n) Γ(T.left, ⊤) (VVsub P N m T)),
    ∃ β' : Module.Basis (Fin n) Γ((overRes W).left, ⊤) (VVsub P N m (overRes W)), ∀ l j,
      (β' l).1 j = ((overResι W ▷ P.A).left.appLE _ _
        (chart_le_res P.A P.L (overResι W ▷ P.A) (whiskerRight_snd _ _) N j)).hom ((β l).1 j)
def VVRankRes (S : Scheme.{0}) : Prop :=
  ∀ (P : PolAV S) (m : ℕ) (ze : Γ(S, ⊤)ˣ), Odd m → IsUnit ((m : Γ(S, ⊤))) →
    Nonempty (Level P (m ^ 2) ze) → ∀ (T : Over S) (p : T.left), ∃ V : T.left.Opens, p ∈ V ∧
      IsAffineOpen V ∧ Module.Free Γ((overRes V).left, ⊤) (VVsub P (m ^ 2) m (overRes V)) ∧
      Module.finrank Γ((overRes V).left, ⊤) (VVsub P (m ^ 2) m (overRes V)) = (m ^ 2) ^ P.g ∧
      RestrictsBases P (m ^ 2) m (overRes V)
end GlobalTheory.VVCompare


