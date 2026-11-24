-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:01:21.857549+00:00
-- url     : https://prove2.me/theorems/82709eec-7ca4-478e-81b9-90806bd7666d
-- title:
--   Exists Unique Sec Is Fn At
-- statement:
--   Definitions and structural lemmas for Exists Unique Sec Is Fn At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_val_linComb
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_exists_chart
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
section Values
variable {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X)
def valHom (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom
theorem valAt'_eq_valHom {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = valHom x U h f := by
  rw [valAt', dif_pos h]; rfl
theorem valAt'_mul {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)) :
    valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  simp only [valAt'_eq_valHom x h, map_mul]
theorem valAt'_add {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)) :
    valAt' x U (f + f') = valAt' x U f + valAt' x U f' := by
  simp only [valAt'_eq_valHom x h, map_add]
theorem valAt'_res {U V : X.Opens} (h : V ≤ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valAt' x V ((X.presheaf.map (homOfLE h).op).hom f) = valAt' x U f :=
  (valueRules X x).2.2.1 U V h f hV
theorem valAt'_app (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f :=
  (valueRules X x).2.2.2.1 Y φ U f
theorem valAt'_sec {M : LB X} (s : M.Sec) (i j : M.ι) (hi : ⊤ ≤ x ⁻¹ᵁ M.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ M.U j) :
    valAt' x (M.U i) (s.f i) =
      valAt' x (M.U i ⊓ M.U j) (M.g i j).val * valAt' x (M.U j) (s.f j) := by
  have hij := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  rw [← valAt'_res x inf_le_left hij (s.f i), s.compat i j, valAt'_mul x hij,
    valAt'_res x inf_le_right hij]
theorem valAt'_id_top (r : Γ(Sp ℂ, ⊤)) :
    valAt' (𝟙 (Sp ℂ)) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom r := by
  have e : ∀ k, Scheme.Hom.appLE (𝟙 (Sp ℂ)) ⊤ ⊤ k = 𝟙 _ := fun k => by
    rw [← Scheme.Hom.id_app]
    exact (Scheme.Hom.app_eq_appLE (𝟙 (Sp ℂ)) (U := ⊤)).symm
  rw [valAt', dif_pos (show ⊤ ≤ 𝟙 (Sp ℂ) ⁻¹ᵁ ⊤ from fun _ _ => trivial), valAt, e]
  rfl
end Values
section Transport
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] [Unique K]
  [Unique K']
theorem res_appLE (h : Z ⟶ Y) {U U' : Y.Opens} {V V' : Z.Opens} (hU : U' ≤ U) (hV : V' ≤ V)
    (e : V ≤ h ⁻¹ᵁ U) (e' : V' ≤ h ⁻¹ᵁ U') (f : Γ(Y, U)) :
    (Z.presheaf.map (homOfLE hV).op).hom ((h.appLE U V e).hom f) =
      (h.appLE U' V' e').hom ((Y.presheaf.map (homOfLE hU).op).hom f) :=
  congrArg (fun t : Γ(Y, U) ⟶ Γ(Z, V') => t.hom f)
    ((Scheme.Hom.appLE_map h e (homOfLE hV).op).trans
      (Scheme.Hom.map_appLE h e' (homOfLE hU).op).symm)
omit [Unique K] in

theorem wchart_le_of_comp {φ : Y ⟶ X} {ψ : Z ⟶ X} {h : Z ⟶ Y} (e : h ≫ φ = ψ) (j : K' → L.ι) :
    LB.wchart L (fun _ : K' => ψ) j ≤
      h ⁻¹ᵁ LB.wchart L (fun _ : K => φ) (fun _ => j default) := by
  subst e
  exact fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy default
theorem le_wchart_unique {W : Scheme.{0}} (x : W ⟶ Y) (φ : Y ⟶ X) (j : K → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : K => φ) j ↔ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (j default) :=
  ⟨fun h _ hy => Set.mem_iInter.1 (h hy) default, fun h _ hy => Set.mem_iInter.2 fun k => by
    rw [Subsingleton.elim k default]; exact h hy⟩
def pullPow {φ : Y ⟶ X} {ψ : Z ⟶ X} (h : Z ⟶ Y) (e : h ≫ φ = ψ) (a : ℤ)
    (s : LB.Sec (LB.LinComb L (fun _ : K => φ) (fun _ => a))) :
    LB.Sec (LB.LinComb L (fun _ : K' => ψ) (fun _ => a)) where
  f j := (h.appLE _ _ (wchart_le_of_comp L (K := K) e j)).hom (s.f (fun _ => j default))
  compat i j := by
    have hij : LB.wchart L (fun _ : K' => ψ) i ⊓ LB.wchart L (fun _ : K' => ψ) j ≤
        h ⁻¹ᵁ (LB.wchart L (fun _ : K => φ) (fun _ => i default) ⊓
          LB.wchart L (fun _ : K => φ) (fun _ => j default)) :=
      le_inf (inf_le_left.trans (wchart_le_of_comp L e i))
        (inf_le_right.trans (wchart_le_of_comp L e j))
    have hc := congrArg (h.appLE _ _ hij).hom (s.compat (fun _ => i default) (fun _ => j default))
    replace hc := hc.trans (map_mul (h.appLE _ _ hij).hom _ _)
    have hg : (h.appLE _ _ hij).hom ((LB.LinComb L (fun _ : K => φ) (fun _ => a)).g
        (fun _ => i default) (fun _ => j default)).val =
        ((LB.LinComb L (fun _ : K' => ψ) (fun _ => a)).g i j).val := by
      subst e
      change (Units.map (h.appLE _ _ hij).hom.toMonoidHom _).val = _
      congr 1
      simp only [LB.LinComb, Fintype.prod_unique, map_zpow]
      congr 1
      ext1
      exact congrArg (fun t => t.hom (L.g (i default) (j default)).val)
        (Scheme.Hom.appLE_comp_appLE h φ _ _ _ _ hij)
    refine Eq.trans ?_ (hc.trans (congrArg₂ (· * ·) hg ?_))
    · exact res_appLE h _ _ _ hij _
    · exact (res_appLE h _ _ _ hij _).symm
theorem pullPow_pullPow {φ : Y ⟶ X} {ψ : Z ⟶ X} (h : Z ⟶ Y) (e : h ≫ φ = ψ) (h' : Y ⟶ Z)
    (e' : h' ≫ ψ = φ) (hh : h' ≫ h = 𝟙 Y) (a : ℤ)
    (s : LB.Sec (LB.LinComb L (fun _ : K => φ) (fun _ => a))) :
    pullPow L (K' := K) h' e' a (pullPow L (K' := K') h e a s) = s := by
  have key : ∀ (t : Y ⟶ Y) (_ : t = 𝟙 Y) (U : Y.Opens) (l : U ≤ t ⁻¹ᵁ U),
      t.appLE U U l = 𝟙 _ := by
    rintro _ rfl U l
    rw [← Scheme.Hom.id_app]
    exact (Scheme.Hom.app_eq_appLE (𝟙 Y) (U := U)).symm
  have hf : (pullPow L (K' := K) h' e' a (pullPow L (K' := K') h e a s)).f = s.f := by
    funext j
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i :=
      ⟨j default, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    exact congrArg (fun t => t.hom (s.f fun _ => i))
      ((Scheme.Hom.appLE_comp_appLE h' h _ _ _ _ _).trans (key _ hh _ _))
  cases s
  exact (LB.Sec.mk.injEq _ _ _ _).mpr hf
end Transport
section Fibre
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable (A) in

def fibreIncl : A ⟶ T ⊗ A := lift (toUnit A ≫ p) (𝟙 A)
omit [GrpObj A] in

theorem fibreIncl_snd : (fibreIncl A p).left ≫ (snd T A).left = 𝟙 A.left := by
  rw [← Over.comp_left, fibreIncl, lift_snd, Over.id_left]
omit [GrpObj A] in

theorem snd_fibreIncl [IsIso p] : (snd T A).left ≫ (fibreIncl A p).left = 𝟙 (T ⊗ A).left := by
  rw [← Over.comp_left, ← Over.id_left]
  congr 1
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [← cancel_mono (inv p)]
    exact toUnit_unique _ _
  · rw [Category.assoc, fibreIncl, lift_snd, Category.comp_id, Category.id_comp]
def exAt (z : Fin g → ℂ) : Sp ℂ ⟶ (T ⊗ A).left := (lift p (u.ex z)).left
theorem exAt_snd (z : Fin g → ℂ) : exAt u p z ≫ (snd T A).left = (u.ex z).left :=
  (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_snd p (u.ex z)))
theorem exAt_fst (z : Fin g → ℂ) : exAt u p z ≫ (fst T A).left = p.left :=
  (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_fst p (u.ex z)))
theorem exAt_mem_chart_iff (k : ℤ) (j : Fin 1 → L.ι) (z : Fin g → ℂ) :
    ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j ↔ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) := by
  refine (le_wchart_unique L (exAt u p z) (snd T A).left j).trans ?_
  rw [exAt_snd]
  rfl
theorem valAt'_liftFun {W : (T ⊗ A).left.Opens} {z : Fin g → ℂ} (hW : ⊤ ≤ exAt u p z ⁻¹ᵁ W)
    (r : Γ(T.left, ⊤)) : valAt' (exAt u p z) W (liftFun A W r) = valAt' p.left ⊤ r := by
  refine (valAt'_res (exAt u p z) (U := (fst T A).left ⁻¹ᵁ ⊤) le_top hW _).trans ?_
  refine (valAt'_app (exAt u p z) (fst T A).left ⊤ r).trans ?_
  rw [exAt_fst]
theorem valAt'_LPow_g (k : ℤ) (j j' : Fin 1 → L.ι) (z : Fin g → ℂ)
    (hj : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j) (hj' : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j') :
    valAt' (exAt u p z) ((LPow A L k T).U j ⊓ (LPow A L k T).U j') ((LPow A L k T).g j j').val =
      valAt' (u.ex z).left (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)).val ^ k := by
  refine (val_linComb (exAt u p z) valueRules L _ _ j j' hj hj').trans ?_
  rw [Fin.prod_univ_one, exAt_snd]
def IsFnAt (k : ℤ) (s : LB.Sec (LPow A L k T)) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (j : Fin 1 → L.ι) z, ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j →
    valAt' (exAt u p z) ((LPow A L k T).U j) (s.f j) = θ z * u.fr (j 0) z ^ k
theorem exists_chart_exAt (hL : L.IsLB) (k : ℤ) (z : Fin g → ℂ) :
    ∃ j : Fin 1 → L.ι, ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL z
  exact ⟨fun _ => i, (exAt_mem_chart_iff u p k _ z).2 hi⟩
theorem fr_zpow_ne_zero {k : ℤ} {j : Fin 1 → L.ι} {z : Fin g → ℂ}
    (hj : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j) (m : ℤ) : u.fr (j 0) z ^ m ≠ 0 :=
  zpow_ne_zero m (u.fr_ne _ z ((exAt_mem_chart_iff u p k j z).1 hj))
variable {u p} in

theorem IsFnAt.eq_div {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) {j : Fin 1 → L.ι} {z : Fin g → ℂ}
    (hj : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j) :
    θ z = valAt' (exAt u p z) ((LPow A L k T).U j) (s.f j) / u.fr (j 0) z ^ k := by
  rw [h j z hj, mul_div_cancel_right₀ _ (fr_zpow_ne_zero u p hj k)]
theorem isFnAt_of_exists_chart {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : ∀ z, ∃ j : Fin 1 → L.ι, ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j ∧
      valAt' (exAt u p z) ((LPow A L k T).U j) (s.f j) = θ z * u.fr (j 0) z ^ k) :
    IsFnAt u p k s θ := by
  intro j z hj
  obtain ⟨j', hj', e⟩ := h z
  have hc := u.fr_compat (j 0) (j' 0) z ((le_preimage_inf _ _ _).2
    ⟨(exAt_mem_chart_iff u p k j z).1 hj, (exAt_mem_chart_iff u p k j' z).1 hj'⟩)
  rw [valAt'_sec _ s j j' hj hj', valAt'_LPow_g u p k j j' z hj hj', e, hc, mul_zpow]
  ring
variable {u p} in

theorem IsFnAt.unique (hL : L.IsLB) {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {θ θ' : (Fin g → ℂ) → ℂ} (h : IsFnAt u p k s θ) (h' : IsFnAt u p k s θ') : θ = θ' := by
  funext z
  obtain ⟨j, hj⟩ := exists_chart_exAt u p hL k z
  rw [h.eq_div hj, h'.eq_div hj]
theorem existsUnique_isFnAt (hL : L.IsLB) (k : ℤ) (s : LB.Sec (LPow A L k T)) :
    ∃! θ, IsFnAt u p k s θ := by
  choose c hc using exists_chart_exAt u p hL k
  have h : IsFnAt u p k s fun z =>
      valAt' (exAt u p z) ((LPow A L k T).U (c z)) (s.f (c z)) / u.fr (c z 0) z ^ k :=
    isFnAt_of_exists_chart u p fun z =>
      ⟨c z, hc z, (div_mul_cancel₀ _ (fr_zpow_ne_zero u p (hc z) k)).symm⟩
  exact ⟨_, h, fun θ hθ => hθ.unique hL h⟩
def fnAt (hL : L.IsLB) (k : ℤ) (s : LB.Sec (LPow A L k T)) : (Fin g → ℂ) → ℂ :=
  (existsUnique_isFnAt u p hL k s).exists.choose
theorem isFnAt_fnAt (hL : L.IsLB) (k : ℤ) (s : LB.Sec (LPow A L k T)) :
    IsFnAt u p k s (fnAt u p hL k s) :=
  (existsUnique_isFnAt u p hL k s).exists.choose_spec
theorem isFnAt_iff_eq_fnAt (hL : L.IsLB) {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {θ : (Fin g → ℂ) → ℂ} : IsFnAt u p k s θ ↔ θ = fnAt u p hL k s :=
  ⟨fun h => h.unique hL (isFnAt_fnAt u p hL k s), fun h => h ▸ isFnAt_fnAt u p hL k s⟩
variable {u p}
theorem IsFnAt.add {k : ℤ} {s s' t : LB.Sec (LPow A L k T)} {θ θ' : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) (h' : IsFnAt u p k s' θ') (ht : ∀ j, t.f j = s.f j + s'.f j) :
    IsFnAt u p k t (θ + θ') := fun j z hj => by
  rw [ht j, valAt'_add _ hj, h j z hj, h' j z hj, Pi.add_apply, add_mul]
theorem IsFnAt.liftFun_mul {k : ℤ} {s t : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) (r : Γ(T.left, ⊤)) (ht : ∀ j, t.f j = liftFun A _ r * s.f j) :
    IsFnAt u p k t (valAt' p.left ⊤ r • θ) := fun j z hj => by
  rw [ht j, valAt'_mul _ hj, valAt'_liftFun u p hj, h j z hj, Pi.smul_apply, smul_eq_mul,
    _root_.mul_assoc]
variable (u p)
theorem isFnAt_zero (k : ℤ) : IsFnAt u p k (H1.SectionArithmetic.secZero (LPow A L k T)) 0 := fun j z hj => by
  rw [Pi.zero_apply, zero_mul, valAt'_eq_valHom _ hj]
  exact map_zero _
def fnAtHom (hL : L.IsLB) (k : ℤ) :
    SecM A L k T →ₛₗ[valHom p.left ⊤ (fun _ _ => trivial)] ((Fin g → ℂ) → ℂ) where
  toFun s := fnAt u p hL k (SecM.toSec A s)
  map_add' s s' := ((isFnAt_iff_eq_fnAt u p hL).1
    ((isFnAt_fnAt u p hL k (SecM.toSec A s)).add (isFnAt_fnAt u p hL k (SecM.toSec A s'))
      (t := SecM.toSec A (s + s')) fun _ => rfl)).symm
  map_smul' r s := by
    refine Eq.trans ((isFnAt_iff_eq_fnAt u p hL).1
      ((isFnAt_fnAt u p hL k (SecM.toSec A s)).liftFun_mul r
        (t := SecM.toSec A (r • s)) fun _ => rfl)).symm ?_
    exact congrArg (· • fnAt u p hL k (SecM.toSec A s)) (valAt'_eq_valHom p.left _ r)
variable (A L) in

def secOfFun (r : Γ(T.left, ⊤)) : LB.Sec (LPow A L 0 T) where
  f j := liftFun A _ r
  compat j j' := by
    have : (LPow A L 0 T).g j j' = 1 := by
      unfold LPow LB.LinComb
      dsimp only
      exact Finset.prod_eq_one fun _ _ => zpow_zero _
    rw [this, Units.val_one, _root_.one_mul]
    exact (res_liftHom A _ r).trans (res_liftHom A _ r).symm
theorem isFnAt_secOfFun (r : Γ(T.left, ⊤)) :
    IsFnAt u p 0 (secOfFun A L r) (fun _ => valAt' p.left ⊤ r) := fun j z hj => by
  rw [zpow_zero, _root_.mul_one]
  exact valAt'_liftFun u p hj r
variable (L) in

def toFibre (n : ℕ) (s : LB.Sec (LPow A L n T)) : (lbPow L n).Sec :=
  pullPow L (K := Fin 1) (K' := PUnit) (fibreIncl A p).left (fibreIncl_snd p) n s
variable (A L T) in

def ofFibre (n : ℕ) (s : (lbPow L n).Sec) : LB.Sec (LPow A L n T) :=
  pullPow L (K := PUnit) (K' := Fin 1) (snd T A).left (Category.comp_id _) n s
omit [GrpObj A] in

theorem toFibre_ofFibre (n : ℕ) (s : (lbPow L n).Sec) : toFibre L p n (ofFibre A L T n s) = s :=
  pullPow_pullPow L _ _ _ _ (fibreIncl_snd p) _ s
omit [GrpObj A] in

theorem ofFibre_toFibre [IsIso p] (n : ℕ) (s : LB.Sec (LPow A L n T)) :
    ofFibre A L T n (toFibre L p n s) = s :=
  pullPow_pullPow L _ _ _ _ (snd_fibreIncl p) _ s
variable (L) in

def fibreEquiv [IsIso p] (n : ℕ) : LB.Sec (LPow A L n T) ≃ (lbPow L n).Sec where
  toFun := toFibre L p n
  invFun := ofFibre A L T n
  left_inv := ofFibre_toFibre p n
  right_inv := toFibre_ofFibre p n
variable {u p}
end Fibre
section Base
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
def basePt : 𝟙_ (Over (Sp ℂ)) ⟶ baseOver (Sp ℂ) := Over.homMk (𝟙 (Sp ℂ)) (Category.id_comp _)
instance isIso_basePt : IsIso basePt := inferInstanceAs (IsIso (𝟙 (𝟙_ (Over (Sp ℂ)))))
abbrev exT (z : Fin g → ℂ) : Sp ℂ ⟶ (baseOver (Sp ℂ) ⊗ A).left := exAt u basePt z
abbrev IsFnT (k : ℤ) (s : LB.Sec (LPow A L k (baseOver (Sp ℂ)))) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  IsFnAt u basePt k s θ
abbrev exUnit (z : Fin g → ℂ) : Sp ℂ ⟶ (𝟙_ (Over (Sp ℂ)) ⊗ A).left := exAt u (𝟙 _) z
abbrev IsFnUnit (k : ℤ) (s : LB.Sec (LPow A L k (𝟙_ (Over (Sp ℂ))))) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  IsFnAt u (𝟙 _) k s θ
abbrev constT (a : ℂ) : Γ((baseOver (Sp ℂ)).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a
abbrev numT (r : Γ((baseOver (Sp ℂ)).left, ⊤)) : ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom r
theorem numT_constT (a : ℂ) : numT (constT a) = a :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply a
theorem valAt'_basePt (r : Γ((baseOver (Sp ℂ)).left, ⊤)) : valAt' basePt.left ⊤ r = numT r :=
  valAt'_id_top r
variable {u}
variable (u)
theorem isFnT_zero (k : ℤ) :
    IsFnT u k (H1.SectionArithmetic.secZero (LPow A L k (baseOver (Sp ℂ)))) 0 := isFnAt_zero u basePt k
theorem isFnT_const (a : ℂ) : IsFnT u 0 (secOfFun A L (constT a)) (fun _ => a) := by
  have h := isFnAt_secOfFun u basePt (constT a)
  rwa [valAt'_basePt, numT_constT] at h
end Base
def zeroUnif : HolUnif (Inh.zeroPolAV (Sp ℂ)).A (Inh.zeroPolAV (Sp ℂ)).L 0 where
  ex _ := 1
  ex_add _ _ := (_root_.mul_one _).symm
  ex_onto x := ⟨0, toUnit_unique _ _⟩
  Λ := ⊤
  ker _ := ⟨fun _ => trivial, fun _ => rfl⟩
  discrete := inferInstance
  full := by simp
  hol _ _ := ⟨isOpen_discrete _, differentiableOn_const _⟩
  fr _ _ := 1
  fr_hol _ := differentiableOn_const _
  fr_ne _ _ _ := one_ne_zero
  fr_compat _ _ _ h := by
    rw [valAt'_eq_valHom _ h, _root_.mul_one]
    exact (map_one _).symm
example (P : PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (a b : ℂ) :
    IsFnT u 0 (secOfFun P.A P.L (constT a)) (fun _ => b) ↔ a = b :=
  ⟨fun h => congrFun ((isFnT_const u a).unique P.isLB h) 0, fun h => h ▸ isFnT_const u a⟩
example (P : PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (k : ℤ) (θ : (Fin P.g → ℂ) → ℂ) :
    IsFnT u k (H1.SectionArithmetic.secZero (LPow P.A P.L k (baseOver (Sp ℂ)))) θ ↔ θ = 0 :=
  ⟨fun h => h.unique P.isLB (isFnT_zero u k), fun h => h ▸ isFnT_zero u k⟩
example : IsFnT zeroUnif 0 (secOfFun _ _ (constT 2)) (fun _ => 2) ∧
    ¬ IsFnT zeroUnif 0 (secOfFun _ _ (constT 2)) (fun _ => 3) :=
  ⟨isFnT_const _ 2, fun h => by
    have := congrFun ((isFnT_const zeroUnif 2).unique (Inh.zeroPolAV (Sp ℂ)).isLB h) 0
    norm_num at this⟩
end GlobalTheory.ThetaFn


