-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.one_cup_and_cup_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/388fe766-5fca-540a-aa45-7bd91096166f

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_one_cup_and_cup_one

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_one_cup_and_cup_one.AlgebraicGeometry"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme Scheme.OrderedAffineCover OModulePresheaf OModulePresheaf.unit Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom"
p2m_open "AlgebraicGeometry"

namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Γ Opens OrderedAffineCover TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom"
namespace OrderedAffineCover
p2m_export "AlgebraicGeometry.Scheme.OrderedAffineCover" "Idx inter face inter_le_inter_face U frontFace backFace frontFace_apply backFace_apply inter_le_inter_frontFace inter_le_inter_backFace"
p2m_open "AlgebraicGeometry.Scheme.OrderedAffineCover AlgebraicGeometry.Scheme"

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

theorem Idx.ext' {i : ℕ} {t t' : K.Idx i} (h : ∀ m : Fin (i + 1), t.1 m = t'.1 m) : t = t' :=
  Subtype.ext (funext h)

theorem face_apply {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) (m : Fin (i + 1)) :
    (K.face s j).1 m = s.1 (j.succAbove m) := rfl

private theorem _root_.Fin.val_succAbove_ite {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    ((p.succAbove i : Fin (n + 1)) : ℕ) = if (i : ℕ) < p then (i : ℕ) else (i : ℕ) + 1 := by
  by_cases hlt : (i : ℕ) < p
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.2 (by simpa using hlt)), if_pos hlt, Fin.val_castSucc]
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.2 (by simpa using not_lt.1 hlt)), if_neg hlt,
      Fin.val_succ]

p2m_alias "P2MW.S_AlgebraicGeometry_OModulePresheaf_one_cup_and_cup_one.Fin.val_succAbove_ite" "Fin.val_succAbove_ite"
theorem frontFace_frontFace (a b c ab bc n : ℕ) (hab : a + b = ab) (hbc : b + c = bc) (h₁ : ab + c = n)
    (h₂ : a + bc = n) (s : K.Idx n) :
    K.frontFace a b ab hab (K.frontFace ab c n h₁ s) = K.frontFace a bc n h₂ s := rfl

theorem backFace_frontFace (a b c ab bc n : ℕ) (hab : a + b = ab) (hbc : b + c = bc) (h₁ : ab + c = n)
    (h₂ : a + bc = n) (s : K.Idx n) :
    K.backFace a b ab hab (K.frontFace ab c n h₁ s) = K.frontFace b c bc hbc (K.backFace a bc n h₂ s) := rfl

private theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.backFace_backFace (a b c ab bc n : ℕ) (hab : a + b = ab) (hbc : b + c = bc) (h₁ : ab + c = n)
    (h₂ : a + bc = n) (s : K.Idx n) :
    K.backFace b c bc hbc (K.backFace a bc n h₂ s) = K.backFace ab c n h₁ s := by
  apply Idx.ext'; intro m
  simp only [backFace_apply]
  refine congrArg s.1 (Fin.ext ?_); simp only [Fin.val_mk]; omega

p2m_export "AlgebraicGeometry.Scheme.OrderedAffineCover" "backFace_backFace"
theorem frontFace_self (a : ℕ) (h : a + 0 = a) (s : K.Idx a) : K.frontFace a 0 a h s = s := rfl

private theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.backFace_self (b : ℕ) (h : 0 + b = b) (s : K.Idx b) : K.backFace 0 b b h s = s := by
  apply Idx.ext'; intro m
  simp only [backFace_apply]
  refine congrArg s.1 (Fin.ext ?_); simp only [Fin.val_mk]; omega

p2m_export "AlgebraicGeometry.Scheme.OrderedAffineCover" "backFace_self"
section Leibniz

variable (a b n : ℕ) (h : a + b = n) (s : K.Idx (n + 1))

private theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.frontFace_face_low (j : Fin (a + 1)) (hj : (j : ℕ) < n + 2) :
    K.frontFace a b n h (K.face s ⟨j, hj⟩)
      = K.face (K.frontFace (a + 1) b (n + 1) (by omega) s) (Fin.castSucc j) := by
  apply Idx.ext'; intro m
  simp only [frontFace_apply, face_apply]
  refine congrArg s.1 (Fin.ext ?_)
  simp only [Fin.val_succAbove_ite, Fin.val_castSucc]

p2m_export "AlgebraicGeometry.Scheme.OrderedAffineCover" "frontFace_face_low"
private theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.backFace_face_low (j : Fin (a + 1)) (hj : (j : ℕ) < n + 2) :
    K.backFace a b n h (K.face s ⟨j, hj⟩) = K.backFace (a + 1) b (n + 1) (by omega) s := by
  apply Idx.ext'; intro m
  simp only [backFace_apply, face_apply]
  refine congrArg s.1 (Fin.ext ?_)
  simp only [Fin.val_succAbove_ite]
  split_ifs <;> omega

p2m_export "AlgebraicGeometry.Scheme.OrderedAffineCover" "backFace_face_low"
private theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.frontFace_face_high (k : Fin (b + 1)) (hk : a + 1 + (k : ℕ) < n + 2) :
    K.frontFace a b n h (K.face s ⟨a + 1 + k, hk⟩) = K.frontFace a (b + 1) (n + 1) (by omega) s := by
  apply Idx.ext'; intro m
  simp only [frontFace_apply, face_apply]
  refine congrArg s.1 (Fin.ext ?_)
  simp only [Fin.val_succAbove_ite]
  split_ifs <;> omega

p2m_export "AlgebraicGeometry.Scheme.OrderedAffineCover" "frontFace_face_high"
private theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.backFace_face_high (k : Fin (b + 1)) (hk : a + 1 + (k : ℕ) < n + 2) :
    K.backFace a b n h (K.face s ⟨a + 1 + k, hk⟩)
      = K.face (K.backFace a (b + 1) (n + 1) (by omega) s) (Fin.succ k) := by
  apply Idx.ext'; intro m
  simp only [backFace_apply, face_apply]
  refine congrArg s.1 (Fin.ext ?_)
  simp only [Fin.val_succAbove_ite, Fin.val_succ]
  split_ifs <;> omega

p2m_export "AlgebraicGeometry.Scheme.OrderedAffineCover" "backFace_face_high"
private theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.frontFace_eq_face_last :
    K.frontFace a (b + 1) (n + 1) (by omega) s
      = K.face (K.frontFace (a + 1) b (n + 1) (by omega) s) (Fin.last (a + 1)) := by
  apply Idx.ext'; intro m
  simp only [frontFace_apply, face_apply, Fin.succAbove_last]
  rfl

p2m_export "AlgebraicGeometry.Scheme.OrderedAffineCover" "frontFace_eq_face_last"
private theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.backFace_eq_face_zero :
    K.backFace (a + 1) b (n + 1) (by omega) s
      = K.face (K.backFace a (b + 1) (n + 1) (by omega) s) 0 := by
  apply Idx.ext'; intro m
  simp only [backFace_apply, face_apply, Fin.succAbove_zero]
  refine congrArg s.1 (Fin.ext ?_)
  simp only [Fin.val_succ]
  omega

p2m_export "AlgebraicGeometry.Scheme.OrderedAffineCover" "backFace_eq_face_zero"
end Leibniz

end Scheme.OrderedAffineCover

namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "res_refl_apply res_res cochain d d_apply unit res res_smul obj cup"
p2m_open "AlgebraicGeometry.OModulePresheaf"

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

def urest {i : ℕ} (α : (unit π).cochain K i) (t : K.Idx i) {U : V.Opens} (h : U ≤ K.inter t) : Γ(V, U) :=
  (V.presheaf.map (homOfLE h).op).hom (α t)

private def _root_.AlgebraicGeometry.OModulePresheaf.rest {i : ℕ} (c : F.cochain K i) (t : K.Idx i) {U : V.Opens} (h : U ≤ K.inter t) : F.obj U :=
  F.res h (c t)

p2m_export "AlgebraicGeometry.OModulePresheaf" "rest"
omit F in
theorem urest_congr {i : ℕ} (α : (unit π).cochain K i) {t t' : K.Idx i} (e : t = t') {U : V.Opens}
    (h : U ≤ K.inter t) (h' : U ≤ K.inter t') : urest K α t h = urest K α t' h' := by
  subst e; rfl

private theorem _root_.AlgebraicGeometry.OModulePresheaf.rest_congr {i : ℕ} (c : F.cochain K i) {t t' : K.Idx i} (e : t = t') {U : V.Opens}
    (h : U ≤ K.inter t) (h' : U ≤ K.inter t') : F.rest K c t h = F.rest K c t' h' := by
  subst e; rfl

p2m_export "AlgebraicGeometry.OModulePresheaf" "rest_congr"
omit F in
theorem urest_self {i : ℕ} (α : (unit π).cochain K i) (t : K.Idx i) (h : K.inter t ≤ K.inter t) :
    urest K α t h = α t :=
  (unit π).res_refl_apply (K.inter t) (α t)

theorem rest_self {i : ℕ} (c : F.cochain K i) (t : K.Idx i) (h : K.inter t ≤ K.inter t) :
    F.rest K c t h = c t :=
  F.res_refl_apply (K.inter t) (c t)

omit F in
theorem map_urest {i : ℕ} (α : (unit π).cochain K i) (t : K.Idx i) {U U' : V.Opens} (h : U' ≤ K.inter t)
    (h' : U ≤ U') : (V.presheaf.map (homOfLE h').op).hom (urest K α t h) = urest K α t (h'.trans h) :=
  (unit π).res_res h' h (α t)

private theorem _root_.AlgebraicGeometry.OModulePresheaf.res_rest {i : ℕ} (c : F.cochain K i) (t : K.Idx i) {U U' : V.Opens} (h : U' ≤ K.inter t)
    (h' : U ≤ U') : F.res h' (F.rest K c t h) = F.rest K c t (h'.trans h) :=
  F.res_res h' h (c t)

p2m_export "AlgebraicGeometry.OModulePresheaf" "res_rest"
omit F in
theorem unit_rest_eq_urest {i : ℕ} (α : (unit π).cochain K i) (t : K.Idx i) {U : V.Opens} (h : U ≤ K.inter t) :
    (unit π).rest K α t h = urest K α t h := rfl

theorem res_urest_smul {U U' : V.Opens} (h' : U ≤ U') (x : Γ(V, U')) (m : F.obj U') :
    F.res h' (x • m) = (V.presheaf.map (homOfLE h').op).hom x • F.res h' m :=
  F.res_smul h' x m

theorem cup_apply_rest (a b n : ℕ) (h : a + b = n) (α : (unit π).cochain K a) (β : F.cochain K b)
    (s : K.Idx n) :
    F.cup K a b n h α β s
      = urest K α (K.frontFace a b n h s) (K.inter_le_inter_frontFace a b n h s)
          • F.rest K β (K.backFace a b n h s) (K.inter_le_inter_backFace a b n h s) := rfl

private theorem _root_.AlgebraicGeometry.OModulePresheaf.rest_cup (a b n : ℕ) (h : a + b = n) (α : (unit π).cochain K a) (β : F.cochain K b)
    (t : K.Idx n) {U : V.Opens} (h' : U ≤ K.inter t) :
    F.rest K (F.cup K a b n h α β) t h'
      = urest K α (K.frontFace a b n h t) (h'.trans (K.inter_le_inter_frontFace a b n h t))
          • F.rest K β (K.backFace a b n h t) (h'.trans (K.inter_le_inter_backFace a b n h t)) := by
  show F.res h' (F.cup K a b n h α β t) = _
  rw [cup_apply_rest, res_urest_smul, map_urest, res_rest]

p2m_export "AlgebraicGeometry.OModulePresheaf" "rest_cup"
private theorem _root_.AlgebraicGeometry.OModulePresheaf.rest_d {i : ℕ} (c : F.cochain K i) (t : K.Idx (i + 1)) {U : V.Opens} (h' : U ≤ K.inter t) :
    F.rest K (F.d K i c) t h'
      = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) • F.rest K c (K.face t j) (h'.trans (K.inter_le_inter_face t j)) := by
  show F.res h' (F.d K i c t) = _
  rw [d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]; exact congrArg _ (F.res_rest K c _ _ h')

p2m_export "AlgebraicGeometry.OModulePresheaf" "rest_d"
omit F in
theorem urest_d {i : ℕ} (α : (unit π).cochain K i) (t : K.Idx (i + 1)) {U : V.Opens} (h' : U ≤ K.inter t) :
    urest K ((unit π).d K i α) t h'
      = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) • urest K α (K.face t j) (h'.trans (K.inter_le_inter_face t j)) :=
  (unit π).rest_d K α t h'

omit F in
theorem urest_one (t : K.Idx 0) {U : V.Opens} (h : U ≤ K.inter t) :
    urest (π := π) K (fun s => (1 : Γ(V, K.inter s))) t h = 1 :=
  map_one (V.presheaf.map (homOfLE h).op).hom

omit F in
theorem urest_add {i : ℕ} (α α' : (unit π).cochain K i) (t : K.Idx i) {U : V.Opens} (h : U ≤ K.inter t) :
    urest K (α + α') t h = urest K α t h + urest K α' t h :=
  map_add (V.presheaf.map (homOfLE h).op).hom (α t) (α' t)

theorem rest_add {i : ℕ} (c c' : F.cochain K i) (t : K.Idx i) {U : V.Opens} (h : U ≤ K.inter t) :
    F.rest K (c + c') t h = F.rest K c t h + F.rest K c' t h :=
  map_add (F.res h) (c t) (c' t)

theorem rest_smul {i : ℕ} (r : R) (c : F.cochain K i) (t : K.Idx i) {U : V.Opens} (h : U ≤ K.inter t) :
    F.rest K (r • c) t h = r • F.rest K c t h :=
  map_smul (F.res h) r (c t)

section Bilinear

variable (a b n : ℕ) (h : a + b = n)

private theorem _root_.AlgebraicGeometry.OModulePresheaf.cup_add_left (α α' : (unit π).cochain K a) (β : F.cochain K b) :
    F.cup K a b n h (α + α') β = F.cup K a b n h α β + F.cup K a b n h α' β := by
  funext s
  simp only [Pi.add_apply, cup_apply_rest, urest_add, add_smul]

p2m_export "AlgebraicGeometry.OModulePresheaf" "cup_add_left"
private theorem _root_.AlgebraicGeometry.OModulePresheaf.cup_add_right (α : (unit π).cochain K a) (β β' : F.cochain K b) :
    F.cup K a b n h α (β + β') = F.cup K a b n h α β + F.cup K a b n h α β' := by
  funext s
  simp only [Pi.add_apply, cup_apply_rest, rest_add, smul_add]

p2m_export "AlgebraicGeometry.OModulePresheaf" "cup_add_right"
private theorem _root_.AlgebraicGeometry.OModulePresheaf.cup_smul_left (r : R) (α : (unit π).cochain K a) (β : F.cochain K b) :
    F.cup K a b n h (r • α) β = r • F.cup K a b n h α β := by
  funext s
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π (K.inter s)
  have e : urest K (r • α) (K.frontFace a b n h s) (K.inter_le_inter_frontFace a b n h s)
      = r • urest K α (K.frontFace a b n h s) (K.inter_le_inter_frontFace a b n h s) :=
    map_smul ((unit π).res (K.inter_le_inter_frontFace a b n h s)) r (α _)
  simp only [Pi.smul_apply, cup_apply_rest]
  rw [e, smul_assoc]

p2m_export "AlgebraicGeometry.OModulePresheaf" "cup_smul_left"
private theorem _root_.AlgebraicGeometry.OModulePresheaf.cup_smul_right (r : R) (α : (unit π).cochain K a) (β : F.cochain K b) :
    F.cup K a b n h α (r • β) = r • F.cup K a b n h α β := by
  funext s
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π (K.inter s)
  simp only [Pi.smul_apply, cup_apply_rest, rest_smul]
  exact smul_algebra_smul_comm r _ _

p2m_export "AlgebraicGeometry.OModulePresheaf" "cup_smul_right"

private def _root_.AlgebraicGeometry.OModulePresheaf.cupₗ : (unit π).cochain K a →ₗ[R] F.cochain K b →ₗ[R] F.cochain K n :=
  LinearMap.mk₂ R (F.cup K a b n h) (F.cup_add_left K a b n h) (F.cup_smul_left K a b n h)
    (F.cup_add_right K a b n h) (F.cup_smul_right K a b n h)

p2m_export "AlgebraicGeometry.OModulePresheaf" "cupₗ"
theorem cupₗ_apply (α : (unit π).cochain K a) (β : F.cochain K b) : F.cupₗ K a b n h α β = F.cup K a b n h α β :=
  rfl

theorem cup_zero_left (β : F.cochain K b) : F.cup K a b n h 0 β = 0 := by
  rw [← cupₗ_apply, LinearMap.map_zero₂]

theorem cup_zero_right (α : (unit π).cochain K a) : F.cup K a b n h α 0 = 0 := by
  rw [← cupₗ_apply, map_zero]

theorem cup_zsmul_left (z : ℤ) (α : (unit π).cochain K a) (β : F.cochain K b) :
    F.cup K a b n h (z • α) β = z • F.cup K a b n h α β := by
  simp only [← cupₗ_apply, map_zsmul, LinearMap.smul_apply]

end Bilinear

end OModulePresheaf

namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "res_refl_apply res_res cochain d d_apply unit res res_smul obj cup"
p2m_open "AlgebraicGeometry.OModulePresheaf"

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

omit F in
theorem unit_res_one {U U' : V.Opens} (h : U ≤ U') :
    (unit π).res h (show (unit π).obj U' from (1 : Γ(V, U'))) = (show (unit π).obj U from (1 : Γ(V, U))) :=
  map_one (V.presheaf.map (homOfLE h).op).hom

omit F in
theorem urest_cup (a b n : ℕ) (h : a + b = n) (α : (unit π).cochain K a) (β : (unit π).cochain K b)
    (t : K.Idx n) {U : V.Opens} (h' : U ≤ K.inter t) :
    urest K ((unit π).cup K a b n h α β) t h'
      = urest K α (K.frontFace a b n h t) (h'.trans (K.inter_le_inter_frontFace a b n h t))
          * urest K β (K.backFace a b n h t) (h'.trans (K.inter_le_inter_backFace a b n h t)) :=
  (unit π).rest_cup K a b n h α β t h'

private theorem _root_.AlgebraicGeometry.OModulePresheaf.one_cup (b : ℕ) (h : 0 + b = b) (β : F.cochain K b) :
    F.cup K 0 b b h (fun s => (1 : Γ(V, K.inter s))) β = β := by
  funext s
  rw [cup_apply_rest, urest_one, one_smul, F.rest_congr K β (K.backFace_self b h s) _ le_rfl, rest_self]

p2m_export "AlgebraicGeometry.OModulePresheaf" "one_cup"
omit F in
theorem cup_one (a : ℕ) (h : a + 0 = a) (α : (unit π).cochain K a) :
    (unit π).cup K a 0 a h α (fun s => (1 : Γ(V, K.inter s))) = α := by
  funext s
  rw [cup_apply_rest, unit_rest_eq_urest, urest_one]
  show urest K α (K.frontFace a 0 a h s) (K.inter_le_inter_frontFace a 0 a h s) * 1 = α s
  rw [mul_one]
  exact urest_self K α s _

omit F in
theorem d_unitOne : (unit π).d K 0 (fun s => (1 : Γ(V, K.inter s))) = 0 := by
  funext s
  have e : ∀ j : Fin 2, (unit π).res (K.inter_le_inter_face s j)
      ((fun s' : K.Idx 0 => (1 : Γ(V, K.inter s'))) (K.face s j))
        = (show (unit π).obj (K.inter s) from (1 : Γ(V, K.inter s))) :=
    fun j => urest_one (π := π) K (K.face s j) _
  rw [d_apply, Fin.sum_univ_two, e, e, Pi.zero_apply]
  simp

private theorem _root_.AlgebraicGeometry.OModulePresheaf.one_cup_and_cup_one' :
    (∀ (b : ℕ) (β : F.cochain K b),
        F.cup K 0 b b (Nat.zero_add b) (fun s => (1 : Γ(V, K.inter s))) β = β) ∧
      (∀ (a : ℕ) (α : (unit π).cochain K a),
        (unit π).cup K a 0 a (Nat.add_zero a) α (fun s => (1 : Γ(V, K.inter s))) = α) :=
  ⟨fun b β => F.one_cup K b _ β, fun a α => cup_one K a _ α⟩

p2m_export "AlgebraicGeometry.OModulePresheaf" "one_cup_and_cup_one'"

theorem cup_cup' (a b c nab n : ℕ) (hab : a + b = nab) (hn : nab + c = n)
    (α : (unit π).cochain K a) (β : (unit π).cochain K b) (γ : F.cochain K c) :
    F.cup K nab c n hn ((unit π).cup K a b nab hab α β) γ =
      F.cup K a (b + c) n (by omega) α (F.cup K b c (b + c) rfl β γ) := by
  funext s
  rw [cup_apply_rest, cup_apply_rest, urest_cup, F.rest_cup K b c (b + c) rfl β γ, mul_smul,
    F.rest_congr K γ (K.backFace_backFace a b c nab (b + c) n hab rfl hn (by omega) s).symm _
      ((K.inter_le_inter_backFace a (b + c) n (by omega) s).trans
        (K.inter_le_inter_backFace b c (b + c) rfl _))]
  rfl

omit F K in
private theorem zsmul_smul_zsmul {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (z z' : ℤ) (x : A) (m : M) : z • (x • (z' • m)) = (z * z') • (x • m) := by
  rw [smul_comm x z' m, smul_smul]

omit F K in
private theorem _root_.Fin.sum_univ_split_low_high {M : Type*} [AddCommMonoid M] (a b n : ℕ)
    (e : (a + 1) + (b + 1) = n + 2) (f : Fin (n + 2) → M) :
    ∑ j, f j = ∑ j : Fin (a + 1), f ⟨j, by omega⟩ + ∑ k : Fin (b + 1), f ⟨a + 1 + k, by omega⟩ := by
  rw [← Equiv.sum_comp (finCongr e), Fin.sum_univ_add]
  rfl

p2m_alias "P2MW.S_AlgebraicGeometry_OModulePresheaf_one_cup_and_cup_one.Fin.sum_univ_split_low_high" "Fin.sum_univ_split_low_high"
theorem d_cup' (a b n : ℕ) (h : a + b = n) (α : (unit π).cochain K a) (β : F.cochain K b) :
    F.d K n (F.cup K a b n h α β) =
      F.cup K (a + 1) b (n + 1) (by omega) ((unit π).d K a α) β +
        ((-1 : ℤ) ^ a) • F.cup K a (b + 1) (n + 1) (by omega) α (F.d K b β) := by
  funext s
  have h1 : a + 1 + b = n + 1 := by omega
  have h2 : a + (b + 1) = n + 1 := by omega
  have PA : ∀ j : Fin (a + 2), K.inter s ≤ K.inter (K.face (K.frontFace (a + 1) b (n + 1) h1 s) j) :=
    fun j => (K.inter_le_inter_frontFace (a + 1) b (n + 1) h1 s).trans (K.inter_le_inter_face _ j)
  have QA : K.inter s ≤ K.inter (K.backFace (a + 1) b (n + 1) h1 s) := K.inter_le_inter_backFace _ _ _ h1 s
  have QB : K.inter s ≤ K.inter (K.frontFace a (b + 1) (n + 1) h2 s) := K.inter_le_inter_frontFace _ _ _ h2 s
  have PB : ∀ k : Fin (b + 2), K.inter s ≤ K.inter (K.face (K.backFace a (b + 1) (n + 1) h2 s) k) :=
    fun k => (K.inter_le_inter_backFace a (b + 1) (n + 1) h2 s).trans (K.inter_le_inter_face _ k)

  have hL : F.d K n (F.cup K a b n h α β) s
      = ∑ j : Fin (a + 1), ((-1 : ℤ) ^ (j : ℕ)) •
            (urest K α (K.face (K.frontFace (a + 1) b (n + 1) h1 s) (Fin.castSucc j)) (PA _)
              • F.rest K β (K.backFace (a + 1) b (n + 1) h1 s) QA)
        + ∑ k : Fin (b + 1), ((-1 : ℤ) ^ (a + 1 + (k : ℕ))) •
            (urest K α (K.frontFace a (b + 1) (n + 1) h2 s) QB
              • F.rest K β (K.face (K.backFace a (b + 1) (n + 1) h2 s) k.succ) (PB _)) := by
    rw [d_apply, Fin.sum_univ_split_low_high a b n (by omega)]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only
      rw [show F.res (K.inter_le_inter_face s ⟨j, by omega⟩) (F.cup K a b n h α β (K.face s ⟨j, by omega⟩)) = _
        from F.rest_cup K a b n h α β (K.face s ⟨j, by omega⟩) (K.inter_le_inter_face s _),
        urest_congr K α (K.frontFace_face_low a b n h s j (by omega)) _ (PA _),
        F.rest_congr K β (K.backFace_face_low a b n h s j (by omega)) _ QA]
    · refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only
      rw [show F.res (K.inter_le_inter_face s ⟨a + 1 + k, by omega⟩)
            (F.cup K a b n h α β (K.face s ⟨a + 1 + k, by omega⟩)) = _
        from F.rest_cup K a b n h α β (K.face s ⟨a + 1 + k, by omega⟩) (K.inter_le_inter_face s _),
        urest_congr K α (K.frontFace_face_high a b n h s k (by omega)) _ QB,
        F.rest_congr K β (K.backFace_face_high a b n h s k (by omega)) _ (PB _)]

  have hR1 : F.cup K (a + 1) b (n + 1) h1 ((unit π).d K a α) β s
      = ∑ j : Fin (a + 1), ((-1 : ℤ) ^ (j : ℕ)) •
            (urest K α (K.face (K.frontFace (a + 1) b (n + 1) h1 s) (Fin.castSucc j)) (PA _)
              • F.rest K β (K.backFace (a + 1) b (n + 1) h1 s) QA)
        + ((-1 : ℤ) ^ (a + 1)) •
            (urest K α (K.face (K.frontFace (a + 1) b (n + 1) h1 s) (Fin.last (a + 1))) (PA _)
              • F.rest K β (K.backFace (a + 1) b (n + 1) h1 s) QA) := by
    rw [cup_apply_rest, urest_d, Finset.sum_smul, Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.val_castSucc, smul_assoc]
    · rw [Fin.val_last, smul_assoc]

  have hR2 : ((-1 : ℤ) ^ a) • F.cup K a (b + 1) (n + 1) h2 α (F.d K b β) s
      = ((-1 : ℤ) ^ a) •
            (urest K α (K.frontFace a (b + 1) (n + 1) h2 s) QB
              • F.rest K β (K.face (K.backFace a (b + 1) (n + 1) h2 s) 0) (PB _))
        + ∑ k : Fin (b + 1), ((-1 : ℤ) ^ (a + 1 + (k : ℕ))) •
            (urest K α (K.frontFace a (b + 1) (n + 1) h2 s) QB
              • F.rest K β (K.face (K.backFace a (b + 1) (n + 1) h2 s) k.succ) (PB _)) := by
    rw [cup_apply_rest, rest_d, Finset.smul_sum, Fin.sum_univ_succ, smul_add, Finset.smul_sum]
    congr 1
    · rw [Fin.val_zero, pow_zero, one_smul]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [zsmul_smul_zsmul, ← pow_add, Fin.val_succ, show a + ((k : ℕ) + 1) = a + 1 + k by omega]

  have hcancel : ((-1 : ℤ) ^ (a + 1)) •
            (urest K α (K.face (K.frontFace (a + 1) b (n + 1) h1 s) (Fin.last (a + 1))) (PA _)
              • F.rest K β (K.backFace (a + 1) b (n + 1) h1 s) QA)
      + ((-1 : ℤ) ^ a) •
            (urest K α (K.frontFace a (b + 1) (n + 1) h2 s) QB
              • F.rest K β (K.face (K.backFace a (b + 1) (n + 1) h2 s) 0) (PB _)) = 0 := by
    rw [urest_congr K α (K.frontFace_eq_face_last a b n h s).symm (PA _) QB,
      F.rest_congr K β (K.backFace_eq_face_zero a b n h s) QA (PB _),
      pow_succ, mul_neg_one, neg_smul, neg_add_cancel]
  have key : ∀ x y l f : F.obj (K.inter s), l + f = 0 → x + y = (x + l) + (f + y) := by
    intro x y l f hlf
    rw [add_assoc, ← add_assoc l, hlf, zero_add]
  rw [Pi.add_apply, Pi.smul_apply, hL, hR1, hR2]
  exact key _ _ _ _ hcancel

end OModulePresheaf

end AlgebraicGeometry

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_one_cup_and_cup_one.AlgebraicGeometry"

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π)
    (𝒦 : V.OrderedAffineCover) :
    (∀ (b : ℕ) (β : F.cochain 𝒦 b),
        F.cup 𝒦 0 b b (Nat.zero_add b) (fun s => (1 : Γ(V, 𝒦.inter s))) β = β) ∧
      (∀ (a : ℕ) (α : (OModulePresheaf.unit π).cochain 𝒦 a),
        (OModulePresheaf.unit π).cup 𝒦 a 0 a (Nat.add_zero a) α (fun s => (1 : Γ(V, 𝒦.inter s))) = α) := by
  exact F.one_cup_and_cup_one' 𝒦

end
end S_AlgebraicGeometry_OModulePresheaf_one_cup_and_cup_one
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_one_cup_and_cup_one (solution)
