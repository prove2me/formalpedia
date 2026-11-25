-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitObj
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitObj
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:08:44.840464+00:00
-- url     : https://prove2.me/theorems/e57943a0-e906-5205-9f1e-c5b3e198bd68
-- title:
--   Twist Split Obj
-- statement:
--   Definitions and structural lemmas for Twist Split Obj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitObj.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Pointwise AddMonoidAlgebra
noncomputable section
universe u w
abbrev LaurUT (Ω : Type w) [Field Ω] : Type w := AddMonoidAlgebra Ω (ℤ × ℤ)
abbrev tDeg (Ω : Type w) [Field Ω] (a : ℤ) : Submodule Ω (LaurUT Ω) :=
  gradeBy Ω (AddMonoidHom.snd ℤ ℤ) a
theorem single_mem_tDeg {Ω : Type w} [Field Ω] (k : ℤ × ℤ) (z : Ω) : single k z ∈ tDeg Ω k.2 :=
  single_mem_gradeBy (R := Ω) (AddMonoidHom.snd ℤ ℤ) k z
theorem coeff_single_mul_sub {Ω : Type w} [Field Ω] (g : ℤ × ℤ) (c : Ω) (v : LaurUT Ω) (k : ℤ × ℤ) :
    (single g c * v).coeff k = c * v.coeff (k - g) := by
  rw [coeff_single_mul_apply, neg_add_eq_sub]
section Obj
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω) {r : ℕ} (η : Fin (r + 1) → Ω)
variable (S) in

def yHom : MvPolynomial (Fin (r + 1)) S →ₐ[S] LaurUT Ω :=
  aeval fun j => single ((1, 0) : ℤ × ℤ) (η j)
variable (S) in

def xyHom : Poly (MvPolynomial (Fin (r + 1)) S) N →+* LaurUT Ω :=
  eval₂Hom (yHom S η).toRingHom fun i => single ((0, 1) : ℤ × ℤ) (x i)
theorem xyHom_X (i : Fin (N + 1)) : xyHom S x η (X i) = single ((0, 1) : ℤ × ℤ) (x i) := by
  simp [xyHom]
theorem xyHom_C (c : MvPolynomial (Fin (r + 1)) S) : xyHom S x η (C c) = yHom S η c := by
  simp [xyHom]
theorem yHom_C (c : S) : yHom S η (C c) = single (0 : ℤ × ℤ) (algebraMap S Ω c) := by
  rw [yHom, aeval_C, coe_algebraMap]; rfl
theorem yHom_X (j : Fin (r + 1)) : yHom S η (X j) = single ((1, 0) : ℤ × ℤ) (η j) := by
  simp [yHom]
theorem yHom_mem_tDeg (c : MvPolynomial (Fin (r + 1)) S) : yHom S η c ∈ tDeg Ω 0 := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    rw [yHom_C]
    exact single_mem_tDeg (0 : ℤ × ℤ) _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul, yHom_X]
    have h2 : single ((1, 0) : ℤ × ℤ) (η j) ∈ tDeg Ω 0 := single_mem_tDeg ((1, 0) : ℤ × ℤ) _
    have := SetLike.GradedMul.mul_mem hp h2
    rwa [add_zero] at this
theorem xyHom_mem_tDeg {p : Poly (MvPolynomial (Fin (r + 1)) S) N} {d : ℕ} (hp : p.IsHomogeneous d) :
    xyHom S x η p ∈ tDeg Ω d := by
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hdeg := hp (mem_support_iff.mp hα)
  rw [xyHom, coe_eval₂Hom, eval₂_monomial]
  have h1 : (yHom S η).toRingHom (coeff α p) ∈ tDeg Ω 0 := yHom_mem_tDeg η _
  have h2 : (α.prod fun i k => single ((0, 1) : ℤ × ℤ) (x i) ^ k) ∈
      tDeg Ω (∑ i ∈ α.support, α i • (1 : ℤ)) := by
    rw [Finsupp.prod]
    exact SetLike.prod_mem_graded (tDeg Ω) (fun i => α i • (1 : ℤ)) _
      fun i _ => SetLike.pow_mem_graded _ (single_mem_tDeg ((0, 1) : ℤ × ℤ) (x i))
  have h3 : (∑ i ∈ α.support, α i • (1 : ℤ)) = d := by
    rw [← hdeg]
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [h3] at h2
  have := SetLike.GradedMul.mul_mem h1 h2
  rwa [zero_add] at this
theorem xyHom_map_C {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    xyHom S x η (MvPolynomial.map (C : S →+* MvPolynomial (Fin (r + 1)) S) f) = single ((0 : ℤ), (e : ℤ)) (aeval x f) := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum]
  rw [show single ((0 : ℤ), (e : ℤ)) (∑ α ∈ f.support, aeval x (monomial α (coeff α f))) =
      ∑ α ∈ f.support, single ((0 : ℤ), (e : ℤ)) (aeval x (monomial α (coeff α f))) from
    map_sum (singleAddHom ((0 : ℤ), (e : ℤ))) _ _]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hdeg := hf (mem_support_iff.mp hα)
  rw [map_monomial, xyHom, coe_eval₂Hom, eval₂_monomial, aeval_monomial]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, yHom_C, single_pow, finsuppProd_single,
    single_mul_single]
  congr 1
  rw [← hdeg]
  ext <;> simp [Finsupp.weight_apply, Finsupp.sum, Prod.fst_sum, Prod.snd_sum]
theorem exists_yHom_eq {n : ℕ} {q : Ω} (hq : q ∈ Set.range η ^ n) :
    ∃ p : MvPolynomial (Fin (r + 1)) S, yHom S η p = single ((n : ℤ), (0 : ℤ)) q := by
  induction n generalizing q with
  | zero =>
    rw [pow_zero, Set.mem_one] at hq
    subst hq
    exact ⟨1, by rw [map_one, AddMonoidAlgebra.one_def]; rfl⟩
  | succ n ih =>
    rw [pow_succ', Set.mem_mul] at hq
    obtain ⟨_, ⟨j, rfl⟩, q', hq', rfl⟩ := hq
    obtain ⟨p, hp⟩ := ih hq'
    refine ⟨X j * p, ?_⟩
    rw [map_mul, hp, yHom_X, single_mul_single]
    congr 1
    ext <;> simp [add_comm]
variable {x} in

def twPart (M₀ : FinGradedSub (S := S) (x := x) Ω) (a b : ℤ) : Submodule S Ω :=
  if 0 ≤ b then Submodule.span S ((M₀.piece a : Set Ω) * Set.range η ^ b.toNat) else ⊥
variable {x}
theorem twPart_of_nonneg (M₀ : FinGradedSub (S := S) (x := x) Ω) (a : ℤ) (n : ℕ) :
    twPart η M₀ a n = Submodule.span S ((M₀.piece a : Set Ω) * Set.range η ^ n) := by
  rw [twPart, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]
theorem twPart_of_neg (M₀ : FinGradedSub (S := S) (x := x) Ω) (a : ℤ) {b : ℤ} (hb : b < 0) :
    twPart η M₀ a b = ⊥ := by
  rw [twPart, if_neg (not_le.mpr hb)]
theorem twPart_form_mul (M₀ : FinGradedSub (S := S) (x := x) Ω) {a b : ℤ} {f : Poly S N} {d : ℕ}
    (hf : f.IsHomogeneous d) {z : Ω} (hz : z ∈ twPart η M₀ a b) :
    aeval x f * z ∈ twPart η M₀ (a + d) b := by
  unfold twPart at hz ⊢
  split_ifs at hz ⊢ with hb
  · refine Submodule.span_induction (p := fun z _ => aeval x f * z ∈
      Submodule.span S ((M₀.piece (a + d) : Set Ω) * Set.range η ^ b.toNat)) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨m, hm, q, hq, rfl⟩
      rw [← mul_assoc]
      exact Submodule.subset_span (Set.mul_mem_mul (M₀.smul_mem d a f m hf hm) hq)
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
    · intro c u _ hu; rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
  · rw [Submodule.mem_bot] at hz ⊢; rw [hz, mul_zero]
theorem twPart_x_mul (M₀ : FinGradedSub (S := S) (x := x) Ω) {a b : ℤ} (i : Fin (N + 1)) {z : Ω}
    (hz : z ∈ twPart η M₀ a b) : x i * z ∈ twPart η M₀ (a + 1) b := by
  have := twPart_form_mul η M₀ (isHomogeneous_X S i) hz
  rwa [aeval_X, Nat.cast_one] at this
theorem twPart_eta_mul (M₀ : FinGradedSub (S := S) (x := x) Ω) {a b : ℤ} (j : Fin (r + 1)) {z : Ω}
    (hz : z ∈ twPart η M₀ a b) : η j * z ∈ twPart η M₀ a (b + 1) := by
  rcases lt_or_ge b 0 with hb | hb
  · rw [twPart_of_neg η M₀ a hb, Submodule.mem_bot] at hz
    rw [hz, mul_zero]; exact Submodule.zero_mem _
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb
    rw [twPart_of_nonneg] at hz
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; rfl, twPart_of_nonneg]
    refine Submodule.span_induction (p := fun z _ => η j * z ∈
      Submodule.span S ((M₀.piece a : Set Ω) * Set.range η ^ (n + 1))) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨m, hm, q, hq, rfl⟩
      rw [mul_left_comm]
      refine Submodule.subset_span (Set.mul_mem_mul hm ?_)
      rw [pow_succ']
      exact Set.mul_mem_mul (Set.mem_range_self j) hq
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
    · intro c u _ hu; rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
def IsTw (M₀ : FinGradedSub (S := S) (x := x) Ω) (v : LaurUT Ω) : Prop :=
  ∀ k : ℤ × ℤ, v.coeff k ∈ twPart η M₀ k.2 k.1
theorem isTw_zero (M₀ : FinGradedSub (S := S) (x := x) Ω) : IsTw η M₀ 0 := fun k => by
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]; exact Submodule.zero_mem _
theorem isTw_add (M₀ : FinGradedSub (S := S) (x := x) Ω) {u v : LaurUT Ω} (hu : IsTw η M₀ u)
    (hv : IsTw η M₀ v) : IsTw η M₀ (u + v) := fun k => by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply]; exact Submodule.add_mem _ (hu k) (hv k)
theorem isTw_single (M₀ : FinGradedSub (S := S) (x := x) Ω) {k : ℤ × ℤ} {z : Ω}
    (hz : z ∈ twPart η M₀ k.2 k.1) : IsTw η M₀ (single k z) := fun k' => by
  classical
  rw [coeff_single, Finsupp.single_apply]
  split_ifs with h
  · subst h; exact hz
  · exact Submodule.zero_mem _
theorem isTw_xyHom_mul (M₀ : FinGradedSub (S := S) (x := x) Ω)
    (p : Poly (MvPolynomial (Fin (r + 1)) S) N) {v : LaurUT Ω} (hv : IsTw η M₀ v) :
    IsTw η M₀ (xyHom S x η p * v) := by
  induction p using MvPolynomial.induction_on generalizing v with
  | C a =>
    rw [xyHom_C]
    induction a using MvPolynomial.induction_on generalizing v with
    | C c =>
      intro k
      rw [yHom_C, coeff_single_mul_sub, sub_zero]
      have := Submodule.smul_mem _ c (hv k)
      rwa [Algebra.smul_def] at this
    | add p q hp hq => rw [map_add, add_mul]; exact isTw_add η M₀ (hp hv) (hq hv)
    | mul_X p j hp =>
      rw [map_mul, mul_assoc]
      apply hp
      intro k
      rw [yHom_X, coeff_single_mul_sub]
      have := twPart_eta_mul η M₀ j (hv (k - (1, 0)))
      simpa using this
  | add p q hp hq => rw [map_add, add_mul]; exact isTw_add η M₀ (hp hv) (hq hv)
  | mul_X p i hp =>
    rw [map_mul, mul_assoc]
    apply hp
    intro k
    rw [xyHom_X, coeff_single_mul_sub]
    have := twPart_x_mul η M₀ i (hv (k - (0, 1)))
    simpa using this
variable (x) in

def UT (_ : Fin (N + 1) → Ω) (_ : Fin (r + 1) → Ω) : Type w := LaurUT Ω
instance : CommRing (UT x η) := inferInstanceAs (CommRing (LaurUT Ω))
variable {η} in

def UT.toL (v : UT x η) : LaurUT Ω := v
variable {η} in

def UT.ofL (v : LaurUT Ω) : UT x η := v
instance : Algebra (Poly (MvPolynomial (Fin (r + 1)) S) N) (UT x η) :=
  RingHom.toAlgebra (show Poly (MvPolynomial (Fin (r + 1)) S) N →+* UT x η from xyHom S x η)
theorem UT.smul_def (p : Poly (MvPolynomial (Fin (r + 1)) S) N) (v : UT x η) :
    UT.toL (p • v) = xyHom S x η p * UT.toL v := rfl
def twSub (M₀ : FinGradedSub (S := S) (x := x) Ω) :
    Submodule (Poly (MvPolynomial (Fin (r + 1)) S) N) (UT x η) where
  carrier := {v | IsTw η M₀ (UT.toL v)}
  add_mem' hu hv := isTw_add η M₀ hu hv
  zero_mem' := isTw_zero η M₀
  smul_mem' p _ hv := isTw_xyHom_mul η M₀ p hv
abbrev TwM (M₀ : FinGradedSub (S := S) (x := x) Ω) : Type w := ↥(twSub η M₀)
variable {η} in

def TwM.val {M₀ : FinGradedSub (S := S) (x := x) Ω} (m : TwM η M₀) : LaurUT Ω := UT.toL (m : UT x η)
instance (M₀ : FinGradedSub (S := S) (x := x) Ω) : Module (MvPolynomial (Fin (r + 1)) S) (TwM η M₀) :=
  Module.compHom _ (algebraMap (MvPolynomial (Fin (r + 1)) S) (Poly (MvPolynomial (Fin (r + 1)) S) N))
instance (M₀ : FinGradedSub (S := S) (x := x) Ω) :
    IsScalarTower (MvPolynomial (Fin (r + 1)) S) (Poly (MvPolynomial (Fin (r + 1)) S) N) (TwM η M₀) where
  smul_assoc s p m := by
    change (s • p) • m = algebraMap _ (Poly (MvPolynomial (Fin (r + 1)) S) N) s • (p • m)
    rw [Algebra.smul_def, mul_smul]
variable {η} in
theorem TwM.val_add {M₀ : FinGradedSub (S := S) (x := x) Ω} (m m' : TwM η M₀) :
    (m + m').val = m.val + m'.val := rfl
variable {η} in
theorem TwM.val_zero {M₀ : FinGradedSub (S := S) (x := x) Ω} : (0 : TwM η M₀).val = 0 := rfl
variable {η} in
theorem TwM.val_smul {M₀ : FinGradedSub (S := S) (x := x) Ω} (p : Poly (MvPolynomial (Fin (r + 1)) S) N)
    (m : TwM η M₀) : (p • m).val = xyHom S x η p * m.val := rfl
variable {η} in
theorem TwM.val_smul' {M₀ : FinGradedSub (S := S) (x := x) Ω} (c : MvPolynomial (Fin (r + 1)) S)
    (m : TwM η M₀) : (c • m).val = yHom S η c * m.val := by
  change xyHom S x η (C c) * m.val = _
  rw [xyHom_C]
variable {η} in
theorem TwM.isTw {M₀ : FinGradedSub (S := S) (x := x) Ω} (m : TwM η M₀) : IsTw η M₀ m.val := m.2
variable {η} in
theorem TwM.val_injective {M₀ : FinGradedSub (S := S) (x := x) Ω} :
    Function.Injective (TwM.val (η := η) (M₀ := M₀)) := fun _ _ h => Subtype.ext h
variable {η} in

def TwM.mk {M₀ : FinGradedSub (S := S) (x := x) Ω} (v : LaurUT Ω) (hv : IsTw η M₀ v) : TwM η M₀ :=
  ⟨UT.ofL v, hv⟩
def twPiece (M₀ : FinGradedSub (S := S) (x := x) Ω) (a : ℤ) :
    Submodule (MvPolynomial (Fin (r + 1)) S) (TwM η M₀) where
  carrier := TwM.val ⁻¹' (tDeg Ω a : Set (LaurUT Ω))
  add_mem' {m m'} hm hm' := by
    change (m + m').val ∈ tDeg Ω a; rw [TwM.val_add]; exact add_mem hm hm'
  zero_mem' := by change (0 : TwM η M₀).val ∈ tDeg Ω a; rw [TwM.val_zero]; exact zero_mem _
  smul_mem' c m hm := by
    change (c • m).val ∈ tDeg Ω a
    rw [TwM.val_smul']
    simpa using SetLike.GradedMul.mul_mem (yHom_mem_tDeg η c) hm
variable {η} in
theorem mem_twPiece {M₀ : FinGradedSub (S := S) (x := x) Ω} {a : ℤ} {m : TwM η M₀} :
    m ∈ twPiece η M₀ a ↔ ∀ k : ℤ × ℤ, k ∈ m.val.coeff.support → k.2 = a := Iff.rfl
theorem twPiece_isInternal (M₀ : FinGradedSub (S := S) (x := x) Ω) :
    DirectSum.IsInternal (twPiece η M₀) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro a
    rw [Submodule.disjoint_def]
    intro m hm hm'
    have key : ∀ k : ℤ × ℤ, k.2 = a → m.val.coeff k = 0 := by
      refine Submodule.iSup_induction (motive := fun m => ∀ k : ℤ × ℤ, k.2 = a → m.val.coeff k = 0)
        _ hm' ?_ ?_ ?_
      · intro j m' hm'
        by_cases hj : j = a
        · subst hj
          simp only [ne_eq, not_true_eq_false, iSup_false, Submodule.mem_bot] at hm'
          subst hm'
          intro k _; rw [TwM.val_zero]; rfl
        · rw [iSup_pos hj] at hm'
          intro k hk
          by_contra hne
          exact hj (mem_twPiece.mp hm' k (Finsupp.mem_support_iff.mpr hne) ▸ hk)
      · intro k _; rw [TwM.val_zero]; rfl
      · intro m₁ m₂ h₁ h₂ k hk
        rw [TwM.val_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h₁ k hk, h₂ k hk, add_zero]
    apply TwM.val_injective
    rw [TwM.val_zero]
    ext k
    by_cases hk : k.2 = a
    · exact key k hk
    · by_contra hne
      exact hk (mem_twPiece.mp hm k (Finsupp.mem_support_iff.mpr hne))
  · rw [eq_top_iff]
    intro m _
    have hsum : m = ∑ k ∈ m.val.coeff.support,
        TwM.mk (single k (m.val.coeff k)) (isTw_single η M₀ (m.isTw k)) := by
      apply TwM.val_injective
      change m.val = UT.toL ((∑ k ∈ m.val.coeff.support, _ : TwM η M₀) : UT x η)
      rw [Submodule.coe_sum]
      exact (sum_coeff_single m.val).symm
    rw [hsum]
    refine Submodule.sum_mem _ fun k _ => Submodule.mem_iSup_of_mem k.2 ?_
    exact single_mem_gradeBy (R := Ω) (AddMonoidHom.snd ℤ ℤ) k _
def twGraded (M₀ : FinGradedSub (S := S) (x := x) Ω) :
    GradedPMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) where
  piece := twPiece η M₀
  isInternal := twPiece_isInternal η M₀
  smul_mem d c p m hp hm := by
    change (p • m).val ∈ tDeg Ω (c + d)
    rw [TwM.val_smul, add_comm]
    exact SetLike.GradedMul.mul_mem (xyHom_mem_tDeg x η hp) hm
theorem twSub_fg (M₀ : FinGradedSub (S := S) (x := x) Ω) : (twSub η M₀).FG := by
  classical
  obtain ⟨n, deg, gen, hgen, hspan⟩ := M₀.fg
  let g : Fin n → UT x η := fun j => UT.ofL (x := x) (η := η) (single ((0 : ℤ), deg j) (gen j))
  refine ⟨(Finset.univ.image g), le_antisymm ?_ ?_⟩
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine isTw_single η M₀ ?_
    change gen j ∈ twPart η M₀ (deg j) ((0 : ℕ) : ℤ)
    rw [twPart_of_nonneg, pow_zero, mul_one]
    exact Submodule.subset_span (hgen j)
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    set Sp := Submodule.span (Poly (MvPolynomial (Fin (r + 1)) S) N) (Set.range g) with hSp

    have hsingle : ∀ (a : ℤ) (b : ℤ) (z : Ω), z ∈ twPart η M₀ a b →
        UT.ofL (x := x) (η := η) (single (b, a) z) ∈ Sp := by
      intro a b z hz
      rcases lt_or_ge b 0 with hb | hb
      · rw [twPart_of_neg η M₀ a hb, Submodule.mem_bot] at hz
        subst hz
        rw [single_zero]; exact Submodule.zero_mem _
      obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hb
      rw [twPart_of_nonneg] at hz
      refine Submodule.span_induction (p := fun z _ => UT.ofL (x := x) (η := η) (single ((k : ℤ), a) z) ∈ Sp)
        ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨m, hm, q, hq, rfl⟩
        obtain ⟨p, hp⟩ := exists_yHom_eq (S := S) η hq
        refine Submodule.span_induction (p := fun m _ =>
          UT.ofL (x := x) (η := η) (single ((k : ℤ), a) (m * q)) ∈ Sp) ?_ ?_ ?_ ?_ (hspan a hm)
        · rintro _ ⟨j, f, e, hf, he, rfl⟩
          have : UT.ofL (x := x) (η := η) (single ((k : ℤ), a) ((aeval x f • gen j) * q)) =
              (MvPolynomial.map (C : S →+* MvPolynomial (Fin (r + 1)) S) f * C p) • g j := by
            change _ = xyHom S x η (MvPolynomial.map (C : S →+* MvPolynomial (Fin (r + 1)) S) f * C p) *
              single ((0 : ℤ), deg j) (gen j)
            rw [map_mul, xyHom_map_C x η hf, xyHom_C, hp, single_mul_single, single_mul_single,
              smul_eq_mul]
            have hidx : ((0 : ℤ), (e : ℤ)) + ((k : ℤ), 0) + (0, deg j) = ((k : ℤ), a) := by
              ext <;> simp [← he]
            rw [hidx, mul_right_comm]
            rfl
          rw [this]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
        · rw [zero_mul, single_zero]; exact Submodule.zero_mem _
        · intro u v _ _ hu hv; rw [add_mul, single_add]; exact Submodule.add_mem _ hu hv
        · intro c u _ hu
          have : UT.ofL (x := x) (η := η) (single ((k : ℤ), a) ((c • u) * q)) =
              (C (C c) : Poly (MvPolynomial (Fin (r + 1)) S) N) •
                UT.ofL (x := x) (η := η) (single ((k : ℤ), a) (u * q)) := by
            change _ = xyHom S x η (C (C c)) * single ((k : ℤ), a) (u * q)
            rw [xyHom_C, yHom_C, single_mul_single, zero_add, smul_mul_assoc, Algebra.smul_def]
            rfl
          rw [this]; exact Submodule.smul_mem _ _ hu
      · rw [single_zero]; exact Submodule.zero_mem _
      · intro u v _ _ hu hv; rw [single_add]; exact Submodule.add_mem _ hu hv
      · intro c u _ hu
        have : UT.ofL (x := x) (η := η) (single ((k : ℤ), a) (c • u)) =
            (C (C c) : Poly (MvPolynomial (Fin (r + 1)) S) N) • UT.ofL (x := x) (η := η) (single ((k : ℤ), a) u) := by
          change _ = xyHom S x η (C (C c)) * single ((k : ℤ), a) u
          rw [xyHom_C, yHom_C, single_mul_single, zero_add, Algebra.smul_def]
          rfl
        rw [this]; exact Submodule.smul_mem _ _ hu
    intro v hv
    have hv' : IsTw η M₀ (UT.toL v) := hv
    have : v = ∑ k ∈ (UT.toL v).coeff.support, UT.ofL (x := x) (η := η) (single k ((UT.toL v).coeff k)) :=
      (sum_coeff_single (UT.toL v)).symm
    rw [this]
    exact Submodule.sum_mem _ fun k _ => hsingle k.2 k.1 _ (hv' k)
instance (M₀ : FinGradedSub (S := S) (x := x) Ω) :
    Module.Finite (Poly (MvPolynomial (Fin (r + 1)) S) N) (TwM η M₀) :=
  Module.Finite.iff_fg.mpr (twSub_fg η M₀)
end Obj
end
end GroundTheory.Heights₂.Heights.Kleiman


