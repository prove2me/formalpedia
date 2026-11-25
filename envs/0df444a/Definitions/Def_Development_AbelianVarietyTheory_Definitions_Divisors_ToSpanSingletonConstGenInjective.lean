-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:16:59.509377+00:00
-- url     : https://prove2.me/theorems/d3b82bdc-66c7-4005-9753-79c99bc815dd
-- title:
--   To Span Singleton Const Gen Injective
-- statement:
--   Definitions and structural lemmas for To Span Singleton Const Gen Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_AugCot_rankAtStalk_eq
import Theorems.Thm_GlobalTheory_CartierDual_counit_addMonoidAlgebra
import Theorems.Thm_GlobalTheory_CartierDual_map_injective
import Theorems.Thm_GlobalTheory_CartierDual_map_map_bidual
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange
import Theorems.Thm_GlobalTheory_PDiv_comp_mulBy_pts
import Theorems.Thm_GlobalTheory_PDiv_convMul_apply_groupLike
import Theorems.Thm_GlobalTheory_PDiv_convPow_apply_groupLike
import Theorems.Thm_GlobalTheory_PDiv_cotMap_comp
import Theorems.Thm_GlobalTheory_PDiv_cotMap_mul
import Theorems.Thm_GlobalTheory_PDiv_cotMap_one
import Theorems.Thm_GlobalTheory_PDiv_cotMap_pow
import Theorems.Thm_GlobalTheory_PDiv_dUnit_mul_groupLike
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_dual_map_surjective
import Theorems.Thm_GlobalTheory_PDiv_dual_mulBy
import Theorems.Thm_GlobalTheory_PDiv_fibreDim_congr
import Theorems.Thm_GlobalTheory_PDiv_fibreDim_dual
import Theorems.Thm_GlobalTheory_PDiv_fibreDim_ker_dual
import Theorems.Thm_GlobalTheory_PDiv_kerIdeal_comp_of_surjective
import Theorems.Thm_GlobalTheory_PDiv_kerIdeal_le_ker_iff
import Theorems.Thm_GlobalTheory_PDiv_ker_eq_of_fibreDim_eq
import Theorems.Thm_GlobalTheory_PDiv_map_mulBy
import Theorems.Thm_GlobalTheory_PDiv_map_torsionIdeal
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
import Theorems.Thm_GlobalTheory_PDiv_muT_pow_self
import Theorems.Thm_GlobalTheory_PDiv_mu_bialgHom_ext
import Theorems.Thm_GlobalTheory_PDiv_mulBy_groupLike
import Theorems.Thm_GlobalTheory_PDiv_mulBy_mulBy
import Theorems.Thm_GlobalTheory_PDiv_pow_digit_add
import Theorems.Thm_GlobalTheory_PDiv_pow_digit_mul
import Theorems.Thm_GlobalTheory_PDiv_pow_digit_natCast
import Theorems.Thm_GlobalTheory_PDiv_pow_digit_one
import Theorems.Thm_GlobalTheory_PDiv_pow_digit_succ
import Theorems.Thm_GlobalTheory_PDiv_pow_dvd_sub_digit
import Theorems.Thm_GlobalTheory_PDiv_rankAtStalk_dual
import Theorems.Thm_GlobalTheory_PDiv_torsionIdeal_le_ker_iff
import Theorems.Thm_GlobalTheory_PDiv_torsionIdeal_le_of_dvd
import Theorems.Thm_ReciprocityTheory_PGsh_IsPtDer_map_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT


set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
namespace GlobalTheory
open PDiv
structure PDivGroup (p : ℕ) (O : Type) [CommRing O] : Type 1 where

  height : ℕ

  A : ℕ → Type
  [commRing : ∀ n, CommRing (A n)]
  [hopf : ∀ n, HopfAlgebra O (A n)]
  [cocomm : ∀ n, IsCocomm O (A n)]
  [finite : ∀ n, Module.Finite O (A n)]
  [projective : ∀ n, Module.Projective O (A n)]

  rank_eq : ∀ (n : ℕ) (q : PrimeSpectrum O), rankAtStalk (A n) q = p ^ (n * height)

  res : ∀ n, A (n + 1) →ₐc[O] A n

  res_surjective : ∀ n, Function.Surjective (res n)

  ker_res : ∀ n, RingHom.ker (res n) = torsionIdeal O (A (n + 1)) (p ^ n)
namespace PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
section Basic
variable (G : PDivGroup p O)
theorem fibreDim_eq (n : ℕ) (q : PrimeSpectrum O) : fibreDim (G.A n) q = p ^ (n * G.height) :=
  (rankAtStalk_eq q).symm.trans (G.rank_eq n q)
theorem mulBy_pow_self (n : ℕ) (a : G.A n) :
    mulBy O (G.A n) (p ^ n) a = algebraMap O _ (counit a) := by
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [← map_mulBy, CoalgHomClass.counit_comp_apply]
  exact (kerIdeal_le_ker_iff _ (G.res n : G.A (n + 1) →ₐ[O] G.A n)).1 (G.ker_res n).ge b
theorem pts_pow_self (n : ℕ) {B : Type*} [CommRing B] [Algebra O B]
    (x : WithConv (G.A n →ₐ[O] B)) : x ^ p ^ n = 1 :=
  ofConv_injective <| (comp_mulBy_pts x.ofConv _).symm.trans <| AlgHom.ext fun a =>
    (congrArg x.ofConv (G.mulBy_pow_self n a)).trans (x.ofConv.commutes _)
theorem hom_pow_self (n : ℕ) {B : Type*} [CommRing B] [Bialgebra O B]
    (x : WithConv (G.A n →ₐc[O] B)) : x ^ p ^ n = 1 :=
  toPts_injective (by rw [map_pow, map_one, pts_pow_self])
def mulP (n : ℕ) : G.A n →ₐc[O] G.A (n + 1) :=
  liftSurj (G.res n) (G.res_surjective n) (mulBy O _ p) <| by
    rw [G.ker_res]
    refine (kerIdeal_le_ker_iff _ (mulBy O (G.A (n + 1)) p : G.A (n + 1) →ₐ[O] G.A (n + 1))).2 fun c => ?_
    change mulBy O _ p (mulBy O _ (p ^ n) c) = _
    rw [mulBy_mulBy, ← pow_succ', mulBy_pow_self]
@[simp] theorem mulP_res (n : ℕ) (a : G.A (n + 1)) : G.mulP n (G.res n a) = mulBy O _ p a :=
  liftSurj_apply ..
@[simp] theorem res_mulP (n : ℕ) (a : G.A n) : G.res n (G.mulP n a) = mulBy O _ p a := by
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [mulP_res, map_mulBy]
theorem mulP_comp_res (n : ℕ) : (G.mulP n).comp (G.res n) = mulBy O _ p :=
  BialgHom.ext (G.mulP_res n)
theorem exists_res_le {m n : ℕ} (h : m ≤ n) : ∃ f : G.A n →ₐc[O] G.A m,
    Function.Surjective f ∧ RingHom.ker f = torsionIdeal O _ (p ^ m) := by
  induction n, h using Nat.le_induction with
  | base =>
    refine ⟨BialgHom.id O _, Function.surjective_id, le_antisymm (fun a ha => ?_) ?_⟩
    · rw [show a = 0 from ha]; exact zero_mem _
    · exact (kerIdeal_le_ker_iff _ (AlgHom.id O _)).2 (G.mulBy_pow_self _)
  | succ n hmn ih =>
    obtain ⟨f, hf, hk⟩ := ih
    refine ⟨f.comp (G.res _), hf.comp (G.res_surjective _), ?_⟩
    have h1 : RingHom.ker (f.comp (G.res n)) =
      (RingHom.ker f).comap (G.res n : G.A (n + 1) →ₐ[O] G.A n) := rfl
    rw [h1, hk, ← map_torsionIdeal (G.res_surjective n), Ideal.comap_map_of_surjective
      (G.res n : G.A (n + 1) →ₐ[O] G.A n) (G.res_surjective n), sup_eq_left]
    exact (G.ker_res n).le.trans (torsionIdeal_le_of_dvd (pow_dvd_pow p hmn))
end Basic
section Dual
variable (G : PDivGroup p O)
theorem dual_mulP_surjective (n : ℕ) : Function.Surjective (CartierDual.map (G.mulP n)) := by
  refine dual_map_surjective _ fun q => ?_
  obtain ⟨f, hf, hk⟩ := G.exists_res_le (m := 1) (n := n + 1) (by omega)
  have h1 : kerIdeal (G.mulP n) = RingHom.ker (f : G.A (n + 1) →ₐ[O] G.A 1) := by
    rw [← kerIdeal_comp_of_surjective _ (G.res_surjective n), mulP_comp_res]
    rw [pow_one] at hk
    exact hk.symm
  rw [h1, fibreDim_congr (Ideal.quotientKerAlgEquivOfSurjective
    (f := (f : G.A (n + 1) →ₐ[O] G.A 1)) hf).toLinearEquiv, fibreDim_eq, fibreDim_eq,
    fibreDim_eq, ← pow_add]
  congr 1
  ring
theorem ker_dual_mulP (n : ℕ) : RingHom.ker (CartierDual.map (G.mulP n)) =
    torsionIdeal O (CartierDual O (G.A (n + 1))) (p ^ n) := by
  refine ker_eq_of_fibreDim_eq
    (CartierDual.map (G.mulP n) : CartierDual O (G.A (n + 1)) →ₐ[O] CartierDual O (G.A n))
    (G.dual_mulP_surjective n) _ ?_ fun q => ?_
  · refine (kerIdeal_le_ker_iff _ _).2 fun φ => CartierDual.ext_apply fun a => ?_
    rw [← dual_mulBy]
    change φ.ofConv (mulBy O _ (p ^ n) (G.mulP n a)) =
      (algebraMap O (CartierDual O (G.A n)) (φ.ofConv 1)) a
    rw [← map_mulBy, mulBy_pow_self, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, map_smul, map_one, map_smul]
    change _ = φ.ofConv 1 * counit a
    rw [smul_eq_mul, mul_comm]
  · have h1 : kerIdeal (mulBy O (G.A (n + 1)) (p ^ n)) =
      RingHom.ker (G.res n : G.A (n + 1) →ₐ[O] G.A n) := (G.ker_res n).symm
    rw [torsionIdeal, ← dual_mulBy, fibreDim_ker_dual, fibreDim_dual, h1]
    exact fibreDim_congr (Ideal.quotientKerAlgEquivOfSurjective
      (f := (G.res n : G.A (n + 1) →ₐ[O] G.A n)) (G.res_surjective n)).toLinearEquiv q
@[reducible] def dual : PDivGroup p O where
  height := G.height
  A n := CartierDual O (G.A n)
  rank_eq n q := (rankAtStalk_dual q).trans (G.rank_eq n q)
  res n := CartierDual.map (G.mulP n)
  res_surjective := G.dual_mulP_surjective
  ker_res := G.ker_dual_mulP
theorem dual_mulP (n : ℕ) : G.dual.mulP n = CartierDual.map (G.res n) :=
  BialgHom.ext fun φ => by
    obtain ⟨ψ, rfl⟩ := G.dual.res_surjective n φ
    rw [mulP_res, ← dual_mulBy, ← mulP_comp_res]
    rfl
end Dual
@[ext] structure Hom (G H : PDivGroup p O) : Type where

  app : ∀ n, H.A n →ₐc[O] G.A n

  comm : ∀ n, (G.res n).comp (app (n + 1)) = (app n).comp (H.res n)
instance : Category (PDivGroup p O) where
  Hom := Hom
  id G := ⟨fun _ => BialgHom.id O _, fun _ => rfl⟩
  comp f g := ⟨fun n => (f.app n).comp (g.app n), fun n => by
    rw [← BialgHom.comp_assoc, f.comm, BialgHom.comp_assoc, g.comm, BialgHom.comp_assoc]⟩
section Hom
variable {G H K : PDivGroup p O}
@[ext] theorem hom_ext {f g : G ⟶ H} (h : ∀ n, f.app n = g.app n) : f = g := Hom.ext (funext h)
@[simp] theorem id_app (n : ℕ) : Hom.app (𝟙 G) n = BialgHom.id O _ := rfl
@[simp] theorem comp_app (f : G ⟶ H) (g : H ⟶ K) (n : ℕ) :
    Hom.app (f ≫ g) n = (f.app n).comp (g.app n) := rfl
theorem res_app (f : G ⟶ H) (n : ℕ) (a : H.A (n + 1)) :
    G.res n (f.app (n + 1) a) = f.app n (H.res n a) := DFunLike.congr_fun (f.comm n) a
theorem app_mulP (f : G ⟶ H) (n : ℕ) (a : H.A n) :
    f.app (n + 1) (H.mulP n a) = G.mulP n (f.app n a) := by
  obtain ⟨b, rfl⟩ := H.res_surjective n a
  rw [mulP_res, ← res_app, mulP_res, map_mulBy]
abbrev Hom.conv (f : G ⟶ H) (n : ℕ) : WithConv (H.A n →ₐc[O] G.A n) := toConv (f.app n)
theorem hom_ext_conv {f g : G ⟶ H} (h : ∀ n, f.conv n = g.conv n) : f = g :=
  hom_ext fun n => congrArg ofConv (h n)
theorem Hom.comm_conv (f : G ⟶ H) (n : ℕ) :
    postcomp _ (G.res n) (f.conv (n + 1)) = precomp _ (H.res n) (f.conv n) :=
  congrArg toConv (f.comm n)
instance : Zero (G ⟶ H) := ⟨⟨fun n => (1 : WithConv (H.A n →ₐc[O] G.A n)).ofConv, fun n =>
  congrArg ofConv ((map_one (postcomp _ (G.res n))).trans (map_one (precomp _ (H.res n))).symm)⟩⟩
instance : Add (G ⟶ H) := ⟨fun f g => ⟨fun n => (f.conv n * g.conv n).ofConv, fun n =>
  congrArg ofConv (show postcomp _ (G.res n) (f.conv (n + 1) * g.conv (n + 1)) =
      precomp _ (H.res n) (f.conv n * g.conv n) by
    rw [map_mul, map_mul, f.comm_conv, g.comm_conv])⟩⟩
@[simp] theorem zero_conv (n : ℕ) : Hom.conv (0 : G ⟶ H) n = 1 := rfl
@[simp] theorem add_conv (f g : G ⟶ H) (n : ℕ) : Hom.conv (f + g) n = f.conv n * g.conv n := rfl
variable [Fact p.Prime]
instance : SMul ℤ_[p] (G ⟶ H) := ⟨fun a f => ⟨fun n => (f.conv n ^ digit n a).ofConv, fun n =>
  congrArg ofConv (show postcomp _ (G.res n) (f.conv (n + 1) ^ digit (n + 1) a) =
      precomp _ (H.res n) (f.conv n ^ digit n a) by
    rw [map_pow, f.comm_conv, ← map_pow, pow_digit_succ (H.hom_pow_self n _)])⟩⟩
@[simp] theorem smul_conv (a : ℤ_[p]) (f : G ⟶ H) (n : ℕ) :
    Hom.conv (a • f) n = f.conv n ^ digit n a := rfl
instance : AddCommGroup (G ⟶ H) where
  add_assoc f g h := hom_ext_conv fun n => mul_assoc _ _ _
  zero_add f := hom_ext_conv fun n => one_mul _
  add_zero f := hom_ext_conv fun n => mul_one _
  add_comm f g := hom_ext_conv fun n => mul_comm _ _
  neg f := (-1 : ℤ_[p]) • f
  nsmul := nsmulRec
  zsmul := @zsmulRec _ _ _ ⟨fun f => (-1 : ℤ_[p]) • f⟩ nsmulRec
  neg_add_cancel f := hom_ext_conv fun n => by
    have h := pow_digit_add (H.hom_pow_self n (f.conv n)) (-1) 1
    rw [neg_add_cancel, digit_zero, pow_zero, pow_digit_one (H.hom_pow_self n _)] at h
    exact h.symm
instance : Module ℤ_[p] (G ⟶ H) where
  one_smul f := hom_ext_conv fun n => pow_digit_one (H.hom_pow_self n _)
  mul_smul a b f := hom_ext_conv fun n => pow_digit_mul (H.hom_pow_self n _) a b
  smul_zero a := hom_ext_conv fun n => one_pow _
  smul_add a f g := hom_ext_conv fun n => mul_pow _ _ _
  add_smul a b f := hom_ext_conv fun n => pow_digit_add (H.hom_pow_self n _) a b
  zero_smul f := hom_ext_conv fun n => by rw [smul_conv, digit_zero, pow_zero, zero_conv]
omit [Fact p.Prime] in

theorem comp_conv_left (f : G ⟶ H) (g : H ⟶ K) (n : ℕ) :
    Hom.conv (f ≫ g) n = precomp (G.A n) (g.app n) (f.conv n) := rfl
omit [Fact p.Prime] in

theorem comp_conv_right (f : G ⟶ H) (g : H ⟶ K) (n : ℕ) :
    Hom.conv (f ≫ g) n = postcomp (K.A n) (f.app n) (g.conv n) := rfl
instance : Preadditive (PDivGroup p O) where
  homGroup _ _ := inferInstance
  add_comp _ _ _ f f' g := hom_ext_conv fun n => by
    rw [add_conv, comp_conv_left, comp_conv_left, comp_conv_left, add_conv, map_mul]
  comp_add _ _ _ f g g' := hom_ext_conv fun n => by
    rw [add_conv, comp_conv_right, comp_conv_right, comp_conv_right, add_conv, map_mul]
instance : Linear ℤ_[p] (PDivGroup p O) where
  homModule _ _ := inferInstance
  smul_comp _ _ _ a f g := hom_ext_conv fun n => by
    rw [smul_conv, comp_conv_left, comp_conv_left, smul_conv, map_pow]
  comp_smul _ _ _ f a g := hom_ext_conv fun n => by
    rw [smul_conv, comp_conv_right, comp_conv_right, smul_conv, map_pow]
abbrev Action (Λ : Type*) [Semiring Λ] (G : PDivGroup p O) : Type _ := Λ →+* End G
def padicAction (G : PDivGroup p O) : Action ℤ_[p] G := algebraMap ℤ_[p] (End G)
theorem pow_smul_conv (f : G ⟶ H) (n : ℕ) : Hom.conv ((p : ℤ_[p]) ^ n • f) n = 1 := by
  rw [smul_conv, ← Nat.cast_pow, pow_digit_natCast (H.hom_pow_self n _), H.hom_pow_self]
theorem Action.eq_padicAction (ρ : Action ℤ_[p] G) : ρ = G.padicAction := by
  have key : ∀ (ψ : Action ℤ_[p] G) (a : ℤ_[p]) (n : ℕ),
      Hom.conv (ψ a : G ⟶ G) n = Hom.conv (show G ⟶ G from (digit n a : End G)) n := by
    intro ψ a n
    obtain ⟨c, hc⟩ := pow_dvd_sub_digit n a
    have h := congrArg ψ (sub_eq_iff_eq_add.1 hc)
    have h2 : (p : End G) ^ n * ψ c = (p : ℤ_[p]) ^ n • ψ c := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [map_add, map_mul, map_pow, map_natCast, map_natCast, h2] at h
    rw [h]
    exact (add_conv _ _ n).trans (by rw [pow_smul_conv, one_mul])
  exact RingHom.ext fun a => hom_ext_conv fun n => (key ρ a n).trans (key _ a n).symm
theorem Action.map_algebraMap {Λ : Type*} [Semiring Λ] [Algebra ℤ_[p] Λ] (ρ : Action Λ G)
    (a : ℤ_[p]) : ρ (algebraMap ℤ_[p] Λ a) = algebraMap ℤ_[p] (End G) a :=
  DFunLike.congr_fun (Action.eq_padicAction (RingHom.comp ρ (algebraMap ℤ_[p] Λ))) a
def Action.toAlgHom {Λ : Type*} [Semiring Λ] [Algebra ℤ_[p] Λ] (ρ : Action Λ G) :
    Λ →ₐ[ℤ_[p]] End G := { (ρ : Λ →+* End G) with commutes' := ρ.map_algebraMap }
variable (G H) in

def dualHom : (G ⟶ H) →ₗ[ℤ_[p]] (H.dual ⟶ G.dual) where
  toFun f := ⟨fun n => CartierDual.map (f.app n), fun n => BialgHom.ext fun φ =>
    CartierDual.ext_apply fun a => congrArg φ.ofConv (app_mulP f n a)⟩
  map_add' f g := hom_ext_conv fun n =>
    map_mul (dualMonoidHom O (G.A n) (H.A n)) (f.conv n) (g.conv n)
  map_smul' a f := hom_ext_conv fun n =>
    map_pow (dualMonoidHom O (G.A n) (H.A n)) (f.conv n) (digit n a)
@[simp] theorem dualHom_app (f : G ⟶ H) (n : ℕ) :
    (dualHom G H f).app n = CartierDual.map (f.app n) := rfl
@[simp] theorem dualHom_id : dualHom G G (𝟙 G) = 𝟙 G.dual := rfl
theorem dualHom_comp (f : G ⟶ H) (g : H ⟶ K) :
    dualHom G K (f ≫ g) = dualHom H K g ≫ dualHom G H f := rfl
omit [Fact p.Prime] in
variable (G) in

def bidual : G ≅ G.dual.dual where
  hom := ⟨fun n => (CartierDual.bidual O (G.A n)).symm, fun n => BialgHom.ext fun x => by
    obtain ⟨a, rfl⟩ := (CartierDual.bidual O (G.A (n + 1))).surjective x
    change G.res n ((CartierDual.bidual O (G.A (n + 1))).symm
      (CartierDual.bidual O (G.A (n + 1)) a)) = (CartierDual.bidual O (G.A n)).symm
        (CartierDual.map (G.dual.mulP n) (CartierDual.bidual O (G.A (n + 1)) a))
    rw [dual_mulP, CartierDual.map_map_bidual, BialgEquiv.symm_apply_apply,
      BialgEquiv.symm_apply_apply]⟩
  inv := ⟨fun n => CartierDual.bidualHom O (G.A n), fun n => BialgHom.ext fun a => by
    change CartierDual.map (G.dual.mulP n) (CartierDual.bidual O (G.A (n + 1)) a) = _
    rw [dual_mulP, CartierDual.map_map_bidual]
    rfl⟩
  hom_inv_id := hom_ext fun n => BialgHom.ext fun a =>
    (CartierDual.bidual O (G.A n)).symm_apply_apply a
  inv_hom_id := hom_ext fun n => BialgHom.ext fun a =>
    (CartierDual.bidual O (G.A n)).apply_symm_apply a
theorem dualHom_dualHom_bidual_inv (f : G ⟶ H) :
    dualHom _ _ (dualHom G H f) ≫ H.bidual.inv = G.bidual.inv ≫ f := rfl
theorem bidual_hom_dualHom_dualHom (f : G ⟶ H) :
    G.bidual.hom ≫ dualHom _ _ (dualHom G H f) = f ≫ H.bidual.hom := by
  rw [← Iso.comp_inv_eq, Category.assoc, dualHom_dualHom_bidual_inv, Iso.hom_inv_id_assoc]
theorem dualHom_bidual_inv : dualHom _ _ G.bidual.inv = G.dual.bidual.hom := by
  rw [← cancel_epi G.dual.bidual.inv, Iso.inv_hom_id, ← cancel_mono G.dual.bidual.inv,
    Category.id_comp, Category.assoc]
  rfl
theorem dualHom_bijective : Function.Bijective (dualHom G H) := by
  refine ⟨fun f g h => hom_ext fun n => CartierDual.map_injective
    (congrArg (fun x => Hom.app x n) h), fun g => ?_⟩
  refine ⟨G.bidual.hom ≫ dualHom _ _ g ≫ H.bidual.inv, ?_⟩
  have h : dualHom _ _ G.bidual.hom = G.dual.bidual.inv := by
    rw [← cancel_epi G.dual.bidual.hom, Iso.hom_inv_id, ← dualHom_bidual_inv, ← dualHom_comp,
      Iso.hom_inv_id, dualHom_id]
  rw [dualHom_comp, dualHom_comp, h, dualHom_bidual_inv, bidual_hom_dualHom_dualHom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]
variable (G H) in

def dualHomEquiv : (G ⟶ H) ≃ₗ[ℤ_[p]] (H.dual ⟶ G.dual) :=
  LinearEquiv.ofBijective (dualHom G H) dualHom_bijective
@[simp] theorem dualHomEquiv_apply (f : G ⟶ H) : dualHomEquiv G H f = dualHom G H f := rfl
end Hom
@[ext] structure TateOver (G : PDivGroup p O) (B : Type) [CommRing B] [Algebra O B] : Type where

  pt : ∀ n, G.A n →ₐ[O] B

  compat : ∀ n, (pt (n + 1)).comp (G.mulP n : G.A n →ₐ[O] G.A (n + 1)) = pt n
abbrev Tate (G : PDivGroup p O) : Type := G.TateOver O
section Tate
variable {G H K : PDivGroup p O} {B B' : Type} [CommRing B] [Algebra O B] [CommRing B']
  [Algebra O B']
namespace TateOver
abbrev conv (x : G.TateOver B) (n : ℕ) : WithConv (G.A n →ₐ[O] B) := toConv (x.pt n)
theorem ext_conv {x y : G.TateOver B} (h : ∀ n, x.conv n = y.conv n) : x = y :=
  TateOver.ext (funext fun n => congrArg ofConv (h n))
theorem compat_conv (x : G.TateOver B) (n : ℕ) :
    pointsMap B (G.mulP n) (x.conv (n + 1)) = x.conv n := congrArg toConv (x.compat n)
theorem pt_mulP (x : G.TateOver B) (n : ℕ) (a : G.A n) : x.pt (n + 1) (G.mulP n a) = x.pt n a :=
  DFunLike.congr_fun (x.compat n) a
instance : Zero (G.TateOver B) := ⟨⟨fun n => (1 : WithConv (G.A n →ₐ[O] B)).ofConv, fun n =>
  congrArg ofConv (map_one (pointsMap B (G.mulP n)))⟩⟩
instance : Add (G.TateOver B) := ⟨fun x y => ⟨fun n => (x.conv n * y.conv n).ofConv, fun n =>
  congrArg ofConv (show pointsMap B (G.mulP n) (x.conv (n + 1) * y.conv (n + 1)) =
      x.conv n * y.conv n by rw [map_mul, compat_conv, compat_conv])⟩⟩
@[simp] theorem zero_conv (n : ℕ) : conv (0 : G.TateOver B) n = 1 := rfl
@[simp] theorem add_conv (x y : G.TateOver B) (n : ℕ) :
    conv (x + y) n = x.conv n * y.conv n := rfl
variable [Fact p.Prime]
instance : SMul ℤ_[p] (G.TateOver B) := ⟨fun a x => ⟨fun n => (x.conv n ^ digit n a).ofConv,
  fun n => congrArg ofConv (show pointsMap B (G.mulP n) (x.conv (n + 1) ^ digit (n + 1) a) =
      x.conv n ^ digit n a by
    rw [map_pow, compat_conv, pow_digit_succ (G.pts_pow_self n _)])⟩⟩
@[simp] theorem smul_conv (a : ℤ_[p]) (x : G.TateOver B) (n : ℕ) :
    conv (a • x) n = x.conv n ^ digit n a := rfl
instance : AddCommGroup (G.TateOver B) where
  add_assoc _ _ _ := ext_conv fun _ => mul_assoc _ _ _
  zero_add _ := ext_conv fun _ => one_mul _
  add_zero _ := ext_conv fun _ => mul_one _
  add_comm _ _ := ext_conv fun _ => mul_comm _ _
  neg x := (-1 : ℤ_[p]) • x
  nsmul := nsmulRec
  zsmul := @zsmulRec _ _ _ ⟨fun x => (-1 : ℤ_[p]) • x⟩ nsmulRec
  neg_add_cancel x := ext_conv fun n => by
    have h := pow_digit_add (G.pts_pow_self n (x.conv n)) (-1) 1
    rw [neg_add_cancel, digit_zero, pow_zero, pow_digit_one (G.pts_pow_self n _)] at h
    exact h.symm
instance : Module ℤ_[p] (G.TateOver B) where
  one_smul _ := ext_conv fun n => pow_digit_one (G.pts_pow_self n _)
  mul_smul a b _ := ext_conv fun n => pow_digit_mul (G.pts_pow_self n _) a b
  smul_zero _ := ext_conv fun _ => one_pow _
  smul_add _ _ _ := ext_conv fun _ => mul_pow _ _ _
  add_smul a b _ := ext_conv fun n => pow_digit_add (G.pts_pow_self n _) a b
  zero_smul _ := ext_conv fun n => by rw [smul_conv, digit_zero, pow_zero, zero_conv]
end TateOver
variable [Fact p.Prime]
omit [Fact p.Prime] in

def TateOver.map (f : G ⟶ H) (x : G.TateOver B) : H.TateOver B :=
  ⟨fun n => (x.pt n).comp (f.app n : H.A n →ₐ[O] G.A n), fun n => AlgHom.ext fun a =>
    (congrArg (x.pt (n + 1)) (app_mulP f n a)).trans (x.pt_mulP n _)⟩
variable (G H B) in

def tateMap : (G ⟶ H) →ₗ[ℤ_[p]] G.TateOver B →ₗ[ℤ_[p]] H.TateOver B :=
  LinearMap.mk₂ ℤ_[p] TateOver.map
    (fun f g x => TateOver.ext_conv fun n =>
      map_mul ((ptsPush (H.A n) (x.pt n)).comp toPts) (f.conv n) (g.conv n))
    (fun a f x => TateOver.ext_conv fun n =>
      map_pow ((ptsPush (H.A n) (x.pt n)).comp toPts) (f.conv n) (digit n a))
    (fun f x y => TateOver.ext_conv fun n => map_mul (pointsMap B (f.app n)) (x.conv n) (y.conv n))
    (fun a f x => TateOver.ext_conv fun n => map_pow (pointsMap B (f.app n)) (x.conv n) (digit n a))
@[simp] theorem tateMap_pt (f : G ⟶ H) (x : G.TateOver B) (n : ℕ) (a : H.A n) :
    (tateMap G H B f x).pt n a = x.pt n (f.app n a) := rfl
@[simp] theorem tateMap_id (x : G.TateOver B) : tateMap G G B (𝟙 G) x = x := rfl
theorem tateMap_comp (f : G ⟶ H) (g : H ⟶ K) (x : G.TateOver B) :
    tateMap G K B (f ≫ g) x = tateMap H K B g (tateMap G H B f x) := rfl
variable (B) in

def tateCongr (e : G ≅ H) : G.TateOver B ≃ₗ[ℤ_[p]] H.TateOver B :=
  LinearEquiv.ofLinearMap (tateMap G H B e.hom) (tateMap H G B e.inv)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← tateMap_comp, e.inv_hom_id, tateMap_id, LinearMap.id_apply])
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← tateMap_comp, e.hom_inv_id, tateMap_id, LinearMap.id_apply])
@[simp] theorem tateCongr_apply (e : G ≅ H) (x : G.TateOver B) :
    tateCongr B e x = tateMap G H B e.hom x := rfl
variable (G B) in

def tateEnd : End G →ₐ[ℤ_[p]] Module.End ℤ_[p] (G.TateOver B) :=
  AlgHom.ofLinearMap (tateMap G G B) rfl fun _ _ => rfl
@[simp] theorem tateEnd_apply (f : End G) : tateEnd G B f = tateMap G G B f := rfl
variable (G) in

def tatePush (g : B →ₐ[O] B') : G.TateOver B →ₗ[ℤ_[p]] G.TateOver B' where
  toFun x := ⟨fun n => g.comp (x.pt n), fun n => congrArg g.comp (x.compat n)⟩
  map_add' x y := TateOver.ext_conv fun n => map_mul (ptsPush (G.A n) g) (x.conv n) (y.conv n)
  map_smul' a x := TateOver.ext_conv fun n => map_pow (ptsPush (G.A n) g) (x.conv n) (digit n a)
@[simp] theorem tatePush_pt (g : B →ₐ[O] B') (x : G.TateOver B) (n : ℕ) (a : G.A n) :
    (G.tatePush g x).pt n a = g (x.pt n a) := rfl
end Tate
section Omega
variable (G H K : PDivGroup p O)
def omegaSub : Submodule O (∀ n, Cot O (G.A n)) where
  carrier := {w | ∀ n, cotMap (G.res n) (w (n + 1)) = w n}
  zero_mem' _ := map_zero _
  add_mem' {v w} hv hw n := by rw [Pi.add_apply, map_add, hv n, hw n, Pi.add_apply]
  smul_mem' c w hw n := by rw [Pi.smul_apply, map_smul, hw n, Pi.smul_apply]
abbrev omega : Type := G.omegaSub
abbrev Lie : Type := Module.Dual O G.omega
theorem pow_smul_cot (n : ℕ) (w : Cot O (G.A n)) : (p : O) ^ n • w = 0 := by
  have h := cotMap_pow (toConv (BialgHom.id O (G.A n))) (p ^ n)
  rw [G.hom_pow_self, cotMap_one, ofConv_toConv, cotMap_id] at h
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact (LinearMap.congr_fun h w).symm
theorem digit_smul_cot [Fact p.Prime] (φ : ℤ_[p] →+* O) (a : ℤ_[p]) (n : ℕ) (w : Cot O (G.A n)) :
    digit n a • w = φ a • w := by
  obtain ⟨c, hc⟩ := pow_dvd_sub_digit n a
  have h := congrArg φ (sub_eq_iff_eq_add.1 hc)
  rw [map_add, map_mul, map_pow, map_natCast, map_natCast, mul_comm] at h
  rw [h, add_smul, mul_smul, pow_smul_cot, smul_zero, zero_add, Nat.cast_smul_eq_nsmul]
variable [Fact p.Prime]
def omegaMap : (G ⟶ H) →+ (H.omega →ₗ[O] G.omega) :=
  AddMonoidHom.mk' (fun f =>
    { toFun := fun w => ⟨fun n => cotMap (f.app n) (w.1 n), fun n => by
        change cotMap (G.res n) (cotMap (f.app (n + 1)) (w.1 (n + 1))) = cotMap (f.app n) (w.1 n)
        rw [← w.2 n, ← LinearMap.comp_apply, ← cotMap_comp, f.comm, cotMap_comp,
          LinearMap.comp_apply]⟩
      map_add' := fun v w => Subtype.ext (funext fun n => map_add (cotMap (f.app n)) _ _)
      map_smul' := fun c w => Subtype.ext (funext fun n => map_smul (cotMap (f.app n)) _ _) })
    fun f g => LinearMap.ext fun w => Subtype.ext (funext fun n =>
      LinearMap.congr_fun (cotMap_mul (f.conv n) (g.conv n)) (w.1 n))
variable {G H K}
@[simp] theorem omegaMap_val (f : G ⟶ H) (w : H.omega) (n : ℕ) :
    (omegaMap G H f w).1 n = cotMap (f.app n) (w.1 n) := rfl
@[simp] theorem omegaMap_id : omegaMap G G (𝟙 G) = LinearMap.id :=
  LinearMap.ext fun w => Subtype.ext (funext fun n => LinearMap.congr_fun cotMap_id (w.1 n))
theorem omegaMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    omegaMap G K (f ≫ g) = omegaMap G H f ∘ₗ omegaMap H K g :=
  LinearMap.ext fun w => Subtype.ext (funext fun n =>
    LinearMap.congr_fun (cotMap_comp (f.app n) (g.app n)) (w.1 n))
theorem omegaMap_smul (φ : ℤ_[p] →+* O) (a : ℤ_[p]) (f : G ⟶ H) :
    omegaMap G H (a • f) = φ a • omegaMap G H f :=
  LinearMap.ext fun w => Subtype.ext (funext fun n =>
    (LinearMap.congr_fun (cotMap_pow (f.conv n) (digit n a)) (w.1 n)).trans
      (G.digit_smul_cot φ a n _))
variable (G H) in

def lieMap : (G ⟶ H) →+ (G.Lie →ₗ[O] H.Lie) :=
  AddMonoidHom.mk' (fun f => (omegaMap G H f).dualMap) fun f g => by
    rw [map_add]; ext; simp
@[simp] theorem lieMap_apply (f : G ⟶ H) (x : G.Lie) (w : H.omega) :
    lieMap G H f x w = x (omegaMap G H f w) := rfl
@[simp] theorem lieMap_id : lieMap G G (𝟙 G) = LinearMap.id :=
  LinearMap.ext fun x => LinearMap.ext fun w => by simp
theorem lieMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    lieMap G K (f ≫ g) = lieMap H K g ∘ₗ lieMap G H f :=
  LinearMap.ext fun x => LinearMap.ext fun w => by simp [omegaMap_comp]
theorem lieMap_smul (φ : ℤ_[p] →+* O) (a : ℤ_[p]) (f : G ⟶ H) :
    lieMap G H (a • f) = φ a • lieMap G H f :=
  LinearMap.ext fun x => LinearMap.ext fun w => by simp [omegaMap_smul φ]
variable (G) in

def lieEnd : End G →+* Module.End O G.Lie where
  __ := lieMap G G
  map_one' := lieMap_id
  map_mul' f g := lieMap_comp g f
@[simp] theorem lieEnd_apply (f : End G) : lieEnd G f = lieMap G G f := rfl
variable (G H) in

def omegaDualMap : (G ⟶ H) →+ (G.dual.omega →ₗ[O] H.dual.omega) :=
  (omegaMap H.dual G.dual).comp (dualHom G H).toAddMonoidHom
@[simp] theorem omegaDualMap_id : omegaDualMap G G (𝟙 G) = LinearMap.id := omegaMap_id
theorem omegaDualMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    omegaDualMap G K (f ≫ g) = omegaDualMap H K g ∘ₗ omegaDualMap G H f :=
  omegaMap_comp (dualHom H K g) (dualHom G H f)
variable (G) in

def omegaDualEnd : End G →+* Module.End O G.dual.omega where
  __ := omegaDualMap G G
  map_one' := omegaDualMap_id
  map_mul' f g := omegaDualMap_comp g f
@[simp] theorem omegaDualEnd_apply (f : End G) : omegaDualEnd G f = omegaDualMap G G f := rfl
namespace Action
variable {Λ : Type*} [Semiring Λ] (ρ : Action Λ G)
def onTate (B : Type) [CommRing B] [Algebra O B] : Λ →+* Module.End ℤ_[p] (G.TateOver B) :=
  (tateEnd G B).toRingHom.comp ρ
def onTateAlg [Algebra ℤ_[p] Λ] (B : Type) [CommRing B] [Algebra O B] :
    Λ →ₐ[ℤ_[p]] Module.End ℤ_[p] (G.TateOver B) := (tateEnd G B).comp ρ.toAlgHom
@[simp] theorem onTate_apply (B : Type) [CommRing B] [Algebra O B] (a : Λ) :
    ρ.onTate B a = tateMap G G B (ρ a) := rfl
@[simp] theorem onTateAlg_apply [Algebra ℤ_[p] Λ] (B : Type) [CommRing B] [Algebra O B] (a : Λ) :
    ρ.onTateAlg B a = tateMap G G B (ρ a) := rfl
def onLie : Λ →+* Module.End O G.Lie := (lieEnd G).comp ρ
def onOmegaDual : Λ →+* Module.End O G.dual.omega := (omegaDualEnd G).comp ρ
@[simp] theorem onLie_apply (a : Λ) : ρ.onLie a = lieMap G G (ρ a) := rfl
@[simp] theorem onOmegaDual_apply (a : Λ) : ρ.onOmegaDual a = omegaDualMap G G (ρ a) := rfl
def dual {Λ : Type*} [CommSemiring Λ] (ρ : Action Λ G) : Action Λ G.dual where
  toFun a := dualHom G G (ρ a)
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [mul_comm, map_mul]; rfl
  map_zero' := by rw [map_zero]; exact map_zero _
  map_add' a b := by rw [map_add]; exact map_add _ _ _
end Action
end Omega
section Examples
variable (p O) [Fact p.Prime]
omit [Fact p.Prime] in

theorem muT_pow_succ (n : ℕ) : muT O (p ^ n) ^ p ^ (n + 1) = 1 := by
  rw [pow_succ, pow_mul, muT_pow_self, one_pow]
def muRes (n : ℕ) :
    AddMonoidAlgebra O (ZMod (p ^ (n + 1))) →ₐc[O] AddMonoidAlgebra O (ZMod (p ^ n)) :=
  muChar (muT O (p ^ n)) (isGroupLikeElem_muT O _) (muT_pow_succ p O n)
@[simp] theorem muRes_muT (n : ℕ) : muRes p O n (muT O _) = muT O _ := muChar_muT ..
@[reducible] def mu : PDivGroup p O where
  height := 1
  A n := AddMonoidAlgebra O (ZMod (p ^ n))
  rank_eq n q := by
    have := q.nontrivial
    rw [rankAtStalk_eq_finrank_of_free, mul_one,
      finrank_eq_card_basis (AddMonoidAlgebra.basis (ZMod (p ^ n)) O), ZMod.card]
    rfl
  res := muRes p O
  res_surjective n x := by
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add ..⟩
    | single k r =>
      refine ⟨r • muT O _ ^ k.val, ?_⟩
      rw [map_smul, map_pow, muRes_muT, muT_pow, ZMod.natCast_zmod_val]
      simp
  ker_res n := by
    have key : ∀ {E : Type} [CommRing E] [Algebra O E]
        (x : AddMonoidAlgebra O (ZMod (p ^ (n + 1))) →ₐ[O] E),
        torsionIdeal O _ (p ^ n) ≤ RingHom.ker x ↔ x (muT O _) ^ p ^ n = 1 := fun x => by
      rw [torsionIdeal_le_ker_iff, ← convPow_apply_groupLike (toConv x) (isGroupLikeElem_muT O _)]
      refine ⟨fun h => by rw [h]; simp [(isGroupLikeElem_muT O _).counit_eq_one], fun h => ?_⟩
      exact ofConv_injective (mu_algHom_ext (h.trans
        (by simp [(isGroupLikeElem_muT O _).counit_eq_one])))
    refine le_antisymm (fun a ha => ?_) ((key (muRes p O n).toAlgHom).2 ?_)
    · let π := Ideal.Quotient.mkₐ O
        (torsionIdeal O (AddMonoidAlgebra O (ZMod (p ^ (n + 1)))) (p ^ n))
      have h1 := (key π).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
      have h2 : (muPoint O _ h1).comp (muRes p O n).toAlgHom = π := mu_algHom_ext <|
        (congrArg (muPoint O _ h1) (muRes_muT p O n)).trans (muPoint_muT _ h1)
      have h3 : π a = muPoint O _ h1 (muRes p O n a) := (DFunLike.congr_fun h2 a).symm
      rw [show muRes p O n a = 0 from ha, map_zero] at h3
      exact Ideal.Quotient.eq_zero_iff_mem.1 h3
    · exact (congrArg (· ^ p ^ n) (muRes_muT p O n)).trans (muT_pow_self O _)
@[simp] theorem mu_mulP_muT (n : ℕ) : (mu p O).mulP n (muT O _) = muT O (p ^ (n + 1)) ^ p := by
  rw [← muRes_muT]
  exact ((mu p O).mulP_res n _).trans (mulBy_groupLike p (isGroupLikeElem_muT O _))
def dlogT : (mu p O).omega :=
  ⟨fun n => dUnit O (muT O (p ^ n)), fun n =>
    (cotMap_d (muRes p O n) _).trans (congrArg (dUnit O) (muRes_muT p O n))⟩
abbrev const : PDivGroup p O := (mu p O).dual
def constFun (n : ℕ) : (const p O).A n ≃ₐ[O] (ZMod (p ^ n) → O) :=
  CartierDual.addMonoidAlgebraEquiv O (ZMod (p ^ n))
variable {p O} {B : Type} [CommRing B] [Algebra O B]
def muRoot (x : (mu p O).TateOver B) (n : ℕ) : B := x.pt n (muT O (p ^ n))
theorem muRoot_pow_self (x : (mu p O).TateOver B) (n : ℕ) : muRoot x n ^ p ^ n = 1 := by
  rw [muRoot, ← map_pow, muT_pow_self, map_one]
theorem muRoot_succ_pow (x : (mu p O).TateOver B) (n : ℕ) : muRoot x (n + 1) ^ p = muRoot x n := by
  rw [muRoot, ← map_pow, ← mu_mulP_muT]
  exact x.pt_mulP n _
theorem muRoot_ext {x y : (mu p O).TateOver B} (h : ∀ n, muRoot x n = muRoot y n) : x = y :=
  TateOver.ext (funext fun n => mu_algHom_ext (h n))
@[simp] theorem muRoot_zero (n : ℕ) : muRoot (0 : (mu p O).TateOver B) n = 1 :=
  (congrArg (algebraMap O B) (isGroupLikeElem_muT O _).counit_eq_one).trans (map_one _)
@[simp] theorem muRoot_add (x y : (mu p O).TateOver B) (n : ℕ) :
    muRoot (x + y) n = muRoot x n * muRoot y n :=
  convMul_apply_groupLike (x.conv n) (y.conv n) (isGroupLikeElem_muT O _)
@[simp] theorem muRoot_smul (a : ℤ_[p]) (x : (mu p O).TateOver B) (n : ℕ) :
    muRoot (a • x) n = muRoot x n ^ digit n a :=
  convPow_apply_groupLike (x.conv n) (isGroupLikeElem_muT O _) _
omit [Fact p.Prime] in

theorem pow_self_of_compat {ζ : ℕ → B} (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n) (n : ℕ) :
    ζ n ^ p ^ n = 1 := by
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [pow_succ', pow_mul, h, ih]
variable (O) in

def muTate (ζ : ℕ → B) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n) : (mu p O).TateOver B :=
  ⟨fun n => muPoint O (ζ n) (pow_self_of_compat h0 h n), fun n => mu_algHom_ext <|
    (congrArg (muPoint O (ζ (n + 1)) (pow_self_of_compat h0 h (n + 1))) (mu_mulP_muT p O n)).trans
      (by rw [map_pow, muPoint_muT, muPoint_muT, h])⟩
@[simp] theorem muRoot_muTate (ζ : ℕ → B) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n) (n : ℕ) :
    muRoot (muTate O ζ h0 h) n = ζ n := muPoint_muT _ (pow_self_of_compat h0 h n)
variable (p O B) in

def muTateEquiv :
    (mu p O).TateOver B ≃ {ζ : ℕ → B // ζ 0 = 1 ∧ ∀ n, ζ (n + 1) ^ p = ζ n} where
  toFun x := ⟨muRoot x, by simpa using muRoot_pow_self x 0, muRoot_succ_pow x⟩
  invFun ζ := muTate O ζ.1 ζ.2.1 ζ.2.2
  left_inv _ := muRoot_ext fun _ => muRoot_muTate ..
  right_inv _ := Subtype.ext (funext fun _ => muRoot_muTate ..)
end Examples
section Char
section Level
variable (O) (A : Type) [CommRing A] [Bialgebra O A] [IsCocomm O A] [Module.Finite O A]
  [Module.Projective O A]
def charFun : WithConv (CartierDual O A →ₐ[O] O) →* A where
  toFun χ := (CartierDual.bidual O A).symm (toConv χ.ofConv.toLinearMap)
  map_one' := CartierDual.eq_of_forall_apply (R := O) fun φ =>
    CartierDual.apply_bidual_symm _ φ
  map_mul' χ ψ := CartierDual.eq_of_forall_apply (R := O) fun φ => by
    rw [← map_mul]
    rfl
variable {O A}
omit [IsCocomm O A] in

@[simp] theorem apply_charFun (χ : WithConv (CartierDual O A →ₐ[O] O)) (φ : CartierDual O A) :
    φ (charFun O A χ) = χ φ := CartierDual.apply_bidual_symm _ φ
omit [IsCocomm O A] in

theorem isGroupLikeElem_charFun (χ : WithConv (CartierDual O A →ₐ[O] O)) :
    IsGroupLikeElem O (charFun O A χ) :=
  (CartierDual.isGroupLikeElem_iff_mul _).2 ⟨by rw [apply_charFun]; exact map_one χ.ofConv,
    fun φ ψ => by rw [apply_charFun, apply_charFun, apply_charFun]; exact map_mul χ.ofConv φ ψ⟩
def evalPoint (u : A) (hu : IsGroupLikeElem O u) : CartierDual O A →ₐ[O] O :=
  AlgHom.ofLinearMap (CartierDual.evalAt O A u) ((CartierDual.isGroupLikeElem_iff_mul u).1 hu).1
    ((CartierDual.isGroupLikeElem_iff_mul u).1 hu).2
omit [IsCocomm O A] in

@[simp] theorem evalPoint_apply (u : A) (hu : IsGroupLikeElem O u) (φ : CartierDual O A) :
    evalPoint u hu φ = φ u := rfl
end Level
variable {G H : PDivGroup p O}
def charElem (χ : G.dual.Tate) (n : ℕ) : G.A n := charFun O (G.A n) (χ.conv n)
@[simp] theorem apply_charElem (χ : G.dual.Tate) (n : ℕ) (φ : CartierDual O (G.A n)) :
    φ (charElem χ n) = χ.pt n φ := apply_charFun _ φ
theorem isGroupLikeElem_charElem (χ : G.dual.Tate) (n : ℕ) : IsGroupLikeElem O (charElem χ n) :=
  isGroupLikeElem_charFun _
theorem charElem_pow_self (χ : G.dual.Tate) (n : ℕ) : charElem χ n ^ p ^ n = 1 := by
  rw [charElem, ← map_pow, G.dual.pts_pow_self, map_one]
@[simp] theorem res_charElem (χ : G.dual.Tate) (n : ℕ) :
    G.res n (charElem χ (n + 1)) = charElem χ n :=
  CartierDual.eq_of_forall_apply (R := O) fun φ => by
    rw [apply_charElem, ← χ.pt_mulP, dual_mulP, ← apply_charElem]
    rfl
@[simp] theorem charElem_zero (n : ℕ) : charElem (0 : G.dual.Tate) n = 1 :=
  map_one (charFun O (G.A n))
@[simp] theorem charElem_add (χ ψ : G.dual.Tate) (n : ℕ) :
    charElem (χ + ψ) n = charElem χ n * charElem ψ n :=
  map_mul (charFun O (G.A n)) (χ.conv n) (ψ.conv n)
variable [Fact p.Prime]
@[simp] theorem charElem_smul (a : ℤ_[p]) (χ : G.dual.Tate) (n : ℕ) :
    charElem (a • χ) n = charElem χ n ^ digit n a :=
  map_pow (charFun O (G.A n)) (χ.conv n) _
@[simp] theorem charElem_tateMap (f : G ⟶ H) (χ : H.dual.Tate) (n : ℕ) :
    charElem (tateMap _ _ O (dualHom G H f) χ) n = f.app n (charElem χ n) :=
  CartierDual.eq_of_forall_apply (R := O) fun φ => by
    rw [apply_charElem, tateMap_pt, ← apply_charElem]
    rfl
theorem hom_mu_ext {f g : G ⟶ mu p O} (h : ∀ n, f.app n (muT O _) = g.app n (muT O _)) : f = g :=
  hom_ext fun n => mu_bialgHom_ext (h n)
omit [Fact p.Prime] in

theorem add_app_groupLike (f g : G ⟶ H) (n : ℕ) {u : H.A n} (hu : IsGroupLikeElem O u) :
    Hom.app (f + g) n u = f.app n u * g.app n u :=
  convMul_apply_groupLike (toPts (f.conv n)) (toPts (g.conv n)) hu
theorem smul_app_groupLike (a : ℤ_[p]) (f : G ⟶ H) (n : ℕ) {u : H.A n}
    (hu : IsGroupLikeElem O u) : Hom.app (a • f) n u = f.app n u ^ digit n a :=
  (DFunLike.congr_fun (congrArg ofConv (map_pow toPts (f.conv n) (digit n a))) u).trans
    (convPow_apply_groupLike (toPts (f.conv n)) hu _)
def toMuHom (χ : G.dual.Tate) : G ⟶ mu p O :=
  ⟨fun n => muChar (charElem χ n) (isGroupLikeElem_charElem χ n) (charElem_pow_self χ n),
    fun n => mu_bialgHom_ext <| by
      rw [BialgHom.comp_apply, BialgHom.comp_apply, muChar_muT, res_charElem, muRes_muT,
        muChar_muT]⟩
theorem toMuHom_app_muT (χ : G.dual.Tate) (n : ℕ) :
    (toMuHom χ).app n (muT O (p ^ n)) = charElem χ n :=
  muChar_muT _ (isGroupLikeElem_charElem χ n) (charElem_pow_self χ n)
def ofMuHom (f : G ⟶ mu p O) : G.dual.Tate :=
  ⟨fun n => evalPoint (f.app n (muT O (p ^ n))) ((isGroupLikeElem_muT O _).map _),
    fun n => AlgHom.ext fun φ => by
      change (G.dual.mulP n φ) (f.app (n + 1) (muT O _)) = φ.ofConv (f.app n (muT O _))
      rw [dual_mulP, CartierDual.map_apply, res_app]
      exact congrArg (fun x => φ.ofConv (f.app n x)) (muRes_muT p O n)⟩
variable (G) in

def charHom : G.dual.Tate ≃ₗ[ℤ_[p]] (G ⟶ mu p O) where
  toFun := toMuHom
  map_add' χ ψ := hom_mu_ext fun n => by
    rw [add_app_groupLike _ _ n (isGroupLikeElem_muT O (p ^ n)), toMuHom_app_muT, toMuHom_app_muT,
      toMuHom_app_muT, charElem_add]
  map_smul' a χ := hom_mu_ext fun n => by
    rw [smul_app_groupLike _ _ n (isGroupLikeElem_muT O (p ^ n)), toMuHom_app_muT,
      toMuHom_app_muT, charElem_smul, RingHom.id_apply]
  invFun := ofMuHom
  left_inv χ := TateOver.ext (funext fun n => AlgHom.ext fun φ =>
    (congrArg φ.ofConv (toMuHom_app_muT χ n)).trans (apply_charElem χ n φ))
  right_inv f := hom_mu_ext fun n => (toMuHom_app_muT _ n).trans <|
    CartierDual.eq_of_forall_apply (R := O) fun φ => apply_charElem _ n φ
@[simp] theorem charHom_app_muT (χ : G.dual.Tate) (n : ℕ) :
    (charHom G χ).app n (muT O _) = charElem χ n := toMuHom_app_muT χ n
@[simp] theorem charHom_symm_pt (f : G ⟶ mu p O) (n : ℕ) (φ : CartierDual O (G.A n)) :
    ((charHom G).symm f).pt n φ = φ (f.app n (muT O _)) := rfl
variable (G) in

def dlog : G.dual.Tate →+ G.omega :=
  AddMonoidHom.mk' (fun χ => ⟨fun n => dUnit O (charElem χ n), fun n =>
      (cotMap_d (G.res n) _).trans (congrArg (dUnit O) (res_charElem χ n))⟩)
    fun χ ψ => Subtype.ext (funext fun n => (congrArg (dUnit O) (charElem_add χ ψ n)).trans
      (dUnit_mul_groupLike (isGroupLikeElem_charElem χ n) (isGroupLikeElem_charElem ψ n)))
@[simp] theorem dlog_val (χ : G.dual.Tate) (n : ℕ) :
    (dlog G χ).1 n = dUnit O (charElem χ n) := rfl
theorem dlog_eq_omegaMap (χ : G.dual.Tate) :
    dlog G χ = omegaMap G (mu p O) (charHom G χ) (dlogT p O) :=
  Subtype.ext (funext fun n => ((cotMap_d ((charHom G χ).app n) _).trans
    (congrArg (dUnit O) (charHom_app_muT χ n))).symm)
theorem dlog_smul (φ : ℤ_[p] →+* O) (a : ℤ_[p]) (χ : G.dual.Tate) :
    dlog G (a • χ) = φ a • dlog G χ := by
  rw [dlog_eq_omegaMap, dlog_eq_omegaMap, map_smul, omegaMap_smul φ, LinearMap.smul_apply]
variable (G) in

def dlogLinear [Algebra ℤ_[p] O] : O ⊗[ℤ_[p]] G.dual.Tate →ₗ[O] G.omega :=
  letI : Module ℤ_[p] G.omega := Module.compHom _ (algebraMap ℤ_[p] O)
  haveI : IsScalarTower ℤ_[p] O G.omega := ⟨fun a b w => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  LinearMap.liftBaseChange O
    { toFun := dlog G, map_add' := map_add _, map_smul' := dlog_smul (algebraMap ℤ_[p] O) }
@[simp] theorem dlogLinear_tmul [Algebra ℤ_[p] O] (c : O) (χ : G.dual.Tate) :
    dlogLinear G (c ⊗ₜ χ) = c • dlog G χ := rfl
variable (p O) in

def constGen : (const p O).Tate := (charHom (mu p O)).symm (𝟙 _)
theorem constGen_pt (n : ℕ) (φ : (const p O).A n) :
    (constGen p O).pt n φ = constFun p O n φ 1 :=
  (CartierDual.addMonoidAlgebraEquiv_apply φ 1).symm
@[simp] theorem charHom_constGen : charHom (mu p O) (constGen p O) = 𝟙 _ :=
  LinearEquiv.apply_symm_apply ..
@[simp] theorem dlog_constGen : dlog (mu p O) (constGen p O) = dlogT p O := by
  rw [dlog_eq_omegaMap, charHom_constGen, omegaMap_id, LinearMap.id_apply]
variable (G) in

def dualChar : G.Tate ≃ₗ[ℤ_[p]] (G.dual ⟶ mu p O) :=
  tateCongr O G.bidual ≪≫ₗ charHom G.dual
@[simp] theorem dualChar_app_muT (t : G.Tate) (n : ℕ) :
    (dualChar G t).app n (muT O _) = toConv (t.pt n).toLinearMap :=
  (charHom_app_muT _ n).trans <| CartierDual.ext_apply fun a =>
    (apply_charElem (G := G.dual) _ n (CartierDual.bidual O (G.A n) a)).trans
      (congrArg (t.pt n) ((CartierDual.bidual O (G.A n)).symm_apply_apply a))
variable (G) in

def constHom : G.Tate ≃ₗ[ℤ_[p]] (const p O ⟶ G) :=
  dualChar G ≪≫ₗ dualHomEquiv G.dual (mu p O) ≪≫ₗ Linear.homCongr ℤ_[p] (Iso.refl _) G.bidual.symm
theorem constHom_eq (t : G.Tate) :
    constHom G t = dualHom G.dual (mu p O) (dualChar G t) ≫ G.bidual.inv := by
  simp [constHom, Linear.homCongr_apply]
theorem constFun_constHom (t : G.Tate) (n k : ℕ) (a : G.A n) :
    constFun p O n ((constHom G t).app n a) k = (t.conv n ^ k) a := by
  rw [constHom_eq]
  simp only [constFun, CartierDual.addMonoidAlgebraEquiv_apply, ← muT_pow]
  change ((dualChar G t).app n (muT O (p ^ n) ^ k)) a = _
  rw [map_pow, dualChar_app_muT, ← AlgHom.toLinearMap_convPow (t.conv n)]
  rfl
@[simp] theorem tateMap_constHom (t : G.Tate) :
    tateMap _ G O (constHom G t) (constGen p O) = t :=
  TateOver.ext (funext fun n => AlgHom.ext fun a => by
    rw [tateMap_pt, constGen_pt, ← Nat.cast_one, constFun_constHom, pow_one])
theorem constHom_symm_apply (f : const p O ⟶ G) :
    (constHom G).symm f = tateMap _ G O f (constGen p O) := by
  obtain ⟨t, rfl⟩ := (constHom G).surjective f
  rw [LinearEquiv.symm_apply_apply, tateMap_constHom]
theorem dualHom_constHom (t : G.Tate) :
    dualHom _ G (constHom G t) ≫ (mu p O).bidual.inv = dualChar G t := by
  rw [constHom_eq, dualHom_comp, Category.assoc, dualHom_dualHom_bidual_inv, dualHom_bidual_inv,
    Iso.hom_inv_id_assoc]
variable (G) in

def hodgeTate : G.Tate →+ G.dual.omega :=
  (dlog G.dual).comp (tateMap G G.dual.dual O G.bidual.hom).toAddMonoidHom
theorem hodgeTate_eq_omegaMap (t : G.Tate) :
    hodgeTate G t = omegaMap G.dual (mu p O) (dualChar G t) (dlogT p O) := dlog_eq_omegaMap _
variable (p O) in

def constDlogT : (const p O).dual.omega :=
  omegaMap _ (mu p O) (mu p O).bidual.inv (dlogT p O)
theorem hodgeTate_eq_omegaDualMap (t : G.Tate) :
    hodgeTate G t = omegaDualMap _ G (constHom G t) (constDlogT p O) := by
  rw [hodgeTate_eq_omegaMap, ← dualHom_constHom, omegaMap_comp]
  rfl
variable (G) in

def hodgeTateLinear [Algebra ℤ_[p] O] : O ⊗[ℤ_[p]] G.Tate →ₗ[O] G.dual.omega :=
  dlogLinear G.dual ∘ₗ (tateMap G G.dual.dual O G.bidual.hom).baseChange O
@[simp] theorem hodgeTateLinear_tmul [Algebra ℤ_[p] O] (c : O) (t : G.Tate) :
    hodgeTateLinear G (c ⊗ₜ t) = c • hodgeTate G t := rfl
def epsHom (ζ : ℕ → O) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n) : const p O ⟶ mu p O :=
  constHom (mu p O) (muTate O ζ h0 h)
variable {B : Type} [CommRing B] [Algebra O B]
variable (G B) in

def pairing : G.TateOver B →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] (mu p O).TateOver B :=
  (tateMap G (mu p O) B ∘ₗ (charHom G).toLinearMap).flip
theorem pairing_apply (t : G.TateOver B) (χ : G.dual.Tate) :
    pairing G B t χ = tateMap G (mu p O) B (charHom G χ) t := rfl
@[simp] theorem muRoot_pairing (t : G.TateOver B) (χ : G.dual.Tate) (n : ℕ) :
    muRoot (pairing G B t χ) n = t.pt n (charElem χ n) :=
  congrArg (t.pt n) (charHom_app_muT χ n)
end Char
section Values
variable (p O) [Fact p.Prime]
theorem const_cot_eq_zero (n : ℕ) (w : Cot O ((const p O).A n)) : w = 0 := by
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ w
  let e := constFun p O n
  have he : ∀ φ, counitAlgHom O ((const p O).A n) φ = e φ 0 :=
    CartierDual.counit_addMonoidAlgebra
  let b := a - algebraMap O _ (e a 0)
  let c := e.symm (1 - Pi.single 0 1)
  have hb : e b 0 = 0 := by simp [b]
  have hc : e c 0 = 0 := by simp [c]
  have hbc : b = b * c := e.injective <| funext fun k => by
    rw [map_mul, Pi.mul_apply]
    by_cases hk : k = 0
    · rw [hk, hb, zero_mul]
    · simp [c, hk]
  have h : AugCot.d (counitAlgHom O ((const p O).A n)) b = 0 := by
    rw [hbc, AugCot.d_mul, he, he, hb, hc, zero_smul, zero_smul, add_zero]
  rwa [map_sub, AugCot.d_algebraMap, sub_zero] at h
instance : Subsingleton (const p O).omega :=
  ⟨fun v w => Subtype.ext (funext fun n => by
    rw [const_cot_eq_zero p O n (v.1 n), const_cot_eq_zero p O n (w.1 n)])⟩
instance : Subsingleton (const p O).Lie := inferInstance
theorem mu_cot_span (n : ℕ) (w : Cot O ((mu p O).A n)) :
    ∃ c : O, c • dUnit O (muT O (p ^ n)) = w := by
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ w
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨c', hc'⟩ := hy
    exact ⟨c + c', by rw [add_smul, hc, hc', map_add]⟩
  | single k r =>
    have h : ∀ j : ℕ, dUnit O (muT O (p ^ n) ^ j) = (j : O) • dUnit O (muT O (p ^ n)) := by
      intro j
      rw [← mulBy_groupLike j (isGroupLikeElem_muT O _), ← cotMap_d, mulBy, cotMap_pow,
        ofConv_toConv, cotMap_id, Nat.cast_smul_eq_nsmul]
      rfl
    refine ⟨r * k.val, ?_⟩
    rw [mul_smul, ← h, ← map_smul, muT_pow, ZMod.natCast_zmod_val]
    simp
omit [Fact p.Prime] in

theorem one_add_inr_pow (n : ℕ) :
    (1 + TrivSqZeroExt.inr 1 : TrivSqZeroExt O (O ⧸ Ideal.span {(p : O) ^ n})) ^ p ^ n = 1 := by
  have hc : ((p ^ n : ℕ) : O ⧸ Ideal.span {(p : O) ^ n}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.mem_span_singleton_self _
  ext
  · simp
  · simp [← Nat.cast_smul_eq_nsmul (O ⧸ Ideal.span {(p : O) ^ n}), hc]
def muDer (n : ℕ) : Cot O ((mu p O).A n) →ₗ[O] O ⧸ Ideal.span {(p : O) ^ n} :=
  AugCot.ofSqZero _ (muPoint O _ (one_add_inr_pow p O n))
    fun a => DFunLike.congr_fun (mu_algHom_ext
      (x := (TrivSqZeroExt.fstHom O O _).comp (muPoint O _ (one_add_inr_pow p O n)))
      (y := counitAlgHom O _) (by simp [(isGroupLikeElem_muT O _).counit_eq_one])) a
@[simp] theorem muDer_muT (n : ℕ) : muDer p O n (dUnit O (muT O (p ^ n))) = 1 := by
  refine (AugCot.ofSqZero_d _ _ _ _).trans ?_
  rw [muPoint_muT]
  simp
theorem smul_dUnit_muT_eq_zero_iff (n : ℕ) (c : O) :
    c • dUnit O (muT O (p ^ n)) = 0 ↔ (p : O) ^ n ∣ c := by
  constructor
  · intro h
    have h1 := congrArg (muDer p O n) h
    rw [map_smul, muDer_muT, map_zero, ← Algebra.algebraMap_eq_smul_one] at h1
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
  · rintro ⟨d, rfl⟩
    rw [mul_comm, mul_smul, (mu p O).pow_smul_cot n, smul_zero]
theorem dlogT_ne_zero (hp : ¬ IsUnit (p : O)) : dlogT p O ≠ 0 := fun h => by
  have h1 : (1 : O) • dUnit O (muT O (p ^ 1)) = 0 :=
    (one_smul _ _).trans (congrArg (fun w : (mu p O).omega => w.1 1) h)
  rw [smul_dUnit_muT_eq_zero_iff, pow_one] at h1
  exact hp (isUnit_of_dvd_one h1)
theorem toSpanSingleton_dlogT_bijective [IsAdicComplete (Ideal.span {(p : O)}) O] :
    Function.Bijective (LinearMap.toSpanSingleton O _ (dlogT p O)) := by
  have hm : ∀ (n : ℕ) (a b : O),
      a ≡ b [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔
        a • dUnit O (muT O (p ^ n)) = b • dUnit O (muT O (p ^ n)) := fun n a b => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, ← smul_dUnit_muT_eq_zero_iff, sub_smul, sub_eq_zero]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    refine IsHausdorff.haus' (I := Ideal.span {(p : O)}) c fun n => (hm n c 0).2 ?_
    rw [zero_smul]
    exact congrArg (fun w : (mu p O).omega => w.1 n) hc
  · intro w
    choose c hc using fun n => mu_cot_span p O n (w.1 n)
    have h1 : ∀ n, c n ≡ c (n + 1) [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] :=
      fun n => (hm n _ _).2 <| by
        rw [hc, ← w.2 n, ← hc, map_smul, cotMap_d, muRes_muT]
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) c fun {m n} hmn => by
      induction n, hmn using Nat.le_induction with
      | base => rfl
      | succ n hmn ih =>
        exact ih.trans ((h1 n).mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)))
    exact ⟨L, Subtype.ext (funext fun n => ((hm n _ _).1 (hL n)).symm.trans (hc n))⟩
def muOmegaEquiv [IsAdicComplete (Ideal.span {(p : O)}) O] : O ≃ₗ[O] (mu p O).omega :=
  LinearEquiv.ofBijective _ (toSpanSingleton_dlogT_bijective p O)
def muLieGen [IsAdicComplete (Ideal.span {(p : O)}) O] : (mu p O).Lie :=
  (muOmegaEquiv p O).symm.toLinearMap
example : (mu p O).height = 1 ∧ (const p O).height = 1 := ⟨rfl, rfl⟩
example : hodgeTate (const p O) (constGen p O) = constDlogT p O := by
  rw [hodgeTate_eq_omegaDualMap, show constHom _ (constGen p O) = 𝟙 _ by
    rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], omegaDualMap_id,
    LinearMap.id_apply]
example (t : (mu p O).Tate) : pairing (mu p O) O t (constGen p O) = t := by
  rw [pairing_apply, charHom_constGen, tateMap_id]
example (a : ℤ_[p]) (x : (mu p ℤ_[p]).Lie) :
    (padicAction (mu p ℤ_[p])).onLie a x = a • x ∧ dlogT p ℤ_[p] ≠ 0 := by
  refine ⟨?_, dlogT_ne_zero p ℤ_[p] PadicInt.prime_p.not_isUnit⟩
  change lieMap _ _ (algebraMap ℤ_[p] (End (mu p ℤ_[p])) a) x = _
  rw [Algebra.algebraMap_eq_smul_one]
  exact (LinearMap.congr_fun (lieMap_smul (RingHom.id _) a (𝟙 _)) x).trans (by simp)
end Values
end PDivGroup
end GlobalTheory


