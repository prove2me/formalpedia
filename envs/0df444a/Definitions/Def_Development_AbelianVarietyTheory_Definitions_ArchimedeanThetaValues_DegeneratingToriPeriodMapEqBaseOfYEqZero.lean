-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
-- name    : Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:07.864221+00:00
-- url     : https://prove2.me/theorems/7c171e07-a28d-414c-a3b9-da252e94747a
-- title:
--   Degenerating Tori Period Map Eq Base Of YEq Zero
-- statement:
--   Definitions and structural lemmas for Degenerating Tori Period Map Eq Base Of YEq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
structure AnArc (O : Type) [CommRing O] [StarRing O] where

  gB : ℕ

  abelian₂ : Submodule ℤ (Fin gB → ℂ)

  discrete : DiscreteTopology abelian₂

  full : Submodule.span ℝ (abelian₂ : Set (Fin gB → ℂ)) = ⊤

  Hm : Matrix (Fin gB) (Fin gB) ℂ

  Hm_herm : Hm.IsHermitian

  Hm_pos : ∀ z : Fin gB → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re

  Ef : LinearMap.BilinForm ℤ abelian₂

  Ef_eq : ∀ l m : abelian₂, (Ef l m : ℝ) = (hermForm Hm l m).im

  Ef_bij : Function.Bijective Ef

  chi : abelian₂ → ℂ

  chi_norm : ∀ l, ‖chi l‖ = 1

  chi_add : ∀ l m : abelian₂,
    chi (l + m) = chi l * chi m * Complex.exp (Real.pi * Complex.I * ((hermForm Hm l m).im : ℂ))

  chi_neg : ∀ l, chi (-l) = chi l

  F : O →+* Module.End ℂ (Fin gB → ℂ)

  F_mem : ∀ a, ∀ l ∈ abelian₂, F a l ∈ abelian₂

  F_adj : ∀ a z w, hermForm Hm (F a z) w = hermForm Hm z (F (star a) w)

  X : Type
  [acg : AddCommGroup X]
  [free : Module.Free ℤ X]
  [fin : Module.Finite ℤ X]
  [mod : Module O X]

  ct : X →+ (Fin gB → ℂ)

  ct_smul : ∀ (a : O) x, ct (a • x) = F a (ct x)

  T : X →+ X →+ ℂ

  T_symm : ∀ x y, T x y = T y x

  T_adj : ∀ (a : O) y x, T (a • y) x = T y (star a • x)

  psi : X → ℂˣ

  psi_neg : ∀ x, psi (-x) = psi x

  psi_add : ∀ x y, (psi (x + y) : ℂ) = psi x * psi y * eTwoPi (T x y)

  be : LinearMap.BilinForm ℤ X

  be_symm : ∀ x y, be x y = be y x

  be_pos : ∀ x, x ≠ 0 → 0 < be x x

  be_adj : ∀ (a : O) y x, be (a • y) x = be y (star a • x)

  be_even : ∀ x, (2 : ℤ) ∣ be x x
attribute [instance] AnArc.acg AnArc.free AnArc.fin AnArc.mod AnArc.discrete
namespace AnArc
theorem e_add (x y : ℂ) : eTwoPi (x + y) = eTwoPi x * eTwoPi y := by
  simp only [eTwoPi, mul_add, Complex.exp_add]
@[simp] theorem e_zero : eTwoPi 0 = 1 := by simp [eTwoPi]
theorem e_ne_zero (x : ℂ) : eTwoPi x ≠ 0 := Complex.exp_ne_zero _
@[simp] theorem e_intCast (n : ℤ) : eTwoPi n = 1 := by
  rw [eTwoPi, mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I n
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
def H (z w : Fin A.gB → ℂ) : ℂ := hermForm A.Hm z w
theorem H_add_left (z z' w : Fin A.gB → ℂ) : A.H (z + z') w = A.H z w + A.H z' w := by
  simp [H, hermForm, add_dotProduct]
theorem H_add_right (z w w' : Fin A.gB → ℂ) : A.H z (w + w') = A.H z w + A.H z w' := by
  simp [H, hermForm, Matrix.mulVec_add, dotProduct_add]
@[simp] theorem H_zero_left (w : Fin A.gB → ℂ) : A.H 0 w = 0 := by simp [H, hermForm]
@[simp] theorem H_zero_right (z : Fin A.gB → ℂ) : A.H z 0 = 0 := by simp [H, hermForm]
theorem H_conj (z w : Fin A.gB → ℂ) : starRingEnd ℂ (A.H z w) = A.H w z := by
  have h : ∀ i k, starRingEnd ℂ (A.Hm i k) = A.Hm k i := fun i k => A.Hm_herm.apply k i
  simp only [H, hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, h, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
theorem H_self_im (z : Fin A.gB → ℂ) : (A.H z z).im = 0 := by
  have := congrArg Complex.im (A.H_conj z z)
  rw [Complex.conj_im] at this
  linarith
theorem Ef_eq_im (l m : A.abelian₂) : (A.Ef l m : ℝ) = (A.H l m).im := A.Ef_eq l m
@[simp] theorem Ef_self (l : A.abelian₂) : A.Ef l l = 0 := by
  have := A.Ef_eq_im l l
  rw [H_self_im] at this
  exact_mod_cast this
@[simp] theorem chi_zero : A.chi 0 = 1 := by
  have h := A.chi_add 0 0
  have h0 : A.chi 0 ≠ 0 := by
    intro h0
    have := A.chi_norm 0
    simp [h0] at this
  have hz : hermForm A.Hm ((0 : A.abelian₂) : Fin A.gB → ℂ) (0 : A.abelian₂) = 0 := A.H_zero_left _
  rw [add_zero, hz] at h
  simp only [Complex.zero_im, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
  exact (mul_eq_left₀ h0).1 h.symm
@[simp] theorem psi_zero : A.psi 0 = 1 := by
  have h := A.psi_add 0 0
  simp only [add_zero, map_zero, e_zero, mul_one] at h
  exact Units.ext ((mul_eq_left₀ (A.psi 0).ne_zero).1 h.symm)
def FLam (a : O) (l : A.abelian₂) : A.abelian₂ := ⟨A.F a l, A.F_mem a l l.2⟩
@[simp] theorem coe_FLam (a : O) (l : A.abelian₂) : (A.FLam a l : Fin A.gB → ℂ) = A.F a l := rfl
def coord : (A.X →+ ℂ) ≃ₗ[ℂ] (Module.Free.ChooseBasisIndex ℤ A.X → ℂ) where
  toFun l i := l (Module.Free.chooseBasis ℤ A.X i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ((Module.Free.chooseBasis ℤ A.X).constr ℤ f).toAddMonoidHom
  left_inv l := by
    have : (Module.Free.chooseBasis ℤ A.X).constr ℤ (fun i => l (Module.Free.chooseBasis ℤ A.X i)) =
        l.toIntLinearMap := (Module.Free.chooseBasis ℤ A.X).ext fun i => by simp
    ext x
    simp [this]
  right_inv f := by
    funext i
    simp
instance : NormedAddCommGroup (A.X →+ ℂ) :=
  NormedAddCommGroup.induced _ _ A.coord.toLinearMap A.coord.injective
instance : NormedSpace ℂ (A.X →+ ℂ) := NormedSpace.induced ℂ _ _ A.coord.toLinearMap
instance : NormedSpace ℝ (A.X →+ ℂ) where
  norm_smul_le r l := norm_smul_le r (A.coord l)
instance : FiniteDimensional ℂ (A.X →+ ℂ) := A.coord.symm.finiteDimensional
instance : FiniteDimensional ℝ (A.X →+ ℂ) := Module.Finite.trans ℂ _
instance : CompleteSpace (A.X →+ ℂ) := FiniteDimensional.complete ℂ _
theorem finrank_hom : Module.finrank ℂ (A.X →+ ℂ) = Module.finrank ℤ A.X := by
  rw [A.coord.finrank_eq, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_chooseBasisIndex]
def evalCLM (x : A.X) : (A.X →+ ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun l => l x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
@[simp] theorem evalCLM_apply (x : A.X) (l : A.X →+ ℂ) : A.evalCLM x l = l x := rfl
abbrev V : Type := (A.X →+ ℂ) × (Fin A.gB → ℂ)
theorem finrank_V : Module.finrank ℂ A.V = Module.finrank ℤ A.X + A.gB := by
  rw [Module.finrank_prod, finrank_hom, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
def actV : O →+* Module.End ℂ A.V where
  toFun a :=
    { toFun := fun v => (v.1.comp (DistribSMul.toAddMonoidHom A.X (star a)), A.F a v.2)
      map_add' := fun v v' => by ext <;> simp
      map_smul' := fun c v => by ext <;> simp }
  map_one' := by ext <;> simp
  map_mul' a b := by
    refine LinearMap.ext fun v => Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · show v.1 (star (a * b) • x) = v.1 (star b • star a • x)
      rw [star_mul, mul_smul]
    · simp
  map_zero' := by ext <;> simp
  map_add' a b := by
    refine LinearMap.ext fun v => Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · simp [add_smul]
    · simp
@[simp] theorem actV_fst_apply (a : O) (v : A.V) (x : A.X) : (A.actV a v).1 x = v.1 (star a • x) := rfl
@[simp] theorem actV_snd (a : O) (v : A.V) : (A.actV a v).2 = A.F a v.2 := rfl
abbrev moduleV : Module O A.V := Module.compHom A.V A.actV
def La : Type := A.X × (A.X →+ ℤ) × A.abelian₂
instance : AddCommGroup A.La := inferInstanceAs (AddCommGroup (A.X × (A.X →+ ℤ) × A.abelian₂))
namespace La
variable {A}
def mk (y : A.X) (n : A.X →+ ℤ) (l : A.abelian₂) : A.La := (y, n, l)
def y (v : A.La) : A.X := Prod.fst v
def n (v : A.La) : A.X →+ ℤ := (Prod.snd v).1
def l (v : A.La) : A.abelian₂ := (Prod.snd v).2
@[simp] theorem mk_y (y : A.X) (n : A.X →+ ℤ) (l : A.abelian₂) : (mk y n l).y = y := rfl
@[simp] theorem mk_n (y : A.X) (n : A.X →+ ℤ) (l : A.abelian₂) : (mk y n l).n = n := rfl
@[simp] theorem mk_l (y : A.X) (n : A.X →+ ℤ) (l : A.abelian₂) : (mk y n l).l = l := rfl
@[simp] theorem mk_eta (v : A.La) : mk v.y v.n v.l = v := rfl
@[ext] theorem ext {v v' : A.La} (hy : v.y = v'.y) (hn : v.n = v'.n) (hl : v.l = v'.l) : v = v' :=
  Prod.ext hy (Prod.ext hn hl)
@[simp] theorem zero_y : (0 : A.La).y = 0 := rfl
@[simp] theorem zero_n : (0 : A.La).n = 0 := rfl
@[simp] theorem zero_l : (0 : A.La).l = 0 := rfl
@[simp] theorem add_y (v v' : A.La) : (v + v').y = v.y + v'.y := rfl
@[simp] theorem add_n (v v' : A.La) : (v + v').n = v.n + v'.n := rfl
@[simp] theorem add_l (v v' : A.La) : (v + v').l = v.l + v'.l := rfl
@[simp] theorem neg_y (v : A.La) : (-v).y = -v.y := rfl
@[simp] theorem neg_n (v : A.La) : (-v).n = -v.n := rfl
@[simp] theorem neg_l (v : A.La) : (-v).l = -v.l := rfl
@[simp] theorem sub_y (v v' : A.La) : (v - v').y = v.y - v'.y := rfl
@[simp] theorem sub_n (v v' : A.La) : (v - v').n = v.n - v'.n := rfl
@[simp] theorem sub_l (v v' : A.La) : (v - v').l = v.l - v'.l := rfl
@[simp] theorem zsmul_y (k : ℤ) (v : A.La) : (k • v).y = k • v.y := rfl
@[simp] theorem zsmul_n (k : ℤ) (v : A.La) : (k • v).n = k • v.n := rfl
@[simp] theorem zsmul_l (k : ℤ) (v : A.La) : (k • v).l = k • v.l := rfl
@[simp] theorem nsmul_y (k : ℕ) (v : A.La) : (k • v).y = k • v.y := rfl
@[simp] theorem nsmul_n (k : ℕ) (v : A.La) : (k • v).n = k • v.n := rfl
@[simp] theorem nsmul_l (k : ℕ) (v : A.La) : (k • v).l = k • v.l := rfl
end La
def laEquiv : A.La ≃ₗ[ℤ] A.X × (A.X →+ ℤ) × A.abelian₂ where
  toFun v := (v.y, v.n, v.l)
  invFun p := La.mk p.1 p.2.1 p.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
instance : IsZLattice ℝ A.abelian₂ := ⟨A.full⟩
instance : Module.Finite ℤ A.abelian₂ := ZLattice.module_finite ℝ A.abelian₂
instance : Module.Free ℤ A.abelian₂ := ZLattice.module_free ℝ A.abelian₂
instance : Module.Finite ℤ A.La := Module.Finite.equiv A.laEquiv.symm
instance : Module.Free ℤ A.La := Module.Free.of_equiv A.laEquiv.symm
instance (priority := low) : SMul O A.La where
  smul a v := La.mk (a • v.y) (v.n.comp (DistribSMul.toAddMonoidHom A.X (star a))) (A.FLam a v.l)
namespace La
variable {A}
@[simp] theorem smul_y (a : O) (v : A.La) : (a • v).y = a • v.y := rfl
@[simp] theorem smul_n_apply (a : O) (v : A.La) (x : A.X) : (a • v).n x = v.n (star a • x) := rfl
@[simp] theorem smul_l (a : O) (v : A.La) : (a • v).l = A.FLam a v.l := rfl
end La
instance (priority := low) : Module O A.La where
  one_smul v := by ext <;> simp
  mul_smul a b v := by
    refine La.ext (by simp [mul_smul]) (AddMonoidHom.ext fun x => ?_) (Subtype.ext (by simp))
    simp only [La.smul_n_apply]
    rw [star_mul, mul_smul]
  smul_zero a := by ext <;> simp
  smul_add a v v' := by ext <;> simp
  add_smul a b v := by ext <;> simp [add_smul]
  zero_smul v := by ext <;> simp
def yLin : A.La →ₗ[O] A.X where
  toFun := La.y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem yLin_apply (v : A.La) : A.yLin v = v.y := rfl
def P0 : A.La →+ A.V where
  toFun v :=
    ({ toFun := fun x => A.T v.y x + v.n x - A.H (A.ct x) v.l / (2 * Complex.I)
       map_zero' := by simp
       map_add' := fun x x' => by simp only [map_add, H_add_left]; push_cast; ring },
      A.ct v.y + v.l)
  map_zero' := by ext <;> simp
  map_add' v v' := by
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · simp only [La.add_y, La.add_n, La.add_l, map_add, AddMonoidHom.add_apply, Submodule.coe_add, H_add_right,
        Prod.fst_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      push_cast; ring
    · simp only [La.add_y, La.add_l, map_add, Submodule.coe_add, Prod.snd_add]
      abel
@[simp] theorem degeneratingTori_basePeriodMap_fst_apply (v : A.La) (x : A.X) :
    (A.P0 v).1 x = A.T v.y x + v.n x - A.H (A.ct x) v.l / (2 * Complex.I) := rfl
@[simp] theorem degeneratingTori_basePeriodMap_snd (v : A.La) : (A.P0 v).2 = A.ct v.y + v.l := rfl
def N : A.La →+ A.V where
  toFun v := ((Int.castAddHom ℂ).comp (A.be v.y).toAddMonoidHom, 0)
  map_zero' := by ext <;> simp
  map_add' v v' := by ext <;> simp
@[simp] theorem N_fst_apply (v : A.La) (x : A.X) : (A.N v).1 x = A.be v.y x := rfl
@[simp] theorem N_snd (v : A.La) : (A.N v).2 = 0 := rfl
def Pw (w : ℂ) : A.La →+ A.V := A.P0 + w • A.N
theorem Pw_apply (w : ℂ) (v : A.La) : A.Pw w v = A.P0 v + w • A.N v := rfl
@[simp] theorem Pw_fst_apply (w : ℂ) (v : A.La) (x : A.X) :
    (A.Pw w v).1 x = A.T v.y x + v.n x - A.H (A.ct x) v.l / (2 * Complex.I) + w * A.be v.y x := rfl
@[simp] theorem Pw_snd (w : ℂ) (v : A.La) : (A.Pw w v).2 = A.ct v.y + v.l := by
  simp [Pw_apply]
def nn : A.La →ₗ[O] A.La where
  toFun v := La.mk 0 (A.be v.y).toAddMonoidHom 0
  map_add' v v' := by ext <;> simp
  map_smul' a v := by ext <;> simp [A.be_adj]
def EF : LinearMap.BilinForm ℤ A.La :=
  LinearMap.mk₂ ℤ (fun v v' => v'.n v.y - v.n v'.y + A.Ef v.l v'.l)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring)
def ah (l : A.abelian₂) (z : Fin A.gB → ℂ) : ℂ :=
  A.chi l * Complex.exp (Real.pi * A.H z l + Real.pi / 2 * A.H l l)
def Theta (j : ℕ) (α : A.X) : Submodule ℂ ((Fin A.gB → ℂ) → ℂ) where
  carrier := {th | Differentiable ℂ th ∧ ∀ (l : A.abelian₂) z,
    th (z + l) = A.ah l z ^ j * Complex.exp (Real.pi * A.H (A.ct α) l) * th z}
  zero_mem' := ⟨differentiable_const 0, fun _ _ => by simp⟩
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun l z => by
    simp only [Pi.add_apply, ha.2 l z, hb.2 l z]; ring⟩
  smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun l z => by
    simp only [Pi.smul_apply, smul_eq_mul, ha.2 l z]; ring⟩
def term (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ : A.X) (v : A.V) : ℂ :=
  (A.psi μ : ℂ) ^ j * eTwoPi (A.T μ α) * eTwoPi (v.1 (α + j • μ)) * th (v.2 + A.ct μ)
def q (μ : A.X) : ℤ := A.be μ μ / 2
theorem two_mul_q (μ : A.X) : 2 * A.q μ = A.be μ μ := Int.mul_ediv_cancel' (A.be_even μ)
@[simp] theorem q_zero : A.q 0 = 0 := by simp [q]
@[simp] theorem q_neg (μ : A.X) : A.q (-μ) = A.q μ := by simp [q]
theorem be_self_nonneg (μ : A.X) : 0 ≤ A.be μ μ := by
  by_cases h : μ = 0
  · simp [h]
  · exact (A.be_pos μ h).le
def exponent (j : ℕ) (α μ : A.X) : ℤ := j * A.q μ + A.be μ α
theorem two_mul_exponent (j : ℕ) (α μ : A.X) :
    2 * A.exponent j α μ = j * A.be μ μ + 2 * A.be μ α := by
  rw [exponent, ← two_mul_q]; ring
def Sum (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (w : ℂ) (v : A.V) : ℂ :=
  ∑' μ : A.X, A.term j α th μ v * eTwoPi (w * A.exponent j α μ)
theorem finite_be_le (R : ℤ) : {μ : A.X | A.be μ μ ≤ R}.Finite := by
  classical
  let b := Module.Free.chooseBasis ℤ A.X
  let f : A.X → (Module.Free.ChooseBasisIndex ℤ A.X → ℤ) := fun μ i => A.be μ (b i)
  have hf : Function.Injective f := by
    intro μ ν h
    have h0 : A.be (μ - ν) = 0 := b.ext fun i => by
      have := congrFun h i
      simp only [f] at this
      simp [this]
    by_contra hne
    have := A.be_pos _ (sub_ne_zero.2 hne)
    rw [h0] at this
    simp at this
  refine Set.Finite.of_finite_image ?_ hf.injOn
  refine (Set.finite_Icc (fun i => -(R + A.be (b i) (b i))) (fun i => R + A.be (b i) (b i))).subset ?_
  rintro _ ⟨μ, hμ, rfl⟩
  have hμ' : A.be μ μ ≤ R := hμ
  have h0 := A.be_self_nonneg μ
  have key : ∀ i, -(R + A.be (b i) (b i)) ≤ A.be μ (b i) ∧ A.be μ (b i) ≤ R + A.be (b i) (b i) := fun i => by
    have h1 := A.be_self_nonneg (μ + b i)
    have h2 := A.be_self_nonneg (μ - b i)
    have h3 := A.be_self_nonneg (b i)
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, A.be_symm (b i) μ] at h1 h2
    constructor <;> omega
  exact ⟨fun i => (key i).1, fun i => (key i).2⟩
theorem be_le_exponent {j : ℕ} (hj : j ≠ 0) (α μ : A.X) :
    A.be μ μ ≤ 4 * (A.exponent j α μ + A.be α α) := by
  have h1 := A.two_mul_exponent j α μ
  have h2 := A.be_self_nonneg (μ + (α + α))
  have h0 := A.be_self_nonneg μ
  simp only [map_add, LinearMap.add_apply, A.be_symm α μ] at h2
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
  nlinarith [mul_le_mul_of_nonneg_right hj' h0]
theorem neg_be_le_exponent {j : ℕ} (hj : j ≠ 0) (α μ : A.X) : -A.be α α ≤ A.exponent j α μ := by
  have h1 := A.be_le_exponent hj α μ
  have h0 := A.be_self_nonneg μ
  omega
theorem finite_exponent_le {j : ℕ} (hj : j ≠ 0) (α : A.X) (n : ℤ) : {μ | A.exponent j α μ ≤ n}.Finite :=
  (A.finite_be_le (4 * (n + A.be α α))).subset fun μ hμ => by
    have h1 := A.be_le_exponent hj α μ
    have h2 : A.exponent j α μ ≤ n := hμ
    show A.be μ μ ≤ _
    omega
theorem finite_exponent_eq {j : ℕ} (hj : j ≠ 0) (α : A.X) (n : ℤ) : {μ | A.exponent j α μ = n}.Finite :=
  (A.finite_exponent_le hj α n).subset fun _ hμ => le_of_eq hμ
def level (j : ℕ) [NeZero j] (α : A.X) (n : ℤ) : Finset A.X := (A.finite_exponent_eq (NeZero.ne j) α n).toFinset
@[simp] theorem mem_level {j : ℕ} [NeZero j] {α : A.X} {n : ℤ} {μ : A.X} :
    μ ∈ A.level j α n ↔ A.exponent j α μ = n := by simp [level]
theorem level_eq_empty {j : ℕ} [NeZero j] {α : A.X} {n : ℤ} (hn : n < -A.be α α) : A.level j α n = ∅ :=
  Finset.eq_empty_of_forall_notMem fun μ hμ => by
    have h1 := A.neg_be_le_exponent (NeZero.ne j) α μ
    rw [mem_level] at hμ
    omega
def FSum (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) : LaurentSeries ℂ :=
  HahnSeries.ofSuppBddBelow (fun n => ∑ μ ∈ A.level j α n, A.term j α th μ v)
    ⟨-A.be α α, fun n hn => by
      by_contra h
      exact hn (by simp only [A.level_eq_empty (not_le.1 h), Finset.sum_empty])⟩
def beInt : LinearMap.BilinForm ℤ ℤ :=
  LinearMap.mk₂ ℤ (fun x y => 2 * x * y) (fun _ _ _ => by ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by ring) (fun _ _ _ => by simp; ring)
@[simp] theorem beInt_apply (x y : ℤ) : beInt x y = 2 * x * y := rfl
def TInt (τ₀ : ℂ) : ℤ →+ ℤ →+ ℂ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => τ₀ * x * y) (fun _ _ => by push_cast; ring))
    (fun _ _ => by ext; simp; ring)
@[simp] theorem TInt_apply (τ₀ : ℂ) (x y : ℤ) : TInt τ₀ x y = τ₀ * x * y := rfl
def psiInt (τ₀ : ℂ) (x : ℤ) : ℂˣ := Units.mk0 (eTwoPi (τ₀ * x ^ 2 / 2)) (e_ne_zero _)
@[simp] theorem coe_psiInt (τ₀ : ℂ) (x : ℤ) : (psiInt τ₀ x : ℂ) = eTwoPi (τ₀ * x ^ 2 / 2) := rfl
theorem psiInt_neg (τ₀ : ℂ) (x : ℤ) : psiInt τ₀ (-x) = psiInt τ₀ x := Units.ext (by simp)
theorem psiInt_add (τ₀ : ℂ) (x y : ℤ) :
    (psiInt τ₀ (x + y) : ℂ) = psiInt τ₀ x * psiInt τ₀ y * eTwoPi (TInt τ₀ x y) := by
  simp only [coe_psiInt, TInt_apply, ← e_add]
  congr 1; push_cast; ring
def tate (τ₀ : ℂ) : AnArc ℤ where
  gB := 0
  abelian₂ := ⊥
  discrete := inferInstance
  full := Subsingleton.elim _ _
  Hm := 0
  Hm_herm := Matrix.isHermitian_zero
  Hm_pos z hz := absurd (Subsingleton.elim _ _) hz
  Ef := 0
  Ef_eq l m := by simp [hermForm]
  Ef_bij := ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  chi _ := 1
  chi_norm _ := norm_one
  chi_add l m := by simp [hermForm]
  chi_neg _ := rfl
  F := Int.castRingHom _
  F_mem a l _ := Subsingleton.elim (α := Fin 0 → ℂ) _ _
  F_adj a z w := by simp [hermForm]
  X := ℤ
  ct := 0
  ct_smul _ _ := Subsingleton.elim _ _
  T := TInt τ₀
  T_symm x y := by simp only [TInt_apply]; ring
  T_adj a y x := by simp; ring
  psi := psiInt τ₀
  psi_neg := psiInt_neg τ₀
  psi_add := psiInt_add τ₀
  be := beInt
  be_symm x y := by simp only [beInt_apply]; ring
  be_pos x hx := by simp only [beInt_apply]; have := mul_self_pos.2 hx; linarith
  be_adj a y x := by simp; ring
  be_even x := ⟨x * x, by simp only [beInt_apply]; ring⟩
def gaussEmb : GaussianInt →ₗ[ℤ] (Fin 1 → ℂ) where
  toFun a _ := a
  map_add' a b := by ext; simp
  map_smul' k a := by ext; simp
@[simp] theorem gaussEmb_apply (a : GaussianInt) (i : Fin 1) : gaussEmb a i = a := rfl
def gaussLam : Submodule ℤ (Fin 1 → ℂ) := LinearMap.range gaussEmb
def gaussEquiv : GaussianInt ≃ₗ[ℤ] gaussLam :=
  LinearEquiv.ofInjective gaussEmb fun _ _ h => GaussianInt.toComplex_injective (congrFun h 0)
@[simp] theorem coe_gaussEquiv (a : GaussianInt) : (gaussEquiv a : Fin 1 → ℂ) = gaussEmb a := rfl
theorem hermForm_one (z w : Fin 1 → ℂ) : hermForm 1 z w = z 0 * starRingEnd ℂ (w 0) := by
  simp [hermForm, dotProduct]
def gaussForm : LinearMap.BilinForm ℤ GaussianInt :=
  LinearMap.mk₂ ℤ (fun a b => a.im * b.re - a.re * b.im) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
@[simp] theorem gaussForm_apply (a b : GaussianInt) : gaussForm a b = a.im * b.re - a.re * b.im := rfl
def gaussEf : LinearMap.BilinForm ℤ gaussLam := LinearMap.BilinForm.congr gaussEquiv gaussForm
@[simp] theorem gaussEf_apply (a b : GaussianInt) :
    gaussEf (gaussEquiv a) (gaussEquiv b) = a.im * b.re - a.re * b.im := by simp [gaussEf]
theorem gaussEf_eq (l m : gaussLam) : (gaussEf l m : ℝ) = (hermForm 1 (l : Fin 1 → ℂ) m).im := by
  obtain ⟨a, rfl⟩ := gaussEquiv.surjective l
  obtain ⟨b, rfl⟩ := gaussEquiv.surjective m
  rw [gaussEf_apply, hermForm_one]
  simp; ring
theorem gaussEf_bij : Function.Bijective gaussEf := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro l hl
    obtain ⟨a, rfl⟩ := gaussEquiv.surjective l
    have h1 := gaussEf_apply a 1
    have h2 := gaussEf_apply a ⟨0, 1⟩
    rw [hl] at h1 h2
    have : a = 0 := by ext <;> simp at h1 h2 ⊢ <;> omega
    simp [this]
  · intro φ
    refine ⟨gaussEquiv ⟨-φ (gaussEquiv ⟨0, 1⟩), φ (gaussEquiv 1)⟩, LinearMap.ext fun m => ?_⟩
    obtain ⟨b, rfl⟩ := gaussEquiv.surjective m
    have hb : b = b.re • (1 : GaussianInt) + b.im • (⟨0, 1⟩ : GaussianInt) := by ext <;> simp
    rw [gaussEf_apply]
    conv_rhs => rw [hb, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_zsmul]
    simp; ring
theorem gaussLam_discrete : DiscreteTopology gaussLam := by
  refine DiscreteTopology.of_forall_le_norm one_pos fun l hl => ?_
  obtain ⟨a, rfl⟩ := gaussEquiv.surjective l
  have ha : a ≠ 0 := by rintro rfl; simp at hl
  have h1 : (1 : ℝ) ≤ Complex.normSq a := by
    rw [← GaussianInt.intCast_real_norm]
    exact_mod_cast GaussianInt.norm_pos.2 ha
  have h2 : (1 : ℝ) ≤ ‖(a : ℂ)‖ := by
    rw [Complex.normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg (a : ℂ)]
  exact h2.trans (norm_le_pi_norm (gaussEmb a) 0)
theorem gaussLam_full : Submodule.span ℝ (gaussLam : Set (Fin 1 → ℂ)) = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  have hz : z = (z 0).re • gaussEmb 1 + (z 0).im • gaussEmb ⟨0, 1⟩ := by
    funext i
    rw [Subsingleton.elim i 0]
    simp [GaussianInt.toComplex_def']
  rw [hz]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
def gaussChi (l : gaussLam) : ℂ :=
  Complex.exp (Real.pi * Complex.I * ((l.1 0).re * (l.1 0).im : ℝ))
theorem gaussChi_norm (l : gaussLam) : ‖gaussChi l‖ = 1 := by
  rw [gaussChi, mul_right_comm, ← Complex.ofReal_mul]
  exact Complex.norm_exp_ofReal_mul_I _
theorem gaussChi_add (l m : gaussLam) : gaussChi (l + m) =
    gaussChi l * gaussChi m * Complex.exp (Real.pi * Complex.I * ((hermForm 1 (l : Fin 1 → ℂ) m).im : ℂ)) := by
  rw [← gaussEf_eq]
  obtain ⟨a, rfl⟩ := gaussEquiv.surjective l
  obtain ⟨b, rfl⟩ := gaussEquiv.surjective m
  rw [gaussEf_apply, gaussChi, gaussChi, gaussChi, ← Complex.exp_add, ← Complex.exp_add,
    Complex.exp_eq_exp_iff_exists_int]
  refine ⟨a.re * b.im, ?_⟩
  simp [← GaussianInt.intCast_re, ← GaussianInt.intCast_im]; ring
theorem gaussChi_neg (l : gaussLam) : gaussChi (-l) = gaussChi l := by simp [gaussChi]
theorem hermForm_one_pos (z : Fin 1 → ℂ) (hz : z ≠ 0) : 0 < (hermForm 1 z z).re := by
  have h : z 0 ≠ 0 := fun h => hz (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
  rw [hermForm_one, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_pos.2 h
def gaussInt (c τ₀ : ℂ) : AnArc ℤ where
  gB := 1
  abelian₂ := gaussLam
  discrete := gaussLam_discrete
  full := gaussLam_full
  Hm := 1
  Hm_herm := Matrix.isHermitian_one
  Hm_pos := hermForm_one_pos
  Ef := gaussEf
  Ef_eq := gaussEf_eq
  Ef_bij := gaussEf_bij
  chi := gaussChi
  chi_norm := gaussChi_norm
  chi_add := gaussChi_add
  chi_neg := gaussChi_neg
  F := Int.castRingHom _
  F_mem a l hl := by simpa using gaussLam.smul_mem a hl
  F_adj a z w := by simp [hermForm_one]; ring
  X := ℤ
  ct := AddMonoidHom.mk' (fun x _ => x * c) fun _ _ => by ext; simp; ring
  ct_smul a x := by ext; simp; ring
  T := TInt τ₀
  T_symm x y := by simp only [TInt_apply]; ring
  T_adj a y x := by simp; ring
  psi := psiInt τ₀
  psi_neg := psiInt_neg τ₀
  psi_add := psiInt_add τ₀
  be := beInt
  be_symm x y := by simp only [beInt_apply]; ring
  be_pos x hx := by simp only [beInt_apply]; have := mul_self_pos.2 hx; linarith
  be_adj a y x := by simp; ring
  be_even x := ⟨x * x, by simp only [beInt_apply]; ring⟩
def gaussProd : (ℤ × ℤ) ≃ₗ[ℤ] GaussianInt where
  toFun p := ⟨p.1, p.2⟩
  invFun a := (a.re, a.im)
  map_add' _ _ := rfl
  map_smul' _ _ := by ext <;> simp
  left_inv _ := rfl
  right_inv _ := rfl
def beGauss : LinearMap.BilinForm ℤ GaussianInt :=
  LinearMap.mk₂ ℤ (fun a b => 2 * (a.re * b.re + a.im * b.im)) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
@[simp] theorem beGauss_apply (a b : GaussianInt) : beGauss a b = 2 * (a.re * b.re + a.im * b.im) := rfl
def gaussCM (c τ₀ : ℂ) : AnArc GaussianInt where
  gB := 1
  abelian₂ := gaussLam
  discrete := gaussLam_discrete
  full := gaussLam_full
  Hm := 1
  Hm_herm := Matrix.isHermitian_one
  Hm_pos := hermForm_one_pos
  Ef := gaussEf
  Ef_eq := gaussEf_eq
  Ef_bij := gaussEf_bij
  chi := gaussChi
  chi_norm := gaussChi_norm
  chi_add := gaussChi_add
  chi_neg := gaussChi_neg
  F := (algebraMap ℂ _).comp GaussianInt.toComplex
  F_mem := by
    rintro a _ ⟨b, rfl⟩
    exact ⟨a * b, by ext; simp⟩
  F_adj a z w := by simp [hermForm_one]; ring
  X := GaussianInt
  free := Module.Free.of_equiv gaussProd
  fin := Module.Finite.equiv gaussProd
  ct := AddMonoidHom.mk' (fun x _ => x * c) fun _ _ => by ext; simp; ring
  ct_smul a x := by ext; simp; ring
  T := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => τ₀ * beGauss x y) fun _ _ => by simp; ring)
    fun _ _ => by ext; simp; ring
  T_symm x y := by
    show τ₀ * (beGauss x y : ℤ) = τ₀ * (beGauss y x : ℤ)
    congr 2; simp only [beGauss_apply]; ring
  T_adj a y x := by
    show τ₀ * (beGauss (a • y) x : ℤ) = τ₀ * (beGauss y (star a • x) : ℤ)
    congr 2; simp; ring
  psi x := Units.mk0 (eTwoPi (τ₀ * (x.re ^ 2 + x.im ^ 2))) (e_ne_zero _)
  psi_neg x := Units.ext (by simp)
  psi_add x y := by
    simp only [Units.val_mk0, ← e_add]
    congr 1; simp; ring
  be := beGauss
  be_symm x y := by simp only [beGauss_apply]; ring
  be_pos x hx := by
    have := GaussianInt.norm_pos.2 hx
    simp only [beGauss_apply]
    rw [Zsqrtd.norm_def] at this
    linarith
  be_adj a y x := by simp; ring
  be_even x := ⟨_, rfl⟩
example (c τ₀ : ℂ) (v : (gaussCM c τ₀).La) :
    ((⟨0, 1⟩ : GaussianInt) • v).n (1 : GaussianInt) = v.n (⟨0, -1⟩ : GaussianInt) := by
  refine congrArg v.n ?_
  show star (⟨0, 1⟩ : GaussianInt) * 1 = ⟨0, -1⟩
  ext <;> simp
example (τ₀ : ℂ) : Module.finrank ℂ (tate τ₀).V = 1 := by
  rw [finrank_V]
  exact congrArg (· + 0) (Module.finrank_self ℤ)
example : (NormedSpace.toModule : Module ℝ A.V) =
    @Prod.instModule ℝ _ _ _ _ _ AddMonoidHom.instModule (Pi.Function.module _ _ _) := by
  with_reducible_and_instances rfl
example : CompleteSpace A.V ∧ FiniteDimensional ℂ A.V ∧ FiniteDimensional ℝ A.V ∧ IsScalarTower ℝ ℂ A.V :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
end AnArc
end GlobalTheory


