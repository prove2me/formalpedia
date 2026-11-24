-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T17:53:26.85886+00:00
-- url     : https://prove2.me/theorems/4758cd13-7dcd-4bb6-bbe0-3a779c81abaa
-- title:
--   Inst Tame Descent Exponent Data Padic Three
-- statement:
--   Definitions and structural lemmas for Inst Tame Descent Exponent Data Padic Three, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InstTameDescentExponentDataPadicThree.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_plus_phi_join
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_coeff_frob
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_mem_tot
import Theorems.Thm_GlobalTheory_BK_mem_uPow_iff_exists
import Theorems.Thm_GlobalTheory_BK_mem_uPow_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BK
open PowerSeries Filter Topology Matrix
class TameDescentExponentData (K : Type) [NormedField K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] :
    Prop where
  succ_eq : e + 1 = l ^ a
  not_dvd : ¬ l ∣ a
  finite : FiniteDimensional ℚ_[l] K
  prim : ∃ ζ : K, IsPrimitiveRoot ζ e
instance instTameDescentExponentDataPadicThree : TameDescentExponentData ℚ_[3] 3 2 1 where
  succ_eq := rfl
  not_dvd := by decide
  finite := inferInstance
  prim := ⟨-1, IsPrimitiveRoot.neg_one 0 (by decide)⟩
section Group
variable {K : Type} [NormedField K] (l : ℕ) {e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero a] [TameDescentExponentData K l e a]
omit [NeZero a] in
theorem pow_pow_mod (ζ : rootsOfUnity e K) (n : ℕ) : ζ ^ l ^ (n % a) = ζ ^ l ^ n := by
  have h1 : ζ ^ e = 1 := Subtype.ext ζ.2
  have h2 (k : ℕ) : ζ ^ (l ^ a) ^ k = ζ := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, ← TameDescentExponentData.succ_eq (K := K) (e := e), pow_succ, h1, one_mul]
  conv_rhs => rw [← Nat.div_add_mod n a, pow_add, pow_mul l, pow_mul, h2]
def powL (s : ZMod a) : rootsOfUnity e K →* rootsOfUnity e K := powMonoidHom (l ^ s.val)
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] in
theorem powL_apply (s : ZMod a) (ζ : rootsOfUnity e K) : powL l s ζ = ζ ^ l ^ s.val := rfl
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] in
@[simp] theorem powL_zero (ζ : rootsOfUnity e K) : powL l (0 : ZMod a) ζ = ζ := by simp [powL_apply]
theorem powL_add (s t : ZMod a) (ζ : rootsOfUnity e K) :
    powL l (s + t) ζ = powL l s (powL l t ζ) := by
  rw [powL_apply, powL_apply, powL_apply, ZMod.val_add, pow_pow_mod l, ← pow_mul, ← pow_add, add_comm]
omit [NeZero a] in
theorem powL_one (ζ : rootsOfUnity e K) : powL l (1 : ZMod a) ζ = ζ ^ l := by
  rw [powL_apply, ZMod.val_one_eq_one_mod, pow_pow_mod l, pow_one]
variable (K e a) in

def frobAut : Multiplicative (ZMod a) →* MulAut (rootsOfUnity e K) where
  toFun s :=
    { powL l s.toAdd with
      invFun := powL l (-s.toAdd)
      left_inv := fun ζ => ((powL_add l _ _ ζ).symm.trans (by simp))
      right_inv := fun ζ => ((powL_add l _ _ ζ).symm.trans (by simp)) }
  map_one' := MulEquiv.ext fun ζ => powL_zero l ζ
  map_mul' s t := MulEquiv.ext fun ζ => powL_add l _ _ ζ
variable (K e a) in

abbrev TameGal : Type := rootsOfUnity e K ⋊[frobAut K l e a] Multiplicative (ZMod a)
namespace TameGal
variable {l}
abbrev inertia : rootsOfUnity e K →* TameGal K l e a := SemidirectProduct.inl
abbrev fr : TameGal K l e a := SemidirectProduct.inr (Multiplicative.ofAdd 1)
def shift (g : TameGal K l e a) : ZMod a := g.right.toAdd
def root (g : TameGal K l e a) (τ : ZMod a) : K := ((powL l (-τ) g.left : rootsOfUnity e K) : Kˣ)
@[simp] theorem shift_one : shift (1 : TameGal K l e a) = 0 := rfl
theorem shift_mul (g h : TameGal K l e a) : shift (g * h) = shift g + shift h := rfl
@[simp] theorem shift_inertia (ζ : rootsOfUnity e K) : shift (inertia ζ : TameGal K l e a) = 0 := rfl
@[simp] theorem shift_fr : shift (fr : TameGal K l e a) = 1 := rfl
@[simp] theorem root_one (τ : ZMod a) : root (1 : TameGal K l e a) τ = 1 := by simp [root]
@[simp] theorem root_fr (τ : ZMod a) : root (fr : TameGal K l e a) τ = 1 := by simp [root]
@[simp] theorem root_inertia_zero (ζ : rootsOfUnity e K) :
    root (inertia ζ : TameGal K l e a) 0 = (ζ : Kˣ) := by simp [root]
theorem root_mul (g h : TameGal K l e a) (τ : ZMod a) :
    root (g * h) τ = root g τ * root h (τ - shift g) := by
  have : powL l (-τ) (g * h).left = powL l (-τ) g.left * powL l (-(τ - shift g)) h.left := by
    rw [SemidirectProduct.mul_left, map_mul, neg_sub', sub_neg_eq_add, powL_add]
    rfl
  rw [root, this]
  simp [root]
theorem root_sub_one (g : TameGal K l e a) (τ : ZMod a) : root g (τ - 1) = root g τ ^ l := by
  rw [root, neg_sub, sub_eq_add_neg, powL_add, powL_one]
  simp [root]
theorem root_pow (g : TameGal K l e a) (τ : ZMod a) : root g τ ^ e = 1 :=
  (mem_rootsOfUnity' _ _).1 (powL l (-τ) g.left).2
variable [NeZero e]
instance : Finite (TameGal K l e a) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
theorem card : Nat.card (TameGal K l e a) = e * a := by
  obtain ⟨ζ, hζ⟩ := TameDescentExponentData.prim (K := K) (l := l) (e := e) (a := a)
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
    hζ.card_rootsOfUnity, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
end TameGal
variable {l}
def ringAct : TameGal K l e a →* ((ZMod a → K⟦X⟧) →ₐ[K] (ZMod a → K⟦X⟧)) where
  toFun g :=
    { toFun := fun f τ => rescale (g.root τ) (f (τ - g.shift))
      map_one' := by ext1; simp
      map_mul' := fun f f' => by ext1; simp
      map_zero' := by ext1; simp
      map_add' := fun f f' => by ext1; simp
      commutes' := fun c => by
        ext τ n
        simp only [Pi.algebraMap_apply, PowerSeries.algebraMap_apply, coeff_rescale, coeff_C]
        split_ifs with h <;> simp [h] }
  map_one' := by ext f τ : 2; simp
  map_mul' g h := by
    ext f τ : 2
    simp [TameGal.root_mul, TameGal.shift_mul, rescale_rescale, sub_sub, mul_comm]
theorem ringAct_apply (g : TameGal K l e a) (f : ZMod a → K⟦X⟧) (τ : ZMod a) :
    ringAct g f τ = rescale (g.root τ) (f (τ - g.shift)) := rfl
theorem ringAct_frobTot (g : TameGal K l e a) (f : ZMod a → K⟦X⟧) :
    ringAct g (frobTot K a l f) = frobTot K a l (ringAct g f) := by
  ext τ n
  rw [ringAct_apply, frobTot_apply, frobTot_apply, ringAct_apply, coeff_rescale, coeff_frob,
    coeff_frob, coeff_rescale, TameGal.root_sub_one, sub_right_comm]
  split_ifs with h
  · rw [← pow_mul, Nat.mul_div_cancel' h]
  · simp
theorem ringAct_X (g : TameGal K l e a) :
    ringAct g (fun _ => X) = fun τ => C (g.root τ) * X := funext fun _ => rescale_X _
end Group
section Join
variable {K : Type} [NormedField K] {a : ℕ} {ι : Type}
omit [NormedField K] in
theorem join_eta (w : Vec K a (ι ⊕ Unit)) :
    join (fun τ i => w τ (.inl i)) (fun τ => w τ (.inr ())) = w := by
  ext τ (i | i) : 2 <;> rfl
theorem join_add (v v' : Vec K a ι) (f f' : ZMod a → K⟦X⟧) :
    join (v + v') (f + f') = join v f + join v' f' := by
  ext τ (i | i) : 2 <;> rfl
theorem join_smul (c : K) (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    join (c • v) (c • f) = c • join v f := by
  ext τ (i | i) : 2 <;> rfl
theorem join_smul_tot (c : ZMod a → K⟦X⟧) (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    join (c • v) (c * f) = c • join v f := by
  ext τ (i | i) : 2 <;> rfl
theorem PhiMod.join_mem_Mext {O : Type} [CommRing O] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e : ℕ} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) {y : Vec K a ι}
    (hy : y ∈ P.Mext (invE l e (A O K))) {B : Subalgebra O K⟦X⟧} {v : Vec K a ι}
    {f : ZMod a → K⟦X⟧} : join v f ∈ (P.plus hy).Mext B ↔ v ∈ P.Mext B ∧ ∀ τ, f τ ∈ B :=
  ⟨fun h => ⟨mem_tot.2 fun τ i => mem_tot.1 h τ (.inl i), fun τ => mem_tot.1 h τ (.inr ())⟩,
    fun h => mem_tot.2 fun τ i => by
      rcases i with i | i
      exacts [mem_tot.1 h.1 τ i, h.2 τ]⟩
end Join
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
section Rot
def Rot (e : ℕ) (B : Subalgebra O K⟦X⟧) : Prop :=
  ∀ c : K, c ^ e = 1 → ∀ f ∈ B, rescale c f ∈ B
omit [IsUltrametricDist K] in
theorem norm_coeff_rescale [NeZero e] {c : K} (hc : c ^ e = 1) (f : K⟦X⟧) (n : ℕ) :
    ‖coeff n (rescale c f)‖ = ‖coeff n f‖ := by
  have h := congrArg norm hc
  rw [norm_pow, norm_one] at h
  rw [coeff_rescale, norm_mul, norm_pow,
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne e)).1 h, one_pow, one_mul]
theorem rot_A [NeZero e] : Rot e (A O K) := fun _ hc f hf n =>
  (norm_coeff_rescale hc f n).trans_le (hf n)
omit [IsUltrametricDist K] [IsUnitBall O K] in
theorem Rot.invE {B : Subalgebra O K⟦X⟧} [HasU B] (h : Rot e B) : Rot e (invE l e B) := by
  rintro c hc f ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have := h c hc _ hn
  rwa [map_mul, map_pow, coe_EIn, E, map_add, map_pow, rescale_X, mul_pow, ← map_pow, hc, map_one,
    one_mul, map_natCast] at this
end Rot
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a]
omit [IsUltrametricDist K] [IsUnitBall O K] in
theorem Rot.ringAct_mem {B : Subalgebra O K⟦X⟧} (h : Rot e B) (g : TameGal K l e a)
    {f : ZMod a → K⟦X⟧} (hf : ∀ τ, f τ ∈ B) (τ : ZMod a) : ringAct g f τ ∈ B :=
  h _ (g.root_pow τ) _ (hf _)
structure Descent (P : PhiMod O K l e a ι) where

  act : Representation K (TameGal K l e a) (Vec K a ι)
  act_smul_tot : ∀ g (f : ZMod a → K⟦X⟧) v, act g (f • v) = ringAct g f • act g v
  act_mem_M : ∀ g, ∀ v ∈ P.M, act g v ∈ P.M
  act_phi : ∀ g v, act g (P.phi v) = P.phi (act g v)
namespace Descent
def matAct (g : TameGal K l e a) (G : ZMod a → Matrix ι ι K⟦X⟧) : Module.End K (Vec K a ι) where
  toFun v τ := G τ *ᵥ fun i => rescale (g.root τ) (v (τ - g.shift) i)
  map_add' v w := by
    ext1 τ
    refine Eq.trans ?_ (Matrix.mulVec_add _ _ _)
    congr 1
    ext1 i
    simp
  map_smul' c v := by
    ext1 τ
    refine Eq.trans ?_
      (Matrix.mulVec_smul (G τ) c fun i => rescale (g.root τ) (v (τ - g.shift) i))
    congr 1
    ext1 i
    exact congrFun (map_smul (ringAct g) c fun σ => v σ i) τ
omit [IsUltrametricDist K] [DecidableEq ι] in
theorem matAct_apply (g : TameGal K l e a) (G : ZMod a → Matrix ι ι K⟦X⟧) (v : Vec K a ι)
    (τ : ZMod a) :
    matAct g G v τ = G τ *ᵥ fun i => rescale (g.root τ) (v (τ - g.shift) i) := rfl
def ofMatrix (P : PhiMod O K l e a ι) (G : TameGal K l e a → ZMod a → Matrix ι ι K⟦X⟧)
    (mem : ∀ g τ i j, G g τ i j ∈ A O K) (one : ∀ τ, G 1 τ = 1)
    (mul : ∀ g h τ, G (g * h) τ = G g τ * (G h (τ - g.shift)).map (rescale (g.root τ)))
    (comm : ∀ g τ, G g τ * (P.mx (τ - g.shift)).map (rescale (g.root τ)) =
      P.mx τ * (G g (τ - 1)).map (frob K l)) [NeZero e] : Descent P where
  act :=
    { toFun := fun g => matAct g (G g)
      map_one' := by
        refine LinearMap.ext fun v => funext fun τ => ?_
        simp [one, matAct_apply]
      map_mul' := fun g h => by
        refine LinearMap.ext fun v => funext fun τ => ?_
        rw [Module.End.mul_apply, matAct_apply, matAct_apply, matAct_apply, mul,
          ← Matrix.mulVec_mulVec]
        congr 1
        ext1 i
        refine Eq.trans ?_ (RingHom.map_mulVec (rescale (g.root τ)) _ _ i).symm
        congr 1
        ext1 j
        simp [TameGal.root_mul, TameGal.shift_mul, rescale_rescale, sub_sub, mul_comm] }
  act_smul_tot g f v := by
    ext1 τ
    change matAct g (G g) (f • v) τ = ringAct g f τ • matAct g (G g) v τ
    rw [matAct_apply, matAct_apply, ← Matrix.mulVec_smul]
    congr 1
    ext1 i
    simp [ringAct_apply]
  act_mem_M g v hv := mem_tot.2 fun τ i => by
    change (matAct g (G g) v τ) i ∈ A O K
    rw [matAct_apply]
    exact Subalgebra.sum_mem _ fun j _ =>
      mul_mem (mem g τ i j) (rot_A _ (g.root_pow τ) _ (mem_tot.1 hv _ j))
  act_phi g v := by
    ext1 τ
    have h1 : (fun i => rescale (g.root τ) (P.phi v (τ - g.shift) i)) =
        (P.mx (τ - g.shift)).map (rescale (g.root τ)) *ᵥ
          fun i => frob K l (ringAct g (fun σ => v σ i) (τ - 1)) := funext fun i => by
      refine (RingHom.map_mulVec (rescale (g.root τ)) _ _ i).trans ?_
      congr 1
      ext1 j
      exact congrFun (ringAct_frobTot g fun σ => v σ j) τ
    change matAct g (G g) (P.phi v) τ = P.phi (matAct g (G g) v) τ
    rw [matAct_apply, h1, Matrix.mulVec_mulVec, comm, ← Matrix.mulVec_mulVec, P.phi_apply,
      matAct_apply]
    congr 1
    ext1 i
    exact (RingHom.map_mulVec (frob K l).toRingHom _ _ i).symm
variable {P : PhiMod O K l e a ι} (Δ : Descent P) (g : TameGal K l e a)
theorem act_mem_uPow {m : ℕ} {v : Vec K a ι} (hv : v ∈ uPow K a ι m) :
    Δ.act g v ∈ uPow K a ι m := by
  obtain ⟨w, rfl⟩ := mem_uPow_iff_exists.1 hv
  have h := Δ.act_smul_tot g ((fun _ => X) ^ m) w
  rw [map_pow, ringAct_X] at h
  intro τ i
  rw [show Δ.act g ((X : K⟦X⟧) ^ m • w) = _ from h]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (Dvd.intro_left _ rfl) m) _
theorem red_act_cst_red (v : Vec K a ι) : red (Δ.act g (cst (red v))) = red (Δ.act g v) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub, ← mem_uPow_one]
  exact Δ.act_mem_uPow g (by rw [mem_uPow_one, map_sub, red_cst, sub_self])
def actD : Representation K (TameGal K l e a) P.D where
  toFun g := red ∘ₗ Δ.act g ∘ₗ cst
  map_one' := LinearMap.ext fun d => by simp
  map_mul' g h := LinearMap.ext fun d => by
    simp only [map_mul, LinearMap.comp_apply, Module.End.mul_apply, red_act_cst_red]
abbrev inv : Submodule K (Vec K a ι) := Δ.act.invariants
def isotypic (c : ZMod e) : Submodule K (Vec K a ι) where
  carrier := {v | ∀ ζ τ, Δ.act (TameGal.inertia ζ) v τ =
    (TameGal.inertia ζ : TameGal K l e a).root τ ^ c.val • v τ}
  add_mem' hv hw ζ τ := by rw [map_add, Pi.add_apply, hv, hw, Pi.add_apply, smul_add]
  zero_mem' ζ τ := by simp
  smul_mem' r v hv ζ τ := by rw [map_smul, Pi.smul_apply, hv, Pi.smul_apply, smul_comm]
def chars (τ : ZMod a) : Set (ZMod e) :=
  {c | ∃ d : P.D, d τ ≠ 0 ∧ ∀ ζ, Δ.actD (TameGal.inertia ζ) d τ =
    (TameGal.inertia ζ : TameGal K l e a).root τ ^ c.val • d τ}
def plusAct : Module.End K (Vec K a (ι ⊕ Unit)) where
  toFun w := join (Δ.act g fun τ i => w τ (.inl i)) (ringAct g fun τ => w τ (.inr ()))
  map_add' v w := by
    rw [← join_add, ← map_add, ← map_add]
    rfl
  map_smul' c v := by
    rw [RingHom.id_apply, ← join_smul, ← map_smul, ← map_smul]
    rfl
theorem plusAct_join (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    Δ.plusAct g (join v f) = join (Δ.act g v) (ringAct g f) := rfl
def plus [NeZero e] {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) (hinv : y ∈ Δ.inv) :
    Descent (P.plus hy) where
  act :=
    { toFun := Δ.plusAct
      map_one' := LinearMap.ext fun w => by
        rw [← join_eta w, plusAct_join]
        simp
      map_mul' := fun g h => LinearMap.ext fun w => by
        rw [← join_eta w, Module.End.mul_apply, plusAct_join, plusAct_join, plusAct_join, map_mul,
          map_mul]
        rfl }
  act_smul_tot g f w := by
    change Δ.plusAct g _ = _ • Δ.plusAct g _
    rw [← join_eta w, ← join_smul_tot, plusAct_join, plusAct_join, ← join_smul_tot, act_smul_tot,
      map_mul]
  act_mem_M g w hw := by
    change Δ.plusAct g w ∈ (P.plus hy).Mext (A O K)
    rw [← join_eta w, plusAct_join, P.join_mem_Mext hy]
    exact ⟨Δ.act_mem_M g _ (mem_tot.2 fun τ i => mem_tot.1 hw τ (.inl i)),
      rot_A.ringAct_mem g fun τ => mem_tot.1 hw τ (.inr ())⟩
  act_phi g w := by
    change Δ.plusAct g _ = (P.plus hy).phi (Δ.plusAct g _)
    rw [← join_eta w, P.plus_phi_join, plusAct_join, plusAct_join, P.plus_phi_join, map_add, act_phi,
      act_smul_tot, hinv g, ringAct_frobTot]
end Descent
def frobPeriod (l : ℕ) {e : ℕ} (c : ZMod e) : ℕ := Function.minimalPeriod (fun x => (l : ZMod e) * x) c
def maxPeriod (l : ℕ) {e : ℕ} (T : Finset (ZMod e)) : ℕ :=
  (T ×ˢ T).sup fun p => frobPeriod l (p.1 - p.2)
example : frobPeriod 3 (1 : ZMod 8) = 2 :=
  Function.minimalPeriod_eq_prime (p := 2) (by decide) (by decide)
example : ringAct (TameGal.inertia (rootsOfUnity.mkOfPowEq (-1 : ℚ_[3]) (n := 2) (by norm_num)) :
    TameGal ℚ_[3] 3 2 1) (fun _ => X) 0 = -X := by
  rw [ringAct_X]
  simp
end GlobalTheory.BK


