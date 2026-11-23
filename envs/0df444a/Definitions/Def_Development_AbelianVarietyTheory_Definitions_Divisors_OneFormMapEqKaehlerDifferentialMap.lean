-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:10.575965+00:00
-- url     : https://prove2.me/theorems/8e0e535c-3360-4f0b-a275-6a1e72ae237c
-- title:
--   One Form Map Eq Kaehler Differential Map
-- statement:
--   Definitions and structural lemmas for One Form Map Eq Kaehler Differential Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Theorems.Thm_GlobalTheory_Cris_Thick_Hom_mem

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
open KaehlerDifferential
namespace GlobalTheory.CechDR
section Alg
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
abbrev DR : Type := ExteriorAlgebra B Ω[B⁄R]
abbrev Om (j : ℕ) : Type := ⋀[B]^j Ω[B⁄R]
variable {R B}
abbrev ι1 : Ω[B⁄R] →ₗ[B] DR R B := ExteriorAlgebra.ι B
def sgn : DR R B →ₐ[B] DR R B := CliffordAlgebra.involute
@[simp] theorem sgn_ι (ω : Ω[B⁄R]) : sgn (ι1 ω) = -ι1 ω := CliffordAlgebra.involute_ι ω
@[simp] theorem sgn_sgn (x : DR R B) : sgn (sgn x) = x := CliffordAlgebra.involute_involute x
theorem ι_mul_ι_swap (a b : Ω[B⁄R]) : ι1 a * ι1 b = -(ι1 b * ι1 a) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a b)
theorem ι_mul (ω : Ω[B⁄R]) (x : DR R B) : ι1 ω * x = sgn x * ι1 ω := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap b => rw [AlgHom.commutes, Algebra.commutes]
  | ι a => rw [sgn_ι, neg_mul]; exact ι_mul_ι_swap _ _
  | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, map_mul, mul_assoc]
  | add a b ha hb => rw [mul_add, ha, hb, map_add, add_mul]
theorem ind1 {P : Ω[B⁄R] → Prop} (h : ∀ b c : B, P (b • D R B c)) (h0 : P 0)
    (ha : ∀ x y, P x → P y → P (x + y)) (ω : Ω[B⁄R]) : P ω := by
  have key : ∀ ω ∈ Submodule.span B (Set.range (D R B)), ∀ b : B, P (b • ω) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact fun b ↦ h b c
    | zero => intro b; rwa [smul_zero]
    | add x y _ _ hx hy => intro b; rw [smul_add]; exact ha _ _ (hx b) (hy b)
    | smul a x _ hx => intro b; rw [smul_smul]; exact hx _
  simpa using key ω (by rw [span_range_derivation]; trivial) 1
theorem indDR {P : DR R B → Prop} (h : ∀ b : B, P (algebraMap B _ b)) (hd : ∀ b : B, P (ι1 (D R B b)))
    (hm : ∀ x y, P x → P y → P (x * y)) (ha : ∀ x y, P x → P y → P (x + y)) (x : DR R B) : P x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap b => exact h b
  | ι a =>
    induction a using ind1 with
    | h b c => rw [map_smul, Algebra.smul_def]; exact hm _ _ (h b) (hd c)
    | h0 => simpa using h 0
    | ha x y hx hy => rw [map_add]; exact ha _ _ hx hy
  | mul a b h1 h2 => exact hm _ _ h1 h2
  | add a b h1 h2 => exact ha _ _ h1 h2
variable (R B) in

def Tw : Type := DR R B × DR R B
namespace Tw
instance : AddCommGroup (Tw R B) := inferInstanceAs (AddCommGroup (DR R B × DR R B))
instance : Mul (Tw R B) := ⟨fun a b ↦ (a.1 * b.1, sgn a.1 * b.2 + a.2 * b.1)⟩
instance : One (Tw R B) := ⟨(1, 0)⟩
def mk (x y : DR R B) : Tw R B := (x, y)
@[simp] theorem mk_1 (x y : DR R B) : (mk x y).1 = x := rfl
@[simp] theorem mk_2 (x y : DR R B) : (mk x y).2 = y := rfl
@[ext] theorem ext' {a b : Tw R B} (h1 : a.1 = b.1) (h2 : a.2 = b.2) : a = b := Prod.ext h1 h2
@[simp] theorem mul_1 (a b : Tw R B) : (a * b).1 = a.1 * b.1 := rfl
@[simp] theorem mul_2 (a b : Tw R B) : (a * b).2 = sgn a.1 * b.2 + a.2 * b.1 := rfl
@[simp] theorem add_1 (a b : Tw R B) : (a + b).1 = a.1 + b.1 := rfl
@[simp] theorem add_2 (a b : Tw R B) : (a + b).2 = a.2 + b.2 := rfl
@[simp] theorem zero_1 : (0 : Tw R B).1 = 0 := rfl
@[simp] theorem zero_2 : (0 : Tw R B).2 = 0 := rfl
@[simp] theorem one_1 : (1 : Tw R B).1 = 1 := rfl
@[simp] theorem one_2 : (1 : Tw R B).2 = 0 := rfl
instance : Ring (Tw R B) :=
  { (inferInstance : AddCommGroup (Tw R B)), (inferInstance : Mul (Tw R B)),
    (inferInstance : One (Tw R B)) with
    left_distrib := fun a b c ↦ by ext <;> simp [mul_add]; abel
    right_distrib := fun a b c ↦ by ext <;> simp [add_mul]; abel
    zero_mul := fun a ↦ by ext <;> simp
    mul_zero := fun a ↦ by ext <;> simp
    mul_assoc := fun a b c ↦ by ext <;> simp [mul_add, add_mul, mul_assoc, add_assoc]
    one_mul := fun a ↦ by ext <;> simp
    mul_one := fun a ↦ by ext <;> simp }
def ofFun : B →+* Tw R B where
  toFun b := mk (algebraMap B _ b) (ι1 (D R B b))
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [← Algebra.smul_def, ← Algebra.commutes b]
@[simp] theorem ofFun_1 (b : B) : (ofFun (R := R) b).1 = algebraMap B _ b := rfl
@[simp] theorem ofFun_2 (b : B) : (ofFun (R := R) b).2 = ι1 (D R B b) := rfl
instance : Algebra B (Tw R B) := (ofFun (R := R)).toAlgebra' fun b x ↦ by
  ext
  · simp [Algebra.commutes]
  · simp [Algebra.commutes, ι_mul (D R B b), add_comm]
theorem smul_def' (b : B) (x : Tw R B) : b • x = ofFun b * x := rfl
instance : Module R (Tw R B) := inferInstanceAs (Module R (DR R B × DR R B))
@[simp] theorem smul_1 (r : R) (a : Tw R B) : (r • a).1 = r • a.1 := rfl
@[simp] theorem smul_2 (r : R) (a : Tw R B) : (r • a).2 = r • a.2 := rfl
instance : IsScalarTower R B (Tw R B) := ⟨fun r b x ↦ by
  ext <;> simp [smul_def', ← Algebra.smul_def]⟩
def der : Derivation R B (Tw R B) :=
  Derivation.mk'
    { toFun b := mk (ι1 (D R B b)) 0
      map_add' a b := by ext <;> simp
      map_smul' r b := by ext <;> simp }
    fun a b ↦ by
      ext
      · simp [smul_def', ← Algebra.smul_def]
      · simp [smul_def', ι_mul_ι_swap (D R B a)]
theorem der_apply (b : B) : der (R := R) b = mk (ι1 (D R B b)) 0 := rfl
theorem lift_anti (a b : Ω[B⁄R]) :
    der.liftKaehlerDifferential a * der.liftKaehlerDifferential b +
      der.liftKaehlerDifferential b * der.liftKaehlerDifferential a = (0 : Tw R B) := by
  induction a using ind1 with
  | h0 => simp
  | ha x y hx hy => rw [map_add, add_mul, mul_add, add_add_add_comm, hx, hy, add_zero]
  | h a a' =>
    induction b using ind1 with
    | h0 => simp
    | ha x y hx hy => rw [map_add, add_mul, mul_add, add_add_add_comm, hx, hy, add_zero]
    | h b b' =>
      simp only [map_smul, smul_mul_assoc, mul_smul_comm, Derivation.liftKaehlerDifferential_comp_D]
      rw [smul_comm a b, ← smul_add, ← smul_add]
      have : der (R := R) a' * der b' + der b' * der a' = 0 := by
        ext <;> simp [der_apply, ι_mul_ι_swap (D R B a')]
      rw [this, smul_zero, smul_zero]
theorem lift_sq (a : Ω[B⁄R]) :
    der.liftKaehlerDifferential a * der.liftKaehlerDifferential a = (0 : Tw R B) := by
  induction a using ind1 with
  | h0 => simp
  | ha x y hx hy =>
    rw [map_add, add_mul, mul_add, mul_add, hx, hy, zero_add, add_zero, lift_anti]
  | h a a' =>
    simp only [map_smul, smul_mul_assoc, mul_smul_comm, Derivation.liftKaehlerDifferential_comp_D]
    have : der (R := R) a' * der a' = 0 := by ext <;> simp [der_apply]
    rw [this, smul_zero, smul_zero]
def graph : DR R B →ₐ[B] Tw R B := ExteriorAlgebra.lift B ⟨der.liftKaehlerDifferential, lift_sq⟩
theorem graph_D (b : B) : graph (ι1 (D R B b)) = mk (ι1 (D R B b)) 0 := by
  rw [graph, ExteriorAlgebra.lift_ι_apply, Derivation.liftKaehlerDifferential_comp_D]; rfl
theorem graph_1 (x : DR R B) : (graph x).1 = x := by
  induction x using indDR with
  | h b => rw [AlgHom.commutes]; rfl
  | hd b => rw [graph_D]; rfl
  | hm x y hx hy => rw [map_mul, mul_1, hx, hy]
  | ha x y hx hy => rw [map_add, add_1, hx, hy]
end Tw
variable (R B) in

def dDR : DR R B →ₗ[R] DR R B where
  toFun x := (Tw.graph x).2
  map_add' x y := by rw [map_add, Tw.add_2]
  map_smul' r x := by
    rw [← algebraMap_smul B r x, map_smul, algebraMap_smul]; rfl
@[simp] theorem dDR_algebraMap (b : B) : dDR R B (algebraMap B _ b) = ι1 (D R B b) := by
  change (Tw.graph _).2 = _
  rw [AlgHom.commutes]; rfl
@[simp] theorem dDR_D (b : B) : dDR R B (ι1 (D R B b)) = 0 := by
  change (Tw.graph _).2 = _
  rw [Tw.graph_D]; rfl
theorem dDR_mul (x y : DR R B) : dDR R B (x * y) = sgn x * dDR R B y + dDR R B x * y := by
  change (Tw.graph _).2 = _
  rw [map_mul, Tw.mul_2, Tw.graph_1, Tw.graph_1]; rfl
theorem dDR_smul (b : B) (x : DR R B) : dDR R B (b • x) = ι1 (D R B b) * x + b • dDR R B x := by
  rw [Algebra.smul_def, dDR_mul, AlgHom.commutes, dDR_algebraMap, Algebra.smul_def, add_comm]
theorem dDR_sgn (x : DR R B) : dDR R B (sgn x) = -sgn (dDR R B x) := by
  induction x using indDR with
  | h b => simp
  | hd b => simp
  | hm x y hx hy => simp [dDR_mul, hx, hy]; abel
  | ha x y hx hy => simp [hx, hy]; abel
theorem dDR_dDR (x : DR R B) : dDR R B (dDR R B x) = 0 := by
  induction x using indDR with
  | h b => simp
  | hd b => simp
  | hm x y hx hy => simp [dDR_mul, dDR_sgn, hx, hy]
  | ha x y hx hy => simp [hx, hy]
theorem ι_mem (ω : Ω[B⁄R]) : ι1 ω ∈ ⋀[B]^1 Ω[B⁄R] := by
  change _ ∈ LinearMap.range _ ^ 1
  rw [pow_one]; exact ⟨ω, rfl⟩
theorem mul_mem {i j : ℕ} {x y : DR R B} (hx : x ∈ ⋀[B]^i Ω[B⁄R]) (hy : y ∈ ⋀[B]^j Ω[B⁄R]) :
    x * y ∈ ⋀[B]^(i + j) Ω[B⁄R] := by
  change _ ∈ LinearMap.range _ ^ (i + j)
  rw [pow_add]; exact Submodule.mul_mem_mul hx hy
theorem dDR_ι_mem (ω : Ω[B⁄R]) : dDR R B (ι1 ω) ∈ ⋀[B]^2 Ω[B⁄R] := by
  induction ω using ind1 with
  | h b c => rw [map_smul, dDR_smul, dDR_D, smul_zero, add_zero]; exact mul_mem (ι_mem _) (ι_mem _)
  | h0 => simp
  | ha x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
theorem dDR_mem {j : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^j Ω[B⁄R]) : dDR R B x ∈ ⋀[B]^(j + 1) Ω[B⁄R] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap b => rw [dDR_algebraMap]; exact ι_mem _
  | add x y i _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    rw [dDR_mul, sgn_ι, neg_mul]
    refine add_mem (neg_mem ?_) ?_
    · have := mul_mem (ι_mem ω) ih
      rwa [show 1 + (i + 1) = i + 1 + 1 by ring] at this
    · have := mul_mem (dDR_ι_mem ω) hx
      rwa [show 2 + i = i + 1 + 1 by ring] at this
variable (R B) in

def dOm (j : ℕ) : Om R B j →ₗ[R] Om R B (j + 1) where
  toFun x := ⟨dDR R B x, dDR_mem x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r x := Subtype.ext (map_smul _ _ _)
@[simp] theorem coe_dOm {j : ℕ} (x : Om R B j) : (dOm R B j x : DR R B) = dDR R B x := rfl
@[simp] theorem dOm_dOm {j : ℕ} (x : Om R B j) : dOm R B (j + 1) (dOm R B j x) = 0 :=
  Subtype.ext (dDR_dDR _)
variable (R B) in

def dOne : Ω[B⁄R] →ₗ[R] Om R B 2 where
  toFun ω := ⟨dDR R B (ι1 ω), dDR_ι_mem ω⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)
variable (R B) in

def dTwo : Om R B 2 →ₗ[R] Om R B 3 := dOm R B 2
@[simp] theorem coe_dOne (ω : Ω[B⁄R]) : (dOne R B ω : DR R B) = dDR R B (ι1 ω) := rfl
@[simp] theorem coe_dTwo (x : Om R B 2) : (dTwo R B x : DR R B) = dDR R B x := rfl
variable (R B) in

def wedge : Ω[B⁄R] →ₗ[B] Ω[B⁄R] →ₗ[B] Om R B 2 :=
  LinearMap.mk₂ B (fun a b ↦ ⟨ι1 a * ι1 b, mul_mem (ι_mem a) (ι_mem b)⟩)
    (fun _ _ _ ↦ Subtype.ext (by simp [add_mul])) (fun _ _ _ ↦ Subtype.ext (by simp))
    (fun _ _ _ ↦ Subtype.ext (by simp [mul_add])) (fun _ _ _ ↦ Subtype.ext (by simp))
@[simp] theorem coe_wedge (a b : Ω[B⁄R]) : (wedge R B a b : DR R B) = ι1 a * ι1 b := rfl
@[simp] theorem wedge_self (a : Ω[B⁄R]) : wedge R B a a = 0 := Subtype.ext (by simp)
@[simp] theorem dOne_D (b : B) : dOne R B (D R B b) = 0 := Subtype.ext (dDR_D b)
@[simp] theorem dTwo_dOne (ω : Ω[B⁄R]) : dTwo R B (dOne R B ω) = 0 := Subtype.ext (dDR_dDR _)
end Alg
section Map
variable {R R' R'' B B' B'' : Type} [CommRing R] [CommRing B] [Algebra R B]
  [CommRing R'] [CommRing B'] [Algebra R' B'] [CommRing R''] [CommRing B''] [Algebra R'' B'']
def SemiHom (σ : R →+* R') (α : B →+* B') : Prop := ∀ (r : R) (b : B), α (r • b) = σ r • α b
variable {σ : R →+* R'} {α : B →+* B'}
theorem SemiHom.map_algebraMap (h : SemiHom σ α) (r : R) : α (algebraMap R B r) = algebraMap R' B' (σ r) := by
  rw [Algebra.algebraMap_eq_smul_one, h, map_one, Algebra.algebraMap_eq_smul_one]
def SemiHom.m1' (h : SemiHom σ α) : Ω[B⁄R] →ₛₗ[α] Ω[B'⁄R'] :=
  letI : Module B Ω[B'⁄R'] := Module.compHom _ α
  letI : Module R Ω[B'⁄R'] := Module.compHom _ σ
  haveI : IsScalarTower R B Ω[B'⁄R'] := ⟨fun r b x ↦ by
    change α (r • b) • x = σ r • α b • x
    rw [h, smul_assoc]⟩
  let δ : Derivation R B Ω[B'⁄R'] := Derivation.mk'
    { toFun b := D R' B' (α b)
      map_add' a b := by simp
      map_smul' r b := by
        change D R' B' (α (r • b)) = σ r • D R' B' (α b)
        rw [h, Derivation.map_smul] }
    fun a b ↦ by
      change D R' B' (α (a * b)) = α a • D R' B' (α b) + α b • D R' B' (α a)
      rw [map_mul, Derivation.leibniz]
  { toFun := δ.liftKaehlerDifferential
    map_add' := map_add _
    map_smul' := fun b x ↦ δ.liftKaehlerDifferential.map_smul b x }
theorem SemiHom.m1'_D (h : SemiHom σ α) (b : B) : h.m1' (D R B b) = D R' B' (α b) := by
  letI : Module B Ω[B'⁄R'] := Module.compHom _ α
  letI : Module R Ω[B'⁄R'] := Module.compHom _ σ
  haveI : IsScalarTower R B Ω[B'⁄R'] := ⟨fun r b x ↦ by
    change α (r • b) • x = σ r • α b • x
    rw [h, smul_assoc]⟩
  exact Derivation.liftKaehlerDifferential_comp_D (M := Ω[B'⁄R']) _ _
def SemiHom.m1 (h : SemiHom σ α) : Ω[B⁄R] →ₛₗ[σ] Ω[B'⁄R'] where
  toFun := h.m1'
  map_add' := map_add _
  map_smul' r x := by rw [← algebraMap_smul B r x, map_smulₛₗ, h.map_algebraMap, algebraMap_smul]
@[simp] theorem SemiHom.m1_D (h : SemiHom σ α) (b : B) : h.m1 (D R B b) = D R' B' (α b) := h.m1'_D b
@[simp] theorem SemiHom.oneFormMap_smul_semilinear (h : SemiHom σ α) (b : B) (ω : Ω[B⁄R]) : h.m1 (b • ω) = α b • h.m1 ω :=
  map_smulₛₗ h.m1' b ω
def SemiHom.mDR (h : SemiHom σ α) : DR R B →+* DR R' B' :=
  letI : Algebra B (DR R' B') := ((algebraMap B' (DR R' B')).comp α).toAlgebra'
    fun b x ↦ Algebra.commutes (α b) x
  (ExteriorAlgebra.lift B (A := DR R' B') ⟨
    { toFun ω := ι1 (h.m1 ω)
      map_add' a b := by simp
      map_smul' b ω := by
        rw [h.oneFormMap_smul_semilinear, map_smul, Algebra.smul_def]; rfl }, fun _ ↦ ExteriorAlgebra.ι_sq_zero _⟩).toRingHom
@[simp] theorem SemiHom.mDR_ι (h : SemiHom σ α) (ω : Ω[B⁄R]) : h.mDR (ι1 ω) = ι1 (h.m1 ω) := by
  letI : Algebra B (DR R' B') := ((algebraMap B' (DR R' B')).comp α).toAlgebra'
    fun b x ↦ Algebra.commutes (α b) x
  exact ExteriorAlgebra.lift_ι_apply (A := DR R' B') _ _ _ _
@[simp] theorem SemiHom.mDR_algebraMap (h : SemiHom σ α) (b : B) :
    h.mDR (algebraMap B _ b) = algebraMap B' _ (α b) := by
  letI : Algebra B (DR R' B') := ((algebraMap B' (DR R' B')).comp α).toAlgebra'
    fun b x ↦ Algebra.commutes (α b) x
  exact AlgHom.commutes (B := DR R' B') _ _
theorem SemiHom.mDR_smul (h : SemiHom σ α) (b : B) (x : DR R B) : h.mDR (b • x) = α b • h.mDR x := by
  rw [Algebra.smul_def, map_mul, h.mDR_algebraMap, Algebra.smul_def]
theorem SemiHom.mDR_mem (h : SemiHom σ α) {j : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^j Ω[B⁄R]) :
    h.mDR x ∈ ⋀[B']^j Ω[B'⁄R'] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap b =>
    rw [h.mDR_algebraMap]
    change _ ∈ LinearMap.range _ ^ 0
    rw [pow_zero]; exact Submodule.algebraMap_mem _
  | add x y i _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    rw [map_mul, h.mDR_ι]
    have := mul_mem (ι_mem (h.m1 ω)) ih
    rwa [add_comm] at this
def SemiHom.mOm (h : SemiHom σ α) (j : ℕ) : Om R B j →ₛₗ[σ] Om R' B' j where
  toFun x := ⟨h.mDR x, h.mDR_mem x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r x := Subtype.ext (by
    change h.mDR (r • x.1) = σ r • h.mDR x.1
    rw [← algebraMap_smul B r x.1, h.mDR_smul, h.map_algebraMap, algebraMap_smul])
variable {τ : R' →+* R''} {β : B' →+* B''} {ρ : R →+* R''} {γ : B →+* B''}
end Map
end GlobalTheory.CechDR


