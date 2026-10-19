-- Prove2me | Definitions.Def_OAIQWCPT000
-- name    : OAIQWCPT000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T21:16:34.05922+00:00
-- url     : https://prove2.me/theorems/cbeeb173-1cf5-461b-96b5-82faf68d768c
-- title:
--   OpenAI choiceless polynomial time split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of `OAI.CPTSeparation.main`. The linear-consistency query over $\mathbb{F}_3$ is isomorphism-invariant and decidable in polynomial time, but it is not definable in choiceless polynomial time with counting. The bundle holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/ModelTheory/Choiceless` (OpenAI, *Choiceless polynomial time with counting does not capture polynomial time*, OpenAI Math Release, September 23, 2026, result family 243, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are the grid structures and their central groups, counting formulas over hereditarily finite structures, flows and projections, the simulation of machines, and the query machine. It also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them.
--
--   The definitions of the published statement (the input structures, hereditarily finite sets, the operational semantics and the full counting language) are not repeated: the bundle imports them from the published bundle `Def_ChoicelessPolynomialTime`. It imports no other bundle.
--
--   Modules: `Bounds`, `Counters`, `Counting`, `Definability`, `Evaluation`, `Flows`, `Forms`, `FullLanguage`, `Gaussian`, `GaussMachine`, `Grid`, `Hereditary`, `Interpretations`, `Matrix`, `Model`, `Observers`, `Operational`, `QueryMachine`, `Simulation`, `Stack`, `Support`, `TableMachine`, `Traces`.
-- source:
--   OpenAI, Choiceless polynomial time with counting does not capture polynomial time, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 243; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Choiceless-polynomial-time-with-counting-does-not-capture-polynomial-time-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/ModelTheory/Choiceless at commit adc7f12

import Mathlib
import Definitions.Def_ChoicelessPolynomialTime

section
-- module Solutions.OAIQW_CPTSeparation.Compat
namespace OAI.CPTSeparation
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434


end OAI.CPTSeparation
end

section
-- module Solutions.OAIQW_CPTSeparation.Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uB uC uF uR

namespace CPTSeparation.Hereditary

section

variable {A : Type uA} {B : Type uB}

attribute [local instance] OAI.CPTSeparation.Hereditary.instDecidableEqHF
@[simp] theorem mk_eq_mk {l r : Lists A} : mk l = mk r ↔ Lists.Equiv l r :=
  Quotient.eq

theorem mem_rawElements (a l : Lists A) : mk a ∈ rawElements l ↔ a ∈ l := by
  classical
  rcases l with ⟨(_ | _), l⟩
  · cases l
    change mk a ∈ (∅ : Finset (HF A)) ↔ False
    simp
  · change mk a ∈ (Lists'.toList l).toFinset.image mk ↔ a ∈ l
    simp only [Finset.mem_image, List.mem_toFinset, Lists'.mem_def, mk_eq_mk]
    constructor
    · rintro ⟨a',ha',heq⟩
      exact ⟨a',ha',heq.symm⟩
    · rintro ⟨a',ha',heq⟩
      exact ⟨a',ha',heq.symm⟩

theorem raw_mem_congr_right {l r : Lists A} (h : Lists.Equiv l r) (a : Lists A) :
    a ∈ l ↔ a ∈ r := by
  cases h with
  | refl => rfl
  | antisymm hl hr =>
    exact ⟨Lists'.mem_of_subset hl, Lists'.mem_of_subset hr⟩

@[simp] theorem mem_mk (a l : Lists A) : mk a ∈ mk l ↔ a ∈ l := mem_rawElements a l

theorem rawRank_lt_of_mem {b : Bool} (l : Lists' A b) (a : Lists A)
    (ha : a ∈ l.toList) : rawRank a < rawRank' l := by
  induction l with
  | atom => simp at ha
  | nil => simp at ha
  | cons' c l ihc ihl =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ihl ha) (le_max_right _ _)

theorem rawRank_congr {l r : Lists A} (h : Lists.Equiv l r) : rawRank l = rawRank r := by
  induction h using Lists.Equiv.rec
      (motive_2 := fun l r _ => rawRank' l ≤ rawRank' r) with
  | refl => rfl
  | antisymm hl hr ihl ihr => exact Nat.le_antisymm ihl ihr
  | nil => exact Nat.zero_le _
  | @cons a a' l r heq hmem hsub iheq ihsub =>
    change max (rawRank a + 1) (rawRank' l) ≤ rawRank' r
    refine max_le ?_ ihsub
    rw [iheq]
    exact rawRank_lt_of_mem r a' hmem

theorem rank_lt_of_mem {x y : HF A} (h : x ∈ y) : rank x < rank y := by
  induction y using Quotient.inductionOn with
  | _ l =>
    induction x using Quotient.inductionOn with
    | _ a =>
      have h' := (mem_mk a l).mp h
      rcases l with ⟨(_ | _), l⟩
      · exact False.elim h'
      · obtain ⟨a',ha',heq⟩ := h'
        change rawRank a < rawRank' l
        rw [rawRank_congr heq]
        exact rawRank_lt_of_mem l a' ha'

end

open Classical Finset

end CPTSeparation.Hereditary

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation

namespace Support

abbrev Scalar := ZMod 3

abbrev Plane := Scalar × Scalar

def omega (u v : Plane) : Scalar := u.1 * v.2 - u.2 * v.1

@[simp] theorem omega_self (u : Plane) : omega u u = 0 := by simp [omega, mul_comm]

@[simp] theorem omega_zero_left (u : Plane) : omega 0 u = 0 := by simp [omega]

@[simp] theorem omega_zero_right (u : Plane) : omega u 0 = 0 := by simp [omega]

@[simp] theorem omega_add_left (u v w : Plane) :
    omega (u + v) w = omega u w + omega v w := by simp [omega]; ring

@[simp] theorem omega_add_right (u v w : Plane) :
    omega u (v + w) = omega u v + omega u w := by simp [omega]; ring

@[simp] theorem omega_neg_left (u v : Plane) : omega (-u) v = -omega u v := by
  simp [omega]; ring

@[simp] theorem omega_neg_right (u v : Plane) : omega u (-v) = -omega u v := by
  simp [omega]; ring

@[simp] theorem omega_smul_left (a : Scalar) (u v : Plane) :
    omega (a • u) v = a * omega u v := by simp [omega]; ring

@[simp] theorem omega_smul_right (a : Scalar) (u v : Plane) :
    omega u (a • v) = a * omega u v := by simp [omega]; ring

variable {F K : Type} [finiteF : Fintype F] [AddCommGroup K] [scalarModuleK : Module Scalar K]

def correction (cycle : F → K) (a b : F → Plane) : K :=
  (2 : Scalar) • ∑ f, omega (a f) (b f) • cycle f

@[simp] theorem correction_self (cycle : F → K) (a : F → Plane) :
    correction cycle a a = 0 := by simp [correction]

@[simp] theorem correction_zero_left (cycle : F → K) (a : F → Plane) :
    correction cycle 0 a = 0 := by simp [correction]

@[simp] theorem correction_zero_right (cycle : F → K) (a : F → Plane) :
    correction cycle a 0 = 0 := by simp [correction]

@[simp] theorem correction_add_left (cycle : F → K) (a b c : F → Plane) :
    correction cycle (a + b) c = correction cycle a c + correction cycle b c := by
  simp [correction, add_smul, Finset.sum_add_distrib, smul_add]

@[simp] theorem correction_add_right (cycle : F → K) (a b c : F → Plane) :
    correction cycle a (b + c) = correction cycle a b + correction cycle a c := by
  simp [correction, add_smul, Finset.sum_add_distrib, smul_add]

@[simp] theorem correction_neg_left (cycle : F → K) (a b : F → Plane) :
    correction cycle (-a) b = -correction cycle a b := by
  simp [correction, Finset.sum_neg_distrib]

@[simp] theorem correction_neg_right (cycle : F → K) (a b : F → Plane) :
    correction cycle a (-b) = -correction cycle a b := by
  simp [correction, Finset.sum_neg_distrib]

@[ext]
structure H (cycle : F → K) where
  face : F → Plane
  flow : K

namespace H

variable (cycle : F → K)

instance instOne : One (H cycle) := ⟨⟨0, 0⟩⟩

instance instMul : Mul (H cycle) := ⟨fun x y =>
  ⟨x.face + y.face, x.flow + y.flow + correction cycle x.face y.face⟩⟩

instance instInv : Inv (H cycle) := ⟨fun x => ⟨-x.face, -x.flow⟩⟩

omit F K cycle in
@[simp] theorem one_face
    {F : Type}
    {K : Type}
    [Fintype F]
    [AddCommGroup K]
    [_root_.Module Support.Scalar K]
    (cycle : F → K) : (1 : H cycle).face = 0 := rfl

omit F K cycle in
@[simp] theorem one_flow
    {F : Type}
    {K : Type}
    [Fintype F]
    [AddCommGroup K]
    [_root_.Module Support.Scalar K]
    (cycle : F → K) : (1 : H cycle).flow = 0 := rfl

@[simp] theorem mul_face (x y : H cycle) : (x * y).face = x.face + y.face := rfl

@[simp] theorem mul_flow (x y : H cycle) :
    (x * y).flow = x.flow + y.flow + correction cycle x.face y.face := rfl

omit F K cycle in
@[simp] theorem inv_face
    {F : Type}
    {K : Type}
    [Fintype F]
    [AddCommGroup K]
    [_root_.Module Support.Scalar K]
    (cycle : F → K) (x : H cycle) : x⁻¹.face = -x.face := rfl

omit F K cycle in
@[simp] theorem inv_flow
    {F : Type}
    {K : Type}
    [Fintype F]
    [AddCommGroup K]
    [_root_.Module Support.Scalar K]
    (cycle : F → K) (x : H cycle) : x⁻¹.flow = -x.flow := rfl

instance instGroup : Group (H cycle) := Group.ofLeftAxioms
  (by intro x y z; ext <;> simp [add_assoc] ; abel)
  (by intro x; ext <;> simp)
  (by intro x; ext <;> simp)

def central (k : K) : H cycle := ⟨0,k⟩

@[simp] theorem central_mul (k l : K) : central cycle k * central cycle l = central cycle (k+l) := by
  ext <;> simp [central]

omit F K cycle in
@[simp] theorem central_zero
    {F : Type}
    {K : Type}
    [Fintype F]
    [AddCommGroup K]
    [_root_.Module Support.Scalar K]
    (cycle : F → K) : central cycle (0 : K) = 1 := rfl

omit F K cycle in
@[simp] theorem central_neg
    {F : Type}
    {K : Type}
    [Fintype F]
    [AddCommGroup K]
    [_root_.Module Support.Scalar K]
    (cycle : F → K) (k : K) : central cycle (-k) = (central cycle k)⁻¹ := by
  apply H.ext <;> simp [central]

def projectedAddSubgroup (S : Subgroup (H cycle)) : AddSubgroup (F → Plane) where
  carrier := {a | ∃ h ∈ S, h.face = a}
  zero_mem' := ⟨1, S.one_mem, rfl⟩
  add_mem' := by
    rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x*y, S.mul_mem hx hy, rfl⟩
  neg_mem' := by
    rintro a ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, S.inv_mem hx, rfl⟩

def centralAddSubgroup (S : Subgroup (H cycle)) : AddSubgroup K where
  carrier := {k | central cycle k ∈ S}
  zero_mem' := S.one_mem
  add_mem' := by
    intro k l hk hl
    change central cycle (k+l) ∈ S
    simpa only [← central_mul] using S.mul_mem hk hl
  neg_mem' := by
    intro k hk
    change central cycle (-k) ∈ S
    simpa only [central_neg] using S.inv_mem hk

def projected (S : Subgroup (H cycle)) : Submodule Scalar (F → Plane) :=
  AddSubgroup.toZModSubmodule 3 (projectedAddSubgroup cycle S)

def centralPart (S : Subgroup (H cycle)) : Submodule Scalar K :=
  AddSubgroup.toZModSubmodule 3 (centralAddSubgroup cycle S)

@[simp] theorem mem_projected (S : Subgroup (H cycle)) (a : F → Plane) :
    a ∈ projected cycle S ↔ ∃ h ∈ S, h.face = a := Iff.rfl

@[simp] theorem mem_centralPart (S : Subgroup (H cycle)) (k : K) :
    k ∈ centralPart cycle S ↔ central cycle k ∈ S := Iff.rfl

def productEquiv : H cycle ≃ (F → Plane) × K where
  toFun x := (x.face,x.flow)
  invFun x := ⟨x.1,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFinite [Finite K] : Finite (H cycle) :=
  Finite.of_equiv ((F → Plane) × K) (productEquiv cycle).symm

noncomputable def projectedLift (S : Subgroup (H cycle)) (a : projected cycle S) : H cycle :=
  Classical.choose a.property

theorem projectedLift_mem (S : Subgroup (H cycle)) (a : projected cycle S) :
    projectedLift cycle S a ∈ S := (Classical.choose_spec a.property).1

@[simp] theorem projectedLift_face (S : Subgroup (H cycle)) (a : projected cycle S) :
    (projectedLift cycle S a).face = a.val := (Classical.choose_spec a.property).2

theorem mul_inv_of_face_eq (x y : H cycle) (h : x.face = y.face) :
    x * y⁻¹ = central cycle (x.flow - y.flow) := by
  apply H.ext
  · simp [h, central]
  · simp [central, h, sub_eq_add_neg]

noncomputable def subgroupEquiv (S : Subgroup (H cycle)) :
    S ≃ projected cycle S × centralPart cycle S where
  toFun x := by
    let a : projected cycle S := ⟨x.val.face, x.val, x.property, rfl⟩
    refine (a, ⟨x.val.flow - (projectedLift cycle S a).flow, ?_⟩)
    rw [mem_centralPart, ← mul_inv_of_face_eq cycle x.val (projectedLift cycle S a)]
    · exact S.mul_mem x.property (S.inv_mem (projectedLift_mem cycle S a))
    · exact (projectedLift_face cycle S a).symm
  invFun p := ⟨central cycle p.2.val * projectedLift cycle S p.1,
    S.mul_mem ((mem_centralPart cycle S p.2.val).mp p.2.property) (projectedLift_mem cycle S p.1)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply H.ext
    · simp [central]
    · simp [central]
  right_inv := by
    rintro ⟨a,k⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [central]
    · apply Subtype.ext
      let a' : projected cycle S := ⟨(central cycle k.val * projectedLift cycle S a).face,
        central cycle k.val * projectedLift cycle S a,
        S.mul_mem ((mem_centralPart cycle S k.val).mp k.property) (projectedLift_mem cycle S a), rfl⟩
      have h : a' = a := by
        apply Subtype.ext
        simp [a', central]
      change (central cycle k.val * projectedLift cycle S a).flow -
        (projectedLift cycle S a').flow = k.val
      rw [h]
      simp [central]

end H

def diagonalForm (weight : F → Scalar) : LinearMap.BilinForm Scalar (F → Plane) where
  toFun a := {
    toFun := fun b => ∑ f, weight f * omega (a f) (b f)
    map_add' := by intro b c; simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro r b
      simp only [Pi.smul_apply, omega_smul_right, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      ring }
  map_add' := by
    intro a b
    ext c
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro r a
    ext b
    simp only [Pi.smul_apply, omega_smul_left, LinearMap.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    change (∑ f, weight f * (r * omega (a f) (b f))) =
      r * (∑ f, weight f * omega (a f) (b f))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    ring

@[simp] theorem diagonalForm_apply (weight : F → Scalar) (a b : F → Plane) :
    diagonalForm weight a b = ∑ f, weight f * omega (a f) (b f) := rfl

theorem mem_diagonalForm_ker (weight : F → Scalar) (a : F → Plane) :
    a ∈ (diagonalForm weight).ker ↔ ∀ f, weight f ≠ 0 → a f = 0 := by
  classical
  constructor
  · intro ha f hf
    have hzero : ∀ b, diagonalForm weight a b = 0 := by
      intro b
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp ha) b
    have heval (b : Plane) : diagonalForm weight a (Pi.single f b) =
        weight f * omega (a f) b := by
      rw [diagonalForm_apply, Finset.sum_eq_single f]
      · simp
      · intro g _ hg
        simp [hg]
      · simp
    have hfst := hzero (Pi.single f (0,1))
    have hsnd := hzero (Pi.single f (1,0))
    simp only [heval, omega, mul_one, mul_zero, sub_zero, zero_sub, mul_neg, neg_eq_zero] at hfst hsnd
    apply Prod.ext
    · exact (mul_eq_zero.mp hfst).resolve_left hf
    · exact (mul_eq_zero.mp hsnd).resolve_left hf
  · intro ha
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro b
    change (∑ f, weight f * omega (a f) (b f)) = 0
    apply Finset.sum_eq_zero
    intro f _
    by_cases hf : weight f = 0
    · simp [hf]
    · simp [ha f hf]

noncomputable def diagonalKerEquiv (weight : F → Scalar) :
    (diagonalForm weight).ker ≃ₗ[Scalar] ({f : F // weight f = 0} → Plane) where
  toFun a f := a.val f.val
  invFun b := by
    classical
    refine ⟨fun f => if hf : weight f = 0 then b ⟨f,hf⟩ else 0, ?_⟩
    rw [mem_diagonalForm_ker]
    intro f hf
    simp [hf]
  left_inv := by
    intro a
    apply Subtype.ext
    funext f
    dsimp
    split_ifs with hf
    · rfl
    · exact ((mem_diagonalForm_ker weight a.val).mp a.property f hf).symm
  right_inv := by intro b; funext f; simp [f.property]
  map_add' := by intro a b; rfl
  map_smul' := by intro r a; rfl

end Support

end CPTSeparation

namespace CPTSeparation.Grid

abbrev Scalar := ZMod 3

abbrev Vertex (n : ℕ) := Fin (n+1) × Fin (n+1) × Fin (n+1)

abbrev EdgeX (n : ℕ) := Fin n × Fin (n+1) × Fin (n+1)

abbrev EdgeY (n : ℕ) := Fin (n+1) × Fin n × Fin (n+1)

abbrev EdgeZ (n : ℕ) := Fin (n+1) × Fin (n+1) × Fin n

abbrev Edge (n : ℕ) := EdgeX n ⊕ EdgeY n ⊕ EdgeZ n

abbrev FaceXY (n : ℕ) := Fin n × Fin n × Fin (n+1)

abbrev FaceXZ (n : ℕ) := Fin n × Fin (n+1) × Fin n

abbrev FaceYZ (n : ℕ) := Fin (n+1) × Fin n × Fin n

abbrev Face (n : ℕ) := FaceXY n ⊕ FaceXZ n ⊕ FaceYZ n

variable {n : ℕ}

def ex (i : Fin n) (j k : Fin (n+1)) : Edge n := .inl (i,j,k)

def ey (i : Fin (n+1)) (j : Fin n) (k : Fin (n+1)) : Edge n := .inr (.inl (i,j,k))

def ez (i j : Fin (n+1)) (k : Fin n) : Edge n := .inr (.inr (i,j,k))

def tail : Edge n → Vertex n
  | .inl (i,j,k) => (i.castSucc,j,k)
  | .inr (.inl (i,j,k)) => (i,j.castSucc,k)
  | .inr (.inr (i,j,k)) => (i,j,k.castSucc)

def head : Edge n → Vertex n
  | .inl (i,j,k) => (i.succ,j,k)
  | .inr (.inl (i,j,k)) => (i,j.succ,k)
  | .inr (.inr (i,j,k)) => (i,j,k.succ)

noncomputable def boundary : (Edge n → Scalar) →ₗ[Scalar] (Vertex n → Scalar) where
  toFun z := ∑ e, z e • (Pi.single (head e) (1 : Scalar) - Pi.single (tail e) 1)
  map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [smul_smul, Finset.smul_sum]

@[simp] theorem boundary_single (e : Edge n) (z : Scalar) :
    boundary (Pi.single e z) = Pi.single (head e) z - Pi.single (tail e) z := by
  classical
  change (∑ x, (Pi.single e z : Edge n → Scalar) x •
    (Pi.single (head x) 1 - Pi.single (tail x) 1)) = _
  rw [Finset.sum_eq_single e]
  · simp [smul_sub, ← Pi.single_smul]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

def cycle : Face n → Edge n → Scalar
  | .inl (i,j,k) => Pi.single (ex i j.castSucc k) 1 + Pi.single (ey i.succ j k) 1 -
      Pi.single (ex i j.succ k) 1 - Pi.single (ey i.castSucc j k) 1
  | .inr (.inl (i,j,k)) => Pi.single (ex i j k.castSucc) 1 + Pi.single (ez i.succ j k) 1 -
      Pi.single (ex i j k.succ) 1 - Pi.single (ez i.castSucc j k) 1
  | .inr (.inr (i,j,k)) => Pi.single (ey i j k.castSucc) 1 + Pi.single (ez i j.succ k) 1 -
      Pi.single (ey i j k.succ) 1 - Pi.single (ez i j.castSucc k) 1

@[simp] theorem boundary_cycle (f : Face n) : boundary (cycle f) = 0 := by
  rcases f with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals
    simp only [cycle, map_sub, map_add, boundary_single, head, tail, ex, ey, ez]
    abel

def gradient (φ : Vertex n → Scalar) (e : Edge n) : Scalar := φ (head e) - φ (tail e)

def curl (l : Edge n → Scalar) (f : Face n) : Scalar := ∑ e, cycle f e * l e

@[simp] theorem curl_sub (l r : Edge n → Scalar) (f : Face n) :
    curl (l-r) f = curl l f - curl r f := by
  simp [curl, mul_sub, Finset.sum_sub_distrib]

def prefixSum (l : Fin n → Scalar) (i : Fin (n+1)) : Scalar :=
  ∑ a : Fin n, if a.val < i.val then l a else 0

@[simp] theorem prefix_zero (l : Fin n → Scalar) : prefixSum l 0 = 0 := by simp [prefixSum]

def phi1 (l : Edge n → Scalar) (v : Vertex n) : Scalar :=
  prefixSum (fun a => l (ex a v.2.1 v.2.2)) v.1

def residual1 (l : Edge n → Scalar) : Edge n → Scalar := l - gradient (phi1 l)

def phi2 (l : Edge n → Scalar) (i0 : Fin (n+1)) (v : Vertex n) : Scalar :=
  prefixSum (fun b => residual1 l (ey i0 b v.2.2)) v.2.1

def residual2 (l : Edge n → Scalar) (i0 : Fin (n+1)) : Edge n → Scalar :=
  residual1 l - gradient (phi2 l i0)

def phi3 (l : Edge n → Scalar) (i0 : Fin (n+1)) (v : Vertex n) : Scalar :=
  prefixSum (fun c => residual2 l i0 (ez i0 0 c)) v.2.2

def residual (l : Edge n → Scalar) (i0 : Fin (n+1)) : Edge n → Scalar :=
  residual2 l i0 - gradient (phi3 l i0)

def nonzeroSet {ι : Type*} [Fintype ι] (f : ι → Scalar) : Finset ι :=
  Finset.univ.filter (fun i => f i ≠ 0)

@[simp] theorem mem_nonzeroSet {ι : Type*} [Fintype ι] (f : ι → Scalar) (i : ι) :
    i ∈ nonzeroSet f ↔ f i ≠ 0 := by simp [nonzeroSet]

def badXY (l : Edge n → Scalar) : Finset (FaceXY n) :=
  nonzeroSet (fun f => curl l (.inl f))

def badXZ (l : Edge n → Scalar) : Finset (FaceXZ n) :=
  nonzeroSet (fun f => curl l (.inr (.inl f)))

def badYZ (l : Edge n → Scalar) : Finset (FaceYZ n) :=
  nonzeroSet (fun f => curl l (.inr (.inr f)))

def badSlice (l : Edge n → Scalar) (i : Fin (n+1)) : Finset (Fin n × Fin n) :=
  nonzeroSet (fun f => curl l (.inr (.inr (i,f))))

end CPTSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Grid

section

open Support

def pairing {ι : Type*} [Fintype ι] (l : ι → Scalar) : (ι → Scalar) →ₗ[Scalar] Scalar where
  toFun z := ∑ e, l e * z e
  map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem pairing_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : ι → Scalar) (e : ι) (z : Scalar) : pairing l (Pi.single e z) = l e * z := by
  classical
  change (∑ j, l j * (Pi.single e z : ι → Scalar) j) = _
  simp only [Pi.single_apply, mul_ite, mul_zero]
  simp

variable {n : ℕ}

abbrev FlowSpace (n : ℕ) := (boundary (n := n)).ker

def flowCycle (f : Face n) : FlowSpace n := ⟨cycle f, boundary_cycle f⟩

abbrev BoxGroup (n : ℕ) := Support.H (flowCycle (n := n))

def faceCodim (S : Subgroup (BoxGroup n)) : ℕ :=
  Module.finrank Scalar (Face n → Support.Plane) -
    Module.finrank Scalar (Support.H.projected flowCycle S)

def flowCodim (S : Subgroup (BoxGroup n)) : ℕ :=
  Module.finrank Scalar (FlowSpace n) -
    Module.finrank Scalar (Support.H.centralPart flowCycle S)

end

open Support

variable {n : ℕ}

theorem sum_subtype_zero {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (p : ι → Prop) [DecidablePred p] (f : ι → M) (h : ∀ i, ¬ p i → f i = 0) :
    (∑ i : {x // p x}, f i.val) = ∑ i, f i := by
  have hz : (∑ i : {x // ¬ p x}, f i.val) = 0 :=
    Finset.sum_eq_zero (fun i _ => h i.val i.property)
  simpa only [hz,add_zero] using Fintype.sum_subtype_add_sum_subtype p f

abbrev EdgeFaces (e : Edge n) := {f : Face n // cycle f e ≠ 0}

def localCycle (e : Edge n) (f : EdgeFaces e) : Scalar := cycle f.val e

abbrev LocalGroup (e : Edge n) := Support.H (localCycle e)

noncomputable def restrictGroup (e : Edge n) : BoxGroup n →* LocalGroup e where
  toFun g := ⟨fun f => g.face f.val, g.flow.val e⟩
  map_one' := rfl
  map_mul' := by
    intro g h
    apply Support.H.ext
    · rfl
    · simp only [Support.H.mul_flow, Submodule.coe_add, Pi.add_apply]
      congr 1
      simp only [Support.correction, Submodule.coe_smul, Submodule.coe_sum,
        Pi.smul_apply, Finset.sum_apply, smul_eq_mul, flowCycle, localCycle]
      congr 1
      exact (sum_subtype_zero _ _ (fun f hf => by simp_all)).symm

@[simp] theorem restrictGroup_face (g : BoxGroup n) (e : Edge n) (f : EdgeFaces e) :
    (restrictGroup e g).face f = g.face f.val := rfl

@[simp] theorem restrictGroup_flow (g : BoxGroup n) (e : Edge n) :
    (restrictGroup e g).flow = g.flow.val e := rfl

def incident (v : Vertex n) (e : Edge n) : Prop := head e = v ∨ tail e = v

instance instDecidableRelVertexEdgeIncident : DecidableRel (incident (n := n)) := fun v e =>
  inferInstanceAs (Decidable (head e = v ∨ tail e = v))

abbrev IncidentEdges (v : Vertex n) := {e : Edge n // incident v e}

noncomputable def epsilon (v : Vertex n) (e : Edge n) : Scalar :=
  (if head e = v then 1 else 0) - (if tail e = v then 1 else 0)

theorem boundary_eval (z : Edge n → Scalar) (v : Vertex n) :
    boundary z v = ∑ e, epsilon v e * z e := by
  classical
  simp only [boundary, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro e _
  simp [epsilon, Pi.single_apply, eq_comm, mul_comm]

theorem epsilon_eq_zero (v : Vertex n) (e : Edge n) (h : ¬ incident v e) :
    epsilon v e = 0 := by
  classical
  simp only [incident, not_or] at h
  simp [epsilon,h.1,h.2]

theorem sum_incident (z : Edge n → Scalar) (v : Vertex n) :
    (∑ e : IncidentEdges v, epsilon v e.val * z e.val) = boundary z v := by
  classical
  rw [boundary_eval]
  exact sum_subtype_zero (incident v) (fun e => epsilon v e * z e)
    (fun e he => by rw [epsilon_eq_zero v e he,zero_mul])

abbrev LocalStates (v : Vertex n) := (e : IncidentEdges v) → LocalGroup e.val

def Compatible {v : Vertex n} (s : LocalStates v) : Prop :=
  ∀ (e e' : IncidentEdges v) (f : Face n) (h : cycle f e.val ≠ 0)
    (h' : cycle f e'.val ≠ 0),
    (s e).face ⟨f,h⟩ = (s e').face ⟨f,h'⟩

theorem compatible_iff_extend {v : Vertex n} (s : LocalStates v) :
    Compatible s ↔ ∃ u : Face n → Plane,
      ∀ (e : IncidentEdges v) (f : EdgeFaces e.val), (s e).face f = u f.val := by
  classical
  constructor
  · intro h
    let u (f : Face n) : Plane := if hh : ∃ e : IncidentEdges v, cycle f e.val ≠ 0
      then (s hh.choose).face ⟨f,hh.choose_spec⟩ else 0
    refine ⟨u,?_⟩
    intro e f
    have hh : ∃ e : IncidentEdges v, cycle f.val e.val ≠ 0 := ⟨e,f.property⟩
    simp only [u,dite_eq_left hh]
    exact h e hh.choose f.val f.property hh.choose_spec
  · rintro ⟨u,h⟩ e e' f hf hf'
    rw [h e ⟨f,hf⟩, h e' ⟨f,hf'⟩]

noncomputable def divergence {v : Vertex n} (s : LocalStates v) : Scalar :=
  ∑ e : IncidentEdges v, epsilon v e.val * (s e).flow

structure Configuration (b : Vertex n → Scalar) (v : Vertex n) where
  state : LocalStates v
  compatible : Compatible state
  charge : divergence state = b v

@[ext] theorem Configuration.ext {b : Vertex n → Scalar} {v : Vertex n}
    {s t : Configuration b v} (h : ∀ e, s.state e = t.state e) : s = t := by
  cases s; cases t
  congr
  exact funext h

noncomputable def actState {v : Vertex n} (g : BoxGroup n) (s : LocalStates v) :
    LocalStates v := fun e => restrictGroup e.val g * s e

theorem actState_compatible {v : Vertex n} (g : BoxGroup n) (s : LocalStates v)
    (hs : Compatible s) : Compatible (actState g s) := by
  intro e e' f hf hf'
  simp only [actState, Support.H.mul_face, Pi.add_apply, restrictGroup_face]
  rw [hs e e' f hf hf']

theorem actState_divergence {v : Vertex n} (g : BoxGroup n) (s : LocalStates v)
    (hs : Compatible s) : divergence (actState g s) = divergence s := by
  classical
  obtain ⟨u,hu⟩ := (compatible_iff_extend s).mp hs
  have hc (e : IncidentEdges v) : Support.correction (localCycle e.val)
      (restrictGroup e.val g).face (s e).face =
        (Support.correction flowCycle g.face u).val e.val := by
    have heq : (s e).face = fun f : EdgeFaces e.val => u f.val := funext (hu e)
    rw [heq]
    simp only [Support.correction, Submodule.coe_smul, Submodule.coe_sum,
      Pi.smul_apply, Finset.sum_apply, smul_eq_mul, flowCycle, localCycle,
      restrictGroup_face]
    congr 1
    exact sum_subtype_zero (fun f : Face n => cycle f e.val ≠ 0)
      (fun f => omega (g.face f) (u f) * cycle f e.val)
      (fun f hf => by push Not at hf; simp only [hf,mul_zero])
  simp only [divergence, actState, Support.H.mul_flow, restrictGroup_flow,
    mul_add, Finset.sum_add_distrib]
  simp_rw [hc]
  rw [sum_incident, sum_incident]
  have hg := congrFun g.flow.property v
  have hb := congrFun (Support.correction flowCycle g.face u).property v
  simp only [Pi.zero_apply] at hg hb
  simp [hg,hb]

noncomputable def actConfiguration {b : Vertex n → Scalar} {v : Vertex n}
    (g : BoxGroup n) (s : Configuration b v) : Configuration b v where
  state := actState g s.state
  compatible := actState_compatible g s.state s.compatible
  charge := by rw [actState_divergence g s.state s.compatible, s.charge]

noncomputable instance instMulActionBoxGroupConfiguration {b : Vertex n → Scalar} {v : Vertex n} :
    MulAction (BoxGroup n) (Configuration b v) where
  smul := actConfiguration
  one_smul s := by
    apply Configuration.ext
    intro e
    change restrictGroup e.val (1 : BoxGroup n) * s.state e = s.state e
    simp only [map_one,one_mul]
  mul_smul g h s := by
    apply Configuration.ext
    intro e
    change restrictGroup e.val (g*h) * s.state e =
      restrictGroup e.val g * (restrictGroup e.val h * s.state e)
    simp only [map_mul,mul_assoc]

abbrev Atom (b : Vertex n → Scalar) := (Σ e : Edge n, LocalGroup e) ⊕
  (Σ v : Vertex n, Configuration b v)

noncomputable def actAtom {b : Vertex n → Scalar} (g : BoxGroup n) : Atom b → Atom b
  | .inl ⟨e,s⟩ => .inl ⟨e, restrictGroup e g * s⟩
  | .inr ⟨v,s⟩ => .inr ⟨v,g • s⟩

noncomputable instance instMulActionBoxGroupAtom {b : Vertex n → Scalar} : MulAction (BoxGroup n) (Atom b) where
  smul := actAtom
  one_smul x := by
    change actAtom 1 x = x
    cases x with
    | inl x => rcases x with ⟨e,s⟩; simp only [actAtom,map_one,one_mul]
    | inr x => rcases x with ⟨v,s⟩; simp only [actAtom,one_smul]
  mul_smul g h x := by
    change actAtom (g*h) x = actAtom g (actAtom h x)
    cases x with
    | inl x => rcases x with ⟨e,s⟩; simp only [actAtom,map_mul,mul_assoc]
    | inr x => rcases x with ⟨v,s⟩; simp only [actAtom,mul_smul]

end CPTSeparation.Grid

namespace CPTSeparation

namespace Input

variable {A B : Type} [finiteA : Fintype A] [finiteB : Fintype B]

instance instDecidableEqEdge [DecidableEq A] (S : Input A) : DecidableEq S.Edge := inferInstanceAs (DecidableEq (Subtype _))

instance instDecidableEqConfig [DecidableEq A] (S : Input A) : DecidableEq S.Config := inferInstanceAs (DecidableEq (Subtype _))

namespace Iso

variable {S : Input A} {T : Input B} (e : S.Iso T)

def edgeEquiv : S.Edge ≃ T.Edge :=
  e.toEquiv.subtypeEquiv (fun a => by simp only [e.rel_eq])

def configEquiv : S.Config ≃ T.Config :=
  e.toEquiv.subtypeEquiv (fun a => by simp only [e.rel_eq])

omit A B S T e in
@[simp] theorem edgeEquiv_val
    {A : Type}
    {B : Type}
    [Fintype A]
    [Fintype B]
    {S : Input A}
    {T : Input B}
    (e : S.Iso T) (x : S.Edge) : (e.edgeEquiv x).val = e.toEquiv x := rfl

omit A B S T e in
@[simp] theorem configEquiv_val
    {A : Type}
    {B : Type}
    [Fintype A]
    [Fintype B]
    {S : Input A}
    {T : Input B}
    (e : S.Iso T) (x : S.Config) : (e.configEquiv x).val = e.toEquiv x := rfl

@[simp] theorem coefficient_eq (y : S.Edge) (a : S.Config) :
    T.coefficient (e.edgeEquiv y) (e.configEquiv a) = S.coefficient y a := by
  unfold coefficient
  symm
  apply Fintype.sum_equiv e.edgeEquiv
  intro x
  simp [edgeEquiv, configEquiv, e.rel_eq]

omit A B S T e in
@[simp] theorem incident_eq
    {A : Type}
    {B : Type}
    [Fintype A]
    [Fintype B]
    {S : Input A}
    {T : Input B}
    (e : S.Iso T) (t : S.Config) (y : S.Edge) :
    T.incident (e.configEquiv t) (e.edgeEquiv y) ↔ S.incident t y := by
  unfold incident
  constructor
  · rintro ⟨a, ha, x, hx, hy⟩
    refine ⟨e.configEquiv.symm a, ?_, e.edgeEquiv.symm x, ?_, ?_⟩
    all_goals
      have heqa : e.toEquiv (e.configEquiv.symm a).val = a.val :=
        congrArg Subtype.val (e.configEquiv.apply_symm_apply a)
      have heqx : e.toEquiv (e.edgeEquiv.symm x).val = x.val :=
        congrArg Subtype.val (e.edgeEquiv.apply_symm_apply x)
      first
      | simpa only [configEquiv_val, edgeEquiv_val, ← heqa, ← heqx, e.rel_eq] using ha
      | simpa only [configEquiv_val, edgeEquiv_val, ← heqa, ← heqx, e.rel_eq] using hx
      | simpa only [configEquiv_val, edgeEquiv_val, ← heqa, ← heqx, e.rel_eq] using hy
  · rintro ⟨a, ha, x, hx, hy⟩
    refine ⟨e.configEquiv a, ?_, e.edgeEquiv x, ?_, ?_⟩
    · simpa only [configEquiv_val, e.rel_eq] using ha
    · simpa only [configEquiv_val, edgeEquiv_val, e.rel_eq] using hx
    · simpa only [edgeEquiv_val, e.rel_eq] using hy

def symm : T.Iso S where
  toEquiv := e.toEquiv.symm
  rel_eq r x y := by
    simpa only [Equiv.apply_symm_apply] using
      (e.rel_eq r (e.toEquiv.symm x) (e.toEquiv.symm y)).symm

end Iso

end Input

end CPTSeparation

namespace CPTSeparation.Grid

section

open Support

variable {n : ℕ} {b : Vertex n → Scalar}

instance instFiniteConfiguration {v : Vertex n} : Finite (Configuration b v) :=
  Finite.of_injective (fun s : Configuration b v => s.state)
    (fun _ _ h => Configuration.ext (fun e => congrFun h e))

noncomputable instance instFintypeConfiguration {v : Vertex n} : Fintype (Configuration b v) := Fintype.ofFinite _

inductive AtomRelation (b : Vertex n → Scalar) : Symbol → Atom b → Atom b → Prop
  | ed (e : Edge n) (s : LocalGroup e) :
      AtomRelation b .Ed (.inl ⟨e,s⟩) (.inl ⟨e,s⟩)
  | cf (v : Vertex n) (s : Configuration b v) :
      AtomRelation b .Cf (.inr ⟨v,s⟩) (.inr ⟨v,s⟩)
  | eb (e : Edge n) (s t : LocalGroup e) :
      AtomRelation b .EB (.inl ⟨e,s⟩) (.inl ⟨e,t⟩)
  | vb (v : Vertex n) (s t : Configuration b v) :
      AtomRelation b .VB (.inr ⟨v,s⟩) (.inr ⟨v,t⟩)
  | inc (v : Vertex n) (s : Configuration b v) (e : IncidentEdges v) :
      AtomRelation b .I (.inr ⟨v,s⟩) (.inl ⟨e.val,s.state e⟩)
  | z (e : Edge n) (s t : LocalGroup e) (δ : Scalar) (h : (s⁻¹*t).flow = δ) :
      AtomRelation b (.Z δ) (.inl ⟨e,s⟩) (.inl ⟨e,t⟩)

theorem AtomRelation.map (g : BoxGroup n) {r : Symbol} {x y : Atom b}
    (h : AtomRelation b r x y) : AtomRelation b r (g • x) (g • y) := by
  cases h with
  | ed e s => exact .ed e _
  | cf v s => exact .cf v _
  | eb e s t => exact .eb e _ _
  | vb v s t => exact .vb v _ _
  | inc v s e => exact .inc v (g • s) e
  | z e s t δ h =>
    apply AtomRelation.z
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using h

theorem AtomRelation.map_iff (g : BoxGroup n) (r : Symbol) (x y : Atom b) :
    AtomRelation b r (g • x) (g • y) ↔ AtomRelation b r x y := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using h.map g⁻¹
  · exact fun h => h.map g

noncomputable def atomInput (b : Vertex n → Scalar) : Input (Atom b) :=
  ⟨fun r x y => @decide (AtomRelation b r x y) (Classical.propDecidable _)⟩

noncomputable def actionIso (g : BoxGroup n) : (atomInput b).Iso (atomInput b) where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv := inv_smul_smul g
  right_inv := smul_inv_smul g
  rel_eq := by
    intro r x y
    exact congrArg (fun p => @decide p (Classical.propDecidable p))
      (propext (AtomRelation.map_iff g r x y))

def zeroEdgeAtom (b : Vertex n → Scalar) (e : Edge n) : Atom b := .inl ⟨e,1⟩

@[simp] theorem central_fix_zeroEdgeAtom_iff (k : FlowSpace n) (e : Edge n) :
    Support.H.central flowCycle k • zeroEdgeAtom b e = zeroEdgeAtom b e ↔ k.val e = 0 := by
  change (Sum.inl ⟨e,restrictGroup e (Support.H.central flowCycle k) * 1⟩ : Atom b) =
    (Sum.inl ⟨e,(1 : LocalGroup e)⟩ : Atom b) ↔ _
  simp only [mul_one, Sum.inl.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  constructor
  · intro h
    exact congrArg Support.H.flow h
  · intro h
    apply Support.H.ext
    · rfl
    · exact h

abbrev CentralGroup (n : ℕ) := Multiplicative (FlowSpace n)

def centralHom : CentralGroup n →* BoxGroup n where
  toFun k := Support.H.central flowCycle k.toAdd
  map_one' := rfl
  map_mul' k l := (Support.H.central_mul flowCycle k.toAdd l.toAdd).symm

noncomputable instance instMulActionCentralGroupAtom : MulAction (CentralGroup n) (Atom b) :=
  MulAction.compHom _ centralHom

@[simp] theorem central_smul_atom (k : CentralGroup n) (x : Atom b) :
    k • x = Support.H.central flowCycle k.toAdd • x := rfl

end

section

variable {n : ℕ}

theorem head_ne_tail (e : Edge n) : head e ≠ tail e := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals simp only [head,tail]
  · intro h
    have hu := congrArg (fun v : Vertex n => v.1.val) h
    simp only [Fin.val_succ,Fin.val_castSucc] at hu
    omega
  · intro h
    have hu := congrArg (fun v : Vertex n => v.2.1.val) h
    simp only [Fin.val_succ,Fin.val_castSucc] at hu
    omega
  · intro h
    have hu := congrArg (fun v : Vertex n => v.2.2.val) h
    simp only [Fin.val_succ,Fin.val_castSucc] at hu
    omega

def edgeAxis : Edge n → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

theorem exists_head_or_tail (hn : 1 ≤ n) (v : Vertex n) :
    ∃ e : Edge n, head e = v ∨ tail e = v := by
  rcases v with ⟨i,j,k⟩
  by_cases hi : i.val = 0
  · refine ⟨ex ⟨0,by omega⟩ j k, Or.inr ?_⟩
    simp only [ex,tail,Prod.mk.injEq, and_true]
    apply Fin.ext
    exact hi.symm
  · refine ⟨ex ⟨i.val-1,by omega⟩ j k, Or.inl ?_⟩
    simp only [ex,head,Prod.mk.injEq,and_true]
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

end

section

open Support

variable {n : ℕ} {b : Vertex n → Scalar}

noncomputable instance instFintypeLocalGroup (e : Edge n) : Fintype (LocalGroup e) := Fintype.ofFinite _

noncomputable instance instFintypeAtom : Fintype (Atom b) := Fintype.ofFinite _

@[simp] theorem atomInput_rel_true (r : Symbol) (x y : Atom b) :
    (atomInput b).rel r x y = true ↔ AtomRelation b r x y := by
  simp [atomInput]

def queryEdge (e : Edge n) (g : LocalGroup e) : (atomInput b).Edge :=
  ⟨.inl ⟨e,g⟩,by simp only [atomInput_rel_true]; exact .ed e g⟩

def queryConfig (v : Vertex n) (s : Configuration b v) : (atomInput b).Config :=
  ⟨.inr ⟨v,s⟩,by simp only [atomInput_rel_true]; exact .cf v s⟩

theorem exists_queryEdge (y : (atomInput b).Edge) :
    ∃ (e : Edge n) (g : LocalGroup e), y = queryEdge e g := by
  rcases y with ⟨y,hy⟩
  have h := (atomInput_rel_true .Ed y y).mp hy
  cases h with
  | ed e g => exact ⟨e,g,rfl⟩

theorem exists_queryConfig (a : (atomInput b).Config) :
    ∃ (v : Vertex n) (s : Configuration b v), a = queryConfig v s := by
  rcases a with ⟨a,ha⟩
  have h := (atomInput_rel_true .Cf a a).mp ha
  cases h with
  | cf v s => exact ⟨v,s,rfl⟩

@[simp] theorem queryEdge_eq {e e' : Edge n} {g : LocalGroup e} {g' : LocalGroup e'} :
    queryEdge (b := b) e g = queryEdge e' g' ↔ (⟨e,g⟩ : Σ e, LocalGroup e) = ⟨e',g'⟩ := by
  simp [queryEdge,Subtype.ext_iff]

@[simp] theorem queryConfig_eq {v v' : Vertex n} {s : Configuration b v}
    {s' : Configuration b v'} :
    queryConfig v s = queryConfig v' s' ↔ (⟨v,s⟩ : Σ v, Configuration b v) = ⟨v',s'⟩ := by
  simp [queryConfig,Subtype.ext_iff]

def queryEdgeEquiv : (Σ e : Edge n, LocalGroup e) ≃ (atomInput b).Edge :=
  Equiv.ofBijective (fun x => queryEdge x.1 x.2) ⟨by
    rintro ⟨e,g⟩ ⟨e',g'⟩ h
    exact queryEdge_eq.mp h,
    fun y => by obtain ⟨e,g,rfl⟩ := exists_queryEdge y; exact ⟨⟨e,g⟩,rfl⟩⟩

def queryConfigEquiv : (Σ v : Vertex n, Configuration b v) ≃ (atomInput b).Config :=
  Equiv.ofBijective (fun x => queryConfig x.1 x.2) ⟨by
    rintro ⟨v,s⟩ ⟨v',s'⟩ h
    exact queryConfig_eq.mp h,
    fun a => by obtain ⟨v,s,rfl⟩ := exists_queryConfig a; exact ⟨⟨v,s⟩,rfl⟩⟩

@[simp] theorem rel_vb (v w : Vertex n) (s : Configuration b v) (t : Configuration b w) :
    (atomInput b).rel .VB (queryConfig v s) (queryConfig w t) = true ↔ v = w := by
  rw [atomInput_rel_true]
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .vb v s t

@[simp] theorem rel_eb (e f : Edge n) (g : LocalGroup e) (h : LocalGroup f) :
    (atomInput b).rel .EB (queryEdge (b := b) e g) (queryEdge (b := b) f h) = true ↔ e = f := by
  rw [atomInput_rel_true]
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .eb e g h

@[simp] theorem rel_inc (v : Vertex n) (s : Configuration b v) (e : Edge n)
    (g : LocalGroup e) :
    (atomInput b).rel .I (queryConfig v s) (queryEdge (b := b) e g) = true ↔
      ∃ h : incident v e, s.state ⟨e,h⟩ = g := by
  rw [atomInput_rel_true]
  constructor
  · intro h
    cases h with
    | inc v s e => exact ⟨e.property,rfl⟩
  · rintro ⟨h,rfl⟩
    exact .inc v s ⟨e,h⟩

@[simp] theorem rel_z_same (e : Edge n) (g h : LocalGroup e) (d : Scalar) :
    (atomInput b).rel (.Z d) (queryEdge (b := b) e g) (queryEdge (b := b) e h) = true ↔ (g⁻¹*h).flow = d := by
  rw [atomInput_rel_true]
  constructor
  · intro h
    cases h with
    | z e g h d hd => exact hd
  · intro hd
    exact .z e g h d hd

@[simp] theorem epsilon_head (e : Edge n) : epsilon (head e) e = 1 := by
  simp [epsilon,Ne.symm (head_ne_tail e)]

@[simp] theorem epsilon_tail (e : Edge n) : epsilon (tail e) e = -1 := by
  simp [epsilon,head_ne_tail e]

theorem epsilon_sq (v : Vertex n) (e : IncidentEdges v) : epsilon v e.val ^ 2 = 1 := by
  rcases e with ⟨e,he⟩
  rcases he with h | h
  · subst v; simp
  · subst v; simp

def someConfiguration (hn : 1 ≤ n) (b : Vertex n → Scalar) (v : Vertex n) : Configuration b v := by
  classical
  let e : IncidentEdges v := ⟨(exists_head_or_tail hn v).choose,(exists_head_or_tail hn v).choose_spec⟩
  let states : LocalStates v := fun f => ⟨0,if f = e then epsilon v e.val * b v else 0⟩
  refine ⟨states,?_,?_⟩
  · intro f f' d hd hd'
    rfl
  · dsimp [divergence,states]
    simp only [mul_ite,mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ e]
    simp only [Finset.mem_univ,ite_true]
    rw [← mul_assoc,← pow_two,epsilon_sq,one_mul]

def zeroConfiguration (v : Vertex n) : Configuration (0 : Vertex n → Scalar) v where
  state := fun _ => 1
  compatible := by intro e e' f hf hf'; rfl
  charge := by simp [divergence,Support.H.one_flow]

def zeroWeight (a : (atomInput (0 : Vertex n → Scalar)).Config) : Scalar := by
  classical
  exact match a.val with
  | .inl _ => 0
  | .inr ⟨v,t⟩ => if t = zeroConfiguration v then 1 else 0

def zeroMu (y : (atomInput (0 : Vertex n → Scalar)).Edge) : Scalar :=
  match y.val with
  | .inl ⟨_,g⟩ => -g.flow
  | .inr _ => 0

end

open Classical Support

variable {n : ℕ} {b b' b'' : Vertex n → Scalar}

def shiftLocal (e : Edge n) (z : Scalar) (s : LocalGroup e) : LocalGroup e :=
  Support.H.central (localCycle e) z * s

@[simp] theorem shiftLocal_face (e : Edge n) (z : Scalar) (s : LocalGroup e) :
    (shiftLocal e z s).face = s.face := by
  simp [shiftLocal,Support.H.mul_face,Support.H.central]

@[simp] theorem shiftLocal_flow (e : Edge n) (z : Scalar) (s : LocalGroup e) :
    (shiftLocal e z s).flow = z+s.flow := by
  simp [shiftLocal,Support.H.mul_flow,Support.H.central,Support.correction]

@[simp] theorem shiftLocal_zero (e : Edge n) (s : LocalGroup e) : shiftLocal e 0 s = s := by
  ext <;> simp

@[simp] theorem shiftLocal_add (e : Edge n) (z w : Scalar) (s : LocalGroup e) :
    shiftLocal e z (shiftLocal e w s) = shiftLocal e (z+w) s := by
  ext <;> simp [add_assoc]

def localShiftEquiv (e : Edge n) (z : Scalar) : LocalGroup e ≃ LocalGroup e where
  toFun := shiftLocal e z
  invFun := shiftLocal e (-z)
  left_inv := by intro s; simp
  right_inv := by intro s; simp

def shiftStates {v : Vertex n} (t : Edge n → Scalar) (s : LocalStates v) : LocalStates v :=
  fun e => shiftLocal e.val (t e.val) (s e)

theorem shiftStates_compatible {v : Vertex n} (t : Edge n → Scalar) (s : LocalStates v)
    (hs : Compatible s) : Compatible (shiftStates t s) := by
  intro e e' f hf hf'
  simpa only [shiftStates,shiftLocal_face] using hs e e' f hf hf'

theorem shiftStates_divergence {v : Vertex n} (t : Edge n → Scalar) (s : LocalStates v) :
    divergence (shiftStates t s) = boundary t v + divergence s := by
  simp only [divergence,shiftStates,shiftLocal_flow,mul_add,Finset.sum_add_distrib,sum_incident]

def Configuration.shift {v : Vertex n} (s : Configuration b v) (t : Edge n → Scalar)
    (h : boundary t v = b' v - b v) : Configuration b' v where
  state := shiftStates t s.state
  compatible := shiftStates_compatible t s.state s.compatible
  charge := by rw [shiftStates_divergence,s.charge,h]; abel

@[simp] theorem Configuration.shift_state {v : Vertex n} (s : Configuration b v)
    (t : Edge n → Scalar) (h : boundary t v = b' v - b v) (e : IncidentEdges v) :
    (s.shift t h).state e = shiftLocal e.val (t e.val) (s.state e) := rfl

def configShiftEquiv (v : Vertex n) (t : Edge n → Scalar)
    (h : boundary t v = b' v - b v) : Configuration b v ≃ Configuration b' v where
  toFun s := s.shift t h
  invFun s := s.shift (-t) (by simp only [map_neg,Pi.neg_apply,h]; abel)
  left_inv s := by apply Configuration.ext; intro e; simp
  right_inv s := by apply Configuration.ext; intro e; simp

inductive AtomShift (t : Edge n → Scalar) : Atom b → Atom b' → Prop
  | edge (e : Edge n) (s : LocalGroup e) :
      AtomShift t (.inl ⟨e,s⟩) (.inl ⟨e,shiftLocal e (t e) s⟩)
  | config (v : Vertex n) (s : Configuration b v) (h : boundary t v = b' v - b v) :
      AtomShift t (.inr ⟨v,s⟩) (.inr ⟨v,s.shift t h⟩)

theorem AtomShift.symm {t : Edge n → Scalar} {x : Atom b} {y : Atom b'}
    (h : AtomShift t x y) : AtomShift (-t) y x := by
  cases h with
  | edge e s => simpa using (AtomShift.edge (b := b') (b' := b) (t := -t) e (shiftLocal e (t e) s))
  | config v s h =>
    have hh : boundary (-t) v = b v - b' v := by simp only [map_neg,Pi.neg_apply,h]; abel
    have he : (s.shift t h).shift (-t) hh = s := by apply Configuration.ext; intro e; simp
    simpa only [he] using (AtomShift.config (t := -t) v (s.shift t h) hh)

def blockShiftEquiv (te : Edge n → Edge n → Scalar) (tv : Vertex n → Edge n → Scalar)
    (hv : ∀ v, boundary (tv v) v = b' v - b v) : Atom b ≃ Atom b' :=
  Equiv.sumCongr (Equiv.sigmaCongrRight fun e => localShiftEquiv e (te e e))
    (Equiv.sigmaCongrRight fun v => configShiftEquiv v (tv v) (hv v))

end CPTSeparation.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Counting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Counting

section

variable {R I A B : Type*}

structure Structure (R : Type*) (A : Type*) where
  rel : R → A → A → Prop

inductive Formula (R I : Type*)
  | falsum
  | equal (x y : I)
  | relation (r : R) (x y : I)
  | neg (φ : Formula R I)
  | and (φ ψ : Formula R I)
  | ex (x : I) (φ : Formula R I)
  | exact (x : I) (n : ℕ) (φ : Formula R I)
  deriving DecidableEq

namespace Formula

variable [DecidableEq I]

def free : Formula R I → Finset I
  | .falsum => ∅
  | .equal x y => {x,y}
  | .relation _ x y => {x,y}
  | .neg φ => φ.free
  | .and φ ψ => φ.free ∪ ψ.free
  | .ex x φ => φ.free.erase x
  | .exact x _ φ => φ.free.erase x

def eval (S : Structure R A) : Formula R I → (I → A) → Prop
  | .falsum, _ => False
  | .equal x y, v => v x = v y
  | .relation r x y, v => S.rel r (v x) (v y)
  | .neg φ, v => ¬ φ.eval S v
  | .and φ ψ, v => φ.eval S v ∧ ψ.eval S v
  | .ex x φ, v => ∃ a, φ.eval S (Function.update v x a)
  | .exact x n φ, v => Nonempty ({a : A // φ.eval S (Function.update v x a)} ≃ Fin n)

theorem eval_congr (S : Structure R A) (φ : Formula R I) {v w : I → A}
    (h : ∀ i ∈ φ.free, v i = w i) : φ.eval S v ↔ φ.eval S w := by
  induction φ generalizing v w with
  | falsum => rfl
  | equal x y => simp only [eval,h x (by simp [free]),h y (by simp [free])]
  | relation r x y => simp only [eval,h x (by simp [free]),h y (by simp [free])]
  | neg φ ih => exact not_congr (ih h)
  | and φ ψ ihφ ihψ =>
    apply and_congr
    · exact ihφ (fun i hi => h i (Finset.mem_union_left _ hi))
    · exact ihψ (fun i hi => h i (Finset.mem_union_right _ hi))
  | ex x φ ih =>
    apply exists_congr
    intro a
    apply ih
    intro i hi
    by_cases heq : i = x
    · subst i; simp
    · simp only [Function.update_of_ne heq]
      exact h i (Finset.mem_erase.mpr ⟨heq,hi⟩)
  | exact x n φ ih =>
    have heq : ∀ a, φ.eval S (Function.update v x a) ↔ φ.eval S (Function.update w x a) := by
      intro a
      apply ih
      intro i hi
      by_cases heq : i = x
      · subst i; simp
      · simp only [Function.update_of_ne heq]
        exact h i (Finset.mem_erase.mpr ⟨heq,hi⟩)
    let e := Equiv.subtypeEquivRight heq
    exact ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩

theorem eval_of_bijectionSystem (S : Structure R A) (T : Structure R B)
    (E : (I → A) → (I → B) → Prop)
    (hequal : ∀ v w, E v w → ∀ i j, (v i = v j ↔ w i = w j))
    (hrel : ∀ v w, E v w → ∀ r i j, S.rel r (v i) (v j) ↔ T.rel r (w i) (w j))
    (hext : ∀ v w, E v w → ∀ i, ∃ e : A ≃ B,
      ∀ a, E (Function.update v i a) (Function.update w i (e a)))
    (φ : Formula R I) : ∀ v w, E v w → (φ.eval S v ↔ φ.eval T w) := by
  induction φ with
  | falsum => intro v w h; rfl
  | equal i j => intro v w h; exact hequal v w h i j
  | relation r i j => intro v w h; exact hrel v w h r i j
  | neg φ ih => intro v w h; exact not_congr (ih v w h)
  | and φ ψ ihφ ihψ => intro v w h; exact and_congr (ihφ v w h) (ihψ v w h)
  | ex i φ ih =>
    intro v w h
    obtain ⟨e,he⟩ := hext v w h i
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨e a,(ih _ _ (he a)).mp ha⟩
    · rintro ⟨b,hb⟩
      obtain ⟨a,rfl⟩ := e.surjective b
      exact ⟨a,(ih _ _ (he a)).mpr hb⟩
  | exact i n φ ih =>
    intro v w h
    obtain ⟨e,he⟩ := hext v w h i
    let f : {a : A // φ.eval S (Function.update v i a)} ≃
        {b : B // φ.eval T (Function.update w i b)} :=
      e.subtypeEquiv (fun a => ih _ _ (he a))
    exact ⟨fun ⟨g⟩ => ⟨f.symm.trans g⟩, fun ⟨g⟩ => ⟨f.trans g⟩⟩

def conjoin : List (Formula R I) → Formula R I
  | [] => .neg .falsum
  | φ :: l => .and φ (conjoin l)

@[simp] theorem eval_conjoin (S : Structure R A) (l : List (Formula R I)) (v : I → A) :
    (conjoin l).eval S v ↔ ∀ φ ∈ l, φ.eval S v := by
  induction l with
  | nil => simp [conjoin,eval]
  | cons φ l ih => simp [conjoin,eval,ih]

end Formula

variable [DecidableEq I]

def typeOf (S : Structure R A) (names : Finset I) (v : I → A) : Set (Formula R I) :=
  {φ | φ.free ⊆ names ∧ φ.eval S v}

theorem typeOf_eq_iff (S : Structure R A) (T : Structure R B) (names : Finset I)
    (v : I → A) (w : I → B) : typeOf S names v = typeOf T names w ↔
      ∀ φ : Formula R I, φ.free ⊆ names → (φ.eval S v ↔ φ.eval T w) := by
  constructor
  · intro h φ hφ
    have heq := Set.ext_iff.mp h φ
    simpa only [typeOf,Set.mem_ofPred_eq,hφ,true_and] using heq
  · intro h
    ext φ
    exact and_congr_right (h φ)

end

variable {R I A B : Type*} [decidableI : DecidableEq I]

namespace Formula

def rename (e : I ≃ I) : Formula R I → Formula R I
  | .falsum => .falsum
  | .equal i j => .equal (e i) (e j)
  | .relation r i j => .relation r (e i) (e j)
  | .neg φ => .neg (φ.rename e)
  | .and φ ψ => .and (φ.rename e) (ψ.rename e)
  | .ex i φ => .ex (e i) (φ.rename e)
  | .exact i n φ => .exact (e i) n (φ.rename e)

@[simp] theorem free_rename (e : I ≃ I) (φ : Formula R I) :
    (φ.rename e).free = φ.free.map e.toEmbedding := by
  induction φ with
  | falsum => simp [rename, free]
  | equal i j => simp [rename, free]
  | relation r i j => simp [rename, free]
  | neg φ ih => simpa [rename, free] using ih
  | and φ ψ ihφ ihψ => simp [rename, free, ihφ, ihψ, Finset.map_union]
  | ex i φ ih => simp [rename, free, ih, Finset.map_erase]
  | exact i n φ ih => simp [rename, free, ih, Finset.map_erase]

@[simp] theorem eval_rename (S : Structure R A) (e : I ≃ I) (φ : Formula R I)
    (v : I → A) : (φ.rename e).eval S v ↔ φ.eval S (v ∘ e) := by
  induction φ generalizing v with
  | falsum => rfl
  | equal i j => rfl
  | relation r i j => rfl
  | neg φ ih => exact not_congr (ih v)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ v) (ihψ v)
  | ex i φ ih =>
    simp only [rename,eval]
    apply exists_congr
    intro a
    rw [ih,Function.update_comp_eq_of_injective _ e.injective]
  | exact i n φ ih =>
    have h (a : A) : (φ.rename e).eval S (Function.update v (e i) a) ↔
        φ.eval S (Function.update (v ∘ e) i a) := by
      rw [ih,Function.update_comp_eq_of_injective _ e.injective]
    let f := Equiv.subtypeEquivRight h
    exact ⟨fun ⟨g⟩ => ⟨f.symm.trans g⟩, fun ⟨g⟩ => ⟨f.trans g⟩⟩

end Formula

theorem typeOf_congr (S : Structure R A) (names : Finset I) {v w : I → A}
    (h : ∀ i ∈ names, v i = w i) : typeOf S names v = typeOf S names w := by
  apply (typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hf
  exact φ.eval_congr S (fun i hi => h i (hf hi))

section Tuple

variable {J J' : Type*} [Fintype J] [Fintype J']

def tupleNames (e : J ↪ I) : Finset I := Finset.univ.map e

omit I J in
@[simp] theorem mem_tupleNames.{uDecl2, uDecl5}
    {I : Type uDecl2}
    [DecidableEq I]
    {J : Type uDecl5}
    [Fintype J] (e : J ↪ I) (i : I) :
    i ∈ tupleNames e ↔ ∃ j, e j = i := by simp [tupleNames]

def tupleAssignment [Nonempty A] (e : J ↪ I) (a : J → A) (i : I) : A :=
  if h : ∃ j, e j = i then a (Classical.choose h) else Classical.choice inferInstance

@[simp] theorem tupleAssignment_apply [Nonempty A] (e : J ↪ I) (a : J → A) (j : J) :
    tupleAssignment e a (e j) = a j := by
  classical
  rw [tupleAssignment,dite_eq_left ⟨j,rfl⟩]
  congr 1
  exact e.injective (Classical.choose_spec (show ∃ k, e k = e j from ⟨j,rfl⟩))

def tupleType [Nonempty A] (S : Structure R A) (e : J ↪ I) (a : J → A) :
    Set (Formula R I) := typeOf S (tupleNames e) (tupleAssignment e a)

theorem tupleType_assignment [Nonempty A] (S : Structure R A) (e : J ↪ I)
    (a : J → A) (v : I → A) (h : ∀ j, v (e j) = a j) :
    tupleType S e a = typeOf S (tupleNames e) v := by
  apply typeOf_congr
  intro i hi
  obtain ⟨j,rfl⟩ := (mem_tupleNames e i).mp hi
  rw [tupleAssignment_apply,h]

end Tuple

theorem eval_iso (S : Structure R A) (T : Structure R B) (e : A ≃ B)
    (he : ∀ r a b, S.rel r a b ↔ T.rel r (e a) (e b))
    (φ : Formula R I) (v : I → A) : φ.eval S v ↔ φ.eval T (e ∘ v) := by
  apply φ.eval_of_bijectionSystem S T (fun v w => ∀ i, w i = e (v i))
  · intro v w h i j
    rw [h i,h j]
    exact e.injective.eq_iff.symm
  · intro v w h r i j
    rw [h i,h j]
    exact he r (v i) (v j)
  · intro v w h i
    refine ⟨e,fun a j => ?_⟩
    by_cases hij : j = i
    · subst j; simp
    · simp only [Function.update_of_ne hij,h j]
  · intro i; rfl

theorem tupleType_iso {J : Type*} [Fintype J] [Nonempty A] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (names : J ↪ I) (e : A ≃ B)
    (he : ∀ r a b, S.rel r a b ↔ T.rel r (e a) (e b)) (a : J → A) :
    tupleType S names a = tupleType T names (e ∘ a) := by
  rw [tupleType_assignment T names (e ∘ a) (e ∘ tupleAssignment names a)
    (fun j => by simp)]
  apply (typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hφ
  exact eval_iso S T e he φ _

end CPTSeparation.Counting

namespace CPTSeparation.Grid

section

open Classical Finset

variable {n : ℕ} {b b' : Vertex n → Scalar}

abbrev ClassLabel (n : ℕ) :=
  (Σ e : Edge n, EdgeFaces e → Support.Plane) ⊕
  (Σ v : Vertex n, (e : IncidentEdges v) → EdgeFaces e.val → Support.Plane)

instance instFintypeClassLabel : Fintype (ClassLabel n) := by
  letI : ∀ v : Vertex n, Finite ((e : IncidentEdges v) → EdgeFaces e.val → Support.Plane) :=
    fun v => inferInstance
  exact Fintype.ofFinite _

def classLabel : Atom b → ClassLabel n
  | .inl ⟨e,s⟩ => .inl ⟨e,s.face⟩
  | .inr ⟨v,s⟩ => .inr ⟨v,fun e => (s.state e).face⟩

def classIndex (x : Atom b) : Fin (Fintype.card (ClassLabel n)) :=
  Fintype.equivFin (ClassLabel n) (classLabel x)

inductive AnalysisSymbol
  | input (s : Symbol)
  | preorder
  | raw (δ : Scalar)
  deriving DecidableEq, Fintype

def rawDifference (b : Vertex n → Scalar) (δ : Scalar) : Atom b → Atom b → Prop
  | .inl ⟨e,s⟩, .inl ⟨f,t⟩ => e = f ∧ t.flow - s.flow = δ
  | _, _ => False

def analysisStructure (b : Vertex n → Scalar) : Counting.Structure AnalysisSymbol (Atom b) where
  rel r x y := match r with
    | .input s => AtomRelation b s x y
    | .preorder => classIndex x ≤ classIndex y
    | .raw δ => rawDifference b δ x y

@[simp] theorem classLabel_shiftLocal (e : Edge n) (s : LocalGroup e) (t : Scalar) :
    classLabel (b := b') (.inl ⟨e,shiftLocal e t s⟩) = classLabel (b := b) (.inl ⟨e,s⟩) := by
  simp [classLabel]

@[simp] theorem classLabel_shiftConfig (v : Vertex n) (s : Configuration b v)
    (t : Edge n → Scalar) (h : boundary t v = b' v-b v) :
    classLabel (.inr ⟨v,s.shift t h⟩) = classLabel (.inr ⟨v,s⟩) := by
  simp [classLabel]

def predecessors (x : Atom b) : Finset (Atom b) := univ.filter fun y => classIndex y < classIndex x

def classFormula {I : Type*} (x y : I) (h : ℕ) : Counting.Formula AnalysisSymbol I :=
  .exact y h (.and (.relation .preorder y x) (.neg (.relation .preorder x y)))

abbrev Block (n : ℕ) := Edge n ⊕ Vertex n

def atomBlock : Atom b → Block n
  | .inl ⟨e,_⟩ => .inl e
  | .inr ⟨v,_⟩ => .inr v

def blockEdges : Block n → Finset (Edge n)
  | .inl e => {e}
  | .inr v => univ.filter (incident v)

def touch (x : Atom b) : Finset (Edge n) := blockEdges (atomBlock x)

theorem touch_shift {t : Edge n → Scalar} {x : Atom b} {y : Atom b'}
    (h : AtomShift t x y) : touch x = touch y := by cases h <;> rfl

def touches {I : Type*} [DecidableEq I] (names : Finset I) (v : I → Atom b) : Finset (Edge n) :=
  names.biUnion (fun i => touch (v i))

end

section

open Classical Finset

variable {n : ℕ} {b : Vertex n → Scalar}

def HasState (x : Atom b) (e : Edge n) (s : LocalGroup e) : Prop :=
  x = .inl ⟨e,s⟩ ∨ AtomRelation b .I x (.inl ⟨e,s⟩)

@[simp] theorem hasState_edge (f : Edge n) (s : LocalGroup f) (e : Edge n) (t : LocalGroup e) :
    HasState (b := b) (.inl ⟨f,s⟩) e t ↔ (⟨f,s⟩ : Σ e, LocalGroup e) = ⟨e,t⟩ := by
  constructor
  · rintro (h | h)
    · exact Sum.inl.inj h
    · cases h
  · exact fun h => Or.inl (congrArg Sum.inl h)

@[simp] theorem hasState_config (v : Vertex n) (s : Configuration b v)
    (e : Edge n) (t : LocalGroup e) :
    HasState (.inr ⟨v,s⟩) e t ↔ ∃ h : incident v e, s.state ⟨e,h⟩ = t := by
  constructor
  · rintro (h | h)
    · cases h
    · cases h with
      | inc v s e => exact ⟨e.property,rfl⟩
  · rintro ⟨h,rfl⟩
    exact Or.inr (.inc v s ⟨e,h⟩)

def stateAt (x : Atom b) (e : Edge n) (he : e ∈ touch x) : LocalGroup e := by
  cases x with
  | inl x =>
    rcases x with ⟨f,s⟩
    have hh : e = f := by simpa [touch,atomBlock,blockEdges] using he
    subst e
    exact s
  | inr x =>
    rcases x with ⟨v,s⟩
    exact s.state ⟨e,by simpa [touch,atomBlock,blockEdges] using he⟩

@[simp] theorem stateAt_edge (e : Edge n) (s : LocalGroup e)
    (he : e ∈ touch (b := b) (.inl ⟨e,s⟩)) : stateAt (.inl ⟨e,s⟩) e he = s := by
  simp [stateAt]

@[simp] theorem stateAt_config (v : Vertex n) (s : Configuration b v) (e : IncidentEdges v)
    (he : e.val ∈ touch (.inr ⟨v,s⟩)) : stateAt (.inr ⟨v,s⟩) e.val he = s.state e := rfl

abbrev Occurrences {J : Type*} (a : J → Atom b) := Σ j : J, {e : Edge n // e ∈ touch (a j)}

def occurrenceAtom {J : Type*} (a : J → Atom b) (o : Occurrences a) : Atom b :=
  .inl ⟨o.2.val,stateAt (a o.1) o.2.val o.2.property⟩

def Augment {J : Type*} (a : J → Atom b) : J ⊕ Occurrences a → Atom b :=
  Sum.elim a (occurrenceAtom a)

structure SameDiagram {J : Type*} (a a' : J → Atom b) : Prop where
  classes : ∀ j, classLabel (a j) = classLabel (a' j)
  equal : ∀ i j, a i = a j ↔ a' i = a' j
  relation : ∀ r i j, (analysisStructure b).rel r (a i) (a j) ↔
    (analysisStructure b).rel r (a' i) (a' j)

end

open Classical Finset

variable {n : ℕ} {b : Vertex n → Scalar}

variable {J : Type*} [Fintype J]

def namesBelow {P : Type*} [Fintype P] {M : ℕ} (h : Fintype.card P < M) : P ↪ Fin M :=
  (Fintype.equivFin P).toEmbedding.trans (Fin.castLEEmb h.le)

end CPTSeparation.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Flows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Projection

open Finset

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

def ind {α : Type*} [DecidableEq α] (S : Finset α) (a : α) : ℕ :=
  if a ∈ S then 1 else 0

end CPTSeparation.Projection

namespace CPTSeparation.BoxLines

open Finset

variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

def projection (R : Finset (Fin (n+1) × J)) : Finset J := R.image Prod.snd

def fullLines (R : Finset (Fin (n+1) × J)) : Finset J :=
  univ.filter fun j => ∀ i, (i,j) ∈ R

def edgeBoundary (R : Finset (Fin (n+1) × J)) : Finset (Fin n × J) :=
  univ.filter fun p => ¬ ((p.1.castSucc,p.2) ∈ R ↔ (p.1.succ,p.2) ∈ R)

end CPTSeparation.BoxLines

namespace CPTSeparation.Grid

section

open Finset

variable {n : ℕ}

def edgeBoundary (R : Finset (Vertex n)) : Finset (Edge n) :=
  univ.filter fun e => ¬(tail e ∈ R ↔ head e ∈ R)

def swapXY (v : Vertex n) : Vertex n := (v.2.1,v.1,v.2.2)

def moveZ (v : Vertex n) : Vertex n := (v.2.2,v.1,v.2.1)

end

noncomputable def boxConstant : ℝ := 1 - (2:ℝ)^(-(1:ℝ)/3)

end CPTSeparation.Grid

namespace CPTSeparation.Flows

section

open Classical

abbrev Scalar := ZMod 3

variable {V E : Type*} [finiteV : Fintype V] [finiteE : Fintype E] [decidableV : DecidableEq V] [decidableE : DecidableEq E]

def incidence (tail head : E → V) : (E → Scalar) →ₗ[Scalar] (V → Scalar) where
  toFun t := ∑ e, t e • (Pi.single (head e) 1 - Pi.single (tail e) 1)
  map_add' := by intros; simp [add_smul,Finset.sum_add_distrib]
  map_smul' := by intros; simp [smul_smul,Finset.smul_sum]

omit V E in
@[simp] theorem incidence_single.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E] (tail head : E → V) (e : E) (z : Scalar) :
    incidence tail head (Pi.single e z) = Pi.single (head e) z - Pi.single (tail e) z := by
  change (∑ x, (Pi.single e z : E → Scalar) x •
    (Pi.single (head x) 1 - Pi.single (tail x) 1)) = _
  rw [Finset.sum_eq_single e]
  · simp [smul_sub,←Pi.single_smul]
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

def edgeRelation (tail head : E → V) (T : Finset E) (x y : V) : Prop :=
  ∃ e, e ∉ T ∧ tail e = x ∧ head e = y

def connected (tail head : E → V) (T : Finset E) : Setoid V :=
  Relation.EqvGen.setoid (edgeRelation tail head T)

abbrev Component (tail head : E → V) (T : Finset E) := Quotient (connected tail head T)

def component (tail head : E → V) (T : Finset E) (v : V) : Finset V :=
  Finset.univ.filter fun w => (connected tail head T).r v w

variable (tail head : E → V) (T : Finset E)

omit V E tail head T in
@[simp] theorem mem_component.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) (v w : V) : w ∈ component tail head T v ↔
    (connected tail head T).r v w := by simp [component]

end

open Classical Finset

variable {V E : Type*} [Fintype V] [finiteE : Fintype E] [decidableV : DecidableEq V] [decidableE : DecidableEq E]

variable (tail head : E → V) (T : Finset E)

instance instFintypeComponent : Fintype (Component tail head T) := Fintype.ofFinite _

def cell (c : Component tail head T) : Finset V := component tail head T c.out

def quotientMap (v : V) : Component tail head T := Quotient.mk (connected tail head T) v

omit V E tail head T in
@[simp] theorem mem_cell.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) (c : Component tail head T) (v : V) :
    v ∈ cell tail head T c ↔ quotientMap tail head T v = c := by
  rw [cell,mem_component]
  constructor
  · intro h
    exact (Quotient.sound h).symm.trans (Quotient.out_eq c)
  · intro h
    exact Quotient.exact ((Quotient.out_eq c).trans h.symm)

def edgeBoundary (U : Finset V) : Finset E := univ.filter fun e => ¬(tail e ∈ U ↔ head e ∈ U)

end CPTSeparation.Flows

namespace CPTSeparation.Flows

open Classical Finset

variable {V E : Type*} [finiteV : Fintype V] [finiteE : Fintype E] [decidableV : DecidableEq V] [decidableE : DecidableEq E]

variable (tail head : E → V)

def IsGiant (T : Finset E) (v : V) : Prop :=
  Fintype.card V < 2*(component tail head T v).card

end CPTSeparation.Flows

namespace CPTSeparation.Grid

open Classical Finset

variable {n M : ℕ} {b b' : Vertex n → Scalar}

def GiantBound (n M : ℕ) : Prop :=
  ((12*(M:ℝ))/boxConstant)^((3:ℝ)/2) < ((n+1)^3:ℕ)

def CompatibleAssignment {I : Type*} [DecidableEq I] (names : Finset I)
    (a : I → Atom b) (a' : I → Atom b') : Prop :=
  ∃ t : Edge n → Scalar, ∃ w : Vertex n,
    Flows.IsGiant tail head (touches names a) w ∧ boundary t = b'-b-Pi.single w 1 ∧
    ∀ i ∈ names, AtomShift t (a i) (a' i)

end CPTSeparation.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Hereditary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Hereditary

variable {A B : Type*}

attribute [local instance] CPTSeparation.Hereditary.instDecidableEqHF

@[simp] theorem mk_out (x : HF A) : mk (Quotient.out x) = x := Quotient.out_eq x

@[simp] theorem isSet_mk (l : Lists A) : isSet (mk l) = l.1 := rfl

@[simp] theorem isSet_atom (a : A) : isSet (atom a) = false := rfl

@[simp] theorem elements_mk (l : Lists A) : elements (mk l) = rawElements l := rfl

@[simp] theorem elements_atom (a : A) : elements (atom a) = ∅ := by
  classical
  change rawElements (Lists.atom a) = ∅
  simp [rawElements, Lists.toList]

@[simp] theorem not_mem_atom (x : HF A) (a : A) : ¬ x ∈ atom a := by
  change ¬ x ∈ elements (atom a)
  simp

@[simp] theorem isSet_ofFinset (s : Finset (HF A)) : isSet (ofFinset s) = true := rfl

@[simp] theorem elements_ofFinset (s : Finset (HF A)) : elements (ofFinset s) = s := by
  classical
  ext x
  simp only [ofFinset, elements_mk, rawElements, Lists.to_ofList, Finset.mem_image,
    List.mem_toFinset]
  simp only [List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨l, ⟨y,hy,rfl⟩,h⟩
    rw [mk_out] at h
    exact h ▸ hy
  · intro hx
    exact ⟨Quotient.out x, ⟨x,hx,rfl⟩, mk_out x⟩

@[simp] theorem mem_ofFinset (x : HF A) (s : Finset (HF A)) : x ∈ ofFinset s ↔ x ∈ s := by
  change x ∈ elements (ofFinset s) ↔ x ∈ s
  rw [elements_ofFinset]

theorem ext_sets {x y : HF A} (hx : isSet x = true) (hy : isSet y = true)
    (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  induction x using Quotient.inductionOn with
  | _ l =>
    induction y using Quotient.inductionOn with
    | _ r =>
      rcases l with ⟨(_ | _), l⟩ <;> (try cases hx)
      rcases r with ⟨(_ | _), r⟩ <;> (try cases hy)
      apply mk_eq_mk.mpr
      apply Lists.Equiv.antisymm
      · apply Lists'.subset_def.mpr
        intro a ha
        apply (mem_mk a (Lists.of' r)).mp
        apply (h (mk a)).mp
        exact (mem_mk a (Lists.of' l)).mpr ⟨a,ha,Lists.Equiv.refl a⟩
      · apply Lists'.subset_def.mpr
        intro a ha
        apply (mem_mk a (Lists.of' l)).mp
        apply (h (mk a)).mpr
        exact (mem_mk a (Lists.of' r)).mpr ⟨a,ha,Lists.Equiv.refl a⟩

@[simp] theorem rank_mk (l : Lists A) : rank (mk l) = rawRank l := rfl

@[simp] theorem rank_atom (a : A) : rank (atom a) = 0 := rfl

def rawMap' (f : A → B) : {b : Bool} → Lists' A b → Lists' B b
  | _, .atom a => .atom (f a)
  | _, .nil => .nil
  | _, .cons' a l => .cons' (rawMap' f a) (rawMap' f l)

def rawMap (f : A → B) (l : Lists A) : Lists B := ⟨l.1, rawMap' f l.2⟩

theorem toList_rawMap' (f : A → B) {b : Bool} (l : Lists' A b) :
    (rawMap' f l).toList = l.toList.map (rawMap f) := by
  induction l with
  | atom => rfl
  | nil => rfl
  | cons' a l iha ihl => simp only [rawMap', Lists'.toList, ihl]; rfl

theorem rawMap_congr (f : A → B) {l r : Lists A} (h : Lists.Equiv l r) :
    Lists.Equiv (rawMap f l) (rawMap f r) := by
  induction h using Lists.Equiv.rec
      (motive_2 := fun l r _ => Lists'.Subset (rawMap' f l) (rawMap' f r)) with
  | refl => exact Lists.Equiv.refl _
  | antisymm hl hr ihl ihr => exact Lists.Equiv.antisymm ihl ihr
  | nil => exact Lists'.Subset.nil
  | @cons a a' l r heq hmem hsub iheq ihsub =>
    apply Lists'.Subset.cons iheq _ ihsub
    rw [toList_rawMap']
    exact List.mem_map.mpr ⟨a',hmem,rfl⟩

def map (f : A → B) (x : HF A) : HF B :=
  Quotient.liftOn x (fun l => mk (rawMap f l)) (fun _ _ h => mk_eq_mk.mpr (rawMap_congr f h))

@[simp] theorem map_mk (f : A → B) (l : Lists A) : map f (mk l) = mk (rawMap f l) := rfl

@[simp] theorem map_atom (f : A → B) (a : A) : map f (atom a) = atom (f a) := rfl

@[simp] theorem isSet_map (f : A → B) (x : HF A) : isSet (map f x) = isSet x := by
  induction x using Quotient.inductionOn with
  | _ l => rfl

theorem elements_map (f : A → B) (x : HF A) :
    elements (map f x) = (elements x).image (map f) := by
  classical
  induction x using Quotient.inductionOn with
  | _ l =>
    change (rawMap f l).toList.toFinset.image mk =
      (l.toList.toFinset.image mk).image (map f)
    rw [Finset.image_image]
    have ht : (rawMap f l).toList = l.toList.map (rawMap f) := toList_rawMap' f l.2
    rw [ht]
    ext z
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨b,⟨a,ha,rfl⟩,h⟩
      exact ⟨a,ha,h⟩
    · rintro ⟨a,ha,h⟩
      exact ⟨rawMap f a,⟨a,ha,rfl⟩,h⟩

@[simp] theorem map_ofFinset (f : A → B) (s : Finset (HF A)) :
    map f (ofFinset s) = ofFinset (s.image (map f)) := by
  classical
  apply ext_sets (by simp) (by simp)
  intro z
  change z ∈ elements (map f (ofFinset s)) ↔ z ∈ elements (ofFinset (s.image (map f)))
  rw [elements_map, elements_ofFinset, elements_ofFinset]

@[simp] theorem rawMap_id : ∀ l : Lists A, rawMap id l = l := by
  rintro ⟨b,l⟩
  have h : rawMap' id l = l := by
    induction l with
    | atom => rfl
    | nil => rfl
    | cons' a l iha ihl => simp only [rawMap', iha,ihl]
  exact congrArg (Sigma.mk b) h

@[simp] theorem map_id (x : HF A) : map id x = x := by
  induction x using Quotient.inductionOn with
  | _ l =>
    change map id (mk l) = mk l
    rw [map_mk, rawMap_id]

theorem rawMap_comp {C : Type*} (g : B → C) (f : A → B) (l : Lists A) :
    rawMap g (rawMap f l) = rawMap (g ∘ f) l := by
  rcases l with ⟨b,l⟩
  have h : rawMap' g (rawMap' f l) = rawMap' (g ∘ f) l := by
    induction l with
    | atom => rfl
    | nil => rfl
    | cons' a l iha ihl => simp only [rawMap', iha,ihl]
  exact congrArg (Sigma.mk b) h

@[simp] theorem map_comp {C : Type*} (g : B → C) (f : A → B) (x : HF A) :
    map g (map f x) = map (g ∘ f) x := by
  induction x using Quotient.inductionOn with
  | _ l =>
    change map g (map f (mk l)) = map (g ∘ f) (mk l)
    simp only [map_mk,rawMap_comp]

def mapEquiv (e : A ≃ B) : HF A ≃ HF B where
  toFun := map e
  invFun := map e.symm
  left_inv x := by
    rw [map_comp]
    have h : (e.symm : B → A) ∘ (e : A → B) = id := by funext a; simp
    rw [h,map_id]
  right_inv x := by
    rw [map_comp]
    have h : (e : A → B) ∘ (e.symm : B → A) = id := by funext a; simp
    rw [h,map_id]

instance instMulActionHF {G : Type*} [Group G] [MulAction G A] : MulAction G (HF A) where
  smul g x := map (fun a => g • a) x
  one_smul x := by
    change map (fun a : A => (1 : G) • a) x = x
    have h : (fun a : A => (1 : G) • a) = id := by funext a; simp
    rw [h,map_id]
  mul_smul g h x := by
    change map (fun a : A => (g*h) • a) x = map (fun a => g • a) (map (fun a => h • a) x)
    rw [map_comp]
    congr 1
    funext a
    exact mul_smul g h a

@[simp] theorem smul_atom {G : Type*} [Group G] [MulAction G A] (g : G) (a : A) :
    g • atom a = atom (g • a) := rfl

@[simp] theorem smul_ofFinset {G : Type*} [Group G] [MulAction G A] (g : G) (s : Finset (HF A)) :
    g • ofFinset s = ofFinset (s.image (fun x => g • x)) := map_ofFinset _ _

def Supports {G : Type*} [Group G] [MulAction G A] {k : ℕ}
    (alpha : Fin k → A) (x : HF A) : Prop :=
  ∀ g : G, (∀ i, g • alpha i = alpha i) → g • x = x

def Supported {G : Type*} [Group G] [MulAction G A] (s : ℕ) (x : HF A) : Prop :=
  ∃ alpha : Fin s → A, Supports (G := G) alpha x

def HereditarilySupported {G : Type*} [Group G] [MulAction G A] (s : ℕ) (x : HF A) : Prop :=
  ∀ y, Relation.ReflTransGen (fun a b : HF A => a ∈ b) y x → Supported (G := G) s y

end CPTSeparation.Hereditary

namespace CPTSeparation.Forms

open Classical

open Counting Hereditary

variable {R I J A B : Type*}

inductive Form (J L : Type*)
  | atom (j : J)
  | set (n : ℕ) (child : Fin n → Form J L) (label : Fin n → L)

namespace Form

variable [finiteI : Fintype I] [Fintype J] [DecidableEq I]

variable [Fintype A] [Nonempty A]

def value (S : Structure R A) (e : J ⊕ J ↪ I) :
    Form J (Set (Formula R I)) → (J → A) → HF A
  | .atom j, a => Hereditary.atom (a j)
  | .set _ child label, a => Hereditary.ofFinset
      (Finset.univ.biUnion fun i =>
        (Finset.univ.filter fun b : J → A =>
          tupleType S e (Sum.elim b a) = label i).image (value S e (child i)))

omit R I J A in
@[simp] theorem value_atom.{uDecl1, uDecl2, uDecl3, uDecl4}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {J : Type uDecl3}
    {A : Type uDecl4}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A] (S : Structure R A) (e : J ⊕ J ↪ I) (j : J) (a : J → A) :
    value S e (.atom j) a = Hereditary.atom (a j) := rfl

omit R I J A in
@[simp] theorem value_set_isSet.{uDecl1, uDecl2, uDecl3, uDecl4}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {J : Type uDecl3}
    {A : Type uDecl4}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A] (S : Structure R A) (e : J ⊕ J ↪ I)
    (n : ℕ) (child : Fin n → Form J (Set (Formula R I))) (label : Fin n → Set (Formula R I))
    (a : J → A) : isSet (value S e (.set n child label) a) = true := rfl

omit R I J A in
@[simp] theorem mem_value_set.{uDecl1, uDecl2, uDecl3, uDecl4}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {J : Type uDecl3}
    {A : Type uDecl4}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A] (S : Structure R A) (e : J ⊕ J ↪ I)
    (n : ℕ) (child : Fin n → Form J (Set (Formula R I))) (label : Fin n → Set (Formula R I))
    (a : J → A) (x : HF A) :
    x ∈ value S e (.set n child label) a ↔
      ∃ i b, tupleType S e (Sum.elim b a) = label i ∧ value S e (child i) b = x := by
  classical
  simp only [value,mem_ofFinset,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Finset.mem_image,Finset.mem_filter,true_and]

omit R I J A B in
theorem value_iso.{uDecl1, uDecl2, uDecl3, uDecl4, uDecl5}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {J : Type uDecl3}
    {A : Type uDecl4}
    {B : Type uDecl5}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A] [Fintype B] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ⊕ J ↪ I) (f : A ≃ B)
    (hf : ∀ r a b, S.rel r a b ↔ T.rel r (f a) (f b))
    (φ : Form J (Set (Formula R I))) (a : J → A) :
    Hereditary.map f (value S e φ a) = value T e φ (f ∘ a) := by
  induction φ generalizing a with
  | atom j => rfl
  | set n child label ih =>
    apply Hereditary.ext_sets (by simp [value]) (by simp)
    intro x
    change x ∈ elements (Hereditary.map f (value S e (.set n child label) a)) ↔ _
    rw [Hereditary.elements_map]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨i,b,ht,rfl⟩ := (mem_value_set S e n child label a y).mp hy
      apply (mem_value_set T e n child label (f ∘ a) _).mpr
      refine ⟨i,f ∘ b,?_,(ih i b).symm⟩
      have heq : Sum.elim (f ∘ b) (f ∘ a) = f ∘ Sum.elim b a := by
        funext j; cases j <;> rfl
      rw [heq,← tupleType_iso S T e f hf,ht]
    · intro hx
      obtain ⟨i,b,ht,hx⟩ := (mem_value_set T e n child label (f ∘ a) x).mp hx
      let c := f.symm ∘ b
      have hc : f ∘ c = b := by funext j; simp [c]
      refine ⟨value S e (child i) c,?_,?_⟩
      · apply (mem_value_set S e n child label a _).mpr
        refine ⟨i,c,?_,rfl⟩
        rw [tupleType_iso S T e f hf]
        have heq : f ∘ Sum.elim c a = Sum.elim b (f ∘ a) := by
          funext j; cases j <;> simp [c]
        rw [heq,ht]
      · rw [ih,hc,hx]

end Form

def cross31 : J ⊕ J ↪ (J ⊕ J) ⊕ J where
  toFun := Sum.elim Sum.inr (fun j => Sum.inl (Sum.inl j))
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def cross42 : J ⊕ J ↪ ((J ⊕ J) ⊕ J) ⊕ J where
  toFun := Sum.elim Sum.inr (fun j => Sum.inl (Sum.inl (Sum.inr j)))
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def cross34 : J ⊕ J ↪ ((J ⊕ J) ⊕ J) ⊕ J where
  toFun := Sum.elim (fun j => Sum.inl (Sum.inr j)) Sum.inr
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

@[simp] theorem elim_comp_cross31 (a b c : J → A) :
    Sum.elim (Sum.elim a b) c ∘ cross31 = Sum.elim c a := by
  funext j; cases j <;> rfl

@[simp] theorem elim_comp_cross42 (a b c d : J → A) :
    Sum.elim (Sum.elim (Sum.elim a b) c) d ∘ cross42 = Sum.elim d b := by
  funext j; cases j <;> rfl

@[simp] theorem elim_comp_cross34 (a b c d : J → A) :
    Sum.elim (Sum.elim (Sum.elim a b) c) d ∘ cross34 = Sum.elim c d := by
  funext j; cases j <;> rfl

variable {G : Type*} [Group G] [MulAction G A]

variable [finiteI : Fintype I] [DecidableEq I] [finiteA : Fintype A] [nonemptyA : Nonempty A] {s : ℕ}

variable (S : Structure R A) (e2 : Fin s ⊕ Fin s ↪ I)

variable (hAut : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

open Form

omit R I A G s S e2 hAut in
theorem value_smul.{uDecl1, uDecl2, uDecl4, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl4}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    {s : ℕ}
    (S : Counting.Structure R A)
    (e2 : Fin s ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b) (g : G) (φ : Form (Fin s) (Set (Formula R I))) (a : Fin s → A) :
    g • value S e2 φ a = value S e2 φ (fun i => g • a i) := by
  exact value_iso S S e2 (MulAction.toPerm g) (fun r a b => (hAut g r a b).symm) φ a

omit R I A G s S e2 hAut in
theorem value_supported.{uDecl1, uDecl2, uDecl4, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl4}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    {s : ℕ}
    (S : Counting.Structure R A)
    (e2 : Fin s ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b) (φ : Form (Fin s) (Set (Formula R I))) (a : Fin s → A) :
    Supports (G := G) a (value S e2 φ a) := by
  intro g hg
  rw [value_smul S e2 hAut]
  exact congrArg (value S e2 φ) (funext hg)

omit A G s in
theorem hereditary_intro.{uDecl4, uDecl6}
    {A : Type uDecl4}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    [Fintype A]
    [Nonempty A]
    {s : ℕ} (x : HF A) (hx : Supported (G := G) s x)
    (hm : ∀ y ∈ x, HereditarilySupported (G := G) s y) :
    HereditarilySupported (G := G) s x := by
  intro y hy
  cases hy with
  | refl => exact hx
  | tail hpath hstep => exact hm _ hstep _ hpath

include hAut in
theorem value_hereditarily_supported (φ : Form (Fin s) (Set (Formula R I)))
    (a : Fin s → A) : HereditarilySupported (G := G) s (value S e2 φ a) := by
  induction φ generalizing a with
  | atom i =>
    apply hereditary_intro _ ⟨a,value_supported S e2 hAut _ a⟩
    intro y hy
    exact (not_mem_atom y (a i) hy).elim
  | set n child label ih =>
    apply hereditary_intro _ ⟨a,value_supported S e2 hAut _ a⟩
    intro y hy
    obtain ⟨i,b,ht,rfl⟩ := (mem_value_set S e2 n child label a y).mp hy
    exact ih i b

end CPTSeparation.Forms

namespace CPTSeparation.Counting

open Classical

variable {R I J A B : Type*} [DecidableEq I]

def triangular {X Y : Type*} (e : X ≃ Y) (f : X → A ≃ B) : X × A ≃ Y × B where
  toFun p := (e p.1, f p.1 p.2)
  invFun p := (e.symm p.1, (f (e.symm p.1)).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

def snocTuple {n : ℕ} (a : Fin n → A) (x : A) : Fin (n+1) → A :=
  Fin.lastCases x a

@[simp] theorem snocTuple_castSucc {n : ℕ} (a : Fin n → A) (x : A) (i : Fin n) :
    snocTuple a x i.castSucc = a i := by simp [snocTuple]

@[simp] theorem snocTuple_last {n : ℕ} (a : Fin n → A) (x : A) :
    snocTuple a x (Fin.last n) = x := by simp [snocTuple]

def snocEquiv (n : ℕ) : (Fin (n+1) → A) ≃ (Fin n → A) × A where
  toFun a := (fun i => a i.castSucc, a (Fin.last n))
  invFun p := snocTuple p.1 p.2
  left_inv a := by
    funext i
    induction i using Fin.lastCases <;> simp
  right_inv p := by ext <;> simp

def appendPosition (J : Type*) (n : ℕ) : (J ⊕ Fin n) ⊕ Unit ≃ J ⊕ Fin (n+1) where
  toFun := Sum.elim (Sum.elim Sum.inl (fun i => Sum.inr i.castSucc)) (fun _ => Sum.inr (Fin.last n))
  invFun := Sum.elim (fun j => Sum.inl (Sum.inl j))
    (Fin.lastCases (Sum.inr ()) (fun i => Sum.inl (Sum.inr i)))
  left_inv p := by rcases p with (j|i)|u <;> simp
  right_inv p := by
    rcases p with j|i
    · rfl
    · induction i using Fin.lastCases <;> simp

end CPTSeparation.Counting

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Forms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Forms

open Classical Counting Hereditary

open scoped BigOperators

variable {R I A B P : Type*} [finiteI : Fintype I] [DecidableEq I]

variable [finiteA : Fintype A] [Fintype B] [nonemptyA : Nonempty A] [Nonempty B] [finiteP : Fintype P]

variable {s : ℕ}

def Molecules (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (p : P → A) (τ : Set (Formula R I)) :=
  {a : Fin s → A // tupleType S ep (Sum.elim p a) = τ}

instance instFintypeMolecules (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (p : P → A) (τ : Set (Formula R I)) : Fintype (Molecules S ep p τ) :=
  inferInstanceAs (Fintype {a : Fin s → A // tupleType S ep (Sum.elim p a) = τ})

def labelValues (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I) (p : P → A) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I))) : Set (HF A) :=
  Set.range (fun a : Molecules S ep p τ => Form.value S e2 φ a.1)

instance instFintypeElemHFLabelValues (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I) (p : P → A) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I))) : Fintype (labelValues S ep e2 p τ φ) :=
  (Set.finite_range _).fintype

section Group

variable {G : Type*} [Group G] [MulAction G A]

variable (S : Structure R A) (ep : P ⊕ Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)

variable (hAut : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (p : P → A) (τ : Set (Formula R I))

omit R I A P s G S ep hAut p in
theorem mol_type_smul.{uDecl1, uDecl2, uDecl3, uDecl5, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {P : Type uDecl5}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    [Fintype P]
    {s : ℕ}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    (S : Counting.Structure R A)
    (ep : P ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (p : P → A) (g : G) (hp : ∀ i, g • p i = p i) (a : Fin s → A) :
    tupleType S ep (Sum.elim p (fun i => g • a i)) = tupleType S ep (Sum.elim p a) := by
  have hh := tupleType_iso S S ep (MulAction.toPerm g) (fun r a b => (hAut g r a b).symm)
    (Sum.elim p a)
  have hh' : (MulAction.toPerm g) ∘ Sum.elim p a = Sum.elim p (fun i => g • a i) := by
    funext i; rcases i with i|i
    · exact hp i
    · rfl
  rw [hh'] at hh
  exact hh.symm

def moleculesPerm (g : G) (hp : ∀ i, g • p i = p i) :
    Molecules S ep p τ ≃ Molecules S ep p τ :=
  (Equiv.piCongrRight (fun _ : Fin s => MulAction.toPerm g)).subtypeEquiv
    (fun a => by
      change tupleType S ep (Sum.elim p a) = τ ↔
        tupleType S ep (Sum.elim p (fun i => g • a i)) = τ
      rw [mol_type_smul S ep hAut p g hp a])

end Group

variable (S : Structure R A) (T : Structure R B)

variable (ep : P ⊕ Fin s ↪ I) (epp : (P ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e2 : Fin s ⊕ Fin s ↪ I)

variable (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

def skipMiddle : P ⊕ Fin s ↪ (P ⊕ Fin s) ⊕ Fin s :=
  Function.Embedding.sumMap Function.Embedding.inl (Function.Embedding.refl _)

def lastTwo : Fin s ⊕ Fin s ↪ (P ⊕ Fin s) ⊕ Fin s :=
  Function.Embedding.sumMap Function.Embedding.inr (Function.Embedding.refl _)

omit A P s in
@[simp] theorem elim_skipMiddle.{uDecl3, uDecl5}
    {A : Type uDecl3}
    {P : Type uDecl5}
    [Fintype A]
    [Nonempty A]
    [Fintype P]
    {s : ℕ} (p : P → A) (a b : Fin s → A) :
    (Sum.elim (Sum.elim p a) b) ∘ skipMiddle = Sum.elim p b := by
  funext j; cases j <;> rfl

omit A P s in
@[simp] theorem elim_lastTwo.{uDecl3, uDecl5}
    {A : Type uDecl3}
    {P : Type uDecl5}
    [Fintype A]
    [Nonempty A]
    [Fintype P]
    {s : ℕ} (p : P → A) (a b : Fin s → A) :
    (Sum.elim (Sum.elim p a) b) ∘ lastTwo = Sum.elim a b := by
  funext j; cases j <;> rfl

end CPTSeparation.Forms

namespace CPTSeparation

open Classical

def cellSetoid {L X : Type*} (C : L → Set X) : Setoid L :=
  ⟨fun l k => C l = C k,⟨fun _ => rfl,Eq.symm,Eq.trans⟩⟩

end CPTSeparation

namespace CPTSeparation.Forms

section

open Classical Counting Hereditary

variable {R I A B P G H : Type*}

variable [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]

variable [Nonempty A] [Nonempty B] [Fintype P]

variable [Group G] [MulAction G A] [Group H] [MulAction H B]

variable {s : ℕ}

abbrev Domain (G : Type*) [Group G] [MulAction G A] (s : ℕ) :=
  {x : HF A // HereditarilySupported (G := G) s x}

def Cell (S : Structure R A) (ep : P ⊕ Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)
    (p : P → A) (φ : Form (Fin s) (Set (Formula R I))) (τ : Set (Formula R I)) :
    Set (Domain (A := A) G s) :=
  {x | x.1 ∈ labelValues S ep e2 p τ φ}

variable (S : Structure R A) (T : Structure R B)

variable (ep : P ⊕ Fin s ↪ I) (epp : (P ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e2 : Fin s ⊕ Fin s ↪ I) (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

variable (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)

def cellEquiv (p : P → A) (φ : Form (Fin s) (Set (Formula R I))) (τ : Set (Formula R I)) :
    Cell (G := G) S ep e2 p φ τ ≃ labelValues S ep e2 p τ φ :=
  Equiv.subtypeSubtypeEquivSubtype
    (p := HereditarilySupported (G := G) s)
    (q := fun x => x ∈ labelValues S ep e2 p τ φ) (fun hx => by
    obtain ⟨a,rfl⟩ := hx
    exact value_hereditarily_supported S e2 hAutA φ a.1)

end

open Classical Counting Hereditary

variable {R I A B V G H : Type*}

variable [finiteI : Fintype I] [DecidableEq I] [finiteA : Fintype A] [Fintype B]

variable [nonemptyA : Nonempty A] [Nonempty B] [finiteV : Fintype V] [decidableV : DecidableEq V]

variable [Group G] [MulAction G A] [Group H] [MulAction H B]

variable {s : ℕ}

inductive HFRelation (R : Type*)
  | mem | atom | base (r : R)

def hfStructure (S : Structure R A) : Structure (HFRelation R) (Domain (A := A) G s) where
  rel
    | .mem, x, y => x.1 ∈ y.1
    | .atom, x, _ => isSet x.1 = false
    | .base r, x, y => ∃ a b, x.1 = Hereditary.atom a ∧ y.1 = Hereditary.atom b ∧ S.rel r a b

def Represented (S : Structure R A) (T : Structure R B)
    (ef : V × Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s) : Prop :=
  ∃ φ : V → Form (Fin s) (Set (Formula R I)), ∃ a : V × Fin s → A,
    ∃ b : V × Fin s → B,
      (∀ i, Form.value S e2 (φ i) (fun j => a (i,j)) = (v i).1) ∧
      (∀ i, Form.value T e2 (φ i) (fun j => b (i,j)) = (w i).1) ∧
      tupleType S ef a = tupleType T ef b

def twoBlocks (i j : V) (h : i ≠ j) : Fin s ⊕ Fin s ↪ V × Fin s where
  toFun := Sum.elim (Prod.mk i) (Prod.mk j)
  inj' := by
    intro a b hab
    cases a <;> cases b <;> simp only [Sum.elim_inl,Sum.elim_inr,Prod.mk.injEq] at hab
    · congr 1; exact hab.2
    · exact (h hab.1).elim
    · exact (h hab.1.symm).elim
    · congr 1; exact hab.2

omit A V s in
@[simp] theorem comp_twoBlocks.{uDecl3, uDecl5}
    {A : Type uDecl3}
    {V : Type uDecl5}
    [Fintype A]
    [Nonempty A]
    [Fintype V]
    [DecidableEq V]
    {s : ℕ} (i j : V) (h : i ≠ j) (a : V × Fin s → A) :
    a ∘ twoBlocks i j h = Sum.elim (fun k => a (i,k)) (fun k => a (j,k)) := by
  funext x; cases x <;> rfl

def splitBlock (i : V) : ({j : V // j ≠ i} × Fin s) ⊕ Fin s ≃ V × Fin s where
  toFun := Sum.elim (fun x => (x.1.1,x.2)) (fun j => (i,j))
  invFun := fun x => if h : x.1 = i then .inr x.2 else .inl (⟨x.1,h⟩,x.2)
  left_inv := by
    intro x; cases x with
    | inl x => simp [x.1.2]
    | inr j => simp
  right_inv := by
    intro x; by_cases h : x.1 = i
    · simp [h]; exact Prod.ext h.symm rfl
    · simp [h]

variable (S : Structure R A) (T : Structure R B)

variable (ef : V × Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)

variable (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

omit V s in
@[simp] theorem splitBlock_symm_new.{uDecl5}
    {V : Type uDecl5}
    [Fintype V]
    [DecidableEq V]
    {s : ℕ} (i : V) (k : Fin s) :
    (splitBlock (s := s) i).symm (i,k) = .inr k := by simp [splitBlock]

omit V s in
@[simp] theorem splitBlock_symm_old.{uDecl5}
    {V : Type uDecl5}
    [Fintype V]
    [DecidableEq V]
    {s : ℕ} (i j : V) (h : j ≠ i) (k : Fin s) :
    (splitBlock (s := s) i).symm (j,k) = .inl (⟨j,h⟩,k) := by simp [splitBlock,h]

variable (eplus : (V × Fin s) ⊕ Fin s ↪ I)

variable (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)

def namesOfCard {J : Type*} [Fintype J] {M : ℕ} (h : Fintype.card J ≤ M) : J ↪ Fin M :=
  (Fintype.equivFin J).toEmbedding.trans (Fin.castLEEmb h)

def HomogeneousThrough (S : Structure R A) (G : Type*) [Group G] [MulAction G A]
    (M r : ℕ) : Prop :=
  ∀ k ≤ r, ∀ e : Fin k ↪ Fin M, ∀ a b : Fin k → A,
    tupleType S e a = tupleType S e b → ∃ g : G, ∀ j, g • a j = b j

end CPTSeparation.Forms

namespace CPTSeparation.Grid

section

open Support Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

@[simp] theorem central_smul_HF (k : CentralGroup n) (x : HF (Atom b)) :
    k • x = centralHom k • x := rfl

end

open Classical Finset

end CPTSeparation.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Interpretations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Interpretations

structure Structure (R : Type) where
  Carrier : Type
  finite : Fintype Carrier
  rel : R → Carrier → Carrier → Bool

attribute [instance] Structure.finite

inductive Formula (R : Type) : ℕ → Type
  | falsum {n} : Formula R n
  | eq {n} (x y : Fin n) : Formula R n
  | rel {n} (r : R) (x y : Fin n) : Formula R n
  | neg {n} : Formula R n → Formula R n
  | and {n} : Formula R n → Formula R n → Formula R n
  | ex {n} : Formula R (n+1) → Formula R n
  | hartig {n} : Formula R (n+1) → Formula R (n+1) → Formula R n

noncomputable def Formula.eval {R : Type} (A : Structure R) :
    {n : ℕ} → Formula R n → (Fin n → A.Carrier) → Prop
  | _, .falsum, _ => False
  | _, .eq x y, v => v x = v y
  | _, .rel r x y, v => A.rel r (v x) (v y) = true
  | _, .neg φ, v => ¬ φ.eval A v
  | _, .and φ ψ, v => φ.eval A v ∧ ψ.eval A v
  | _, .ex φ, v => ∃ a, φ.eval A (Fin.cons a v)
  | _, .hartig φ ψ, v =>
    Nat.card {a : A.Carrier // φ.eval A (Fin.cons a v)} =
    Nat.card {a : A.Carrier // ψ.eval A (Fin.cons a v)}

structure Interpretation (R T : Type) where
  domain : Formula R 2
  identify : Formula R 4
  relation : T → Formula R 4

namespace Interpretation

variable {R T : Type} (I : Interpretation R T) (A : Structure R)

abbrev Domain := {a : A.Carrier × A.Carrier // I.domain.eval A ![a.1,a.2]}

def link (a b : I.Domain A) : Prop :=
  I.identify.eval A ![a.val.1,a.val.2,b.val.1,b.val.2]

def classSetoid : Setoid (I.Domain A) :=
  Relation.EqvGen.setoid (I.link A)

abbrev Vertex := Quotient (I.classSetoid A)

noncomputable def apply : Structure T := by
  classical
  letI : Fintype (I.Domain A) := Fintype.ofFinite _
  letI : Fintype (I.Vertex A) := Fintype.ofFinite _
  exact {
    Carrier := I.Vertex A
    finite := inferInstance
    rel := fun r x y => decide (∃ a b : I.Domain A,
      Quotient.mk (I.classSetoid A) a = x ∧
      Quotient.mk (I.classSetoid A) b = y ∧
      (I.relation r).eval A ![a.val.1,a.val.2,b.val.1,b.val.2]) }

end Interpretation

structure Program (InputSymbols : Type) where
  StateSymbols : Type
  stateFinite : Fintype StateSymbols
  init : Interpretation InputSymbols StateSymbols
  step : Interpretation StateSymbols StateSymbols
  halt : Formula StateSymbols 0
  output : Formula StateSymbols 0

namespace Program

variable {R : Type} (P : Program R)

noncomputable def state (A : Structure R) : ℕ → Structure P.StateSymbols
  | 0 => P.init.apply A
  | j+1 => P.step.apply (state A j)

noncomputable def cost (A : Structure R) (j : ℕ) : ℕ :=
  (j+1) + ∑ k ∈ Finset.range (j+1), Fintype.card (P.state A k).Carrier

end Program

end CPTSeparation.Interpretations

namespace CPTSeparation.Hereditary

open Classical Finset

variable {A B : Type*}

@[simp] theorem ofFinset_inj {s t : Finset (HF A)} : ofFinset s = ofFinset t ↔ s = t :=
  ⟨fun h => by simpa using congrArg elements h,fun h => congrArg ofFinset h⟩

def singleton (a : HF A) : HF A := ofFinset {a}

def pair (a b : HF A) : HF A := double (singleton a) (double a b)

@[simp] theorem mem_singleton (x a : HF A) : x ∈ singleton a ↔ x = a := by simp [singleton]

@[simp] theorem mem_double (x a b : HF A) : x ∈ double a b ↔ x = a ∨ x = b := by simp [double]

@[simp] theorem singleton_inj {a b : HF A} : singleton a = singleton b ↔ a = b := by simp [singleton]

@[simp] theorem map_singleton (f : A → B) (a : HF A) : map f (singleton a) = singleton (map f a) := by simp [singleton]

@[simp] theorem map_double (f : A → B) (a b : HF A) : map f (double a b) = double (map f a) (map f b) := by
  simp only [double,map_ofFinset,image_insert,image_singleton]
  apply ofFinset_inj.mpr
  ext x
  simp

@[simp] theorem map_pair (f : A → B) (a b : HF A) : map f (pair a b) = pair (map f a) (map f b) := by simp [pair]

@[simp] theorem ordinal_isSet (i : ℕ) : isSet (ordinal (A := A) i) = true := by cases i <;> simp [ordinal]

@[simp] theorem map_ordinal (f : A → B) (i : ℕ) : map f (ordinal i) = ordinal i := by
  induction i with
  | zero => simp [ordinal]
  | succ i ih =>
    simp only [ordinal,map_ofFinset,image_insert,ih]
    rw [← elements_map,ih]
    apply ofFinset_inj.mpr
    ext x
    simp

end CPTSeparation.Hereditary

namespace CPTSeparation.Counting

open Classical Finset

variable {R D : Type*} (S : Structure R D) {m n k : ℕ}

def Definable (m n : ℕ) (P : (Fin n → D) → Prop) : Prop :=
  ∀ args : Fin n → Fin m, ∃ φ : Formula R (Fin m),
    φ.free ⊆ univ.image args ∧ ∀ v, φ.eval S v ↔ P (v ∘ args)

namespace Definable

variable {S} {P Q : (Fin n → D) → Prop}

theorem congr (h : Definable S m n P) (heq : ∀ v, P v ↔ Q v) : Definable S m n Q := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  exact ⟨φ,hφ,fun v => (he v).trans (heq _)⟩

theorem neg (h : Definable S m n P) : Definable S m n (fun v => ¬ P v) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  exact ⟨.neg φ,hφ,fun v => not_congr (he v)⟩

theorem fresh (args : Fin n → Fin m) (hn : n < m) : ∃ i, ∀ j, args j ≠ i := by
  have hns : ¬ Function.Surjective args := by
    intro hs
    have h := Fintype.card_le_of_surjective args hs
    simp only [Fintype.card_fin] at h
    omega
  simp only [Function.Surjective] at hns
  push Not at hns
  exact hns

theorem updated_args (args : Fin n → Fin m) (i : Fin m)
    (hi : ∀ j, args j ≠ i) (v : Fin m → D) (x : D) :
    Function.update v i x ∘ Fin.cons i args = Fin.cons x (v ∘ args) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [hi j]

theorem free_binder {args : Fin n → Fin m} {i : Fin m} {φ : Formula R (Fin m)}
    (hφ : φ.free ⊆ univ.image (Fin.cons i args)) : φ.free.erase i ⊆ univ.image args := by
  intro j hj
  obtain ⟨k,_,hk⟩ := mem_image.mp (hφ (mem_erase.mp hj).2)
  cases k using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero] at hk
    exact False.elim ((mem_erase.mp hj).1 hk.symm)
  | succ k => exact mem_image.mpr ⟨k,mem_univ _,hk⟩

theorem ex {P : (Fin (n+1) → D) → Prop} (h : Definable S m (n+1) P) (hn : n < m) :
    Definable S m n (fun v => ∃ x, P (Fin.cons x v)) := by
  intro args
  obtain ⟨i,hi⟩ := fresh args hn
  obtain ⟨φ,hφ,he⟩ := h (Fin.cons i args)
  refine ⟨.ex i φ,free_binder hφ,?_⟩
  intro v
  apply exists_congr
  intro x
  simpa only [updated_args args i hi] using he (Function.update v i x)

theorem all {P : (Fin (n+1) → D) → Prop} (h : Definable S m (n+1) P) (hn : n < m) :
    Definable S m n (fun v => ∀ x, P (Fin.cons x v)) :=
  (h.neg.ex hn).neg.congr (fun _ => by simp)

end Definable

end CPTSeparation.Counting

namespace CPTSeparation.HFCoding

open Classical Finset Hereditary Counting

variable {A R : Type} {d : Set (HF A)}

abbrev Domain (d : Set (HF A)) := {x : HF A // x ∈ d}

variable (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d)

variable (S : Counting.Structure R (Domain d)) {m : ℕ}

def SingletonTest (u a : Domain d) : Prop :=
  isSet u.val = true ∧ ∀ w : Domain d, w.val ∈ u.val ↔ w = a

def DoubleTest (u a b : Domain d) : Prop :=
  isSet u.val = true ∧ ∀ w : Domain d, w.val ∈ u.val ↔ w = a ∨ w = b

end CPTSeparation.HFCoding

namespace CPTSeparation.Counting

open Classical Finset

variable {R ι : Type*} {D : ι → Type*} (S : ∀ i, Structure R (D i)) {m n k : ℕ}

def UniformDefinable (m n : ℕ) (P : ∀ i, (Fin n → D i) → Prop) : Prop :=
  ∀ args : Fin n → Fin m, ∃ φ : Formula R (Fin m),
    φ.free ⊆ univ.image args ∧ ∀ i v, φ.eval (S i) v ↔ P i (v ∘ args)

namespace UniformDefinable

variable {S} {P Q : ∀ i, (Fin n → D i) → Prop}

theorem congr (h : UniformDefinable S m n P) (heq : ∀ i v, P i v ↔ Q i v) :
    UniformDefinable S m n Q := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  exact ⟨φ,hφ,fun i v => (he i v).trans (heq _ _)⟩

theorem neg (h : UniformDefinable S m n P) : UniformDefinable S m n (fun i v => ¬ P i v) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  exact ⟨.neg φ,hφ,fun i v => not_congr (he i v)⟩

theorem fresh (args : Fin n → Fin m) (hn : n < m) : ∃ i, ∀ j, args j ≠ i := by
  have hns : ¬ Function.Surjective args := by
    intro hs
    have h := Fintype.card_le_of_surjective args hs
    simp only [Fintype.card_fin] at h
    omega
  simp only [Function.Surjective] at hns
  push Not at hns
  exact hns

theorem updated_args {X : Type*} (args : Fin n → Fin m) (i : Fin m)
    (hi : ∀ j, args j ≠ i) (v : Fin m → X) (x : X) :
    Function.update v i x ∘ Fin.cons i args = Fin.cons x (v ∘ args) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [hi j]

theorem free_binder {args : Fin n → Fin m} {i : Fin m} {φ : Formula R (Fin m)}
    (hφ : φ.free ⊆ univ.image (Fin.cons i args)) : φ.free.erase i ⊆ univ.image args := by
  intro j hj
  obtain ⟨k,_,hk⟩ := mem_image.mp (hφ (mem_erase.mp hj).2)
  cases k using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero] at hk
    exact False.elim ((mem_erase.mp hj).1 hk.symm)
  | succ k => exact mem_image.mpr ⟨k,mem_univ _,hk⟩

theorem ex {P : ∀ i, (Fin (n+1) → D i) → Prop} (h : UniformDefinable S m (n+1) P) (hn : n < m) :
    UniformDefinable S m n (fun i v => ∃ x, P i (Fin.cons x v)) := by
  intro args
  obtain ⟨a,ha⟩ := fresh args hn
  obtain ⟨φ,hφ,he⟩ := h (Fin.cons a args)
  refine ⟨.ex a φ,free_binder hφ,?_⟩
  intro i v
  apply exists_congr
  intro x
  simpa only [updated_args args a ha] using he i (Function.update v a x)

theorem all {P : ∀ i, (Fin (n+1) → D i) → Prop} (h : UniformDefinable S m (n+1) P) (hn : n < m) :
    UniformDefinable S m n (fun i v => ∀ x, P i (Fin.cons x v)) :=
  (h.neg.ex hn).neg.congr (fun _ _ => by simp)

end UniformDefinable

end CPTSeparation.Counting

namespace CPTSeparation.Interpretations

open Classical Finset Hereditary

variable {R T : Type} {S S' : Structure R}

structure Structure.Iso (S S' : Structure R) where
  equiv : S.Carrier ≃ S'.Carrier
  rel : ∀ r x y, S.rel r x y = S'.rel r (equiv x) (equiv y)

end CPTSeparation.Interpretations

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Grid

open Classical Finset Support

variable {n : ℕ}

def localSizeBound : ℕ := 3^25

def atomSizeConstant : ℕ := 3*localSizeBound+localSizeBound^6

end CPTSeparation.Grid

namespace CPTSeparation.Grid

section

open Classical Hereditary Counting HFCoding Interpretations

variable {n : ℕ} (b : Vertex n → Scalar)

variable (P : Interpretations.Program Symbol)

variable {ι : Type} (bs : ι → Vertex n → Scalar) {s m : ℕ}

def programDomain (i : ι) : Set (HF (Atom (bs i))) := HereditarilySupported (G := CentralGroup n) s

def programHF (i : ι) : Counting.Structure (Forms.HFRelation AnalysisSymbol) (Domain (programDomain bs (s := s) i)) :=
  Forms.hfStructure (analysisStructure (bs i))

end

open Classical Hereditary Counting HFCoding Interpretations

variable {n B K N m M : ℕ} (P : Program Symbol) (vstar : Vertex n)

def twoCharges : Bool → Vertex n → Scalar
  | false => 0
  | true => Pi.single vstar 1

end CPTSeparation.Grid

namespace CPTSeparation.Quantitative

section

open Filter Asymptotics Topology

def radius (C q L : ℝ) : ℕ := ⌈2*L*(q*Real.logb 3 (C*L^3))^2⌉₊

def palette (L : ℝ) : ℕ := ⌊L^((7:ℝ)/4)⌋₊

end

def timeExponent (c d : ℕ) := c + 2*d + 2

def traceExponent (c d : ℕ) := 3*timeExponent c d + 4

end CPTSeparation.Quantitative

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Operational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Operational

open Classical Hereditary Finset

variable {A B R F : Type*} {arity : F → ℕ}

attribute [local instance] CPTSeparation.Operational.instDecidableEqHF

inductive Term (R F : Type*) (arity : F → ℕ) : ℕ → Type _
  | var {k} (i : Fin k) : Term R F arity k
  | constant {k} (n : ℕ) : Term R F arity k
  | atoms {k} : Term R F arity k
  | app {k} (f : F) (args : Fin (arity f) → Term R F arity k) : Term R F arity k
  | pair {k} (a b : Term R F arity k) : Term R F arity k
  | union {k} (a : Term R F arity k) : Term R F arity k
  | unique {k} (a : Term R F arity k) : Term R F arity k
  | card {k} (a : Term R F arity k) : Term R F arity k
  | equal {k} (a b : Term R F arity k) : Term R F arity k
  | member {k} (a b : Term R F arity k) : Term R F arity k
  | isAtom {k} (a : Term R F arity k) : Term R F arity k
  | input {k} (r : R) (a b : Term R F arity k) : Term R F arity k
  | not {k} (a : Term R F arity k) : Term R F arity k
  | and {k} (a b : Term R F arity k) : Term R F arity k
  | conditional {k} (c a b : Term R F arity k) : Term R F arity k
  | comprehension {k} (bound : Term R F arity k)
      (guard body : Term R F arity (k+1)) : Term R F arity k

namespace State

@[simp] theorem mem_support (s : State F arity A) (l : Location F arity A) :
    l ∈ s.support ↔ s.value l ≠ empty := Set.Finite.mem_toFinset _

end State

namespace Term

variable [Fintype A]

def eval (rel : R → A → A → Bool) (s : State F arity A) :
    {k : ℕ} → Term R F arity k → (Fin k → HF A) → HF A
  | _, .var i, v => v i
  | _, .constant n, _ => ordinal n
  | _, .atoms, _ => allAtoms
  | _, .app f args, v => s.value ⟨f,fun i => eval rel s (args i) v⟩
  | _, .pair a b, v => double (eval rel s a v) (eval rel s b v)
  | _, .union a, v => unionHF (eval rel s a v)
  | _, .unique a, v => uniqueHF (eval rel s a v)
  | _, .card a, v => cardinalityHF (eval rel s a v)
  | _, .equal a b, v => boolean (eval rel s a v = eval rel s b v)
  | _, .member a b, v => boolean (eval rel s a v ∈ eval rel s b v)
  | _, .isAtom a, v => boolean (isSet (eval rel s a v) = false)
  | _, .input r a b,v => boolean (inputRelation rel r (eval rel s a v) (eval rel s b v))
  | _, .not a,v => boolean (eval rel s a v ≠ truth)
  | _, .and a b,v => boolean (eval rel s a v = truth ∧ eval rel s b v = truth)
  | _, .conditional c a b,v => if eval rel s c v = truth then eval rel s a v else eval rel s b v
  | _, .comprehension bound guard body,v =>
      ofFinset (((elements (eval rel s bound v)).filter
        (fun x => eval rel s guard (Fin.cons x v) = truth)).image
        (fun x => eval rel s body (Fin.cons x v)))

end Term

inductive Rule (R F : Type*) (arity : F → ℕ) : ℕ → Type _
  | skip {k} : Rule R F arity k
  | update {k} (f : F) (args : Fin (arity f) → Term R F arity k)
      (value : Term R F arity k) : Rule R F arity k
  | parallel {k} (a b : Rule R F arity k) : Rule R F arity k
  | conditional {k} (c : Term R F arity k) (a b : Rule R F arity k) : Rule R F arity k
  | forall {k} (bound : Term R F arity k) (body : Rule R F arity (k+1)) : Rule R F arity k
  | letValue {k} (value : Term R F arity k) (body : Rule R F arity (k+1)) : Rule R F arity k

namespace Rule

variable [Fintype A]

def updates (rel : R → A → A → Bool) (s : State F arity A) :
    {k : ℕ} → Rule R F arity k → (Fin k → HF A) → Finset (Update F arity A)
  | _, .skip, _ => ∅
  | _, .update f args value, v => { (⟨f,fun i => (args i).eval rel s v⟩,value.eval rel s v) }
  | _, .parallel a b,v => updates rel s a v ∪ updates rel s b v
  | _, .conditional c a b,v => if c.eval rel s v = truth then updates rel s a v else updates rel s b v
  | _, .forall bound body,v => (elements (bound.eval rel s v)).biUnion
      (fun x => updates rel s body (Fin.cons x v))
  | _, .letValue value body,v => updates rel s body (Fin.cons (value.eval rel s v) v)

end Rule

instance instFintypeControl : Fintype Control where
  elems := {.halt,.accept}
  complete := by intro x; cases x <;> simp

structure Machine (R : Type*) where
  Functions : Type
  finiteFunctions : Fintype Functions
  arity : Functions → ℕ
  rule : Rule R (Control ⊕ Functions) (Sum.elim (fun _ => 0) arity) 0

namespace Machine

variable (P : Machine R) [Fintype A]

abbrev functionArity : Control ⊕ P.Functions → ℕ := Sum.elim (fun _ => 0) P.arity

abbrev Store := State (Control ⊕ P.Functions) P.functionArity A

def flag (s : P.Store (A := A)) (c : Control) : Prop := s.value ⟨.inl c,Fin.elim0⟩ = truth

def step (rel : R → A → A → Bool) (s : P.Store (A := A)) : Option (P.Store (A := A)) :=
  if P.flag s .halt then some s else
    let u := P.rule.updates rel s Fin.elim0
    if State.Consistent u then some (s.applyUpdates u) else none

def run (rel : R → A → A → Bool) : ℕ → Option (P.Store (A := A))
  | 0 => some State.initial
  | j+1 => (run rel j).bind (P.step rel)

end Machine

end CPTSeparation.Operational

namespace CPTSeparation.Hereditary

open Classical Finset

variable {A B : Type*}

attribute [local instance] CPTSeparation.Hereditary.instDecidableEqHF_1

@[simp] lemma mem_closure_self (x : HF A) : x ∈ closure x := by rw [closure]; simp

end CPTSeparation.Hereditary

namespace CPTSeparation.Operational

section

open Classical Hereditary Finset

variable {A R F : Type*} {arity : F → ℕ}

attribute [local instance] CPTSeparation.Operational.instDecidableEqHF_1

namespace Machine

variable (P : Machine R) [Fintype A]

def runActive (rel : R → A → A → Bool) (h : ℕ) : Finset (HF A) :=
  (range (h+1)).biUnion fun j => match P.run rel j with
    | none => ∅
    | some s => s.active

end Machine

end

open Classical Hereditary Finset

variable {A B R F : Type*} {arity : F → ℕ}

local instance instDecidableEqHF_2 {C : Type*} : DecidableEq (HF C) := Classical.decEq _

abbrev lift (e : A ≃ B) : HF A ≃ HF B := mapEquiv e

@[simp] lemma lift_empty (e : A ≃ B) : lift e empty = empty := map_ordinal e 0

@[simp] lemma lift_truth (e : A ≃ B) : lift e truth = truth := map_ordinal e 1

@[simp] lemma lift_ordinal (e : A ≃ B) (n : ℕ) : lift e (ordinal n) = ordinal n := map_ordinal e n

@[simp] lemma lift_double (e : A ≃ B) (x y : HF A) : lift e (double x y) = double (lift e x) (lift e y) := map_double e x y

@[simp] lemma lift_isSet (e : A ≃ B) (x : HF A) : isSet (lift e x) = isSet x := isSet_map e x

@[simp] lemma lift_boolean (e : A ≃ B) (p : Prop) : lift e (boolean p) = boolean p := by
  by_cases h : p <;> simp [boolean,h]

@[simp] lemma lift_truth_iff (e : A ≃ B) (x : HF A) : lift e x = truth ↔ x = truth := by
  rw [← lift_truth e,Equiv.apply_eq_iff_eq]

@[simp] lemma lift_empty_iff (e : A ≃ B) (x : HF A) : lift e x = empty ↔ x = empty := by
  rw [← lift_empty e,Equiv.apply_eq_iff_eq]

def locationEquiv (e : A ≃ B) : Location F arity A ≃ Location F arity B :=
  Equiv.sigmaCongrRight (fun _ => Equiv.piCongrRight (fun _ => lift e))

@[simp] lemma locationEquiv_apply (e : A ≃ B) (f : F) (v : Fin (arity f) → HF A) :
    locationEquiv e ⟨f,v⟩ = ⟨f,fun j => lift e (v j)⟩ := rfl

@[simp] lemma locationEquiv_symm_apply (e : A ≃ B) (f : F) (v : Fin (arity f) → HF B) :
    (locationEquiv e).symm ⟨f,v⟩ = ⟨f,fun j => (lift e).symm (v j)⟩ := rfl

namespace State

def transport (e : A ≃ B) (s : State F arity A) : State F arity B where
  value := fun l => lift e (s.value ((locationEquiv e).symm l))
  finite := by
    apply (s.finite.image (locationEquiv e)).subset
    intro l hl
    exact ⟨(locationEquiv e).symm l,by simpa using hl,Equiv.apply_symm_apply _ _⟩

@[simp] lemma transport_value (e : A ≃ B) (s : State F arity A) (l : Location F arity A) :
    (s.transport e).value (locationEquiv e l) = lift e (s.value l) := by
  simp [transport]

@[ext] lemma ext_value (s t : State F arity A) (h : ∀ l, s.value l = t.value l) : s = t := by
  cases s; cases t
  congr
  funext l
  exact h l

@[simp] lemma transport_initial (e : A ≃ B) : (initial : State F arity A).transport e = initial := by
  apply ext_value
  intro l
  simp [transport,initial]

end State

abbrev updateEquiv (e : A ≃ B) : Update F arity A ≃ Update F arity B :=
  Equiv.prodCongr (locationEquiv e) (lift e)

end CPTSeparation.Operational

namespace CPTSeparation.Hereditary

open Classical Finset

variable {A : Type*}

local instance instDecidableEqHF_2 {C : Type*} : DecidableEq (HF C) := Classical.decEq _

end CPTSeparation.Hereditary

namespace CPTSeparation.Operational

open Classical Hereditary Finset

variable {A R F : Type*} {arity : F → ℕ}

local instance instDecidableEqHF_3 {C : Type*} : DecidableEq (HF C) := Classical.decEq _

namespace Term

variable [Fintype A]

def trace (rel : R → A → A → Bool) (s : State F arity A) :
    {k : ℕ} → Term R F arity k → (Fin k → HF A) → Finset (HF A)
  | _, .var i,v => closure (v i)
  | _, .constant n,_ => closure (ordinal n)
  | _, .atoms,_ => closure allAtoms
  | _, .app f args,v => closure (s.value ⟨f,fun j => (args j).eval rel s v⟩) ∪
      univ.biUnion (fun j => trace rel s (args j) v)
  | _, .pair a b,v => closure (double (a.eval rel s v) (b.eval rel s v)) ∪ trace rel s a v ∪ trace rel s b v
  | _, .union a,v => closure (unionHF (a.eval rel s v)) ∪ trace rel s a v
  | _, .unique a,v => closure (uniqueHF (a.eval rel s v)) ∪ trace rel s a v
  | _, .card a,v => closure (cardinalityHF (a.eval rel s v)) ∪ trace rel s a v
  | _, .equal a b,v => closure (boolean (a.eval rel s v = b.eval rel s v)) ∪ trace rel s a v ∪ trace rel s b v
  | _, .member a b,v => closure (boolean (a.eval rel s v ∈ b.eval rel s v)) ∪ trace rel s a v ∪ trace rel s b v
  | _, .isAtom a,v => closure (boolean (isSet (a.eval rel s v) = false)) ∪ trace rel s a v
  | _, .input r a b,v => closure (boolean (inputRelation rel r (a.eval rel s v) (b.eval rel s v))) ∪ trace rel s a v ∪ trace rel s b v
  | _, .not a,v => closure (boolean (a.eval rel s v ≠ truth)) ∪ trace rel s a v
  | _, .and a b,v => closure (boolean (a.eval rel s v = truth ∧ b.eval rel s v = truth)) ∪ trace rel s a v ∪ trace rel s b v
  | _, .conditional c a b,v => trace rel s c v ∪ trace rel s a v ∪ trace rel s b v
  | _, .comprehension bound guard body,v =>
      insert (ofFinset (((elements (bound.eval rel s v)).filter
        (fun x => guard.eval rel s (Fin.cons x v) = truth)).image
        (fun x => body.eval rel s (Fin.cons x v))))
      (trace rel s bound v ∪ (elements (bound.eval rel s v)).biUnion
        (fun x => trace rel s guard (Fin.cons x v) ∪ trace rel s body (Fin.cons x v)))

def bound : {k : ℕ} → Term R F arity k → Polynomial ℕ
  | _, .var _ => .X
  | _, .constant n => .C (n+1)
  | _, .atoms => .X
  | _, .app _ args => .X + ∑ j, bound (args j)
  | _, .pair a b => 1 + 2 * (bound a + bound b)
  | _, .union a => 1 + 2 * bound a
  | _, .unique a => 1 + 2 * bound a
  | _, .card a => 1 + 2 * bound a
  | _, .equal a b => 2 + bound a + bound b
  | _, .member a b => 2 + bound a + bound b
  | _, .isAtom a => 2 + bound a
  | _, .input _ a b => 2 + bound a + bound b
  | _, .not a => 2 + bound a
  | _, .and a b => 2 + bound a + bound b
  | _, .conditional c a b => bound c + bound a + bound b
  | _, .comprehension b g t => 1 + bound b + bound b *
      ((bound g).comp (.X + bound b) + (bound t).comp (.X + bound b))

def potential {k : ℕ} (s : State F arity A) (v : Fin k → HF A) : ℕ :=
  s.active.card + ∑ j, (closure (v j)).card

end Term

end CPTSeparation.Operational

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Definability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Operational

open Classical Hereditary Counting HFCoding Finset

local instance instDecidableEqHF_4_r2d95cd_1 {A : Type*} : DecidableEq (HF A) := Classical.decEq _
variable {ι R : Type} {A : ι → Type} [finiteFamilyA : ∀ i, Fintype (A i)]

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure R (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (hm : 6 ≤ m)

include hd hmem hset hm

def BoundedCard (K : ℕ) {i : ι} (z x : Domain (d i)) : Prop :=
  (elements x.val).card ≤ K ∧ z.val = cardinalityHF x.val

end CPTSeparation.Operational

namespace CPTSeparation.Operational.Term

open Classical Hereditary Counting HFCoding Finset

local instance instDecidableEqHF {A : Type*} : DecidableEq (HF A) := Classical.decEq _

variable {A R F : Type} {arity : F → ℕ} [Fintype A]

def Graph (d : Set (HF A)) (K : ℕ) (rel : R → A → A → Bool) (s : State F arity A) :
    {k : ℕ} → Term R F arity k → Domain d → (Fin k → Domain d) → Prop
  | _,.var j,z,v => z = v j
  | _,.constant n,z,_ => z.val = ordinal n
  | _,.atoms,z,_ => z.val = allAtoms
  | _,.app f args,z,v => ∃ w : Fin (arity f) → Domain d,
      (∀ j, Graph d K rel s (args j) (w j) v) ∧ z.val = s.value ⟨f,fun j => (w j).val⟩
  | _,.pair a b,z,v => ∃ x y, Graph d K rel s a x v ∧ Graph d K rel s b y v ∧ z.val = double x.val y.val
  | _,.union a,z,v => ∃ x, Graph d K rel s a x v ∧ z.val = unionHF x.val
  | _,.unique a,z,v => ∃ x, Graph d K rel s a x v ∧ z.val = uniqueHF x.val
  | _,.card a,z,v => ∃ x, Graph d K rel s a x v ∧ (elements x.val).card ≤ K ∧ z.val = cardinalityHF x.val
  | _,.equal a b,z,v => ∃ x y, Graph d K rel s a x v ∧ Graph d K rel s b y v ∧ z.val = boolean (x.val = y.val)
  | _,.member a b,z,v => ∃ x y, Graph d K rel s a x v ∧ Graph d K rel s b y v ∧ z.val = boolean (x.val ∈ y.val)
  | _,.isAtom a,z,v => ∃ x, Graph d K rel s a x v ∧ z.val = boolean (isSet x.val = false)
  | _,.input r a b,z,v => ∃ x y, Graph d K rel s a x v ∧ Graph d K rel s b y v ∧ z.val = boolean (inputRelation rel r x.val y.val)
  | _,.not a,z,v => ∃ x, Graph d K rel s a x v ∧ z.val = boolean (x.val ≠ truth)
  | _,.and a b,z,v => ∃ x y, Graph d K rel s a x v ∧ Graph d K rel s b y v ∧ z.val = boolean (x.val = truth ∧ y.val = truth)
  | _,.conditional c a b,z,v => ∃ x, Graph d K rel s c x v ∧
      ((x.val = truth ∧ Graph d K rel s a z v) ∨ (x.val ≠ truth ∧ Graph d K rel s b z v))
  | _,.comprehension bound guard body,z,v => ∃ b, Graph d K rel s bound b v ∧
      (∀ x : Domain d, x.val ∈ b.val → ∃ g y, Graph d K rel s guard g (Fin.cons x v) ∧ Graph d K rel s body y (Fin.cons x v)) ∧
      isSet z.val = true ∧ ∀ y : Domain d, y.val ∈ z.val ↔ ∃ x : Domain d,
        x.val ∈ b.val ∧ (∃ g, Graph d K rel s guard g (Fin.cons x v) ∧ g.val = truth) ∧
        Graph d K rel s body y (Fin.cons x v)

end CPTSeparation.Operational.Term

namespace CPTSeparation.Operational.Term

open Classical Hereditary Counting HFCoding Finset

local instance instDecidableEqHF_1_r2d95cd_1 {A : Type*} : DecidableEq (HF A) := Classical.decEq _
variable {R F : Type} {arity : F → ℕ}

def width : {k : ℕ} → Term R F arity k → ℕ
  | k,.var _ | k,.constant _ | k,.atoms => k+6
  | k,.app f args => k+6+arity f+∑ j, width (args j)
  | k,.pair a b | k,.equal a b | k,.member a b | k,.input _ a b | k,.and a b => k+6+width a+width b
  | k,.union a | k,.unique a | k,.card a | k,.isAtom a | k,.not a => k+6+width a
  | k,.conditional c a b => k+6+width c+width a+width b
  | k,.comprehension a b c => k+6+width a+width b+width c

end CPTSeparation.Operational.Term

namespace CPTSeparation.Operational.Rule

section

open Classical Hereditary Finset

variable {A R F : Type} {arity : F → ℕ} [Fintype A]

local instance instDecidableEqHF {C : Type} : DecidableEq (HF C) := Classical.decEq _

def trace (rel : R → A → A → Bool) (s : State F arity A) :
    {k : ℕ} → Rule R F arity k → (Fin k → HF A) → Finset (HF A)
  | _,.skip,_ => ∅
  | _,.update _ args value,v => value.trace rel s v ∪ univ.biUnion (fun j => (args j).trace rel s v)
  | _,.parallel a b,v => trace rel s a v ∪ trace rel s b v
  | _,.conditional c a b,v => c.trace rel s v ∪ trace rel s a v ∪ trace rel s b v
  | _,.forall b r,v => b.trace rel s v ∪ (elements (b.eval rel s v)).biUnion (fun x => trace rel s r (Fin.cons x v))
  | _,.letValue b r,v => b.trace rel s v ∪ trace rel s r (Fin.cons (b.eval rel s v) v)

def bound : {k : ℕ} → Rule R F arity k → Polynomial ℕ
  | _,.skip => 0
  | _,.update _ args value => value.bound + ∑ j, (args j).bound
  | _,.parallel a b => bound a + bound b
  | _,.conditional c a b => c.bound + bound a + bound b
  | _,.forall b r => b.bound + b.bound * (bound r).comp (.X + b.bound)
  | _,.letValue b r => b.bound + (bound r).comp (.X + b.bound)

end

section

open Classical Hereditary Counting HFCoding Finset

variable {A R F : Type} {arity : F → ℕ} [Fintype A]

local instance instDecidableEqHF_1 {C : Type} : DecidableEq (HF C) := Classical.decEq _

def Graph (d : Set (HF A)) (K : ℕ) (rel : R → A → A → Bool) (s : State F arity A) :
    {k : ℕ} → Rule R F arity k → (f : F) → Domain d → (Fin (arity f) → Domain d) → (Fin k → Domain d) → Prop
  | _,.skip,_,_,_,_ => False
  | _,.update g args value,f,z,a,v => if h : g = f then
      Term.Graph d K rel s value z v ∧ ∀ j, Term.Graph d K rel s (args j) (a (Fin.cast (congrArg arity h) j)) v else False
  | _,.parallel r t,f,z,a,v => Graph d K rel s r f z a v ∨ Graph d K rel s t f z a v
  | _,.conditional c r t,f,z,a,v => ∃ b, Term.Graph d K rel s c b v ∧
      ((b.val = truth ∧ Graph d K rel s r f z a v) ∨ (b.val ≠ truth ∧ Graph d K rel s t f z a v))
  | _,.forall b r,f,z,a,v => ∃ w x, Term.Graph d K rel s b w v ∧ x.val ∈ w.val ∧ Graph d K rel s r f z a (Fin.cons x v)
  | _,.letValue b r,f,z,a,v => ∃ w, Term.Graph d K rel s b w v ∧ Graph d K rel s r f z a (Fin.cons w v)

end

open Classical Hereditary Counting HFCoding Finset

variable {R F : Type} {arity : F → ℕ}

def width : {k : ℕ} → Rule R F arity k → ℕ
  | _,.skip => 6
  | _,.update _ args value => 6+value.width+∑ j, (args j).width
  | _,.parallel r t => 6+width r+width t
  | _,.conditional c r t => 6+c.width+width r+width t
  | _,.forall b r | _,.letValue b r => 6+b.width+width r

end CPTSeparation.Operational.Rule

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Simulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Operational

section

open Classical Hereditary Finset

variable {A R F : Type} {arity : F → ℕ} [finiteA : Fintype A]

local instance instDecidableEqHF_5 {B : Type} : DecidableEq (HF B) := Classical.decEq _

def Closed (t : Finset (HF A)) : Prop := ∀ x ∈ t, ∀ y, y ∈ x → y ∈ t

end

open Classical Hereditary Finset

variable {A B R F : Type} {arity : F → ℕ} [finiteA : Fintype A] [finiteB : Fintype B]

local instance instDecidableEqHF_7 {C : Type} : DecidableEq (HF C) := Classical.decEq _

end CPTSeparation.Operational

namespace CPTSeparation.Operational.Machine

section

open Classical Hereditary Finset

variable {A B R : Type} [Fintype A] [Fintype B]

local instance instDecidableEqHF {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable (P : Machine R)

def runTrace (rel : R → A → A → Bool) (h : ℕ) : Finset (HF A) :=
  P.runActive rel h ∪ (range (h+1)).biUnion (fun j => match P.run rel j with
    | none => ∅
    | some s => P.rule.trace rel s Fin.elim0)

end

open Classical Hereditary Counting HFCoding Finset

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

section

open Classical Hereditary Counting HFCoding Operational Finset

local instance instDecidableEqHF {C : Type} : DecidableEq (HF C) := Classical.decEq _

end

open Classical Hereditary Counting HFCoding Operational Finset

end CPTSeparation.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Traces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Hereditary

open Classical Finset

variable {A : Type}

local instance instDecidableEqHF_3 : DecidableEq (HF A) := Classical.decEq _

def descendants (t : Finset (HF A)) : ℕ → Finset (HF A)
  | 0 => t
  | k+1 => descendants t k ∪ (descendants t k).biUnion elements

end CPTSeparation.Hereditary

namespace CPTSeparation.Operational.State

open Classical Hereditary Counting HFCoding Finset

variable {ι L F : Type} {A : ι → Type} [finiteFamilyA : ∀ i, Fintype (A i)] [finiteF : Fintype F] {arity : F → ℕ}

local instance instDecidableEqHF {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (s : ∀ i, State F arity (A i))

variable (hstate : ∀ f, UniformDefinable S m (arity f+1)
  (fun i v => (v 0).val = (s i).value ⟨f,fun j => (v j.succ).val⟩))

def rootFamily {i : ι} (s : State F arity (A i)) : Finset (HF (A i)) :=
  s.critical ∪ {allAtoms,empty,truth} ∪ univ.image atom

end CPTSeparation.Operational.State

namespace CPTSeparation.Operational

open Classical Hereditary Counting HFCoding Finset

variable {ι R L F : Type} {A : ι → Type} [finiteFamilyA : ∀ i, Fintype (A i)] [Fintype F] {arity : F → ℕ}

local instance instDecidableEqHF_8 {C : Type} : DecidableEq (HF C) := Classical.decEq _

end CPTSeparation.Operational

namespace CPTSeparation.Operational

open Classical Hereditary Counting HFCoding Finset

variable {A R F : Type} [Fintype A] {arity : F → ℕ}

local instance instDecidableEqHF_9 {C : Type} : DecidableEq (HF C) := Classical.decEq _

namespace Machine

variable (P : Machine R)

def boundedAccepts (rel : R → A → A → Bool) (time space : ℕ) : Prop :=
  ∃ h st, h ≤ time ∧ P.run rel h = some st ∧ P.flag st .halt ∧ P.flag st .accept ∧
    ∀ j, j ≤ h → ∀ t, P.run rel j = some t → t.active.card ≤ space

end Machine

end CPTSeparation.Operational

namespace CPTSeparation.Operational.Machine

open Classical Hereditary Counting HFCoding Finset

variable {R : Type} {A : Bool → Type} [∀ i, Fintype (A i)]

local instance instDecidableEqHF_2_r2d95cd_1 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable (P : Machine R) (rel : ∀ i, R → A i → A i → Bool)

def PrefixBound (h K : ℕ) : Prop :=
  ∀ i j, j ≤ h → ∃ st, P.run (rel i) j = some st ∧ st.active.card ≤ K

def ObservationsAt (h : ℕ) : Prop :=
  ∀ (i j : Bool) (s : P.Store (A := A i)) (t : P.Store (A := A j)),
    P.run (rel i) h = some s → P.run (rel j) h = some t →
      (∀ c, P.flag s c ↔ P.flag t c) ∧
      (State.Consistent (P.rule.updates (rel i) s Fin.elim0) ↔
        State.Consistent (P.rule.updates (rel j) t Fin.elim0)) ∧ s.active.card = t.active.card

end CPTSeparation.Operational.Machine

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.FullLanguage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation.FullCPT

noncomputable section

open Classical Hereditary Finset

open Operational (State Control Location Update)

attribute [local instance] CPTSeparation.FullCPT.instDecidableEqHF

variable {A R F : Type} {arity : F → ℕ}

def bindSlots {k : ℕ} (slots : ℕ → Option (Fin k)) (name : ℕ) : ℕ → Option (Fin (k+1)) :=
  fun x => if x = name then some 0 else (slots x).map Fin.succ

def Agrees {k : ℕ} (slots : ℕ → Option (Fin k)) (env : ℕ → HF A)
    (values : Fin k → HF A) : Prop :=
  ∀ x, env x = (slots x).elim Operational.empty values

namespace Term

def compile : Term R F arity → {k : ℕ} → (ℕ → Option (Fin k)) → Operational.Term R F arity k
  | .var n, _, slots => match slots n with
      | none => .constant 0
      | some i => .var i
  | .ordinal n, _, _ => .constant n
  | .atoms, _, _ => .atoms
  | .app f args, _, slots => .app f (fun i => compile (args i) slots)
  | .pair a b, _, slots => .pair (compile a slots) (compile b slots)
  | .union a, _, slots => .union (compile a slots)
  | .unique a, _, slots => .unique (compile a slots)
  | .card a, _, slots => .card (compile a slots)
  | .equal a b, _, slots => .equal (compile a slots) (compile b slots)
  | .member a b, _, slots => .member (compile a slots) (compile b slots)
  | .isAtom a, _, slots => .isAtom (compile a slots)
  | .input r a b, _, slots => .input r (compile a slots) (compile b slots)
  | .not a, _, slots => .not (compile a slots)
  | .and a b, _, slots => .and (compile a slots) (compile b slots)
  | .or a b, _, slots => .not (.and (.not (compile a slots)) (.not (compile b slots)))
  | .conditional c a b, _, slots => .conditional (compile c slots) (compile a slots) (compile b slots)
  | .comprehend n bound guard body, _, slots =>
      .comprehension (compile bound slots) (compile guard (bindSlots slots n))
        (compile body (bindSlots slots n))

end Term

namespace Rule

def compile : Rule R F arity → {k : ℕ} → (ℕ → Option (Fin k)) → Operational.Rule R F arity k
  | .skip, _, _ => .skip
  | .update f args value, _, slots => .update f (fun i => (args i).compile slots) (value.compile slots)
  | .parallel a b, _, slots => .parallel (compile a slots) (compile b slots)
  | .conditional c a b, _, slots => .conditional (c.compile slots) (compile a slots) (compile b slots)
  | .forall n bound body, _, slots => .forall (bound.compile slots) (compile body (bindSlots slots n))
  | .letValue n value body, _, slots => .letValue (value.compile slots) (compile body (bindSlots slots n))

end Rule

namespace Program

variable (P : Program R) [finiteA : Fintype A]

def compile : Operational.Machine R where
  Functions := P.Functions
  finiteFunctions := P.finiteFunctions
  arity := P.arity
  rule := P.body.compile (fun _ => none)

end Program

end

end CPTSeparation.FullCPT

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Observers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Operational.Machine

open Classical Hereditary Counting HFCoding Finset

variable {A R : Type} [Fintype A]

local instance instDecidableEqHF_5 {C : Type} : DecidableEq (HF C) := Classical.decEq _

abbrev Observer (P : Machine R) := Term R (Control ⊕ P.Functions) P.functionArity 0

abbrev instrument (P : Machine R) (O : P.Observer) : Machine R where
 Functions := P.Functions
 finiteFunctions := P.finiteFunctions
 arity := P.arity
 rule := .parallel P.rule (.letValue O .skip)

variable (P : Machine R) (O : P.Observer)

@[simp] lemma instrument_step (rel : R → A → A → Bool) (s : P.Store (A := A)) :
 (P.instrument O).step rel s = P.step rel s := by
 simp only [step,instrument,Rule.updates,union_empty]
 rfl

@[simp] lemma instrument_run (rel : R → A → A → Bool) (h : ℕ) :
 (P.instrument O).run rel h = P.run rel h := by
 induction h with
 | zero => rfl
 | succ h ih =>
   simp only [run,ih]
   congr 1
   funext s
   exact P.instrument_step O rel s

@[simp] lemma instrument_active (rel : R → A → A → Bool) (h : ℕ) :
 (P.instrument O).runActive rel h = P.runActive rel h := by
 simp only [runActive,instrument_run]
 apply biUnion_congr rfl
 intro j hj
 cases P.run rel j <;> rfl

def observed (rel : R → A → A → Bool) (h : ℕ) : Finset (HF A) :=
 P.runActive rel h ∪ (range h).biUnion (fun j => match P.run rel j with
  | none => ∅
  | some s => familyClosure (elements (O.eval rel s Fin.elim0)))

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Operational.Machine

section

open Classical Hereditary Finset

variable {A R : Type} [Fintype A]

local instance instDecidableEqHF_7_r2d95cd_1 {C : Type} : DecidableEq (HF C) := Classical.decEq _
variable (P : Machine R) (O : P.Observer)

def observedAccepts (rel : R → A → A → Bool) (time space : ℕ) : Prop :=
  ∃ h st, h ≤ time ∧ P.run rel h = some st ∧ P.flag st .halt ∧ P.flag st .accept ∧
    (P.observed O rel h).card ≤ space

end

def polynomialObservedAccepts {A R : Type} [Fintype A] (P : Machine R) (O : P.Observer)
 (time space : Polynomial ℕ) (rel : R → A → A → Bool) : Prop :=
 P.observedAccepts O rel (time.eval (Fintype.card A)) (space.eval (Fintype.card A))

end CPTSeparation.Operational.Machine

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Evaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation.FullCPT

noncomputable section

open Classical Hereditary Finset

open Operational (State Control)

attribute [local instance] CPTSeparation.FullCPT.instDecidableEqHF_1

variable {A R F : Type} {arity : F → ℕ}

namespace Term

variable [finiteA : Fintype A]

omit A in
@[simp] lemma elements_zero
    {A : Type}
    [Fintype A] : elements (Hereditary.ordinal (A := A) 0) = ∅ := by simp [Hereditary.ordinal]

def pack (t : Term R F arity) : Term R F arity := .pair t t

def merge (a b : Term R F arity) : Term R F arity := .union (.pair a b)

def merges (ts : List (Term R F arity)) : Term R F arity := ts.foldr merge (.ordinal 0)

def collect : Term R F arity → Term R F arity
  | t@(.var _) | t@(.ordinal _) | t@(.atoms) => pack t
  | t@(.app _ args) => merge (pack t) (merges (List.ofFn (fun i => collect (args i))))
  | t@(.pair a b) | t@(.equal a b) | t@(.member a b)
  | t@(.input _ a b) | t@(.and a b) | t@(.or a b) =>
      merge (pack t) (merge (collect a) (collect b))
  | t@(.union a) | t@(.unique a) | t@(.card a)
  | t@(.isAtom a) | t@(.not a) => merge (pack t) (collect a)
  | .conditional c a b => merge (collect c) (.conditional c (collect a) (collect b))
  | t@(.comprehend n bound guard body) => merge (pack t)
      (merge (collect bound) (.union (.comprehend n bound (.ordinal 1)
        (merge (collect guard) (.conditional guard (collect body) (.ordinal 0))))))

@[simp] lemma eval_pack (rel : R → A → A → Bool) (s : State F arity A) (t : Term R F arity) (v : ℕ → HF A) :
 (pack t).eval rel s v = ofFinset {t.eval rel s v} := by simp [pack,eval,double]

@[simp] lemma eval_merge (rel : R → A → A → Bool) (s : State F arity A) (a b : Term R F arity) (v : ℕ → HF A) :
 (merge a b).eval rel s v = ofFinset (elements (a.eval rel s v) ∪ elements (b.eval rel s v)) := by
 simp [merge,eval,Operational.unionHF,double]

@[simp] lemma eval_merges (rel : R → A → A → Bool) (s : State F arity A) (ts : List (Term R F arity)) (v : ℕ → HF A) :
 (merges ts).eval rel s v = ofFinset ((ts.map (fun t => elements (t.eval rel s v))).foldr (· ∪ ·) ∅) := by
 induction ts with
 | nil => rfl
 | cons t ts ih =>
   simp only [merges] at ih ⊢
   simp only [List.foldr_cons,eval_merge,ih,elements_ofFinset,List.map_cons,List.foldr_cons]

@[simp] lemma eval_spread (rel : R → A → A → Bool) (s : State F arity A)
 (n : ℕ) (bound body : Term R F arity) (v : ℕ → HF A) :
 (Term.union (Term.comprehend n bound (.ordinal 1) body)).eval rel s v =
   ofFinset ((elements (bound.eval rel s v)).biUnion
     (fun x => elements (body.eval rel s (Function.update v n x)))) := by
 simp [eval,Operational.unionHF,image_biUnion]

end Term

namespace Rule

variable [Fintype A]

def collect : Rule R F arity → Term R F arity
 | .skip => .ordinal 0
 | .update _ args value => Term.merge value.collect (Term.merges (List.ofFn (fun i => (args i).collect)))
 | .parallel a b => Term.merge (collect a) (collect b)
 | .conditional c a b => Term.merge c.collect (.conditional c (collect a) (collect b))
 | .forall n bound body => Term.merge bound.collect (.union (.comprehend n bound (.ordinal 1) (collect body)))
 | .letValue n value body => Term.merge value.collect
     (.union (.comprehend n (Term.pack value) (.ordinal 1) (collect body)))

end Rule

namespace Program

variable (P : Program R) [Fintype A]

def rootObserver : P.compile.Observer :=
 (Term.conditional (.app (.inl .halt) Fin.elim0) (.ordinal 0) P.body.collect).compile (fun _ => none)

end Program

end

end CPTSeparation.FullCPT

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Gaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation.Gaussian

abbrev Scalar := ZMod 3

structure Row (n : ℕ) where
  coeff : Fin n → Scalar
  rhs : Scalar

namespace Row

def satisfies {n} (r : Row n) (v : Fin n → Scalar) : Prop :=
  (∑ i, r.coeff i * v i) = r.rhs

def tail {n} (r : Row (n+1)) : Row n := ⟨fun i => r.coeff i.succ,r.rhs⟩

def reduce {n} (p r : Row (n+1)) : Row n :=
  ⟨fun i => r.coeff i.succ - (r.coeff 0 / p.coeff 0)*p.coeff i.succ,
    r.rhs - (r.coeff 0 / p.coeff 0)*p.rhs⟩

end Row

def Solvable {n} (rows : List (Row n)) : Prop := ∃ v, ∀ r ∈ rows, r.satisfies v

def pivot {n} (rows : List (Row (n+1))) : Option (Row (n+1)) :=
  rows.find? (fun r => r.coeff 0 != 0)

def solve : {n : ℕ} → List (Row n) → Bool
  | 0, rows => rows.all (fun r => r.rhs == 0)
  | _+1, rows => match pivot rows with
    | none => solve (rows.map Row.tail)
    | some p => solve (rows.map (Row.reduce p))

namespace Row

def dense {n} (r : Row n) : Row n :=
  let a := Vector.ofFn r.coeff
  ⟨a.get,r.rhs⟩

@[simp] lemma dense_eq {n} (r : Row n) : r.dense = r := by
  cases r
  simp only [dense]
  congr 1
  funext i
  exact Vector.get_ofFn _ i

def reduceDense {n} (p r : Row (n+1)) : Row n :=
  let c := r.coeff 0 / p.coeff 0
  let a := Vector.ofFn (fun i : Fin n => r.coeff i.succ - c*p.coeff i.succ)
  ⟨a.get,r.rhs-c*p.rhs⟩

@[simp] lemma reduceDense_eq {n} (p r : Row (n+1)) : p.reduceDense r = p.reduce r := by
  simp only [reduceDense,reduce]
  congr 1
  funext i
  exact Vector.get_ofFn _ i

end Row

def metered : {n : ℕ} → List (Row n) → Bool × ℕ
  | 0, rows => (rows.all (fun r => r.rhs == 0),2*rows.length+1)
  | n+1, rows =>
    let next := match pivot rows with
      | none => metered (rows.map (fun (r : Row (n+1)) => r.tail.dense))
      | some p => metered (rows.map (Row.reduceDense p))
    (next.1, next.2 + (8*n+12)*rows.length+2)

@[simp] theorem metered_answer {n} (rows : List (Row n)) : (metered rows).1 = solve rows := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hp : pivot rows with
    | none => simp [metered,solve,hp,ih]
    | some p =>
      have he : p.reduceDense = p.reduce := funext (fun r => Row.reduceDense_eq p r)
      simp [metered,solve,hp,ih,he]

end CPTSeparation.Gaussian

namespace CPTSeparation.OrderedQuery

open Finset

variable {N : ℕ}

def coefficient (S : Data N) (y a : Fin N) : Scalar :=
  ∑ x, if S.rel .Ed x x ∧ S.rel .I a x then
    ∑ δ : Scalar, if S.rel (.Z δ) y x then δ else 0 else 0

def incident (S : Data N) (t y : Fin N) : Bool :=
  (List.finRange N).any fun a => S.rel .Cf a a && S.rel .VB t a &&
    (List.finRange N).any fun x => S.rel .Ed x x && S.rel .I a x && S.rel .EB y x

def normalizationRow (S : Data N) (t : Fin N) : Gaussian.Row (N+N) := if S.rel .Cf t t then
  ⟨Fin.addCases (fun a => if S.rel .Cf a a && S.rel .VB t a then 1 else 0)
    (fun _ => 0),1⟩ else ⟨fun _ => 0,0⟩

def consistencyRow (S : Data N) (t y : Fin N) : Gaussian.Row (N+N) :=
  if S.rel .Cf t t && S.rel .Ed y y && incident S t y then
    ⟨Fin.addCases (fun a => if S.rel .Cf a a && S.rel .VB t a then -coefficient S y a else 0)
      (fun z => if z = y then 1 else 0),0⟩ else ⟨fun _ => 0,0⟩

def rows (S : Data N) : List (Gaussian.Row (N+N)) :=
  (List.finRange N).map (normalizationRow S) ++
    (List.finRange N).flatMap (fun t => (List.finRange N).map (consistencyRow S t))

def decideQuery (S : Data N) : Bool :=
  (Gaussian.metered ((rows S).map Gaussian.Row.dense)).1

def left (v : Fin (N+N) → Scalar) (a : Fin N) := v (Fin.castAdd N a)

def right (v : Fin (N+N) → Scalar) (y : Fin N) := v (Fin.natAdd N y)

theorem rows_length (S : Data N) : (rows S).length = N+N*N := by
  simp [rows,List.length_flatMap]

end CPTSeparation.OrderedQuery

namespace CPTSeparation.SerialGaussian

structure Row (n : ℕ) where
  coeff : List Scalar
  length_eq : coeff.length = n
  rhs : Scalar

def Row.decode {n} (r : Row n) : Gaussian.Row n :=
  ⟨fun i => r.coeff[i.val]'(by rw [r.length_eq]; exact i.isLt),r.rhs⟩

def Row.encode {n} (r : Gaussian.Row n) : Row n :=
  ⟨List.ofFn r.coeff,by simp,r.rhs⟩

def Row.head {n} (r : Row (n+1)) : Scalar := r.coeff.headD 0

def Row.tail {n} (r : Row (n+1)) : Row n :=
  ⟨r.coeff.tail,by simp [r.length_eq],r.rhs⟩

def Row.reduce {n} (p r : Row (n+1)) : Row n :=
  let c := r.head / p.head
  ⟨List.zipWith (fun x y => x-c*y) r.coeff.tail p.coeff.tail,
    by simp [r.length_eq,p.length_eq],r.rhs-c*p.rhs⟩

def pivot {n} (rows : List (Row (n+1))) : Option (Row (n+1)) :=
  rows.find? (fun r => r.head != 0)

def solve : {n : ℕ} → List (Row n) → Bool
  | 0,rows => rows.all (fun r => r.rhs == 0)
  | _+1,rows => match pivot rows with
    | none => solve (rows.map Row.tail)
    | some p => solve (rows.map (Row.reduce p))

@[simp] theorem Row.decode_encode {n} (r : Gaussian.Row n) : (Row.encode r).decode = r := by
  cases r
  simp only [Row.encode,Row.decode,List.getElem_ofFn]

@[simp] theorem Row.head_decode {n} (r : Row (n+1)) : r.head = r.decode.coeff 0 := by
  rcases r with ⟨l,h,b⟩
  cases l with
  | nil => simp at h
  | cons a l => rfl

@[simp] theorem Row.decode_tail {n} (r : Row (n+1)) : r.tail.decode = r.decode.tail := by
  apply congrArg₂ Gaussian.Row.mk
  · funext i
    simp [Row.decode,Row.tail]
  · rfl

@[simp] theorem Row.decode_reduce {n} (p r : Row (n+1)) :
    (p.reduce r).decode = p.decode.reduce r.decode := by
  apply congrArg₂ Gaussian.Row.mk
  · funext i
    simp [Row.decode,Row.reduce,List.getElem_zipWith,Row.head_decode]
  · simp [Row.decode,Row.reduce,Row.head_decode]

@[simp] theorem pivot_decode {n} (rows : List (Row (n+1))) :
    Gaussian.pivot (rows.map Row.decode) = (pivot rows).map Row.decode := by
  simp only [Gaussian.pivot,pivot,List.find?_map]
  congr 2
  funext r
  simp []

def payload {n} (rows : List (Row n)) : List (Option Scalar) :=
  rows.flatMap (fun r => r.coeff.map some ++ [some r.rhs,none])

theorem payload_length {n} (rows : List (Row n)) :
    (payload rows).length = rows.length*(n+2) := by
  induction rows with
  | nil => simp [payload]
  | cons r rs ih =>
    simp only [payload,List.flatMap_cons,List.length_append,List.length_map,
      r.length_eq,List.length_cons,List.length_nil] at *
    rw [Nat.add_mul]
    omega

def queryRows {N} (S : OrderedQuery.Data N) : List (Row (N+N)) :=
  (OrderedQuery.rows S).map Row.encode

end CPTSeparation.SerialGaussian

namespace CPTSeparation.OrderedQuery

def symbolIndex : Symbol → Fin 8
  | .Ed => 0 | .Cf => 1 | .EB => 2 | .VB => 3 | .I => 4
  | .Z δ => ⟨5+δ.val,by have := δ.val_lt; omega⟩

@[simp] theorem indexSymbol_symbolIndex (r : Symbol) : indexSymbol (symbolIndex r) = r := by
  cases r with
  | Ed => decide
  | Cf => decide
  | EB => decide
  | VB => decide
  | I => decide
  | Z δ => fin_cases δ <;> decide

@[simp] theorem symbolIndex_indexSymbol (i : Fin 8) : symbolIndex (indexSymbol i) = i := by
  fin_cases i <;> decide

variable {N : ℕ}

def cellIndex (r : Symbol) (a b : Fin N) : Fin (8*(N*N)) :=
  finProdFinEquiv (symbolIndex r,finProdFinEquiv (a,b))

@[simp] theorem cellValue_index (S : Data N) (r : Symbol) (a b : Fin N) :
    cellValue S (cellIndex r a b) = S.rel r a b := by
  simp [cellValue,cellIndex]

abbrev Alphabet := Option Bool

def encode (S : OrderedInput) : List Alphabet :=
  List.replicate S.1 none ++ some false :: (tableBits S.2).map some

@[simp] theorem tableBits_length (S : Data N) : (tableBits S).length = 8*(N*N) := by
  simp [tableBits]

@[simp] theorem encode_size (S : OrderedInput) : (encode S).count none = S.1 := by
  simp only [encode,List.count_append,List.count_replicate,List.count_cons]
  have h : List.count none ((tableBits S.2).map some) = 0 :=
    List.count_eq_zero_of_not_mem (by simp)
  simp [h]

@[simp] theorem encode_length (S : OrderedInput) :
    (encode S).length = S.1+1+8*(S.1*S.1) := by simp [encode]; omega

def answer (S : OrderedInput) : Bool := decideQuery S.2

end CPTSeparation.OrderedQuery

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Stack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation.StackLang

section

open Turing StateTransition

variable {K : Type} {Γ : K → Type} {σ : Type}

structure Store (Γ : K → Type) (σ : Type) where
  control : σ
  stk : ∀ k, List (Γ k)

inductive Action (Γ : K → Type) (σ : Type) where
  | done
  | push (k : K) (value : σ → Γ k) (next : Action Γ σ)
  | peek (k : K) (update : σ → Option (Γ k) → σ) (next : Action Γ σ)
  | pop (k : K) (update : σ → Option (Γ k) → σ) (next : Action Γ σ)
  | load (update : σ → σ) (next : Action Γ σ)
  | branch (test : σ → Bool) (yes no : Action Γ σ)

namespace Action

variable [DecidableEq K]

def run : Action Γ σ → Store Γ σ → Store Γ σ
  | .done, s => s
  | .push k f a, s => run a ⟨s.control, Function.update s.stk k (f s.control :: s.stk k)⟩
  | .peek k f a, s => run a ⟨f s.control (s.stk k).head?, s.stk⟩
  | .pop k f a, s => run a ⟨f s.control (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
  | .load f a, s => run a ⟨f s.control, s.stk⟩
  | .branch f a b, s => if f s.control then run a s else run b s

def stmt {Λ : Type} (exit : TM2.Stmt Γ Λ σ) : Action Γ σ → TM2.Stmt Γ Λ σ
  | .done => exit
  | .push k f a => .push k f (stmt exit a)
  | .peek k f a => .peek k f (stmt exit a)
  | .pop k f a => .pop k f (stmt exit a)
  | .load f a => .load f (stmt exit a)
  | .branch f a b => .branch f (stmt exit a) (stmt exit b)

lemma stmt_run {Λ : Type} (exit : TM2.Stmt Γ Λ σ) (a : Action Γ σ) (s : Store Γ σ) :
    TM2.stepAux (a.stmt exit) s.control s.stk =
      TM2.stepAux exit (a.run s).control (a.run s).stk := by
  induction a generalizing s with
  | done => rfl
  | push k f a ih => exact ih ⟨s.control, Function.update s.stk k (f s.control :: s.stk k)⟩
  | peek k f a ih => exact ih ⟨f s.control (s.stk k).head?, s.stk⟩
  | pop k f a ih => exact ih ⟨f s.control (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
  | load f a ih => exact ih ⟨f s.control, s.stk⟩
  | branch f a b iha ihb =>
      cases hf : f s.control <;> simp [stmt, run, TM2.stepAux, hf, iha, ihb]

end Action

inductive Program (Γ : K → Type) (σ : Type) where
  | atom (a : Action Γ σ)
  | seq (a b : Program Γ σ)
  | cond (test : σ → Bool) (a b : Program Γ σ)
  | loop (test : σ → Bool) (body : Program Γ σ)

inductive Exec [DecidableEq K] : Program Γ σ → Store Γ σ → ℕ → Store Γ σ → Type
  | atom (a) (s) : Exec (.atom a) s 1 (a.run s)
  | seq {a b s t u n m} : Exec a s n t → Exec b t m u → Exec (.seq a b) s (1+(n+m)) u
  | cond_true {f a b s t n} : f s.control = true → Exec a s n t → Exec (.cond f a b) s (1+n) t
  | cond_false {f a b s t n} : f s.control = false → Exec b s n t → Exec (.cond f a b) s (1+n) t
  | loop_false {f body s} : f s.control = false → Exec (.loop f body) s 1 s
  | loop_true {f body s t u n m} : f s.control = true → Exec body s n t → Exec (.loop f body) t m u →
      Exec (.loop f body) s (1+(n+m)) u

namespace Program

def Labels : Program Γ σ → Type
  | .atom _ => Unit
  | .seq a b => Unit ⊕ (Labels a ⊕ Labels b)
  | .cond _ a b => Unit ⊕ (Labels a ⊕ Labels b)
  | .loop _ a => Unit ⊕ Labels a

noncomputable instance finiteLabels (p : Program Γ σ) : Fintype p.Labels := by
  induction p with
  | atom a => change Fintype Unit; infer_instance
  | seq a b iha ihb => change Fintype (Unit ⊕ (a.Labels ⊕ b.Labels)); letI := iha; letI := ihb; infer_instance
  | cond f a b iha ihb => change Fintype (Unit ⊕ (a.Labels ⊕ b.Labels)); letI := iha; letI := ihb; infer_instance
  | loop f a ih => change Fintype (Unit ⊕ a.Labels); letI := ih; infer_instance

def start : (p : Program Γ σ) → p.Labels
  | .atom _ => ()
  | .seq _ _ => .inl ()
  | .cond _ _ _ => .inl ()
  | .loop _ _ => .inl ()

def jump {Λ : Type} : Option Λ → TM2.Stmt Γ Λ σ
  | none => .halt
  | some l => .goto (fun _ => l)

@[simp] lemma stepAux_jump [DecidableEq K] {Λ : Type} (l : Option Λ) (v : σ) (s : ∀ k, List (Γ k)) :
    TM2.stepAux (jump l) v s = ⟨l,v,s⟩ := by cases l <;> rfl

def code {Λ : Type} : (p : Program Γ σ) → (p.Labels → Λ) → Option Λ → p.Labels → TM2.Stmt Γ Λ σ
  | .atom a, _, exit, _ => a.stmt (jump exit)
  | .seq a _, embed, _, .inl _ => .goto (fun _ => embed (.inr (.inl a.start)))
  | .seq a b, embed, _, .inr (.inl l) =>
      code a (fun x => embed (.inr (.inl x))) (some (embed (.inr (.inr b.start)))) l
  | .seq _ b, embed, exit, .inr (.inr l) =>
      code b (fun x => embed (.inr (.inr x))) exit l
  | .cond f a b, embed, _, .inl _ => .branch f
      (.goto (fun _ => embed (.inr (.inl a.start)))) (.goto (fun _ => embed (.inr (.inr b.start))))
  | .cond _ a _, embed, exit, .inr (.inl l) =>
      code a (fun x => embed (.inr (.inl x))) exit l
  | .cond _ _ b, embed, exit, .inr (.inr l) =>
      code b (fun x => embed (.inr (.inr x))) exit l
  | .loop f a, embed, exit, .inl _ => .branch f
      (.goto (fun _ => embed (.inr a.start))) (jump exit)
  | .loop _ a, embed, _, .inr l =>
      code a (fun x => embed (.inr x)) (some (embed (.inl ()))) l

end Program

variable [DecidableEq K]

def configuration {Λ : Type} (label : Option Λ) (s : Store Γ σ) : TM2.Cfg Γ Λ σ :=
  ⟨label,s.control,s.stk⟩

def one_step {Λ : Type} {M : Λ → TM2.Stmt Γ Λ σ} {s t : TM2.Cfg Γ Λ σ}
    (h : TM2.step M s = some t) : EvalsToInTime (TM2.step M) s (some t) 1 := ⟨⟨1,h⟩,le_rfl⟩

noncomputable def Exec.simulates {p : Program Γ σ} {s t : Store Γ σ} {n : ℕ} (h : Exec p s n t)
    {Λ : Type} (M : Λ → TM2.Stmt Γ Λ σ) (embed : p.Labels → Λ) (exit : Option Λ)
    (hc : ∀ l, M (embed l) = p.code embed exit l) :
    EvalsToInTime (TM2.step M) (configuration (some (embed p.start)) s) (some (configuration exit t)) n := by
  induction h generalizing Λ with
  | atom a s =>
      apply one_step
      simp only [configuration, TM2.step, hc, Program.code, Action.stmt_run, Program.stepAux_jump]
  | @seq a b s t u n m ha hb iha ihb =>
      have h₀ : TM2.step M (configuration (some (embed (Program.seq a b).start)) s) =
          some (configuration (some (embed (.inr (.inl a.start)))) s) := by
        simp only [configuration, TM2.step]; rw [hc]; simp [Program.start, Program.code]
      have h₁ := iha M (fun x => embed (.inr (.inl x))) (some (embed (.inr (.inr b.start))))
        (fun l => hc (.inr (.inl l)))
      have h₂ := ihb M (fun x => embed (.inr (.inr x))) exit (fun l => hc (.inr (.inr l)))
      simpa only [Nat.add_comm] using EvalsToInTime.trans (TM2.step M) 1 (m+n) _ _ _
        (one_step h₀) (EvalsToInTime.trans (TM2.step M) n m _ _ _ h₁ h₂)
  | @cond_true f a b s t n hf ha ih =>
      have h₀ : TM2.step M (configuration (some (embed (Program.cond f a b).start)) s) =
          some (configuration (some (embed (.inr (.inl a.start)))) s) := by
        simp only [configuration, TM2.step]; rw [hc]; simp [Program.start, Program.code, hf]
      have h₁ := ih M (fun x => embed (.inr (.inl x))) exit (fun l => hc (.inr (.inl l)))
      simpa only [Nat.add_comm] using EvalsToInTime.trans (TM2.step M) 1 n _ _ _ (one_step h₀) h₁
  | @cond_false f a b s t n hf hb ih =>
      have h₀ : TM2.step M (configuration (some (embed (Program.cond f a b).start)) s) =
          some (configuration (some (embed (.inr (.inr b.start)))) s) := by
        simp only [configuration, TM2.step]; rw [hc]; simp [Program.start, Program.code, hf]
      have h₁ := ih M (fun x => embed (.inr (.inr x))) exit (fun l => hc (.inr (.inr l)))
      simpa only [Nat.add_comm] using EvalsToInTime.trans (TM2.step M) 1 n _ _ _ (one_step h₀) h₁
  | @loop_false f body s hf =>
      apply one_step
      simp only [configuration, TM2.step]; rw [hc]; simp [Program.start, Program.code, hf]
  | @loop_true f body s t u n m hf ha hb iha ihb =>
      have h₀ : TM2.step M (configuration (some (embed (Program.loop f body).start)) s) =
          some (configuration (some (embed (.inr body.start))) s) := by
        simp only [configuration, TM2.step]; rw [hc]; simp [Program.start, Program.code, hf]
      have h₁ := iha M (fun x => embed (.inr x)) (some (embed (.inl ()))) (fun l => hc (.inr l))
      have h₂ := ihb M embed exit hc
      simpa only [Program.start, Nat.add_comm] using EvalsToInTime.trans (TM2.step M) 1 (m+n) _ _ _
        (one_step h₀) (EvalsToInTime.trans (TM2.step M) n m _ _ _ h₁ h₂)

namespace Program

variable [Fintype K] [Fintype σ] [∀ k, Fintype (Γ k)]

noncomputable def machine (p : Program Γ σ) (input output : K) (initial : σ) : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ := Γ
  Λ := p.Labels
  main := p.start
  σ := σ
  initialState := initial
  m := p.code id none

instance machine_alphabet_finite (p : Program Γ σ) (input output : K) (initial : σ)
    (k : K) : Fintype ((p.machine input output initial).Γ k) :=
  ‹∀ k, Fintype (Γ k)› k

noncomputable def compiles {p : Program Γ σ} {s t : Store Γ σ} {n : ℕ} (h : Exec p s n t)
    (input output : K) (initial : σ) :
    EvalsToInTime (p.machine input output initial).step
      (configuration (some p.start) s) (some (configuration none t)) n :=
  h.simulates (p.code id none) id none (fun _ => rfl)

end Program

end

variable {K α σ : Type} {Γ : K → Type} [decidableK : DecidableEq K]

abbrev SStore (K α σ : Type) := Store (fun _ : K => α) (Option α × σ)

abbrev SProgram (K α σ : Type) := Program (fun _ : K => α) (Option α × σ)

def Runs (p : Program Γ σ) (s t : Store Γ σ) (n : ℕ) : Prop :=
  ∃ m ≤ n, Nonempty (Exec p s m t)

namespace Runs

lemma atom (a : Action Γ σ) (s : Store Γ σ) : Runs (.atom a) s (a.run s) 1 :=
  ⟨1,le_rfl,⟨.atom a s⟩⟩

lemma atom_of (a : Action Γ σ) (s t : Store Γ σ) (h : a.run s = t) : Runs (.atom a) s t 1 :=
  h ▸ atom a s

lemma mono {p : Program Γ σ} {s t : Store Γ σ} {m n : ℕ}
    (h : Runs p s t m) (hn : m ≤ n) : Runs p s t n := by
  rcases h with ⟨a,ha,⟨h⟩⟩
  exact ⟨a,ha.trans hn,⟨h⟩⟩

lemma seq {a b : Program Γ σ} {s t u : Store Γ σ} {m n : ℕ}
    (ha : Runs a s t m) (hb : Runs b t u n) : Runs (.seq a b) s u (1+(m+n)) := by
  rcases ha with ⟨ma,hma,⟨ha⟩⟩
  rcases hb with ⟨nb,hnb,⟨hb⟩⟩
  exact ⟨1+(ma+nb),by omega,⟨.seq ha hb⟩⟩

lemma loop_false {f : σ → Bool} {b : Program Γ σ} {s : Store Γ σ}
    (h : f s.control = false) : Runs (.loop f b) s s 1 := ⟨1,le_rfl,⟨.loop_false h⟩⟩

lemma loop_true {f : σ → Bool} {b : Program Γ σ} {s t u : Store Γ σ} {m n : ℕ}
    (h : f s.control = true) (ha : Runs b s t m) (hb : Runs (.loop f b) t u n) :
    Runs (.loop f b) s u (1+(m+n)) := by
  rcases ha with ⟨ma,hma,⟨ha⟩⟩
  rcases hb with ⟨nb,hnb,⟨hb⟩⟩
  exact ⟨1+(ma+nb),by omega,⟨.loop_true h ha hb⟩⟩

lemma cond_true {f : σ → Bool} {a b : Program Γ σ} {s t : Store Γ σ} {n : ℕ}
    (hf : f s.control = true) (h : Runs a s t n) : Runs (.cond f a b) s t (1+n) := by
  rcases h with ⟨m,hm,⟨h⟩⟩
  exact ⟨1+m,by omega,⟨.cond_true hf h⟩⟩

lemma cond_false {f : σ → Bool} {a b : Program Γ σ} {s t : Store Γ σ} {n : ℕ}
    (hf : f s.control = false) (h : Runs b s t n) : Runs (.cond f a b) s t (1+n) := by
  rcases h with ⟨m,hm,⟨h⟩⟩
  exact ⟨1+m,by omega,⟨.cond_false hf h⟩⟩

end Runs

namespace Store

omit K σ Γ in
@[ext] lemma ext'
    {K : Type}
    {σ : Type}
    {Γ : K → Type}
    [DecidableEq K] {s t : Store Γ σ} (h : s.control = t.control) (g : s.stk = t.stk) : s = t := by
  cases s; cases t; simp_all

end Store

namespace Macros

variable [inhabitedα : Inhabited α]

def state (v : σ) (buf : Option α) (w : K → List α) : SStore K α σ := ⟨(buf,v),w⟩

def peek (i : K) : SProgram K α σ := .atom (.peek i (fun c a => (a,c.2)) .done)

def moveBody (i j : K) (f : σ → α → α) : SProgram K α σ :=
 .atom (.pop i (fun c _ => c) (.push j (fun c => f c.2 (c.1.getD default))
   (.peek i (fun c a => (a,c.2)) .done)))

def moveLoop (i j : K) (f : σ → α → α) : SProgram K α σ :=
 .loop (fun c => c.1.isSome) (moveBody i j f)

def moveRev (i j : K) (f : σ → α → α) : SProgram K α σ :=
 .seq (peek i) (moveLoop i j f)

lemma moveLoop_runs (i j : K) (hij : i ≠ j) (f : σ → α → α) (v : σ)
    (w : K → List α) (xs ys : List α) :
    Runs (moveLoop i j f)
      (state v xs.head? (Function.update (Function.update w i xs) j ys))
      (state v none (Function.update (Function.update w i []) j ((xs.map (f v)).reverse ++ ys)))
      (2*xs.length+1) := by
  induction xs generalizing ys with
  | nil =>
      simpa only [moveLoop,List.head?_nil,List.map_nil,List.reverse_nil,List.nil_append,List.length_nil,
        Nat.mul_zero,Nat.zero_add] using
        Runs.loop_false (b := moveBody i j f) (f := fun c => c.1.isSome)
          (s := state v none (Function.update (Function.update w i []) j ys)) rfl
  | cons a xs ih =>
      have hbody : Runs (moveBody i j f)
          (state v (some a) (Function.update (Function.update w i (a::xs)) j ys))
          (state v xs.head? (Function.update (Function.update w i xs) j (f v a :: ys))) 1 := by
        unfold moveBody
        apply Runs.atom_of
        apply Store.ext'
        · simp [Action.run, state, Function.update, hij, Ne.symm hij]
        · simp only [Action.run, state, Option.getD_some]
          funext k
          by_cases hki : k = i
          · subst k; simp [Function.update, hij]
          · by_cases hkj : k = j
            · subst k; simp [Function.update, Ne.symm hij]
            · simp [Function.update, hki,hkj]
      have h := Runs.loop_true (f := fun c : Option α × σ => c.1.isSome) rfl
        hbody (ih (f v a :: ys))
      convert h using 1 <;> simp [moveLoop,List.map_cons,List.reverse_cons,List.append_assoc] ; omega

lemma moveRev_runs (i j : K) (hij : i ≠ j) (f : σ → α → α) (v : σ) (buf : Option α)
    (w : K → List α) (xs ys : List α) :
    Runs (moveRev i j f)
      (state v buf (Function.update (Function.update w i xs) j ys))
      (state v none (Function.update (Function.update w i []) j ((xs.map (f v)).reverse ++ ys)))
      (2*xs.length+3) := by
  have hp : Runs (peek i)
      (state v buf (Function.update (Function.update w i xs) j ys))
      (state v xs.head? (Function.update (Function.update w i xs) j ys)) 1 := by
    unfold peek
    apply Runs.atom_of
    simp [Action.run, state, Function.update, hij]
  convert hp.seq (moveLoop_runs i j hij f v w xs ys) using 1 <;> first | rfl | omega

def clearBody (i : K) : SProgram K α σ :=
  .atom (.pop i (fun c _ => c) (.peek i (fun c a => (a,c.2)) .done))

def clearLoop (i : K) : SProgram K α σ := .loop (fun c => c.1.isSome) (clearBody i)

def clear (i : K) : SProgram K α σ := .seq (peek i) (clearLoop i)

omit K α σ in
lemma clearLoop_runs
    {K : Type}
    {α : Type}
    {σ : Type}
    [DecidableEq K]
    [Inhabited α] (i : K) (v : σ) (w : K → List α) (xs : List α) :
    Runs (clearLoop i) (state v xs.head? (Function.update w i xs))
      (state v none (Function.update w i [])) (2*xs.length+1) := by
  induction xs with
  | nil => exact Runs.loop_false rfl
  | cons a xs ih =>
      have hb : Runs (clearBody i) (state v (some a) (Function.update w i (a::xs)))
          (state v xs.head? (Function.update w i xs)) 1 := by
        apply Runs.atom_of
        simp [Action.run,state]
      have h := Runs.loop_true (f := fun c : Option α × σ => c.1.isSome) rfl hb ih
      convert h using 1 <;> first | rfl | simp only [List.length_cons]; omega

omit K α σ in
lemma clear_runs
    {K : Type}
    {α : Type}
    {σ : Type}
    [DecidableEq K]
    [Inhabited α] (i : K) (v : σ) (buf : Option α) (w : K → List α) (xs : List α) :
    Runs (clear i) (state v buf (Function.update w i xs))
      (state v none (Function.update w i [])) (2*xs.length+3) := by
  have hb : Runs (peek i) (state v buf (Function.update w i xs))
      (state v xs.head? (Function.update w i xs)) 1 := by
    apply Runs.atom_of
    simp [Action.run,state]
  convert hb.seq (clearLoop_runs i v w xs) using 1 <;> first | rfl | omega

def dupeBody (i j k : K) : SProgram K α σ :=
 .atom (.pop i (fun c _ => c) (.push j (fun c => c.1.getD default)
   (.push k (fun c => c.1.getD default) (.peek i (fun c a => (a,c.2)) .done))))

def dupeLoop (i j k : K) : SProgram K α σ :=
 .loop (fun c => c.1.isSome) (dupeBody i j k)

def dupeRev (i j k : K) : SProgram K α σ := .seq (peek i) (dupeLoop i j k)

lemma dupeLoop_runs (i j k : K) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : σ) (w : K → List α) (xs ys zs : List α) :
    Runs (dupeLoop i j k)
      (state v xs.head? (Function.update (Function.update (Function.update w i xs) j ys) k zs))
      (state v none (Function.update (Function.update (Function.update w i []) j (xs.reverse ++ ys))
        k (xs.reverse ++ zs))) (2*xs.length+1) := by
  induction xs generalizing ys zs with
  | nil => simpa only [dupeLoop,List.head?_nil,List.reverse_nil,List.nil_append,List.length_nil,
        Nat.mul_zero,Nat.zero_add] using
        (Runs.loop_false (f := fun c : Option α × σ => c.1.isSome) (b := dupeBody i j k)
          (s := state v none (Function.update (Function.update (Function.update w i []) j ys) k zs)) rfl)
  | cons a xs ih =>
      have hb : Runs (dupeBody i j k)
          (state v (some a) (Function.update (Function.update (Function.update w i (a::xs)) j ys) k zs))
          (state v xs.head? (Function.update (Function.update (Function.update w i xs) j (a::ys)) k (a::zs))) 1 := by
        apply Runs.atom_of
        apply Store.ext'
        · simp [Action.run,state,Function.update,hij,hik,Ne.symm hij,Ne.symm hik]
        · simp only [Action.run,state,Option.getD_some]
          funext l
          by_cases hi : l = i
          · subst l; simp [Function.update,hij,hik,]
          · by_cases hj : l = j
            · subst l; simp [Function.update,hjk,Ne.symm hij,]
            · by_cases hk : l = k
              · subst l; simp [Function.update,Ne.symm hik,Ne.symm hjk]
              · simp [Function.update,hi,hj,hk]
      have h := Runs.loop_true (f := fun c : Option α × σ => c.1.isSome) rfl hb
        (ih (a::ys) (a::zs))
      convert h using 1 <;> first | rfl | (simp [List.reverse_cons,List.append_assoc] <;> omega)

lemma dupeRev_runs (i j k : K) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : σ) (buf : Option α) (w : K → List α) (xs ys zs : List α) :
    Runs (dupeRev i j k)
      (state v buf (Function.update (Function.update (Function.update w i xs) j ys) k zs))
      (state v none (Function.update (Function.update (Function.update w i []) j (xs.reverse ++ ys))
        k (xs.reverse ++ zs))) (2*xs.length+3) := by
  have hp : Runs (peek i)
      (state v buf (Function.update (Function.update (Function.update w i xs) j ys) k zs))
      (state v xs.head? (Function.update (Function.update (Function.update w i xs) j ys) k zs)) 1 := by
    apply Runs.atom_of
    simp [Action.run,state,Function.update,hij,hik]
  convert hp.seq (dupeLoop_runs i j k hij hik hjk v w xs ys zs) using 1 <;> first | rfl | omega

def copy (i j scratch : K) : SProgram K α σ :=
 .seq (moveRev i scratch (fun _ a => a)) (dupeRev scratch i j)

lemma copy_runs (i j k : K) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : σ) (buf : Option α) (w : K → List α) (xs ys : List α) :
    Runs (copy i j k)
      (state v buf (Function.update (Function.update (Function.update w k []) i xs) j ys))
      (state v none (Function.update (Function.update (Function.update w k []) i xs) j (xs ++ ys)))
      (4*xs.length+7) := by
  have hm := moveRev_runs i k hik (fun (_ : σ) a => a) v buf (Function.update w j ys) xs []
  have hd := dupeRev_runs k i j (Ne.symm hik) (Ne.symm hjk) hij v none w xs.reverse [] ys
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at hm hd
  have hm' : Runs (moveRev i k (fun (_ : σ) a => a))
      (state v buf (Function.update (Function.update (Function.update w k []) i xs) j ys))
      (state v none (Function.update (Function.update (Function.update w k xs.reverse) i []) j ys))
      (2*xs.length+3) := by
    convert hm using 1 <;> congr 1 <;> funext l <;>
      by_cases hi : l = i <;> by_cases hj : l = j <;> by_cases hk : l = k <;>
      simp_all [Function.update]
  convert hm'.seq hd using 1 <;> first | rfl | omega

end Macros

end CPTSeparation.StackLang

namespace CPTSeparation.StackLang.Macros

section

variable {K α σ : Type} [DecidableEq K] [inhabitedα : Inhabited α]

def rowLoop (i j : K) (f : σ → Option α → Option α) : SProgram K (Option α) σ :=
  .loop (fun c => (c.1.bind id).isSome) (moveBody i j f)

def moveRow (i j : K) (f : σ → Option α → Option α) : SProgram K (Option α) σ :=
 .seq (peek i) (.seq (rowLoop i j f) (.atom (.pop i (fun c _ => (none,c.2)) .done)))

omit K α σ in
lemma rowLoop_runs
    {K : Type}
    {α : Type}
    {σ : Type}
    [DecidableEq K]
    [Inhabited α] (i j : K) (hij : i ≠ j) (f : σ → Option α → Option α) (v : σ)
    (w : K → List (Option α)) (xs : List α) (suffix ys : List (Option α)) :
    Runs (rowLoop i j f)
      (state v (xs.map some ++ none::suffix).head?
        (Function.update (Function.update w i (xs.map some ++ none::suffix)) j ys))
      (state v (some none) (Function.update (Function.update w i (none::suffix))
        j ((xs.map (fun x => f v (some x))).reverse ++ ys))) (2*xs.length+1) := by
  induction xs generalizing ys with
  | nil =>
      simpa only [rowLoop,List.map_nil,List.nil_append,List.head?_cons,List.reverse_nil,
        List.length_nil,Nat.mul_zero,Nat.zero_add] using
        (Runs.loop_false (f := fun c : Option (Option α) × σ => (c.1.bind id).isSome)
          (b := moveBody i j f)
          (s := state v (some none) (Function.update (Function.update w i (none::suffix)) j ys)) rfl)
  | cons a xs ih =>
      have hb : Runs (moveBody i j f)
          (state v (some (some a)) (Function.update
            (Function.update w i (some a :: (xs.map some ++ none::suffix))) j ys))
          (state v (xs.map some ++ none::suffix).head? (Function.update
            (Function.update w i (xs.map some ++ none::suffix)) j (f v (some a)::ys))) 1 := by
        apply Runs.atom_of
        apply Store.ext'
        · simp [Action.run,state,Function.update,hij,Ne.symm hij]
        · simp only [Action.run,state,Option.getD_some]
          funext k
          by_cases hi : k = i
          · subst k; simp [Function.update,hij]
          · by_cases hj : k = j
            · subst k; simp [Function.update,Ne.symm hij]
            · simp [Function.update,hi,hj]
      have h := Runs.loop_true (f := fun c : Option (Option α) × σ => (c.1.bind id).isSome)
        rfl hb (ih (f v (some a)::ys))
      convert h using 1 <;> first | rfl | (simp [List.map_cons,List.reverse_cons,List.append_assoc] <;> omega)

omit K α σ in
lemma moveRow_runs
    {K : Type}
    {α : Type}
    {σ : Type}
    [DecidableEq K]
    [Inhabited α] (i j : K) (hij : i ≠ j) (f : σ → Option α → Option α) (v : σ)
    (buf : Option (Option α)) (w : K → List (Option α)) (xs : List α)
    (suffix ys : List (Option α)) :
    Runs (moveRow i j f)
      (state v buf (Function.update (Function.update w i (xs.map some ++ none::suffix)) j ys))
      (state v none (Function.update (Function.update w i suffix)
        j ((xs.map (fun x => f v (some x))).reverse ++ ys))) (2*xs.length+5) := by
  have hp : Runs (peek i)
      (state v buf (Function.update (Function.update w i (xs.map some ++ none::suffix)) j ys))
      (state v (xs.map some ++ none::suffix).head?
        (Function.update (Function.update w i (xs.map some ++ none::suffix)) j ys)) 1 := by
    apply Runs.atom_of
    simp [Action.run,state,Function.update,hij]
  have hf : Runs (.atom (.pop i (fun (c : Option (Option α) × σ) _ => (none,c.2)) .done))
      (state v (some none) (Function.update (Function.update w i (none::suffix))
        j ((xs.map (fun x => f v (some x))).reverse ++ ys)))
      (state v none (Function.update (Function.update w i suffix)
        j ((xs.map (fun x => f v (some x))).reverse ++ ys))) 1 := by
    apply Runs.atom_of
    apply Store.ext'
    · rfl
    · funext k
      by_cases hi : k = i
      · subst k; simp [Action.run,state,Function.update,hij]
      · simp [Action.run,state,Function.update,hi]
  convert hp.seq ((rowLoop_runs i j hij f v w xs suffix ys).seq hf) using 1 <;> first | rfl | omega

def skipRowLoop (i : K) : SProgram K (Option α) σ :=
  .loop (fun c => (c.1.bind id).isSome) (clearBody i)

def skipRow (i : K) : SProgram K (Option α) σ :=
  .seq (peek i) (.seq (skipRowLoop i) (.atom (.pop i (fun c _ => (none,c.2)) .done)))

omit K α σ in
lemma skipRowLoop_runs
    {K : Type}
    {α : Type}
    {σ : Type}
    [DecidableEq K]
    [Inhabited α] (i : K) (v : σ) (w : K → List (Option α)) (xs : List α)
    (suffix : List (Option α)) :
    Runs (skipRowLoop i)
      (state v (xs.map some ++ none::suffix).head?
        (Function.update w i (xs.map some ++ none::suffix)))
      (state v (some none) (Function.update w i (none::suffix))) (2*xs.length+1) := by
  induction xs with
  | nil => exact Runs.loop_false rfl
  | cons a xs ih =>
      have hb : Runs (clearBody i)
          (state v (some (some a)) (Function.update w i (some a :: (xs.map some ++ none::suffix))))
          (state v (xs.map some ++ none::suffix).head?
            (Function.update w i (xs.map some ++ none::suffix))) 1 := by
        apply Runs.atom_of
        simp [Action.run,state]
      have h := Runs.loop_true (f := fun c : Option (Option α) × σ => (c.1.bind id).isSome) rfl hb ih
      convert h using 1 <;> first | rfl | (simp only [List.length_cons]; omega)

omit K α σ in
lemma skipRow_runs
    {K : Type}
    {α : Type}
    {σ : Type}
    [DecidableEq K]
    [Inhabited α] (i : K) (v : σ) (buf : Option (Option α))
    (w : K → List (Option α)) (xs : List α) (suffix : List (Option α)) :
    Runs (skipRow i) (state v buf (Function.update w i (xs.map some ++ none::suffix)))
      (state v none (Function.update w i suffix)) (2*xs.length+5) := by
  have hp : Runs (peek i) (state v buf (Function.update w i (xs.map some ++ none::suffix)))
      (state v (xs.map some ++ none::suffix).head? (Function.update w i (xs.map some ++ none::suffix))) 1 := by
    apply Runs.atom_of
    simp [Action.run,state]
  have hf : Runs (.atom (.pop i (fun (c : Option (Option α) × σ) _ => (none,c.2)) .done))
      (state v (some none) (Function.update w i (none::suffix)))
      (state v none (Function.update w i suffix)) 1 := by
    apply Runs.atom_of
    simp [Action.run,state]
  convert hp.seq ((skipRowLoop_runs i v w xs suffix).seq hf) using 1 <;> first | rfl | omega

end

variable {K α τ : Type} [DecidableEq K] [Inhabited α]

def zipRowBody (i o p b : K) (f : τ → α → α → α) :
    SProgram K (Option α) (Option α × τ) :=
 .atom (.pop i (fun c a => (a,c.2))
  (.pop p (fun c a => (c.1,(a.getD none,c.2.2)))
   (.push b (fun c => c.2.1)
    (.push o (fun c => some (f c.2.2 ((c.1.bind id).getD default) (c.2.1.getD default)))
     (.peek i (fun c a => (a,(none,c.2.2))) .done)))))

def zipRowLoop (i o p b : K) (f : τ → α → α → α) :
    SProgram K (Option α) (Option α × τ) :=
 .loop (fun c => (c.1.bind id).isSome) (zipRowBody i o p b f)

def zipRow (i o p b : K) (f : τ → α → α → α) :
    SProgram K (Option α) (Option α × τ) :=
 .seq (peek i) (.seq (zipRowLoop i o p b f)
   (.atom (.pop i (fun c _ => (none,c.2)) .done)))

lemma zipRowLoop_runs (i o p b : K) (hio : i ≠ o) (hip : i ≠ p) (hib : i ≠ b)
    (hop : o ≠ p) (hob : o ≠ b) (hpb : p ≠ b)
    (f : τ → α → α → α) (v : τ) (w : K → List (Option α))
    (xs ys : List α) (hlen : xs.length = ys.length)
    (suffix os bs : List (Option α)) :
    Runs (zipRowLoop i o p b f)
      (state ((none : Option α),v) (xs.map some ++ none::suffix).head?
        (Function.update (Function.update (Function.update (Function.update w i
          (xs.map some ++ none::suffix)) o os) p (ys.map some)) b bs))
      (state ((none : Option α),v) (some none)
        (Function.update (Function.update (Function.update (Function.update w i (none::suffix))
          o (((List.zipWith (f v) xs ys).map some).reverse ++ os)) p [])
          b ((ys.map some).reverse ++ bs))) (2*xs.length+1) := by
  induction xs generalizing ys os bs with
  | nil =>
      have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst ys
      simpa only [zipRowLoop,List.map_nil,List.nil_append,List.head?_cons,List.zipWith_nil_left,List.reverse_nil,
        List.length_nil,Nat.mul_zero,Nat.zero_add] using
        (Runs.loop_false (f := fun c : Option (Option α) × (Option α × τ) => (c.1.bind id).isSome)
          (b := zipRowBody i o p b f)
          (s := state ((none : Option α),v) (some none) (Function.update (Function.update
            (Function.update (Function.update w i (none::suffix)) o os) p []) b bs)) rfl)
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hlen' : xs.length = ys.length := by simpa using hlen
          have hb : Runs (zipRowBody i o p b f)
              (state ((none : Option α),v) (some (some a)) (Function.update (Function.update (Function.update
                (Function.update w i (some a :: (xs.map some ++ none::suffix))) o os)
                  p (some y :: ys.map some)) b bs))
              (state ((none : Option α),v) (xs.map some ++ none::suffix).head?
                (Function.update (Function.update (Function.update (Function.update w i
                  (xs.map some ++ none::suffix)) o (some (f v a y)::os)) p (ys.map some)) b (some y::bs))) 1 := by
            apply Runs.atom_of
            apply Store.ext'
            · simp [Action.run,state,Function.update,hio,hip,hib,hop,hob,hpb,
                Ne.symm hio,Ne.symm hip,Ne.symm hib,Ne.symm hpb]
            · simp only [Action.run,state]
              funext k
              by_cases hi : k = i <;> by_cases ho : k = o <;>
                by_cases hp : k = p <;> by_cases hb : k = b <;>
                simp_all [Function.update,Ne.symm hio,Ne.symm hip,Ne.symm hib,Ne.symm hop,Ne.symm hob,Ne.symm hpb]
          have h := Runs.loop_true (f := fun c : Option (Option α) × (Option α × τ) => (c.1.bind id).isSome)
            rfl hb (ih ys hlen' (some (f v a y)::os) (some y::bs))
          convert h using 1 <;> first | rfl |
            (simp [List.map_cons,List.reverse_cons,List.append_assoc] <;> omega)

lemma zipRow_runs (i o p b : K) (hio : i ≠ o) (hip : i ≠ p) (hib : i ≠ b)
    (hop : o ≠ p) (hob : o ≠ b) (hpb : p ≠ b)
    (f : τ → α → α → α) (v : τ) (buf : Option (Option α)) (w : K → List (Option α))
    (xs ys : List α) (hlen : xs.length = ys.length)
    (suffix os bs : List (Option α)) :
    Runs (zipRow i o p b f)
      (state ((none : Option α),v) buf
        (Function.update (Function.update (Function.update (Function.update w i
          (xs.map some ++ none::suffix)) o os) p (ys.map some)) b bs))
      (state ((none : Option α),v) none
        (Function.update (Function.update (Function.update (Function.update w i suffix)
          o (((List.zipWith (f v) xs ys).map some).reverse ++ os)) p [])
          b ((ys.map some).reverse ++ bs))) (2*xs.length+5) := by
  have hp : Runs (peek i)
      (state ((none : Option α),v) buf (Function.update (Function.update (Function.update (Function.update w i
          (xs.map some ++ none::suffix)) o os) p (ys.map some)) b bs))
      (state ((none : Option α),v) (xs.map some ++ none::suffix).head?
        (Function.update (Function.update (Function.update (Function.update w i
          (xs.map some ++ none::suffix)) o os) p (ys.map some)) b bs)) 1 := by
    apply Runs.atom_of
    simp [Action.run,state,Function.update,hio,hip,hib]
  have hf : Runs (.atom (.pop i (fun (c : Option (Option α) × (Option α × τ)) _ => (none,c.2)) .done))
      (state ((none : Option α),v) (some none)
        (Function.update (Function.update (Function.update (Function.update w i (none::suffix))
          o (((List.zipWith (f v) xs ys).map some).reverse ++ os)) p [])
          b ((ys.map some).reverse ++ bs)))
      (state ((none : Option α),v) none
        (Function.update (Function.update (Function.update (Function.update w i suffix)
          o (((List.zipWith (f v) xs ys).map some).reverse ++ os)) p [])
          b ((ys.map some).reverse ++ bs))) 1 := by
    apply Runs.atom_of
    apply Store.ext'
    · rfl
    · simp only [Action.run,state]
      funext k
      by_cases hi : k = i <;> by_cases ho : k = o <;>
        by_cases hp : k = p <;> by_cases hb : k = b <;>
        simp_all [Function.update,Ne.symm hio,Ne.symm hip,Ne.symm hib,Ne.symm hop,Ne.symm hob,Ne.symm hpb]
  convert hp.seq ((zipRowLoop_runs i o p b hio hip hib hop hob hpb f v w xs ys hlen suffix os bs).seq hf)
    using 1 <;> first | rfl | omega

end CPTSeparation.StackLang.Macros

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.GaussMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation.GaussMachine

open StackLang StackLang.Macros SerialGaussian

inductive Reg where
 | mat | back | scan | piv | pivBack | width | output
 deriving DecidableEq

instance instFintypeReg : Fintype Reg where
 elems := {.mat, .back, .scan, .piv, .pivBack, .width, .output}
 complete := by intro k; cases k <;> simp

structure Control where
  pivot : Scalar := 0
  factor : Scalar := 0
  answer : Bool := true
 deriving DecidableEq, Fintype

abbrev Local := Option Scalar × Control

abbrev Prog := SProgram Reg Letter Local

structure Data where
  mat : List Letter := []
  back : List Letter := []
  scan : List Letter := []
  piv : List Letter := []
  pivBack : List Letter := []
  width : List Letter := []
  output : List Letter := []
 deriving DecidableEq

def Data.tapes (d : Data) : Reg → List Letter
 | .mat => d.mat
 | .back => d.back
 | .scan => d.scan
 | .piv => d.piv
 | .pivBack => d.pivBack
 | .width => d.width
 | .output => d.output

@[simp] lemma tapes_mat (d : Data) (xs : List Letter) : Function.update d.tapes .mat xs = ({d with mat := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

@[simp] lemma tapes_back (d : Data) (xs : List Letter) : Function.update d.tapes .back xs = ({d with back := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

@[simp] lemma tapes_scan (d : Data) (xs : List Letter) : Function.update d.tapes .scan xs = ({d with scan := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

@[simp] lemma tapes_piv (d : Data) (xs : List Letter) : Function.update d.tapes .piv xs = ({d with piv := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

@[simp] lemma tapes_pivBack (d : Data) (xs : List Letter) : Function.update d.tapes .pivBack xs = ({d with pivBack := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

@[simp] lemma tapes_width (d : Data) (xs : List Letter) : Function.update d.tapes .width xs = ({d with width := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

@[simp] lemma tapes_output (d : Data) (xs : List Letter) : Function.update d.tapes .output xs = ({d with output := xs}).tapes := by funext k; cases k <;> simp [Data.tapes,Function.update]

def st (c : Control) (buf : Option Letter) (d : Data) : SStore Reg Letter Local := state (none,c) buf d.tapes

def _root_.OAI.CPTSeparation.SerialGaussian.Row.entries {n} (r : SerialGaussian.Row n) : List Scalar := r.coeff ++ [r.rhs]

@[simp] lemma entries_length {n} (r : SerialGaussian.Row n) : r.entries.length = n+1 := by simp [SerialGaussian.Row.entries,r.length_eq]

lemma payload_cons {n} (r : SerialGaussian.Row n) (rs) :
 payload (r::rs) = r.entries.map some ++ none::payload rs := by
 simp [payload,SerialGaussian.Row.entries,List.map_append,List.append_assoc]

lemma entries_head_tail {n} (r : SerialGaussian.Row (n+1)) :
 r.entries = r.head :: r.tail.entries := by
 rcases r with ⟨coeff,hl,rhs⟩
 cases coeff with
 | nil => simp at hl
 | cons a coeff => rfl

def scanBody : Prog :=
 .seq (.atom (.pop .scan (fun c a => (none,(none,{c.2.2 with factor := (a.bind id).getD 0}))) .done))
 (.seq (.cond (fun c => c.2.2.pivot == 0 && c.2.2.factor != 0)
    (.seq (.atom (.load (fun c => (c.1,(none,{c.2.2 with pivot := c.2.2.factor}))) .done))
      (moveRow .scan .pivBack (fun _ a => a)))
    (skipRow .scan))
  (.atom (.peek .scan (fun c a => (a,(none,{c.2.2 with factor := 0}))) .done)))

def scanLoop : Prog := .loop (fun c => c.1.isSome) scanBody

def scanMatrix : Prog := .seq (peek .scan) scanLoop

lemma scanBody_skip {n} (c : Control) (buf : Option Letter) (d : Data)
    (r : SerialGaussian.Row (n+1)) (rs : List (SerialGaussian.Row (n+1)))
    (h : c.pivot ≠ 0 ∨ r.head = 0) :
 Runs scanBody (st c buf {d with scan := payload (r::rs)})
   (st {c with factor := 0} (payload rs).head? {d with scan := payload rs})
   (2*(n+1)+10) := by
 let c' : Control := {c with factor := r.head}
 have hp : Runs (.atom (.pop .scan (fun (c : Option Letter × Local) a =>
       (none,(none,{c.2.2 with factor := (a.bind id).getD 0}))) .done))
     (st c buf {d with scan := payload (r::rs)})
     (st c' none {d with scan := r.tail.entries.map some ++ none::payload rs}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,payload_cons,entries_head_tail,c',Data.tapes]
 have hs := skipRow_runs (σ := Local) Reg.scan (none,c') none d.tapes
   r.tail.entries (payload rs)
 have hs' : Runs (skipRow Reg.scan)
      (st c' none {d with scan := r.tail.entries.map some ++ none::payload rs})
      (st c' none {d with scan := payload rs}) (2*(n+1)+5) := by
   simpa [st] using hs
 have hc := Runs.cond_false (a := .seq
    (.atom (.load (fun c : Option Letter × Local =>
      (c.1,(none,{c.2.2 with pivot := c.2.2.factor}))) .done))
    (moveRow Reg.scan Reg.pivBack (fun (_ : Local) a => a)))
    (f := fun c : Option Letter × Local => c.2.2.pivot == 0 && c.2.2.factor != 0)
    (s := st c' none {d with scan := r.tail.entries.map some ++ none::payload rs})
    (by rcases h with h | h <;> simp_all [st,state,c']) hs'
 have hf : Runs (.atom (.peek .scan (fun (c : Option Letter × Local) a =>
       (a,(none,{c.2.2 with factor := 0}))) .done))
     (st c' none {d with scan := payload rs})
     (st {c with factor := 0} (payload rs).head? {d with scan := payload rs}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,c',Data.tapes]
 convert hp.seq (hc.seq hf) using 1 <;> first | rfl | omega

def ctrl (p : Scalar) (a : Bool) : Control := ⟨p,0,a⟩

lemma payload_head {n} (r : SerialGaussian.Row (n+1)) (rs) :
 (payload (r::rs)).head? = some (some r.head) := by
 rw [payload_cons,entries_head_tail]
 rfl

lemma scanLoop_nonzero {n} (p : Scalar) (hp : p ≠ 0) (a : Bool) (d : Data)
    (rs : List (SerialGaussian.Row (n+1))) :
 Runs scanLoop (st (ctrl p a) (payload rs).head? {d with scan := payload rs})
   (st (ctrl p a) none {d with scan := []}) ((2*(n+1)+13)*rs.length+1) := by
 induction rs with
 | nil => exact Runs.loop_false rfl
 | cons r rs ih =>
   have hb := scanBody_skip (ctrl p a) (payload (r::rs)).head? d r rs (Or.inl hp)
   have h := Runs.loop_true (f := fun c : Option Letter × Local => c.1.isSome)
     (by simp [st,state,payload_head]) hb ih
   exact h.mono (by simp only [List.length_cons,Nat.mul_add,Nat.mul_one]; omega)

lemma scanBody_pick {n} (a : Bool) (buf : Option Letter) (d : Data)
    (r : SerialGaussian.Row (n+1)) (rs : List (SerialGaussian.Row (n+1))) (hr : r.head ≠ 0) :
 Runs scanBody (st (ctrl 0 a) buf {d with scan := payload (r::rs), pivBack := []})
   (st (ctrl r.head a) (payload rs).head?
     {d with scan := payload rs, pivBack := (r.tail.entries.map some).reverse})
   (2*(n+1)+12) := by
 let c' : Control := ⟨0,r.head,a⟩
 let c'' : Control := ⟨r.head,r.head,a⟩
 have hp : Runs (.atom (.pop .scan (fun (c : Option Letter × Local) a =>
       (none,(none,{c.2.2 with factor := (a.bind id).getD 0}))) .done))
     (st (ctrl 0 a) buf {d with scan := payload (r::rs),pivBack := []})
     (st c' none {d with scan := r.tail.entries.map some ++ none::payload rs,pivBack := []}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,payload_cons,entries_head_tail,c',ctrl,Data.tapes]
 have hl : Runs (.atom (.load (fun c : Option Letter × Local =>
       (c.1,(none,{c.2.2 with pivot := c.2.2.factor}))) .done))
     (st c' none {d with scan := r.tail.entries.map some ++ none::payload rs,pivBack := []})
     (st c'' none {d with scan := r.tail.entries.map some ++ none::payload rs,pivBack := []}) 1 := by
   exact Runs.atom_of _ _ _ rfl
 have hm := moveRow_runs Reg.scan Reg.pivBack (by decide) (fun (_ : Local) a => a)
   (none,c'') none d.tapes r.tail.entries (payload rs) []
 have hm' : Runs (moveRow Reg.scan Reg.pivBack (fun (_ : Local) a => a))
      (st c'' none {d with scan := r.tail.entries.map some ++ none::payload rs,pivBack := []})
      (st c'' none {d with scan := payload rs,pivBack := (r.tail.entries.map some).reverse})
      (2*(n+1)+5) := by simpa [st] using hm
 have hc := Runs.cond_true (b := skipRow Reg.scan)
    (f := fun c : Option Letter × Local => c.2.2.pivot == 0 && c.2.2.factor != 0)
    (s := st c' none {d with scan := r.tail.entries.map some ++ none::payload rs,pivBack := []})
    (by simpa [st,state,c'] using hr) (hl.seq hm')
 have hf : Runs (.atom (.peek .scan (fun (c : Option Letter × Local) a =>
       (a,(none,{c.2.2 with factor := 0}))) .done))
     (st c'' none {d with scan := payload rs,pivBack := (r.tail.entries.map some).reverse})
     (st (ctrl r.head a) (payload rs).head?
       {d with scan := payload rs,pivBack := (r.tail.entries.map some).reverse}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,c'',ctrl,Data.tapes]
 convert hp.seq (hc.seq hf) using 1 <;> first | rfl | omega

def pivotHead {n} (p : Option (SerialGaussian.Row (n+1))) : Scalar := p.elim 0 Row.head

def pivotTail {n} (p : Option (SerialGaussian.Row (n+1))) : List Letter :=
 p.elim [] (fun r => r.tail.entries.map some)

lemma scanLoop_initial {n} (a : Bool) (d : Data) (rs : List (SerialGaussian.Row (n+1))) :
 Runs scanLoop (st (ctrl 0 a) (payload rs).head? {d with scan := payload rs,pivBack := []})
   (st (ctrl (pivotHead (pivot rs)) a) none
      {d with scan := [],pivBack := (pivotTail (pivot rs)).reverse})
   ((2*(n+1)+13)*rs.length+1) := by
 induction rs with
 | nil => exact Runs.loop_false rfl
 | cons r rs ih =>
   by_cases hr : r.head = 0
   · have hb := scanBody_skip (ctrl 0 a) (payload (r::rs)).head? {d with pivBack := []} r rs (Or.inr hr)
     have h := Runs.loop_true (f := fun c : Option Letter × Local => c.1.isSome)
       (by simp [st,state,payload_head]) hb ih
     simpa [scanLoop,pivot,List.find?_cons,hr,← Row.head_decode,List.length_cons,Nat.mul_add,
       Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
       h.mono (show 1+(2*(n+1)+10+((2*(n+1)+13)*rs.length+1)) ≤
         (2*(n+1)+13)*(rs.length+1)+1 by simp only [Nat.mul_add,Nat.mul_one]; omega)
   · have hb := scanBody_pick a (payload (r::rs)).head? d r rs hr
     have ht := scanLoop_nonzero r.head hr a
       {d with pivBack := (r.tail.entries.map some).reverse} rs
     have h := Runs.loop_true (f := fun c : Option Letter × Local => c.1.isSome)
       (by simp [st,state,payload_head]) hb ht
     convert h using 1 <;>
       simp [scanLoop,pivot,hr,-Row.head_decode,pivotHead,pivotTail,List.length_cons]; ring

def findPivot : Prog :=
 .seq (.atom (.load (fun c => (c.1,(none,ctrl 0 c.2.2.answer))) .done))
 (.seq (copy .mat .scan .back)
  (.seq scanMatrix (moveRev .pivBack .piv (fun _ a => a))))

lemma pivotTail_length {n} (p : Option (SerialGaussian.Row (n+1))) :
 (pivotTail p).length ≤ n+1 := by
 cases p <;> simp [pivotTail]

lemma findPivot_runs {n} (c : Control) (buf : Option Letter) (d : Data)
    (rs : List (SerialGaussian.Row (n+1))) :
 Runs findPivot
   (st c buf {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := []})
   (st (ctrl (pivotHead (pivot rs)) c.answer) none
     {d with mat := payload rs,back := [],scan := [],piv := pivotTail (pivot rs),pivBack := []})
   (30*(rs.length+1)*(n+3)) := by
 let d' : Data := {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := []}
 have hl : Runs (.atom (.load (fun c : Option Letter × Local =>
       (c.1,(none,ctrl 0 c.2.2.answer))) .done))
     (st c buf d') (st (ctrl 0 c.answer) buf d') 1 := Runs.atom_of _ _ _ rfl
 have hc := copy_runs (σ := Local) Reg.mat Reg.scan Reg.back (by decide) (by decide) (by decide)
   (none,ctrl 0 c.answer) buf d'.tapes (payload rs) []
 have hc' : Runs (copy Reg.mat Reg.scan Reg.back) (st (ctrl 0 c.answer) buf d')
   (st (ctrl 0 c.answer) none {d' with scan := payload rs}) (4*(payload rs).length+7) := by
   simpa [st,d'] using hc
 have hp : Runs (peek Reg.scan) (st (ctrl 0 c.answer) none {d' with scan := payload rs})
   (st (ctrl 0 c.answer) (payload rs).head? {d' with scan := payload rs}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes]
 have hs := scanLoop_initial c.answer d' rs
 have hs' : Runs scanMatrix (st (ctrl 0 c.answer) none {d' with scan := payload rs})
   (st (ctrl (pivotHead (pivot rs)) c.answer) none
     {d' with scan := [],pivBack := (pivotTail (pivot rs)).reverse})
   ((2*(n+1)+13)*rs.length+3) := by
   convert hp.seq hs using 1 <;> first | rfl | omega
 have hm := moveRev_runs Reg.pivBack Reg.piv (by decide) (fun (_ : Local) a => a)
   (none,ctrl (pivotHead (pivot rs)) c.answer) none d'.tapes (pivotTail (pivot rs)).reverse []
 have hm' : Runs (moveRev Reg.pivBack Reg.piv (fun (_ : Local) a => a))
    (st (ctrl (pivotHead (pivot rs)) c.answer) none
      {d' with scan := [],pivBack := (pivotTail (pivot rs)).reverse})
    (st (ctrl (pivotHead (pivot rs)) c.answer) none {d' with piv := pivotTail (pivot rs)})
    (2*(pivotTail (pivot rs)).length+3) := by simpa [st,d'] using hm
 have h := hl.seq (hc'.seq (hs'.seq hm'))
 apply h.mono
 rw [payload_length]
 have ht := pivotTail_length (pivot rs)
 nlinarith

lemma entries_reduce {n} (p r : SerialGaussian.Row (n+1)) :
 (p.reduce r).entries = List.zipWith (fun x y => x-(r.head/p.head)*y) r.tail.entries p.tail.entries := by
 simp only [SerialGaussian.Row.entries,Row.tail,Row.reduce]
 rw [List.zipWith_append (by simp [r.length_eq,p.length_eq])]
 rfl

def reduceInner : Prog :=
 .seq (.cond (fun c => c.2.2.pivot == 0)
    (moveRow .mat .back (fun _ a => a))
    (zipRow .mat .back .piv .pivBack (fun c x y => x-c.factor*y)))
   (moveRev .pivBack .piv (fun _ a => a))

def reduceBody : Prog :=
 .seq (.atom (.pop .mat (fun c a =>
   (none,(none,{c.2.2 with factor := (a.bind id).getD 0 / c.2.2.pivot}))) .done))
 (.seq reduceInner
   (.atom (.push .back (fun _ => none)
      (.peek .mat (fun c a => (a,(none,{c.2.2 with factor := 0}))) .done))))

def reduceLoop : Prog := .loop (fun c => c.1.isSome) reduceBody

def reduceMatrix : Prog := .seq (peek .mat) reduceLoop

def reducedRow {n} (p : Option (SerialGaussian.Row (n+1))) (r : SerialGaussian.Row (n+1)) : SerialGaussian.Row n :=
 p.elim r.tail (fun p => p.reduce r)

def reduceControl {n} (p : Option (SerialGaussian.Row (n+1))) (r : SerialGaussian.Row (n+1)) (a : Bool) : Control :=
 ⟨pivotHead p,r.head/pivotHead p,a⟩

lemma reduceInner_runs {n} (p : Option (SerialGaussian.Row (n+1)))
    (hp : ∀ q ∈ p, q.head ≠ 0) (r : SerialGaussian.Row (n+1)) (a : Bool)
    (d : Data) (xs bs : List Letter) :
 Runs reduceInner
   (st (reduceControl p r a) none
     {d with mat := r.tail.entries.map some ++ none::xs,back := bs,piv := pivotTail p,pivBack := []})
   (st (reduceControl p r a) none
     {d with mat := xs,back := ((reducedRow p r).entries.map some).reverse ++ bs,piv := pivotTail p,pivBack := []})
   (4*(n+1)+10) := by
 cases p with
 | none =>
   let c := reduceControl none r a
   have hm := moveRow_runs Reg.mat Reg.back (by decide) (fun (_ : Local) a => a)
     (none,c) none ({d with piv := [],pivBack := []}).tapes r.tail.entries xs bs
   have hm' : Runs (moveRow Reg.mat Reg.back (fun (_ : Local) a => a))
     (st c none {d with mat := r.tail.entries.map some ++ none::xs,back := bs,piv := [],pivBack := []})
     (st c none {d with mat := xs,back := (r.tail.entries.map some).reverse ++ bs,piv := [],pivBack := []})
     (2*(n+1)+5) := by simpa [st] using hm
   have hc := Runs.cond_true (f := fun c : Option Letter × Local => c.2.2.pivot == 0)
     (b := zipRow Reg.mat Reg.back Reg.piv Reg.pivBack (fun (c : Control) x y => x-c.factor*y))
     (by simp [st,state,c,reduceControl,pivotHead]) hm'
   have hr := moveRev_runs Reg.pivBack Reg.piv (by decide) (fun (_ : Local) a => a)
     (none,c) none ({d with mat := xs,back := (r.tail.entries.map some).reverse ++ bs}).tapes [] []
   have hr' : Runs (moveRev Reg.pivBack Reg.piv (fun (_ : Local) a => a))
     (st c none {d with mat := xs,back := (r.tail.entries.map some).reverse ++ bs,piv := [],pivBack := []})
     (st c none {d with mat := xs,back := (r.tail.entries.map some).reverse ++ bs,piv := [],pivBack := []}) 3 := by
     simpa [st,Function.comp_def] using hr
   exact (hc.seq hr').mono (by omega)
 | some p =>
   let c := reduceControl (some p) r a
   have hm := zipRow_runs Reg.mat Reg.back Reg.piv Reg.pivBack
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (fun (c : Control) x y => x-c.factor*y) c none d.tapes r.tail.entries p.tail.entries
     (by simp) xs bs []
   have hm' : Runs (zipRow Reg.mat Reg.back Reg.piv Reg.pivBack (fun (c : Control) x y => x-c.factor*y))
     (st c none {d with mat := r.tail.entries.map some ++ none::xs,back := bs,piv := p.tail.entries.map some,pivBack := []})
     (st c none {d with mat := xs,back := ((p.reduce r).entries.map some).reverse ++ bs,piv := [],pivBack := (p.tail.entries.map some).reverse}) (2*(n+1)+5) := by
     simpa [st,c,reduceControl,pivotHead,entries_reduce] using hm
   have hc := Runs.cond_false (f := fun c : Option Letter × Local => c.2.2.pivot == 0)
     (a := moveRow Reg.mat Reg.back (fun (_ : Local) a => a))
     (by simpa [st,state,c,reduceControl,pivotHead] using hp p (by simp)) hm'
   have hr := moveRev_runs Reg.pivBack Reg.piv (by decide) (fun (_ : Local) a => a)
     (none,c) none ({d with mat := xs,back := ((p.reduce r).entries.map some).reverse ++ bs}).tapes
     (p.tail.entries.map some).reverse []
   have hr' : Runs (moveRev Reg.pivBack Reg.piv (fun (_ : Local) a => a))
     (st c none {d with mat := xs,back := ((p.reduce r).entries.map some).reverse ++ bs,piv := [],pivBack := (p.tail.entries.map some).reverse})
     (st c none {d with mat := xs,back := ((p.reduce r).entries.map some).reverse ++ bs,piv := p.tail.entries.map some,pivBack := []}) (2*(n+1)+3) := by
     simpa [st,Function.comp_def] using hr
   convert hc.seq hr' using 1 <;> first | rfl | omega

lemma reduceBody_runs {n} (p : Option (SerialGaussian.Row (n+1)))
    (hp : ∀ q ∈ p, q.head ≠ 0) (r : SerialGaussian.Row (n+1)) (rs) (a : Bool)
    (buf : Option Letter) (d : Data) (bs : List Letter) :
 Runs reduceBody
   (st (ctrl (pivotHead p) a) buf
     {d with mat := payload (r::rs),back := bs,piv := pivotTail p,pivBack := []})
   (st (ctrl (pivotHead p) a) (payload rs).head?
     {d with mat := payload rs,back := (payload [reducedRow p r]).reverse ++ bs,piv := pivotTail p,pivBack := []})
   (4*(n+1)+14) := by
 have ho : Runs (.atom (.pop .mat (fun (c : Option Letter × Local) a =>
       (none,(none,{c.2.2 with factor := (a.bind id).getD 0/c.2.2.pivot}))) .done))
     (st (ctrl (pivotHead p) a) buf
       {d with mat := payload (r::rs),back := bs,piv := pivotTail p,pivBack := []})
     (st (reduceControl p r a) none
       {d with mat := r.tail.entries.map some ++ none::payload rs,back := bs,piv := pivotTail p,pivBack := []}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes,payload_cons,entries_head_tail,ctrl,reduceControl]
 have hi := reduceInner_runs p hp r a d (payload rs) bs
 have hf : Runs (.atom (.push .back (fun _ : Option Letter × Local => none)
       (.peek .mat (fun (c : Option Letter × Local) a => (a,(none,{c.2.2 with factor := 0}))) .done)))
     (st (reduceControl p r a) none
       {d with mat := payload rs,back := ((reducedRow p r).entries.map some).reverse ++ bs,piv := pivotTail p,pivBack := []})
     (st (ctrl (pivotHead p) a) (payload rs).head?
       {d with mat := payload rs,back := (payload [reducedRow p r]).reverse ++ bs,piv := pivotTail p,pivBack := []}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes,payload,SerialGaussian.Row.entries,ctrl,reduceControl,List.reverse_append]
 convert ho.seq (hi.seq hf) using 1 <;> first | rfl | omega

lemma reduceLoop_runs {n} (p : Option (SerialGaussian.Row (n+1)))
    (hp : ∀ q ∈ p, q.head ≠ 0) (a : Bool) (d : Data)
    (rs : List (SerialGaussian.Row (n+1))) (bs : List Letter) :
 Runs reduceLoop
   (st (ctrl (pivotHead p) a) (payload rs).head?
     {d with mat := payload rs,back := bs,piv := pivotTail p,pivBack := []})
   (st (ctrl (pivotHead p) a) none
     {d with mat := [],back := (payload (rs.map (reducedRow p))).reverse ++ bs,piv := pivotTail p,pivBack := []})
   ((4*(n+1)+15)*rs.length+1) := by
 induction rs generalizing bs with
 | nil => simpa [payload,reduceLoop] using
     (Runs.loop_false (b := reduceBody) (f := fun c : Option Letter × Local => c.1.isSome)
       (s := st (ctrl (pivotHead p) a) none {d with mat := [],back := bs,piv := pivotTail p,pivBack := []}) rfl)
 | cons r rs ih =>
   have hb := reduceBody_runs p hp r rs a (payload (r::rs)).head? d bs
   have ht := ih ((payload [reducedRow p r]).reverse ++ bs)
   have h := Runs.loop_true (f := fun c : Option Letter × Local => c.1.isSome)
     (by simp [st,state,payload_head]) hb ht
   convert h using 1 <;>
     simp [reduceLoop,payload,List.map_cons,List.reverse_append,List.append_assoc] ; ring

lemma reduceMatrix_runs {n} (p : Option (SerialGaussian.Row (n+1)))
    (hp : ∀ q ∈ p, q.head ≠ 0) (a : Bool) (buf : Option Letter) (d : Data)
    (rs : List (SerialGaussian.Row (n+1))) :
 Runs reduceMatrix
   (st (ctrl (pivotHead p) a) buf
     {d with mat := payload rs,back := [],piv := pivotTail p,pivBack := []})
   (st (ctrl (pivotHead p) a) none
     {d with mat := [],back := (payload (rs.map (reducedRow p))).reverse,piv := pivotTail p,pivBack := []})
   ((4*(n+1)+15)*rs.length+3) := by
 have hpeek : Runs (peek Reg.mat)
     (st (ctrl (pivotHead p) a) buf {d with mat := payload rs,back := [],piv := pivotTail p,pivBack := []})
     (st (ctrl (pivotHead p) a) (payload rs).head? {d with mat := payload rs,back := [],piv := pivotTail p,pivBack := []}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes]
 have h := hpeek.seq (reduceLoop_runs p hp a d rs [])
 have h' := h.mono (show 1+(1+((4*(n+1)+15)*rs.length+1)) ≤ (4*(n+1)+15)*rs.length+3 by omega)
 simpa only [List.append_nil,reduceMatrix] using h'

def eliminate : Prog :=
 .seq findPivot (.seq reduceMatrix
   (.seq (moveRev .back .mat (fun _ a => a))
      (.seq (clear .piv) (.atom (.load (fun c => (none,(none,ctrl 0 c.2.2.answer))) .done)))))

def nextRows {n} (rs : List (SerialGaussian.Row (n+1))) : List (SerialGaussian.Row n) :=
 rs.map (reducedRow (pivot rs))

@[simp] lemma nextRows_length {n} (rs : List (SerialGaussian.Row (n+1))) :
 (nextRows rs).length = rs.length := by simp [nextRows]

lemma pivot_nonzero {n} (rs : List (SerialGaussian.Row (n+1))) :
 ∀ q ∈ pivot rs, q.head ≠ 0 := by
 intro q hq
 have h := List.find?_some hq
 simpa [pivot,← Row.head_decode] using h

lemma solve_next {n} (rs : List (SerialGaussian.Row (n+1))) :
 solve rs = solve (nextRows rs) := by
 cases hp : pivot rs <;> simp only [solve,nextRows,hp] <;> rfl

lemma eliminate_runs {n} (c : Control) (buf : Option Letter) (d : Data)
    (rs : List (SerialGaussian.Row (n+1))) :
 Runs eliminate
   (st c buf {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := []})
   (st (ctrl 0 c.answer) none
     {d with mat := payload (nextRows rs),back := [],scan := [],piv := [],pivBack := []})
   (100*(rs.length+1)*(n+3)) := by
 let d' : Data := {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := []}
 let p := pivot rs
 have hf := findPivot_runs c buf d rs
 have hr := reduceMatrix_runs p (pivot_nonzero rs) c.answer none d' rs
 have hm := moveRev_runs Reg.back Reg.mat (by decide) (fun (_ : Local) a => a)
   (none,ctrl (pivotHead p) c.answer) none ({d' with piv := pivotTail p}).tapes
   (payload (nextRows rs)).reverse []
 have hm' : Runs (moveRev Reg.back Reg.mat (fun (_ : Local) a => a))
     (st (ctrl (pivotHead p) c.answer) none {d' with mat := [],back := (payload (nextRows rs)).reverse,piv := pivotTail p})
     (st (ctrl (pivotHead p) c.answer) none {d' with mat := payload (nextRows rs),piv := pivotTail p})
     (2*(payload (nextRows rs)).length+3) := by simpa [st,d',Function.comp_def] using hm
 have hc := clear_runs (σ := Local) Reg.piv (none,ctrl (pivotHead p) c.answer) none
   ({d' with mat := payload (nextRows rs)}).tapes (pivotTail p)
 have hc' : Runs (clear Reg.piv)
     (st (ctrl (pivotHead p) c.answer) none {d' with mat := payload (nextRows rs),piv := pivotTail p})
     (st (ctrl (pivotHead p) c.answer) none {d' with mat := payload (nextRows rs)})
     (2*(pivotTail p).length+3) := by simpa [st,d'] using hc
 have hl : Runs (.atom (.load (fun c : Option Letter × Local =>
       (none,(none,ctrl 0 c.2.2.answer))) .done))
     (st (ctrl (pivotHead p) c.answer) none {d' with mat := payload (nextRows rs)})
     (st (ctrl 0 c.answer) none {d' with mat := payload (nextRows rs)}) 1 := Runs.atom_of _ _ _ rfl
 have h := hf.seq (hr.seq (hm'.seq (hc'.seq hl)))
 apply h.mono
 rw [payload_length,nextRows_length]
 have ht := pivotTail_length p
 nlinarith

def normal : {n : ℕ} → List (SerialGaussian.Row n) → List (SerialGaussian.Row 0)
 | 0,rs => rs
 | _+1,rs => normal (nextRows rs)

@[simp] lemma normal_length {n} (rs : List (SerialGaussian.Row n)) :
 (normal rs).length = rs.length := by
 induction n with
 | zero => rfl
 | succ n ih => simpa [normal] using ih (nextRows rs)

lemma solve_normal {n} (rs : List (SerialGaussian.Row n)) : solve (normal rs) = solve rs := by
 induction n with
 | zero => rfl
 | succ n ih => rw [normal,ih,← solve_next]

def eliminationBody : Prog := .seq eliminate
 (.atom (.pop .width (fun c _ => c) (.peek .width (fun c a => (a,c.2)) .done)))

def eliminationLoop : Prog := .loop (fun c => c.1.isSome) eliminationBody

lemma eliminationBody_runs {n} (a : Bool) (buf : Option Letter) (d : Data)
    (rs : List (SerialGaussian.Row (n+1))) (ws : List Letter) :
 Runs eliminationBody
   (st (ctrl 0 a) buf {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [],width := none::ws})
   (st (ctrl 0 a) ws.head?
     {d with mat := payload (nextRows rs),back := [],scan := [],piv := [],pivBack := [],width := ws})
   (100*(rs.length+1)*(n+3)+2) := by
 have he := eliminate_runs (ctrl 0 a) buf {d with width := none::ws} rs
 have hp : Runs (.atom (.pop .width (fun c : Option Letter × Local => fun _ => c)
       (.peek .width (fun (c : Option Letter × Local) a => (a,c.2)) .done)))
     (st (ctrl 0 a) none {d with mat := payload (nextRows rs),back := [],scan := [],piv := [],pivBack := [],width := none::ws})
     (st (ctrl 0 a) ws.head? {d with mat := payload (nextRows rs),back := [],scan := [],piv := [],pivBack := [],width := ws}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes]
 convert he.seq hp using 1 <;> first | rfl | omega

lemma eliminationLoop_runs {n} (a : Bool) (d : Data) (rs : List (SerialGaussian.Row n)) :
 Runs eliminationLoop
   (st (ctrl 0 a) (List.replicate n (none : Letter)).head?
     {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [],width := List.replicate n none})
   (st (ctrl 0 a) none
     {d with mat := payload (normal rs),back := [],scan := [],piv := [],pivBack := [],width := []})
   (200*(rs.length+1)*(n+3)^2) := by
 induction n with
 | zero =>
   apply (Runs.loop_false rfl).mono
   norm_num
   omega
 | succ n ih =>
   have hb := eliminationBody_runs a (List.replicate (n+1) (none : Letter)).head? d rs
     (List.replicate n none)
   have ht := ih (nextRows rs)
   have h := Runs.loop_true (f := fun c : Option Letter × Local => c.1.isSome)
     (by simp [st,state,List.replicate_succ]) hb ht
   have h' : Runs eliminationLoop
       (st (ctrl 0 a) (List.replicate (n+1) (none : Letter)).head?
         {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [],width := List.replicate (n+1) none})
       (st (ctrl 0 a) none
         {d with mat := payload (normal rs),back := [],scan := [],piv := [],pivBack := [],width := []})
       (1+(100*(rs.length+1)*(n+3)+2+200*(rs.length+1)*(n+3)^2)) := by
     simpa only [eliminationLoop,List.replicate_succ,normal,nextRows_length] using h
   exact h'.mono (by nlinarith)

def zeroBody : Prog := .atom
 (.pop .mat (fun c a => (none,(none,{c.2.2 with answer := c.2.2.answer && ((a.bind id).getD 0 == 0)})))
  (.pop .mat (fun c _ => c) (.peek .mat (fun c a => (a,c.2)) .done)))

def zeroLoop : Prog := .loop (fun c => c.1.isSome) zeroBody

def checkZero : Prog :=
 .seq (.atom (.load (fun _ => (none,(none,ctrl 0 true)))
   (.peek .mat (fun c a => (a,c.2)) .done)))
 (.seq zeroLoop (.atom (.push .output (fun c => some (if c.2.2.answer then 1 else 0)) .done)))

lemma payload_zero_cons (r : SerialGaussian.Row 0) (rs) :
 payload (r::rs) = some r.rhs :: none :: payload rs := by
 have hc : r.coeff = [] := List.eq_nil_of_length_eq_zero r.length_eq
 simp [payload, hc]

lemma zeroLoop_runs (a : Bool) (d : Data) (rs : List (SerialGaussian.Row 0)) :
 Runs zeroLoop (st (ctrl 0 a) (payload rs).head? {d with mat := payload rs})
   (st (ctrl 0 (a && solve rs)) none {d with mat := []}) (2*rs.length+1) := by
 induction rs generalizing a with
 | nil => simpa [zeroLoop,solve,payload,ctrl] using
     (Runs.loop_false (b := zeroBody) (f := fun c : Option Letter × Local => c.1.isSome)
       (s := st (ctrl 0 a) none {d with mat := []}) rfl)
 | cons r rs ih =>
   have hb : Runs zeroBody (st (ctrl 0 a) (payload (r::rs)).head? {d with mat := payload (r::rs)})
       (st (ctrl 0 (a && (r.rhs == 0))) (payload rs).head? {d with mat := payload rs}) 1 := by
     apply Runs.atom_of
     simp [Action.run,st,state,ctrl,Data.tapes,payload_zero_cons]
   have h := Runs.loop_true (f := fun c : Option Letter × Local => c.1.isSome)
     (by simp [st,state,payload_zero_cons]) hb (ih (a && (r.rhs == 0)))
   convert h using 1 <;> simp [zeroLoop,solve,Bool.and_assoc] ; omega

lemma checkZero_runs (c : Control) (buf : Option Letter) (d : Data) (rs : List (SerialGaussian.Row 0)) :
 Runs checkZero (st c buf {d with mat := payload rs,output := []})
   (st (ctrl 0 (solve rs)) none {d with mat := [],output := boolCode (solve rs)}) (2*rs.length+5) := by
 have hi : Runs (.atom (.load (fun _ : Option Letter × Local => (none,(none,ctrl 0 true)))
       (.peek .mat (fun (c : Option Letter × Local) a => (a,c.2)) .done)))
     (st c buf {d with mat := payload rs,output := []})
     (st (ctrl 0 true) (payload rs).head? {d with mat := payload rs,output := []}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes]
 have hz := zeroLoop_runs true {d with output := []} rs
 have ho : Runs (.atom (.push .output (fun c : Option Letter × Local =>
       some (if c.2.2.answer then 1 else 0)) .done))
     (st (ctrl 0 (true && solve rs)) none {d with mat := [],output := []})
     (st (ctrl 0 (solve rs)) none {d with mat := [],output := boolCode (solve rs)}) 1 := by
   apply Runs.atom_of
   simp [Action.run,st,state,Data.tapes,ctrl,boolCode]
 convert hi.seq (hz.seq ho) using 1 <;> first | rfl | omega

def solver : Prog := .seq (peek .width) (.seq eliminationLoop checkZero)

lemma solver_runs {n} (d : Data) (rs : List (SerialGaussian.Row n)) :
 Runs solver
   (st (ctrl 0 true) none {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [], width := List.replicate n none,output := []})
   (st (ctrl 0 (solve rs)) none {d with mat := [],back := [],scan := [],piv := [],pivBack := [], width := [],output := boolCode (solve rs)})
   (300*(rs.length+1)*(n+3)^2) := by
 have hp : Runs (peek .width)
     (st (ctrl 0 true) none {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [], width := List.replicate n none,output := []})
     (st (ctrl 0 true) (List.replicate n (none : Letter)).head?
       {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [], width := List.replicate n none,output := []}) 1 := by
   apply Runs.atom_of
   rfl
 have he := eliminationLoop_runs true {d with output := []} rs
 have hz := checkZero_runs (ctrl 0 true) none
     {d with back := [],scan := [],piv := [],pivBack := [],width := []}
     (normal rs)
 have h := hp.seq (he.seq hz)
 have h' : Runs solver
   (st (ctrl 0 true) none {d with mat := payload rs,back := [],scan := [],piv := [],pivBack := [], width := List.replicate n none,output := []})
   (st (ctrl 0 (solve rs)) none {d with mat := [],back := [],scan := [],piv := [],pivBack := [], width := [],output := boolCode (solve rs)})
   (1+(1+(1+(200*(rs.length+1)*(n+3)^2+(2*rs.length+5))))) := by
   simpa only [solver,solve_normal,normal_length] using h
 exact h'.mono (by
   have hs : 1 ≤ (n+3)^2 := Nat.succ_le_iff.mpr (pow_pos (by omega) 2)
   have hm := Nat.mul_le_mul_left (rs.length+1) hs
   nlinarith)

end CPTSeparation.GaussMachine

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Counters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation.CounterLang

section

open StackLang StackLang.Macros

inductive Reg (R : Type) where
 | reg : R → Reg R
 | input | output | work | back | count
 deriving DecidableEq, Fintype

structure Data (R : Type) where
 regs : R → List Letter
 input : List Letter := []
 output : List Letter := []
 work : List Letter := []
 back : List Letter := []
 count : List Letter := []

namespace Data

variable {R : Type} [DecidableEq R]

def tapes (d : Data R) : Reg R → List Letter
 | .reg r => d.regs r
 | .input => d.input
 | .output => d.output
 | .work => d.work
 | .back => d.back
 | .count => d.count

@[simp] lemma tapes_reg (d : Data R) (r : R) (xs : List Letter) :
 Function.update d.tapes (.reg r) xs = ({d with regs := Function.update d.regs r xs}).tapes := by
 funext k; cases k with
 | reg k => simp [tapes,Function.update]
 | _ => simp [tapes,Function.update]

@[simp] lemma tapes_input (d : Data R) (xs : List Letter) : Function.update d.tapes .input xs = ({d with input := xs}).tapes := by funext k; cases k <;> simp [tapes,Function.update]

@[simp] lemma tapes_output (d : Data R) (xs : List Letter) : Function.update d.tapes .output xs = ({d with output := xs}).tapes := by funext k; cases k <;> simp [tapes,Function.update]

@[simp] lemma tapes_work (d : Data R) (xs : List Letter) : Function.update d.tapes .work xs = ({d with work := xs}).tapes := by funext k; cases k <;> simp [tapes,Function.update]

@[simp] lemma tapes_back (d : Data R) (xs : List Letter) : Function.update d.tapes .back xs = ({d with back := xs}).tapes := by funext k; cases k <;> simp [tapes,Function.update]

@[simp] lemma tapes_count (d : Data R) (xs : List Letter) : Function.update d.tapes .count xs = ({d with count := xs}).tapes := by funext k; cases k <;> simp [tapes,Function.update]

end Data

structure State (R σ : Type) where
 ctl : σ
 nums : R → ℕ
 input : List Letter
 output : List Letter

variable {R σ : Type} [DecidableEq R]

def unary (ns : R → ℕ) : R → List Letter := fun r => List.replicate (ns r) none

@[simp] lemma unary_update (ns : R → ℕ) (i : R) (n : ℕ) :
 unary (Function.update ns i n) = Function.update (unary ns) i (List.replicate n none) := by
 funext r; by_cases h : r = i <;> simp [unary,Function.update,h]

def State.data (s : State R σ) : Data R := ⟨unary s.nums,s.input,s.output,[],[],[]⟩

def State.encode (s : State R σ) : SStore (Reg R) Letter σ := state s.ctl none s.data.tapes

inductive Atom (R σ : Type) where
 | load (f : σ → σ)
 | zero (r : R)
 | inc (r : R)
 | dec (r : R)
 | positive (r : R) (f : σ → Bool → σ)
 | copy (r s : R) (h : r ≠ s)
 | add (r s : R) (h : r ≠ s)
 | lookup (r : R) (f : σ → Option Letter → σ)
 | consume (f : σ → Option Letter → σ)
 | emit (f : σ → Letter)

namespace Atom

def eval : Atom R σ → State R σ → State R σ
 | .load f,s => {s with ctl := f s.ctl}
 | .zero r,s => {s with nums := Function.update s.nums r 0}
 | .inc r,s => {s with nums := Function.update s.nums r (s.nums r+1)}
 | .dec r,s => {s with nums := Function.update s.nums r (s.nums r-1)}
 | .positive r f,s => {s with ctl := f s.ctl (s.nums r != 0)}
 | .copy r t _,s => {s with nums := Function.update s.nums t (s.nums r)}
 | .add r t _,s => {s with nums := Function.update s.nums t (s.nums r+s.nums t)}
 | .lookup r f,s => {s with ctl := f s.ctl s.input[s.nums r]?}
 | .consume f,s => {s with ctl := f s.ctl s.input.head?, input := s.input.tail}
 | .emit f,s => {s with output := f s.ctl :: s.output}

def cost : Atom R σ → State R σ → ℕ
 | .zero r,s => 2*s.nums r+3
 | .copy r t _,s => 2*s.nums t+4*s.nums r+12
 | .add r _ _,s => 4*s.nums r+7
 | .lookup r _,s => 10*(s.nums r+s.input.length+1)+30
 | _,_ => 1

end Atom

inductive Program (R σ : Type) where
 | atom (a : Atom R σ)
 | seq (a b : Program R σ)
 | cond (f : σ → Bool) (a b : Program R σ)
 | loop (f : σ → Bool) (a : Program R σ)

inductive Runs : Program R σ → State R σ → State R σ → ℕ → Prop
 | atom (a : Atom R σ) (s : State R σ) : Runs (.atom a) s (a.eval s) (a.cost s)
 | seq {a b s t u m n} : Runs a s t m → Runs b t u n → Runs (.seq a b) s u (1+(m+n))
 | cond_true {f a b s t n} : f s.ctl = true → Runs a s t n → Runs (.cond f a b) s t (1+n)
 | cond_false {f a b s t n} : f s.ctl = false → Runs b s t n → Runs (.cond f a b) s t (1+n)
 | loop_false {f a s} : f s.ctl = false → Runs (.loop f a) s s 1
 | loop_true {f a s t u m n} : f s.ctl = true → Runs a s t m → Runs (.loop f a) t u n →
     Runs (.loop f a) s u (1+(m+n))
 | mono {a s t m n} : Runs a s t m → m ≤ n → Runs a s t n

lemma Runs.loop_steps {f : σ → Bool} {p : Program R σ} (states : ℕ → State R σ) (n b : ℕ)
    (guard : ∀ i < n, f (states i).ctl = true) (stop : f (states n).ctl = false)
    (step : ∀ i < n, Runs p (states i) (states (i+1)) b) :
    Runs (.loop f p) (states 0) (states n) ((b+1)*n+1) := by
 induction n generalizing states with
 | zero => simpa using Runs.loop_false stop
 | succ n ih =>
   have h := Runs.loop_true (guard 0 (by omega)) (step 0 (by omega))
     (ih (fun i => states (i+1)) (fun i hi => guard (i+1) (by omega)) stop
       (fun i hi => step (i+1) (by omega)))
   convert h using 1 ; first | rfl | ring

end

section

open StackLang StackLang.Macros

variable {R σ : Type} [decidableR : DecidableEq R]

abbrev LowProgram (R σ : Type) := SProgram (Reg R) Letter σ

def skipBody : LowProgram R σ := .atom
 (.pop .count (fun c _ => c) (.pop .work (fun c _ => c)
  (.peek .count (fun c a => (a,c.2)) .done)))

def skipLoop : LowProgram R σ := .loop (fun c => c.1.isSome) skipBody

def lookup (r : R) (f : σ → Option Letter → σ) : LowProgram R σ :=
 .seq (copy .input .work .back)
 (.seq (copy (.reg r) .count .back)
 (.seq (peek .count)
 (.seq skipLoop
 (.seq (.atom (.peek .work (fun c a => (none,f c.2 a)) .done)) (clear .work)))))

namespace Atom

def compile : Atom R σ → LowProgram R σ
 | .load f => .atom (.load (fun c => (none,f c.2)) .done)
 | .zero r => clear (.reg r)
 | .inc r => .atom (.push (.reg r) (fun _ => none) .done)
 | .dec r => .atom (.pop (.reg r) (fun c _ => c) .done)
 | .positive r f => .atom (.peek (.reg r) (fun c a => (none,f c.2 a.isSome)) .done)
 | .copy r t _ => .seq (clear (.reg t)) (StackLang.Macros.copy (.reg r) (.reg t) .back)
 | .add r t _ => StackLang.Macros.copy (.reg r) (.reg t) .back
 | .lookup r f => CounterLang.lookup r f
 | .consume f => .atom (.pop .input (fun c a => (none,f c.2 a)) .done)
 | .emit f => .atom (.push .output (fun c => f c.2) .done)

end Atom

@[simp] lemma unary_update_self (ns : R → ℕ) (r : R) :
 Function.update (unary ns) r (List.replicate (ns r) none) = unary ns :=
  Function.update_eq_self r (unary ns)

@[simp] lemma unary_head (n : ℕ) : (List.replicate n (none : Letter)).head?.isSome = (n != 0) := by
 cases n <;> rfl

lemma skipLoop_runs (v : σ) (d : Data R) (k : ℕ) (xs : List Letter) :
 StackLang.Runs skipLoop
   (state v (List.replicate k (none : Letter)).head? ({d with count := List.replicate k none,work := xs}).tapes)
   (state v none ({d with count := [],work := xs.drop k}).tapes) (2*k+1) := by
 induction k generalizing xs with
 | zero => simpa [skipLoop] using
     (StackLang.Runs.loop_false (b := skipBody) (f := fun c : Option Letter × σ => c.1.isSome)
       (s := state v none ({d with count := [],work := xs}).tapes) rfl)
 | succ k ih =>
   have hb : StackLang.Runs skipBody
       (state v (some none) ({d with count := List.replicate (k+1) none,work := xs}).tapes)
       (state v (List.replicate k (none : Letter)).head?
         ({d with count := List.replicate k none,work := xs.tail}).tapes) 1 := by
     apply StackLang.Runs.atom_of
     simp [Action.run,state,Data.tapes,List.replicate_succ]
   have h := StackLang.Runs.loop_true (f := fun c : Option Letter × σ => c.1.isSome) rfl hb (ih xs.tail)
   convert h using 1 <;> first | rfl | omega | simp [List.drop_tail]

lemma lookup_runs (r : R) (f : σ → Option Letter → σ) (s : State R σ) :
 StackLang.Runs (lookup r f) s.encode ((Atom.lookup r f).eval s).encode
   ((Atom.lookup r f).cost s) := by
 let d := s.data
 have hc₁ := copy_runs (.input : Reg R) .work .back (by simp) (by simp) (by simp)
     s.ctl none d.tapes s.input []
 have hc₂ := copy_runs (.reg r) (.count : Reg R) .back (by simp) (by simp) (by simp)
     s.ctl none ({d with work := s.input}).tapes (List.replicate (s.nums r) none) []
 have hp : StackLang.Runs (peek (.count : Reg R))
     (state s.ctl none ({d with work := s.input,count := List.replicate (s.nums r) none}).tapes)
     (state s.ctl (List.replicate (s.nums r) (none : Letter)).head?
       ({d with work := s.input,count := List.replicate (s.nums r) none}).tapes) 1 := by
   apply StackLang.Runs.atom_of
   rfl
 have hs := skipLoop_runs s.ctl d (s.nums r) s.input
 have he : StackLang.Runs
     (.atom (.peek (.work : Reg R) (fun c a => (none,f c.2 a)) .done))
     (state s.ctl none ({d with work := s.input.drop (s.nums r),count := []}).tapes)
     (state (f s.ctl s.input[s.nums r]?) none
       ({d with work := s.input.drop (s.nums r),count := []}).tapes) 1 := by
   apply StackLang.Runs.atom_of
   simp [Action.run,state,Data.tapes]
 have hcl := clear_runs (.work : Reg R) (f s.ctl s.input[s.nums r]?) none
     ({d with count := []}).tapes (s.input.drop (s.nums r))
 have hc₁' : StackLang.Runs (copy (.input : Reg R) .work .back) s.encode
     (state s.ctl none ({d with work := s.input}).tapes) (4*s.input.length+7) := by
   simpa [d,State.encode,State.data] using hc₁
 have hc₂' : StackLang.Runs (copy (.reg r) (.count : Reg R) .back)
     (state s.ctl none ({d with work := s.input}).tapes)
     (state s.ctl none ({d with work := s.input,count := List.replicate (s.nums r) none}).tapes)
     (4*s.nums r+7) := by
   simpa [d,State.data] using hc₂
 have hcl' : StackLang.Runs (clear (.work : Reg R))
     (state (f s.ctl s.input[s.nums r]?) none ({d with work := s.input.drop (s.nums r),count := []}).tapes)
     ((Atom.lookup r f).eval s).encode (2*(s.input.drop (s.nums r)).length+3) := by
   simpa [d,State.encode,State.data,Atom.eval] using hcl
 have h := hc₁'.seq (hc₂'.seq (hp.seq (hs.seq (he.seq hcl'))))
 exact h.mono (by simp only [Atom.cost,List.length_drop]; omega)

lemma Atom.zero_runs (r : R) (s : State R σ) :
 StackLang.Runs (Atom.compile (.zero r)) s.encode ((Atom.zero r).eval s).encode ((Atom.zero r).cost s) := by
 have h := clear_runs (.reg r) s.ctl none s.data.tapes (List.replicate (s.nums r) none)
 simpa [compile,State.encode,State.data,eval,cost,unary_update] using h

lemma Atom.add_runs (r t : R) (hrt : r ≠ t) (s : State R σ) :
 StackLang.Runs (Atom.compile (.add r t hrt)) s.encode ((Atom.add r t hrt).eval s).encode
   ((Atom.add r t hrt).cost s) := by
 have h := copy_runs (.reg r) (.reg t) (.back : Reg R) (by simpa) (by simp) (by simp)
     s.ctl none s.data.tapes (List.replicate (s.nums r) none) (List.replicate (s.nums t) none)
 simpa [compile,State.encode,State.data,eval,cost,unary_update,← List.replicate_add] using h

lemma Atom.compile_runs (a : Atom R σ) (s : State R σ) :
 StackLang.Runs a.compile s.encode (a.eval s).encode (a.cost s) := by
 cases a with
 | load f =>
   apply StackLang.Runs.atom_of
   rfl
 | zero r => exact zero_runs r s
 | inc r =>
   apply StackLang.Runs.atom_of
   simp [Action.run,State.encode,State.data,eval,state,Data.tapes,unary_update,List.replicate_succ,unary]
 | dec r =>
   apply StackLang.Runs.atom_of
   simp [Action.run,State.encode,State.data,eval,state,Data.tapes,unary_update,unary]
 | positive r f =>
   apply StackLang.Runs.atom_of
   simp [Action.run,State.encode,State.data,state,Data.tapes,eval,unary]
 | consume f =>
   apply StackLang.Runs.atom_of
   simp [Action.run,State.encode,State.data,state,Data.tapes,eval]
 | emit f =>
   apply StackLang.Runs.atom_of
   simp [Action.run,State.encode,State.data,state,Data.tapes,eval]
 | add r t hrt => exact add_runs r t hrt s
 | copy r t hrt =>
   have hz := zero_runs t s
   have ha := add_runs r t hrt ((Atom.zero t).eval s)
   have h := hz.seq ha
   have h' : StackLang.Runs (Atom.compile (.copy r t hrt)) s.encode
       ((Atom.copy r t hrt).eval s).encode (1+(2*s.nums t+3+(4*s.nums r+7))) := by
     simpa only [compile,eval,cost,Function.update_self,Function.update_of_ne hrt,
       Nat.add_zero,Function.update_idem] using h
   exact h'.mono (by simp only [cost]; omega)
 | lookup r f => exact lookup_runs r f s

namespace Program

def compile : Program R σ → LowProgram R σ
 | .atom a => a.compile
 | .seq a b => .seq a.compile b.compile
 | .cond f a b => .cond (fun c => f c.2) a.compile b.compile
 | .loop f a => .loop (fun c => f c.2) a.compile

end Program

lemma Runs.compiles {p : Program R σ} {s t : State R σ} {n : ℕ} (h : Runs p s t n) :
 StackLang.Runs p.compile s.encode t.encode n := by
 induction h with
 | atom a s => exact a.compile_runs s
 | seq _ _ ih₁ ih₂ => exact ih₁.seq ih₂
 | cond_true hf _ ih => exact StackLang.Runs.cond_true hf ih
 | cond_false hf _ ih => exact StackLang.Runs.cond_false hf ih
 | loop_false hf => exact StackLang.Runs.loop_false hf
 | loop_true hf _ _ ih₁ ih₂ => exact StackLang.Runs.loop_true hf ih₁ ih₂
 | mono _ h ih => exact ih.mono h

end

section

variable {R V : Type} [decidableR : DecidableEq R]

omit R V in
@[ext] lemma State.ext
    {R : Type}
    {V : Type}
    [DecidableEq R] {s t : State R V} (hc : s.ctl = t.ctl) (hn : s.nums = t.nums)
   (hi : s.input = t.input) (ho : s.output = t.output) : s = t := by
 cases s; cases t; simp_all

lemma Runs.atom_of {a : Atom R V} {s t : State R V} {n : ℕ}
    (he : a.eval s = t) (hn : a.cost s ≤ n) : Runs (.atom a) s t n := by
 subst t
 exact (Runs.atom a s).mono hn

@[simp] lemma bne_nat_zero (n : ℕ) : (n != 0) = decide (0 < n) := by
 cases n <;> rfl

def testPos (r : R) : Program R (Bool × V) := .atom (.positive r (fun c b => (b,c.2)))

def flag (s : State R (Bool × V)) (b : Bool) : State R (Bool × V) := {s with ctl := (b,s.ctl.2)}

def mulBody (a dst tmp : R) (had : a ≠ dst) : Program R (Bool × V) :=
 .seq (.atom (.add a dst had)) (.seq (.atom (.dec tmp)) (testPos tmp))

def mulLoop (a dst tmp : R) (had : a ≠ dst) : Program R (Bool × V) :=
 .loop Prod.fst (mulBody a dst tmp had)

def multiply (a b dst tmp : R) (had : a ≠ dst) (hbt : b ≠ tmp) : Program R (Bool × V) :=
 .seq (.atom (.zero dst)) (.seq (.atom (.copy b tmp hbt))
   (.seq (testPos tmp) (mulLoop a dst tmp had)))

def mulState (s : State R (Bool × V)) (dst tmp : R) (A B i : ℕ) : State R (Bool × V) :=
 {s with ctl := (decide (i < B),s.ctl.2), nums := Function.update (Function.update s.nums dst (A*i)) tmp (B-i)}

lemma mulBody_runs (a dst tmp : R) (had : a ≠ dst) (hat : a ≠ tmp) (hdt : dst ≠ tmp)
   (s : State R (Bool × V)) (B i : ℕ) (hi : i < B) :
 Runs (mulBody a dst tmp had) (mulState s dst tmp (s.nums a) B i)
   (mulState s dst tmp (s.nums a) B (i+1)) (4*s.nums a+11) := by
 let s₀ := mulState s dst tmp (s.nums a) B i
 let s₁ := (Atom.add a dst had).eval s₀
 let s₂ := (Atom.dec tmp).eval s₁
 have h := (Runs.atom (.add a dst had) s₀).seq
   ((Runs.atom (.dec tmp) s₁).seq (Runs.atom (.positive tmp (fun c b => (b,c.2))) s₂))
 have he : (Atom.positive tmp (fun (c : Bool × V) b => (b,c.2))).eval s₂ =
     mulState s dst tmp (s.nums a) B (i+1) := by
   apply State.ext
   · have hb : 0 < B-i-1 ↔ i+1 < B := by omega
     simp [s₂,s₁,s₀,mulState,Atom.eval,Function.update,Ne.symm hdt,bne_nat_zero,hb]
   · funext k
     by_cases hk : k = tmp
     · subst k; simp [s₂,s₁,s₀,mulState,Atom.eval,Function.update,hdt,Ne.symm hdt]; omega
     · by_cases hk' : k = dst
       · subst k
         simp [s₂,s₁,s₀,mulState,Atom.eval,Function.update,hdt,hat,had,Ne.symm hdt]
         ring
       · simp [s₂,s₁,s₀,mulState,Atom.eval,Function.update,hk,hk']
   · rfl
   · rfl
 rw [he] at h
 exact h.mono (by simp [s₀,mulState,Atom.cost,Function.update,hat,had]; omega)

lemma mulLoop_runs (a dst tmp : R) (had : a ≠ dst) (hat : a ≠ tmp) (hdt : dst ≠ tmp)
   (s : State R (Bool × V)) (B : ℕ) :
 Runs (mulLoop a dst tmp had) (mulState s dst tmp (s.nums a) B 0)
   (mulState s dst tmp (s.nums a) B B) ((4*s.nums a+12)*B+1) := by
 exact Runs.loop_steps (fun i => mulState s dst tmp (s.nums a) B i) B (4*s.nums a+11)
   (by intro i hi; simp [mulState,hi]) (by simp [mulState])
   (by intro i hi; exact mulBody_runs a dst tmp had hat hdt s B i hi)

lemma multiply_runs (a b dst tmp : R) (had : a ≠ dst) (hbt : b ≠ tmp)
   (hat : a ≠ tmp) (hbd : b ≠ dst) (hdt : dst ≠ tmp) (s : State R (Bool × V)) :
 Runs (multiply a b dst tmp had hbt) s
   {s with ctl := (false,s.ctl.2), nums := Function.update (Function.update s.nums dst (s.nums a*s.nums b)) tmp 0}
   (2*s.nums dst+2*s.nums tmp+4*s.nums b+(4*s.nums a+12)*s.nums b+20) := by
 let s₁ := (Atom.zero dst).eval s
 let s₂ := (Atom.copy b tmp hbt).eval s₁
 have he : (Atom.positive tmp (fun (c : Bool × V) b => (b,c.2))).eval s₂ =
     mulState s dst tmp (s.nums a) (s.nums b) 0 := by
   ext k <;> simp [s₂,s₁,Atom.eval,mulState,Function.update,hbd,bne_nat_zero]
 have hpre := (Runs.atom (.copy b tmp hbt) s₁).seq
    ((Runs.atom (.positive tmp (fun (c : Bool × V) b => (b,c.2))) s₂))
 have hp : Runs (.seq (.atom (.copy b tmp hbt)) (testPos tmp)) s₁
     (mulState s dst tmp (s.nums a) (s.nums b) 0) (2*s.nums tmp+4*s.nums b+14) := by
   rw [he] at hpre
   exact hpre.mono (by simp [s₁,Atom.cost,Atom.eval,Function.update,hbd,Ne.symm hdt]; omega)
 have hlo := mulLoop_runs a dst tmp had hat hdt s (s.nums b)
 have hf : mulState s dst tmp (s.nums a) (s.nums b) (s.nums b) =
     {s with ctl := (false,s.ctl.2), nums := Function.update (Function.update s.nums dst (s.nums a*s.nums b)) tmp 0} := by
   simp [mulState]
 rw [hf] at hlo
 have ht := (Runs.atom (.positive tmp (fun (c : Bool × V) b => (b,c.2))) s₂)
 rw [he] at ht
 have h := (Runs.atom (.zero dst) s).seq ((Runs.atom (.copy b tmp hbt) s₁).seq (ht.seq hlo))
 exact h.mono (by simp [s₁,Atom.cost,Atom.eval,Function.update,hbd,Ne.symm hdt]; omega)

def repeatAdd (src dst : R) (h : src ≠ dst) : ℕ → Program R V
 | 0 => .atom (.load id)
 | k+1 => .seq (.atom (.add src dst h)) (repeatAdd src dst h k)

lemma repeatAdd_runs (src dst : R) (hnd : src ≠ dst) (k : ℕ) (s : State R V) :
 Runs (repeatAdd src dst hnd k) s
   {s with nums := Function.update s.nums dst (s.nums dst+k*s.nums src)}
   ((4*s.nums src+8)*k+1) := by
 induction k generalizing s with
 | zero => simpa [repeatAdd,Atom.eval,Atom.cost] using Runs.atom (.load id) s
 | succ k ih =>
   have h := (Runs.atom (.add src dst hnd) s).seq (ih ((Atom.add src dst hnd).eval s))
   have he : (s.nums src+s.nums dst)+k*s.nums src = s.nums dst+(k+1)*s.nums src := by ring
   have h' : Runs (repeatAdd src dst hnd (k+1)) s
       {s with nums := Function.update s.nums dst (s.nums dst+(k+1)*s.nums src)}
       (1+(4*s.nums src+7+((4*s.nums src+8)*k+1))) := by
     simpa [repeatAdd,Atom.eval,Atom.cost,he,hnd] using h
   exact h'.mono (by nlinarith)

end

variable {R V : Type} [DecidableEq R]

def indexState (idx rem : R) (N i : ℕ) (s : State R (Bool × V)) : State R (Bool × V) :=
 {s with ctl := (decide (i<N),s.ctl.2), nums := Function.update (Function.update s.nums idx i) rem (N-i)}

def rangeBody (idx rem : R) (body : Program R (Bool × V)) : Program R (Bool × V) :=
 .seq body (.seq (.atom (.inc idx)) (.seq (.atom (.dec rem)) (testPos rem)))

def forRange (size idx rem : R) (hnr : size ≠ rem) (body : Program R (Bool × V)) : Program R (Bool × V) :=
 .seq (.atom (.copy size rem hnr)) (.seq (testPos rem)
   (.seq (.loop Prod.fst (rangeBody idx rem body)) (.atom (.zero idx))))

lemma rangeTail_runs (idx rem : R) (hir : idx ≠ rem) (N i : ℕ) (s : State R (Bool × V)) (hi : i<N) :
 Runs (.seq (.atom (.inc idx)) (.seq (.atom (.dec rem)) (testPos rem)))
   (flag (indexState idx rem N i s) false) (indexState idx rem N (i+1) s) 5 := by
 let s₀ := flag (indexState idx rem N i s) false
 let s₁ := (Atom.inc idx).eval s₀
 let s₂ := (Atom.dec rem).eval s₁
 have h := (Runs.atom (.inc idx) s₀).seq
   ((Runs.atom (.dec rem) s₁).seq (Runs.atom (.positive rem (fun c b => (b,c.2))) s₂))
 have he : (Atom.positive rem (fun (c : Bool × V) b => (b,c.2))).eval s₂ =
     indexState idx rem N (i+1) s := by
   have hh : 0 < N-i-1 ↔ i+1<N := by omega
   apply State.ext
   · simp [s₂,s₁,s₀,flag,indexState,Atom.eval,Function.update,Ne.symm hir,bne_nat_zero,hh]
   · funext k
     by_cases hk : k = rem
     · subst k; simp [s₂,s₁,s₀,flag,indexState,Atom.eval,Function.update,Ne.symm hir]; omega
     · by_cases hki : k = idx
       · subst k; simp [s₂,s₁,s₀,flag,indexState,Atom.eval,Function.update,hir]
       · simp [s₂,s₁,s₀,flag,indexState,Atom.eval,Function.update,hk,hki]
   · rfl
   · rfl
 rw [he] at h
 exact h

lemma forRange_runs (size idx rem : R) (hnr : size ≠ rem) (hir : idx ≠ rem)
   (body : Program R (Bool × V)) (S : ℕ → State R (Bool × V)) (N b : ℕ)
   (hsize : (S 0).nums size = N)
   (hi₀ : (S 0).nums idx = 0) (hr₀ : (S 0).nums rem = 0)
   (hiN : (S N).nums idx = 0) (hrN : (S N).nums rem = 0)
   (hcN : (S N).ctl.1 = false)
   (hb : ∀ i<N, Runs body (indexState idx rem N i (S i))
      (flag (indexState idx rem N i (S (i+1))) false) b) :
 Runs (forRange size idx rem hnr body) (S 0) (S N) ((b+13)*N+20) := by
 let inner := fun i => indexState idx rem N i (S i)
 have loop : Runs (.loop Prod.fst (rangeBody idx rem body)) (inner 0) (inner N) ((b+7)*N+1) := by
   apply Runs.loop_steps inner N (b+6)
   · intro i hi; simp [inner,indexState,hi]
   · simp [inner,indexState]
   · intro i hi
     have h := (hb i hi).seq (rangeTail_runs idx rem hir N i (S (i+1)) hi)
     convert h using 1 <;> first | rfl | omega
 have hz : Runs (.atom (.zero idx)) (inner N) (S N) (2*N+3) := by
   apply Runs.atom_of
   · apply State.ext
     · apply Prod.ext <;> simp [inner,indexState,Atom.eval,hcN]
     · funext k
       by_cases hki : k = idx
       · subst k; simp [inner,indexState,Atom.eval,Function.update,hiN]
       · by_cases hkr : k = rem
         · subst k; simp [inner,indexState,Atom.eval,Function.update,hrN,Ne.symm hir]
         · simp [inner,indexState,Atom.eval,Function.update,hki,hkr]
     · rfl
     · rfl
   · simp [inner,indexState,Atom.cost,Function.update,hir]
 let s₁ := (Atom.copy size rem hnr).eval (S 0)
 have ht : Runs (testPos rem) s₁ (inner 0) 1 := by
   apply Runs.atom_of
   · apply State.ext
     · simp [s₁,inner,indexState,Atom.eval,Function.update,hsize,bne_nat_zero]
     · funext k
       by_cases hkr : k = rem
       · subst k; simp [s₁,inner,indexState,Atom.eval,Function.update,hsize]
       · by_cases hki : k = idx
         · subst k; simp [s₁,inner,indexState,Atom.eval,Function.update,hi₀,hir]
         · simp [s₁,inner,indexState,Atom.eval,Function.update,hkr,hki]
     · rfl
     · rfl
   · rfl
 have h := (Runs.atom (.copy size rem hnr) (S 0)).seq (ht.seq (loop.seq hz))
 exact h.mono (by simp only [Atom.cost,hr₀,hsize]; nlinarith)

def bothPositive (a b : R) : Program R (Bool × V) :=
 .seq (testPos a) (.atom (.positive b (fun c q => (c.1 && q,c.2))))

def compareBody (a b : R) : Program R (Bool × V) :=
 .seq (.atom (.dec a)) (.seq (.atom (.dec b)) (bothPositive a b))

def compare (i j a b : R) (hia : i ≠ a) (hjb : j ≠ b)
    (f : V → Bool → V) : Program R (Bool × V) :=
 Program.seq (.atom (.copy i a hia)) <|
 Program.seq (.atom (.copy j b hjb)) <|
 Program.seq (bothPositive a b) <|
 Program.seq (.loop Prod.fst (compareBody a b)) <|
 Program.seq (testPos a) <|
 Program.seq (.atom (.positive b (fun c q => (c.1 || q,c.2))))
   (.atom (.load (fun c => (false,f c.2 (!c.1)))))

lemma bothPositive_runs (a b : R) (s : State R (Bool × V)) :
 Runs (bothPositive a b) s (flag s (decide (0<s.nums a ∧ 0<s.nums b))) 3 := by
 have h := (Runs.atom (.positive a (fun c q => (q,c.2))) s).seq
   (Runs.atom (.positive b (fun c q => (c.1 && q,c.2)))
     ((Atom.positive a (fun c q => (q,c.2))).eval s))
 simpa [bothPositive,testPos,Atom.eval,Atom.cost,flag,bne_nat_zero,Nat.pos_iff_ne_zero] using h

lemma compare_runs (i j a b : R) (hia : i ≠ a) (hjb : j ≠ b)
    (hja : j ≠ a) (hab : a ≠ b) (f : V → Bool → V) (s : State R (Bool × V)) :
 Runs (compare i j a b hia hjb f) s
   {s with ctl := (false,f s.ctl.2 (decide (s.nums i = s.nums j))), nums := Function.update (Function.update s.nums a (s.nums i - s.nums j)) b (s.nums j - s.nums i)}
   (2*s.nums a+2*s.nums b+20*(s.nums i+s.nums j)+40) := by
 let x := s.nums i
 let y := s.nums j
 let m := min x y
 let st (k : ℕ) : State R (Bool × V) :=
   {s with ctl := (decide (k < m),s.ctl.2), nums := Function.update (Function.update s.nums a (x-k)) b (y-k)}
 have guard (k : ℕ) : (0<x-k ∧ 0<y-k) ↔ k < m := by dsimp [m]; omega
 have hb (k : ℕ) (hk : k < m) : Runs (compareBody a b) (st k) (st (k+1)) 7 := by
   let s₁ := (Atom.dec a).eval (st k)
   let s₂ := (Atom.dec b).eval s₁
   have h := (Runs.atom (.dec a) (st k)).seq
      ((Runs.atom (.dec b) s₁).seq (bothPositive_runs a b s₂))
   have he : flag s₂ (decide (0<s₂.nums a ∧ 0<s₂.nums b)) = st (k+1) := by
     have hg : (0<x-k-1 ∧ 0<y-k-1) ↔ k+1 < m := by dsimp [m]; omega
     apply State.ext
     · apply Prod.ext
       · apply Bool.eq_iff_iff.mpr
         simp [s₂,s₁,st,flag,Atom.eval,Function.update,hab,Ne.symm hab]
         dsimp [m]; omega
       · rfl
     · funext r
       by_cases hra : r=a
       · subst r; simp [s₂,s₁,st,flag,Atom.eval,Function.update,hab,Ne.symm hab]; omega
       · by_cases hrb : r=b
         · subst r; simp [s₂,s₁,st,flag,Atom.eval,Function.update,hab,Ne.symm hab]; omega
         · simp [s₂,s₁,st,flag,Atom.eval,Function.update,hra,hrb]
     · rfl
     · rfl
   rw [he] at h
   exact h
 have hl : Runs (.loop Prod.fst (compareBody a b)) (st 0) (st m) (8*m+1) :=
   Runs.loop_steps st m 7 (by intro k hk; simp [st,hk]) (by simp [st]) hb
 let s₁ := (Atom.copy i a hia).eval s
 let s₂ := (Atom.copy j b hjb).eval s₁
 have hin : flag s₂ (decide (0<s₂.nums a ∧ 0<s₂.nums b)) = st 0 := by
   apply State.ext
   · apply Prod.ext
     · apply Bool.eq_iff_iff.mpr
       simp [s₂,s₁,st,flag,Atom.eval,Function.update,hab,hja,x,y,m]
     · rfl
   · funext r; simp [s₂,s₁,st,flag,Atom.eval,Function.update,hab,hja,x,y]
   · rfl
   · rfl
 have ht := bothPositive_runs a b s₂
 rw [hin] at ht
 let s₃ := (Atom.positive a (fun c q => (q,c.2))).eval (st m)
 let s₄ := (Atom.positive b (fun c q => (c.1 || q,c.2))).eval s₃
 have hend : (Atom.load (fun c : Bool × V => (false,f c.2 (!c.1)))).eval s₄ =
     {s with ctl := (false,f s.ctl.2 (decide (s.nums i = s.nums j))), nums := Function.update (Function.update s.nums a (s.nums i-s.nums j)) b (s.nums j-s.nums i)} := by
   have hx : x-m=x-y := by dsimp [m]; omega
   have hy : y-m=y-x := by dsimp [m]; omega
   have hz : (!decide (m<x) && !decide (m<y)) = decide (x=y) := by
     apply Bool.eq_iff_iff.mpr
     simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq]
     dsimp [m]; omega
   apply State.ext
   · simpa [s₄,s₃,st,Atom.eval,Function.update,hab,Ne.symm hab,x,y] using congrArg (fun z => (false,f s.ctl.2 z)) hz
   · simp [s₄,s₃,st,Atom.eval,hx,hy,x,y]
   · rfl
   · rfl
 have he := Runs.atom (.load (fun c : Bool × V => (false,f c.2 (!c.1)))) s₄
 rw [hend] at he
 have h := (Runs.atom (.copy i a hia) s).seq
   ((Runs.atom (.copy j b hjb) s₁).seq
   (ht.seq (hl.seq ((Runs.atom (.positive a (fun c q => (q,c.2))) (st m)).seq
   ((Runs.atom (.positive b (fun c q => (c.1 || q,c.2))) s₃).seq he)))))
 apply h.mono
 simp [s₁,Atom.cost,Atom.eval,Function.update,hja,Ne.symm hab]
 dsimp [x,y,m] at *
 omega

end CPTSeparation.CounterLang

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.TableMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation.TableMachine

open CounterLang

inductive Index where
 | t | y | a | x | z
 deriving DecidableEq

instance instFintypeIndex : Fintype Index := ⟨{.t,.y,.a,.x,.z}, by intro i; cases i <;> simp⟩

inductive Reg where
 | size | width
 | idx : Index → Reg
 | rem : Index → Reg
 | addr | prod | tmp | cmp
 deriving DecidableEq, Fintype

abbrev CState (V : Type) := CounterLang.State Reg (Bool × V)

abbrev Prog (V : Type) := CounterLang.Program Reg (Bool × V)

lemma tableInput_length {N} (S : OrderedQuery.Data N) : (tableInput S).length = 8*(N*N) := by
 simp [tableInput]

lemma tableInput_lookup {N} (S : OrderedQuery.Data N) (r : Symbol) (a b : Fin N) :
 (tableInput S)[((OrderedQuery.symbolIndex r).val*N+a.val)*N+b.val]? =
   some (bitLetter (S.rel r a b)) := by
 have hi : ((OrderedQuery.symbolIndex r).val*N+a.val)*N+b.val =
     (OrderedQuery.cellIndex r a b).val := by
   simp [OrderedQuery.cellIndex,finProdFinEquiv]
   ring
 rw [hi]
 simp [tableInput,OrderedQuery.tableBits,OrderedQuery.cellValue_index]

def readCell {V} (k : ℕ) (i j : Index) (f : V → Option Letter → V) : Prog V :=
 .seq (.atom (.zero .addr))
 (.seq (repeatAdd .size .addr (by decide) k)
 (.seq (.atom (.add (.idx i) .addr (by simp)))
 (.seq (multiply .addr .size .prod .tmp (by decide) (by decide))
 (.seq (.atom (.add (.idx j) .prod (by simp)))
 (.seq (.atom (.lookup .prod (fun c a => (c.1,f c.2 a))))
 (.seq (.atom (.zero .addr)) (.atom (.zero .prod))))))))

lemma readCell_runs {V} (s : CState V) (k : ℕ) (i j : Index) (f : V → Option Letter → V)
   (haddr : s.nums .addr = 0) (hprod : s.nums .prod = 0) (htmp : s.nums .tmp = 0) :
 Runs (readCell k i j f) s
   {s with ctl := (false,f s.ctl.2 s.input[((k*s.nums .size+s.nums (.idx i))*s.nums .size+s.nums (.idx j))]?)}
   (16*k*(s.nums .size)^2+16*s.nums (.idx i)*s.nums .size +
     6*k*s.nums .size+8*k+16*s.nums .size+6*s.nums (.idx i)+16*s.nums (.idx j)+10*s.input.length+101) := by
 let s₁ := (Atom.zero .addr).eval s
 let s₂ : CState V := {s₁ with nums := Function.update s₁.nums .addr (s₁.nums .addr+k*s₁.nums .size)}
 let s₃ := (Atom.add (.idx i) .addr (by simp)).eval s₂
 let s₄ : CState V := {s₃ with ctl := (false,s₃.ctl.2), nums := Function.update (Function.update s₃.nums .prod (s₃.nums .addr*s₃.nums .size)) .tmp 0}
 let s₅ := (Atom.add (.idx j) .prod (by simp)).eval s₄
 let s₆ := (Atom.lookup .prod (fun c a => (c.1,f c.2 a))).eval s₅
 let s₇ := (Atom.zero .addr).eval s₆
 let s₈ := (Atom.zero .prod).eval s₇
 have hm := multiply_runs .addr .size .prod .tmp (by decide) (by decide) (by decide) (by decide) (by decide) s₃
 have h := (Runs.atom (.zero .addr) s).seq
   ((repeatAdd_runs .size .addr (by decide) k s₁).seq
   ((Runs.atom (.add (.idx i) .addr (by simp)) s₂).seq
   (hm.seq ((Runs.atom (.add (.idx j) .prod (by simp)) s₄).seq
   ((Runs.atom (.lookup .prod (fun c a => (c.1,f c.2 a))) s₅).seq
   ((Runs.atom (.zero .addr) s₆).seq (Runs.atom (.zero .prod) s₇)))))))
 have he : s₈ = {s with ctl := (false,f s.ctl.2 s.input[((k*s.nums .size+s.nums (.idx i))*s.nums .size+s.nums (.idx j))]?)} := by
   apply CounterLang.State.ext
   · simp [s₈,s₇,s₆,s₅,s₄,s₃,s₂,s₁,Atom.eval,Function.update,Nat.add_comm]
   · funext r; cases r <;> simp [s₈,s₇,s₆,s₅,s₄,s₃,s₂,s₁,Atom.eval,Function.update,haddr,hprod,htmp]
   · rfl
   · rfl
 change Runs (readCell k i j f) s s₈ _ at h
 rw [he] at h
 apply h.mono
 simp only [s₇,s₆,s₅,s₄,s₃,s₂,s₁,Atom.eval,Atom.cost]
 simp [Function.update,haddr,hprod,htmp]
 ; nlinarith

end CPTSeparation.TableMachine

namespace CPTSeparation.Bounded

section

open CounterLang TableMachine

inductive Program (V : Type) where
 | load (f : V → V)
 | emit (f : V → Letter)
 | cell (r : Symbol) (i j : Index) (f : V → Bool → V)
 | equal (i j : Index) (f : V → Bool → V)
 | seq (a b : Program V)
 | loop (i : Index) (body : Program V)

variable {V : Type}

def isOne (a : Option Letter) : Bool := a == some (some 1)

def Program.WF : Program V → Finset Index → Prop
 | .load _,_ => True
 | .emit _,_ => True
 | .cell _ _ _ _,_ => True
 | .equal _ _ _,_ => True
 | .seq a b,S => a.WF S ∧ b.WF S
 | .loop i b,S => i ∉ S ∧ b.WF (insert i S)

def Program.eval (N : ℕ) (table : List Letter) :
    Program V → (Index → ℕ) → V × List Letter → V × List Letter
 | .load f,_,s => (f s.1,s.2)
 | .emit f,_,s => (s.1,f s.1::s.2)
 | .cell r i j f,e,s => (f s.1 (isOne table[((OrderedQuery.symbolIndex r).val*N+e i)*N+e j]?),s.2)
 | .equal i j f,e,s => (f s.1 (e i == e j),s.2)
 | .seq a b,e,s => b.eval N table e (a.eval N table e s)
 | .loop i b,e,s => (List.range N).foldl (fun s k => b.eval N table (Function.update e i k) s) s

def equalCode (i j : Index) (f : V → Bool → V) : Prog V :=
 .seq (CounterLang.compare (.idx i) (.idx j) .addr .prod (by simp) (by simp) f)
   (.seq (.atom (.zero .addr)) (.atom (.zero .prod)))

def Program.compile : Program V → Prog V
 | .load f => .atom (.load (fun c => (false,f c.2)))
 | .emit f => .seq (.atom (.emit (fun c => f c.2))) (.atom (.load (fun c => (false,c.2))))
 | .cell r i j f => readCell (OrderedQuery.symbolIndex r).val i j (fun v a => f v (isOne a))
 | .equal i j f => equalCode i j f
 | .seq a b => .seq a.compile b.compile
 | .loop i b => .seq (.atom (.load (fun c => (false,c.2))))
   (forRange .size (.idx i) (.rem i) (by simp) b.compile)

def Program.time (N L : ℕ) : Program V → ℕ
 | .load _ => 1
 | .emit _ => 3
 | .cell _ _ _ _ => 1000*(N+1)^2+10*L
 | .equal _ _ _ => 100*(N+1)
 | .seq a b => 1+(a.time N L+b.time N L)
 | .loop _ b => (b.time N L+13)*N+22

def env (s : CState V) : Index → ℕ := fun i => s.nums (.idx i)

def result (s : CState V) (v : V × List Letter) : CState V :=
 {s with ctl := (false,v.1), output := v.2}

def Ready (S : Finset Index) (N : ℕ) (s : CState V) : Prop :=
 s.nums .size = N ∧ s.nums .addr = 0 ∧ s.nums .prod = 0 ∧ s.nums .tmp = 0 ∧
 (∀ i, s.nums (.idx i) ≤ N) ∧ (∀ i ∉ S, s.nums (.idx i) = 0 ∧ s.nums (.rem i) = 0)

@[simp] lemma ready_result {S N} (s : CState V) (v) : Ready S N (result s v) ↔ Ready S N s := Iff.rfl

@[simp] lemma env_result (s : CState V) (v) : env (result s v) = env s := rfl

@[simp] lemma result_result (s : CState V) (v w) : result (result s v) w = result s w := rfl

lemma ready_index {S N} (s : CState V) (hs : Ready S N s) (i : Index) (k : ℕ) (hk : k≤N) :
 Ready (insert i S) N (indexState (.idx i) (.rem i) N k s) := by
 rcases hs with ⟨hN,ha,hp,ht,hidx,hr⟩
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · simpa [indexState,Function.update] using hN
 · simpa [indexState,Function.update] using ha
 · simpa [indexState,Function.update] using hp
 · simpa [indexState,Function.update] using ht
 · intro j
   by_cases hji : j=i
   · subst j; simpa [indexState,Function.update] using hk
   · simpa [indexState,Function.update,hji] using hidx j
 · intro j hj
   have hh : j≠i ∧ j∉S := by simpa using hj
   simpa [indexState,Function.update,hh.1] using hr j hh.2

@[simp] lemma env_index (s : CState V) (i : Index) (N k) :
 env (indexState (.idx i) (.rem i) N k s) = Function.update (env s) i k := by
 funext j; by_cases h : j=i <;> simp [env,indexState,Function.update,h]

lemma equalCode_runs (i j : Index) (f : V → Bool → V) (s : CState V)
    (ha : s.nums .addr=0) (hp : s.nums .prod=0) (N : ℕ)
    (hi : s.nums (.idx i)≤N) (hj : s.nums (.idx j)≤N) :
 Runs (equalCode i j f) s (result s (f s.ctl.2 (s.nums (.idx i)==s.nums (.idx j)),s.output)) (100*(N+1)) := by
 let s₁ : CState V := {s with ctl := (false,f s.ctl.2 (decide (s.nums (.idx i)=s.nums (.idx j)))), nums := Function.update (Function.update s.nums .addr (s.nums (.idx i)-s.nums (.idx j))) .prod (s.nums (.idx j)-s.nums (.idx i))}
 let s₂ := (Atom.zero .addr).eval s₁
 have hc := compare_runs (.idx i) (.idx j) .addr .prod (by simp) (by simp) (by simp) (by decide) f s
 change Runs _ s s₁ _ at hc
 have h := hc.seq ((Runs.atom (.zero .addr) s₁).seq (Runs.atom (.zero .prod) s₂))
 have he : (Atom.zero .prod).eval s₂ = result s (f s.ctl.2 (s.nums (.idx i)==s.nums (.idx j)),s.output) := by
   apply CounterLang.State.ext
   · rfl
   · funext r; cases r <;> simp [s₂,s₁,Atom.eval,result,Function.update,ha,hp]
   · rfl
   · rfl
 rw [he] at h
 apply h.mono
 simp [s₂,s₁,Atom.cost,Atom.eval,Function.update,ha,hp]
 omega

lemma cell_runs (r : Symbol) (i j : Index) (f : V → Bool → V)
    (s : CState V) {S N} (hs : Ready S N s) :
 Runs (Program.compile (.cell r i j f)) s
   (result s ((Program.cell r i j f).eval N s.input (env s) (s.ctl.2,s.output)))
   (1000*(N+1)^2+10*s.input.length) := by
 have h := readCell_runs s (OrderedQuery.symbolIndex r).val i j (fun v a => f v (isOne a)) hs.2.1 hs.2.2.1 hs.2.2.2.1
 have he : s.nums .size=N := hs.1
 simp only [he] at h
 apply h.mono
 have hk : (OrderedQuery.symbolIndex r).val ≤ 8 := (OrderedQuery.symbolIndex r).isLt.le
 have hi := hs.2.2.2.2.1 i
 have hj := hs.2.2.2.2.1 j
 calc
  _ ≤ 16*8*N^2+16*N*N+6*8*N+8*8+16*N+6*N+16*N+10*s.input.length+101 := by gcongr
  _ ≤ _ := by nlinarith

lemma compile_runs (p : Program V) (S : Finset Index) (hw : p.WF S)
    (N : ℕ) (s : CState V) (hs : Ready S N s) :
 Runs p.compile s (result s (p.eval N s.input (env s) (s.ctl.2,s.output)))
   (p.time N s.input.length) := by
 induction p generalizing S s with
 | load f => exact Runs.atom (.load (fun c => (false,f c.2))) s
 | emit f =>
   exact (Runs.atom (.emit (fun c => f c.2)) s).seq
     (Runs.atom (.load (fun c => (false,c.2))) ((Atom.emit (fun c => f c.2)).eval s))
 | cell r i j f => exact cell_runs r i j f s hs
 | equal i j f => exact equalCode_runs i j f s hs.2.1 hs.2.2.1 N (hs.2.2.2.2.1 i) (hs.2.2.2.2.1 j)
 | seq a b iha ihb =>
   have ha := iha S hw.1 s hs
   have hb := ihb S hw.2 (result s (a.eval N s.input (env s) (s.ctl.2,s.output))) hs
   exact ha.seq hb
 | loop i b ih =>
   let e := env s
   let step := fun v k => b.eval N s.input (Function.update e i k) v
   let pref := fun k => (List.range k).foldl step (s.ctl.2,s.output)
   let st := fun k => result s (pref k)
   have hstep (k : ℕ) : pref (k+1) = step (pref k) k := by simp [pref,List.range_succ,step]
   have hbody (k : ℕ) (hk : k<N) :
       Runs b.compile (indexState (.idx i) (.rem i) N k (st k))
         (flag (indexState (.idx i) (.rem i) N k (st (k+1))) false) (b.time N s.input.length) := by
     have hr : Ready (insert i S) N (indexState (.idx i) (.rem i) N k (st k)) :=
       ready_index (st k) hs i k hk.le
     have h := ih (insert i S) hw.2 (indexState (.idx i) (.rem i) N k (st k)) hr
     rw [env_index] at h
     change Runs _ _ (result (indexState (.idx i) (.rem i) N k (st k)) (step (pref k) k)) _ at h
     rw [← hstep k] at h
     exact h
   have hi := hs.2.2.2.2.2 i hw.1
   have h := forRange_runs TableMachine.Reg.size (.idx i) (.rem i) (by simp) (by simp)
     b.compile st N (b.time N s.input.length)
     (by simpa [st,result] using hs.1)
     (by simpa [st,result] using hi.1) (by simpa [st,result] using hi.2)
     (by simpa [st,result] using hi.1) (by simpa [st,result] using hi.2)
     rfl hbody
   have hin : Runs (.atom (.load (fun c : Bool × V => (false,c.2)))) s (st 0) 1 := by
     simpa [st,pref,result,Atom.eval,Atom.cost] using Runs.atom (.load (fun c : Bool × V => (false,c.2))) s
   have total := hin.seq h
   convert total using 1 <;> first | rfl | (simp only [Program.time]; omega)

end

open CounterLang TableMachine

variable {V : Type}

abbrev Relation := Symbol → ℕ → ℕ → Bool

def readTable (N : ℕ) (w : List Letter) : Relation := fun r a b =>
 isOne w[((OrderedQuery.symbolIndex r).val*N+a)*N+b]?

def Program.interpret (N : ℕ) (rel : Relation) :
    Program V → (Index → ℕ) → V × List Letter → V × List Letter
 | .load f,_,s => (f s.1,s.2)
 | .emit f,_,s => (s.1,f s.1::s.2)
 | .cell r i j f,e,s => (f s.1 (rel r (e i) (e j)),s.2)
 | .equal i j f,e,s => (f s.1 (e i == e j),s.2)
 | .seq a b,e,s => b.interpret N rel e (a.interpret N rel e s)
 | .loop i b,e,s => (List.range N).foldl (fun s k => b.interpret N rel (Function.update e i k) s) s

lemma Program.eval_interpret (p : Program V) (N : ℕ) (w : List Letter) (e) (s) :
 p.eval N w e s = p.interpret N (readTable N w) e s := by
 induction p generalizing e s with
 | load _ => rfl
 | emit _ => rfl
 | cell _ _ _ _ => rfl
 | equal _ _ _ => rfl
 | seq a b iha ihb => simp only [Program.eval,Program.interpret,iha,ihb]
 | loop i b ih =>
   simp only [Program.eval,Program.interpret]
   congr 1
   funext s k
   exact ih _ _

lemma readTable_input {N} (S : OrderedQuery.Data N) (r : Symbol) (a b : Fin N) :
 readTable N (tableInput S) r a b = S.rel r a b := by
 rw [readTable,tableInput_lookup]
 cases h : S.rel r a b <;> decide +revert

lemma fold_emits {α : Type} (ls : List α) (step : V × List Letter → α → V × List Letter)
    (v : V) (chunk : α → List Letter)
    (h : ∀ a ∈ ls, ∀ out, step (v,out) a = (v,(chunk a).reverse++out)) (out) :
 ls.foldl step (v,out) = (v,(ls.flatMap chunk).reverse++out) := by
 induction ls generalizing out with
 | nil => rfl
 | cons a ls ih =>
   rw [List.foldl_cons,h a (by simp),ih (by intro b hb; exact h b (by simp [hb]))]
   simp [List.reverse_append,List.append_assoc]

lemma loop_emits (N : ℕ) (rel : Relation) (body : Program V) (i : Index)
    (e : Index → ℕ) (v : V) (chunk : ℕ → List Letter)
    (h : ∀ k<N, ∀ out, body.interpret N rel (Function.update e i k) (v,out) = (v,(chunk k).reverse++out))
    (out) :
 (Program.loop i body).interpret N rel e (v,out) =
   (v,((List.range N).flatMap chunk).reverse++out) := by
 exact fold_emits _ _ v chunk (by intro k hk; exact h k (List.mem_range.mp hk)) out

lemma Program.time_polynomial (p : Program V) :
 ∃ q : Polynomial ℕ, ∀ N, p.time N (8*(N*N)) = q.eval N := by
 induction p with
 | load f => exact ⟨1,by simp [Program.time]⟩
 | emit f => exact ⟨3,by simp [Program.time]⟩
 | cell r i j f => exact ⟨1000*(Polynomial.X+1)^2+80*Polynomial.X^2,by intro N; simp [Program.time]; ring⟩
 | equal i j f => exact ⟨100*(Polynomial.X+1),by simp [Program.time]⟩
 | seq a b iha ihb =>
   obtain ⟨p,hp⟩ := iha
   obtain ⟨q,hq⟩ := ihb
   exact ⟨1+(p+q),by intro N; simp [Program.time,hp,hq]⟩
 | loop i b ih =>
   obtain ⟨p,hp⟩ := ih
   exact ⟨(p+13)*Polynomial.X+22,by intro N; simp [Program.time,hp]⟩

end CPTSeparation.Bounded

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation.MatrixProgram

section

open Bounded TableMachine CounterLang

structure Control where
 active : Bool
 member : Bool
 test : Bool
 acc : Scalar
 deriving DecidableEq, Fintype

abbrev Prog := Bounded.Program Control

local infixr:60 " ;; " => Bounded.Program.seq

def ctrl (b : Bool) : Control := ⟨b,false,false,0⟩

def memberCode : Prog :=
 .cell .Cf .a .a (fun c b => {c with member := b}) ;;
 .cell .VB .t .a (fun c b => {c with member := c.member && b})

def coefficientStep : Prog :=
 .cell .Ed .x .x (fun c b => {c with test := b}) ;;
 .cell .I .a .x (fun c b => {c with test := c.test && b}) ;;
 .cell (.Z 1) .y .x (fun c b => {c with acc := c.acc + if c.test && b then 1 else 0}) ;;
 .cell (.Z 2) .y .x (fun c b => {c with acc := c.acc + if c.test && b then 2 else 0}) ;;
 .load (fun c => {c with test := false})

def coefficientCode : Prog :=
 .load (fun c => {c with acc := 0}) ;; .loop .x coefficientStep

def incidentStepX : Prog :=
 .cell .Ed .x .x (fun c b => {c with test := b}) ;;
 .cell .I .a .x (fun c b => {c with test := c.test && b}) ;;
 .cell .EB .y .x (fun c b => {c with test := c.test && b}) ;;
 .load (fun c => {c with active := c.active || (c.member && c.test),test := false})

def incidentStepA : Prog :=
 memberCode ;; .loop .x incidentStepX ;; .load (fun c => {c with member := false})

def incidentCode : Prog := .load (fun _ => ctrl false) ;; .loop .a incidentStepA

def normColumn : Prog := memberCode ;;
 .emit (fun c => some (if c.active && c.member then 1 else 0)) ;;
 .load (fun c => {c with member := false})

def lambdaColumn : Prog := memberCode ;; coefficientCode ;;
 .emit (fun c => some (if c.active && c.member then -c.acc else 0)) ;;
 .load (fun c => {c with member := false,acc := 0})

def muColumn : Prog :=
 .equal .z .y (fun c b => {c with test := b}) ;;
 .emit (fun c => some (if c.active && c.test then 1 else 0)) ;;
 .load (fun c => {c with test := false})

def normRowCode : Prog :=
 .cell .Cf .t .t (fun _ b => ctrl b) ;;
 .loop .a normColumn ;;
 .loop .z (.emit (fun _ => some 0)) ;;
 .emit (fun c => some (if c.active then 1 else 0)) ;;
 .emit (fun _ => none) ;;
 .load (fun _ => ctrl false)

def consRowCode : Prog :=
 incidentCode ;;
 .cell .Cf .t .t (fun c b => {c with active := c.active && b}) ;;
 .cell .Ed .y .y (fun c b => {c with active := c.active && b}) ;;
 .loop .a lambdaColumn ;;
 .loop .z muColumn ;;
 .emit (fun _ => some 0) ;;
 .emit (fun _ => none) ;;
 .load (fun _ => ctrl false)

def program : Prog :=
 .load (fun _ => ctrl false) ;;
 .loop .t normRowCode ;;
 .loop .t (.loop .y consRowCode)

lemma program_wf : program.WF ∅ := by
 simp [program,normRowCode,consRowCode,normColumn,lambdaColumn,muColumn,
   memberCode,coefficientCode,coefficientStep,incidentCode,incidentStepA,incidentStepX,
   Bounded.Program.WF]

def member (rel : Relation) (t a : ℕ) : Bool := rel .Cf a a && rel .VB t a

def contribution (rel : Relation) (y a x : ℕ) : Scalar :=
 if rel .Ed x x && rel .I a x then
   (if rel (.Z 1) y x then 1 else 0)+(if rel (.Z 2) y x then 2 else 0) else 0

def coefficient (N : ℕ) (rel : Relation) (y a : ℕ) : Scalar :=
 ((List.range N).map (contribution rel y a)).sum

def edgeTest (rel : Relation) (y a x : ℕ) : Bool :=
 rel .Ed x x && rel .I a x && rel .EB y x

def incident (N : ℕ) (rel : Relation) (t y : ℕ) : Bool :=
 (List.range N).any fun a => member rel t a && (List.range N).any (edgeTest rel y a)

def normChunk (N : ℕ) (rel : Relation) (t : ℕ) : List Letter :=
 (List.range N).map (fun a => some (if rel .Cf t t && member rel t a then 1 else 0)) ++
 List.replicate N (some 0) ++ [some (if rel .Cf t t then 1 else 0),none]

def consActive (N : ℕ) (rel : Relation) (t y : ℕ) : Bool :=
 (incident N rel t y && rel .Cf t t) && rel .Ed y y

def consChunk (N : ℕ) (rel : Relation) (t y : ℕ) : List Letter :=
 (List.range N).map (fun a => some (if consActive N rel t y && member rel t a then -coefficient N rel y a else 0)) ++
 (List.range N).map (fun z => some (if consActive N rel t y && (z==y) then 1 else 0)) ++ [some 0,none]

def matrix (N : ℕ) (rel : Relation) : List Letter :=
 (List.range N).flatMap (normChunk N rel) ++
 (List.range N).flatMap (fun t => (List.range N).flatMap (consChunk N rel t))

end

section

open Bounded TableMachine CounterLang

lemma interp_seq {V} (a b : Bounded.Program V) (N : ℕ) (rel : Relation) (e) (s) :
 (Bounded.Program.seq a b).interpret N rel e s = b.interpret N rel e (a.interpret N rel e s) := rfl

lemma interp_load {V} (f : V → V) (N : ℕ) (rel : Relation) (e) (s) :
 (Bounded.Program.load f).interpret N rel e s = (f s.1,s.2) := rfl

lemma interp_cell {V} (r i j) (f : V → Bool → V) (N : ℕ) (rel : Relation) (e) (s) :
 (Bounded.Program.cell r i j f).interpret N rel e s = (f s.1 (rel r (e i) (e j)),s.2) := rfl

lemma interp_emit {V} (f : V → Letter) (N : ℕ) (rel : Relation) (e) (s) :
 (Bounded.Program.emit f).interpret N rel e s = (s.1,f s.1::s.2) := rfl

lemma memberCode_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (c : Control) (out) :
 memberCode.interpret N rel e (c,out) = ({c with member := member rel (e .t) (e .a)},out) := rfl

lemma coefficientStep_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act mem : Bool) (acc : Scalar) (out) :
 coefficientStep.interpret N rel e (⟨act,mem,false,acc⟩,out) =
   (⟨act,mem,false,acc+contribution rel (e .y) (e .a) (e .x)⟩,out) := by
 simp only [coefficientStep,Bounded.Program.interpret,contribution]
 by_cases h : (rel .Ed (e .x) (e .x) && rel .I (e .a) (e .x)) = true <;>
   simp only [Bool.and_eq_true] at h ⊢ <;> simp [h,add_assoc]

lemma coefficient_fold_spec (N : ℕ) (rel : Relation) (e : Index → ℕ)
    (ls : List ℕ) (act mem : Bool) (acc : Scalar) (out) :
 ls.foldl (fun s k => coefficientStep.interpret N rel (Function.update e .x k) s)
    (⟨act,mem,false,acc⟩,out) =
   (⟨act,mem,false,acc+(ls.map (contribution rel (e .y) (e .a))).sum⟩,out) := by
 induction ls generalizing acc with
 | nil => simp
 | cons a ls ih =>
   rw [List.foldl_cons,coefficientStep_spec]
   simp only [Function.update_self,Function.update_of_ne (show Index.y ≠ .x by decide),
      Function.update_of_ne (show Index.a ≠ .x by decide)]
   rw [ih]
   simp [add_assoc]

lemma coefficientCode_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act mem : Bool) (acc : Scalar) (out) :
 coefficientCode.interpret N rel e (⟨act,mem,false,acc⟩,out) =
   (⟨act,mem,false,coefficient N rel (e .y) (e .a)⟩,out) := by
 simp only [coefficientCode,Bounded.Program.interpret]
 exact (coefficient_fold_spec N rel e (List.range N) act mem 0 out).trans (by simp [coefficient])

lemma incidentStepX_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act mem : Bool) (out) :
 incidentStepX.interpret N rel e (⟨act,mem,false,0⟩,out) =
   (⟨act || (mem && edgeTest rel (e .y) (e .a) (e .x)),mem,false,0⟩,out) := rfl

lemma incident_fold_x (N : ℕ) (rel : Relation) (e : Index → ℕ)
    (ls : List ℕ) (act mem : Bool) (out) :
 ls.foldl (fun s k => incidentStepX.interpret N rel (Function.update e .x k) s)
    (⟨act,mem,false,0⟩,out) =
   (⟨act || (mem && ls.any (edgeTest rel (e .y) (e .a))),mem,false,0⟩,out) := by
 induction ls generalizing act with
 | nil => simp
 | cons a ls ih =>
   rw [List.foldl_cons,incidentStepX_spec]
   simp only [Function.update_self,Function.update_of_ne (show Index.y ≠ .x by decide),
      Function.update_of_ne (show Index.a ≠ .x by decide)]
   rw [ih]
   cases act <;> cases mem <;> simp []

lemma incidentStepA_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act : Bool) (out) :
 incidentStepA.interpret N rel e (ctrl act,out) =
   (ctrl (act || (member rel (e .t) (e .a) && (List.range N).any (edgeTest rel (e .y) (e .a)))),out) := by
 simp only [incidentStepA,interp_seq,memberCode_spec,ctrl]

 simp only [Bounded.Program.interpret]
 rw [incident_fold_x]

lemma incident_fold_a (N : ℕ) (rel : Relation) (e : Index → ℕ)
    (ls : List ℕ) (act : Bool) (out) :
 ls.foldl (fun s k => incidentStepA.interpret N rel (Function.update e .a k) s)
    (ctrl act,out) =
   (ctrl (act || ls.any (fun a => member rel (e .t) a &&
     (List.range N).any (edgeTest rel (e .y) a))),out) := by
 induction ls generalizing act with
 | nil => simp
 | cons a ls ih =>
   rw [List.foldl_cons,incidentStepA_spec]
   simp only [Function.update_self,Function.update_of_ne (show Index.y ≠ .a by decide),
      Function.update_of_ne (show Index.t ≠ .a by decide)]
   rw [ih]
   simp [Bool.or_assoc]

lemma incidentCode_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (c : Control) (out) :
 incidentCode.interpret N rel e (c,out) =
   (ctrl (incident N rel (e .t) (e .y)),out) := by
 simp only [incidentCode,Bounded.Program.interpret]
 rw [incident_fold_a]
 simp [incident]

lemma normColumn_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act : Bool) (out) :
 normColumn.interpret N rel e (ctrl act,out) =
   (ctrl act,some (if act && member rel (e .t) (e .a) then 1 else 0)::out) := by
 simp only [normColumn,Bounded.Program.interpret,memberCode_spec]
 rfl

lemma lambdaColumn_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act : Bool) (out) :
 lambdaColumn.interpret N rel e (ctrl act,out) =
   (ctrl act,some (if act && member rel (e .t) (e .a) then -coefficient N rel (e .y) (e .a) else 0)::out) := by
 simp only [lambdaColumn,interp_seq,memberCode_spec,ctrl]
 rw [coefficientCode_spec]
 rfl

lemma muColumn_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act : Bool) (out) :
 muColumn.interpret N rel e (ctrl act,out) =
   (ctrl act,some (if act && (e .z == e .y) then 1 else 0)::out) := rfl

lemma normRowCode_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (c : Control) (out) :
 normRowCode.interpret N rel e (c,out) =
   (ctrl false,(normChunk N rel (e .t)).reverse++out) := by
 have ha := loop_emits N rel normColumn .a e (ctrl (rel .Cf (e .t) (e .t)))
   (fun a => [some (if rel .Cf (e .t) (e .t) && member rel (e .t) a then 1 else 0)])
   (by intro k hk o; simpa [Function.update] using normColumn_spec N rel (Function.update e .a k) (rel .Cf (e .t) (e .t)) o) out
 have hz (o) := loop_emits N rel (.emit (fun _ : Control => some 0)) .z e (ctrl (rel .Cf (e .t) (e .t)))
   (fun _ => [some 0]) (by intro k hk z; rfl) o
 simp only [normRowCode,interp_seq,interp_cell]
 rw [ha,hz]
 simp [interp_emit,interp_load,normChunk,List.reverse_append,List.append_assoc,← List.map_eq_flatMap,ctrl]

lemma consRowCode_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (c : Control) (out) :
 consRowCode.interpret N rel e (c,out) =
   (ctrl false,(consChunk N rel (e .t) (e .y)).reverse++out) := by
 let act := consActive N rel (e .t) (e .y)
 have ha (o) := loop_emits N rel lambdaColumn .a e (ctrl act)
   (fun a => [some (if act && member rel (e .t) a then -coefficient N rel (e .y) a else 0)])
   (by intro k hk z; simpa [Function.update] using lambdaColumn_spec N rel (Function.update e .a k) act z) o
 have hz (o) := loop_emits N rel muColumn .z e (ctrl act)
   (fun z => [some (if act && (z==e .y) then 1 else 0)])
   (by intro k hk z; simpa [Function.update] using muColumn_spec N rel (Function.update e .z k) act z) o
 simp only [consRowCode,interp_seq,incidentCode_spec,interp_cell,ctrl]
 dsimp [ctrl,act,consActive] at ha hz
 rw [ha,hz]
 simp [interp_emit,interp_load,consChunk,consActive,List.reverse_append,List.append_assoc,← List.map_eq_flatMap]

lemma program_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (c : Control) (out) :
 program.interpret N rel e (c,out) = (ctrl false,(matrix N rel).reverse++out) := by
 have hn := loop_emits N rel normRowCode .t e (ctrl false) (normChunk N rel)
   (by intro k hk o; simpa [Function.update] using normRowCode_spec N rel (Function.update e .t k) (ctrl false) o) out
 have hc (o) := loop_emits N rel (.loop .y consRowCode) .t e (ctrl false)
   (fun t => (List.range N).flatMap (consChunk N rel t))
   (by
     intro t ht o
     apply loop_emits
     intro y hy z
     simpa [Function.update] using consRowCode_spec N rel
       (Function.update (Function.update e .t t) .y y) (ctrl false) z) o
 simp only [program,interp_seq,interp_load]
 rw [hn,hc]
 simp [matrix,List.reverse_append,List.append_assoc]

end

open Bounded TableMachine

lemma range_eq_finRange_map (N : ℕ) : List.range N = (List.finRange N).map Fin.val := by
 apply List.ext_getElem
 · simp
 · intro i hi hj
   simp

lemma range_map_eq {α} (N : ℕ) (f : ℕ → α) :
 (List.range N).map f = List.ofFn (fun i : Fin N => f i) := by
 rw [range_eq_finRange_map,List.map_map, List.ofFn_eq_map]
 rfl

lemma range_flatMap_eq {α} (N : ℕ) (f : ℕ → List α) :
 (List.range N).flatMap f = (List.finRange N).flatMap (fun i : Fin N => f i) := by
 rw [range_eq_finRange_map,List.flatMap_map]

lemma ofFn_addCases {α : Type} {m n : ℕ} (f : Fin m → α) (g : Fin n → α) :
 List.ofFn (Fin.addCases f g) = List.ofFn f ++ List.ofFn g := by
 have he : Fin.addCases f g = Fin.append f g := by
   funext i
   refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
 rw [he,List.ofFn_fin_append]

lemma sum_scalar_three (f : Scalar → Scalar) : (∑ δ, f δ) = f 0+f 1+f 2 := by
 have h : (Finset.univ : Finset Scalar) = {0,1,2} := by decide
 change Finset.sum Finset.univ f = _
 rw [h]
 rw [Finset.sum_insert (by decide : (0:Scalar) ∉ ({1,2} : Finset Scalar)),
   Finset.sum_insert (by decide : (1:Scalar) ∉ ({2} : Finset Scalar)),Finset.sum_singleton]
 ring

variable {N : ℕ} (S : OrderedQuery.Data N) (rel : Relation)

variable (reads : ∀ (r : Symbol) (a b : Fin N), rel r a b = S.rel r a b)

include reads

lemma contribution_eq (y a x : Fin N) :
 contribution rel y a x = if S.rel .Ed x x ∧ S.rel .I a x then
   ∑ δ : Scalar, if S.rel (.Z δ) y x then δ else 0 else 0 := by
 simp only [contribution,reads,Bool.and_eq_true,sum_scalar_three]
 simp

lemma coefficient_eq_ordered (y a : Fin N) : coefficient N rel y a = OrderedQuery.coefficient S y a := by
 rw [coefficient,range_map_eq]
 simp only [contribution_eq S rel reads,List.sum_ofFn,OrderedQuery.coefficient]

lemma incident_eq_ordered (t y : Fin N) : incident N rel t y = OrderedQuery.incident S t y := by
 simp only [incident,range_eq_finRange_map,List.any_map,Function.comp_def,member,edgeTest,
   reads,OrderedQuery.incident]

lemma normChunk_eq (t : Fin N) : normChunk N rel t =
 (SerialGaussian.Row.encode (OrderedQuery.normalizationRow S t)).coeff.map some ++
   [some (OrderedQuery.normalizationRow S t).rhs,none] := by
 have hr : ∀ (a : Fin N), member rel t a = (S.rel .Cf a a && S.rel .VB t a) := by
   intro a; simp [member,reads]
 simp only [normChunk,reads,range_map_eq,SerialGaussian.Row.encode,OrderedQuery.normalizationRow]
 by_cases ht : S.rel .Cf t t = true
 · simp only [ht,ite_true,Bool.true_and,hr]
   simp [ofFn_addCases,List.map_ofFn,List.map_append,Function.comp_def]
 · have hf : S.rel .Cf t t = false := Bool.eq_false_iff.mpr ht
   simp [hf,]

lemma consActive_eq (t y : Fin N) : consActive N rel t y =
 (S.rel .Cf t t && S.rel .Ed y y && OrderedQuery.incident S t y) := by
 rw [consActive,incident_eq_ordered S rel reads,reads,reads]
 cases S.rel .Cf t t <;> cases S.rel .Ed y y <;> cases OrderedQuery.incident S t y <;> rfl

lemma consChunk_eq (t y : Fin N) : consChunk N rel t y =
 (SerialGaussian.Row.encode (OrderedQuery.consistencyRow S t y)).coeff.map some ++
   [some (OrderedQuery.consistencyRow S t y).rhs,none] := by
 have hr : ∀ (a : Fin N), member rel t a = (S.rel .Cf a a && S.rel .VB t a) := by
   intro a; simp [member,reads]
 simp only [consChunk,consActive_eq S rel reads,range_map_eq,
   SerialGaussian.Row.encode,OrderedQuery.consistencyRow]
 by_cases ht : (S.rel .Cf t t && S.rel .Ed y y && OrderedQuery.incident S t y) = true
 · simp only [ht,ite_true,Bool.true_and,hr,coefficient_eq_ordered S rel reads]
   simp [ofFn_addCases,List.map_append,List.map_ofFn,Function.comp_def,beq_iff_eq,Fin.val_inj]
 · have hf : (S.rel .Cf t t && S.rel .Ed y y && OrderedQuery.incident S t y) = false := Bool.eq_false_iff.mpr ht
   simp [hf,]

lemma matrix_eq_payload : matrix N rel = SerialGaussian.payload (SerialGaussian.queryRows S) := by
 simp only [matrix,range_flatMap_eq,normChunk_eq S rel reads,consChunk_eq S rel reads,
   SerialGaussian.queryRows,OrderedQuery.rows,SerialGaussian.payload,List.map_append,
   List.flatMap_append,List.flatMap_map,List.map_flatMap,List.flatMap_assoc]
 rfl

omit reads in
lemma matrix_input {N : ℕ} (S : OrderedQuery.Data N) :
 matrix N (readTable N (tableInput S)) = SerialGaussian.payload (SerialGaussian.queryRows S) :=
 matrix_eq_payload S _ (readTable_input S)

end CPTSeparation.MatrixProgram

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.QueryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CPTSeparation.TableMachine

open CounterLang

variable {V : Type}

local infixr:60 " ;; " => CounterLang.Program.seq

def headerConsume : Prog V := .atom (.consume (fun c a => (a == some none,c.2)))

def headerBody : Prog V :=
 .atom (.inc .size) ;; .atom (.inc .width) ;; .atom (.inc .width) ;; headerConsume

def headerLoop : Prog V := .loop (fun c => c.1) headerBody

def header : Prog V := headerConsume ;; headerLoop

def headerNums (k : ℕ) : Reg → ℕ := fun r => match r with
 | .size => k
 | .width => k+k
 | _ => 0

def headerState (v : V) (k n : ℕ) (w out : List Letter) : CState V :=
 ⟨(n != 0,v),headerNums k, if n = 0 then w else List.replicate (n-1) none ++ some 0 :: w,out⟩

lemma headerBody_runs (v : V) (k n : ℕ) (w out : List Letter) :
 Runs (headerBody (V := V)) (headerState v k (n+1) w out) (headerState v (k+1) n w out) 7 := by
 let s := headerState v k (n+1) w out
 have h := (Runs.atom (.inc .size) s).seq
   ((Runs.atom (.inc .width) ((Atom.inc .size).eval s)).seq
   ((Runs.atom (.inc .width) ((Atom.inc .width).eval ((Atom.inc .size).eval s))).seq
    (Runs.atom (.consume (fun c a => (a == some none,c.2)))
      ((Atom.inc .width).eval ((Atom.inc .width).eval ((Atom.inc .size).eval s))))))
 have he : (Atom.consume (fun c a => (a == some none,c.2))).eval
     ((Atom.inc .width).eval ((Atom.inc .width).eval ((Atom.inc .size).eval s))) =
     headerState v (k+1) n w out := by
   cases n <;> simp [s,headerState,Atom.eval,headerNums,Function.update,List.replicate_succ,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
   all_goals funext r; cases r <;> simp [headerNums,Function.update] ; omega
 simpa only [headerBody,headerConsume,Atom.cost,he] using h

lemma headerLoop_runs (v : V) (k n : ℕ) (w out : List Letter) :
 Runs headerLoop (headerState v k n w out)
   (⟨(false,v),headerNums (k+n),w,out⟩ : CState V) (8*n+1) := by
 induction n generalizing k with
 | zero =>
   simpa [headerState,headerLoop] using (Runs.loop_false (a := headerBody) (f := fun c : Bool × V => c.1)
      (s := headerState v k 0 w out) rfl)
 | succ n ih =>
   have h := Runs.loop_true (f := fun c : Bool × V => c.1)
     (s := headerState v k (n+1) w out) (by simp [headerState])
     (headerBody_runs v k n w out) (ih (k+1))
   simpa only [headerLoop, show k+1+n = k+(n+1) by omega,
     show 1+(7+(8*n+1)) = 8*(n+1)+1 by omega] using h

lemma header_runs (v : V) (n : ℕ) (w out : List Letter) :
 Runs header (⟨(false,v),headerNums 0,List.replicate n none ++ some 0::w,out⟩ : CState V)
   (⟨(false,v),headerNums n,w,out⟩ : CState V) (8*n+3) := by
 let s : CState V := ⟨(false,v),headerNums 0,List.replicate n none ++ some 0::w,out⟩
 have he : (Atom.consume (fun c a => (a == some none,c.2))).eval s = headerState v 0 n w out := by
   cases n <;> simp [s,headerState,Atom.eval,List.replicate_succ]
 have hc : Runs headerConsume s (headerState v 0 n w out) 1 := by
   simpa only [headerConsume,he,Atom.cost] using Runs.atom (.consume (fun c a => (a == some none,c.2))) s
 have h := hc.seq (headerLoop_runs v 0 n w out)
 simpa only [header,s,Nat.zero_add,show 1+(1+(8*n+1)) = 8*n+3 by omega] using h

end CPTSeparation.TableMachine

namespace CPTSeparation.StackLang

open Macros

variable {K L α σ τ : Type} [DecidableEq K] [DecidableEq L]

@[simp] lemma update_sum_left (f : K → List α) (g : L → List α) (k : K) (xs : List α) :
 Function.update (Sum.elim f g) (.inl k) xs = Sum.elim (Function.update f k xs) g := by
 funext j; cases j <;> simp [Function.update]

@[simp] lemma update_sum_right (f : K → List α) (g : L → List α) (k : L) (xs : List α) :
 Function.update (Sum.elim f g) (.inr k) xs = Sum.elim f (Function.update g k xs) := by
 funext j; cases j <;> simp [Function.update]

def leftStore (s : SStore K α σ) (v : τ) (g : L → List α) : SStore (K ⊕ L) α (σ × τ) :=
 ⟨(s.control.1,(s.control.2,v)),Sum.elim s.stk g⟩

def Action.frameLeft : Action (fun _ : K => α) (Option α × σ) →
 Action (fun _ : K ⊕ L => α) (Option α × (σ × τ))
 | .done => .done
 | .push k f a => .push (.inl k) (fun c => f (c.1,c.2.1)) a.frameLeft
 | .peek k f a => .peek (.inl k) (fun c b => let r := f (c.1,c.2.1) b; (r.1,(r.2,c.2.2))) a.frameLeft
 | .pop k f a => .pop (.inl k) (fun c b => let r := f (c.1,c.2.1) b; (r.1,(r.2,c.2.2))) a.frameLeft
 | .load f a => .load (fun c => let r := f (c.1,c.2.1); (r.1,(r.2,c.2.2))) a.frameLeft
 | .branch f a b => .branch (fun c => f (c.1,c.2.1)) a.frameLeft b.frameLeft

lemma Action.run_frameLeft (a : Action (fun _ : K => α) (Option α × σ))
 (s : SStore K α σ) (v : τ) (g : L → List α) :
 a.frameLeft.run (leftStore s v g) = leftStore (a.run s) v g := by
 induction a generalizing s with
 | done => rfl
 | push k f a ih => simpa only [frameLeft,run,leftStore,Sum.elim_inl,update_sum_left,Prod.mk.eta] using ih ⟨s.control,Function.update s.stk k (f s.control::s.stk k)⟩
 | peek k f a ih => simpa only [frameLeft,run,leftStore,Sum.elim_inl,update_sum_left,Prod.mk.eta] using ih ⟨f s.control (s.stk k).head?,s.stk⟩
 | pop k f a ih => simpa only [frameLeft,run,leftStore,Sum.elim_inl,update_sum_left,Prod.mk.eta] using ih ⟨f s.control (s.stk k).head?,Function.update s.stk k (s.stk k).tail⟩
 | load f a ih => simpa only [frameLeft,run,leftStore,Sum.elim_inl,update_sum_left,Prod.mk.eta] using ih ⟨f s.control,s.stk⟩
 | branch f a b iha ihb =>
   cases h : f s.control
   · simpa only [frameLeft,run,leftStore,Prod.mk.eta,h,Bool.false_eq_true,ite_false] using ihb s
   · simpa only [frameLeft,run,leftStore,Prod.mk.eta,h,ite_true] using iha s

def Program.frameLeft : SProgram K α σ → SProgram (K ⊕ L) α (σ × τ)
 | .atom a => .atom a.frameLeft
 | .seq a b => .seq a.frameLeft b.frameLeft
 | .cond f a b => .cond (fun c => f (c.1,c.2.1)) a.frameLeft b.frameLeft
 | .loop f a => .loop (fun c => f (c.1,c.2.1)) a.frameLeft

noncomputable def Exec.frameLeft {p : SProgram K α σ} {s t} {n} (h : Exec p s n t)
 (v : τ) (g : L → List α) : Exec p.frameLeft (leftStore s v g) n (leftStore t v g) := by
 induction h with
 | atom a s => simpa only [Program.frameLeft,Action.run_frameLeft] using Exec.atom a.frameLeft (leftStore s v g)
 | seq ha hb iha ihb => exact .seq iha ihb
 | cond_true hf ha ih => exact .cond_true hf ih
 | cond_false hf ha ih => exact .cond_false hf ih
 | loop_false hf => exact .loop_false hf
 | loop_true hf ha hb iha ihb => exact .loop_true hf iha ihb

lemma Runs.frameLeft {p : SProgram K α σ} {s t} {n} (h : Runs p s t n)
 (v : τ) (g : L → List α) : Runs p.frameLeft (leftStore s v g) (leftStore t v g) n := by
 obtain ⟨m,hm,⟨h⟩⟩ := h
 exact ⟨m,hm,⟨h.frameLeft v g⟩⟩

def rightStore (s : SStore K α σ) (v : τ) (g : L → List α) : SStore (L ⊕ K) α (τ × σ) :=
 ⟨(s.control.1,(v,s.control.2)),Sum.elim g s.stk⟩

def Action.frameRight : Action (fun _ : K => α) (Option α × σ) →
 Action (fun _ : L ⊕ K => α) (Option α × (τ × σ))
 | .done => .done
 | .push k f a => .push (.inr k) (fun c => f (c.1,c.2.2)) a.frameRight
 | .peek k f a => .peek (.inr k) (fun c b => let r := f (c.1,c.2.2) b; (r.1,(c.2.1,r.2))) a.frameRight
 | .pop k f a => .pop (.inr k) (fun c b => let r := f (c.1,c.2.2) b; (r.1,(c.2.1,r.2))) a.frameRight
 | .load f a => .load (fun c => let r := f (c.1,c.2.2); (r.1,(c.2.1,r.2))) a.frameRight
 | .branch f a b => .branch (fun c => f (c.1,c.2.2)) a.frameRight b.frameRight

lemma Action.run_frameRight (a : Action (fun _ : K => α) (Option α × σ))
 (s : SStore K α σ) (v : τ) (g : L → List α) :
 a.frameRight.run (rightStore s v g) = rightStore (a.run s) v g := by
 induction a generalizing s with
 | done => rfl
 | push k f a ih => simpa only [frameRight,run,rightStore,Sum.elim_inr,update_sum_right,Prod.mk.eta] using ih ⟨s.control,Function.update s.stk k (f s.control::s.stk k)⟩
 | peek k f a ih => simpa only [frameRight,run,rightStore,Sum.elim_inr,update_sum_right,Prod.mk.eta] using ih ⟨f s.control (s.stk k).head?,s.stk⟩
 | pop k f a ih => simpa only [frameRight,run,rightStore,Sum.elim_inr,update_sum_right,Prod.mk.eta] using ih ⟨f s.control (s.stk k).head?,Function.update s.stk k (s.stk k).tail⟩
 | load f a ih => simpa only [frameRight,run,rightStore,Sum.elim_inr,update_sum_right,Prod.mk.eta] using ih ⟨f s.control,s.stk⟩
 | branch f a b iha ihb =>
   cases h : f s.control
   · simpa only [frameRight,run,rightStore,Prod.mk.eta,h,Bool.false_eq_true,ite_false] using ihb s
   · simpa only [frameRight,run,rightStore,Prod.mk.eta,h,ite_true] using iha s

def Program.frameRight : SProgram K α σ → SProgram (L ⊕ K) α (τ × σ)
 | .atom a => .atom a.frameRight
 | .seq a b => .seq a.frameRight b.frameRight
 | .cond f a b => .cond (fun c => f (c.1,c.2.2)) a.frameRight b.frameRight
 | .loop f a => .loop (fun c => f (c.1,c.2.2)) a.frameRight

noncomputable def Exec.frameRight {p : SProgram K α σ} {s t} {n} (h : Exec p s n t)
 (v : τ) (g : L → List α) : Exec p.frameRight (rightStore s v g) n (rightStore t v g) := by
 induction h with
 | atom a s => simpa only [Program.frameRight,Action.run_frameRight] using Exec.atom a.frameRight (rightStore s v g)
 | seq ha hb iha ihb => exact .seq iha ihb
 | cond_true hf ha ih => exact .cond_true hf ih
 | cond_false hf ha ih => exact .cond_false hf ih
 | loop_false hf => exact .loop_false hf
 | loop_true hf ha hb iha ihb => exact .loop_true hf iha ihb

lemma Runs.frameRight {p : SProgram K α σ} {s t} {n} (h : Runs p s t n)
 (v : τ) (g : L → List α) : Runs p.frameRight (rightStore s v g) (rightStore t v g) n := by
 obtain ⟨m,hm,⟨h⟩⟩ := h
 exact ⟨m,hm,⟨h.frameRight v g⟩⟩

end CPTSeparation.StackLang

namespace CPTSeparation.QueryMachine

open StackLang StackLang.Macros

abbrev Letter := CounterLang.Letter

abbrev LeftReg := CounterLang.Reg TableMachine.Reg

abbrev Reg := LeftReg ⊕ GaussMachine.Reg

abbrev Local := (Bool × MatrixProgram.Control) × GaussMachine.Local

abbrev Prog := SProgram Reg Letter Local

def initialLocal : Local := ((false,MatrixProgram.ctrl false),(none,GaussMachine.ctrl 0 true))

def cs (n : ℕ) (input output : List Letter) : TableMachine.CState MatrixProgram.Control :=
 ⟨(false,MatrixProgram.ctrl false),TableMachine.headerNums n,input,output⟩

def combined (s : TableMachine.CState MatrixProgram.Control) (c : GaussMachine.Control)
 (d : GaussMachine.Data) : SStore Reg Letter Local := leftStore s.encode (none,c) d.tapes

def build : TableMachine.Prog MatrixProgram.Control :=
 .seq TableMachine.header MatrixProgram.program.compile

def transfers : Prog :=
 .seq (moveRev (.inl .output) (.inr .mat) (fun _ a => a))
   (moveRev (.inl (.reg .width)) (.inr .width) (fun _ a => a))

def finish : Prog :=
 .seq (clear (.inl .input))
 (.seq (clear (.inl (.reg .size)))
 (.atom (.load (fun _ => (none,initialLocal)) .done)))

def program : Prog :=
 .seq build.compile.frameLeft
 (.seq transfers (.seq GaussMachine.solver.frameRight finish))

def finalStore (b : Bool) : SStore Reg Letter Local :=
 state initialLocal none (Function.update (fun _ => []) (.inr .output) (GaussMachine.boolCode b))

lemma cs_ready (n : ℕ) (input output : List Letter) :
 Bounded.Ready ∅ n (cs n input output) := by
 simp [Bounded.Ready,cs,TableMachine.headerNums]

lemma build_runs {N} (S : OrderedQuery.Data N) :
 CounterLang.Runs build (cs 0 (TableMachine.code ⟨N,S⟩) [])
   (cs N (TableMachine.tableInput S) (SerialGaussian.payload (SerialGaussian.queryRows S)).reverse)
   (8*N+4+MatrixProgram.program.time N (TableMachine.tableInput S).length) := by
 have hh := TableMachine.header_runs (MatrixProgram.ctrl false) N (TableMachine.tableInput S) []
 have hb := Bounded.compile_runs MatrixProgram.program ∅ MatrixProgram.program_wf N
   (cs N (TableMachine.tableInput S) []) (cs_ready _ _ _)
 rw [Bounded.Program.eval_interpret,MatrixProgram.program_spec] at hb
 simp only [cs, MatrixProgram.matrix_input, List.append_nil] at hb
 have h := hh.seq hb
 convert h using 1 <;> first | rfl | omega

lemma transfers_runs (s : TableMachine.CState MatrixProgram.Control) (n : ℕ) (xs : List Letter)
 (hs : s.output = xs.reverse) (hw : s.nums .width=n) :
 Runs transfers (combined s (GaussMachine.ctrl 0 true) {})
   (combined {s with output := [], nums := Function.update s.nums .width 0}
     (GaussMachine.ctrl 0 true) {mat := xs,width := List.replicate n none})
   (2*xs.length+2*n+7) := by
 let d : GaussMachine.Data := {}
 let w := Sum.elim s.data.tapes d.tapes
 have h₁ := moveRev_runs (.inl CounterLang.Reg.output : Reg) (.inr .mat) (by simp)
   (fun (_ : Local) a => a) (s.ctl,(none,GaussMachine.ctrl 0 true)) none w xs.reverse []
 have h₂ := moveRev_runs (.inl (CounterLang.Reg.reg TableMachine.Reg.width) : Reg) (.inr .width)
   (by simp) (fun (_ : Local) a => a) (s.ctl,(none,GaussMachine.ctrl 0 true)) none
   (Sum.elim ({s.data with output := []}).tapes ({mat := xs} : GaussMachine.Data).tapes)
   (List.replicate n none) []
 have h₁' : Runs (moveRev (.inl .output : Reg) (.inr .mat) (fun (_ : Local) a => a))
   (combined s (GaussMachine.ctrl 0 true) {})
   (combined {s with output := []} (GaussMachine.ctrl 0 true) {mat := xs})
   (2*xs.length+3) := by
   simpa [w,d,combined,leftStore,CounterLang.State.encode,CounterLang.State.data,state,
     hs] using h₁
 have h₂' : Runs (moveRev (.inl (.reg .width) : Reg) (.inr .width) (fun (_ : Local) a => a))
   (combined {s with output := []} (GaussMachine.ctrl 0 true) {mat := xs})
   (combined {s with output := [],nums := Function.update s.nums .width 0}
     (GaussMachine.ctrl 0 true) {mat := xs,width := List.replicate n none}) (2*n+3) := by
   simpa [combined,leftStore,CounterLang.State.encode,CounterLang.State.data,state,
    CounterLang.unary_update,←hw,CounterLang.unary] using h₂
 convert h₁'.seq h₂' using 1 <;> first | rfl | omega

lemma solver_framed {n} (s : TableMachine.CState MatrixProgram.Control)
 (rs : List (SerialGaussian.Row n)) :
 Runs GaussMachine.solver.frameRight
   (combined s (GaussMachine.ctrl 0 true) {mat := SerialGaussian.payload rs,width := List.replicate n none})
   (combined s (GaussMachine.ctrl 0 (SerialGaussian.solve rs)) {output := GaussMachine.boolCode (SerialGaussian.solve rs)})
   (300*(rs.length+1)*(n+3)^2) := by
 exact (GaussMachine.solver_runs {} rs).frameRight s.ctl s.data.tapes

lemma finish_runs (n : ℕ) (input : List Letter) (b : Bool) :
 Runs finish
   (combined {cs n input [] with nums := Function.update (TableMachine.headerNums n) .width 0}
     (GaussMachine.ctrl 0 b) {output := GaussMachine.boolCode b})
   (finalStore b) (2*input.length+2*n+9) := by
 let s := {cs n input [] with nums := Function.update (TableMachine.headerNums n) .width 0}
 let d : GaussMachine.Data := {output := GaussMachine.boolCode b}
 let w := Sum.elim s.data.tapes d.tapes
 let v : Local := (s.ctl,(none,GaussMachine.ctrl 0 b))
 have h₁ := clear_runs (.inl CounterLang.Reg.input : Reg) v none w input
 have h₂ := clear_runs (.inl (CounterLang.Reg.reg TableMachine.Reg.size) : Reg) v none
   (Function.update w (.inl .input) []) (List.replicate n none)
 have h₁' : Runs (clear (.inl CounterLang.Reg.input : Reg)) (combined s (GaussMachine.ctrl 0 b) d)
   (state v none (Function.update w (.inl .input) [])) (2*input.length+3) := by
   simpa [w,v,combined,leftStore,CounterLang.State.encode,CounterLang.State.data,state,s,cs] using h₁
 have h₂' : Runs (clear (.inl (CounterLang.Reg.reg TableMachine.Reg.size) : Reg))
   (state v none (Function.update w (.inl .input) []))
   (state v none (Function.update (fun _ => []) (.inr .output) (GaussMachine.boolCode b))) (2*n+3) := by
   convert h₂ using 1
   · refine Store.ext' (by rfl) ?_
     funext k; cases k with
     | inl k => cases k with
       | reg r => cases r <;> simp [state,w,s,CounterLang.State.data,CounterLang.Data.tapes,CounterLang.unary,cs,TableMachine.headerNums,Function.update]
       | _ => simp [state,w,s,CounterLang.State.data,CounterLang.Data.tapes,cs]
     | inr k => simp [state,w]
   · refine Store.ext' (by rfl) ?_
     funext k; cases k with
     | inl k => cases k with
       | reg r => cases r <;> simp [state,w,s,CounterLang.State.data,CounterLang.Data.tapes,CounterLang.unary,cs,TableMachine.headerNums,Function.update]
       | _ => simp [state,w,s,CounterLang.State.data,CounterLang.Data.tapes,cs,Function.update]
     | inr k => cases k <;> simp [state,w,d,GaussMachine.Data.tapes,Function.update]
   · simp
 have h₃ : Runs (.atom (.load (fun _ : Option Letter × Local => (none,initialLocal)) .done))
   (state v none (Function.update (fun _ => []) (.inr .output) (GaussMachine.boolCode b)))
   (finalStore b) 1 := Runs.atom_of _ _ _ rfl
 convert h₁'.seq (h₂'.seq h₃) using 1 <;> first | rfl | omega

def time (N : ℕ) : ℕ :=
 MatrixProgram.program.time N (8*(N*N)) + 2*(N+N*N)*(N+N+2) +
 300*(N+N*N+1)*(N+N+3)^2 + 14*N+16*(N*N)+23

lemma program_runs {N} (S : OrderedQuery.Data N) :
 Runs program (combined (cs 0 (TableMachine.code ⟨N,S⟩) []) (GaussMachine.ctrl 0 true) {})
   (finalStore (SerialGaussian.solve (SerialGaussian.queryRows S))) (time N) := by
 have h₁ := (build_runs S).compiles.frameLeft ((none,GaussMachine.ctrl 0 true) : GaussMachine.Local)
   ({} : GaussMachine.Data).tapes
 have h₂ := transfers_runs
   (cs N (TableMachine.tableInput S) (SerialGaussian.payload (SerialGaussian.queryRows S)).reverse)
   (N+N) (SerialGaussian.payload (SerialGaussian.queryRows S)) rfl rfl
 have h₃ := solver_framed
   ({cs N (TableMachine.tableInput S) [] with nums := Function.update (TableMachine.headerNums N) .width 0})
   (SerialGaussian.queryRows S)
 have h₄ := finish_runs N (TableMachine.tableInput S) (SerialGaussian.solve (SerialGaussian.queryRows S))
 have h := h₁.seq (h₂.seq (h₃.seq h₄))
 convert h using 1
 · rfl
 · rfl
 · simp only [time,TableMachine.tableInput_length,SerialGaussian.payload_length,
     SerialGaussian.queryRows,List.length_map,OrderedQuery.rows_length]
   ring

lemma time_polynomial : ∃ p : Polynomial ℕ, ∀ N, time N = p.eval N := by
 obtain ⟨p,hp⟩ := Bounded.Program.time_polynomial MatrixProgram.program
 refine ⟨p + 2*(Polynomial.X+Polynomial.X^2)*(2*Polynomial.X+2) +
  300*(Polynomial.X+Polynomial.X^2+1)*(2*Polynomial.X+3)^2 +
  14*Polynomial.X+16*Polynomial.X^2+23, ?_⟩
 intro N
 simp [time,hp]
 ring

open StackLang StackLang.Macros

open Turing StateTransition

def includeLetter : OrderedQuery.Alphabet → Letter
 | none => none
 | some b => TableMachine.bitLetter b

lemma code_map (S : OrderedQuery.OrderedInput) :
 TableMachine.code S = (OrderedQuery.encode S).map includeLetter := by
 simp [TableMachine.code,OrderedQuery.encode,TableMachine.tableInput,List.map_map,includeLetter,
   TableMachine.bitLetter,Function.comp_def]

@[simp] lemma code_length (S : OrderedQuery.OrderedInput) :
 (TableMachine.code S).length = S.1+1+8*(S.1*S.1) := by
 rw [code_map,List.length_map,OrderedQuery.encode_length]

def answer (S : OrderedQuery.OrderedInput) : Bool := SerialGaussian.solve (SerialGaussian.queryRows S.2)

noncomputable def machine : FinTM2 :=
 program.machine (.inl .input) (.inr .output) (none,initialLocal)

lemma initial_configuration (S : OrderedQuery.OrderedInput) :
 configuration (some program.start)
   (combined (cs 0 (TableMachine.code S) []) (GaussMachine.ctrl 0 true) {}) =
 initList machine (TableMachine.code S) := by
 suffices h : (configuration (some program.start)
   (combined (cs 0 (TableMachine.code S) []) (GaussMachine.ctrl 0 true) {})).stk =
   (initList machine (TableMachine.code S)).stk by
   exact congrArg (Turing.TM2.Cfg.mk (some program.start) (none,initialLocal)) h
 funext k
 cases k with
 | inl k => cases k with
     | reg r => cases r <;> simp [configuration,combined,leftStore,CounterLang.State.encode,
       state,CounterLang.State.data,CounterLang.Data.tapes,CounterLang.unary,cs,TableMachine.headerNums,
       initList,machine,Program.machine]
     | _ => simp [configuration,combined,leftStore,CounterLang.State.encode,
       state,CounterLang.State.data,CounterLang.Data.tapes,cs,initList,machine,Program.machine] <;> rfl
 | inr k => cases k <;> simp [configuration,combined,leftStore,GaussMachine.Data.tapes,
       initList,machine,Program.machine]

lemma final_configuration (b : Bool) : configuration (Λ := program.Labels) none (finalStore b) =
 haltList machine (GaussMachine.boolCode b) := by
 suffices h : (finalStore b).stk = (haltList machine (GaussMachine.boolCode b)).stk by
   exact congrArg (Turing.TM2.Cfg.mk none (none,initialLocal)) h
 funext k
 simp only [finalStore,state,haltList,machine,Program.machine]
 by_cases h : k = Sum.inr GaussMachine.Reg.output
 · subst k; simp [Function.update]; rfl
 · simp [h,Function.update]

lemma polynomial_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
 induction p using Polynomial.induction_on' with
 | add p q hp hq => simpa only [Polynomial.eval_add] using add_le_add hp hq
 | monomial n c => simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

noncomputable def polynomialAlgorithm :
 TM2ComputableInPolyTime TableMachine.code GaussMachine.boolCode answer := by
 let p := Classical.choose time_polynomial
 have hp := Classical.choose_spec time_polynomial
 refine ⟨⟨machine,Equiv.refl _,Equiv.refl _⟩,p,?_⟩
 rintro ⟨N,S⟩
 let m := Classical.choose (program_runs S)
 have hm := (Classical.choose_spec (program_runs S)).1
 let h := Classical.choice (Classical.choose_spec (program_runs S)).2
 have hc := StackLang.Program.compiles h (.inl CounterLang.Reg.input) (.inr GaussMachine.Reg.output) (none,initialLocal)
 dsimp only [StackLang.Program.machine] at hc
 rw [initial_configuration ⟨N,S⟩,final_configuration] at hc
 change TM2OutputsInTime machine ((TableMachine.code ⟨N,S⟩).map id)
   (some ((GaussMachine.boolCode (answer ⟨N,S⟩)).map id)) (p.eval (TableMachine.code ⟨N,S⟩).length)
 dsimp only [machine, StackLang.Program.machine, TM2OutputsInTime]
 simp only [List.map_id, Option.map_some]
 refine ⟨hc.toEvalsTo,?_⟩
 have hn : N ≤ (TableMachine.code ⟨N,S⟩).length := by rw [code_length]; dsimp only; omega
 exact hc.steps_le_m.trans (hm.trans ((hp N).le.trans (polynomial_eval_mono p hn)))

end CPTSeparation.QueryMachine

end OAI
end


