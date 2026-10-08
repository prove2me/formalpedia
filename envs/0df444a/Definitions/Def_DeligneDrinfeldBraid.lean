-- Prove2me | Definitions.Def_DeligneDrinfeldBraid
-- name    : DeligneDrinfeldBraid
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-07T18:41:29.254105+00:00
-- url     : https://prove2.me/theorems/b3d92d2a-5827-4f71-bcd4-32ad8f55339f
-- title:
--   OpenAI's Deligne–Drinfeld proof — internal definitions III (real solutions and the truncated braid categories)
-- statement:
--   The definitions needed to state the lemmas about braid categories and real solutions in OpenAI's proof of the Deligne–Drinfeld conjecture (*The Deligne–Drinfeld conjecture*, OpenAI Math Release, September 23, 2026, §§6–7, [github.com/openai/math](https://github.com/openai/math), [paper](https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf)). They are taken from OpenAI's Lean development `lean/OAI/Algebra/Drinfeld` (Apache License 2.0), with comments removed and line-level edits for this platform's Lean and Mathlib, keep OpenAI's names, and build on the bundles `DeligneDrinfeldInternals` and `DeligneDrinfeldKZ`.
--
--   It contains OpenAI's real solution space and weight pieces (`RealDeligneDrinfeld.IsSolution`, `W`, `Ln`, with the weight bridge to word gradings); truncated word algebras with derivations, the exponential of nilpotent operators and its action on categories (`TruncatedWords`, `OperatorExp`, `CategoryExp`, `TruncatedDerivation`); the free cutoff category of a solution and the truncated braid algebra on four strands (`FreeCutoffCategory`, `BraidCutoff`); the five insertion maps of the pentagon (`BraidInsertionExp.IAB`, `IAD`, `IDE`, `IBC`, `ICE`) and the derivation of a finite family of solutions (`BraidInsertionSum.free`); and the six chords of a homomorphism from $\mathfrak t_4$ (`KZRectangle.chords`), with the lemmas these definitions need.
-- source:
--   OpenAI, The Deligne–Drinfeld conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf, Sections 6-7, pp. 27-38 (real solutions and the truncated braid categories); Lean: https://github.com/openai/math/tree/main/lean/OAI/Algebra/Drinfeld (Apache-2.0)

import Mathlib
import Definitions.Def_DeligneDrinfeldKZ

/-!
# OpenAI's proof of the Deligne–Drinfeld conjecture: internal definitions

OpenAI, *The Deligne–Drinfeld conjecture*, OpenAI Math Release, September 23, 2026,
https://github.com/openai/math (paper:
`preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf`).

The definitions, structures and instances below, with the lemmas they need, are taken from
OpenAI's Lean development `lean/OAI/Algebra/Drinfeld` in that repository (Apache License,
Version 2.0), with comments removed and line-level edits for this Lean and Mathlib version.
They are the declarations needed to state the published intermediate lemmas of that proof.
-/

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section

namespace TruncatedWords
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]

theorem quotient_relation (P : Set (A R α)) (N : ℕ) {p : A R α} (hp : p∈P) :
    quotient P N p=0 := by
  have h := RingQuot.mkAlgHom_rel (S:=R) (show relations P N p 0 from ⟨rfl,Or.inl hp⟩)
  simpa only [quotient,map_zero] using h

variable [Finite α]

variable (P : Set (A ℝ α)) (N : ℕ)

end TruncatedWords
end

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace OperatorExp
open IsNilpotent
open scoped TensorProduct
variable {R V W U : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module ℚ V]
  [AddCommGroup W] [Module R W] [Module ℚ W]
  [AddCommGroup U] [Module R U] [Module ℚ U]

omit [Algebra ℚ R] in
 theorem fixed (A : Module.End R V) (hA : IsNilpotent A) {v : V} (hv : A v=0) :
    exp A v=v := by
  obtain ⟨n,hn⟩ := hA
  have hn' : A^(n+1)=0 := pow_eq_zero_of_le (by omega) hn
  rw [exp_eq_sum hn',LinearMap.sum_apply,Finset.sum_range_succ']
  have hz : ∀ i : ℕ,(A^(i+1)) v=0 := by
    intro i
    rw [_root_.pow_succ,Module.End.mul_apply,hv,map_zero]
  simp only [LinearMap.smul_apply,hz,smul_zero,Finset.sum_const_zero,pow_zero,
    Module.End.one_apply,Nat.factorial_zero,Nat.cast_one,inv_one,one_smul,zero_add]

end OperatorExp

namespace CategoryExp

section
open IsNilpotent
variable {R A B O P : Type*} [CommRing R] [Ring A] [Algebra R A] [Module ℚ A]
  [Ring B] [Algebra R B] [Module ℚ B]

structure Data (R A O : Type*) [CommRing R] [Ring A] [Algebra R A] where
  D : O → O → Module.End R A
  comp : ∀ p q r (a b : A),D p r (b*a)=D q r b*a+b*D p q a
  one : ∀ p,D p p 1=0

 def gauge (d : Module.End R A) (hd : ∀ a b,d (a*b)=d a*b+a*d b)
    (h1 : d 1=0) (h : O → A) : Data R A O where
  D p q := d+LinearMap.mulLeft R (h q)-LinearMap.mulRight R (h p)
  comp p q r a b := by
    simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply,hd]
    noncomm_ring
  one p := by
    simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply,h1,zero_add,mul_one,one_mul,sub_self]

 def act (g : Data R A O) (p q : O) : Module.End R A := exp (g.D p q)

 @[simp] theorem one (g : Data R A O) (hn : ∀ p q,IsNilpotent (g.D p q)) (p : O) :
    act g p p 1=1 := OperatorExp.fixed _ (hn p p) (g.one p)

end

open IsNilpotent
variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V]
  [Module R V] [Module ℚ V] [IsScalarTower ℚ R V]
variable {N : ℕ} (F : FilteredComparison.Filtration R V N)
  (d : Module.End R V) (k : ℕ)
  (hd : ∀ n a,a∈F.step n → d a∈F.step (n+k))

include hd

end CategoryExp

namespace TruncatedDerivation
open AssociativeElimination WordGrading TruncatedWords
variable {R α : Type*} [CommRing R]
variable (P : Set (A R α)) (N : ℕ)
local notation "Q" => TruncatedWords.Q P N
local notation "F" => filtration P N

 def gen (a : α) : Q := quotient P N (atom a)
 theorem gen_mem (a : α) : gen P N a∈F 1 :=
  ⟨atom a,word_mem (FreeMonoid.of a) (by simp [wt]),rfl⟩

 def jet (v : α → Q) : A R α →ₐ[R] TrivSqZeroExt Q Q :=
  AssociativeElimination.lift (R:=R) (fun a => (⟨gen P N a,v a⟩ : TrivSqZeroExt Q Q))

 @[simp] theorem jet_atom (v : α → Q) (a : α) : jet P N v (atom a)=⟨gen P N a,v a⟩ := by
  unfold jet
  exact AssociativeElimination.lift_atom (R:=R) (B:=TrivSqZeroExt Q Q) (fun a => (⟨gen P N a,v a⟩ : TrivSqZeroExt Q Q)) a

 theorem fst_jet (v : α → Q) (p : A R α) : (jet P N v p).fst=quotient P N p := by
  have he : (TrivSqZeroExt.fstHom R Q Q).comp (jet P N v)=quotient P N := by
    apply hom_ext
    intro a
    change (jet P N v (atom a)).fst=quotient P N (atom a)
    rw [jet_atom]
    rfl
  exact AlgHom.congr_fun he p

 def raw (v : α → Q) : A R α →ₗ[R] Q :=
  ((TrivSqZeroExt.sndHom Q Q).restrictScalars R).comp (jet P N v).toLinearMap

 @[simp] theorem raw_atom (v : α → Q) (a : α) : raw P N v (atom a)=v a := by
  change (jet P N v (atom a)).snd=v a
  rw [jet_atom]
  rfl
 @[simp] theorem raw_one (v : α → Q) : raw P N v 1=0 := by
  change (jet P N v 1).snd=0
  rw [map_one,TrivSqZeroExt.snd_one]
 theorem raw_mul (v : α → Q) (p q : A R α) :
    raw P N v (p*q)=quotient P N p*raw P N v q+raw P N v p*quotient P N q := by
  change (jet P N v (p*q)).snd=_
  rw [map_mul,TrivSqZeroExt.snd_mul,fst_jet,fst_jet]
  rfl

 theorem raw_word_mem (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1)) (w : FreeMonoid α) :
    raw P N v (word w)∈F (degree wt w+k) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [word_one,raw_one]; exact Submodule.zero_mem _
  | of_mul a w ih =>
    rw [word_mul,word_of,raw_mul,raw_atom,degree_mul,degree_of]
    change _∈F (1+degree wt w+k)
    apply Submodule.add_mem
    · simpa only [Nat.add_assoc,wt,gen] using filtration_mul P N 1 _ (gen_mem P N a) ih
    · have hm : quotient P N (word w)∈F (degree wt w) := ⟨word w,word_mem w le_rfl,rfl⟩
      simpa only [show k+1+degree wt w=1+degree wt w+k by omega] using
        filtration_mul P N (k+1) _ (hv a) hm

 theorem raw_mem (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    {n : ℕ} {p : A R α} (hp : p∈above wt n) : raw P N v p∈F (n+k) :=
  map_space (raw P N v) _ (fun w hw =>
    filtration_antitone P N (Nat.add_le_add_right hw k) (raw_word_mem P N k v hv w)) hp

 def descend (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) : Q →ₐ[R] TrivSqZeroExt Q Q :=
  RingQuot.liftAlgHom R ⟨jet P N v,by
    rintro p q ⟨rfl,hp⟩
    rw [map_zero]
    apply TrivSqZeroExt.ext
    · rw [fst_jet]
      rcases hp with hp|hp
      · exact quotient_relation P N hp
      · exact quotient_above P N hp
    · change raw P N v p=0
      rcases hp with hp|hp
      · exact hP p hp
      · have hh := filtration_antitone P N (Nat.le_add_right (N+1) k) (raw_mem P N k v hv hp)
        simpa only [filtration_terminal,Submodule.mem_bot] using hh⟩

 @[simp] theorem descend_quotient (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) (p : A R α) :
    descend P N k v hv hP (quotient P N p)=jet P N v p := by
  simp only [descend,quotient,RingQuot.liftAlgHom_mkAlgHom_apply]

 theorem descend_fst (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) (p : Q) : (descend P N k v hv hP p).fst=p := by
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations P N) p
  rw [←quotient,descend_quotient,fst_jet]

 def derivation (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) : Module.End R Q :=
  ((TrivSqZeroExt.sndHom Q Q).restrictScalars R).comp (descend P N k v hv hP).toLinearMap

 @[simp] theorem derivation_quotient (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) (p : A R α) :
    derivation P N k v hv hP (quotient P N p)=raw P N v p := by
  change (descend P N k v hv hP (quotient P N p)).snd=_
  rw [descend_quotient]
  rfl

 @[simp] theorem derivation_one (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) : derivation P N k v hv hP 1=0 := by
  rw [←map_one (quotient P N),derivation_quotient,raw_one]

 theorem derivation_mul (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) (p q : Q) :
    derivation P N k v hv hP (p*q)=derivation P N k v hv hP p*q+p*derivation P N k v hv hP q := by
  change (descend P N k v hv hP (p*q)).snd=_
  rw [map_mul,TrivSqZeroExt.snd_mul,descend_fst,descend_fst]
  exact add_comm _ _

end TruncatedDerivation

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section
namespace RealDeligneDrinfeld

def x : L := FreeLieAlgebra.of ℝ false
def y : L := FreeLieAlgebra.of ℝ true

def IsSolution (p : L) : Prop :=
  p + eval y x p = 0 ∧
  p + eval y (-x-y) p + eval (-x-y) x p = 0 ∧
  eval (t 0 1) (t 1 2 + t 1 3) p + eval (t 0 2 + t 1 2) (t 2 3) p =
    eval (t 1 2) (t 2 3) p + eval (t 0 1 + t 0 2) (t 1 3 + t 2 3) p +
      eval (t 0 1) (t 1 2) p

def W : Submodule ℝ L where
  carrier := {p | IsSolution p}
  zero_mem' := by simp [IsSolution]
  add_mem' := by
    intro p q hp hq
    rcases hp with ⟨hp1, hp2, hp3⟩
    rcases hq with ⟨hq1, hq2, hq3⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [map_add]
      calc
        _ = (p + eval y x p) + (q + eval y x q) := by abel
        _ = 0 := by rw [hp1, hq1, add_zero]
    · simp only [map_add]
      calc
        _ = (p + eval y (-x-y) p + eval (-x-y) x p) +
            (q + eval y (-x-y) q + eval (-x-y) x q) := by abel
        _ = 0 := by rw [hp2, hq2, add_zero]
    · simp only [map_add]
      calc
        _ = (eval (t 0 1) (t 1 2 + t 1 3) p + eval (t 0 2 + t 1 2) (t 2 3) p) +
            (eval (t 0 1) (t 1 2 + t 1 3) q + eval (t 0 2 + t 1 2) (t 2 3) q) := by abel
        _ = _ := by rw [hp3, hq3]; abel
  smul_mem' := by
    intro a p hp
    rcases hp with ⟨hp1, hp2, hp3⟩
    change IsSolution (a • p)
    simp only [IsSolution, map_smul]
    constructor
    · simpa only [smul_add, smul_zero] using congrArg (a • ·) hp1
    constructor
    · simpa only [smul_add, smul_zero] using congrArg (a • ·) hp2
    · simpa only [smul_add] using congrArg (a • ·) hp3

structure Tangent where
  base : L
  velocity : L

def Tangent.equiv : Tangent ≃ L × L where
  toFun z := (z.base, z.velocity)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup Tangent := Tangent.equiv.addCommGroup
instance : Module ℝ Tangent := Tangent.equiv.addEquiv.module ℝ
instance : Bracket Tangent Tangent :=
  ⟨fun a b => ⟨⁅a.base, b.base⁆,
    ⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆⟩⟩

@[ext] theorem Tangent.ext {a b : Tangent} (h : a.base = b.base)
    (k : a.velocity = b.velocity) : a = b := by cases a; cases b; simp_all

@[simp] theorem Tangent.base_zero : (0 : Tangent).base = 0 := rfl
@[simp] theorem Tangent.velocity_zero : (0 : Tangent).velocity = 0 := rfl
@[simp] theorem Tangent.base_add (a b : Tangent) : (a+b).base = a.base+b.base := rfl
@[simp] theorem Tangent.velocity_add (a b : Tangent) :
    (a+b).velocity = a.velocity+b.velocity := rfl
@[simp] theorem Tangent.base_smul (q : ℝ) (a : Tangent) : (q • a).base = q • a.base := rfl
@[simp] theorem Tangent.velocity_smul (q : ℝ) (a : Tangent) :
    (q • a).velocity = q • a.velocity := rfl
@[simp] theorem Tangent.base_lie (a b : Tangent) : ⁅a,b⁆.base = ⁅a.base,b.base⁆ := rfl
@[simp] theorem Tangent.velocity_lie (a b : Tangent) :
    ⁅a,b⁆.velocity = ⁅a.velocity,b.base⁆ + ⁅a.base,b.velocity⁆ := rfl

instance : LieRing Tangent where
  add_lie a b c := by
    ext
    · simp [add_lie]
    · simp only [Tangent.velocity_lie, Tangent.velocity_add, Tangent.base_add, add_lie]
      abel
  lie_add a b c := by
    ext
    · simp [lie_add]
    · simp only [Tangent.velocity_lie, Tangent.velocity_add, Tangent.base_add, lie_add]
      abel
  lie_self a := by
    ext
    · simp
    · change ⁅a.velocity, a.base⁆ + ⁅a.base, a.velocity⁆ = 0
      rw [← lie_skew a.velocity a.base]
      exact neg_add_cancel _
  leibniz_lie a b c := by
    ext
    · simp [lie_lie]
    · simp only [Tangent.velocity_lie, Tangent.velocity_add, Tangent.base_lie,
        lie_add, add_lie, lie_lie]
      abel
instance : LieAlgebra ℝ Tangent where
  lie_smul q a b := by ext <;> simp [lie_smul, smul_add]

def tangentLift (p : L) : L →ₗ⁅ℝ⁆ Tangent :=
  FreeLieAlgebra.lift ℝ (fun i => if i then ⟨y, ⁅y,p⁆⟩ else ⟨x, 0⟩)

def D (p q : L) : L := (tangentLift p q).velocity

@[simp] theorem eval_x {M : Type*} [LieRing M] [LieAlgebra ℝ M] (a b : M) :
    eval a b x = a := by simp [eval, x]
@[simp] theorem eval_y {M : Type*} [LieRing M] [LieAlgebra ℝ M] (a b : M) :
    eval a b y = b := by simp [eval, y]

def Tangent.baseHom : Tangent →ₗ⁅ℝ⁆ L where
  toFun := Tangent.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

@[simp] theorem tangentLift_base (p q : L) : (tangentLift p q).base = q := by
  have h : Tangent.baseHom.comp (tangentLift p) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [tangentLift, Tangent.baseHom, x, y] <;> rfl
  exact LieHom.congr_fun h q

@[simp] theorem D_x (p : L) : D p x = 0 := by simp [D, tangentLift, x]
@[simp] theorem D_y (p : L) : D p y = ⁅y,p⁆ := by simp [D, tangentLift, y]
@[simp] theorem D_zero (p : L) : D p 0 = 0 := by simp [D]
@[simp] theorem D_add (p q r : L) : D p (q+r) = D p q + D p r := by simp [D]
@[simp] theorem D_smul (p q : L) (a : ℝ) : D p (a • q) = a • D p q := by simp [D]
theorem D_lie (p q r : L) : D p ⁅q,r⁆ = ⁅D p q,r⁆ + ⁅q,D p r⁆ := by
  simp [D, LieHom.map_lie]

def derivation (p : L) : LieDerivation ℝ L L where
  toFun := D p
  map_add' := D_add p
  map_smul' a q := D_smul p q a
  leibniz' a b := by
    change D p ⁅a,b⁆ = ⁅a,D p b⁆ - ⁅b,D p a⁆
    rw [D_lie, sub_eq_add_neg, lie_skew, add_comm]

@[simp] theorem derivation_apply (p q : L) : derivation p q = D p q := rfl

theorem derivation_ext {d₁ d₂ : LieDerivation ℝ L L}
    (hx : d₁ x = d₂ x) (hy : d₁ y = d₂ y) : d₁ = d₂ := by
  apply DFunLike.ext
  intro q
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i; exact hx; exact hy
  | ha a b ha hb => simp [ha, hb]
  | hs r a ha => simp [ha]
  | hl a b ha hb => simp [ha, hb]

@[simp] theorem D_zero_left (q : L) : D 0 q = 0 := by
  have h : derivation 0 = 0 := by
    apply derivation_ext <;> simp
  exact LieDerivation.congr_fun h q

@[simp] theorem D_add_left (p q r : L) : D (p+q) r = D p r + D q r := by
  have h : derivation (p+q) = derivation p + derivation q := by
    apply derivation_ext <;> simp [lie_add]
  exact LieDerivation.congr_fun h r

@[simp] theorem D_smul_left (p q : L) (a : ℝ) : D (a • p) q = a • D p q := by
  have h : derivation (a • p) = a • derivation p := by
    apply derivation_ext <;> simp
  exact LieDerivation.congr_fun h q

inductive WeightedWord {α : Type*} (wt : α → ℕ) : ℕ → FreeLieAlgebra ℝ α → Prop
  | generator (a : α) : WeightedWord wt (wt a) (FreeLieAlgebra.of ℝ a)
  | bracket {n m a b} : WeightedWord wt n a → WeightedWord wt m b →
      WeightedWord wt (n+m) ⁅a,b⁆

def weightPiece {α : Type*} (wt : α → ℕ) (n : ℕ) : Submodule ℝ (FreeLieAlgebra ℝ α) :=
  Submodule.span ℝ {p | WeightedWord wt n p}

abbrev Ln (n : ℕ) := weightPiece (fun _ : Bool => 1) n

end RealDeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace RealDeligneDrinfeld.WeightBridge
open DeligneDrinfeld.LieGrading DeligneDrinfeld.UniversalEmbedding
variable {α : Type*}
 theorem tree_word (wt : α → ℕ) (t : DeligneDrinfeld.UniversalEmbedding.Tree α) : WeightedWord wt (treeDegree wt t) (t.eval : FreeLieAlgebra ℝ α) := by
  induction t with
  | leaf a => simpa only [DeligneDrinfeld.UniversalEmbedding.Tree.eval,treeDegree_leaf] using WeightedWord.generator (wt:=wt) a
  | node a b ha hb => simpa only [DeligneDrinfeld.UniversalEmbedding.Tree.eval,treeDegree_node] using WeightedWord.bracket ha hb

 theorem word_tree {wt : α → ℕ} {n : ℕ} {p : FreeLieAlgebra ℝ α} (hp : WeightedWord wt n p) :
    ∃ t : DeligneDrinfeld.UniversalEmbedding.Tree α,treeDegree wt t=n ∧ t.eval=p := by
  induction hp with
  | generator a => exact ⟨.leaf a,by simp [DeligneDrinfeld.UniversalEmbedding.Tree.eval]⟩
  | bracket hp hq ihp ihq =>
    obtain ⟨t,ht,rfl⟩ := ihp
    obtain ⟨u,hu,rfl⟩ := ihq
    exact ⟨.node t u,by simp [ht,hu,DeligneDrinfeld.UniversalEmbedding.Tree.eval]⟩

 theorem piece_eq (wt : α → ℕ) (n : ℕ) : weightPiece wt n=homogeneousLie (R:=ℝ) wt n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro p hp
    exact Submodule.subset_span (word_tree hp)
  · apply Submodule.span_le.mpr
    rintro p ⟨t,ht,rfl⟩
    apply Submodule.subset_span
    exact ht ▸ tree_word wt t

 theorem embed_homogeneous {wt : α → ℕ} {n : ℕ} {p : FreeLieAlgebra ℝ α}
    (hp : p∈weightPiece wt n) : DeligneDrinfeld.AssociativeElimination.embed p∈
      DeligneDrinfeld.WordGrading.homogeneous wt n := by
  rw [piece_eq] at hp
  exact homogeneousLie_embed hp

 theorem y_mem : y∈Ln 1 := Submodule.subset_span (WeightedWord.generator _)

end RealDeligneDrinfeld.WeightBridge

namespace DeligneDrinfeld
end DeligneDrinfeld

namespace DeligneDrinfeld
end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld
end DeligneDrinfeld

namespace RealDeligneDrinfeld.CategoricalValues
open DeligneDrinfeld.CategoryGauge

def rotateLie : L →ₗ⁅ℝ⁆ L := eval y (-x-y)

end RealDeligneDrinfeld.CategoricalValues

namespace DeligneDrinfeld.PresentedSubstitution
open AssociativeElimination WordGrading TruncatedWords
variable {R α β : Type*} [CommRing R] (P : Set (A R β)) (N : ℕ)
variable (f : α → TruncatedWords.Q P N) (hf : ∀ a,f a∈filtration P N 1)
include hf
 theorem lift_word_mem (w : FreeMonoid α) :
    lift (R:=R) f (word w)∈filtration P N (degree (fun _ => 1) w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa only [word_one,map_one,degree_one] using filtration_one P N
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,lift_atom,degree_mul,degree_of]
    exact filtration_mul P N 1 _ (hf a) ih
 theorem lift_mem {n : ℕ} {a : A R α} (ha : a∈above (fun _ => 1) n) :
    lift (R:=R) f a∈filtration P N n :=
  map_space (lift (R:=R) f).toLinearMap _
    (fun w hw => filtration_antitone P N hw (lift_word_mem P N f hf w)) ha
 def subst : TruncatedWords.Q (∅:Set (A R α)) N →ₐ[R] TruncatedWords.Q P N :=
  RingQuot.liftAlgHom R ⟨lift (R:=R) f,by
    rintro p q ⟨rfl,hp⟩
    rcases hp with hp|hp
    · exact False.elim hp
    · simpa only [filtration_terminal,Submodule.mem_bot,map_zero] using lift_mem P N f hf hp⟩
 @[simp] theorem subst_quotient (a : A R α) :
    subst P N f hf (quotient ∅ N a)=lift (R:=R) f a := by
  simp only [subst,quotient,RingQuot.liftAlgHom_mkAlgHom_apply]
 @[simp] theorem subst_gen (a : α) :
    subst P N f hf (TruncatedDerivation.gen ∅ N a)=f a := by
  rw [TruncatedDerivation.gen,subst_quotient,lift_atom]
end DeligneDrinfeld.PresentedSubstitution

end

end OAI

end

section

namespace OAI

noncomputable section

namespace RealDeligneDrinfeld.T4Basic
open BraidSix

def c : T4 := t 2 3
def d : T4 := t 0 2
def e : T4 := t 1 3

end RealDeligneDrinfeld.T4Basic

namespace RealDeligneDrinfeld.ThreeSolutionCategory
open CategoricalValues DeligneDrinfeld.CategoryGauge

def data (q : L) : Data ℝ L (Fin 3) :=
  ⟨derivation q,![0,q,q+rotateLie q]⟩

@[simp] theorem loop_zero (q : L) : loop (data q) 0=derivation q := by
  ext p
  simp [loop_apply,data]
@[simp] theorem value (q : L) : unit (data q) 0 1=q := by simp [unit,data]

end RealDeligneDrinfeld.ThreeSolutionCategory

end

end OAI

end

section

namespace OAI

noncomputable section

namespace RealDeligneDrinfeld.FreeCutoffCategory
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.TruncatedWords
attribute [local instance] LieRing.ofAssociativeRing
abbrev P : Set (DeligneDrinfeld.AssociativeElimination.A ℝ Bool) := ∅
abbrev Q (N : ℕ) := DeligneDrinfeld.TruncatedWords.Q P N
abbrev F (N n : ℕ) := filtration P N n

 def j (N : ℕ) : L →ₗ⁅ℝ⁆ Q N := (quotient P N).toLieHom.comp embed
 @[simp] theorem j_of (N : ℕ) (a : Bool) : j N (FreeLieAlgebra.of ℝ a)=DeligneDrinfeld.TruncatedDerivation.gen P N a := by
  change quotient P N (embed (FreeLieAlgebra.of ℝ a))=_
  rw [embed_of]; rfl
 theorem j_mem {N n : ℕ} {q : L} (hq : q∈Ln n) : j N q∈F N n := by
  refine ⟨embed q,?_,rfl⟩
  exact space_mono (by intro w hw; exact le_of_eq hw.symm) (WeightBridge.embed_homogeneous hq)
 theorem lie_mem {N r s : ℕ} {a b : Q N} (ha : a∈F N r) (hb : b∈F N s) : ⁅a,b⁆∈F N (r+s) :=
  (F N (r+s)).sub_mem (filtration_mul P N r s ha hb)
    (by simpa only [Nat.add_comm s r] using filtration_mul P N s r hb ha)

 def velocity (N : ℕ) (q : L) (a : Bool) : Q N := j N (RealDeligneDrinfeld.derivation q (FreeLieAlgebra.of ℝ a))
 theorem velocity_mem {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (a : Bool) : velocity N q a∈F N (n+1) := by
  cases a
  · change j N (RealDeligneDrinfeld.derivation q x)∈_
    simp only [derivation_apply,D_x,map_zero,Submodule.zero_mem]
  · change j N (RealDeligneDrinfeld.derivation q y)∈_
    rw [derivation_apply,D_y,LieHom.map_lie]
    simpa only [Nat.add_comm 1 n] using lie_mem (j_mem (N:=N) WeightBridge.y_mem) (j_mem (N:=N) hq)

 def d {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) : Module.End ℝ (Q N) :=
  DeligneDrinfeld.TruncatedDerivation.derivation P N n (velocity N q) (velocity_mem N hq) (by intros p hp; exact False.elim hp)

 theorem d_one {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) : d N hq 1=0 :=
  DeligneDrinfeld.TruncatedDerivation.derivation_one P N n _ _ _
 theorem d_mul {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (a b : Q N) :
    d N hq (a*b)=d N hq a*b+a*d N hq b :=
  DeligneDrinfeld.TruncatedDerivation.derivation_mul P N n _ _ _ a b

 def h (N : ℕ) (q : L) (p : Fin 3) : Q N := j N ((ThreeSolutionCategory.data q).h p)

 def data {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) : DeligneDrinfeld.CategoryExp.Data ℝ (Q N) (Fin 3) :=
  DeligneDrinfeld.CategoryExp.gauge (d N hq) (d_mul N hq) (d_one N hq) (h N q)

end RealDeligneDrinfeld.FreeCutoffCategory

namespace RealDeligneDrinfeld.BraidCutoff
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.TruncatedWords
attribute [local instance] LieRing.ofAssociativeRing

def presentation : Set (DeligneDrinfeld.AssociativeElimination.A ℝ Edge) :=
  DeligneDrinfeld.AssociativeElimination.embed '' braidRelations
abbrev Q (N : ℕ) := DeligneDrinfeld.TruncatedWords.Q presentation N
abbrev F (N n : ℕ) := filtration presentation N n

def freeMap (N : ℕ) : BraidFree →ₗ⁅ℝ⁆ Q N :=
  (quotient presentation N).toLieHom.comp DeligneDrinfeld.AssociativeElimination.embed

theorem freeMap_relation (N : ℕ) {p : BraidFree} (hp : p∈braidRelations) : freeMap N p=0 :=
  quotient_relation presentation N ⟨p,hp,rfl⟩

def lieMap (N : ℕ) : T4 →ₗ⁅ℝ⁆ Q N := by
  have hk : braidIdeal ≤ (freeMap N).ker := by
    rw [braidIdeal,LieSubmodule.lieSpan_le]
    intro p hp
    exact freeMap_relation N hp
  exact { braidIdeal.toSubmodule.liftQ (freeMap N).toLinearMap hk with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact (freeMap N).map_lie a b }

def projection : BraidFree →ₗ⁅ℝ⁆ T4 where
  toLinearMap := braidIdeal.toSubmodule.mkQ
  map_lie' := rfl

@[simp] theorem lieMap_projection (N : ℕ) (p : BraidFree) : lieMap N (projection p)=freeMap N p := rfl
@[simp] theorem projection_of (a : Edge) : projection (FreeLieAlgebra.of ℝ a)=t a.val.1 a.val.2 := by
  simp only [t,chord,dif_pos a.property]; rfl
 theorem lieMap_of (N : ℕ) (a : Edge) : lieMap N (projection (FreeLieAlgebra.of ℝ a))=
    DeligneDrinfeld.TruncatedDerivation.gen presentation N a := by
  rw [lieMap_projection]
  change quotient presentation N (DeligneDrinfeld.AssociativeElimination.embed (FreeLieAlgebra.of ℝ a))=_
  rw [DeligneDrinfeld.AssociativeElimination.embed_of]; rfl

 theorem t_mem (N : ℕ) (i j : Fin 4) : lieMap N (t i j)∈F N 1 := by
  unfold t chord
  split_ifs with hij hji
  · change lieMap N (projection (FreeLieAlgebra.of ℝ ⟨(i,j),hij⟩))∈_
    rw [lieMap_of]
    exact DeligneDrinfeld.TruncatedDerivation.gen_mem presentation N _
  · change lieMap N (projection (FreeLieAlgebra.of ℝ ⟨(j,i),hji⟩))∈_
    rw [lieMap_of]
    exact DeligneDrinfeld.TruncatedDerivation.gen_mem presentation N _
  · change lieMap N 0∈_; rw [map_zero]; exact Submodule.zero_mem _

open T4Basic T4SolutionData
variable {n : ℕ} {q : L}

end RealDeligneDrinfeld.BraidCutoff

namespace RealDeligneDrinfeld.BraidInsertionExp
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.TruncatedWords DeligneDrinfeld.CategoryGauge
attribute [local instance] LieRing.ofAssociativeRing
variable (N : ℕ) (X Y : T4)
  (hX : BraidCutoff.lieMap N X∈BraidCutoff.F N 1) (hY : BraidCutoff.lieMap N Y∈BraidCutoff.F N 1)
 def family (a : Bool) : BraidCutoff.Q N := if a then BraidCutoff.lieMap N Y else BraidCutoff.lieMap N X
include hX hY in
 theorem family_mem (a : Bool) : family N X Y a∈BraidCutoff.F N 1 := by
  cases a <;> assumption
 def insert : FreeCutoffCategory.Q N →ₐ[ℝ] BraidCutoff.Q N :=
  DeligneDrinfeld.PresentedSubstitution.subst BraidCutoff.presentation N (family N X Y) (family_mem N X Y hX hY)

 variable {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n)

 open T4Basic
 abbrev IAB := insert N a b (BraidCutoff.t_mem N 0 1) (BraidCutoff.t_mem N 1 2)
 abbrev IAD := insert N (d+b) c (by rw [map_add]; exact Submodule.add_mem _ (BraidCutoff.t_mem N 0 2) (BraidCutoff.t_mem N 1 2)) (BraidCutoff.t_mem N 2 3)
 abbrev IDE := insert N a (b+e) (BraidCutoff.t_mem N 0 1) (by rw [map_add]; exact Submodule.add_mem _ (BraidCutoff.t_mem N 1 2) (BraidCutoff.t_mem N 1 3))
 abbrev IBC := insert N (a+d) (e+c) (by rw [map_add]; exact Submodule.add_mem _ (BraidCutoff.t_mem N 0 1) (BraidCutoff.t_mem N 0 2))
   (by rw [map_add]; exact Submodule.add_mem _ (BraidCutoff.t_mem N 1 3) (BraidCutoff.t_mem N 2 3))
 abbrev ICE := insert N b c (BraidCutoff.t_mem N 1 2) (BraidCutoff.t_mem N 2 3)

end RealDeligneDrinfeld.BraidInsertionExp

namespace DeligneDrinfeld.CategoryExp
variable {R A B O P I : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Ring B] [Algebra R B]
 def sum (s : Finset I) (g : I → Data R A O) : Data R A O where
  D p q := ∑ i∈s,(g i).D p q
  comp p q r a b := by
    simp only [LinearMap.sum_apply]
    rw [Finset.sum_mul,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    exact (g i).comp p q r a b
  one p := by simp only [LinearMap.sum_apply,Data.one,Finset.sum_const_zero]
end DeligneDrinfeld.CategoryExp

section

namespace RealDeligneDrinfeld.BraidInsertionSum
open DeligneDrinfeld.CategoryExp
open BraidInsertionExp
variable {I : Type*} (N : ℕ) (s : Finset I) (q : I → L) (n : I → ℕ)
  (hq : ∀ i,q i∈W) (hqn : ∀ i,q i∈Ln (n i)) (hn : ∀ i,2<n i)
 def free : Data ℝ (FreeCutoffCategory.Q N) (Fin 3) := sum s (fun i => FreeCutoffCategory.data N (hqn i))
end RealDeligneDrinfeld.BraidInsertionSum

end

end

end OAI

end

section

namespace OAI

noncomputable section

section

end

namespace DeligneDrinfeld.KZRectangle
open MeasureTheory Set Filter FinitePicard LogRectangle
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {K A : Type*} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
  [NormedRing A] [NormedAlgebra K A] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A]

def edges : Fin 6 → Fin 4×Fin 4 := ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

def chords (j : GenericBraid.T K (Fin 4) →ₗ⁅K⁆ A) (i : Fin 6) : A :=
  j (GenericBraid.t (edges i).1 (edges i).2)

variable [CompleteSpace A] [FiniteDimensional ℝ A]

end DeligneDrinfeld.KZRectangle

end

end OAI

end


