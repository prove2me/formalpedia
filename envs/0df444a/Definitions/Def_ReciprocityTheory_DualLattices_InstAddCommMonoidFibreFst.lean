-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
-- name    : ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:42.173873+00:00
-- url     : https://prove2.me/theorems/36a93e7a-ffb2-49c6-b43e-d7deb33e2b44
-- title:
--   Inst Add Comm Monoid Fibre Fst
-- statement:
--   Definitions and structural lemmas for Inst Add Comm Monoid Fibre Fst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace BX
variable (B : BX R₀) {R : LAlg R₀}
lemma smul_eq_self {x y : B.G R} {l : (R : Type u)ˣ} {u : B.P R x y} (h : B.smul l u = u) :
    l = 1 := by
  obtain ⟨m, -, hm⟩ := B.trans u u
  exact (hm l h).trans (hm 1 (B.one_smul u)).symm
lemma smul_inj {x y : B.G R} {l l' : (R : Type u)ˣ} {u : B.P R x y}
    (h : B.smul l u = B.smul l' u) : l = l' := by
  have h1 : B.smul (l'⁻¹ * l) u = u := by
    rw [B.mul_smul, h, ← B.mul_smul, inv_mul_cancel, B.one_smul]
  have h2 := B.smul_eq_self h1
  calc l = l' * (l'⁻¹ * l) := (mul_inv_cancel_left l' l).symm
    _ = l' := by rw [h2, mul_one]
lemma exists_smul {x y : B.G R} (u w : B.P R x y) : ∃ l, B.smul l u = w :=
  (B.trans u w).exists
lemma heq_zero1 {y y' : B.G R} (h : y = y') : HEq (B.zero1 y) (B.zero1 y') := by subst h; rfl
lemma heq_zero2 {x x' : B.G R} (h : x = x') : HEq (B.zero2 x) (B.zero2 x') := by subst h; rfl
lemma castSnd_heq {x y y' : B.G R} (h : y = y') (u : B.P R x y) : HEq (B.tr2 h u) u := by
  subst h; rfl
lemma addFst_hcongr {x₁ x₂ x₁' x₂' y₁ y₂ : B.G R} (hx : x₁ = x₂) (hx' : x₁' = x₂') (hy : y₁ = y₂)
    {u₁ : B.P R x₁ y₁} {u₂ : B.P R x₂ y₂} {w₁ : B.P R x₁' y₁} {w₂ : B.P R x₂' y₂}
    (hu : HEq u₁ u₂) (hw : HEq w₁ w₂) : HEq (B.add1 u₁ w₁) (B.add1 u₂ w₂) := by
  subst hx hx' hy; cases eq_of_heq hu; cases eq_of_heq hw; rfl
lemma addSnd_hcongr {x₁ x₂ y₁ y₂ y₁' y₂' : B.G R} (hx : x₁ = x₂) (hy : y₁ = y₂) (hy' : y₁' = y₂')
    {u₁ : B.P R x₁ y₁} {u₂ : B.P R x₂ y₂} {w₁ : B.P R x₁ y₁'} {w₂ : B.P R x₂ y₂'}
    (hu : HEq u₁ u₂) (hw : HEq w₁ w₂) : HEq (B.add2 u₁ w₁) (B.add2 u₂ w₂) := by
  subst hx hy hy'; cases eq_of_heq hu; cases eq_of_heq hw; rfl
def S1 (R : LAlg R₀) (y : B.G R) : Type u := Σ x : B.G R, B.P R x y
instance instZS1 (R : LAlg R₀) (y : B.G R) : Zero (B.S1 R y) := ⟨⟨0, B.zero1 y⟩⟩
instance instAS1 (R : LAlg R₀) (y : B.G R) : Add (B.S1 R y) :=
  ⟨fun a b => ⟨a.1 + b.1, B.add1 a.2 b.2⟩⟩
instance instAddCommMonoidFibreFst (R : LAlg R₀) (y : B.G R) : AddCommMonoid (B.S1 R y) where
  add := (· + ·)
  zero := 0
  add_assoc a b c := Sigma.ext (add_assoc a.1 b.1 c.1) (B.addFst_assoc a.2 b.2 c.2)
  zero_add a := Sigma.ext (zero_add a.1) (B.zeroFst_add a.2)
  add_zero a := Sigma.ext (add_zero a.1) ((B.addFst_comm a.2 (B.zero1 y)).trans (B.zeroFst_add a.2))
  add_comm a b := Sigma.ext (add_comm a.1 b.1) (B.addFst_comm a.2 b.2)
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
def S1mk {x y : B.G R} (u : B.P R x y) : B.S1 R y := ⟨x, u⟩
def PrimaryComponentScale {y : B.G R} (l : (R : Type u)ˣ) (a : B.S1 R y) : B.S1 R y := ⟨a.1, B.smul l a.2⟩
lemma S1smul_add {y : B.G R} (l l' : (R : Type u)ˣ) (a b : B.S1 R y) :
    B.PrimaryComponentScale l a + B.PrimaryComponentScale l' b = B.PrimaryComponentScale (l * l') (a + b) :=
  Sigma.ext rfl (heq_of_eq (B.addFst_smul l l' a.2 b.2))
lemma S1smul_one {y : B.G R} (a : B.S1 R y) : B.PrimaryComponentScale 1 a = a :=
  Sigma.ext rfl (heq_of_eq (B.one_smul a.2))
lemma fibreFst_idem {y : B.G R} (a : B.S1 R y) (h : a + a = a) : a = 0 := by
  obtain ⟨x, u⟩ := a
  change B.S1mk u + B.S1mk u = B.S1mk u at h
  change B.S1mk u = 0
  have hx' : x + x = x := congrArg Sigma.fst h
  have hx : x = 0 := add_left_cancel (hx'.trans (add_zero x).symm)
  subst hx
  obtain ⟨μ, rfl⟩ := B.exists_smul (B.zero1 y) u
  have e : (B.S1mk (B.smul μ (B.zero1 y))) = B.PrimaryComponentScale μ 0 := rfl
  rw [e] at h ⊢
  rw [S1smul_add, add_zero] at h
  have h2 : B.smul (μ * μ) (B.zero1 y) = B.smul μ (B.zero1 y) := eq_of_heq (Sigma.ext_iff.1 h).2
  have h3 : μ * μ = μ * 1 := by rw [B.smul_inj h2, mul_one]
  rw [mul_left_cancel h3, S1smul_one]
def PrimaryComponentMap {S : LAlg R₀} (f : LHom R S) (y : B.G R) : B.S1 R y →+ B.S1 S (B.map f y) where
  toFun a := ⟨B.map f a.1, B.pmap f a.2⟩
  map_zero' := Sigma.ext (map_zero _) (B.zeroFst_nat f y)
  map_add' a b := Sigma.ext (map_add _ _ _) (B.addFst_nat f a.2 b.2)
def S2 (R : LAlg R₀) (x : B.G R) : Type u := Σ y : B.G R, B.P R x y
instance instZS2 (R : LAlg R₀) (x : B.G R) : Zero (B.S2 R x) := ⟨⟨0, B.zero2 x⟩⟩
instance instAS2 (R : LAlg R₀) (x : B.G R) : Add (B.S2 R x) :=
  ⟨fun a b => ⟨a.1 + b.1, B.add2 a.2 b.2⟩⟩
instance instAddCommMonoidFibreSnd (R : LAlg R₀) (x : B.G R) : AddCommMonoid (B.S2 R x) where
  add := (· + ·)
  zero := 0
  add_assoc a b c := Sigma.ext (add_assoc a.1 b.1 c.1) (B.addSnd_assoc a.2 b.2 c.2)
  zero_add a := Sigma.ext (zero_add a.1) (B.zeroSnd_add a.2)
  add_zero a := Sigma.ext (add_zero a.1) ((B.addSnd_comm a.2 (B.zero2 x)).trans (B.zeroSnd_add a.2))
  add_comm a b := Sigma.ext (add_comm a.1 b.1) (B.addSnd_comm a.2 b.2)
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
def S2mk {x y : B.G R} (u : B.P R x y) : B.S2 R x := ⟨y, u⟩
def SecondaryComponentScale {x : B.G R} (l : (R : Type u)ˣ) (a : B.S2 R x) : B.S2 R x := ⟨a.1, B.smul l a.2⟩
lemma S2smul_add {x : B.G R} (l l' : (R : Type u)ˣ) (a b : B.S2 R x) :
    B.SecondaryComponentScale l a + B.SecondaryComponentScale l' b = B.SecondaryComponentScale (l * l') (a + b) :=
  Sigma.ext rfl (heq_of_eq (B.addSnd_smul l l' a.2 b.2))
lemma S2smul_one {x : B.G R} (a : B.S2 R x) : B.SecondaryComponentScale 1 a = a :=
  Sigma.ext rfl (heq_of_eq (B.one_smul a.2))
lemma fibreSnd_idem {x : B.G R} (a : B.S2 R x) (h : a + a = a) : a = 0 := by
  obtain ⟨y, u⟩ := a
  change B.S2mk u + B.S2mk u = B.S2mk u at h
  change B.S2mk u = 0
  have hy' : y + y = y := congrArg Sigma.fst h
  have hy : y = 0 := add_left_cancel (hy'.trans (add_zero y).symm)
  subst hy
  obtain ⟨μ, rfl⟩ := B.exists_smul (B.zero2 x) u
  have e : (B.S2mk (B.smul μ (B.zero2 x))) = B.SecondaryComponentScale μ 0 := rfl
  rw [e] at h ⊢
  rw [S2smul_add, add_zero] at h
  have h2 : B.smul (μ * μ) (B.zero2 x) = B.smul μ (B.zero2 x) := eq_of_heq (Sigma.ext_iff.1 h).2
  have h3 : μ * μ = μ * 1 := by rw [B.smul_inj h2, mul_one]
  rw [mul_left_cancel h3, S2smul_one]
def SecondaryComponentMap {S : LAlg R₀} (f : LHom R S) (x : B.G R) : B.S2 R x →+ B.S2 S (B.map f x) where
  toFun a := ⟨B.map f a.1, B.pmap f a.2⟩
  map_zero' := Sigma.ext (map_zero _) (B.zeroSnd_nat f x)
  map_add' a b := Sigma.ext (map_add _ _ _) (B.addSnd_nat f a.2 b.2)
lemma zeroFst_addSnd (y y' : B.G R) : B.add2 (B.zero1 y) (B.zero1 y') = B.zero1 (y + y') := by
  let a : B.S1 R (y + y') := ⟨0, B.add2 (B.zero1 y) (B.zero1 y')⟩
  have h : a + a = a := by
    refine Sigma.ext (add_zero (0 : B.G R)) ?_
    show HEq (B.add1 (B.add2 (B.zero1 y) (B.zero1 y')) (B.add2 (B.zero1 y) (B.zero1 y')))
      (B.add2 (B.zero1 y) (B.zero1 y'))
    rw [← B.interchange]
    exact B.addSnd_hcongr (add_zero 0) rfl rfl (B.zeroFst_add _) (B.zeroFst_add _)
  exact eq_of_heq (Sigma.ext_iff.1 (B.fibreFst_idem a h)).2
lemma zeroSnd_addFst (x x' : B.G R) : B.add1 (B.zero2 x) (B.zero2 x') = B.zero2 (x + x') := by
  let a : B.S2 R (x + x') := ⟨0, B.add1 (B.zero2 x) (B.zero2 x')⟩
  have h : a + a = a := by
    refine Sigma.ext (add_zero (0 : B.G R)) ?_
    show HEq (B.add2 (B.add1 (B.zero2 x) (B.zero2 x')) (B.add1 (B.zero2 x) (B.zero2 x')))
      (B.add1 (B.zero2 x) (B.zero2 x'))
    rw [B.interchange]
    exact B.addFst_hcongr rfl rfl (add_zero 0) (B.zeroSnd_add _) (B.zeroSnd_add _)
  exact eq_of_heq (Sigma.ext_iff.1 (B.fibreSnd_idem a h)).2
lemma zeroFst_zero : B.zero1 (0 : B.G R) = B.zero2 0 := by
  let a : B.S1 R 0 := ⟨0, B.zero2 0⟩
  have h : a + a = a := by
    refine Sigma.ext (add_zero (0 : B.G R)) ?_
    show HEq (B.add1 (B.zero2 (0 : B.G R)) (B.zero2 0)) (B.zero2 (0 : B.G R))
    rw [zeroSnd_addFst]; exact B.heq_zero2 (add_zero 0)
  exact (eq_of_heq (Sigma.ext_iff.1 (B.fibreFst_idem a h)).2).symm
lemma nsmul2_zero1 (y : B.G R) (n : ℕ) : HEq (B.nsmul2 (B.zero1 y) n) (B.zero1 (n • y)) := by
  induction n with
  | zero =>
    refine (B.castSnd_heq _ _).trans ?_
    rw [← B.zeroFst_zero]; exact B.heq_zero1 (zero_nsmul y).symm
  | succ n ih =>
    refine (B.castSnd_heq _ _).trans ?_
    refine (B.addSnd_hcongr rfl rfl rfl ih HEq.rfl).trans ?_
    rw [zeroFst_addSnd]; exact B.heq_zero1 (succ_nsmul y n).symm
lemma nsmulSnd_addFst {x x' y : B.G R} (u : B.P R x y) (u' : B.P R x' y) (n : ℕ) :
    B.nsmul2 (B.add1 u u') n = B.add1 (B.nsmul2 u n) (B.nsmul2 u' n) := by
  induction n with
  | zero =>
    apply eq_of_heq
    refine (B.castSnd_heq _ _).trans ?_
    rw [← zeroSnd_addFst]
    exact B.addFst_hcongr rfl rfl (zero_nsmul y).symm (B.castSnd_heq (zero_nsmul y).symm (B.zero2 x)).symm
      (B.castSnd_heq (zero_nsmul y).symm (B.zero2 x')).symm
  | succ n ih =>
    apply eq_of_heq
    refine (B.castSnd_heq _ _).trans ?_
    rw [ih, B.interchange]
    exact B.addFst_hcongr rfl rfl (succ_nsmul y n).symm
      (B.castSnd_heq (succ_nsmul y n).symm (B.add2 (B.nsmul2 u n) u)).symm
      (B.castSnd_heq (succ_nsmul y n).symm (B.add2 (B.nsmul2 u' n) u')).symm
def S1n2 (y : B.G R) (n : ℕ) : B.S1 R y →+ B.S1 R (n • y) where
  toFun a := ⟨a.1, B.nsmul2 a.2 n⟩
  map_zero' := Sigma.ext rfl (B.nsmul2_zero1 y n)
  map_add' a b := Sigma.ext rfl (heq_of_eq (B.nsmulSnd_addFst a.2 b.2 n))
end BX
end ReciprocityTheory.PGsh


