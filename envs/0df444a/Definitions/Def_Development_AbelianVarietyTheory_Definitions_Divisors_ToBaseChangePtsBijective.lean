-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:21:53.968002+00:00
-- url     : https://prove2.me/theorems/fa39fc1d-2ed2-4542-a340-ba1df7097354
-- title:
--   To Base Change Pts Bijective
-- statement:
--   Definitions and structural lemmas for To Base Change Pts Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToBaseChangePtsBijective.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_map_comp
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange
import Theorems.Thm_GlobalTheory_PDivGroup_exists_comp_res_iff
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
import Theorems.Thm_GlobalTheory_PDiv_torsionIdeal_le_ker_iff
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
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_id
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_mk


set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory
namespace GlobalTheory
namespace PDiv
section Semi
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
@[ext] structure SemiBialgHom (σ : R →+* R') (A A' : Type) [CommRing A] [Bialgebra R A]
    [CommRing A'] [Bialgebra R' A'] : Type where

  toRingHom : A →+* A'

  smul_map : ∀ (r : R) (a : A), toRingHom (r • a) = σ r • toRingHom a

  counit_map : ∀ a, counit (R := R') (toRingHom a) = σ (counit a)

  comul_map : ∀ a, comul (R := R') (toRingHom a) =
    TensorProduct.map (σ₁₂ := σ) ⟨⟨toRingHom, toRingHom.map_add⟩, smul_map⟩
      ⟨⟨toRingHom, toRingHom.map_add⟩, smul_map⟩ (comul a)
variable {σ : R →+* R'} {τ : R' →+* R''} {A A' A'' : Type} [CommRing A] [Bialgebra R A]
  [CommRing A'] [Bialgebra R' A'] [CommRing A''] [Bialgebra R'' A'']
theorem map_smul_of_algebraMap {A A' : Type} [CommRing A] [Algebra R A] [CommRing A']
    [Algebra R' A'] (f : A →+* A') (h : ∀ r, f (algebraMap R A r) = algebraMap R' A' (σ r))
    (r : R) (a : A) : f (r • a) = σ r • f a := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, h]
namespace SemiBialgHom
instance : CoeFun (SemiBialgHom σ A A') fun _ => A → A' := ⟨fun f => f.toRingHom⟩
variable (f : SemiBialgHom σ A A')
def lin : A →ₛₗ[σ] A' := ⟨⟨f.toRingHom, f.toRingHom.map_add⟩, f.smul_map⟩
@[simp] theorem lin_apply (a : A) : f.lin a = f a := rfl
theorem map_algebraMap (r : R) : f (algebraMap R A r) = algebraMap R' A' (σ r) := by
  rw [Algebra.algebraMap_eq_smul_one, f.smul_map, map_one, Algebra.algebraMap_eq_smul_one]
abbrev two : A ⊗[R] A →ₛₗ[σ] A' ⊗[R'] A' := TensorProduct.map f.lin f.lin
theorem two_comul (a : A) : f.two (comul a) = comul (f a) := (f.comul_map a).symm
def ofBialgHom {B : Type} [CommRing B] [Bialgebra R B] (g : A →ₐc[R] B) :
    SemiBialgHom (RingHom.id R) A B where
  toRingHom := g
  smul_map := map_smul g
  counit_map := CoalgHomClass.counit_comp_apply g
  comul_map a := (pullTwo_comul g a).symm
@[simp] theorem ofBialgHom_apply {B : Type} [CommRing B] [Bialgebra R B] (g : A →ₐc[R] B) (a : A) :
    ofBialgHom g a = g a := rfl
def toBialgHom {B : Type} [CommRing B] [Bialgebra R B] (g : SemiBialgHom (RingHom.id R) A B) :
    A →ₐc[R] B :=
  .ofAlgHom { g.toRingHom with commutes' := g.map_algebraMap } (AlgHom.ext g.counit_map)
    (AlgHom.ext g.two_comul)
@[simp] theorem toBialgHom_apply {B : Type} [CommRing B] [Bialgebra R B]
    (g : SemiBialgHom (RingHom.id R) A B) (a : A) : g.toBialgHom a = g a := rfl
theorem two_two (g : SemiBialgHom τ A' A'') {ρ : R →+* R''} (k : A →ₛₗ[ρ] A'')
    (h : ∀ a, k a = g (f a)) (c : A ⊗[R] A) : g.two (f.two c) = TensorProduct.map k k c := by
  induction c with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp [h]
def comp (g : SemiBialgHom τ A' A'') (f : SemiBialgHom σ A A') :
    SemiBialgHom (τ.comp σ) A A'' where
  toRingHom := g.toRingHom.comp f.toRingHom
  smul_map r a := by simp [f.smul_map, g.smul_map]
  counit_map a := by simp [f.counit_map, g.counit_map]
  comul_map a := by
    rw [RingHom.comp_apply, ← g.two_comul, ← f.two_comul]
    exact f.two_two g _ (fun _ => rfl) _
@[simp] theorem comp_apply (g : SemiBialgHom τ A' A'') (a : A) : g.comp f a = g (f a) := rfl
section Points
variable (B : Type) [CommRing B] [Algebra R B] [Algebra R' B]
  (hB : ∀ r, algebraMap R B r = algebraMap R' B (σ r))
def pts : WithConv (A' →ₐ[R'] B) →* WithConv (A →ₐ[R] B) where
  toFun x := toConv { (x.ofConv : A' →+* B).comp f.toRingHom with
    commutes' := fun r => by simp [f.map_algebraMap, hB] }
  map_one' := ofConv_injective (AlgHom.ext fun a => by
    change (1 : WithConv (A' →ₐ[R'] B)).ofConv (f a) = _
    rw [AlgHom.convOne_apply, AlgHom.convOne_apply, f.counit_map, hB])
  map_mul' x y := ofConv_injective (AlgHom.ext fun a => by
    change (x * y).ofConv (f a) = _
    rw [AlgHom.convMul_apply, AlgHom.convMul_apply, ← f.two_comul]
    generalize comul (R := R) a = c
    induction c with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => rfl)
@[simp] theorem pts_apply (x : WithConv (A' →ₐ[R'] B)) (a : A) :
    (f.pts B hB x).ofConv a = x.ofConv (f a) := rfl
end Points
def ofPts (g : A →+* A') (hg : ∀ r, g (algebraMap R A r) = algebraMap R' A' (σ r))
    (h1 : ∀ a, counit (R := R') (g a) = σ (counit a))
    (h2 : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra R' B],
      (∀ r, algebraMap R B r = algebraMap R' B (σ r)) →
      ∀ (x y : WithConv (A' →ₐ[R'] B)) (x₀ y₀ : WithConv (A →ₐ[R] B)),
        (∀ a, x₀.ofConv a = x.ofConv (g a)) → (∀ a, y₀.ofConv a = y.ofConv (g a)) →
        ∀ a, (x₀ * y₀).ofConv a = (x * y).ofConv (g a)) : SemiBialgHom σ A A' where
  toRingHom := g
  smul_map := map_smul_of_algebraMap g hg
  counit_map := h1
  comul_map a := by
    letI : Algebra R (A' ⊗[R'] A') := ((algebraMap R' _).comp σ).toAlgebra
    let u : (A' →ₐ[R'] A' ⊗[R'] A') → (A →ₐ[R] A' ⊗[R'] A') := fun x =>
      { (x : A' →+* A' ⊗[R'] A').comp g with
        commutes' := fun r => (congrArg x (hg r)).trans (x.commutes _) }
    have h := h2 (A' ⊗[R'] A') (fun _ => rfl) (toConv Algebra.TensorProduct.includeLeft)
      (toConv Algebra.TensorProduct.includeRight) (toConv (u Algebra.TensorProduct.includeLeft))
      (toConv (u Algebra.TensorProduct.includeRight))
      (fun _ => rfl) (fun _ => rfl) a
    rw [AlgHom.convMul_apply, AlgHom.convMul_apply] at h
    have e : ∀ c : A' ⊗[R'] A', Algebra.TensorProduct.lift
        (Algebra.TensorProduct.includeLeft : A' →ₐ[R'] A' ⊗[R'] A')
        Algebra.TensorProduct.includeRight (fun _ _ => .all _ _) c = c := fun c => by simp
    refine ((e _).symm.trans h.symm).trans ?_
    generalize comul (R := R) a = c
    induction c with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      rw [Algebra.TensorProduct.lift_tmul, TensorProduct.map_tmul]
      exact (Algebra.TensorProduct.tmul_mul_tmul ..).trans (by simp)
def cot : Cot R A →ₛₗ[σ] Cot R' A' :=
  letI : Module R (Cot R' A') := Module.compHom _ σ
  let D : A →ₗ[R] Cot R' A' :=
    { toFun := fun a => dUnit R' (f a)
      map_add' := fun a b => by rw [map_add, dUnit, map_add]
      map_smul' := fun r a => by rw [f.smul_map, dUnit, LinearMap.map_smul]; rfl }
  { (AugCot.lift (counitAlgHom R A) D fun a b => by
      change dUnit R' (f (a * b)) = σ (counit a) • dUnit R' (f b) + σ (counit b) • dUnit R' (f a)
      rw [map_mul, dUnit, AugCot.d_mul, ← f.counit_map, ← f.counit_map]
      rfl) with }
@[simp] theorem cot_d (a : A) : f.cot (dUnit R a) = dUnit R' (f a) := by
  change dUnit R' (f (a - algebraMap R A (counit a))) = _
  rw [map_sub, f.map_algebraMap, dUnit, map_sub, AugCot.d_algebraMap, sub_zero]
theorem two_cobOne (b : A) : f.two (cobOne R A b) = cobOne R' A' (f b) := by
  simp [cobOne_apply, two_comul]
theorem cobTwo_two (c : A ⊗[R] A) :
    cobTwo R' A' (f.two c) = TensorProduct.map f.lin f.two (cobTwo R A c) := by
  induction c with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    have h : ∀ t : A ⊗[R] A, TensorProduct.map f.lin f.two (TensorProduct.assoc R A A A (t ⊗ₜ b)) =
        TensorProduct.assoc R' A' A' A' (f.two t ⊗ₜ f b) := fun t => by
      induction t with
      | zero => simp
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
      | tmul a b => simp
    simp [cobTwo_apply, ← two_comul, h]
theorem two_mem {c : A ⊗[R] A} (hc : c ∈ symCocycles R A) : f.two c ∈ symCocycles R' A' := by
  rw [mem_symCocycles] at hc ⊢
  refine ⟨by rw [cobTwo_two, hc.1, map_zero], ?_⟩
  conv_rhs => rw [← hc.2]
  generalize c = t
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp
end SemiBialgHom
section BaseChange
variable (R R' A) [Algebra R R']
def toBaseChange : SemiBialgHom (algebraMap R R') A (R' ⊗[R] A) where
  toRingHom := (Algebra.TensorProduct.includeRight : A →ₐ[R] R' ⊗[R] A)
  smul_map r a := by simp
  counit_map a := by simp [Algebra.smul_def]
  comul_map a := by
    change comul (R := R') ((1 : R') ⊗ₜ[R] a) = _
    rw [TensorProduct.comul_tmul]
    generalize comul (R := R) a = c
    induction c with
    | zero => simp
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
    | tmul a b => simp
@[simp] theorem toBaseChange_apply (a : A) : toBaseChange R R' A a = (1 : R') ⊗ₜ[R] a := rfl
variable {R A} in

theorem toBaseChange_pts_bijective (B : Type) [CommRing B] [Algebra R B] [Algebra R' B]
    (hB : ∀ r, algebraMap R B r = algebraMap R' B (algebraMap R R' r)) :
    Function.Bijective ((toBaseChange R R' A).pts B hB) := by
  haveI : IsScalarTower R R' B := .of_algebraMap_eq hB
  refine ⟨fun x y h => ofConv_injective (Algebra.TensorProduct.ext (Subsingleton.elim _ _)
    (AlgHom.ext fun a => DFunLike.congr_fun (congrArg ofConv h) a)), fun x => ?_⟩
  exact ⟨toConv (Algebra.TensorProduct.lift (Algebra.ofId R' B) x.ofConv fun _ _ => .all _ _),
    ofConv_injective (AlgHom.ext fun a => by simp)⟩
variable {R R' A}
def bcMap (R' : Type) [CommRing R'] [Algebra R R'] {C : Type} [CommRing C] [Bialgebra R C]
    (g : A →ₐc[R] C) : R' ⊗[R] A →ₐc[R'] R' ⊗[R] C :=
  Bialgebra.TensorProduct.map (BialgHom.id R' R') g
@[simp] theorem bcMap_tmul {C : Type} [CommRing C] [Bialgebra R C] (g : A →ₐc[R] C) (r : R')
    (a : A) : bcMap R' g (r ⊗ₜ a) = r ⊗ₜ g a := rfl
theorem bc_hom_ext {g h : R' ⊗[R] A →ₐc[R'] A'} (e : ∀ a, g (1 ⊗ₜ a) = h (1 ⊗ₜ a)) : g = h :=
  BialgHom.ext fun x => by
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a => rw [← mul_one r, ← smul_eq_mul, ← smul_tmul', map_smul, map_smul, e]
def SemiBialgHom.liftBC (f : SemiBialgHom (algebraMap R R') A A') : R' ⊗[R] A →ₐc[R'] A' :=
  letI : Algebra R A' := ((algebraMap R' A').comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' A' := .of_algebraMap_eq fun _ => rfl
  let g : R' ⊗[R] A →ₐ[R'] A' := Algebra.TensorProduct.lift (Algebra.ofId R' A')
    { f.toRingHom with commutes' := f.map_algebraMap } fun _ _ => .all _ _
  have hg : ∀ a, g (1 ⊗ₜ a) = f a := fun a => by simp [g]
  .ofAlgHom g
    (AlgHom.ext fun x => by
      induction x with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul r a =>
        rw [← mul_one r, ← smul_eq_mul, ← smul_tmul', map_smul, map_smul, AlgHom.comp_apply, hg]
        exact congrArg _ ((f.counit_map a).trans ((toBaseChange R R' A).counit_map a).symm))
    (AlgHom.ext fun x => by
      induction x with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul r a =>
        rw [← mul_one r, ← smul_eq_mul, ← smul_tmul', map_smul, map_smul, AlgHom.comp_apply,
          AlgHom.comp_apply, hg]
        congr 1
        change Algebra.TensorProduct.map g g (comul (toBaseChange R R' A a)) = comul (f a)
        rw [← SemiBialgHom.two_comul, ← SemiBialgHom.two_comul]
        generalize comul (R := R) a = c
        induction c with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul a b => simp [hg])
@[simp] theorem SemiBialgHom.liftBC_tmul (f : SemiBialgHom (algebraMap R R') A A') (r : R')
    (a : A) : f.liftBC (r ⊗ₜ a) = r • f a := (Algebra.smul_def r (f a)).symm
end BaseChange
end Semi
end PDiv
namespace PDivGroup
open PDiv
variable {p : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
@[ext] structure SemiHom (σ : O →+* O') (G' : PDivGroup p O') (G : PDivGroup p O) : Type where

  app : ∀ n, SemiBialgHom σ (G.A n) (G'.A n)

  res_app : ∀ n a, G'.res n (app (n + 1) a) = app n (G.res n a)
namespace SemiHom
variable {σ : O →+* O'} {τ : O' →+* O''} {G H : PDivGroup p O} {G' H' : PDivGroup p O'}
  {G'' : PDivGroup p O''}
theorem ext_apply {s t : SemiHom σ G' G} (h : ∀ n a, s.app n a = t.app n a) : s = t :=
  SemiHom.ext (funext fun n => SemiBialgHom.ext (RingHom.ext (h n)))
def ofHom (f : G ⟶ H) : SemiHom (RingHom.id O) G H :=
  ⟨fun n => .ofBialgHom (f.app n), PDivGroup.res_app f⟩
@[simp] theorem ofHom_app (f : G ⟶ H) (n : ℕ) (a : H.A n) : (ofHom f).app n a = f.app n a := rfl
def toHom (s : SemiHom (RingHom.id O) G H) : G ⟶ H :=
  ⟨fun n => (s.app n).toBialgHom, fun n => BialgHom.ext (s.res_app n)⟩
@[simp] theorem toHom_app (s : SemiHom (RingHom.id O) G H) (n : ℕ) (a : H.A n) :
    s.toHom.app n a = s.app n a := rfl
def comp (t : SemiHom τ G'' G') (s : SemiHom σ G' G) : SemiHom (τ.comp σ) G'' G :=
  ⟨fun n => (t.app n).comp (s.app n), fun n a => by simp [t.res_app, s.res_app]⟩
@[simp] theorem comp_app (t : SemiHom τ G'' G') (s : SemiHom σ G' G) (n : ℕ) (a : G.A n) :
    (t.comp s).app n a = t.app n (s.app n a) := rfl
variable (s : SemiHom σ G' G)
def funs : G.funs →ₛₗ[σ] G'.funs where
  toFun b := ⟨fun n => s.app n (b.1 n), fun n => (s.res_app n _).trans (congrArg _ (b.2 n))⟩
  map_add' _ _ := Subtype.ext (funext fun n => map_add (s.app n).lin _ _)
  map_smul' _ _ := Subtype.ext (funext fun n => (s.app n).smul_map _ _)
@[simp] theorem funs_val (b : G.funs) (n : ℕ) : (s.funs b).1 n = s.app n (b.1 n) := rfl
theorem res_two (n : ℕ) (c : G.A (n + 1) ⊗[O] G.A (n + 1)) :
    pullbackTwo (G'.res n) ((s.app (n + 1)).two c) = (s.app n).two (pullbackTwo (G.res n) c) := by
  induction c with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp [s.res_app]
def cocycles : G.cocycles →ₛₗ[σ] G'.cocycles where
  toFun c := ⟨fun n => (s.app n).two (c.1 n), fun n => ⟨(s.app n).two_mem (c.2 n).1,
    (s.res_two n _).trans (congrArg _ (c.2 n).2)⟩⟩
  map_add' _ _ := Subtype.ext (funext fun n => map_add (s.app n).two _ _)
  map_smul' _ _ := Subtype.ext (funext fun n => map_smulₛₗ (s.app n).two _ _)
@[simp] theorem cocycles_val (c : G.cocycles) (n : ℕ) :
    (s.cocycles c).1 n = (s.app n).two (c.1 n) := rfl
theorem res_cot (n : ℕ) (w : Cot O (G.A (n + 1))) :
    cotMap (G'.res n) ((s.app (n + 1)).cot w) = (s.app n).cot (cotMap (G.res n) w) := by
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ w
  simp [s.res_app]
def omega : G.omega →ₛₗ[σ] G'.omega where
  toFun w := ⟨fun n => (s.app n).cot (w.1 n), fun n => (s.res_cot n _).trans (congrArg _ (w.2 n))⟩
  map_add' _ _ := Subtype.ext (funext fun n => map_add (s.app n).cot _ _)
  map_smul' _ _ := Subtype.ext (funext fun n => map_smulₛₗ (s.app n).cot _ _)
@[simp] theorem omega_val (w : G.omega) (n : ℕ) : (s.omega w).1 n = (s.app n).cot (w.1 n) := rfl
theorem cocycles_cob (b : G.funs) : s.cocycles (G.cob b) = G'.cob (s.funs b) :=
  Subtype.ext (funext fun n => (s.app n).two_cobOne _)
theorem omega_dFun (b : G.funs) : s.omega (G.dFun b) = G'.dFun (s.funs b) :=
  Subtype.ext (funext fun n => (s.app n).cot_d _)
def vecExt : G.VecExt →ₛₗ[σ] G'.VecExt :=
  Submodule.mapQ _ _ s.cocycles (by rintro _ ⟨b, rfl⟩; exact ⟨s.funs b, (s.cocycles_cob b).symm⟩)
def pair : G.cocycles × G.omega →ₛₗ[σ] G'.cocycles × G'.omega where
  toFun x := (s.cocycles x.1, s.omega x.2)
  map_add' _ _ := Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' _ _ := Prod.ext (map_smulₛₗ _ _ _) (map_smulₛₗ _ _ _)
def rig : G.RigExt →ₛₗ[σ] G'.RigExt :=
  Submodule.mapQ _ _ s.pair (by
    rintro _ ⟨b, rfl⟩
    exact ⟨s.funs b, Prod.ext (s.cocycles_cob b).symm (s.omega_dFun b).symm⟩)
@[simp] theorem rig_mk (c : G.cocycles) (w : G.omega) :
    s.rig (G.rigMk (c, w)) = G'.rigMk (s.cocycles c, s.omega w) := rfl
section Comp
variable (t : SemiHom τ G'' G') {ρ : O →+* O''} (u : SemiHom ρ G'' G)
  (h : ∀ n a, u.app n a = t.app n (s.app n a))
include h
end Comp
@[simp] theorem ofHom_cocycles (f : G ⟶ H) : (ofHom f).cocycles = cocyclesMap f := rfl
variable [Fact p.Prime]
@[simp] theorem ofHom_omega (f : G ⟶ H) : (ofHom f).omega = omegaMap G H f :=
  LinearMap.ext fun w => Subtype.ext (funext fun n => by
    obtain ⟨a, ha⟩ := AugCot.d_surjective _ (w.1 n)
    simp [← ha])
@[simp] theorem ofHom_rig (f : G ⟶ H) : (ofHom f).rig = rigExtMap f :=
  LinearMap.ext fun x => by
    obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    exact congrArg G.rigMk (Prod.ext rfl (LinearMap.congr_fun (ofHom_omega f) w))
end SemiHom
section BaseChange
variable (G H K : PDivGroup p O) (O') [Algebra O O']
@[reducible] def baseChange : PDivGroup p O' where
  height := G.height
  A n := O' ⊗[O] G.A n
  rank_eq n q := (Module.rankAtStalk_baseChange q).trans (G.rank_eq n _)
  res n := bcMap O' (G.res n)
  res_surjective n := LinearMap.lTensor_surjective O' (g := (G.res n : G.A (n + 1) →ₗ[O] G.A n))
    (G.res_surjective n)
  ker_res n := by
    have key : ∀ (B : Type) [CommRing B] [Algebra O' B] (x : O' ⊗[O] G.A (n + 1) →ₐ[O'] B),
        toConv x ^ p ^ n = 1 ↔ ∃ y : O' ⊗[O] G.A n →ₐ[O'] B,
          y.comp (bcMap O' (G.res n) : O' ⊗[O] G.A (n + 1) →ₐ[O'] O' ⊗[O] G.A n) = x := by
      intro B _ _ x
      letI : Algebra O B := ((algebraMap O' B).comp (algebraMap O O')).toAlgebra
      have hb := fun m => toBaseChange_pts_bijective (R := O) O' (A := G.A m) B fun _ => rfl
      rw [← (hb (n + 1)).1.eq_iff, map_pow, map_one]
      refine (G.exists_comp_res_iff n _).symm.trans ⟨fun ⟨y, hy⟩ => ?_, fun ⟨y, hy⟩ => ?_⟩
      · obtain ⟨z, hz⟩ := (hb n).2 (toConv y)
        refine ⟨z.ofConv, congrArg ofConv ((hb (n + 1)).1 (a₁ := toConv _) (a₂ := toConv x)
          (ofConv_injective (AlgHom.ext fun a => ?_)))⟩
        exact (DFunLike.congr_fun (congrArg ofConv hz) (G.res n a)).trans (DFunLike.congr_fun hy a)
      · exact ⟨((toBaseChange O O' _).pts B (fun _ => rfl) (toConv y)).ofConv,
          AlgHom.ext fun a => DFunLike.congr_fun hy (1 ⊗ₜ a)⟩
    refine le_antisymm (fun a ha => ?_) ((torsionIdeal_le_ker_iff _
      (bcMap O' (G.res n) : O' ⊗[O] G.A (n + 1) →ₐ[O'] O' ⊗[O] G.A n)).2
        ((key _ _).2 ⟨AlgHom.id _ _, rfl⟩))
    obtain ⟨y, hy⟩ := (key _ (Ideal.Quotient.mkₐ O' (torsionIdeal O' _ (p ^ n)))).1
      ((torsionIdeal_le_ker_iff _ _).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha)
    have h := DFunLike.congr_fun hy a
    have ha' : bcMap O' (G.res n) a = 0 := ha
    exact Ideal.Quotient.eq_zero_iff_mem.1 (h.symm.trans ((congrArg y ha').trans (map_zero y)))
def toBase : SemiHom (algebraMap O O') (G.baseChange O') G :=
  ⟨fun n => toBaseChange O O' (G.A n), fun _ _ => rfl⟩
@[simp] theorem toBase_app (n : ℕ) (a : G.A n) : (G.toBase O').app n a = (1 : O') ⊗ₜ[O] a := rfl
variable {G H K}
def baseChangeMap (f : G ⟶ H) : G.baseChange O' ⟶ H.baseChange O' :=
  ⟨fun n => bcMap O' (f.app n), fun n => bc_hom_ext fun a => congrArg ((1 : O') ⊗ₜ[O] ·) (res_app f n a)⟩
@[simp] theorem baseChangeMap_app (f : G ⟶ H) (n : ℕ) :
    (baseChangeMap O' f).app n = bcMap O' (f.app n) := rfl
variable {O'} in

theorem baseChange_hom_ext {G' : PDivGroup p O'} {f g : G' ⟶ G.baseChange O'}
    (h : ∀ n a, f.app n (1 ⊗ₜ a) = g.app n (1 ⊗ₜ a)) : f = g :=
  hom_ext fun n => bc_hom_ext (h n)
variable (p O) in

@[simps] def baseChangeFunctor : PDivGroup p O ⥤ PDivGroup p O' where
  obj G := G.baseChange O'
  map := baseChangeMap O'
  map_id _ := baseChange_hom_ext fun _ _ => rfl
  map_comp _ _ := baseChange_hom_ext fun _ _ => rfl
variable {O'}
def SemiHom.lift {G' : PDivGroup p O'} (s : SemiHom (algebraMap O O') G' G) :
    G' ⟶ G.baseChange O' :=
  ⟨fun n => (s.app n).liftBC, fun n => bc_hom_ext fun a => by simp [s.res_app]⟩
@[simp] theorem SemiHom.lift_app {G' : PDivGroup p O'} (s : SemiHom (algebraMap O O') G' G)
    (n : ℕ) (r : O') (a : G.A n) : s.lift.app n (r ⊗ₜ a) = r • s.app n a :=
  (s.app n).liftBC_tmul r a
variable (G) in

def semiHomEquiv (G' : PDivGroup p O') :
    SemiHom (algebraMap O O') G' G ≃ (G' ⟶ G.baseChange O') where
  toFun := SemiHom.lift
  invFun f := (SemiHom.ofHom f).comp (G.toBase O')
  left_inv s := SemiHom.ext_apply fun n a => (s.lift_app n 1 a).trans (one_smul _ _)
  right_inv f := baseChange_hom_ext fun n a => (SemiHom.lift_app _ n 1 a).trans (one_smul _ _)
end BaseChange
section Examples
variable [Fact p.Prime]
example [Algebra O O'] (n : ℕ) : (((mu p O).toBase O').omega (dlogT p O)).1 n =
    dUnit O' ((1 : O') ⊗ₜ[O] muT O (p ^ n)) := SemiBialgHom.cot_d _ _
example [Algebra O O'] : ((mu p O).baseChange O').height = 1 := rfl
end Examples
end PDivGroup
end GlobalTheory


