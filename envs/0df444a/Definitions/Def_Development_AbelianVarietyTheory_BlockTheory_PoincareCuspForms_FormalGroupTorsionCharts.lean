-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_FormalGroupTorsionCharts
-- name    : Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_FormalGroupTorsionCharts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:43.020419+00:00
-- url     : https://prove2.me/theorems/03cb5456-db6d-4fda-8389-b70f5a475280
-- title:
--   Formal Group Torsion Charts
-- statement:
--   Definitions and structural lemmas for Formal Group Torsion Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/FormalGroupTorsionCharts.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing TensorProduct ReciprocityTheory.PGsh
namespace GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts
universe u v
section Eval
variable {A : Type*} {R : Type*} [CommRing A] [CommRing R] [Algebra A R] {σ : Type*}
def evalTerm (F : MvPowerSeries σ A) (x : σ → R) (d : σ →₀ ℕ) : R :=
  MvPowerSeries.coeff d F • d.prod fun i n => x i ^ n
theorem evalTerm_finite [Finite σ] (F : MvPowerSeries σ A) (x : σ → R)
    (hx : ∀ i, IsNilpotent (x i)) : (Function.support (evalTerm F x)).Finite := by
  classical
  choose N hN using hx
  haveI := Fintype.ofFinite σ
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm N)).subset fun d hd => ?_
  by_contra hcon
  apply hd
  have : ∃ i, N i < d i := by
    by_contra h
    push Not at h
    exact hcon fun i => by simpa using h i
  obtain ⟨i, hi⟩ := this
  have hi0 : i ∈ d.support := by
    rw [Finsupp.mem_support_iff]; omega
  unfold evalTerm
  have h0 : x i ^ d i = 0 := pow_eq_zero_of_le hi.le (hN i)
  rw [Finsupp.prod, Finset.prod_eq_zero (f := fun a => x a ^ d a) hi0 h0, smul_zero]
def evalNil [Finite σ] (F : MvPowerSeries σ A) (x : σ → R) (hx : ∀ i, IsNilpotent (x i)) : R :=
  ∑ d ∈ (evalTerm_finite F x hx).toFinset, evalTerm F x d
theorem evalNil_eq_finsum [Finite σ] (F : MvPowerSeries σ A) (x : σ → R)
    (hx : ∀ i, IsNilpotent (x i)) : evalNil F x hx = ∑ᶠ d, evalTerm F x d :=
  (finsum_eq_sum _ (evalTerm_finite F x hx)).symm
example [Finite σ] (x : σ → R) (hx : ∀ i, IsNilpotent (x i)) (j : σ) :
    evalNil (MvPowerSeries.X j : MvPowerSeries σ A) x hx = x j := by
  classical
  rw [evalNil_eq_finsum, finsum_eq_single _ (Finsupp.single j 1)]
  · simp [evalTerm, MvPowerSeries.coeff_X]
  · intro d hd
    simp [evalTerm, MvPowerSeries.coeff_X, hd]
end Eval
open MvPowerSeries in

structure FormalGroupLaw (A : Type*) [CommRing A] (g : ℕ) where

  F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) A
  const : ∀ a, constantCoeff (F a) = 0
  lin_left : ∀ a b, coeff (Finsupp.single (Sum.inl b) 1) (F a) = if a = b then 1 else 0
  lin_right : ∀ a b, coeff (Finsupp.single (Sum.inr b) 1) (F a) = if a = b then 1 else 0

  assoc : ∀ a,
    (F a).subst (Sum.elim
        (fun b => (F b).subst (Sum.elim (fun c => (X (0, c) : MvPowerSeries (Fin 3 × Fin g) A))
          (fun c => X (1, c))))
        (fun b => (X (2, b) : MvPowerSeries (Fin 3 × Fin g) A))) =
      (F a).subst (Sum.elim (fun b => (X (0, b) : MvPowerSeries (Fin 3 × Fin g) A))
        (fun b => (F b).subst (Sum.elim (fun c => (X (1, c) : MvPowerSeries (Fin 3 × Fin g) A))
          (fun c => X (2, c)))))

  comm : ∀ a, (F a).subst (fun s => (X s.swap : MvPowerSeries (Fin g ⊕ Fin g) A)) = F a
open MvPowerSeries in

def FormalGroupLaw.additive (A : Type*) [CommRing A] (g : ℕ) : FormalGroupLaw A g where
  F a := X (Sum.inl a) + X (Sum.inr a)
  const a := by simp
  lin_left a b := by
    classical
    simp [coeff_X, Finsupp.single_left_inj, eq_comm]
  lin_right a b := by
    classical
    simp [coeff_X, Finsupp.single_left_inj, eq_comm]
  assoc a := by
    have h : ∀ {τ : Type} (f : Fin g ⊕ Fin g → MvPowerSeries τ A),
        (∀ s, constantCoeff (f s) = 0) → ∀ b,
        (X (Sum.inl b) + X (Sum.inr b) : MvPowerSeries (Fin g ⊕ Fin g) A).subst f =
          f (Sum.inl b) + f (Sum.inr b) := fun f hf b => by
      have hs : HasSubst f := hasSubst_of_constantCoeff_zero hf
      rw [subst_add hs, subst_X hs, subst_X hs]
    have h1 : ∀ (i j : Fin 3) (b : Fin g),
        (X (Sum.inl b) + X (Sum.inr b) : MvPowerSeries (Fin g ⊕ Fin g) A).subst
          (Sum.elim (fun c => (X (i, c) : MvPowerSeries (Fin 3 × Fin g) A)) (fun c => X (j, c))) =
          X (i, b) + X (j, b) := fun i j b => by
      rw [h _ (by rintro (s | s) <;> simp)]; simp
    simp only [h1]
    rw [h _ (by rintro (s | s) <;> simp), h _ (by rintro (s | s) <;> simp)]
    simp [add_assoc]
  comm a := by
    have hs : HasSubst (fun s : Fin g ⊕ Fin g => (X s.swap : MvPowerSeries (Fin g ⊕ Fin g) A)) :=
      hasSubst_of_constantCoeff_zero (by simp)
    rw [subst_add hs, subst_X hs, subst_X hs]
    simp [add_comm]
variable {R₀ : Type u} [CommRing R₀]
structure ResAlg (k : LAlg R₀) where

  alg : LAlg R₀

  res : LHom alg k
  res_surj : Function.Surjective res.1
  res_ker : RingHom.ker res.1 = maximalIdeal (alg : Type u)
structure NilAlg (k : LAlg R₀) extends ResAlg k where
  nil : ∀ x ∈ maximalIdeal (alg : Type u), IsNilpotent x
variable {k : LAlg R₀}
abbrev kerRes (B : BX R₀) (R : ResAlg k) : AddSubgroup (B.G R.alg) := (B.map R.res).ker
theorem map_mem_kerRes (B : BX R₀) {R S : ResAlg k} (f : LHom R.alg S.alg)
    (hf : S.res.comp f = R.res) (x : kerRes B R) : B.map f x ∈ kerRes B S := by
  rw [AddMonoidHom.mem_ker, ← B.map_comp, hf]
  exact x.2
theorem tg_mem_kerRes (B : BX R₀) (R : ResAlg k) {S : LAlg R₀} (π : LHom R.alg S)
    (hπ : π.SqZero) (w : B.gg ⊗[R₀] π.ker) : B.tg π hπ w ∈ kerRes B R := by
  have hle : RingHom.ker π.1 ≤ RingHom.ker R.res.1 := by
    rw [R.res_ker]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  let r : (S : Type u) →ₐ[R₀] (k : Type u) := AlgHom.liftOfSurjective π.1 hπ.1 R.res.1 hle
  have hr : ∀ a, r (π.1 a) = R.res.1 a := fun a => AlgHom.liftOfSurjective_apply _ _ _ _ a
  let r' : LHom S k := ⟨r, ⟨fun s hs => by
    obtain ⟨a, rfl⟩ := hπ.1 s
    have h1 : IsUnit (R.res.1 a) := by rw [← hr]; exact hs
    exact (R.res.2.map_nonunit a h1).map π.1⟩⟩
  have hc : r'.comp π = R.res := Subtype.ext (AlgHom.ext hr)
  rw [AddMonoidHom.mem_ker, ← hc, B.map_comp, (B.tg_ker π hπ _).2 ⟨w, rfl⟩, map_zero]
structure FormalChart (B : BX R₀) {g : ℕ} (gb : Module.Basis (Fin g) R₀ B.gg) (k : LAlg R₀) where

  law : FormalGroupLaw R₀ g

  coord : ∀ R : NilAlg k, kerRes B R.toResAlg ≃ (Fin g → maximalIdeal (R.alg : Type u))
  coord_nat : ∀ (R S : NilAlg k) (f : LHom R.alg S.alg) (hf : S.res.comp f = R.res)
    (x : kerRes B R.toResAlg) (a : Fin g),
    (coord S ⟨B.map f x, map_mem_kerRes B f hf x⟩ a : (S.alg : Type u)) =
      f.1 (coord R x a : (R.alg : Type u))
  coord_add : ∀ (R : NilAlg k) (x y : kerRes B R.toResAlg) (a : Fin g),
    (coord R (x + y) a : (R.alg : Type u)) =
      evalNil (law.F a) (fun s => (Sum.elim (coord R x) (coord R y) s).1)
        (fun s => R.nil _ (Sum.elim (coord R x) (coord R y) s).2)
  coord_tg : ∀ (R : NilAlg k) (S : LAlg R₀) (π : LHom R.alg S) (hπ : π.SqZero) (w : B.gg)
    (i : π.ker) (a : Fin g),
    (coord R ⟨B.tg π hπ (w ⊗ₜ i), tg_mem_kerRes B R.toResAlg π hπ _⟩ a : (R.alg : Type u)) =
      gb.repr w a • (i : (R.alg : Type u))
def LiftsFromResidue (B : BX R₀) (W : NilAlg k) : Prop :=
  Function.Surjective (B.map W.res)
abbrev Tors (B : BX R₀) (n : ℕ) (R : LAlg R₀) : AddSubgroup (B.G R) :=
  AddSubgroup.torsionBy (B.G R) n
def tateModule (B : BX R₀) (p : ℕ) (O : LAlg R₀) : AddSubgroup (ℕ → B.G O) where
  carrier := {τ | (∀ n, p ^ (n + 1) • τ n = 0) ∧ ∀ n, τ n = p • τ (n + 1)}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨fun n => by simp [ha n, hb n], fun n => by
      rw [Pi.add_apply, Pi.add_apply, smul_add, ← ha' n, ← hb' n]⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨fun n => by simp [ha n], fun n => by
      rw [Pi.neg_apply, Pi.neg_apply, smul_neg, ← ha' n]⟩
structure TorsionRep (B : BX R₀) (p : ℕ) (O : ResAlg k) where

  A : Tors B p k → ResAlg k

  str : ∀ x, LHom O.alg (A x).alg
  str_res : ∀ x, (A x).res.comp (str x) = O.res

  y : ∀ x, Tors B p (A x).alg
  y_res : ∀ x, B.map (A x).res (y x : B.G (A x).alg) = (x : B.G k)
  universal : ∀ (S : LAlg R₀) (s : LHom O.alg S) (t : Tors B p S),
    ∃! c : Σ x : Tors B p k, LHom (A x).alg S,
      c.2.comp (str c.1) = s ∧ B.map c.2 (y c.1 : B.G (A c.1).alg) = (t : B.G S)
namespace TorsionRep
variable {B : BX R₀} {p : ℕ} {O : ResAlg k} (D : TorsionRep B p O)
instance (x : Tors B p k) : Algebra (O.alg : Type u) ((D.A x).alg : Type u) :=
  ((D.str x).1 : (O.alg : Type u) →+* ((D.A x).alg : Type u)).toAlgebra
abbrev total : Type u := ∀ x, ((D.A x).alg : Type u)
def classify (t : Tors B p O.alg) : Σ x : Tors B p k, LHom (D.A x).alg O.alg :=
  (D.universal O.alg (LHom.id _) t).exists.choose
theorem classify_spec (t : Tors B p O.alg) :
    (D.classify t).2.comp (D.str _) = LHom.id _ ∧
      B.map (D.classify t).2 (D.y (D.classify t).1 : B.G (D.A _).alg) = (t : B.G O.alg) :=
  (D.universal O.alg (LHom.id _) t).exists.choose_spec
def pull (t : Tors B p O.alg) : D.total →ₐ[(O.alg : Type u)] (O.alg : Type u) :=
  { ((D.classify t).2.1 : ((D.A _).alg : Type u) →+* (O.alg : Type u)).comp
      (Pi.evalRingHom (fun x => ((D.A x).alg : Type u)) (D.classify t).1) with
    commutes' := fun a => congrArg (fun f : LHom O.alg O.alg => f.1 a) (D.classify_spec t).1 }
variable (C : Type v) [Field C] [Algebra (O.alg : Type u) C]
def toFun : C ⊗[(O.alg : Type u)] D.total →ₐ[C] (Tors B p O.alg → C) :=
  Algebra.TensorProduct.lift (Algebra.ofId C _)
    (Pi.algHom _ _ fun t => (Algebra.ofId (O.alg : Type u) C).comp (D.pull t))
    (fun _ _ => Commute.all _ _)
end TorsionRep
structure FiniteTorsion (B : BX R₀) (p g : ℕ) (O : ResAlg k) (C : Type v) [Field C]
    [Algebra (O.alg : Type u) C] [IsFractionRing (O.alg : Type u) C] where

  rep : TorsionRep B p O
  free : Module.Free (O.alg : Type u) rep.total
  finite : Module.Finite (O.alg : Type u) rep.total
  generic : Function.Bijective (rep.toFun C)
  tate_surj : ∀ t : Tors B p O.alg, ∃ τ ∈ tateModule B p O.alg, τ 0 = (t : B.G O.alg)
  card : Nat.card (Tors B p O.alg) = p ^ (2 * g)
structure ChartData (B : BX R₀) {g : ℕ} (gb : Module.Basis (Fin g) R₀ B.gg) (p : ℕ)
    [Fact p.Prime] (k : LAlg R₀) (O : ResAlg k) (W : NilAlg k) (C : Type v) [Field C]
    [Algebra (O.alg : Type u) C] [IsFractionRing (O.alg : Type u) C] where

  chart : FormalChart B gb k
  smooth : LiftsFromResidue B W

  fin : FiniteTorsion B p g O C
example (hk : IsField (k : Type u)) : NilAlg k where
  alg := k
  res := LHom.id k
  res_surj := fun a => ⟨a, rfl⟩
  res_ker := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.1 hk]
    exact (RingHom.injective_iff_ker_eq_bot _).1 fun _ _ h => h
  nil := fun x hx => by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.1 hk, Ideal.mem_bot] at hx
    exact hx ▸ IsNilpotent.zero
end GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts


