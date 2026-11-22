-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:28:05.893969+00:00
-- url     : https://prove2.me/theorems/a623b331-e5af-4abc-b1e8-107e7c15e149
-- title:
--   Is Unit Det Of Const
-- statement:
--   Definitions and structural lemmas for Is Unit Det Of Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.NG
namespace BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
def liftHom : (X' → O) →+* (X' → FractionRing O) :=
  RingHom.pi fun x' => (algebraMap O (FractionRing O)).comp (Pi.evalRingHom (fun _ : X' => O) x')
def Fr (T' : Subalgebra O (X' → O)) : Subring (X' → FractionRing O) :=
  T'.toSubring.map liftHom
def goodS (T' : Subalgebra O (X' → O)) : Subring (PowerSeries (X' → FractionRing O)) where
  carrier := {φ | ∀ n, PowerSeries.coeff n φ ∈ Fr T'}
  mul_mem' {a b} ha hb n := by
    rw [PowerSeries.coeff_mul]
    exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (ha _) (hb _)
  one_mem' n := by
    rw [PowerSeries.coeff_one]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  add_mem' {a b} ha hb n := by
    rw [map_add]
    exact Subring.add_mem _ (ha n) (hb n)
  zero_mem' n := by
    rw [map_zero]
    exact Subring.zero_mem _
  neg_mem' {a} ha n := by
    rw [map_neg]
    exact Subring.neg_mem _ (ha n)
variable {d : Type} [Fintype d] [DecidableEq d]
def coefMat (n : ℕ) (a : Matrix d d (PowerSeries (X' → FractionRing O))) :
    X' → Matrix d d (FractionRing O) :=
  fun x' i j => PowerSeries.coeff n (a i j) x'
lemma coefMat_mul (n : ℕ) (a b : Matrix d d (PowerSeries (X' → FractionRing O))) :
    coefMat n (a * b) = ∑ p ∈ antidiagonal n, coefMat p.1 a * coefMat p.2 b := by
  ext x' i j
  simp only [coefMat, Matrix.mul_apply, map_sum, PowerSeries.coeff_mul, Finset.sum_apply, Matrix.sum_apply,
    Pi.mul_apply]
  exact Finset.sum_comm
lemma coefMat_add (n : ℕ) (a b : Matrix d d (PowerSeries (X' → FractionRing O))) :
    coefMat n (a + b) = coefMat n a + coefMat n b := by
  ext x' i j
  simp [coefMat]
lemma coefMat_neg (n : ℕ) (a : Matrix d d (PowerSeries (X' → FractionRing O))) :
    coefMat n (-a) = -coefMat n a := by
  ext x' i j
  simp [coefMat]
lemma coefMat_zero (n : ℕ) :
    coefMat n (0 : Matrix d d (PowerSeries (X' → FractionRing O))) = 0 := by
  ext x' i j
  simp [coefMat]
lemma coefMat_one (n : ℕ) :
    coefMat n (1 : Matrix d d (PowerSeries (X' → FractionRing O))) = if n = 0 then 1 else 0 := by
  ext x' i j
  by_cases hn : n = 0 <;> by_cases hij : i = j <;>
    simp [coefMat, Matrix.one_apply, hn, hij, PowerSeries.coeff_one]
def goodM (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) :
    Subring (Matrix d d (PowerSeries (X' → FractionRing O))) where
  carrier := {a | ∀ n, coefMat n a ∈ R'}
  mul_mem' {a b} ha hb n := by
    rw [coefMat_mul]
    exact Subalgebra.sum_mem _ fun p _ => Subalgebra.mul_mem _ (ha _) (hb _)
  one_mem' n := by
    rw [coefMat_one]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  add_mem' {a b} ha hb n := by
    rw [coefMat_add]
    exact Subalgebra.add_mem _ (ha n) (hb n)
  zero_mem' n := by
    rw [coefMat_zero]
    exact Subalgebra.zero_mem _
  neg_mem' {a} ha n := by
    rw [coefMat_neg]
    exact Subalgebra.neg_mem _ (ha n)
section Trunc
variable {K : Type*} [CommRing K]
def wt {m : ℕ} (e : Fin m →₀ ℕ) : ℕ := ∑ j, (j.1 + 1) * e j
def bnd (m : ℕ) : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => m)
def psi (m : ℕ) : MvPolynomial (Fin m) K →+* PowerSeries K :=
  MvPolynomial.eval₂Hom (PowerSeries.C) (fun j : Fin m => PowerSeries.X ^ (j.1 + 1))
end Trunc
section Good
variable {d : Type} [Fintype d] [DecidableEq d]
def HypDet (T' : Subalgebra O (X' → O)) (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) :
    Prop :=
  ∀ (m : ℕ) (r : Fin m → R') (s : Fin m →₀ ℕ), ∃ f ∈ T', ∀ x',
    algebraMap O (FractionRing O) (f x') =
      MvPolynomial.coeff s (Matrix.det (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) (FractionRing O)) •
        ((r i : X' → Matrix d d (FractionRing O)) x').map MvPolynomial.C))
end Good
section Inv
variable {d : Type} [Fintype d] [DecidableEq d]
end Inv
section Schur
variable {d : Type} [Fintype d] [DecidableEq d]
def optEquiv (g d : Type) : Option g × d ≃ d ⊕ (g × d) where
  toFun x := match x with
    | (none, i) => Sum.inl i
    | (some p, i) => Sum.inr (p, i)
  invFun y := match y with
    | Sum.inl i => (none, i)
    | Sum.inr (p, i) => (some p, i)
  left_inv := by rintro ⟨_ | p, i⟩ <;> rfl
  right_inv := by rintro (i | ⟨p, i⟩) <;> rfl
def SchurP (T' : Subalgebra O (X' → O)) (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (g : Type) [Fintype g] : Prop :=
  ∀ [DecidableEq g] (Φ : Matrix (g × d) (g × d) (PowerSeries (X' → FractionRing O))),
    (∀ p q, (Matrix.of fun i j => Φ (p, i) (q, j)) ∈ goodM R') →
    (PowerSeries.constantCoeff).mapMatrix Φ = 1 → Φ.det ∈ goodS T'
end Schur
section Final
variable {d : Type} [Fintype d] [DecidableEq d]
def phiMat (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) {g : Type} [Fintype g]
    [DecidableEq g] (Θ : Matrix g g R') : Matrix (g × d) (g × d) (PowerSeries (X' → FractionRing O)) :=
  1 - (PowerSeries.X : PowerSeries (X' → FractionRing O)) •
    Matrix.of fun P Q => PowerSeries.C (fun x' => (Θ P.1 Q.1 : X' → Matrix d d (FractionRing O)) x' P.2 Q.2)
end Final
end BlockDetAlt
end Formalism.NG


