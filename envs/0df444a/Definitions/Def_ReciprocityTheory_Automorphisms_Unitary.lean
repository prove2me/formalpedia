-- Prove2me | Definitions.Def_ReciprocityTheory_Automorphisms_Unitary
-- name    : ReciprocityTheory_Automorphisms_Unitary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:32.731799+00:00
-- url     : https://prove2.me/theorems/8f941651-3fd6-40c7-912c-90f107c1a37c
-- title:
--   Unitary
-- statement:
--   Definitions and structural lemmas for Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/Unitary.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Aut
open NumberField IsDedekindDomain TensorProduct
section General
variable {R : Type*} [CommRing R] {n : ℕ}
def conjT (σ : R →+* R) (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := (g.map σ).transpose
theorem conjT_mul (σ : R →+* R) (g h : Matrix (Fin n) (Fin n) R) :
    conjT σ (g * h) = conjT σ h * conjT σ g := by
  unfold conjT
  rw [Matrix.map_mul, Matrix.transpose_mul]
theorem conjT_one (σ : R →+* R) : conjT σ (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold conjT
  simp
theorem conjT_conjT (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (g : Matrix (Fin n) (Fin n) R) :
    conjT σ (conjT σ g) = g := by
  ext i j
  simp [conjT, hσ]
def UGroup (n : ℕ) (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) : Subgroup (GL (Fin n) R) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) R) * conjT σ g = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    rw [conjT_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (b : Matrix (Fin n) (Fin n) R), hb,
      Matrix.one_mul, ha]
  one_mem' := by
    simp [conjT_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = conjT σ a :=
      Units.inv_eq_of_mul_eq_one_right ha
    rw [h1, conjT_conjT σ hσ]
    exact mul_eq_one_comm.mp ha
end General
variable (L : Type*) [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L
abbrev AFplus : Type _ := FiniteAdeleRing (𝓞 L⁺) L⁺
abbrev AL : Type _ := L ⊗[L⁺] AFplus L
noncomputable def conjAL : AL L →+* AL L :=
  (Algebra.TensorProduct.map (IsCMField.complexConj L).toAlgHom (AlgHom.id L⁺ (AFplus L))).toRingHom
theorem conjAL_conjAL (x : AL L) : conjAL L (conjAL L x) = x := by
  have hc : ∀ y : L, IsCMField.complexConj L (IsCMField.complexConj L y) = y := by
    intro y
    have h := pow_orderOf_eq_one (IsCMField.complexConj L)
    rw [IsCMField.orderOf_complexConj, pow_two] at h
    simpa [AlgEquiv.mul_apply] using DFunLike.congr_fun h y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [conjAL, hc]
  | add x y hx hy => simp only [map_add, hx, hy]
theorem complexConj_invol (x : L) :
    (IsCMField.complexConj L : L →+* L) ((IsCMField.complexConj L : L →+* L) x) = x := by
  have hc : ∀ y : L, IsCMField.complexConj L (IsCMField.complexConj L y) = y := by
    intro y
    have h := pow_orderOf_eq_one (IsCMField.complexConj L)
    rw [IsCMField.orderOf_complexConj, pow_two] at h
    simpa [AlgEquiv.mul_apply] using DFunLike.congr_fun h y
  simpa using hc x
structure SplitPlace where
  v : HeightOneSpectrum (𝓞 L⁺)
  i : L →ₐ[L⁺] v.adicCompletion L⁺
noncomputable def evalAt (v : HeightOneSpectrum (𝓞 L⁺)) : AFplus L →ₐ[L⁺] v.adicCompletion L⁺ :=
  { RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 L⁺) => v.adicCompletion L⁺) v with
    commutes' := fun _ => rfl }
noncomputable def compAt (v : HeightOneSpectrum (𝓞 L⁺)) : AL L →+* L ⊗[L⁺] v.adicCompletion L⁺ :=
  (Algebra.TensorProduct.map (AlgHom.id L⁺ L) (evalAt L v)).toRingHom
variable {L} in

noncomputable def SplitPlace.proj (s : SplitPlace L) : AL L →+* s.v.adicCompletion L⁺ :=
  (Algebra.TensorProduct.lift s.i (evalAt L s.v) (fun _ _ => Commute.all _ _)).toRingHom
noncomputable def ALint : Subring (AL L) :=
  Subring.closure ({x | ∃ y : 𝓞 L, x = (y : L) ⊗ₜ[L⁺] (1 : AFplus L)} ∪
    {x | ∃ a : AFplus L, (∀ v, a v ∈ v.adicCompletionIntegers L⁺) ∧ x = (1 : L) ⊗ₜ[L⁺] a})
noncomputable def GA (n : ℕ) : Subgroup (GL (Fin n) (AL L)) := UGroup n (conjAL L) (conjAL_conjAL L)
noncomputable def GQ0 (n : ℕ) : Subgroup (GL (Fin n) L) :=
  UGroup n (IsCMField.complexConj L : L →+* L) (complexConj_invol L)
noncomputable def GQ (n : ℕ) : Subgroup (GA L n) :=
  ((GQ0 L n).map (Matrix.GeneralLinearGroup.map
    (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L))).subgroupOf (GA L n)
theorem conjAL_mem_ALint {x : AL L} (hx : x ∈ ALint L) : conjAL L x ∈ ALint L := by
  have key : ALint L ≤ (ALint L).comap (conjAL L) := by
    refine Subring.closure_le.mpr ?_
    rintro x (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · refine Subring.subset_closure (Or.inl
        ⟨RingOfIntegers.mapRingEquiv (IsCMField.complexConj L).toRingEquiv y, ?_⟩)
      simp [conjAL] <;> rfl
    · refine Subring.subset_closure (Or.inr ⟨a, ha, ?_⟩)
      simp [conjAL]
  exact key hx
noncomputable def Umax (n : ℕ) : Subgroup (GA L n) where
  carrier := {g | ∀ i j, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L}
  mul_mem' := by
    intro a b ha hb i j
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (ha i k) (hb k j)
  one_mem' := by
    intro i j
    simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  inv_mem' := by
    intro a ha i j
    have hm := a.2
    simp only [GA, UGroup, Subgroup.mem_mk] at hm
    have h1 : ((a.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) a.1 :=
      Units.inv_eq_of_mul_eq_one_right hm
    simp only [Set.mem_ofPred_eq] at ha
    simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]
    exact conjAL_mem_ALint L (ha j i)
variable {L} in

noncomputable def SplitPlace.loc (s : SplitPlace L) (n : ℕ) :
    GA L n →* GL (Fin n) (s.v.adicCompletion L⁺) :=
  (Matrix.GeneralLinearGroup.map s.proj).comp (GA L n).subtype
variable {L} in

def TrivOutside {n : ℕ} (T : Set (HeightOneSpectrum (𝓞 L⁺))) (x : GA L n) : Prop :=
  ∀ v, v ∉ T → (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1
variable {L} in

noncomputable def Level {n : ℕ} {ι : Type*} (s : ι → SplitPlace L)
    (H : ∀ a, Subgroup (GL (Fin n) ((s a).v.adicCompletion L⁺))) : Subgroup (GA L n) :=
  Umax L n ⊓ ⨅ a, (H a).comap ((s a).loc n)
def IsNeat {n : ℕ} (U : Subgroup (GA L n)) : Prop :=
  ∀ g : GA L n, ∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ U → γ = 1
end ReciprocityTheory.Aut


