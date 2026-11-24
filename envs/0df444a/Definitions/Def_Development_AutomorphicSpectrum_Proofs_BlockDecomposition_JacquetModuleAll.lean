-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:51.197747+00:00
-- url     : https://prove2.me/theorems/c07a050d-6460-440d-9ef4-baceaa81cd9c
-- title:
--   Jacquet Module All
-- statement:
--   Definitions and structural lemmas for Jacquet Module All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin
noncomputable section
namespace GlobalTheory.CompanionTheory.TyFinJacquet
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
def leviHom (b : ι → Fin s) : parab K b →* (∀ c, GL {i // b i = c} K) where
  toFun p c := levi K b c p
  map_one' := by
    funext c
    apply Units.ext
    ext ⟨i, hi⟩ ⟨j, hj⟩
    show ((1 : GL ι K) : Matrix ι ι K) i j = (1 : Matrix {i // b i = c} {i // b i = c} K) ⟨i, hi⟩ ⟨j, hj⟩
    simp [Matrix.one_apply]
  map_mul' p q := by
    funext c
    apply Units.ext
    exact blk_mul b c p.2.1 q.2.1
theorem mem_unip_iff (b : ι → Fin s) (p : parab K b) : p.1 ∈ unip K b ↔ leviHom b p = 1 := by
  constructor
  · intro h
    funext c
    apply Units.ext
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have h1 := h.2 i j (hi.trans hj.symm)
    show (p.1 : Matrix ι ι K) i j = (1 : Matrix {i // b i = c} {i // b i = c} K) ⟨i, hi⟩ ⟨j, hj⟩
    rw [h1, Matrix.one_apply]
    simp
  · intro h
    refine ⟨p.2, fun i j hij => ?_⟩
    have h1 := congrArg (fun f : (∀ c, GL {i // b i = c} K) =>
      ((f (b i) : GL {k // b k = b i} K) : Matrix {k // b k = b i} {k // b k = b i} K) ⟨i, rfl⟩ ⟨j, hij.symm⟩) h
    have h2 : (p.1 : Matrix ι ι K) i j =
        (1 : Matrix {k // b k = b i} {k // b k = b i} K) ⟨i, rfl⟩ ⟨j, hij.symm⟩ := h1
    rw [h2, Matrix.one_apply]
    simp
theorem blockDiagonal_entry (b : ι → Fin s) (M : ∀ c, Matrix {i // b i = c} {i // b i = c} K) (k k' : Fin s)
    (x : {i // b i = k}) (y : {i // b i = k'}) :
    Matrix.blockDiagonal' M ⟨k, x⟩ ⟨k', y⟩ = if h : k' = k then M k x ⟨y.1, y.2.trans h⟩ else 0 := by
  by_cases h : k' = k
  · subst h
    simp
  · have h' : k ≠ k' := fun e => h e.symm
    simp [Matrix.blockDiagonal'_apply, h, h']
def blockHom (b : ι → Fin s) : (∀ c, Matrix {i // b i = c} {i // b i = c} K) →* Matrix ι ι K where
  toFun M := (Matrix.blockDiagonal' M).submatrix (Equiv.sigmaFiberEquiv b).symm (Equiv.sigmaFiberEquiv b).symm
  map_one' := by
    rw [Matrix.blockDiagonal'_one]
    simp
  map_mul' M N := by
    show (Matrix.blockDiagonal' (fun k => M k * N k)).submatrix _ _ = _
    rw [Matrix.blockDiagonal'_mul, Matrix.submatrix_mul_equiv]
theorem blockHom_apply (b : ι → Fin s) (M : ∀ c, Matrix {i // b i = c} {i // b i = c} K) (i j : ι) :
    blockHom b M i j = if h : b j = b i then M (b i) ⟨i, rfl⟩ ⟨j, h⟩ else 0 :=
  blockDiagonal_entry b M (b i) (b j) ⟨i, rfl⟩ ⟨j, rfl⟩
def dGL (b : ι → Fin s) : (∀ c, GL {i // b i = c} K) →* GL ι K :=
  (Units.map (blockHom b)).comp
    (MulEquiv.piUnits (M := fun c => Matrix {i // b i = c} {i // b i = c} K)).symm.toMonoidHom
theorem dGL_val (b : ι → Fin s) (g : ∀ c, GL {i // b i = c} K) :
    ((dGL b g : GL ι K) : Matrix ι ι K) =
      blockHom b (fun c => ((g c : GL {i // b i = c} K) : Matrix {i // b i = c} {i // b i = c} K)) := rfl
theorem isBlockUT_dGL (b : ι → Fin s) (g : ∀ c, GL {i // b i = c} K) :
    IsBlockUT K b ((dGL b g : GL ι K) : Matrix ι ι K) := by
  intro i j h
  rw [dGL_val, blockHom_apply, dif_neg (ne_of_lt h)]
theorem dGL_mem (b : ι → Fin s) (g : ∀ c, GL {i // b i = c} K) : dGL b g ∈ parab K b :=
  ⟨isBlockUT_dGL b g, by rw [← map_inv]; exact isBlockUT_dGL b g⁻¹⟩
theorem unip_conj (b : ι → Fin s) (g : ∀ c, GL {i // b i = c} K) {u : GL ι K} (hu : u ∈ unip K b) :
    (dGL b g)⁻¹ * u * dGL b g ∈ unip K b := by
  have hd := dGL_mem b g
  have hl := (mem_unip_iff b ⟨u, hu.1⟩).1 hu
  have := (mem_unip_iff b ((⟨dGL b g, hd⟩ : parab K b)⁻¹ * ⟨u, hu.1⟩ * ⟨dGL b g, hd⟩)).2
    (by rw [map_mul, map_mul, hl, map_inv, mul_one, inv_mul_cancel])
  exact this
def fixSub (τ : FDRep ℂ (GL ι K)) (b : ι → Fin s) : Submodule ℂ τ where
  carrier := {v | ∀ u ∈ unip K b, τ.ρ u v = v}
  add_mem' := by
    intro x y hx hy u hu
    rw [map_add, hx u hu, hy u hu]
  zero_mem' := by
    intro u _
    exact map_zero _
  smul_mem' := by
    intro a x hx u hu
    rw [map_smul, hx u hu]
theorem fixSub_stable (τ : FDRep ℂ (GL ι K)) (b : ι → Fin s) (g : ∀ c, GL {i // b i = c} K) :
    ∀ v ∈ fixSub τ b, τ.ρ (dGL b g) v ∈ fixSub τ b := by
  intro v hv u hu
  have h := hv _ (unip_conj b g hu)
  have e : u * dGL b g = dGL b g * ((dGL b g)⁻¹ * u * dGL b g) := by group
  calc τ.ρ u (τ.ρ (dGL b g) v) = τ.ρ (u * dGL b g) v := by rw [map_mul]; rfl
    _ = τ.ρ (dGL b g * ((dGL b g)⁻¹ * u * dGL b g)) v := by rw [e]
    _ = τ.ρ (dGL b g) (τ.ρ ((dGL b g)⁻¹ * u * dGL b g) v) := by rw [map_mul]; rfl
    _ = τ.ρ (dGL b g) v := by rw [h]
def wRep (τ : FDRep ℂ (GL ι K)) (b : ι → Fin s) :
    Representation ℂ (∀ c, GL {i // b i = c} K) (fixSub τ b) where
  toFun g := (τ.ρ (dGL b g)).restrict (fixSub_stable τ b g)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp
def HasFixed (τ : FDRep ℂ (GL ι K)) (s : ℕ) : Prop :=
  ∃ b : ι → Fin s, Function.Surjective b ∧ ∃ v : τ, v ≠ 0 ∧ ∀ u ∈ unip K b, τ.ρ u v = v
section Refine
variable (b : ι → Fin s) (c : Fin s) {t : ℕ} (b₁ : {i // b i = c} → Fin t) (ht : 1 ≤ t)
def refine (i : ι) : Fin (s + t - 1) :=
  if h : b i = c then ⟨c + b₁ ⟨i, h⟩, by have := c.2; have := (b₁ ⟨i, h⟩).2; omega⟩
  else if h2 : (b i : ℕ) < c then ⟨b i, by have := c.2; omega⟩
  else ⟨b i + t - 1, by have := (b i).2; omega⟩
end Refine
section Cusp
variable {τ : FDRep ℂ (GL ι K)} {b : ι → Fin s} {lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)}
  {Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ}
def killSub (Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ) (c : Fin s) : Submodule ℂ (lam c) where
  carrier := {x | ∀ f : ∀ c, (lam c : Type), Φ (PiTensorProduct.tprod ℂ (Function.update f c x)) = 0}
  add_mem' := by
    intro x y hx hy f
    rw [MultilinearMap.map_update_add, map_add, hx f, hy f, add_zero]
  zero_mem' := by
    intro f
    rw [MultilinearMap.map_update_zero, map_zero]
  smul_mem' := by
    intro a x hx f
    rw [MultilinearMap.map_update_smul, map_smul, hx f, smul_zero]
end Cusp
end GlobalTheory.CompanionTheory.TyFinJacquet


