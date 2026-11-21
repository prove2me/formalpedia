-- Prove2me | Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
-- name    : LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:39:45.016447+00:00
-- url     : https://prove2.me/theorems/7c28f2b3-b981-4c61-9e35-4c65791efb55
-- title:
--   Hybrid Couplers Phase Shifters
-- statement:
--   Definitions and structural lemmas for Hybrid Couplers Phase Shifters, from Matteo Nerini and Claude AI; maintained by LeanPool contributors's pinned Microwave network synthesis and power-of-two DFT implementation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Theorems.Thm_MiLAC_castAdd_ne_natAdd
public import Theorems.Thm_MiLAC_natAdd_ne_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_natAdd
public import Theorems.Thm_MiLAC_parallel_natAdd_castAdd
public import Theorems.Thm_MiLAC_parallel_natAdd_natAdd
attribute [local simp] MiLAC.castAdd_ne_natAdd
attribute [local simp] MiLAC.natAdd_ne_castAdd
attribute [local simp] MiLAC.parallel_castAdd_castAdd
attribute [local simp] MiLAC.parallel_castAdd_natAdd
attribute [local simp] MiLAC.parallel_natAdd_castAdd
attribute [local simp] MiLAC.parallel_natAdd_natAdd


set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace MiLAC.HybridCouplersPhaseShifters
@[expose] noncomputable def hybridCoupler : Network 2 :=
  (1 / Real.sqrt 2 : ℂ) • !![Complex.I, 1; 1, Complex.I]
inductive Implementable : {n : ℕ} → Network n → Prop where
  /-- An interconnection is implementable. -/
  | ic : Implementable interconnection
  /-- A phase shifter is implementable. -/
  | ps (φ : ℝ) : Implementable (phaseShifter φ)
  /-- A permutation network is implementable. -/
  | pn {n : ℕ} (σ : Equiv.Perm (Fin n)) : Implementable (permutationNetwork σ)
  /-- A hybrid coupler is implementable. -/
  | hc : Implementable hybridCoupler
  /-- The series of two implementable networks is implementable. -/
  | series {n : ℕ} {A B : Network n} :
      Implementable A → Implementable B → Implementable (series A B)
  /-- The parallel of two implementable networks is implementable. -/
  | parallel {n m : ℕ} {A : Network n} {B : Network m} :
      Implementable A → Implementable B → Implementable (parallel A B)
@[expose] def NetEquiv (X Y : Σ n : ℕ, Network n) : Prop :=
  ∃ e : Fin X.1 ≃ Fin Y.1, X.2 = Y.2.submatrix e e
lemma NetEquiv.trans {X Y Z : Σ n : ℕ, Network n}
    (hXY : NetEquiv X Y) (hYZ : NetEquiv Y Z) : NetEquiv X Z := by
  obtain ⟨e, he⟩ := hXY
  obtain ⟨f, hf⟩ := hYZ
  exact ⟨e.trans f, by rw [he, hf, Matrix.submatrix_submatrix]; rfl⟩
lemma NetEquiv.reindex {n k : ℕ} (e : Fin k ≃ Fin n) (M : Network k) :
    NetEquiv ⟨n, Matrix.reindex e e M⟩ ⟨k, M⟩ :=
  ⟨e.symm, rfl⟩
@[expose] def ImplementableOn {ι : Type*} (M : Matrix ι ι ℂ) : Prop :=
  ∃ (n : ℕ) (e : ι ≃ Fin n), Implementable (Matrix.reindex e e M)
lemma ImplementableOn.of_equiv {ι : Type*}
    {M : Matrix ι ι ℂ} {m : ℕ} (g : ι ≃ Fin m)
    (h : Implementable (Matrix.reindex g g M)) : ImplementableOn M :=
  ⟨m, g, h⟩
lemma ImplementableOn.reindex {ι κ : Type*}
    {M : Matrix ι ι ℂ} (h : ImplementableOn M) (f : ι ≃ κ) :
    ImplementableOn (Matrix.reindex f f M) := by
  obtain ⟨n, e, h⟩ := h
  refine ImplementableOn.of_equiv (f.symm.trans e) ?_
  convert h using 1
  ext i j
  simp [Matrix.reindex_apply]
lemma ImplementableOn.fromBlocks {ι κ : Type*}
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : ImplementableOn A) (hB : ImplementableOn B) :
    ImplementableOn (Matrix.fromBlocks A 0 0 B) := by
  obtain ⟨n, eA, hA⟩ := hA
  obtain ⟨m, eB, hB⟩ := hB
  refine ImplementableOn.of_equiv ((Equiv.sumCongr eA eB).trans finSumFinEquiv) ?_
  have hM : Matrix.reindex ((Equiv.sumCongr eA eB).trans finSumFinEquiv)
      ((Equiv.sumCongr eA eB).trans finSumFinEquiv) (Matrix.fromBlocks A 0 0 B) =
      parallel (Matrix.reindex eA eA A) (Matrix.reindex eB eB B) := by
    ext i j
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [Matrix.reindex_apply]
  rw [hM]
  exact Implementable.parallel hA hB
lemma implementableOn_of_isEmpty {ι : Type*} [IsEmpty ι]
    (M : Matrix ι ι ℂ) : ImplementableOn M := by
  refine ImplementableOn.of_equiv (m := 0) (Equiv.equivOfIsEmpty _ _) ?_
  convert Implementable.pn (Equiv.refl (Fin 0)) using 1
  ext i
  exact Fin.elim0 i
lemma ImplementableOn.blockDiagonal_one {m : Type*}
    (g : Fin 1 → Matrix m m ℂ) (h : ImplementableOn (g 0)) :
    ImplementableOn (Matrix.blockDiagonal g) := by
  have hM : Matrix.blockDiagonal g =
      Matrix.reindex (Equiv.prodUnique m (Fin 1)).symm (Equiv.prodUnique m (Fin 1)).symm
        (g 0) := by
    ext ⟨i, c⟩ ⟨j, d⟩
    simp [Matrix.reindex_apply, Matrix.blockDiagonal_apply, Fin.fin_one_eq_zero c,
      Fin.fin_one_eq_zero d]
  rw [hM]
  exact h.reindex _
lemma ImplementableOn.blockDiagonal {m : Type*} :
    ∀ (N : ℕ) (g : Fin N → Matrix m m ℂ), (∀ c, ImplementableOn (g c)) →
      ImplementableOn (Matrix.blockDiagonal g)
  | 0, g, _ => implementableOn_of_isEmpty _
  | N + 1, g, hg => by
      let f : m × Fin (N + 1) ≃ (m × Fin N) ⊕ (m × Fin 1) :=
        (Equiv.prodCongr (Equiv.refl m) finSumFinEquiv.symm).trans
          (Equiv.prodSumDistrib _ _ _)
      have hsplit : Matrix.reindex f f (Matrix.blockDiagonal g) =
          Matrix.fromBlocks (Matrix.blockDiagonal (fun c : Fin N => g (Fin.castAdd 1 c))) 0 0
            (Matrix.blockDiagonal (fun c : Fin 1 => g (Fin.natAdd N c))) := by
        ext (⟨i, c⟩ | ⟨i, c⟩) (⟨j, d⟩ | ⟨j, d⟩)
        all_goals simp [f, Matrix.reindex_apply, Matrix.blockDiagonal_apply]
      have h : ImplementableOn (Matrix.reindex f f (Matrix.blockDiagonal g)) := by
        rw [hsplit]
        exact ImplementableOn.fromBlocks
          (ImplementableOn.blockDiagonal N _ fun c => hg _)
          (ImplementableOn.blockDiagonal_one _ (hg _))
      simpa using h.reindex f.symm
@[expose] noncomputable def block (θ₁₁ θ₁₂ θ₂₁ : ℝ) : Network 2 :=
  (1 / Real.sqrt 2 : ℂ) • !![
    Complex.exp (θ₁₁ * Complex.I),
    Complex.exp (θ₁₂ * Complex.I);
    Complex.exp (θ₂₁ * Complex.I),
    Complex.exp ((Real.pi - θ₁₁ + θ₁₂ + θ₂₁) * Complex.I)]
@[expose] noncomputable def blockDiagonal {C S : ℕ}
    (θ₁₁ θ₁₂ θ₂₁ : Fin C → ℝ) (φ : Fin S → ℝ) : Network (2 * C + S) :=
  parallel
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.blockDiagonal fun c => block (θ₁₁ c) (θ₁₂ c) (θ₂₁ c)))
    (phaseDiagonal φ)
structure Layer (n : ℕ) where
  /-- The number of blocks of `D_ℓ`. -/
  C : ℕ
  /-- The number of phases of `D_ℓ`. -/
  S : ℕ
  /-- The parameters `θ₁₁` of the blocks of `D_ℓ`. -/
  θ₁₁ : Fin C → ℝ
  /-- The parameters `θ₁₂` of the blocks of `D_ℓ`. -/
  θ₁₂ : Fin C → ℝ
  /-- The parameters `θ₂₁` of the blocks of `D_ℓ`. -/
  θ₂₁ : Fin C → ℝ
  /-- The phases of `D_ℓ`. -/
  φ : Fin S → ℝ
  /-- `D_ℓ` has `n` ports. -/
  size : 2 * C + S = n
  /-- The permutation of `P_ℓ`. -/
  σ : Equiv.Perm (Fin n)
@[expose] noncomputable def layered {n : ℕ} (σ₀ : Equiv.Perm (Fin n)) : List (Layer n) → Network n
  | [] => permutationNetwork σ₀
  | layer :: layers =>
      permutationNetwork layer.σ *
        Matrix.reindex (finCongr layer.size) (finCongr layer.size)
          (blockDiagonal layer.θ₁₁ layer.θ₁₂ layer.θ₂₁ layer.φ) *
        layered σ₀ layers
@[expose] def IsLayered {n : ℕ} (S : Network n) : Prop :=
  ∃ σ₀ : Equiv.Perm (Fin n), ∃ layers : List (Layer n), S = layered σ₀ layers
@[expose] noncomputable def dft (N : ℕ) : Network N :=
  fun i k => (1 / Real.sqrt N : ℂ) *
    Complex.exp (-2 * Real.pi * Complex.I * (i : ℕ) * (k : ℕ) / N)
@[expose] noncomputable def butterfly (L : ℕ) (i : Fin (2 ^ L)) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b => (1 / Real.sqrt 2 : ℂ) * ((-1) ^ ((a : ℕ) * (b : ℕ)) *
    Complex.exp (-2 * Real.pi * Complex.I * (i : ℕ) * (b : ℕ) / 2 ^ (L + 1)))
end MiLAC.HybridCouplersPhaseShifters


