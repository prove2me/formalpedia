-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:42.809733+00:00
-- url     : https://prove2.me/theorems/7b2e5284-4cc3-4d70-ab3e-6f8edb0a732c
-- title:
--   Exists Is Unit Eval Of Map Residue Ne Zero
-- statement:
--   Definitions and structural lemmas for Exists Is Unit Eval Of Map Residue Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
namespace GlobalTheory
section PolynomialFunction
variable (K : Type*) [CommSemiring K] {M : Type*} [AddCommMonoid M] [Module K M]
def IsPolynomialFunction (P : M → K) : Prop :=
  P ∈ Algebra.adjoin K (Set.range fun φ : Module.Dual K M => (φ : M → K))
variable {K}
theorem IsPolynomialFunction.linear (φ : Module.Dual K M) : IsPolynomialFunction K φ :=
  Algebra.subset_adjoin ⟨φ, rfl⟩
theorem IsPolynomialFunction.const (c : K) : IsPolynomialFunction K (fun _ : M => c) :=
  Subalgebra.algebraMap_mem _ c
theorem IsPolynomialFunction.add {P Q : M → K} (hP : IsPolynomialFunction K P)
    (hQ : IsPolynomialFunction K Q) : IsPolynomialFunction K (fun x => P x + Q x) :=
  Subalgebra.add_mem _ hP hQ
theorem IsPolynomialFunction.mul {P Q : M → K} (hP : IsPolynomialFunction K P)
    (hQ : IsPolynomialFunction K Q) : IsPolynomialFunction K (fun x => P x * Q x) :=
  Subalgebra.mul_mem _ hP hQ
theorem IsPolynomialFunction.eval {σ : Type*} (L : σ → Module.Dual K M) (p : MvPolynomial σ K) :
    IsPolynomialFunction K (fun x => MvPolynomial.eval (fun i => L i x) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using IsPolynomialFunction.const c
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (IsPolynomialFunction.linear (L i))
end PolynomialFunction
section Frames
variable {ι : Type*} {K : Type*} {V : ι → Type*}
section Semiring
variable [CommSemiring K] [∀ s, AddCommMonoid (V s)] [∀ s, Module K (V s)]
  {l m n : ι → Type*} [∀ s, Fintype (l s)] [∀ s, Fintype (m s)]
def frameMul (x : ∀ s, m s → V s) (b : ∀ s, Matrix (m s) (n s) K) : ∀ s, n s → V s :=
  fun s j => ∑ i, b s i j • x s i
abbrev EntryIndex (m n : ι → Type*) : Type _ := Σ s, m s × n s
def entries {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) : EntryIndex m n → α :=
  fun k => b k.1 k.2.1 k.2.2
def ofEntries {α : Type*} (ξ : EntryIndex m n → α) : ∀ s, Matrix (m s) (n s) α :=
  fun s => Matrix.of fun i j => ξ ⟨s, i, j⟩
omit [∀ s, Fintype (m s)] in
@[simp] theorem entries_apply {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) (s : ι) (i : m s)
    (j : n s) : entries b ⟨s, i, j⟩ = b s i j := rfl
omit [∀ s, Fintype (m s)] in
@[simp] theorem ofEntries_apply {α : Type*} (ξ : EntryIndex m n → α) (s : ι) (i : m s)
    (j : n s) : ofEntries ξ s i j = ξ ⟨s, i, j⟩ := rfl
omit [∀ s, Fintype (m s)] in
@[simp] theorem entries_ofEntries {α : Type*} (ξ : EntryIndex m n → α) :
    entries (ofEntries ξ) = ξ := rfl
omit [∀ s, Fintype (m s)] in
@[simp] theorem ofEntries_entries {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) :
    ofEntries (entries b) = b := rfl
def frameMulLinear (n : ι → Type*) (w : ∀ s, m s → V s) :
    (EntryIndex m n → K) →ₗ[K] (∀ s, n s → V s) where
  toFun ξ := frameMul w (ofEntries ξ)
  map_add' ξ η := by
    funext s j
    simp [frameMul, add_smul, Finset.sum_add_distrib]
  map_smul' c ξ := by
    funext s j
    simp [frameMul, Finset.smul_sum, smul_smul]
end Semiring
variable [Fintype ι] {r : ι → ℕ} [Field K] [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)]
  {W : Type*} [AddCommGroup W] [Module K W]
variable (K) in

def HasTriangularWeight (a : ∀ s, Fin (r s) → ℕ) (P : (∀ s, Fin (r s) → V s) → W) : Prop :=
  ∀ (x : ∀ s, Fin (r s) → V s) (b : ∀ s, Matrix (Fin (r s)) (Fin (r s)) K),
    (∀ s, (b s).IsUpperTriangular) → (∀ s i, b s i i ≠ 0) →
      P (frameMul x b) = (∏ s, ∏ i, b s i i ^ a s i) • P x
end Frames
section Hadamard
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜] {V : ι → Type*}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
section Inner
variable [∀ s, NormedAddCommGroup (V s)] [∀ s, InnerProductSpace 𝕜 (V s)]
  [∀ s, FiniteDimensional 𝕜 (V s)]
end Inner
end Hadamard
section PolynomialWeight
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {K : Type*} [Field K]
def HasTriangularWeightPoly (a : ∀ s, Fin (r s) → ℕ)
    (p : MvPolynomial (EntryIndex (fun s => Fin (r s)) (fun s => Fin (r s))) K) : Prop :=
  ∀ x b : ∀ s, Matrix (Fin (r s)) (Fin (r s)) K,
    (∀ s, (b s).IsUpperTriangular) → (∀ s i, b s i i ≠ 0) →
      MvPolynomial.eval (entries fun s => x s * b s) p =
        (∏ s, ∏ i, b s i i ^ a s i) * MvPolynomial.eval (entries x) p
noncomputable def detProdPoly (R : Type*) [CommRing R] (n : ι → Type*) [∀ s, Fintype (n s)]
    [∀ s, DecidableEq (n s)] : MvPolynomial (EntryIndex n n) R :=
  ∏ s, (ofEntries MvPolynomial.X s).det
end PolynomialWeight
section HadamardPolynomial
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜]
end HadamardPolynomial
section Gauss
open MvPolynomial IsLocalRing
variable {K Γ O : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ}
  [CommRing O] [Algebra O K]
variable [IsLocalRing O] [Infinite (ResidueField O)]
variable {ι : Type*} [Fintype ι]
section Matrices
variable {n : ι → Type*} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]
end Matrices
section Lattices
variable {V : ι → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ s, Module O (V s)]
  [∀ s, IsScalarTower O K (V s)] {Λ : ∀ s, Submodule O (V s)}
variable {r : ι → ℕ}
end Lattices
end Gauss
end GlobalTheory


