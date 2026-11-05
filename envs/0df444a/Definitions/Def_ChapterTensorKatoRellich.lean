-- Prove2me | Definitions.Def_ChapterTensorKatoRellich
-- name    : ChapterTensorKatoRellich
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-04T14:57:58.170137+00:00
-- url     : https://prove2.me/theorems/a4f9fa20-aef3-45d7-9420-8012d41f7e0e
-- title:
--   Chapter TensorKatoRellich
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterTensorKatoRellich.lean`): generated def bundle for ChapterTensorKatoRellich. See BookProof/ChapterTensorKatoRellich.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterTensorKatoRellich.lean

import Definitions.Def_ChapterTensorSumEsa
import Definitions.Def_ChapterKatoRellichRelative
import Theorems.Thm_BookProof_KatoRellich_essentiallySelfAdjointOn_add_relBounded
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Mathlib


/-!
# Kato–Rellich for product couplings on a tensor sum with a finite-dimensional factor

`BookProof.ChapterTensorSumEsa` proves that a tensor **sum** `A ⊗ 1 + 1 ⊗ B` of two essentially
self-adjoint operators is essentially self-adjoint on `D_A ⊗ D_B`.  A tensor sum is not an
interaction.  This module adds a genuine coupling between the two factors,

`H = A ⊗ 1 + 1 ⊗ B + Σᵢ Vᵢ ⊗ Yᵢ`,

when the second factor is **finite-dimensional** and every `Vᵢ` is `A`-bounded with relative
bound `0` (`‖Vᵢ u‖ ≤ ε‖A u‖ + C_ε‖u‖` for every `ε > 0`).  The `Yᵢ` are arbitrary symmetric
operators on the finite-dimensional factor.

## What is proved

* `norm_sq_sum_tmul_orthonormal`, `norm_sum_tmul_le` — norm identities for sums of elementary
  tensors against an orthonormal family;
* `pairLiftOp`, `pairLiftOp_apply` — any linear map `D_A ⊗ D_B → H ⊗ K`, read as an operator
  in the completed tensor product on the domain `cpairDom` of the tensor sum
  (`cpairOp = pairLiftOp (sumPoly …)`, `cpairOp_eq_pairLiftOp`);
* `mapPoly_symm`, `symmetricOn_pairLiftOp`, `symmetricOn_coupling` — the product coupling
  `Σᵢ Vᵢ ⊗ Yᵢ` is symmetric when every `Vᵢ` and `Yᵢ` is;
* `coupling_relBound` — **the relative bound**: the coupling is bounded relative to the tensor
  sum with a relative bound `< 1`;
* **`essentiallySelfAdjointOn_tensorSum_add_coupling`** — hence, by Kato–Rellich
  (`KatoRellich.essentiallySelfAdjointOn_add_relBounded`), the coupled operator is essentially
  self-adjoint on `cpairDom` whenever the tensor sum is.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.TensorKatoRellich

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore BookProof.TensorSumEsa

noncomputable section

/-! ## 1. Norms of sums of elementary tensors -/

theorem norm_sq_sum_tmul_orthonormal {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] {ι : Type*}
    [Fintype ι] {b : ι → F} (hb : Orthonormal ℂ b) (v : ι → E) :
    ‖∑ i, v i ⊗ₜ[ℂ] b i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  classical
  rw [orthonormal_iff_ite] at hb
  have h : (inner ℂ (∑ i, v i ⊗ₜ[ℂ] b i) (∑ i, v i ⊗ₜ[ℂ] b i) : ℂ)
      = ∑ i, (inner ℂ (v i) (v i) : ℂ) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum, Finset.sum_eq_single i]
    · rw [TensorProduct.inner_tmul, hb, if_pos rfl, mul_one]
    · intro j _ hj
      rw [TensorProduct.inner_tmul, hb, if_neg (Ne.symm hj), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [@norm_sq_eq_re_inner ℂ, h, map_sum]
  exact Finset.sum_congr rfl fun i _ => (@norm_sq_eq_re_inner ℂ _ _ _ _ (v i)).symm

/-- Each coefficient of an orthonormal expansion is bounded by the whole vector. -/
theorem norm_le_norm_sum_tmul_orthonormal {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] {ι : Type*}
    [Fintype ι] {b : ι → F} (hb : Orthonormal ℂ b) (v : ι → E) (j : ι) :
    ‖v j‖ ≤ ‖∑ i, v i ⊗ₜ[ℂ] b i‖ := by
  have h := norm_sq_sum_tmul_orthonormal hb v
  have hj : ‖v j‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ j)
  rw [← h] at hj
  exact le_of_sq_le_sq (by simpa using hj) (norm_nonneg _) |>.trans le_rfl

theorem norm_sum_tmul_le {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {ι : Type*} [Fintype ι]
    (v : ι → E) (w : ι → F) :
    ‖∑ i, v i ⊗ₜ[ℂ] w i‖ ≤ ∑ i, ‖v i‖ * ‖w i‖ := by
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp [TensorProduct.norm_tmul]

/-! ## 2. Operators on the domain of the tensor sum -/

section Lift

variable (Hs Ks : IPSpace) (DA : Submodule ℂ Hs.carrier) (DB : Submodule ℂ Ks.carrier)

/-- A linear map `D_A ⊗ D_B → H ⊗ K`, read as an operator on the subspace `pairDom` of `H ⊗ K`. -/
def pairLiftDom (L : (DA ⊗[ℂ] DB) →ₗ[ℂ] (Hs.carrier ⊗[ℂ] Ks.carrier)) :
    pairDom Hs Ks DA DB →ₗ[ℂ] (Hs.carrier ⊗[ℂ] Ks.carrier) :=
  L ∘ₗ
    (LinearEquiv.ofInjective (inclPair Hs Ks DA DB).toLinearMap
      (fun _ _ h => (inclPair Hs Ks DA DB).injective h)).symm.toLinearMap

theorem pairLiftDom_apply (L : (DA ⊗[ℂ] DB) →ₗ[ℂ] (Hs.carrier ⊗[ℂ] Ks.carrier))
    (x : pairDom Hs Ks DA DB) (x₀ : DA ⊗[ℂ] DB)
    (hx : (x : Hs.carrier ⊗[ℂ] Ks.carrier) = inclPair Hs Ks DA DB x₀) :
    pairLiftDom Hs Ks DA DB L x = L x₀ := by
  have hxx : (LinearEquiv.ofInjective (inclPair Hs Ks DA DB).toLinearMap
      (fun _ _ h => (inclPair Hs Ks DA DB).injective h)) x₀ = x := by
    apply Subtype.ext; rw [hx]; rfl
  have h2 : (LinearEquiv.ofInjective (inclPair Hs Ks DA DB).toLinearMap
      (fun _ _ h => (inclPair Hs Ks DA DB).injective h)).symm x = x₀ := by
    rw [← hxx]; simp
  exact congrArg (fun z => L z) h2

/-- A linear map `D_A ⊗ D_B → H ⊗ K`, read as an operator in the completed tensor product on
the domain `cpairDom` of the tensor sum. -/
def pairLiftOp (L : (DA ⊗[ℂ] DB) →ₗ[ℂ] (Hs.carrier ⊗[ℂ] Ks.carrier)) :
    cpairDom Hs Ks DA DB →ₗ[ℂ] ctensor Hs Ks :=
  pushOp (pairEmb Hs Ks) (pairLiftDom Hs Ks DA DB L)

theorem pairLiftOp_apply (L : (DA ⊗[ℂ] DB) →ₗ[ℂ] (Hs.carrier ⊗[ℂ] Ks.carrier))
    (x : cpairDom Hs Ks DA DB) (x₀ : DA ⊗[ℂ] DB)
    (hx : (x : ctensor Hs Ks) = pairEmb Hs Ks (inclPair Hs Ks DA DB x₀)) :
    pairLiftOp Hs Ks DA DB L x = pairEmb Hs Ks (L x₀) := by
  have hmem : inclPair Hs Ks DA DB x₀ ∈ pairDom Hs Ks DA DB := ⟨x₀, rfl⟩
  have h1 : pairLiftOp Hs Ks DA DB L x
      = pairEmb Hs Ks (pairLiftDom Hs Ks DA DB L ⟨inclPair Hs Ks DA DB x₀, hmem⟩) :=
    pushOp_apply (pairEmb Hs Ks) (pairLiftDom Hs Ks DA DB L) x ⟨inclPair Hs Ks DA DB x₀, hmem⟩ hx
  rw [h1, pairLiftDom_apply Hs Ks DA DB L ⟨inclPair Hs Ks DA DB x₀, hmem⟩ x₀ rfl]

theorem cpairOp_eq_pairLiftOp (A : DA →ₗ[ℂ] Hs.carrier) (B : DB →ₗ[ℂ] Ks.carrier) :
    cpairOp Hs Ks DA DB A B = pairLiftOp Hs Ks DA DB (sumPoly Hs Ks DA DB A B) := rfl

/-- Every vector of `cpairDom` comes from the algebraic tensor product of the domains. -/
theorem exists_pre (x : cpairDom Hs Ks DA DB) :
    ∃ x₀ : DA ⊗[ℂ] DB, (x : ctensor Hs Ks) = pairEmb Hs Ks (inclPair Hs Ks DA DB x₀) := by
  obtain ⟨z, hz, hze⟩ := x.2
  obtain ⟨x₀, rfl⟩ := hz
  exact ⟨x₀, hze.symm⟩

/-- A linear map that is symmetric at the algebraic level gives a symmetric operator. -/
theorem symmetricOn_pairLiftOp (L : (DA ⊗[ℂ] DB) →ₗ[ℂ] (Hs.carrier ⊗[ℂ] Ks.carrier))
    (hL : ∀ x y : DA ⊗[ℂ] DB,
      (inner ℂ (L x) (inclPair Hs Ks DA DB y) : ℂ) = inner ℂ (inclPair Hs Ks DA DB x) (L y)) :
    SymmetricOn (cpairDom Hs Ks DA DB) (pairLiftOp Hs Ks DA DB L) := by
  intro x y
  obtain ⟨x₀, hx⟩ := exists_pre Hs Ks DA DB x
  obtain ⟨y₀, hy⟩ := exists_pre Hs Ks DA DB y
  rw [pairLiftOp_apply Hs Ks DA DB L x x₀ hx, pairLiftOp_apply Hs Ks DA DB L y y₀ hy, hx, hy,
    LinearIsometry.inner_map_map, LinearIsometry.inner_map_map]
  exact hL x₀ y₀

/-- The product `V ⊗ Y` of two symmetric operators is symmetric at the algebraic level. -/
theorem mapPoly_symm (V : DA →ₗ[ℂ] Hs.carrier) (Y : DB →ₗ[ℂ] Ks.carrier)
    (hV : SymmetricOn DA V) (hY : SymmetricOn DB Y) :
    ∀ x y : DA ⊗[ℂ] DB,
      (inner ℂ (TensorProduct.map V Y x) (inclPair Hs Ks DA DB y) : ℂ)
        = inner ℂ (inclPair Hs Ks DA DB x) (TensorProduct.map V Y y) := by
  have hI : ∀ z : DA ⊗[ℂ] DB, inclPair Hs Ks DA DB z = (inclPair Hs Ks DA DB).toLinearMap z :=
    fun z => rfl
  have hpure : ∀ (a : DA) (b : DB) (y : DA ⊗[ℂ] DB),
      (inner ℂ (TensorProduct.map V Y (a ⊗ₜ[ℂ] b)) (inclPair Hs Ks DA DB y) : ℂ)
        = inner ℂ (inclPair Hs Ks DA DB (a ⊗ₜ[ℂ] b)) (TensorProduct.map V Y y) := by
    intro a b y
    induction y using TensorProduct.induction_on with
    | zero => rw [hI 0, map_zero, map_zero, inner_zero_right, inner_zero_right]
    | tmul c d =>
        simp only [TensorProduct.map_tmul, inclPair_tmul, TensorProduct.inner_tmul, hV a c,
          hY b d]
    | add s t hs ht => rw [hI (s + t), map_add, map_add, inner_add_right, inner_add_right,
        ← hI s, ← hI t, hs, ht]
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => rw [hI 0, map_zero, map_zero, inner_zero_left, inner_zero_left]
  | tmul a b => exact hpure a b y
  | add s t hs ht => rw [hI (s + t), map_add, map_add, inner_add_left, inner_add_left,
      ← hI s, ← hI t, hs, ht]

variable {ι : Type*} [Fintype ι]

/-- The product coupling `Σᵢ Vᵢ ⊗ Yᵢ` on the algebraic tensor product of the domains. -/
def couplingPoly (V : ι → DA →ₗ[ℂ] Hs.carrier) (Y : ι → DB →ₗ[ℂ] Ks.carrier) :
    (DA ⊗[ℂ] DB) →ₗ[ℂ] (Hs.carrier ⊗[ℂ] Ks.carrier) :=
  ∑ i, TensorProduct.map (V i) (Y i)

theorem symmetricOn_coupling (V : ι → DA →ₗ[ℂ] Hs.carrier) (Y : ι → DB →ₗ[ℂ] Ks.carrier)
    (hV : ∀ i, SymmetricOn DA (V i)) (hY : ∀ i, SymmetricOn DB (Y i)) :
    SymmetricOn (cpairDom Hs Ks DA DB) (pairLiftOp Hs Ks DA DB (couplingPoly Hs Ks DA DB V Y)) := by
  refine symmetricOn_pairLiftOp Hs Ks DA DB _ fun x y => ?_
  simp only [couplingPoly, LinearMap.sum_apply, sum_inner, inner_sum]
  exact Finset.sum_congr rfl fun i _ => mapPoly_symm Hs Ks DA DB (V i) (Y i) (hV i) (hY i) x y

/-! ## 3. The relative bound -/

/-- **The coupling is bounded relative to the tensor sum**, with relative bound `< 1`, as soon
as the second factor is finite-dimensional and every `Vᵢ` is `A`-bounded with relative bound
`0`. -/
theorem coupling_relBound [FiniteDimensional ℂ DB] (A : DA →ₗ[ℂ] Hs.carrier)
    (B : DB →ₗ[ℂ] Ks.carrier) (V : ι → DA →ₗ[ℂ] Hs.carrier) (Y : ι → DB →ₗ[ℂ] Ks.carrier)
    (hV : ∀ i, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ u : DA,
      ‖V i u‖ ≤ ε * ‖A u‖ + C * ‖(u : Hs.carrier)‖) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ b ∧ ∀ x : cpairDom Hs Ks DA DB,
      ‖pairLiftOp Hs Ks DA DB (couplingPoly Hs Ks DA DB V Y) x‖
        ≤ a * ‖cpairOp Hs Ks DA DB A B x‖ + b * ‖(x : ctensor Hs Ks)‖ := by
  classical
  set β := stdOrthonormalBasis ℂ DB with hβdef
  have hβK : Orthonormal ℂ (fun j => ((β j : DB) : Ks.carrier)) :=
    β.orthonormal.comp_linearIsometry DB.subtypeₗᵢ
  set MY : ℝ := ∑ i, ∑ j, ‖Y i (β j)‖ with hMY
  set MB : ℝ := ∑ j, ‖B (β j)‖ with hMB
  have hMY0 : 0 ≤ MY := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hMB0 : 0 ≤ MB := Finset.sum_nonneg fun j _ => norm_nonneg _
  set ε : ℝ := 1 / (2 * (MY + 1)) with hε
  have hε0 : 0 < ε := by positivity
  choose C hC using fun i => hV i ε hε0
  set Cs : ℝ := ∑ i, |C i| with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hCi : ∀ i, |C i| ≤ Cs := fun i =>
    Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  refine ⟨MY * ε, MY * ε * MB + MY * Cs, by positivity, ?_, by positivity, ?_⟩
  · rw [hε]
    rw [show MY * (1 / (2 * (MY + 1))) = MY / (2 * (MY + 1)) by ring,
      div_lt_one (by positivity)]
    linarith
  intro x
  obtain ⟨x₀, hx⟩ := exists_pre Hs Ks DA DB x
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℂ DB) → DA, x₀ = ∑ j, c j ⊗ₜ[ℂ] β j := by
    refine ⟨fun j => TensorProduct.equivFinsuppOfBasisRight β.toBasis x₀ j, ?_⟩
    conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisRight β.toBasis).symm_apply_apply x₀]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_fintype]
    · simp [OrthonormalBasis.coe_toBasis]
    · intro i; simp
  have hincl : inclPair Hs Ks DA DB x₀
      = ∑ j, (c j : Hs.carrier) ⊗ₜ[ℂ] ((β j : DB) : Ks.carrier) := by
    change (inclPair Hs Ks DA DB).toLinearMap x₀ = _
    rw [hc, map_sum]; rfl
  have hsum : sumPoly Hs Ks DA DB A B x₀
      = ∑ j, A (c j) ⊗ₜ[ℂ] ((β j : DB) : Ks.carrier)
        + ∑ j, (c j : Hs.carrier) ⊗ₜ[ℂ] B (β j) := by
    rw [hc, map_sum, ← Finset.sum_add_distrib]; rfl
  have hcoup : couplingPoly Hs Ks DA DB V Y x₀
      = ∑ i, ∑ j, V i (c j) ⊗ₜ[ℂ] Y i (β j) := by
    rw [hc, couplingPoly, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]; rfl
  have hnx : ‖(x : ctensor Hs Ks)‖ = ‖inclPair Hs Ks DA DB x₀‖ := by
    rw [hx, LinearIsometry.norm_map]
  have hnH : ‖cpairOp Hs Ks DA DB A B x‖ = ‖sumPoly Hs Ks DA DB A B x₀‖ := by
    rw [cpairOp_apply Hs Ks DA DB A B x x₀ hx, LinearIsometry.norm_map]
  have hnB : ‖pairLiftOp Hs Ks DA DB (couplingPoly Hs Ks DA DB V Y) x‖
      = ‖couplingPoly Hs Ks DA DB V Y x₀‖ := by
    rw [pairLiftOp_apply Hs Ks DA DB _ x x₀ hx, LinearIsometry.norm_map]
  rw [hnx, hnH, hnB, hincl, hsum, hcoup]
  set S := ‖∑ j, (c j : Hs.carrier) ⊗ₜ[ℂ] ((β j : DB) : Ks.carrier)‖ with hS
  set Sh := ‖∑ j, A (c j) ⊗ₜ[ℂ] ((β j : DB) : Ks.carrier)‖ with hSh
  set T := ‖∑ j, A (c j) ⊗ₜ[ℂ] ((β j : DB) : Ks.carrier)
      + ∑ j, (c j : Hs.carrier) ⊗ₜ[ℂ] B (β j)‖ with hT
  have hcj : ∀ j, ‖(c j : Hs.carrier)‖ ≤ S := fun j =>
    norm_le_norm_sum_tmul_orthonormal hβK (fun j => (c j : Hs.carrier)) j
  have hAcj : ∀ j, ‖A (c j)‖ ≤ Sh := fun j =>
    norm_le_norm_sum_tmul_orthonormal hβK (fun j => A (c j)) j
  have hS0 : 0 ≤ S := norm_nonneg _
  have hSh0 : 0 ≤ Sh := norm_nonneg _
  have hShT : Sh ≤ T + S * MB := by
    have h1 : Sh ≤ T + ‖∑ j, (c j : Hs.carrier) ⊗ₜ[ℂ] B (β j)‖ := by
      rw [hSh, hT]
      have := norm_sub_le (∑ j, A (c j) ⊗ₜ[ℂ] ((β j : DB) : Ks.carrier)
        + ∑ j, (c j : Hs.carrier) ⊗ₜ[ℂ] B (β j)) (∑ j, (c j : Hs.carrier) ⊗ₜ[ℂ] B (β j))
      simpa using this
    have h2 : ‖∑ j, (c j : Hs.carrier) ⊗ₜ[ℂ] B (β j)‖ ≤ S * MB := by
      refine (norm_sum_tmul_le _ _).trans ?_
      rw [hMB, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcj j) (norm_nonneg _)
    linarith
  have hVc : ∀ i j, ‖V i (c j)‖ ≤ ε * Sh + Cs * S := by
    intro i j
    refine (hC i (c j)).trans ?_
    have h1 : C i * ‖(c j : Hs.carrier)‖ ≤ Cs * S :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)).trans
        (mul_le_mul (hCi i) (hcj j) (norm_nonneg _) hCs0)
    have h2 : ε * ‖A (c j)‖ ≤ ε * Sh := mul_le_mul_of_nonneg_left (hAcj j) hε0.le
    linarith
  have hcoupB : ‖∑ i, ∑ j, V i (c j) ⊗ₜ[ℂ] Y i (β j)‖ ≤ (ε * Sh + Cs * S) * MY := by
    refine (norm_sum_le _ _).trans ?_
    rw [hMY, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (norm_sum_tmul_le _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hVc i j) (norm_nonneg _)
  calc ‖∑ i, ∑ j, V i (c j) ⊗ₜ[ℂ] Y i (β j)‖ ≤ (ε * Sh + Cs * S) * MY := hcoupB
    _ ≤ (ε * (T + S * MB) + Cs * S) * MY := by
        gcongr
    _ = MY * ε * T + (MY * ε * MB + MY * Cs) * S := by ring

/-- **Kato–Rellich for a product coupling on a tensor sum.**  If the tensor sum
`A ⊗ 1 + 1 ⊗ B` is essentially self-adjoint on `cpairDom`, the second factor is
finite-dimensional, every `Vᵢ` is symmetric and `A`-bounded with relative bound `0`, and every
`Yᵢ` is symmetric, then `A ⊗ 1 + 1 ⊗ B + Σᵢ Vᵢ ⊗ Yᵢ` is essentially self-adjoint on
`cpairDom`. -/
theorem essentiallySelfAdjointOn_tensorSum_add_coupling [FiniteDimensional ℂ DB]
    (A : DA →ₗ[ℂ] Hs.carrier) (B : DB →ₗ[ℂ] Ks.carrier)
    (V : ι → DA →ₗ[ℂ] Hs.carrier) (Y : ι → DB →ₗ[ℂ] Ks.carrier)
    (hA : SymmetricOn DA A) (hB : SymmetricOn DB B)
    (hV : ∀ i, SymmetricOn DA (V i)) (hY : ∀ i, SymmetricOn DB (Y i))
    (hrel : ∀ i, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ u : DA,
      ‖V i u‖ ≤ ε * ‖A u‖ + C * ‖(u : Hs.carrier)‖)
    (hesa : EssentiallySelfAdjointOn (cpairDom Hs Ks DA DB) (cpairOp Hs Ks DA DB A B)) :
    EssentiallySelfAdjointOn (cpairDom Hs Ks DA DB)
      (cpairOp Hs Ks DA DB A B + pairLiftOp Hs Ks DA DB (couplingPoly Hs Ks DA DB V Y)) := by
  obtain ⟨a, b, ha, ha1, hb, hbound⟩ := coupling_relBound Hs Ks DA DB A B V Y hrel
  exact KatoRellich.essentiallySelfAdjointOn_add_relBounded _ _
    (symmetricOn_cpairOp Hs Ks DA DB A B hA hB) hesa
    (symmetricOn_coupling Hs Ks DA DB V Y hV hY) ha ha1 hb hbound

end Lift

end

end BookProof.TensorKatoRellich


