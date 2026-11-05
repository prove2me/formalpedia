-- Prove2me | Definitions.Def_ChapterTensorSumEsa
-- name    : ChapterTensorSumEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-04T14:51:16.310134+00:00
-- url     : https://prove2.me/theorems/ad91af46-ce2f-4e42-bfde-03442e14ef9a
-- title:
--   Chapter TensorSumEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterTensorSumEsa.lean`): generated def bundle for ChapterTensorSumEsa. See BookProof/ChapterTensorSumEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterTensorSumEsa.lean

import Theorems.Thm_BookProof_GraphCore_mem_pushDom

import Definitions.Def_ChapterFlowDGammaEsa
import Definitions.Def_ChapterEsaOneParticleDGamma
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneSeparable
import Theorems.Thm_BookProof_ChapterStoneSeparable_mulSA_position_unbounded
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Mathlib
import Theorems.Thm_BookProof_GraphCore_essentiallySelfAdjointOn_of_graphCore
import Theorems.Thm_BookProof_GraphCore_isGraphCore_pushOp
import Theorems.Thm_BookProof_GraphCore_pushDom_mono
import Theorems.Thm_BookProof_GraphCore_pushOp_apply
import Theorems.Thm_BookProof_GraphCore_symmetricOn_pushOp
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Theorems.Thm_BookProof_TensorCore_norm_tmul_sub_le


/-!
# The tensor sum of two **different** operators: `A ⊗ 1 + 1 ⊗ B`

`BookProof/ChapterFlowDGammaEsa.lean` and `BookProof/ChapterEsaOneParticleDGamma.lean` settle
the second quantization `dΓ(A)` of a *single* one-particle operator, where every factor of the
tensor power carries the *same* operator.  This module removes that restriction in the
two-factor case: the two Hilbert spaces are different, and so are the two operators.

For a symmetric operator `A` on a dense domain `D_A` of `H` and a symmetric operator `B` on a
dense domain `D_B` of `K`, the **tensor sum**

`(A ⊗ 1 + 1 ⊗ B) (x ⊗ y) = (A x) ⊗ y + x ⊗ (B y)`

is studied on the algebraic tensor product `D_A ⊗ D_B`, inside the Hilbert space `H ⊗̂ K` — the
completion of the algebraic tensor product of the two spaces.  This is the separated-variables
form of a Hamiltonian: for `V(u, v) = V₁(u) + V₂(v)` the operator `−Δ + V` on a product is the
tensor sum of the two one-factor operators, so the theorem below is the exact tool that glues
two continuum factors together without any relative bound, semiboundedness or sign condition.

## What is proved

* `inclPair`, `sumPoly`, `pairDom`, `pairOp`, `ctensor`, `pairEmb`, `cpairDom`, `cpairOp` — the
  tensor sum as an operator on `D_A ⊗ D_B`, in `H ⊗ K` and then in the completion `H ⊗̂ K`.
* `sumPoly_symm`, `symmetricOn_pairOp`, `symmetricOn_cpairOp` — the tensor sum of two
  symmetric operators is symmetric.
* `dense_pairDom`, `dense_cpairDom` — the tensor product of two dense domains is dense: an
  elementary tensor is approximated by moving each factor into its domain, and the two errors
  add.
* `pflow`, `norm_pflow`, `hasDerivAt_pflow` — the **product flow** `U t ⊗ V t` of the two
  one-factor flows: it is isometric, preserves `D_A ⊗ D_B`, and satisfies the Leibniz rule,
  hence solves the Schrödinger equation of the tensor sum.
* `essentiallySelfAdjointOn_cpairDom_flow` — Nelson's invariant-domain criterion
  (`BookProof.FlowDGamma.essentiallySelfAdjointOn_of_orbits`) applied to those orbits: **the
  tensor sum is essentially self-adjoint** as soon as each factor carries a unitary flow.
* `essentiallySelfAdjointOn_cpairDom_selfAdjoint` — the headline for two **self-adjoint**
  operators, Stone's theorem supplying the two flows.  No boundedness, no positivity and no
  assumption on either spectrum.
* `pairCorePoly`, `graphPair`, `exists_pair_core_approx`, `isGraphCore_pairCore`,
  `isGraphCore_cpairCore` — the **two-factor core estimate**: if `C_A` is a graph-norm core of
  `A` and `C_B` one of `B`, then `C_A ⊗ C_B` is a core of the tensor sum; with the transfer
  principle this gives `essentiallySelfAdjointOn_cpairCore` and
  `essentiallySelfAdjointOn_cpairCore_selfAdjoint`.
* `essentiallySelfAdjointOn_cpairDom_esa` — the hypotheses weakened from self-adjointness to
  **essential** self-adjointness on each factor: the two closures are self-adjoint
  (`BookProof.EsaOneParticle.closureSelfAdjoint`), each domain is a core of its closure, the
  core estimate applies, and `exists_pair_of_mem_pairCorePoly` identifies the graph of the
  tensor sum of the closures over `D_A ⊗ D_B` with the graph of the tensor sum of `A` and `B`.
* `tensorSum_stone_flow`, `tensorSum_stone_flow_esa` — the resulting **unitary group**
  `e^{−it(A ⊗ 1 + 1 ⊗ B)}` on `H ⊗̂ K`, via the Stone bridge.
* `positionCube_essentiallySelfAdjoint` — a concrete instance with two *different* unbounded
  operators: multiplication by `k` on `ℓ²(ℤ)` in the first factor and by `k³` in the second;
  `positionCube_first_not_bounded` records that the first factor is genuinely unbounded.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.TensorSumEsa

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
  BookProof.FlowDGamma BookProof.EsaOneParticle BookProof.ChapterStoneResolvent
  BookProof.TensorOpBound BookProof.EsaClosure

noncomputable section

/-! ## 1. The two-factor tensor sum -/

section Defs

variable (Hs Ks : IPSpace) (DA : Submodule ℂ Hs.carrier) (DB : Submodule ℂ Ks.carrier)

/-- The isometric inclusion `D_A ⊗ D_B → H ⊗ K` of the algebraic tensor product of the two
domains into the algebraic tensor product of the two spaces. -/
def inclPair : (DA ⊗[ℂ] DB) →ₗᵢ[ℂ] (Hs.carrier ⊗[ℂ] Ks.carrier) :=
  TensorProduct.mapIsometry DA.subtypeₗᵢ DB.subtypeₗᵢ

@[simp] theorem inclPair_tmul (a : DA) (b : DB) :
    inclPair Hs Ks DA DB (a ⊗ₜ[ℂ] b) = (a : Hs.carrier) ⊗ₜ[ℂ] (b : Ks.carrier) := rfl

variable (A : DA →ₗ[ℂ] Hs.carrier) (B : DB →ₗ[ℂ] Ks.carrier)

/-- The **tensor sum** `A ⊗ 1 + 1 ⊗ B`, on the algebraic tensor product of the domains. -/
def sumPoly : (DA ⊗[ℂ] DB) →ₗ[ℂ] (Hs.carrier ⊗[ℂ] Ks.carrier) :=
  TensorProduct.map A DB.subtype + TensorProduct.map DA.subtype B

@[simp] theorem sumPoly_tmul (a : DA) (b : DB) :
    sumPoly Hs Ks DA DB A B (a ⊗ₜ[ℂ] b)
      = (A a) ⊗ₜ[ℂ] (b : Ks.carrier) + (a : Hs.carrier) ⊗ₜ[ℂ] (B b) := rfl

/-- The image of `D_A ⊗ D_B` inside `H ⊗ K`: the domain of the tensor sum. -/
def pairDom : Submodule ℂ (Hs.carrier ⊗[ℂ] Ks.carrier) :=
  LinearMap.range (inclPair Hs Ks DA DB).toLinearMap

/-- The tensor sum as an operator on the subspace `pairDom` of `H ⊗ K`. -/
def pairOp : pairDom Hs Ks DA DB →ₗ[ℂ] (Hs.carrier ⊗[ℂ] Ks.carrier) :=
  sumPoly Hs Ks DA DB A B ∘ₗ
    (LinearEquiv.ofInjective (inclPair Hs Ks DA DB).toLinearMap
      (fun a b h => (inclPair Hs Ks DA DB).injective h)).symm.toLinearMap

theorem pairOp_apply (x : pairDom Hs Ks DA DB) (x₀ : DA ⊗[ℂ] DB)
    (hx : (x : Hs.carrier ⊗[ℂ] Ks.carrier) = inclPair Hs Ks DA DB x₀) :
    pairOp Hs Ks DA DB A B x = sumPoly Hs Ks DA DB A B x₀ := by
  have hxx : (LinearEquiv.ofInjective (inclPair Hs Ks DA DB).toLinearMap
      (fun a b h => (inclPair Hs Ks DA DB).injective h)) x₀ = x := by
    apply Subtype.ext; rw [hx]; rfl
  have h2 : (LinearEquiv.ofInjective (inclPair Hs Ks DA DB).toLinearMap
      (fun a b h => (inclPair Hs Ks DA DB).injective h)).symm x = x₀ := by
    rw [← hxx]; simp
  exact congrArg (fun z => sumPoly Hs Ks DA DB A B z) h2

/-- The Hilbert space `H ⊗̂ K`: the completion of the algebraic tensor product. -/
abbrev ctensor : Type := UniformSpace.Completion (Hs.carrier ⊗[ℂ] Ks.carrier)

/-- The isometric embedding of the algebraic tensor product into its completion. -/
def pairEmb : (Hs.carrier ⊗[ℂ] Ks.carrier) →ₗᵢ[ℂ] ctensor Hs Ks :=
  UniformSpace.Completion.toComplₗᵢ

/-- The domain of the tensor sum inside the completed tensor product. -/
def cpairDom : Submodule ℂ (ctensor Hs Ks) :=
  pushDom (pairEmb Hs Ks) (pairDom Hs Ks DA DB)

/-- The tensor sum as an operator in the completed tensor product. -/
def cpairOp : cpairDom Hs Ks DA DB →ₗ[ℂ] ctensor Hs Ks :=
  pushOp (pairEmb Hs Ks) (pairOp Hs Ks DA DB A B)

theorem cpairOp_apply (x : cpairDom Hs Ks DA DB) (x₀ : DA ⊗[ℂ] DB)
    (hx : (x : ctensor Hs Ks) = pairEmb Hs Ks (inclPair Hs Ks DA DB x₀)) :
    cpairOp Hs Ks DA DB A B x = pairEmb Hs Ks (sumPoly Hs Ks DA DB A B x₀) := by
  have hmem : inclPair Hs Ks DA DB x₀ ∈ pairDom Hs Ks DA DB := ⟨x₀, rfl⟩
  have h1 : cpairOp Hs Ks DA DB A B x
      = pairEmb Hs Ks (pairOp Hs Ks DA DB A B ⟨inclPair Hs Ks DA DB x₀, hmem⟩) :=
    pushOp_apply (pairEmb Hs Ks) (pairOp Hs Ks DA DB A B) x ⟨inclPair Hs Ks DA DB x₀, hmem⟩ hx
  rw [h1, pairOp_apply Hs Ks DA DB A B ⟨inclPair Hs Ks DA DB x₀, hmem⟩ x₀ rfl]

end Defs

/-! ## 2. Symmetry -/

section Symmetry

variable (Hs Ks : IPSpace) (DA : Submodule ℂ Hs.carrier) (DB : Submodule ℂ Ks.carrier)
  (A : DA →ₗ[ℂ] Hs.carrier) (B : DB →ₗ[ℂ] Ks.carrier)

set_option maxHeartbeats 1000000 in
/-- The tensor sum of two symmetric operators is symmetric, on the algebraic level. -/
theorem sumPoly_symm (hA : SymmetricOn DA A) (hB : SymmetricOn DB B) :
    ∀ x y : DA ⊗[ℂ] DB,
      (inner ℂ (sumPoly Hs Ks DA DB A B x) (inclPair Hs Ks DA DB y) : ℂ)
        = inner ℂ (inclPair Hs Ks DA DB x) (sumPoly Hs Ks DA DB A B y) := by
  have hspan : ∀ z : DA ⊗[ℂ] DB,
      z ∈ Submodule.span ℂ {t : DA ⊗[ℂ] DB | ∃ (p : DA) (q : DB), p ⊗ₜ[ℂ] q = t} := by
    intro z
    rw [TensorProduct.span_tmul_eq_top]
    trivial
  have hpure : ∀ (a : DA) (b : DB) (y : DA ⊗[ℂ] DB),
      (inner ℂ (sumPoly Hs Ks DA DB A B (a ⊗ₜ[ℂ] b)) (inclPair Hs Ks DA DB y) : ℂ)
        = inner ℂ (inclPair Hs Ks DA DB (a ⊗ₜ[ℂ] b)) (sumPoly Hs Ks DA DB A B y) := by
    intro a b y
    induction (hspan y) using Submodule.span_induction with
    | mem t ht =>
        obtain ⟨c, d, rfl⟩ := ht
        simp only [sumPoly_tmul, inclPair_tmul, inner_add_left, inner_add_right,
          TensorProduct.inner_tmul, hA a c, hB b d]
    | zero =>
      have hz1 : (inclPair Hs Ks DA DB) (0 : DA ⊗[ℂ] DB) = 0 := by simp [inclPair]
      have hz2 : (sumPoly Hs Ks DA DB A B) (0 : DA ⊗[ℂ] DB) = 0 := by simp [sumPoly]
      rw [hz1, hz2]
      exact (inner_zero_right _).trans (inner_zero_right _).symm
    | add s t _ _ hs ht => simp only [map_add, inner_add_right, hs, ht]
    | smul r s _ hs =>
      have h1 : (inclPair Hs Ks DA DB) (r • s) = r • (inclPair Hs Ks DA DB) s := by
        simp [inclPair]
      have h2 : (sumPoly Hs Ks DA DB A B) (r • s) = r • (sumPoly Hs Ks DA DB A B) s := by
        simp [sumPoly]
      rw [h1, h2]
      -- The `have`s pin the statement's instances (elaboration is
      -- left-to-right there), unlike a bare `exact a.trans b.trans c`, whose
      -- instance metavariables are still unresolved when the middle argument
      -- is checked.
      have e1 : inner ℂ ((sumPoly Hs Ks DA DB A B) (a ⊗ₜ[ℂ] b))
          (r • (inclPair Hs Ks DA DB) s)
          = r * inner ℂ ((sumPoly Hs Ks DA DB A B) (a ⊗ₜ[ℂ] b))
            ((inclPair Hs Ks DA DB) s) := by
        exact inner_smul_right ((sumPoly Hs Ks DA DB A B) (a ⊗ₜ[ℂ] b))
          ((inclPair Hs Ks DA DB) s) r
      have e2 : inner ℂ ((inclPair Hs Ks DA DB) (a ⊗ₜ[ℂ] b))
          (r • (sumPoly Hs Ks DA DB A B) s)
          = r * inner ℂ ((inclPair Hs Ks DA DB) (a ⊗ₜ[ℂ] b))
            ((sumPoly Hs Ks DA DB A B) s) := by
        exact inner_smul_right ((inclPair Hs Ks DA DB) (a ⊗ₜ[ℂ] b))
          ((sumPoly Hs Ks DA DB A B) s) r
      rw [e1, e2]
      exact congrArg (fun z => r * z) hs
  intro x y
  induction (hspan x) using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨a, b, rfl⟩ := ht
      exact hpure a b y
  | zero =>
      have hz1 : (inclPair Hs Ks DA DB) (0 : DA ⊗[ℂ] DB) = 0 := by simp [inclPair]
      rw [hz1]
      exact (inner_zero_left _).symm
  | add s t _ _ hs ht => simp only [map_add, inner_add_left, hs, ht]
  | smul r s _ hs =>
      have h1 : (inclPair Hs Ks DA DB) (r • s) = r • (inclPair Hs Ks DA DB) s := by
        simp [inclPair]
      have h2 : (sumPoly Hs Ks DA DB A B) (r • s) = r • (sumPoly Hs Ks DA DB A B) s := by
        simp [sumPoly]
      rw [h1, h2]
      have e1 : inner ℂ (r • (sumPoly Hs Ks DA DB A B) s) ((inclPair Hs Ks DA DB) y)
          = star r * inner ℂ ((sumPoly Hs Ks DA DB A B) s) ((inclPair Hs Ks DA DB) y) := by
        exact inner_smul_left ((sumPoly Hs Ks DA DB A B) s) ((inclPair Hs Ks DA DB) y) r
      have e2 : inner ℂ (r • (inclPair Hs Ks DA DB) s) ((sumPoly Hs Ks DA DB A B) y)
          = star r * inner ℂ ((inclPair Hs Ks DA DB) s) ((sumPoly Hs Ks DA DB A B) y) := by
        exact inner_smul_left ((inclPair Hs Ks DA DB) s) ((sumPoly Hs Ks DA DB A B) y) r
      rw [e1, e2]
      exact congrArg (fun z => star r * z) hs

/-- The tensor sum is symmetric on its domain inside `H ⊗ K`. -/
theorem symmetricOn_pairOp (hA : SymmetricOn DA A) (hB : SymmetricOn DB B) :
    SymmetricOn (pairDom Hs Ks DA DB) (pairOp Hs Ks DA DB A B) := by
  intro x y
  obtain ⟨x₀, hx₀⟩ := x.2
  obtain ⟨y₀, hy₀⟩ := y.2
  have hx : (x : Hs.carrier ⊗[ℂ] Ks.carrier) = inclPair Hs Ks DA DB x₀ := hx₀.symm
  have hy : (y : Hs.carrier ⊗[ℂ] Ks.carrier) = inclPair Hs Ks DA DB y₀ := hy₀.symm
  rw [pairOp_apply Hs Ks DA DB A B x x₀ hx, pairOp_apply Hs Ks DA DB A B y y₀ hy, hx, hy]
  exact sumPoly_symm Hs Ks DA DB A B hA hB x₀ y₀

/-- The tensor sum is symmetric in the completed tensor product. -/
theorem symmetricOn_cpairOp (hA : SymmetricOn DA A) (hB : SymmetricOn DB B) :
    SymmetricOn (cpairDom Hs Ks DA DB) (cpairOp Hs Ks DA DB A B) :=
  symmetricOn_pushOp (pairEmb Hs Ks) (pairOp Hs Ks DA DB A B)
    (symmetricOn_pairOp Hs Ks DA DB A B hA hB)

end Symmetry

/-! ## 3. Density -/

section Density

variable (Hs Ks : IPSpace) (DA : Submodule ℂ Hs.carrier) (DB : Submodule ℂ Ks.carrier)

/-- If the two domains are dense, the algebraic tensor product of the domains is dense in the
algebraic tensor product of the spaces: an elementary tensor is approximated by moving each
factor into its domain, and the two errors add. -/
theorem dense_pairDom (hA : Dense (DA : Set Hs.carrier)) (hB : Dense (DB : Set Ks.carrier)) :
    Dense ((pairDom Hs Ks DA DB : Submodule ℂ (Hs.carrier ⊗[ℂ] Ks.carrier)) :
      Set (Hs.carrier ⊗[ℂ] Ks.carrier)) := by
  have hclosed : ∀ z : Hs.carrier ⊗[ℂ] Ks.carrier,
      z ∈ (pairDom Hs Ks DA DB).topologicalClosure := by
    have hpure : ∀ (x : Hs.carrier) (y : Ks.carrier),
        x ⊗ₜ[ℂ] y ∈ (pairDom Hs Ks DA DB).topologicalClosure := by
      intro x y
      change x ⊗ₜ[ℂ] y ∈ closure ((pairDom Hs Ks DA DB : Submodule ℂ _) : Set _)
      refine Metric.mem_closure_iff.mpr ?_
      intro ε hε
      set C : ℝ := ‖x‖ + ‖y‖ + 2 with hC
      have hCpos : 0 < C := by
        have := norm_nonneg x
        have := norm_nonneg y
        rw [hC]; linarith
      set δ : ℝ := min 1 (ε / (2 * C)) with hδ
      have hδpos : 0 < δ := lt_min one_pos (by positivity)
      have hδone : δ ≤ 1 := min_le_left _ _
      have hδC : δ * C < ε := by
        have h1 : δ ≤ ε / (2 * C) := min_le_right _ _
        have h2 : δ * C ≤ (ε / (2 * C)) * C := mul_le_mul_of_nonneg_right h1 hCpos.le
        have h3 : (ε / (2 * C)) * C = ε / 2 := by field_simp
        rw [h3] at h2
        linarith
      obtain ⟨a, haD, ha⟩ := Metric.mem_closure_iff.mp (hA.closure_eq ▸ Set.mem_univ x) δ hδpos
      obtain ⟨b, hbD, hb⟩ := Metric.mem_closure_iff.mp (hB.closure_eq ▸ Set.mem_univ y) δ hδpos
      have ha' : ‖x - a‖ < δ := by rwa [← dist_eq_norm]
      have hb' : ‖y - b‖ < δ := by rwa [← dist_eq_norm]
      have hanorm : ‖a‖ ≤ ‖x‖ + δ := by
        have h1 := norm_sub_norm_le a x
        have h2 : ‖a - x‖ < δ := by rw [norm_sub_rev]; exact ha'
        linarith
      refine ⟨(a : Hs.carrier) ⊗ₜ[ℂ] (b : Ks.carrier),
        ⟨(⟨a, haD⟩ : DA) ⊗ₜ[ℂ] (⟨b, hbD⟩ : DB), rfl⟩, ?_⟩
      rw [dist_eq_norm]
      have hmove := TensorCore.norm_tmul_sub_le x a y b
      have hb1 : ‖x - a‖ * ‖y‖ ≤ δ * ‖y‖ :=
        mul_le_mul_of_nonneg_right ha'.le (norm_nonneg _)
      have hb2 : ‖a‖ * ‖y - b‖ ≤ (‖x‖ + δ) * δ :=
        mul_le_mul hanorm hb'.le (norm_nonneg _) (by
          have := norm_nonneg x; linarith)
      have hbudget : δ * ‖y‖ + (‖x‖ + δ) * δ ≤ δ * C := by
        have hfac : δ * C - (δ * ‖y‖ + (‖x‖ + δ) * δ) = δ * (2 - δ) := by rw [hC]; ring
        have hnn : 0 ≤ δ * (2 - δ) := mul_nonneg hδpos.le (by linarith)
        linarith
      linarith
    intro z
    have hz : z ∈ Submodule.span ℂ
        {t : Hs.carrier ⊗[ℂ] Ks.carrier |
          ∃ (p : Hs.carrier) (q : Ks.carrier), p ⊗ₜ[ℂ] q = t} := by
      rw [TensorProduct.span_tmul_eq_top]; trivial
    induction hz using Submodule.span_induction with
    | mem t ht => obtain ⟨p, q, rfl⟩ := ht; exact hpure p q
    | zero => exact Submodule.zero_mem _
    | add s t _ _ hs ht => exact Submodule.add_mem _ hs ht
    | smul c s _ hs => exact Submodule.smul_mem _ c hs
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  exact hclosed

/-- The same, in the completed tensor product: the image of a dense subspace under the
completion embedding is dense, because the embedding itself has dense range. -/
theorem dense_cpairDom (hA : Dense (DA : Set Hs.carrier)) (hB : Dense (DB : Set Ks.carrier)) :
    Dense ((cpairDom Hs Ks DA DB : Submodule ℂ (ctensor Hs Ks)) : Set (ctensor Hs Ks)) := by
  have hcont : Continuous (pairEmb Hs Ks) := (pairEmb Hs Ks).continuous
  have himg : (pairEmb Hs Ks) '' ((pairDom Hs Ks DA DB : Submodule ℂ _) : Set _)
      = ((cpairDom Hs Ks DA DB : Submodule ℂ (ctensor Hs Ks)) : Set (ctensor Hs Ks)) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
  rw [← himg]
  have hsub : Set.range (pairEmb Hs Ks)
      ⊆ closure ((pairEmb Hs Ks) '' ((pairDom Hs Ks DA DB : Submodule ℂ _) : Set _)) := by
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ closure ((pairDom Hs Ks DA DB : Submodule ℂ _) : Set _) := by
      rw [(dense_pairDom Hs Ks DA DB hA hB).closure_eq]; trivial
    exact (image_closure_subset_closure_image hcont) ⟨w, hw, rfl⟩
  have hdr : DenseRange (pairEmb Hs Ks) := by
    have : DenseRange ((↑) : (Hs.carrier ⊗[ℂ] Ks.carrier) → ctensor Hs Ks) :=
      UniformSpace.Completion.denseRange_coe
    exact this
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro z
  have h1 : closure (Set.range (pairEmb Hs Ks))
      ⊆ closure (closure ((pairEmb Hs Ks) '' ((pairDom Hs Ks DA DB : Submodule ℂ _) : Set _))) :=
    closure_mono hsub
  have h2 := h1 (hdr.closure_eq ▸ Set.mem_univ z)
  rwa [closure_closure] at h2

end Density

/-! ## 4. The product flow and essential self-adjointness -/

section Flow

variable {Hs Ks : IPSpace} {DA : Submodule ℂ Hs.carrier} {DB : Submodule ℂ Ks.carrier}
  {A : DA →ₗ[ℂ] Hs.carrier} {B : DB →ₗ[ℂ] Ks.carrier}

variable (P : OneParticleFlow Hs DA A) (Q : OneParticleFlow Ks DB B)

local instance : ContinuousSMul ℝ (Hs.carrier ⊗[ℂ] Ks.carrier) := by
  haveI : IsBoundedSMul ℝ (Hs.carrier ⊗[ℂ] Ks.carrier) := NormedSpace.toIsBoundedSMul
  exact IsBoundedSMul.continuousSMul

-- The normed `AddCommGroup`/`Module` structures on the complex tensor product are the ones
-- the product rule and the `Submodule.span_induction` motive both elaborate to; pinning
-- them here keeps goal and hypothesis from disagreeing about the hidden instances.
local instance : AddCommGroup (Hs.carrier ⊗[ℂ] Ks.carrier) :=
  TensorProduct.instNormedAddCommGroup.toAddCommGroup
local instance : Module ℝ (Hs.carrier ⊗[ℂ] Ks.carrier) := NormedSpace.complexToReal.toModule

/-- The product flow `U t ⊗ V t`, acting on the algebraic tensor product of the domains. -/
def pflow (t : ℝ) : (DA ⊗[ℂ] DB) →ₗ[ℂ] (DA ⊗[ℂ] DB) :=
  TensorProduct.map (OneParticleFlow.dmap P t) (OneParticleFlow.dmap Q t)

@[simp] theorem pflow_tmul (t : ℝ) (a : DA) (b : DB) :
    pflow P Q t (a ⊗ₜ[ℂ] b)
      = (OneParticleFlow.dmap P t a) ⊗ₜ[ℂ] (OneParticleFlow.dmap Q t b) :=
  TensorProduct.map_tmul _ _ _ _

theorem mem_span_tmul (x : DA ⊗[ℂ] DB) :
    x ∈ Submodule.span ℂ {t : DA ⊗[ℂ] DB | ∃ (p : DA) (q : DB), p ⊗ₜ[ℂ] q = t} := by
  rw [TensorProduct.span_tmul_eq_top]; trivial

theorem pflow_zero_time (x : DA ⊗[ℂ] DB) : pflow P Q 0 x = x := by
  induction (mem_span_tmul x) using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨p, q, rfl⟩ := hy
      rw [pflow_tmul]
      congr 1 <;> apply Subtype.ext
      · simp [P.U_zero]
      · simp [Q.U_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, ha]

theorem pflow_neg (t : ℝ) (x : DA ⊗[ℂ] DB) : pflow P Q (-t) (pflow P Q t x) = x := by
  induction (mem_span_tmul x) using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨p, q, rfl⟩ := hy
      rw [pflow_tmul, pflow_tmul, OneParticleFlow.dmap_neg, OneParticleFlow.dmap_neg]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, map_smul, ha]

theorem norm_pflow_le (t : ℝ) (x : DA ⊗[ℂ] DB) : ‖pflow P Q t x‖ ≤ ‖x‖ := by
  have h := TensorOpBound.norm_map_le (OneParticleFlow.dmap P t) (OneParticleFlow.dmap Q t)
    zero_le_one
    zero_le_one (fun a => by rw [OneParticleFlow.norm_dmap]; simp)
    (fun b => by rw [OneParticleFlow.norm_dmap]; simp) x
  simpa [pflow] using h

theorem norm_pflow (t : ℝ) (x : DA ⊗[ℂ] DB) : ‖pflow P Q t x‖ = ‖x‖ := by
  refine le_antisymm (norm_pflow_le P Q t x) ?_
  have h := norm_pflow_le P Q (-t) (pflow P Q t x)
  rwa [pflow_neg P Q t x] at h

include P Q in
/-- **The Leibniz rule for the product flow**: it solves the Schrödinger equation of the
tensor sum. -/
theorem hasDerivAt_pflow (x : DA ⊗[ℂ] DB) (t : ℝ) :
    @HasDerivAt ℝ _ (Hs.carrier ⊗[ℂ] Ks.carrier)
      TensorProduct.instNormedAddCommGroup.toAddCommGroup (NormedSpace.complexToReal.toModule)
      _ _ (fun s : ℝ => inclPair Hs Ks DA DB (pflow P Q s x))
      ((-Complex.I) • sumPoly Hs Ks DA DB A B (pflow P Q t x)) t := by
  have hpure : ∀ (a : DA) (b : DB),
      HasDerivAt (fun s : ℝ => inclPair Hs Ks DA DB (pflow P Q s (a ⊗ₜ[ℂ] b)))
        ((-Complex.I) • sumPoly Hs Ks DA DB A B (pflow P Q t (a ⊗ₜ[ℂ] b))) t := by
    intro a b
    have hf : HasDerivAt (fun s : ℝ => P.U s (a : Hs.carrier))
        ((-Complex.I) • A ⟨P.U t (a : Hs.carrier), P.mem_domain t a⟩) t := P.hasDerivAt_U a t
    have hg : HasDerivAt (fun s : ℝ => Q.U s (b : Ks.carrier))
        ((-Complex.I) • B ⟨Q.U t (b : Ks.carrier), Q.mem_domain t b⟩) t := Q.hasDerivAt_U b t
    have h := hasDerivAt_tmul hf hg
    have hcurve : (fun s : ℝ => (P.U s (a : Hs.carrier)) ⊗ₜ[ℂ] (Q.U s (b : Ks.carrier)))
        = fun s : ℝ => inclPair Hs Ks DA DB (pflow P Q s (a ⊗ₜ[ℂ] b)) := by
      funext s
      rw [pflow_tmul, inclPair_tmul, OneParticleFlow.dmap_coe, OneParticleFlow.dmap_coe]
    rw [hcurve] at h
    have hval : ((-Complex.I) • A ⟨P.U t (a : Hs.carrier), P.mem_domain t a⟩)
          ⊗ₜ[ℂ] (Q.U t (b : Ks.carrier))
        + (P.U t (a : Hs.carrier)) ⊗ₜ[ℂ]
            ((-Complex.I) • B ⟨Q.U t (b : Ks.carrier), Q.mem_domain t b⟩)
        = (-Complex.I) • sumPoly Hs Ks DA DB A B (pflow P Q t (a ⊗ₜ[ℂ] b)) := by
      rw [pflow_tmul, sumPoly_tmul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
        ← smul_add, OneParticleFlow.dmap_coe, OneParticleFlow.dmap_coe]
      rfl
    rw [hval] at h
    exact h
  induction (mem_span_tmul x) using Submodule.span_induction with
  | mem y hy => obtain ⟨p, q, rfl⟩ := hy; exact hpure p q
  | zero =>
      -- `simpa using h` re-elaborated the goal with a different (but intended
      -- to be equal) instance path and the defeq check failed; rewriting the
      -- function to the literal constant keeps the goal's own instances, so
      -- `hasDerivAt_const` unifies against them directly.
      have h0 : (fun s : ℝ => inclPair Hs Ks DA DB (pflow P Q s (0 : DA ⊗[ℂ] DB)))
          = fun _ : ℝ => (0 : Hs.carrier ⊗[ℂ] Ks.carrier) := by
        funext s; simp [inclPair, pflow, map_zero]
      rw [h0]
      exact hasDerivAt_const _ _
  | add a b _ _ ha hb =>
      have h := ha.add hb
      convert h using 1
      · funext s; simp [pflow, map_add]
      · simp [pflow, map_add, smul_add]
  | smul c a _ ha =>
      have h := ha.const_smul c
      have hfun : (c • fun s : ℝ => inclPair Hs Ks DA DB (pflow P Q s a))
          = fun s : ℝ => inclPair Hs Ks DA DB (pflow P Q s (c • a)) := by
        funext s; simp
      rw [hfun] at h
      have hval : c • ((-Complex.I) • sumPoly Hs Ks DA DB A B (pflow P Q t a))
          = (-Complex.I) • sumPoly Hs Ks DA DB A B (pflow P Q t (c • a)) := by
        rw [map_smul, map_smul]
        exact smul_comm c (-Complex.I) _
      rw [hval] at h
      exact h

/-- The orbit of a vector of `D_A ⊗ D_B`, inside the completed tensor product. -/
def porbit (x : DA ⊗[ℂ] DB) (t : ℝ) : cpairDom Hs Ks DA DB :=
  ⟨pairEmb Hs Ks (inclPair Hs Ks DA DB (pflow P Q t x)),
    mem_pushDom (pairEmb Hs Ks)
      (⟨inclPair Hs Ks DA DB (pflow P Q t x), ⟨pflow P Q t x, rfl⟩⟩ : pairDom Hs Ks DA DB)⟩

@[simp] theorem porbit_coe (x : DA ⊗[ℂ] DB) (t : ℝ) :
    ((porbit P Q x t : cpairDom Hs Ks DA DB) : ctensor Hs Ks)
      = pairEmb Hs Ks (inclPair Hs Ks DA DB (pflow P Q t x)) := rfl

theorem porbit_zero (x : DA ⊗[ℂ] DB) :
    ((porbit P Q x 0 : cpairDom Hs Ks DA DB) : ctensor Hs Ks)
      = pairEmb Hs Ks (inclPair Hs Ks DA DB x) := by
  rw [porbit_coe, pflow_zero_time]

theorem norm_porbit (x : DA ⊗[ℂ] DB) (t : ℝ) :
    ‖((porbit P Q x t : cpairDom Hs Ks DA DB) : ctensor Hs Ks)‖
      = ‖((porbit P Q x 0 : cpairDom Hs Ks DA DB) : ctensor Hs Ks)‖ := by
  rw [porbit_coe, porbit_zero, (pairEmb Hs Ks).norm_map, (pairEmb Hs Ks).norm_map,
    (inclPair Hs Ks DA DB).norm_map, (inclPair Hs Ks DA DB).norm_map, norm_pflow]

theorem hasDerivAt_porbit (x : DA ⊗[ℂ] DB) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ((porbit P Q x s : cpairDom Hs Ks DA DB) : ctensor Hs Ks))
      ((-Complex.I) • cpairOp Hs Ks DA DB A B (porbit P Q x t)) t := by
  have h := hasDerivAt_pflow P Q x t
  have hcomp := (((pairEmb Hs Ks).toContinuousLinearMap.restrictScalars
    ℝ).hasFDerivAt).comp_hasDerivAt t h
  have hop : cpairOp Hs Ks DA DB A B (porbit P Q x t)
      = pairEmb Hs Ks (sumPoly Hs Ks DA DB A B (pflow P Q t x)) :=
    cpairOp_apply Hs Ks DA DB A B (porbit P Q x t) (pflow P Q t x) rfl
  rw [hop]
  have hval : (ContinuousLinearMap.restrictScalars ℝ (pairEmb Hs Ks).toContinuousLinearMap)
      ((-Complex.I) • sumPoly Hs Ks DA DB A B (pflow P Q t x))
      = (-Complex.I) • pairEmb Hs Ks (sumPoly Hs Ks DA DB A B (pflow P Q t x)) := by
    simp
  rw [hval] at hcomp
  exact hcomp

include P Q in
/-- **The tensor sum is essentially self-adjoint** on the algebraic tensor product of the two
domains, inside the completed tensor product, as soon as each factor carries a unitary flow
and each domain is dense. -/
theorem essentiallySelfAdjointOn_cpairDom_flow
    (hA : Dense (DA : Set Hs.carrier)) (hB : Dense (DB : Set Ks.carrier)) :
    EssentiallySelfAdjointOn (cpairDom Hs Ks DA DB) (cpairOp Hs Ks DA DB A B) := by
  have hrange : (Set.range fun x : DA ⊗[ℂ] DB =>
      ((porbit P Q x 0 : cpairDom Hs Ks DA DB) : ctensor Hs Ks))
      = ((cpairDom Hs Ks DA DB : Submodule ℂ (ctensor Hs Ks)) : Set (ctensor Hs Ks)) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact (porbit P Q x 0).2
    · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
      refine ⟨x, ?_⟩
      exact porbit_zero P Q x
  have hdense : Dense ((Submodule.span ℂ (Set.range fun x : DA ⊗[ℂ] DB =>
      ((porbit P Q x 0 : cpairDom Hs Ks DA DB) : ctensor Hs Ks)) :
      Submodule ℂ (ctensor Hs Ks)) : Set (ctensor Hs Ks)) := by
    rw [hrange, Submodule.span_eq]
    exact dense_cpairDom Hs Ks DA DB hA hB
  exact essentiallySelfAdjointOn_of_orbits _ (fun x => porbit P Q x)
    (fun x t => norm_porbit P Q x t) (fun x t => hasDerivAt_porbit P Q x t) hdense

end Flow

/-! ## 5. Two self-adjoint operators -/

section SelfAdjoint

variable {Hs Ks : IPSpace} [CompleteSpace Hs.carrier] [CompleteSpace Ks.carrier]

/-- **The tensor sum of two self-adjoint operators is essentially self-adjoint** on the
algebraic tensor product of their domains. -/
theorem essentiallySelfAdjointOn_cpairDom_selfAdjoint (T : UnboundedSelfAdjoint Hs.carrier)
    (S : UnboundedSelfAdjoint Ks.carrier) :
    EssentiallySelfAdjointOn (cpairDom Hs Ks T.domain S.domain)
      (cpairOp Hs Ks T.domain S.domain T.op S.op) :=
  essentiallySelfAdjointOn_cpairDom_flow (ofSelfAdjoint T) (ofSelfAdjoint S) T.denseDomain
    S.denseDomain

end SelfAdjoint

/-! ## 6. The two-factor core estimate -/

section Core

variable (Hs Ks : IPSpace) (DA : Submodule ℂ Hs.carrier) (DB : Submodule ℂ Ks.carrier)
  (A : DA →ₗ[ℂ] Hs.carrier) (B : DB →ₗ[ℂ] Ks.carrier)
  (CA : Submodule ℂ Hs.carrier) (CB : Submodule ℂ Ks.carrier)

/-- The algebraic tensor product `C_A ⊗ C_B` of the two cores, inside `D_A ⊗ D_B`. -/
def pairCorePoly : Submodule ℂ (DA ⊗[ℂ] DB) :=
  Submodule.span ℂ
    {t | ∃ a : DA, (a : Hs.carrier) ∈ CA ∧ ∃ b : DB, (b : Ks.carrier) ∈ CB ∧ a ⊗ₜ[ℂ] b = t}

theorem tmul_mem_pairCorePoly {a : DA} (ha : (a : Hs.carrier) ∈ CA) {b : DB}
    (hb : (b : Ks.carrier) ∈ CB) : a ⊗ₜ[ℂ] b ∈ pairCorePoly Hs Ks DA DB CA CB :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

/-- The graph map `x ↦ (x, (A ⊗ 1 + 1 ⊗ B) x)`. -/
def graphPair :
    (DA ⊗[ℂ] DB) →ₗ[ℂ] (Hs.carrier ⊗[ℂ] Ks.carrier) × (Hs.carrier ⊗[ℂ] Ks.carrier) :=
  (inclPair Hs Ks DA DB).toLinearMap.prod (sumPoly Hs Ks DA DB A B)

@[simp] theorem graphPair_apply (x : DA ⊗[ℂ] DB) :
    graphPair Hs Ks DA DB A B x
      = (inclPair Hs Ks DA DB x, sumPoly Hs Ks DA DB A B x) := rfl

/-- **The two-factor telescoping estimate**, at an elementary tensor: moving each factor into
its core costs its own graph distance, and the two costs add. -/
theorem graphPair_tmul_mem_closure (hcoreA : IsGraphCore CA A) (hcoreB : IsGraphCore CB B)
    (a : DA) (b : DB) :
    graphPair Hs Ks DA DB A B (a ⊗ₜ[ℂ] b) ∈
      (Submodule.map (graphPair Hs Ks DA DB A B)
        (pairCorePoly Hs Ks DA DB CA CB)).topologicalClosure := by
  change graphPair Hs Ks DA DB A B (a ⊗ₜ[ℂ] b) ∈
    closure ((Submodule.map (graphPair Hs Ks DA DB A B)
      (pairCorePoly Hs Ks DA DB CA CB)) : Set _)
  refine Metric.mem_closure_iff.mpr ?_
  intro ε hε
  set na : ℝ := ‖(a : Hs.carrier)‖ with hna
  set nAa : ℝ := ‖A a‖ with hnAa
  set nb : ℝ := ‖(b : Ks.carrier)‖ with hnb
  set nBb : ℝ := ‖B b‖ with hnBb
  set C : ℝ := na + nAa + nb + nBb + 4 with hC
  have hna0 : 0 ≤ na := norm_nonneg _
  have hnAa0 : 0 ≤ nAa := norm_nonneg _
  have hnb0 : 0 ≤ nb := norm_nonneg _
  have hnBb0 : 0 ≤ nBb := norm_nonneg _
  have hCpos : 0 < C := by rw [hC]; linarith
  set δ : ℝ := min 1 (ε / (2 * C)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδone : δ ≤ 1 := min_le_left _ _
  have hδC : δ * C < ε := by
    have h1 : δ ≤ ε / (2 * C) := min_le_right _ _
    have h2 : δ * C ≤ (ε / (2 * C)) * C := mul_le_mul_of_nonneg_right h1 hCpos.le
    have h3 : (ε / (2 * C)) * C = ε / 2 := by field_simp
    rw [h3] at h2
    linarith
  obtain ⟨a', ha'C, ha'₁, ha'₂⟩ := hcoreA a δ hδpos
  obtain ⟨b', hb'C, hb'₁, hb'₂⟩ := hcoreB b δ hδpos
  have ha'norm : ‖(a' : Hs.carrier)‖ ≤ na + δ := by
    have h1 := norm_sub_norm_le (a' : Hs.carrier) (a : Hs.carrier)
    have h2 : ‖(a' : Hs.carrier) - (a : Hs.carrier)‖ < δ := by rw [norm_sub_rev]; exact ha'₁
    rw [hna]; linarith
  have hAa'norm : ‖A a'‖ ≤ nAa + δ := by
    have h1 := norm_sub_norm_le (A a') (A a)
    have h2 : ‖A a' - A a‖ < δ := by rw [norm_sub_rev]; exact ha'₂
    rw [hnAa]; linarith
  refine ⟨graphPair Hs Ks DA DB A B (a' ⊗ₜ[ℂ] b'),
    ⟨a' ⊗ₜ[ℂ] b', tmul_mem_pairCorePoly Hs Ks DA DB CA CB ha'C hb'C, rfl⟩, ?_⟩
  have hmove₁ : ‖(a : Hs.carrier) ⊗ₜ[ℂ] (b : Ks.carrier)
        - (a' : Hs.carrier) ⊗ₜ[ℂ] (b' : Ks.carrier)‖ ≤ δ * nb + (na + δ) * δ := by
    refine le_trans (TensorCore.norm_tmul_sub_le (a : Hs.carrier) (a' : Hs.carrier)
      (b : Ks.carrier) (b' : Ks.carrier)) ?_
    refine add_le_add (mul_le_mul_of_nonneg_right ha'₁.le hnb0) ?_
    exact mul_le_mul ha'norm hb'₁.le (norm_nonneg _) (by linarith)
  have hmove₂ : ‖(A a) ⊗ₜ[ℂ] (b : Ks.carrier) - (A a') ⊗ₜ[ℂ] (b' : Ks.carrier)‖
      ≤ δ * nb + (nAa + δ) * δ := by
    refine le_trans (TensorCore.norm_tmul_sub_le (A a) (A a') (b : Ks.carrier)
      (b' : Ks.carrier)) ?_
    refine add_le_add (mul_le_mul_of_nonneg_right ha'₂.le hnb0) ?_
    exact mul_le_mul hAa'norm hb'₁.le (norm_nonneg _) (by linarith)
  have hmove₃ : ‖(a : Hs.carrier) ⊗ₜ[ℂ] (B b) - (a' : Hs.carrier) ⊗ₜ[ℂ] (B b')‖
      ≤ δ * nBb + (na + δ) * δ := by
    refine le_trans (TensorCore.norm_tmul_sub_le (a : Hs.carrier) (a' : Hs.carrier) (B b)
      (B b')) ?_
    refine add_le_add (mul_le_mul_of_nonneg_right ha'₁.le hnBb0) ?_
    exact mul_le_mul ha'norm hb'₂.le (norm_nonneg _) (by linarith)
  have hbudget₁ : δ * nb + (na + δ) * δ ≤ δ * C := by
    have hfac : δ * C - (δ * nb + (na + δ) * δ) = δ * (nAa + nBb + 4 - δ) := by rw [hC]; ring
    have hnn : 0 ≤ δ * (nAa + nBb + 4 - δ) := mul_nonneg hδpos.le (by linarith)
    linarith
  have hbudget₂ : (δ * nb + (nAa + δ) * δ) + (δ * nBb + (na + δ) * δ) ≤ δ * C := by
    have hfac : δ * C - ((δ * nb + (nAa + δ) * δ) + (δ * nBb + (na + δ) * δ))
        = 2 * (δ * (2 - δ)) := by rw [hC]; ring
    have hnn : 0 ≤ 2 * (δ * (2 - δ)) := by
      have : 0 ≤ δ * (2 - δ) := mul_nonneg hδpos.le (by linarith)
      linarith
    linarith
  rw [Prod.dist_eq]
  refine max_lt ?_ ?_
  · rw [dist_eq_norm]
    have hcomp : (graphPair Hs Ks DA DB A B (a ⊗ₜ[ℂ] b)).1
        - (graphPair Hs Ks DA DB A B (a' ⊗ₜ[ℂ] b')).1
        = (a : Hs.carrier) ⊗ₜ[ℂ] (b : Ks.carrier)
          - (a' : Hs.carrier) ⊗ₜ[ℂ] (b' : Ks.carrier) := rfl
    rw [hcomp]
    linarith
  · rw [dist_eq_norm]
    have hcomp : (graphPair Hs Ks DA DB A B (a ⊗ₜ[ℂ] b)).2
        - (graphPair Hs Ks DA DB A B (a' ⊗ₜ[ℂ] b')).2
        = ((A a) ⊗ₜ[ℂ] (b : Ks.carrier) - (A a') ⊗ₜ[ℂ] (b' : Ks.carrier))
          + ((a : Hs.carrier) ⊗ₜ[ℂ] (B b) - (a' : Hs.carrier) ⊗ₜ[ℂ] (B b')) := by
      change ((A a) ⊗ₜ[ℂ] (b : Ks.carrier) + (a : Hs.carrier) ⊗ₜ[ℂ] (B b))
          - ((A a') ⊗ₜ[ℂ] (b' : Ks.carrier) + (a' : Hs.carrier) ⊗ₜ[ℂ] (B b')) = _
      abel
    rw [hcomp]
    refine lt_of_le_of_lt (norm_add_le _ _) ?_
    linarith

/-- The graph of the tensor sum is the closure of the graph of its restriction to the tensor
product of the two cores. -/
theorem graphPair_range_le_closure (hcoreA : IsGraphCore CA A) (hcoreB : IsGraphCore CB B) :
    LinearMap.range (graphPair Hs Ks DA DB A B)
      ≤ (Submodule.map (graphPair Hs Ks DA DB A B)
        (pairCorePoly Hs Ks DA DB CA CB)).topologicalClosure := by
  rintro y ⟨x, rfl⟩
  induction (mem_span_tmul x) using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨p, q, rfl⟩ := ht
      exact graphPair_tmul_mem_closure Hs Ks DA DB A B CA CB hcoreA hcoreB p q
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add s t _ _ hs ht => simpa [map_add] using Submodule.add_mem _ hs ht
  | smul c s _ hs => simpa [map_smul] using Submodule.smul_mem _ c hs

/-- **The two-factor core estimate.**  If `C_A` is a core for `A` and `C_B` is a core for `B`,
then `C_A ⊗ C_B` is a core for the tensor sum. -/
theorem exists_pair_core_approx (hcoreA : IsGraphCore CA A) (hcoreB : IsGraphCore CB B)
    (x : DA ⊗[ℂ] DB) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ pairCorePoly Hs Ks DA DB CA CB,
      ‖inclPair Hs Ks DA DB x - inclPair Hs Ks DA DB y‖ < ε ∧
        ‖sumPoly Hs Ks DA DB A B x - sumPoly Hs Ks DA DB A B y‖ < ε := by
  have hmem : graphPair Hs Ks DA DB A B x ∈
      closure ((Submodule.map (graphPair Hs Ks DA DB A B)
        (pairCorePoly Hs Ks DA DB CA CB)) : Set _) :=
    graphPair_range_le_closure Hs Ks DA DB A B CA CB hcoreA hcoreB ⟨x, rfl⟩
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨y, hy, rfl⟩ := hz
  refine ⟨y, hy, ?_, ?_⟩
  · have := (max_lt_iff.mp (by simpa [Prod.dist_eq, dist_eq_norm] using hdist)).1
    simpa using this
  · have := (max_lt_iff.mp (by simpa [Prod.dist_eq, dist_eq_norm] using hdist)).2
    simpa using this

/-- The image of `C_A ⊗ C_B` inside `H ⊗ K`. -/
def pairCore : Submodule ℂ (Hs.carrier ⊗[ℂ] Ks.carrier) :=
  Submodule.map (inclPair Hs Ks DA DB).toLinearMap (pairCorePoly Hs Ks DA DB CA CB)

theorem pairCore_le_pairDom : pairCore Hs Ks DA DB CA CB ≤ pairDom Hs Ks DA DB := by
  rintro x ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

/-- The image of `C_A ⊗ C_B` in the completed tensor product. -/
def cpairCore : Submodule ℂ (ctensor Hs Ks) :=
  pushDom (pairEmb Hs Ks) (pairCore Hs Ks DA DB CA CB)

theorem cpairCore_le_cpairDom : cpairCore Hs Ks DA DB CA CB ≤ cpairDom Hs Ks DA DB :=
  pushDom_mono (pairEmb Hs Ks) (pairCore_le_pairDom Hs Ks DA DB CA CB)

/-- The core estimate in the form used by the transfer principle. -/
theorem isGraphCore_pairCore (hcoreA : IsGraphCore CA A) (hcoreB : IsGraphCore CB B) :
    IsGraphCore (pairCore Hs Ks DA DB CA CB) (pairOp Hs Ks DA DB A B) := by
  intro x ε hε
  obtain ⟨x₀, hx₀⟩ := x.2
  have hx : (x : Hs.carrier ⊗[ℂ] Ks.carrier) = inclPair Hs Ks DA DB x₀ := hx₀.symm
  obtain ⟨y₀, hy₀, hy₁, hy₂⟩ :=
    exists_pair_core_approx Hs Ks DA DB A B CA CB hcoreA hcoreB x₀ hε
  refine ⟨⟨inclPair Hs Ks DA DB y₀, ⟨y₀, rfl⟩⟩, ⟨y₀, hy₀, rfl⟩, ?_, ?_⟩
  · simpa [hx] using hy₁
  · rw [pairOp_apply Hs Ks DA DB A B x x₀ hx,
      pairOp_apply Hs Ks DA DB A B ⟨inclPair Hs Ks DA DB y₀, ⟨y₀, rfl⟩⟩ y₀ rfl]
    exact hy₂

/-- The same, in the completed tensor product. -/
theorem isGraphCore_cpairCore (hcoreA : IsGraphCore CA A) (hcoreB : IsGraphCore CB B) :
    IsGraphCore (cpairCore Hs Ks DA DB CA CB) (cpairOp Hs Ks DA DB A B) :=
  isGraphCore_pushOp (pairEmb Hs Ks) (pairOp Hs Ks DA DB A B)
    (isGraphCore_pairCore Hs Ks DA DB A B CA CB hcoreA hcoreB)

/-- **Essential self-adjointness descends to the tensor product of two cores.** -/
theorem essentiallySelfAdjointOn_cpairCore (hcoreA : IsGraphCore CA A)
    (hcoreB : IsGraphCore CB B)
    (hesa : EssentiallySelfAdjointOn (cpairDom Hs Ks DA DB) (cpairOp Hs Ks DA DB A B)) :
    EssentiallySelfAdjointOn (cpairCore Hs Ks DA DB CA CB)
      (restrictOp (cpairOp Hs Ks DA DB A B) (cpairCore_le_cpairDom Hs Ks DA DB CA CB)) :=
  essentiallySelfAdjointOn_of_graphCore _ _
    (isGraphCore_cpairCore Hs Ks DA DB A B CA CB hcoreA hcoreB) hesa

end Core

/-! ## 7. Two self-adjoint operators and two cores -/

section SelfAdjointCore

variable {Hs Ks : IPSpace} [CompleteSpace Hs.carrier] [CompleteSpace Ks.carrier]

/-- **The tensor sum on a product of cores.**  For self-adjoint `A` and `B` and graph-norm
cores `C_A` of `A` and `C_B` of `B`, the tensor sum `A ⊗ 1 + 1 ⊗ B` is essentially
self-adjoint on `C_A ⊗ C_B`. -/
theorem essentiallySelfAdjointOn_cpairCore_selfAdjoint (T : UnboundedSelfAdjoint Hs.carrier)
    (S : UnboundedSelfAdjoint Ks.carrier) (CA : Submodule ℂ Hs.carrier)
    (CB : Submodule ℂ Ks.carrier) (hcoreA : IsGraphCore CA T.op)
    (hcoreB : IsGraphCore CB S.op) :
    EssentiallySelfAdjointOn (cpairCore Hs Ks T.domain S.domain CA CB)
      (restrictOp (cpairOp Hs Ks T.domain S.domain T.op S.op)
        (cpairCore_le_cpairDom Hs Ks T.domain S.domain CA CB)) :=
  essentiallySelfAdjointOn_cpairCore Hs Ks T.domain S.domain T.op S.op CA CB hcoreA hcoreB
    (essentiallySelfAdjointOn_cpairDom_selfAdjoint T S)

end SelfAdjointCore

/-! ## 8. Two merely essentially self-adjoint operators -/

section Esa

variable {Hs Ks : IPSpace}

/-- A vector of the tensor product of the two small domains, viewed inside the tensor product
of the two large ones, comes from the small tensor product with the same image and the same
value of the tensor sum — because the large operators extend the small ones. -/
theorem exists_pair_of_mem_pairCorePoly {DA' : Submodule ℂ Hs.carrier}
    {DB' : Submodule ℂ Ks.carrier} (A' : DA' →ₗ[ℂ] Hs.carrier) (B' : DB' →ₗ[ℂ] Ks.carrier)
    {DA : Submodule ℂ Hs.carrier} {DB : Submodule ℂ Ks.carrier} (A : DA →ₗ[ℂ] Hs.carrier)
    (B : DB →ₗ[ℂ] Ks.carrier) (hleA : DA ≤ DA') (hleB : DB ≤ DB')
    (hextA : ∀ v : DA, A' ⟨(v : Hs.carrier), hleA v.2⟩ = A v)
    (hextB : ∀ v : DB, B' ⟨(v : Ks.carrier), hleB v.2⟩ = B v)
    (y : DA' ⊗[ℂ] DB') (hy : y ∈ pairCorePoly Hs Ks DA' DB' DA DB) :
    ∃ y' : DA ⊗[ℂ] DB,
      inclPair Hs Ks DA DB y' = inclPair Hs Ks DA' DB' y ∧
        sumPoly Hs Ks DA DB A B y' = sumPoly Hs Ks DA' DB' A' B' y := by
  induction hy using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨a, haD, b, hbD, rfl⟩ := ht
      refine ⟨(⟨(a : Hs.carrier), haD⟩ : DA) ⊗ₜ[ℂ] (⟨(b : Ks.carrier), hbD⟩ : DB), rfl, ?_⟩
      have hA : A' a = A ⟨(a : Hs.carrier), haD⟩ := by
        have := hextA ⟨(a : Hs.carrier), haD⟩
        simpa using this
      have hB : B' b = B ⟨(b : Ks.carrier), hbD⟩ := by
        exact hextB ⟨(b : Ks.carrier), hbD⟩
      simp [sumPoly_tmul, hA, hB]
  | zero => exact ⟨0, by simp [inclPair, map_zero], by simp [map_zero]⟩
  | add s t _ _ hs ht =>
      obtain ⟨s', hs₁, hs₂⟩ := hs
      obtain ⟨t', ht₁, ht₂⟩ := ht
      exact ⟨s' + t', by rw [map_add, map_add, hs₁, ht₁], by rw [map_add, map_add, hs₂, ht₂]⟩
  | smul c s _ hs =>
      obtain ⟨s', hs₁, hs₂⟩ := hs
      exact ⟨c • s', by rw [map_smul, map_smul, hs₁], by rw [map_smul, map_smul, hs₂]⟩

variable [CompleteSpace Hs.carrier] [CompleteSpace Ks.carrier]

/-- **The tensor sum of two essentially self-adjoint operators.**  Let `A` be symmetric and
essentially self-adjoint on the dense domain `D_A` of `H`, and `B` symmetric and essentially
self-adjoint on the dense domain `D_B` of `K`.  Then `A ⊗ 1 + 1 ⊗ B` is essentially
self-adjoint on `D_A ⊗ D_B` in the completed tensor product `H ⊗̂ K`.  No self-adjointness,
no semiboundedness and no relative bound is assumed. -/
theorem essentiallySelfAdjointOn_cpairDom_esa {DA : Submodule ℂ Hs.carrier}
    {DB : Submodule ℂ Ks.carrier} (A : DA →ₗ[ℂ] Hs.carrier) (B : DB →ₗ[ℂ] Ks.carrier)
    (hdenseA : Dense (DA : Set Hs.carrier)) (hdenseB : Dense (DB : Set Ks.carrier))
    (hsymA : SymmetricOn DA A) (hsymB : SymmetricOn DB B)
    (hesaA : EssentiallySelfAdjointOn DA A) (hesaB : EssentiallySelfAdjointOn DB B) :
    EssentiallySelfAdjointOn (cpairDom Hs Ks DA DB) (cpairOp Hs Ks DA DB A B) := by
  set A' := clExt A hdenseA hsymA with hA'
  set B' := clExt B hdenseB hsymB with hB'
  have hcoreA : IsGraphCore DA A' := isGraphCore_clDom A hdenseA hsymA
  have hcoreB : IsGraphCore DB B' := isGraphCore_clDom B hdenseB hsymB
  have hbig : EssentiallySelfAdjointOn (cpairDom Hs Ks (clDom A) (clDom B))
      (cpairOp Hs Ks (clDom A) (clDom B) A' B') :=
    essentiallySelfAdjointOn_cpairDom_selfAdjoint
      (closureSelfAdjoint A hdenseA hsymA hesaA) (closureSelfAdjoint B hdenseB hsymB hesaB)
  have hsource : EssentiallySelfAdjointOn (cpairCore Hs Ks (clDom A) (clDom B) DA DB)
      (restrictOp (cpairOp Hs Ks (clDom A) (clDom B) A' B')
        (cpairCore_le_cpairDom Hs Ks (clDom A) (clDom B) DA DB)) :=
    essentiallySelfAdjointOn_cpairCore Hs Ks (clDom A) (clDom B) A' B' DA DB hcoreA hcoreB hbig
  refine esa_graph_le ?_ hsource
  rintro ⟨v, hv⟩
  obtain ⟨w, hwmem, hwv⟩ := hv
  obtain ⟨y, hy, hyw⟩ := hwmem
  obtain ⟨y', hy₁, hy₂⟩ := exists_pair_of_mem_pairCorePoly A' B' A B (le_clDom A) (le_clDom B)
    (fun v => clExt_extends A hdenseA hsymA v) (fun v => clExt_extends B hdenseB hsymB v) y hy
  have hvy : v = pairEmb Hs Ks (inclPair Hs Ks (clDom A) (clDom B) y) := by
    have hy'' : pairEmb Hs Ks (inclPair Hs Ks (clDom A) (clDom B) y) = v := by
      rw [show inclPair Hs Ks (clDom A) (clDom B) y = w from hyw]
      exact hwv
    exact hy''.symm
  have hvval : v = pairEmb Hs Ks (inclPair Hs Ks DA DB y') := by
    rw [hy₁]
    exact hvy
  refine ⟨⟨pairEmb Hs Ks (inclPair Hs Ks DA DB y'),
    mem_pushDom (pairEmb Hs Ks)
      (⟨inclPair Hs Ks DA DB y', ⟨y', rfl⟩⟩ : pairDom Hs Ks DA DB)⟩, hvval.symm, ?_⟩
  rw [cpairOp_apply Hs Ks DA DB A B _ y' rfl, hy₂]
  exact (cpairOp_apply Hs Ks (clDom A) (clDom B) A' B' _ y hvy).symm

end Esa

/-! ## 9. The unitary flow -/

section StoneFlow

open BookProof.StoneBridge

variable {Hs Ks : IPSpace} [CompleteSpace Hs.carrier] [CompleteSpace Ks.carrier]

/-- **The unitary flow of the tensor sum of two self-adjoint operators.**  The tensor sum has
a self-adjoint extension on the completed tensor product, and that extension generates a
complete unitary group solving the Schrödinger equation. -/
theorem tensorSum_stone_flow (T : UnboundedSelfAdjoint Hs.carrier)
    (S : UnboundedSelfAdjoint Ks.carrier) :
    ∃ (G : UnboundedSelfAdjoint (ctensor Hs Ks))
      (U : ℝ → (ctensor Hs Ks →L[ℂ] ctensor Hs Ks)),
      IsSelfAdjointExtension (cpairOp Hs Ks T.domain S.domain T.op S.op) G.op ∧
        IsStoneFlow G U :=
  exists_stone_flow_of_esa _
    (dense_cpairDom Hs Ks T.domain S.domain T.denseDomain S.denseDomain)
    (symmetricOn_cpairOp Hs Ks T.domain S.domain T.op S.op T.symmetric S.symmetric)
    (essentiallySelfAdjointOn_cpairDom_selfAdjoint T S)

/-- The same for two merely essentially self-adjoint operators. -/
theorem tensorSum_stone_flow_esa {DA : Submodule ℂ Hs.carrier} {DB : Submodule ℂ Ks.carrier}
    (A : DA →ₗ[ℂ] Hs.carrier) (B : DB →ₗ[ℂ] Ks.carrier)
    (hdenseA : Dense (DA : Set Hs.carrier)) (hdenseB : Dense (DB : Set Ks.carrier))
    (hsymA : SymmetricOn DA A) (hsymB : SymmetricOn DB B)
    (hesaA : EssentiallySelfAdjointOn DA A) (hesaB : EssentiallySelfAdjointOn DB B) :
    ∃ (G : UnboundedSelfAdjoint (ctensor Hs Ks))
      (U : ℝ → (ctensor Hs Ks →L[ℂ] ctensor Hs Ks)),
      IsSelfAdjointExtension (cpairOp Hs Ks DA DB A B) G.op ∧ IsStoneFlow G U :=
  exists_stone_flow_of_esa _ (dense_cpairDom Hs Ks DA DB hdenseA hdenseB)
    (symmetricOn_cpairOp Hs Ks DA DB A B hsymA hsymB)
    (essentiallySelfAdjointOn_cpairDom_esa A B hdenseA hdenseB hsymA hsymB hesaA hesaB)

end StoneFlow

/-! ## 10. A genuinely unbounded instance -/

section Instance

open BookProof.ChapterStoneSeparable BookProof.ChapterUnboundedPosition

/-- Multiplication by `k³` on `ℓ²(ℤ)`. -/
def cubeField : ℤ → ℝ := fun k => (k : ℝ) ^ 3

/-- **A concrete tensor sum of two different unbounded operators.**  On the completed tensor
product of `ℓ²(ℤ)` with itself, the operator `k ⊗ 1 + 1 ⊗ k³` — the sum of multiplication
by `k` in the first factor and multiplication by `k³` in the second — is essentially
self-adjoint on the algebraic tensor product of the two maximal multiplication domains. -/
theorem positionCube_essentiallySelfAdjoint :
    EssentiallySelfAdjointOn
      (cpairDom L2ZSpace L2ZSpace (mulSA positionField).domain (mulSA cubeField).domain)
      (cpairOp L2ZSpace L2ZSpace (mulSA positionField).domain (mulSA cubeField).domain
        (mulSA positionField).op (mulSA cubeField).op) :=
  essentiallySelfAdjointOn_cpairDom_selfAdjoint (Hs := L2ZSpace) (Ks := L2ZSpace)
    (mulSA positionField) (mulSA cubeField)

/-- The first factor of the previous theorem is a genuinely unbounded operator. -/
theorem positionCube_first_not_bounded :
    ¬ ∃ C : ℝ, ∀ x : (mulSA positionField).domain,
      ‖(mulSA positionField).op x‖ ≤ C * ‖(x : BookProof.ChapterContinuityUnitaryInfinite.L2Z)‖ :=
  BookProof.ChapterStoneSeparable.mulSA_position_unbounded

end Instance

end

end BookProof.TensorSumEsa


