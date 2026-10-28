-- Prove2me | Definitions.Def_ChapterEsaPairDGamma
-- name    : ChapterEsaPairDGamma
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T04:56:32.734157+00:00
-- url     : https://prove2.me/theorems/efb1370e-798e-4b12-bd1e-3c7dbb8177fa
-- title:
--   Chapter EsaPairDGamma
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterEsaPairDGamma.lean`): generated def bundle for ChapterEsaPairDGamma. See BookProof/ChapterEsaPairDGamma.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterEsaPairDGamma.lean

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterScalarDGammaEsa
import Mathlib
import Theorems.Thm_BookProof_GraphCore_pushOp_apply
import Theorems.Thm_BookProof_GraphCore_essentiallySelfAdjointOn_of_bounded_dense
import Theorems.Thm_BookProof_SecondQuantizationCore_dGamma_essentiallySelfAdjointOn_fockCore
import Theorems.Thm_BookProof_SecondQuantizationCore_symmetricOn_fockSectorOp
import Theorems.Thm_BookProof_ScalarDGamma_dense_fockSectorDom


/-!
# The essentially-self-adjoint one-particle package, and `dΓ` over it

This module packages the data of the second quantization theorem in the form in which the
hypothesis "`A` is **essentially** self-adjoint on `D`" is naturally supplied: a symmetric
operator `A` on the domain `D₂` of its closure, together with a subspace `D ≤ D₂` which is a
**core** — graph-norm dense in `D₂`.  The operator one is really given is the restriction
`A|_D`; the pair records the ambient operator through which it is analysed.

**No positivity anywhere.**  Nothing in the package or in its consequences asks for a lower
bound on the spectrum: the only quantitative facts used are the graph norm `‖x‖ + ‖A x‖` and
the Pythagoras identity `‖A x - d i x‖² = ‖A x‖² + d² ‖x‖²`, valid for *every* symmetric
operator (`BookProof.FarisLavine.norm_sub_smul_sq`, recorded here as
`ESAPair.norm_sub_smul_sq`).  The imaginary shift `± i` is what makes `A ± i` bounded below,
irrespective of the sign of the spectrum, so operators unbounded below — the momentum
operator, a Dirac operator, or simply `-id` — are covered on the same footing as positive
ones.  In particular no quadratic form domain and no Friedrichs extension appear.

## Contents

* `ESAPair` — the package: a symmetric one-particle operator, its sectorwise input, and a
  graph-norm core;
* `ESAPair.toOp` — the operator actually given, the restriction to the core;
* `ESAPair.norm_sub_smul_sq` — the Pythagoras identity, valid with no semiboundedness;
* `ESAPair.dGammaOp` — the second quantization on the finite-particle domain over the core;
* `ESAPair.dGamma_essentiallySelfAdjoint` — **the main theorem** in packaged form;
* `ESAPair.dGamma_symmetricOn`, `ESAPair.exists_ne_zero_mem_domain` — symmetry and
  non-vacuity;
* `ESAPair.ofBounded` — a package for every bounded symmetric one-particle operator and every
  dense core, with no positivity: by
  `BookProof.BoundedDGamma.essentiallySelfAdjointOn_fockSectorDom_bounded` its sectorwise
  input is proved, not assumed.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.TensorOpBound

open scoped TensorProduct

variable {E E' F F' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-! ## Orthonormal representation of a tensor -/

/-- **Pythagoras in a tensor product.**  If the right legs `e i` form an orthonormal family,
the squared norm of `∑ i, x i ⊗ₜ e i` is `∑ i ‖x i‖²`. -/
theorem norm_sum_tmul_orthonormal {m : ℕ} (x : Fin m → E) (e : Fin m → F)
    (he : Orthonormal ℂ e) :
    ‖(∑ i, x i ⊗ₜ[ℂ] e i : E ⊗[ℂ] F)‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  have hinner : (inner ℂ (∑ i, x i ⊗ₜ[ℂ] e i : E ⊗[ℂ] F) (∑ j, x j ⊗ₜ[ℂ] e j) : ℂ)
      = ∑ i, (inner ℂ (x i) (x i) : ℂ) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [inner_sum, Finset.sum_eq_single i]
    · simp [he.1 i]
    · intro j _ hji
      rw [TensorProduct.inner_tmul, he.2 (Ne.symm hji)]
      ring
    · intro h; simp at h
  have h1 : ‖(∑ i, x i ⊗ₜ[ℂ] e i : E ⊗[ℂ] F)‖ ^ 2
      = (RCLike.re (inner ℂ (∑ i, x i ⊗ₜ[ℂ] e i : E ⊗[ℂ] F) (∑ i, x i ⊗ₜ[ℂ] e i) : ℂ)) := by
    exact (inner_self_eq_norm_sq _).symm
  rw [h1, hinner, map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [inner_self_eq_norm_sq])

/-- **Every tensor has an orthonormal representation.**  Any `u : E ⊗[ℂ] F` is a finite sum
`∑ i, x i ⊗ₜ e i` whose right legs form an orthonormal family. -/
theorem exists_orthonormal_repr (u : E ⊗[ℂ] F) :
    ∃ (m : ℕ) (x : Fin m → E) (e : Fin m → F), Orthonormal ℂ e ∧ u = ∑ i, x i ⊗ₜ[ℂ] e i := by
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset u
  set W : Submodule ℂ F := Submodule.span ℂ ((S.image Prod.snd : Finset F) : Set F) with hW
  have hfd : FiniteDimensional ℂ W := by
    rw [hW]; exact FiniteDimensional.span_finset ℂ _
  set b := stdOrthonormalBasis ℂ W with hb
  have hmem : ∀ p ∈ S, p.2 ∈ W := by
    intro p hp
    refine Submodule.subset_span ?_
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Prod.exists, exists_eq_right]
    exact ⟨p.1, hp⟩
  have hrepr : ∀ p ∈ S, ∑ i, (inner ℂ ((b i : F)) p.2 : ℂ) • ((b i : W) : F) = p.2 := by
    intro p hp
    have h := b.sum_repr' (⟨p.2, hmem p hp⟩ : W)
    have h2 := congrArg (fun w : W => (w : F)) h
    simpa using h2
  have hstep : ∑ p ∈ S, p.1 ⊗ₜ[ℂ] p.2
      = ∑ p ∈ S, ∑ i, p.1 ⊗ₜ[ℂ] ((inner ℂ ((b i : F)) p.2 : ℂ) • ((b i : W) : F)) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [← TensorProduct.tmul_sum, hrepr p hp]
  refine ⟨Module.finrank ℂ W, fun i => ∑ p ∈ S, (inner ℂ ((b i : F)) p.2 : ℂ) • p.1,
    fun i => (b i : F), ?_, ?_⟩
  · rw [show (fun i => ((b i : W) : F)) = (W.subtypeₗᵢ ∘ b) from rfl]
    exact (LinearIsometry.orthonormal_comp_iff W.subtypeₗᵢ).mpr b.orthonormal
  · rw [hS, hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-! ## The operator bounds -/

/-- **Bound for an operator acting on the left factor.**  If `‖S a‖ ≤ C ‖a‖` then
`‖(S ⊗ 1) u‖ ≤ C ‖u‖`.  No positivity, no self-adjointness and no completeness is used. -/
theorem norm_map_left_le (S : E →ₗ[ℂ] E') {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ a : E, ‖S a‖ ≤ C * ‖a‖)
    (u : E ⊗[ℂ] F) :
    ‖TensorProduct.map S (LinearMap.id : F →ₗ[ℂ] F) u‖ ≤ C * ‖u‖ := by
  obtain ⟨m, x, e, he, rfl⟩ := exists_orthonormal_repr u
  have himg : TensorProduct.map S (LinearMap.id : F →ₗ[ℂ] F) (∑ i, x i ⊗ₜ[ℂ] e i)
      = ∑ i, (S (x i)) ⊗ₜ[ℂ] e i := by
    rw [map_sum]; simp
  rw [himg]
  have h1 := norm_sum_tmul_orthonormal (fun i => S (x i)) e he
  have h2 := norm_sum_tmul_orthonormal x e he
  have h3 : ∑ i, ‖S (x i)‖ ^ 2 ≤ C ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have := hC (x i)
    nlinarith [norm_nonneg (S (x i)), norm_nonneg (x i)]
  have hsq : ‖(∑ i, (S (x i)) ⊗ₜ[ℂ] e i : E' ⊗[ℂ] F)‖ ^ 2
      ≤ (C * ‖(∑ i, x i ⊗ₜ[ℂ] e i : E ⊗[ℂ] F)‖) ^ 2 := by
    rw [h1, mul_pow, h2]; exact h3
  have hn1 := norm_nonneg (∑ i, (S (x i)) ⊗ₜ[ℂ] e i : E' ⊗[ℂ] F)
  have hn2 := norm_nonneg (∑ i, x i ⊗ₜ[ℂ] e i : E ⊗[ℂ] F)
  nlinarith [mul_nonneg hC0 hn2]

/-- The commutation isometry intertwines an operator on the right factor with the same
operator on the left factor. -/
theorem comm_map_id (T : F →ₗ[ℂ] F') (u : E ⊗[ℂ] F) :
    TensorProduct.comm ℂ E F' (TensorProduct.map LinearMap.id T u)
      = TensorProduct.map T (LinearMap.id : E →ₗ[ℂ] E) (TensorProduct.comm ℂ E F u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add s t hs ht => simp [hs, ht]

/-- **Bound for an operator acting on the right factor.** -/
theorem norm_map_right_le (T : F →ₗ[ℂ] F') {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ b : F, ‖T b‖ ≤ C * ‖b‖)
    (u : E ⊗[ℂ] F) :
    ‖TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T u‖ ≤ C * ‖u‖ := by
  have h1 : ‖TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T u‖
      = ‖TensorProduct.comm ℂ E F' (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T u)‖ := by
    rw [TensorProduct.norm_comm]
  rw [h1, comm_map_id T u]
  have h2 := norm_map_left_le (F := E) T hC0 hC (TensorProduct.comm ℂ E F u)
  rwa [TensorProduct.norm_comm] at h2

/-- **The operator bound on a tensor product.**  For arbitrary bounded (in particular,
possibly indefinite) factors, `‖(S ⊗ T) u‖ ≤ C₁ C₂ ‖u‖`. -/
theorem norm_map_le (S : E →ₗ[ℂ] E') (T : F →ₗ[ℂ] F') {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hS : ∀ a : E, ‖S a‖ ≤ C₁ * ‖a‖) (hT : ∀ b : F, ‖T b‖ ≤ C₂ * ‖b‖) (u : E ⊗[ℂ] F) :
    ‖TensorProduct.map S T u‖ ≤ C₁ * C₂ * ‖u‖ := by
  have hfac : TensorProduct.map S T u
      = TensorProduct.map S (LinearMap.id : F' →ₗ[ℂ] F')
          (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T u) := by
    have : TensorProduct.map S T
        = (TensorProduct.map S (LinearMap.id : F' →ₗ[ℂ] F')) ∘ₗ
          (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T) := by
      rw [← TensorProduct.map_comp]; simp
    exact congrArg (fun L : (E ⊗[ℂ] F) →ₗ[ℂ] (E' ⊗[ℂ] F') => L u) this
  rw [hfac]
  calc ‖TensorProduct.map S (LinearMap.id : F' →ₗ[ℂ] F')
          (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T u)‖
      ≤ C₁ * ‖TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T u‖ :=
        norm_map_left_le S hC₁ hS _
    _ ≤ C₁ * (C₂ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (norm_map_right_le T hC₂ hT u) hC₁
    _ = C₁ * C₂ * ‖u‖ := by ring

end BookProof.TensorOpBound

/-! Inlined from the unpublished `ChapterBoundedDGammaEsa` bundle. -/
namespace BookProof.BoundedDGamma

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.TensorOpBound
  BookProof.SecondQuantizationCore BookProof.DirectSumEsa

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)

/-! ## The sector estimate -/

/-- **The sector estimate.**  If the one-particle operator is bounded by `C`, the `n`-sector
derivation `dΓ(A)⁽ⁿ⁾` is bounded by `n C`.  This is the Leibniz recursion
`dΓ⁽ⁿ⁺¹⁾ = A ⊗ 1 + 1 ⊗ dΓ⁽ⁿ⁾` together with the tensor operator bound; no positivity of `A` is
used, only the norm bound. -/
theorem norm_derPow_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ a : D₂, ‖A a‖ ≤ C * ‖a‖) :
    ∀ (n : ℕ) (x : ((domSpace Hs D₂).pow n)), ‖derPow Hs D₂ A n x‖ ≤ ((n : ℝ) * C) * ‖x‖ := by
  intro n
  induction n with
  | zero => intro x; simp [derPow]
  | succ n ih =>
      intro x
      have hfirst : ‖TensorProduct.map A (inclPow Hs D₂ n).toLinearMap x‖ ≤ C * 1 * ‖x‖ :=
        norm_map_le A (inclPow Hs D₂ n).toLinearMap hC0 zero_le_one hC
          (fun b => le_of_eq (by rw [one_mul]; exact (inclPow Hs D₂ n).norm_map b)) x
      have hsecond : ‖TensorProduct.map D₂.subtype (derPow Hs D₂ A n) x‖
          ≤ 1 * ((n : ℝ) * C) * ‖x‖ :=
        norm_map_le D₂.subtype (derPow Hs D₂ A n) zero_le_one (by positivity)
          (fun a => le_of_eq (by rw [one_mul]; rfl)) ih x
      have hsplit : derPow Hs D₂ A (n + 1) x
          = TensorProduct.map A (inclPow Hs D₂ n).toLinearMap x
            + TensorProduct.map D₂.subtype (derPow Hs D₂ A n) x := rfl
      have hnn : 0 ≤ ‖x‖ := norm_nonneg _
      calc ‖derPow Hs D₂ A (n + 1) x‖ ≤ ‖TensorProduct.map A (inclPow Hs D₂ n).toLinearMap x‖
            + ‖TensorProduct.map D₂.subtype (derPow Hs D₂ A n) x‖ := by
              rw [hsplit]; exact norm_add_le _ _
        _ ≤ C * 1 * ‖x‖ + 1 * ((n : ℝ) * C) * ‖x‖ := add_le_add hfirst hsecond
        _ = (((n : ℕ) + 1 : ℝ) * C) * ‖x‖ := by ring
        _ = ((((n + 1 : ℕ) : ℝ)) * C) * ‖x‖ := by push_cast; ring

/-- The sector estimate inside `H^{⊗n}`. -/
theorem norm_sectorOp_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ a : D₂, ‖A a‖ ≤ C * ‖a‖) (n : ℕ)
    (x : sectorDom Hs D₂ n) :
    ‖sectorOp Hs D₂ A n x‖ ≤ ((n : ℝ) * C) * ‖(x : (Hs.pow n).carrier)‖ := by
  obtain ⟨x₀, hx₀⟩ := x.2
  have hx : (x : (Hs.pow n).carrier) = inclPow Hs D₂ n x₀ := hx₀.symm
  rw [sectorOp_apply Hs D₂ A n x x₀ hx, hx, (inclPow Hs D₂ n).norm_map]
  exact norm_derPow_le Hs D₂ A hC0 hC n x₀

/-- The sector estimate inside the completed sector. -/
theorem norm_fockSectorOp_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ a : D₂, ‖A a‖ ≤ C * ‖a‖) (n : ℕ)
    (x : fockSectorDom Hs D₂ n) :
    ‖fockSectorOp Hs D₂ A n x‖ ≤ ((n : ℝ) * C) * ‖(x : fockSector Hs n)‖ := by
  obtain ⟨x₀, hx₀, hxe⟩ := x.2
  have hx' : (x : fockSector Hs n)
      = sectorEmb Hs n ((⟨x₀, hx₀⟩ : sectorDom Hs D₂ n) : (Hs.pow n).carrier) := hxe.symm
  have hop : fockSectorOp Hs D₂ A n x
      = sectorEmb Hs n (sectorOp Hs D₂ A n ⟨x₀, hx₀⟩) :=
    pushOp_apply (sectorEmb Hs n) (sectorOp Hs D₂ A n) x ⟨x₀, hx₀⟩ hx'
  rw [hop, (sectorEmb Hs n).norm_map, hx', (sectorEmb Hs n).norm_map]
  exact norm_sectorOp_le Hs D₂ A hC0 hC n ⟨x₀, hx₀⟩

/-! ## Everywhere-defined bounded operators -/

variable (B : (⊤ : Submodule ℂ Hs.carrier) →ₗ[ℂ] Hs.carrier)

/-- **Every dense subspace is a core for an everywhere-defined bounded operator.**  The graph
norm of a bounded operator is equivalent to the norm, so graph-norm density is plain
density. -/
theorem isGraphCore_of_bounded {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ a : (⊤ : Submodule ℂ Hs.carrier), ‖B a‖ ≤ C * ‖(a : Hs.carrier)‖)
    {D : Submodule ℂ Hs.carrier} (hdense : Dense (D : Set Hs.carrier)) : IsGraphCore D B := by
  intro x ε hε
  have hden : (0 : ℝ) < 1 + C := by linarith
  have hpos : 0 < ε / (1 + C) := by positivity
  obtain ⟨y, hyD, hy⟩ := Metric.mem_closure_iff.mp (hdense (x : Hs.carrier)) _ hpos
  have hxy : ‖(x : Hs.carrier) - y‖ < ε / (1 + C) := by rw [← dist_eq_norm]; exact hy
  have hmul : (1 + C) * ‖(x : Hs.carrier) - y‖ < ε := by
    calc (1 + C) * ‖(x : Hs.carrier) - y‖ < (1 + C) * (ε / (1 + C)) :=
          mul_lt_mul_of_pos_left hxy hden
      _ = ε := by field_simp
  have hnn : 0 ≤ ‖(x : Hs.carrier) - y‖ := norm_nonneg _
  refine ⟨⟨y, trivial⟩, hyD, ?_, ?_⟩
  · nlinarith
  · have hsub : B x - B ⟨y, trivial⟩ = B (x - ⟨y, trivial⟩) := (map_sub B _ _).symm
    have hval : ((x - ⟨y, trivial⟩ : (⊤ : Submodule ℂ Hs.carrier)) : Hs.carrier)
        = (x : Hs.carrier) - y := rfl
    rw [hsub]
    have := hC (x - ⟨y, trivial⟩)
    rw [hval] at this
    nlinarith

/-- **The sector hypothesis for a bounded symmetric one-particle operator.**  On the
`n`-particle sector the derivation is bounded by `n C` on a dense domain, hence essentially
self-adjoint there.  No positivity is used. -/
theorem essentiallySelfAdjointOn_fockSectorDom_bounded (hB : SymmetricOn ⊤ B) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ a : (⊤ : Submodule ℂ Hs.carrier), ‖B a‖ ≤ C * ‖(a : Hs.carrier)‖)
    (n : ℕ) :
    EssentiallySelfAdjointOn (fockSectorDom Hs ⊤ n) (fockSectorOp Hs ⊤ B n) :=
  essentiallySelfAdjointOn_of_bounded_dense _
    (symmetricOn_fockSectorOp Hs ⊤ B hB n) (by positivity)
    (norm_fockSectorOp_le Hs ⊤ B hC0 hC n)
    (BookProof.ScalarDGamma.dense_fockSectorDom Hs n)

/-! ## The theorem -/

/-- **Second quantization over a core, for an arbitrary bounded symmetric one-particle
operator.**  Let `B` be symmetric on all of `H` with `‖B a‖ ≤ C ‖a‖` — *no positivity or
semiboundedness is assumed*, so the spectrum of `B` may straddle `0` — and let `D ⊆ H` be any
dense subspace.  Then `dΓ(B)` is essentially self-adjoint on the finite-particle domain
`𝓕_fin(D)` built from `D` alone.  `D` is only a core: it is not invariant under anything, and
no resolvent of `B` on `D` is used. -/
theorem dGamma_bounded_essentiallySelfAdjointOn_fockCore (hB : SymmetricOn ⊤ B) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ a : (⊤ : Submodule ℂ Hs.carrier), ‖B a‖ ≤ C * ‖(a : Hs.carrier)‖)
    {D : Submodule ℂ Hs.carrier} (hdense : Dense (D : Set Hs.carrier)) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs ⊤ D n))
      (dGammaCoreOp Hs ⊤ B D) :=
  dGamma_essentiallySelfAdjointOn_fockCore Hs ⊤ B D
    (isGraphCore_of_bounded Hs B hC0 hC hdense)
    (essentiallySelfAdjointOn_fockSectorDom_bounded Hs B hB hC0 hC)

/-! ## An operator that is unbounded below

The scalar operator `-id` is symmetric with `‖-id‖ = 1`, and its second quantization is the
negative of the number operator, whose spectrum `{-n : n ∈ ℕ}` is unbounded below.  It is an
instance of the theorem above: nothing in the argument needs a spectral lower bound. -/

/-- The second quantization of `-id` — minus the number operator, which is unbounded below —
is essentially self-adjoint on the finite-particle domain over any dense subspace. -/
theorem dGamma_neg_id_essentiallySelfAdjointOn_fockCore {D : Submodule ℂ Hs.carrier}
    (hdense : Dense (D : Set Hs.carrier)) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs ⊤ D n))
      (dGammaCoreOp Hs ⊤ (BookProof.ScalarDGamma.scalarOp Hs (-1)) D) :=
  dGamma_bounded_essentiallySelfAdjointOn_fockCore Hs _
    (BookProof.ScalarDGamma.symmetricOn_scalarOp Hs (-1)) zero_le_one
    (fun a => by
      rw [BookProof.ScalarDGamma.scalarOp_apply, norm_smul]
      simp) hdense

end

end BookProof.BoundedDGamma

namespace BookProof.EsaPair

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.TensorOpBound
  BookProof.SecondQuantizationCore BookProof.DirectSumEsa BookProof.BoundedDGamma
  BookProof.SecondQuantizationCore BookProof.DirectSumEsa

noncomputable section

/-- **An essentially self-adjoint one-particle operator, packaged as a core of a reference
operator.**  `closureOp` is the operator on the domain `D₂ = closureDomain` of the closure,
`coreDomain` is the small domain `D` on which the operator is really given, and `is_core`
says that `D` is graph-norm dense in `D₂`.  `sector_esa` is the one-particle input at the
level of the sectors: essential self-adjointness of `dΓ(closureOp)⁽ⁿ⁾` on the tensor power of
`closureDomain`, which is the statement for a *self-adjoint* one-particle operator.

No positivity, semiboundedness or order structure is required of `closureOp`. -/
structure ESAPair (Hs : IPSpace) where
  /-- the domain of the reference (closure) operator -/
  closureDomain : Submodule ℂ Hs.carrier
  /-- the reference operator, on the domain of the closure -/
  closureOp : closureDomain →ₗ[ℂ] Hs.carrier
  /-- the reference operator is symmetric (no positivity assumed) -/
  symmetric : SymmetricOn closureDomain closureOp
  /-- the sectorwise input: `dΓ⁽ⁿ⁾` is essentially self-adjoint on the tensor power of the
  domain of the closure -/
  sector_esa : ∀ n : ℕ, EssentiallySelfAdjointOn (fockSectorDom Hs closureDomain n)
    (fockSectorOp Hs closureDomain closureOp n)
  /-- the domain on which the operator is really given -/
  coreDomain : Submodule ℂ Hs.carrier
  /-- the core is contained in the domain of the closure -/
  sub_domain : coreDomain ≤ closureDomain
  /-- the core is graph-norm dense in the domain of the closure -/
  is_core : IsGraphCore coreDomain closureOp

variable {Hs : IPSpace} (P : ESAPair Hs)

/-- The operator that is really given: the restriction of the reference operator to the
core. -/
def ESAPair.toOp : P.coreDomain →ₗ[ℂ] Hs.carrier := restrictOp P.closureOp P.sub_domain





/-- The second quantization `dΓ(A)` on the finite-particle domain over the core. -/
def ESAPair.dGammaOp :
    dsCore (fun n : ℕ => fockSectorCore Hs P.closureDomain P.coreDomain n) →ₗ[ℂ]
      lp (fun n : ℕ => fockSector Hs n) 2 :=
  dGammaCoreOp Hs P.closureDomain P.closureOp P.coreDomain







/-! ## Packages that exist: bounded symmetric one-particle operators -/

/-- **A package for every bounded symmetric one-particle operator and every dense core.**  The
operator is not assumed positive — `B = -id` is allowed, and then `dΓ(B)` is unbounded below —
and the sectorwise input is *proved* here rather than assumed. -/
def ESAPair.ofBounded (Hs : IPSpace) (B : (⊤ : Submodule ℂ Hs.carrier) →ₗ[ℂ] Hs.carrier)
    (hB : SymmetricOn ⊤ B) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ a : (⊤ : Submodule ℂ Hs.carrier), ‖B a‖ ≤ C * ‖(a : Hs.carrier)‖)
    (D : Submodule ℂ Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) : ESAPair Hs where
  closureDomain := ⊤
  closureOp := B
  symmetric := hB
  sector_esa := essentiallySelfAdjointOn_fockSectorDom_bounded Hs B hB hC0 hC
  coreDomain := D
  sub_domain := le_top
  is_core := isGraphCore_of_bounded Hs B hC0 hC hdense

end

end BookProof.EsaPair


