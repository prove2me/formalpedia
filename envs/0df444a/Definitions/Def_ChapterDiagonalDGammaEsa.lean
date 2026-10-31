-- Prove2me | Definitions.Def_ChapterDiagonalDGammaEsa
-- name    : ChapterDiagonalDGammaEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-30T08:27:15.008994+00:00
-- url     : https://prove2.me/theorems/f18a57d1-e825-4dbc-bc79-62da6b189a51
-- title:
--   The Lean 4 theorem `and` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterDiagonalDGammaEsa.lean`): generated def bundle for ChapterDiagonalDGammaEsa. See BookProof/ChapterDiagonalDGammaEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterDiagonalDGammaEsa.lean

import Theorems.Thm_BookProof_GraphCore_pushOp_apply

import Theorems.Thm_BookProof_TensorCore_sectorOp_apply

import Theorems.Thm_BookProof_GraphCore_mem_pushDom

import Theorems.Thm_BookProof_TensorCore_norm_tmul_sub_le

import Definitions.Def_ChapterEsaPairDGamma
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Mathlib


/-!
# Second quantization of an **unbounded** hermitian one-particle operator

The main theorem of `BookProof/ChapterSecondQuantizationCoreEsa.lean` carries, sector by
sector, one hypothesis: essential self-adjointness of the derivation `dΓ(A)⁽ⁿ⁾` on the tensor
power of the domain of the one-particle operator.  `BookProof/ChapterBoundedDGammaEsa.lean`
discharged that hypothesis for **bounded** one-particle operators, by a norm estimate.  This
module discharges it for **unbounded** hermitian one-particle operators — every operator with
a total family of eigenvectors, i.e. with pure point spectrum, the eigenvalues being an
arbitrary family of reals, unbounded above and below if one likes.

The mechanism is not an estimate — there is none available — but an eigenvector argument:

* `essentiallySelfAdjointOn_of_dense_eigenvectors` — a symmetric-free criterion: an operator
  possessing a family of eigenvectors with **real** eigenvalues whose span is dense has both
  deficiency spaces trivial, hence is essentially self-adjoint.  (No bound, no positivity, no
  invariant domain and no resolvent is used: if `T v = λ v` with `λ` real and
  `⟪T u, w⟫ = ± i ⟪u, w⟫` for all `u`, then `(λ ∓ i)⟪v, w⟫ = 0`, so `w ⊥ v`.)
* `derPow_eigTensor` — the sector derivation `dΓ(A)⁽ⁿ⁾` acts on an elementary tensor of
  eigenvectors as the scalar `λ_{i₁} + ⋯ + λ_{iₙ}`, by the Leibniz recursion;
* `dense_eigSpan` — the eigen-tensors span a dense subspace of `H^{⊗n}`, by the multilinear
  approximation estimate `norm_tmul_sub_le`, and `dense_span_fockEigVec` transports this to
  the completed sector;
* `essentiallySelfAdjointOn_fockSectorDom_diagonal` — **the sector hypothesis, proved for an
  unbounded one-particle operator**;
* `dGamma_diagonal_essentiallySelfAdjointOn_fockCore` and `esaPairOfDiagonal` — the main
  theorem and the packaged form: for a hermitian `A` with a total family of eigenvectors and
  any graph-norm core `D ≤ D(A)`, `dΓ(A)` is essentially self-adjoint on the finite-particle
  domain `𝓕_fin(D)`.

The last section builds such operators from scratch, so the hypotheses are not vacuous:
`diagOp` is multiplication by an arbitrary real family `lam` along an orthonormal family `E`
with dense span, `symmetricOn_diagOp` and `essentiallySelfAdjointOn_diagOp` show it is
hermitian and essentially self-adjoint on the algebraic span, `not_bounded_diagOp` shows it is
**genuinely unbounded** as soon as `lam` is unbounded, and
`dGamma_diag_essentiallySelfAdjointOn_fockCore` is the second-quantization theorem for it,
with no hypothesis left over.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.DiagonalDGamma

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
  BookProof.SecondQuantizationCore BookProof.DirectSumEsa BookProof.EsaPair

noncomputable section

/-! ## The elementary-tensor equations of `inclPow` / `derPow`

The platform's published `Def_ChapterTensorGraphCore` carries the definitions but not these
three `rfl` equations (they exist only in the source `ChapterTensorGraphCore.lean`).  Every
consumer therefore states them itself; the local declaration also shadows nothing, because no
imported bundle provides the name. -/

@[simp] theorem inclPow_tmul (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (n : ℕ)
    (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    inclPow Hs D₂ (n + 1) (a ⊗ₜ[ℂ] b) = (a : Hs.carrier) ⊗ₜ[ℂ] inclPow Hs D₂ n b := rfl

@[simp] theorem derPow_zero (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
    (A : D₂ →ₗ[ℂ] Hs.carrier) (x : ((domSpace Hs D₂).pow 0)) :
    derPow Hs D₂ A 0 x = 0 := rfl

@[simp] theorem derPow_tmul (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
    (A : D₂ →ₗ[ℂ] Hs.carrier) (n : ℕ) (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    derPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)
      = (A a) ⊗ₜ[ℂ] inclPow Hs D₂ n b + (a : Hs.carrier) ⊗ₜ[ℂ] derPow Hs D₂ A n b := rfl

/-! ## The eigenvector criterion for essential self-adjointness -/

section Criterion

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

/-- **Deficiency triviality from a total family of eigenvectors.**  If `T v_k = λ_k v_k` with
`λ_k` real and the `v_k` span a dense subspace, then no nonzero `w` satisfies
`⟪T u, w⟫ = z ⟪u, w⟫` for a non-real `z`: testing against `v_k` gives `(λ_k - z)⟪v_k, w⟫ = 0`,
and `λ_k ≠ z`. -/
theorem deficiencyTrivialAt_of_dense_eigenvectors {ι' : Type*} (T : D →ₗ[ℂ] F)
    (v : ι' → D) (lam : ι' → ℝ) (heig : ∀ k, T (v k) = (lam k : ℂ) • (v k : F))
    (hdense : Dense (Submodule.span ℂ (Set.range fun k => (v k : F)) : Set F))
    {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt D T z := by
  intro w hw
  have hperp : ∀ k, (inner ℂ (v k : F) w : ℂ) = 0 := by
    intro k
    have h1 : (inner ℂ (T (v k)) w : ℂ) = z * inner ℂ (v k : F) w := hw (v k)
    rw [heig k, inner_smul_left, Complex.conj_ofReal] at h1
    have hne : ((lam k : ℂ) - z) ≠ 0 := by
      intro h
      apply hz
      have hzk : z = (lam k : ℂ) := by linear_combination -h
      rw [hzk]
      simp
    have hz0 : ((lam k : ℂ) - z) * inner ℂ (v k : F) w = 0 := by linear_combination h1
    rcases mul_eq_zero.mp hz0 with h | h
    · exact absurd h hne
    · exact h
  have hspan : ((Submodule.span ℂ (Set.range fun k => (v k : F)) : Submodule ℂ F) : Set F)
      ⊆ {x : F | (inner ℂ x w : ℂ) = 0} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hperp k
    | zero => simp
    | add a b _ _ ha hb =>
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha =>
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [inner_smul_left, ha, mul_zero]
  have hclosed : IsClosed {x : F | (inner ℂ x w : ℂ) = 0} :=
    isClosed_eq (Continuous.inner continuous_id continuous_const) continuous_const
  have hall : (inner ℂ w w : ℂ) = 0 := hclosed.closure_subset_iff.mpr hspan (hdense w)
  exact inner_self_eq_zero.mp hall

/-- **The eigenvector criterion.**  An operator with a family of eigenvectors with real
eigenvalues spanning a dense subspace is essentially self-adjoint.  No boundedness, no
positivity, no invariant domain and no symmetry hypothesis is needed. -/
theorem essentiallySelfAdjointOn_of_dense_eigenvectors {ι' : Type*} (T : D →ₗ[ℂ] F)
    (v : ι' → D) (lam : ι' → ℝ) (heig : ∀ k, T (v k) = (lam k : ℂ) • (v k : F))
    (hdense : Dense (Submodule.span ℂ (Set.range fun k => (v k : F)) : Set F)) :
    EssentiallySelfAdjointOn D T :=
  ⟨deficiencyTrivialAt_of_dense_eigenvectors T v lam heig hdense (by simp),
    deficiencyTrivialAt_of_dense_eigenvectors T v lam heig hdense (by simp)⟩

end Criterion

/-! ## Eigen-tensors of the sector derivation -/

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  {ι : Type*} (e : ι → D₂) (lam : ι → ℝ)

/-- The elementary tensor `e_{f 0} ⊗ ⋯ ⊗ e_{f (n-1)}` of eigenvectors, inside the tensor power
of the domain. -/
def eigTensor : ∀ (n : ℕ), (Fin n → ι) → ((domSpace Hs D₂).pow n)
  | 0, _ => (1 : ℂ)
  | (n + 1), f => (e (f 0)) ⊗ₜ[ℂ] eigTensor n (fun j => f j.succ)

@[simp] theorem eigTensor_succ (n : ℕ) (f : Fin (n + 1) → ι) :
    eigTensor Hs D₂ e (n + 1) f
      = (e (f 0)) ⊗ₜ[ℂ] eigTensor Hs D₂ e n (fun j => f j.succ) := rfl

theorem eigTensor_cons (n : ℕ) (i : ι) (f : Fin n → ι) :
    eigTensor Hs D₂ e (n + 1) (Fin.cons i f) = (e i) ⊗ₜ[ℂ] eigTensor Hs D₂ e n f := by
  have hs : (fun j : Fin n => (Fin.cons i f : Fin (n + 1) → ι) j.succ) = f := by
    funext j; simp
  rw [eigTensor_succ, hs]
  rfl

/-- The same eigen-tensor, seen inside `H^{⊗n}`. -/
def eigVec (n : ℕ) (f : Fin n → ι) : (Hs.pow n).carrier :=
  inclPow Hs D₂ n (eigTensor Hs D₂ e n f)

theorem eigVec_cons (n : ℕ) (i : ι) (f : Fin n → ι) :
    eigVec Hs D₂ e (n + 1) (Fin.cons i f)
      = (e i : Hs.carrier) ⊗ₜ[ℂ] eigVec Hs D₂ e n f := by
  rw [eigVec, eigTensor_cons]
  rfl

/-- **The eigenvalue equation for the sector derivation.**  On an elementary tensor of
eigenvectors, `dΓ(A)⁽ⁿ⁾` is the scalar `λ_{f 0} + ⋯ + λ_{f (n-1)}`; this is the Leibniz
recursion `dΓ⁽ⁿ⁺¹⁾ = A ⊗ 1 + 1 ⊗ dΓ⁽ⁿ⁾`. -/
theorem derPow_eigTensor (heig : ∀ i, A (e i) = (lam i : ℂ) • (e i : Hs.carrier)) :
    ∀ (n : ℕ) (f : Fin n → ι), derPow Hs D₂ A n (eigTensor Hs D₂ e n f)
      = ((∑ j, lam (f j) : ℝ) : ℂ) • eigVec Hs D₂ e n f := by
  intro n
  induction n with
  | zero => intro f; simp [derPow, eigVec]
  | succ n ih =>
      intro f
      rw [eigTensor_succ, derPow_tmul, heig, ih]
      simp only [eigVec, eigTensor_succ, Fin.sum_univ_succ]
      push_cast
      rw [inclPow_tmul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← add_smul]

/-! ## The eigen-tensors are total -/

/-- The span of the eigen-tensors inside `H^{⊗n}`. -/
def eigSpan (n : ℕ) : Submodule ℂ (Hs.pow n).carrier :=
  Submodule.span ℂ (Set.range (eigVec Hs D₂ e n))

theorem tmul_mem_eigSpan_of_eigVec (n : ℕ) (i : ι) {y : (Hs.pow n).carrier}
    (hy : y ∈ eigSpan Hs D₂ e n) :
    ((e i : Hs.carrier) ⊗ₜ[ℂ] y : (Hs.pow (n + 1)).carrier) ∈ eigSpan Hs D₂ e (n + 1) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨f, rfl⟩ := hz
      exact Submodule.subset_span ⟨Fin.cons i f, (eigVec_cons Hs D₂ e n i f)⟩
  | zero => simp
  | add a b _ _ ha hb =>
      rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
      rw [TensorProduct.tmul_smul]; exact Submodule.smul_mem _ c ha

theorem tmul_mem_eigSpan (n : ℕ) {x : Hs.carrier}
    (hx : x ∈ Submodule.span ℂ (Set.range fun i => (e i : Hs.carrier)))
    {y : (Hs.pow n).carrier} (hy : y ∈ eigSpan Hs D₂ e n) :
    (x ⊗ₜ[ℂ] y : (Hs.pow (n + 1)).carrier) ∈ eigSpan Hs D₂ e (n + 1) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact tmul_mem_eigSpan_of_eigVec Hs D₂ e n i hy
  | zero => simp
  | add a b _ _ ha hb =>
      rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
      rw [← TensorProduct.smul_tmul']; exact Submodule.smul_mem _ c ha

/-- **The multilinear approximation step.**  An elementary tensor `p ⊗ q` is approximated by
eigen-tensors: move `p` into the span of the eigenvectors and `q` into the span of the
eigen-tensors of one particle less, and add the two costs (`norm_tmul_sub_le`). -/
theorem tmul_mem_closure_eigSpan
    (hdense : Dense (Submodule.span ℂ (Set.range fun i => (e i : Hs.carrier)) :
      Set Hs.carrier))
    (n : ℕ) (ih : Dense ((eigSpan Hs D₂ e n : Submodule ℂ (Hs.pow n).carrier) :
      Set (Hs.pow n).carrier))
    (p : Hs.carrier) (q : (Hs.pow n).carrier) :
    (p ⊗ₜ[ℂ] q : (Hs.pow (n + 1)).carrier) ∈ (eigSpan Hs D₂ e (n + 1)).topologicalClosure := by
  refine Metric.mem_closure_iff.mpr ?_
  intro ε hε
  set C : ℝ := ‖p‖ + ‖q‖ + 2 with hCdef
  have hCpos : 0 < C := by
    have h1 : (0 : ℝ) ≤ ‖p‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
    rw [hCdef]; linarith
  set δ : ℝ := min 1 (ε / (2 * C)) with hδdef
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδone : δ ≤ 1 := min_le_left _ _
  have hδC : δ * C < ε := by
    have h1 : δ ≤ ε / (2 * C) := min_le_right _ _
    have h2 : δ * C ≤ (ε / (2 * C)) * C := mul_le_mul_of_nonneg_right h1 hCpos.le
    have h3 : (ε / (2 * C)) * C = ε / 2 := by field_simp
    rw [h3] at h2
    linarith
  obtain ⟨p', hp'mem, hp'⟩ := Metric.mem_closure_iff.mp (hdense p) δ hδpos
  obtain ⟨q', hq'mem, hq'⟩ := Metric.mem_closure_iff.mp (ih q) δ hδpos
  have h1 : ‖p - p'‖ < δ := by rw [← dist_eq_norm]; exact hp'
  have h2 : ‖q - q'‖ < δ := by rw [← dist_eq_norm]; exact hq'
  have hp'norm : ‖p'‖ ≤ ‖p‖ + δ := by
    have hle := norm_sub_norm_le p' p
    have : ‖p' - p‖ < δ := by rw [norm_sub_rev]; exact h1
    linarith
  refine ⟨p' ⊗ₜ[ℂ] q', tmul_mem_eigSpan Hs D₂ e n hp'mem hq'mem, ?_⟩
  rw [dist_eq_norm]
  have hbound : ‖(p ⊗ₜ[ℂ] q : (Hs.pow (n + 1)).carrier) - p' ⊗ₜ[ℂ] q'‖
      ≤ ‖p - p'‖ * ‖q‖ + ‖p'‖ * ‖q - q'‖ := norm_tmul_sub_le p p' q q'
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
  have hp0 : (0 : ℝ) ≤ ‖p‖ := norm_nonneg _
  have hstep : ‖p - p'‖ * ‖q‖ + ‖p'‖ * ‖q - q'‖ ≤ δ * C := by
    have e1 : ‖p - p'‖ * ‖q‖ ≤ δ * ‖q‖ := mul_le_mul_of_nonneg_right h1.le hq0
    have e2 : ‖p'‖ * ‖q - q'‖ ≤ (‖p‖ + δ) * δ :=
      mul_le_mul hp'norm h2.le (norm_nonneg _) (by linarith)
    have e3 : δ * ‖q‖ + (‖p‖ + δ) * δ ≤ δ * C := by
      rw [hCdef]; nlinarith
    linarith
  linarith

/-- **The eigen-tensors are total in every sector.**  If the eigenvectors span a dense
subspace of `H`, then the eigen-tensors span a dense subspace of `H^{⊗n}`. -/
theorem dense_eigSpan
    (hdense : Dense (Submodule.span ℂ (Set.range fun i => (e i : Hs.carrier)) :
      Set Hs.carrier)) :
    ∀ n : ℕ, Dense ((eigSpan Hs D₂ e n : Submodule ℂ (Hs.pow n).carrier) :
      Set (Hs.pow n).carrier) := by
  intro n
  induction n with
  | zero =>
      have htop : eigSpan Hs D₂ e 0 = ⊤ := by
        refine top_unique fun x _ => ?_
        have h1 : ((1 : ℂ) : (Hs.pow 0).carrier) ∈ Set.range (eigVec Hs D₂ e 0) :=
          ⟨Fin.elim0, rfl⟩
        have h2 := Submodule.smul_mem (eigSpan Hs D₂ e 0) (x : ℂ) (Submodule.subset_span h1)
        simpa using h2
      rw [htop]
      simp
  | succ n ih =>
      intro x
      have hx : x ∈ Submodule.span ℂ
          {t : Hs.carrier ⊗[ℂ] (Hs.pow n).carrier |
            ∃ (p : Hs.carrier) (q : (Hs.pow n).carrier), p ⊗ₜ[ℂ] q = t} := by
        rw [TensorProduct.span_tmul_eq_top]; trivial
      have hmem : x ∈ (eigSpan Hs D₂ e (n + 1)).topologicalClosure := by
        induction hx using Submodule.span_induction with
        | mem t ht =>
            obtain ⟨p, q, rfl⟩ := ht
            exact tmul_mem_closure_eigSpan Hs D₂ e hdense n ih p q
        | zero => exact Submodule.zero_mem _
        | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
        | smul c a _ ha => exact Submodule.smul_mem _ c ha
      exact hmem

/-! ## Passage to the completed sector -/

/-- The eigen-tensors, inside the completed `n`-particle sector. -/
def fockEigVec (n : ℕ) (f : Fin n → ι) : fockSector Hs n :=
  sectorEmb Hs n (eigVec Hs D₂ e n f)

theorem fockEigVec_mem (n : ℕ) (f : Fin n → ι) :
    fockEigVec Hs D₂ e n f ∈ fockSectorDom Hs D₂ n :=
  mem_pushDom (sectorEmb Hs n)
    (⟨eigVec Hs D₂ e n f, ⟨eigTensor Hs D₂ e n f, rfl⟩⟩ : sectorDom Hs D₂ n)

/-- Totality of the eigen-tensors survives the completion. -/
theorem dense_span_fockEigVec
    (hdense : Dense (Submodule.span ℂ (Set.range fun i => (e i : Hs.carrier)) :
      Set Hs.carrier)) (n : ℕ) :
    Dense ((Submodule.span ℂ (Set.range (fockEigVec Hs D₂ e n)) :
      Submodule ℂ (fockSector Hs n)) : Set (fockSector Hs n)) := by
  have hd := dense_eigSpan Hs D₂ e hdense n
  set U := sectorEmb Hs n with hU
  have himg : (Submodule.map U.toLinearMap (eigSpan Hs D₂ e n) : Set (fockSector Hs n))
      ⊆ (Submodule.span ℂ (Set.range (fockEigVec Hs D₂ e n)) : Set (fockSector Hs n)) := by
    have hmap : Submodule.map U.toLinearMap (eigSpan Hs D₂ e n)
        = Submodule.span ℂ (Set.range (fockEigVec Hs D₂ e n)) := by
      rw [eigSpan, Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap]
  intro y
  have hrange : Set.range (fun z : (Hs.pow n).carrier => U z)
      ⊆ closure ((Submodule.span ℂ (Set.range (fockEigVec Hs D₂ e n)) :
        Submodule ℂ (fockSector Hs n)) : Set (fockSector Hs n)) := by
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ closure ((eigSpan Hs D₂ e n : Submodule ℂ (Hs.pow n).carrier) :
        Set (Hs.pow n).carrier) := hd z
    have himg2 : U z ∈ closure (U '' ((eigSpan Hs D₂ e n :
        Submodule ℂ (Hs.pow n).carrier) : Set (Hs.pow n).carrier)) := by
      have := image_closure_subset_closure_image (f := fun z => U z) U.continuous
        (Set.mem_image_of_mem _ hz)
      exact this
    refine closure_mono ?_ himg2
    rintro _ ⟨z', hz', rfl⟩
    exact himg ⟨z', hz', rfl⟩
  have hdr : DenseRange (fun z : (Hs.pow n).carrier => U z) := by
    have : DenseRange ((↑) : (Hs.pow n).carrier → UniformSpace.Completion (Hs.pow n).carrier) :=
      UniformSpace.Completion.denseRange_coe
    exact this
  have hy : y ∈ closure (Set.range (fun z : (Hs.pow n).carrier => U z)) := hdr y
  have := closure_mono hrange hy
  rwa [closure_closure] at this

/-! ## The sector hypothesis, for an unbounded one-particle operator -/

/-- **The sector hypothesis, proved.**  Let `A` be a one-particle operator with a family of
eigenvectors `e i` with real eigenvalues `lam i` whose span is dense in `H` — an arbitrary
hermitian operator with pure point spectrum, *possibly unbounded*, with eigenvalues unbounded
above and below.  Then the sector derivation `dΓ(A)⁽ⁿ⁾` is essentially self-adjoint on the
tensor power of the domain of `A`, for every `n`. -/
theorem essentiallySelfAdjointOn_fockSectorDom_diagonal
    (heig : ∀ i, A (e i) = (lam i : ℂ) • (e i : Hs.carrier))
    (hdense : Dense (Submodule.span ℂ (Set.range fun i => (e i : Hs.carrier)) :
      Set Hs.carrier)) (n : ℕ) :
    EssentiallySelfAdjointOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n) := by
  have hval : ∀ f : Fin n → ι, fockSectorOp Hs D₂ A n
      (⟨fockEigVec Hs D₂ e n f, fockEigVec_mem Hs D₂ e n f⟩ : fockSectorDom Hs D₂ n)
      = (((∑ j, lam (f j) : ℝ) : ℂ)) •
        ((⟨fockEigVec Hs D₂ e n f, fockEigVec_mem Hs D₂ e n f⟩ :
          fockSectorDom Hs D₂ n) : fockSector Hs n) := by
    intro f
    have hx₀ : ((⟨fockEigVec Hs D₂ e n f, fockEigVec_mem Hs D₂ e n f⟩ :
        fockSectorDom Hs D₂ n) : fockSector Hs n)
        = sectorEmb Hs n ((⟨eigVec Hs D₂ e n f, ⟨eigTensor Hs D₂ e n f, rfl⟩⟩ :
          sectorDom Hs D₂ n) : (Hs.pow n).carrier) := rfl
    have h1 : fockSectorOp Hs D₂ A n
        (⟨fockEigVec Hs D₂ e n f, fockEigVec_mem Hs D₂ e n f⟩ : fockSectorDom Hs D₂ n)
        = sectorEmb Hs n (sectorOp Hs D₂ A n
          (⟨eigVec Hs D₂ e n f, ⟨eigTensor Hs D₂ e n f, rfl⟩⟩ : sectorDom Hs D₂ n)) :=
      pushOp_apply (sectorEmb Hs n) (sectorOp Hs D₂ A n) _ _ hx₀
    rw [h1, sectorOp_apply Hs D₂ A n _ (eigTensor Hs D₂ e n f) rfl,
      derPow_eigTensor Hs D₂ A e lam heig n f, map_smul]
    rfl
  exact essentiallySelfAdjointOn_of_dense_eigenvectors _
    (fun f : Fin n → ι => (⟨fockEigVec Hs D₂ e n f, fockEigVec_mem Hs D₂ e n f⟩ :
      fockSectorDom Hs D₂ n))
    (fun f : Fin n → ι => ∑ j, lam (f j)) hval (dense_span_fockEigVec Hs D₂ e hdense n)

/-! ## The main theorem -/

/-- **Second quantization over a core, for an unbounded hermitian one-particle operator with
pure point spectrum.**  `A` is symmetric on `D₂`, has a total family of eigenvectors with real
eigenvalues (no bound on them: `A` may be unbounded above and below), and `D ≤ D₂` is a
graph-norm core.  Then `dΓ(A)` is essentially self-adjoint on the finite-particle domain
`𝓕_fin(D)` built from `D` alone. -/
theorem dGamma_diagonal_essentiallySelfAdjointOn_fockCore
    (heig : ∀ i, A (e i) = (lam i : ℂ) • (e i : Hs.carrier))
    (hdense : Dense (Submodule.span ℂ (Set.range fun i => (e i : Hs.carrier)) :
      Set Hs.carrier))
    (D : Submodule ℂ Hs.carrier) (hcore : IsGraphCore D A) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n))
      (dGammaCoreOp Hs D₂ A D) :=
  dGamma_essentiallySelfAdjointOn_fockCore Hs D₂ A D hcore
    (essentiallySelfAdjointOn_fockSectorDom_diagonal Hs D₂ A e lam heig hdense)

/-- The packaged form: an `ESAPair` whose sectorwise input is **proved**, for an unbounded
hermitian one-particle operator with a total family of eigenvectors. -/
def esaPairOfDiagonal (hA : SymmetricOn D₂ A)
    (heig : ∀ i, A (e i) = (lam i : ℂ) • (e i : Hs.carrier))
    (hdense : Dense (Submodule.span ℂ (Set.range fun i => (e i : Hs.carrier)) :
      Set Hs.carrier))
    (D : Submodule ℂ Hs.carrier) (hsub : D ≤ D₂) (hcore : IsGraphCore D A) : ESAPair Hs where
  closureDomain := D₂
  closureOp := A
  symmetric := hA
  sector_esa := essentiallySelfAdjointOn_fockSectorDom_diagonal Hs D₂ A e lam heig hdense
  coreDomain := D
  sub_domain := hsub
  is_core := hcore

/-! ## Such operators exist, and are unbounded

Nothing above is vacuous: the diagonal operator along an orthonormal family with dense span,
with an arbitrary real family of eigenvalues, satisfies every hypothesis, and is unbounded as
soon as the eigenvalues are. -/

section Diagonal

variable {Hs}
variable {E : ι → Hs.carrier} (hE : Orthonormal ℂ E)

/-- The domain of the diagonal operator: the algebraic span of the orthonormal family. -/
def diagDomain (E : ι → Hs.carrier) : Submodule ℂ Hs.carrier := Submodule.span ℂ (Set.range E)

/-- The basis of `diagDomain` given by the orthonormal family. -/
def diagBasis : Module.Basis ι ℂ (diagDomain E) := Module.Basis.span hE.linearIndependent

theorem diagBasis_apply (i : ι) : (diagBasis hE i : Hs.carrier) = E i :=
  Module.Basis.coe_span_apply hE.linearIndependent i

/-- **Multiplication by an arbitrary real family along an orthonormal family**: the diagonal
one-particle operator, on the algebraic span of the family. -/
def diagOp (lam : ι → ℝ) : diagDomain E →ₗ[ℂ] Hs.carrier :=
  (diagBasis hE).constr ℂ fun i => (lam i : ℂ) • E i

theorem diagOp_apply_basis (lam : ι → ℝ) (i : ι) :
    diagOp hE lam (diagBasis hE i) = (lam i : ℂ) • E i := by
  rw [diagOp, Module.Basis.constr_basis]

/-- The eigenvectors of the diagonal operator, as elements of its domain. -/
def diagVec (i : ι) : diagDomain E := diagBasis hE i

theorem diagOp_eig (lam : ι → ℝ) (i : ι) :
    diagOp hE lam (diagVec hE i) = (lam i : ℂ) • ((diagVec hE i : Hs.carrier)) := by
  rw [diagVec, diagOp_apply_basis, diagBasis_apply]

theorem diagVec_coe (i : ι) : ((diagVec hE i : Hs.carrier)) = E i := diagBasis_apply hE i

theorem range_diagVec :
    (Set.range fun i => ((diagVec hE i : Hs.carrier))) = Set.range E := by
  have hfun : (fun i => ((diagVec hE i : Hs.carrier))) = E := funext fun i => diagVec_coe hE i
  rw [hfun]

/-- The diagonal operator is **hermitian** on its domain: the eigenvalues are real and the
eigenvectors are orthogonal. -/
theorem symmetricOn_diagOp (lam : ι → ℝ) : SymmetricOn (diagDomain E) (diagOp hE lam) := by
  classical
  intro x y
  have hx := (diagBasis hE).linearCombination_repr x
  have hy := (diagBasis hE).linearCombination_repr y
  rw [← hx, ← hy]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    inner_sum, sum_inner, inner_smul_left, inner_smul_right, Submodule.coe_sum,
    Submodule.coe_smul, diagOp_apply_basis, diagBasis_apply, Finset.mul_sum,
    Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases eq_or_ne j i with rfl | hji
  · ring
  · rw [hE.2 hji]; ring

/-- The diagonal operator is **essentially self-adjoint** on the algebraic span of the family,
by the eigenvector criterion — for any real eigenvalues, bounded or not. -/
theorem essentiallySelfAdjointOn_diagOp (lam : ι → ℝ)
    (hdense : Dense (Submodule.span ℂ (Set.range E) : Set Hs.carrier)) :
    EssentiallySelfAdjointOn (diagDomain E) (diagOp hE lam) :=
  essentiallySelfAdjointOn_of_dense_eigenvectors _ (diagVec hE) lam (diagOp_eig hE lam)
    (by rw [range_diagVec hE]; exact hdense)

/-- **The diagonal operator is genuinely unbounded** whenever the eigenvalues are: there is no
constant `C` with `‖A x‖ ≤ C ‖x‖`. -/
theorem not_bounded_diagOp (lam : ι → ℝ) (hlam : ∀ C : ℝ, ∃ i, C < |lam i|) :
    ¬ ∃ C : ℝ, ∀ x : diagDomain E, ‖diagOp hE lam x‖ ≤ C * ‖(x : Hs.carrier)‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨i, hi⟩ := hlam C
  have hnorm : ‖E i‖ = 1 := hE.1 i
  have h1 : ‖diagOp hE lam (diagVec hE i)‖ = |lam i| := by
    rw [diagOp_eig, norm_smul, diagVec_coe, hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 := hC (diagVec hE i)
  rw [h1, diagVec_coe, hnorm, mul_one] at h2
  linarith



end Diagonal

end

end BookProof.DiagonalDGamma


