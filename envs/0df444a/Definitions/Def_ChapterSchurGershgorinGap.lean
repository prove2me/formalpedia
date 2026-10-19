-- Prove2me | Definitions.Def_ChapterSchurGershgorinGap
-- name    : ChapterSchurGershgorinGap
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-17T13:16:37.434992+00:00
-- url     : https://prove2.me/theorems/1cecd674-3ff8-4659-bc1d-32d79914c8a0
-- title:
--   Chapter SchurGershgorinGap
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSchurGershgorinGap.lean`): generated def bundle for ChapterSchurGershgorinGap. See BookProof/ChapterSchurGershgorinGap.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSchurGershgorinGap.lean

import Definitions.Def_ChapterTruncationGapLift
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Mathlib
import Theorems.Thm_BookProof_TruncationGapLift_gap_of_level_gap_and_tail
import Theorems.Thm_BookProof_YangMillsFockGapChain_ym_fock_mass_gap_of_one_particle_form_gap
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_symmetricOn


/-!
# Chapter SchurGershgorinGap — the tail and coupling inputs, from matrix elements

`CONSOLIDATED_PLAN.md`, QYM-1 **task 3**: "`λ₁(H₁|core) > 0` (strict positivity, not just
non-negativity) is the mathematical claim to establish or to leave as the single named
hypothesis."

`ChapterTruncationGapLift` reduced the core form gap of the *infinite* one-particle operator
to three inputs: a gap certified on the order-`m` truncation, **tail coercivity** on
`tailSpan b m`, and a **coupling bound** across the split.  The last two were left as
hypotheses.  This chapter proves both of them from *matrix-element data* — the numbers
`aᵢⱼ = ⟪bᵢ, H bⱼ⟫` a certificate actually records — so that strict positivity of the
one-particle operator becomes a checkable family of inequalities on the entries rather than
an unanalysed assumption.

## The two criteria

* **Gershgorin (diagonal dominance) ⇒ coercivity.**  If on an index set `T` the diagonal
  entries satisfy `dᵢ ≤ Re aᵢᵢ` and the off-diagonal absolute row sums satisfy
  `∑_{j ∈ T, j ≠ i} ‖aᵢⱼ‖ ≤ rᵢ`, then on the span of `{bᵢ | i ∈ T}` the energy form obeys
  `⟪v, H v⟫ ≥ (infᵢ (dᵢ − rᵢ)) ‖v‖²` (`quadForm_ge_of_gershgorin_on`).  Taking
  `T = {i | m ≤ i}` gives exactly the tail coercivity of the lift
  (`tail_coercive_of_gershgorin`); taking `T = Set.univ` gives a core form gap outright
  (`quadForm_ge_of_gershgorin`).

* **Schur test ⇒ coupling bound.**  If the off-diagonal block `{i < m} × {m ≤ j}` has all
  row sums and all column sums at most `ε`, then `|⟪x, H w⟫| ≤ ε‖x‖‖w‖` across the split
  (`abs_inner_block_le`, `coupling_bound_of_schur`) — the second hypothesis of the lift.

Both criteria are stated with the sums quantified over *arbitrary finite subsets* of the
index set, which is the form a summable row / column bound delivers and which keeps every
proof finite.

## Deliverables

* `bvec`, `entry` — the basis vectors as core elements and the matrix elements;
* `exists_repr_of_mem_span_image`, `norm_sq_sum`, `quadForm_sum`, `inner_sum_apply_sum` —
  the finite-combination calculus behind everything else;
* **`quadForm_sum_ge`**, **`quadForm_ge_of_gershgorin_on`**, `quadForm_ge_of_gershgorin`,
  **`tail_coercive_of_gershgorin`**;
* **`abs_inner_block_le`**, `coupling_bound_of_schur`;
* **`gap_of_level_gap_and_matrix_bounds`** — the composition with
  `TruncationGapLift.gap_of_level_gap_and_tail`: certified order-`m` gap + Gershgorin tail
  data + Schur block data ⇒ core form gap `μ − ε`, and `strict_pos_of_matrix_bounds` — the
  strict positivity `⟪v, H v⟫ > 0` for `v ≠ 0` when `ε < μ`, which is QYM-1 task 3's claim
  in the form the chain consumes;
* **`ym_fock_gap_of_truncated_gap_and_matrix_bounds`** and
  **`ym_fock_mass_gap_of_truncated_gap_and_matrix_bounds`** — the same for the concrete
  gauge-fixed Yang–Mills one-particle Hamiltonian and its `dΓ` lift.

## Honest boundary

What is proved here is the *implication*: the recorded matrix elements satisfying diagonal
dominance on the tail and a Schur bound on the coupling block give the gap, with the
explicit constant `μ − ε`.  Whether the gauge-fixed Yang–Mills entries satisfy those
inequalities is not decided here — it is a computation on the entries, not an assumption
about the spectrum, which is the point: the remaining input is now finite, checkable data
of the same kind the certificate already reports.  No mass gap of the physical Yang–Mills
Hamiltonian is claimed.

Everything in this module is `sorry`-free and `axiom`-free.
-/

noncomputable section

namespace BookProof.SchurGershgorin

open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.TruncationGapLift
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ## 1. Basis vectors, matrix elements, and finite combinations -/

/-- The `i`-th basis vector, as an element of the finite-mode core. -/
def bvec (b : HilbertBasis ℕ ℂ F) (i : ℕ) : finiteModeDomain b :=
  ⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩

@[simp] theorem bvec_coe (b : HilbertBasis ℕ ℂ F) (i : ℕ) :
    ((bvec b i : finiteModeDomain b) : F) = b i := rfl

/-- **The matrix element** `aᵢⱼ = ⟪bᵢ, H bⱼ⟫` — the number a certificate records. -/
def entry (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F) (i j : ℕ) : ℂ :=
  inner ℂ (b i) (H (bvec b j))

/-- For a symmetric operator the matrix is Hermitian. -/
theorem entry_conj (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    (hsym : SymmetricOn _ H) (i j : ℕ) :
    (starRingEnd ℂ) (entry b H i j) = entry b H j i := by
  simp only [entry]
  rw [inner_conj_symm]
  simpa using hsym (bvec b j) (bvec b i)

/-- The absolute values of the matrix are symmetric. -/
theorem norm_entry_symm (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    (hsym : SymmetricOn _ H) (i j : ℕ) : ‖entry b H i j‖ = ‖entry b H j i‖ := by
  rw [← entry_conj b H hsym i j, RCLike.norm_conj]

/-- **Every vector of a basis-span is a finite combination with distinct indices.** -/
theorem exists_repr_of_mem_span_image (b : HilbertBasis ℕ ℂ F) (T : Set ℕ) {v : F}
    (hv : v ∈ Submodule.span ℂ (b '' T)) :
    ∃ (S : Finset ℕ) (c : ℕ → ℂ), (↑S : Set ℕ) ⊆ T ∧ v = ∑ i ∈ S, c i • b i := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  refine ⟨l.support, fun i => l i, (Finsupp.mem_supported ℂ l).mp hl, ?_⟩
  simp [Finsupp.linearCombination_apply, Finsupp.sum]

/-- Pythagoras for a finite orthonormal combination. -/
theorem norm_sq_sum (b : HilbertBasis ℕ ℂ F) (S : Finset ℕ) (c : ℕ → ℂ) :
    ‖∑ i ∈ S, c i • b i‖ ^ 2 = ∑ i ∈ S, ‖c i‖ ^ 2 := by
  have h := congrArg Complex.re (b.orthonormal.inner_sum c c S)
  have hl : (inner ℂ (∑ i ∈ S, c i • b i) (∑ i ∈ S, c i • b i) : ℂ).re
      = ‖∑ i ∈ S, c i • b i‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    norm_cast
  have hr : (∑ i ∈ S, (starRingEnd ℂ) (c i) * c i).re = ∑ i ∈ S, ‖c i‖ ^ 2 := by
    simp [Complex.re_sum, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      -Complex.ofReal_pow]
  rw [hl, hr] at h
  exact h

/-- The energy pairing of two finite combinations, in matrix elements. -/
theorem inner_sum_apply_sum (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    (S T : Finset ℕ) (c e : ℕ → ℂ) :
    (inner ℂ (∑ i ∈ S, c i • b i) (H (∑ j ∈ T, e j • bvec b j)) : ℂ)
      = ∑ i ∈ S, ∑ j ∈ T, (starRingEnd ℂ) (c i) * e j * entry b H i j := by
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right]
  simp only [entry]
  ring

/-- The energy form of a finite combination, in matrix elements. -/
theorem quadForm_sum (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    (S : Finset ℕ) (c : ℕ → ℂ) :
    quadForm H (∑ i ∈ S, c i • bvec b i)
      = (∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * entry b H i j).re := by
  have hcoe : ((∑ i ∈ S, c i • bvec b i : finiteModeDomain b) : F) = ∑ i ∈ S, c i • b i := by
    push_cast
    rfl
  simp only [quadForm, hcoe]
  rw [inner_sum_apply_sum]

/-- Swapping the two indices of an off-diagonal double sum. -/
theorem sum_off_diag_comm (S : Finset ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ i ∈ S, ∑ j ∈ S.erase i, G i j = ∑ j ∈ S, ∑ i ∈ S.erase j, G i j := by
  have h1 : ∀ i ∈ S, ∑ j ∈ S.erase i, G i j = (∑ j ∈ S, G i j) - G i i :=
    fun i hi => Finset.sum_erase_eq_sub hi
  have h2 : ∀ j ∈ S, ∑ i ∈ S.erase j, G i j = (∑ i ∈ S, G i j) - G j j :=
    fun j hj => Finset.sum_erase_eq_sub hj
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_comm]

/-! ## 2. Gershgorin: diagonal dominance gives coercivity -/

/-- **The Gershgorin estimate on a finite combination.**  Each mode contributes at least its
diagonal entry minus the absolute row sum of the off-diagonal entries. -/
theorem quadForm_sum_ge (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    (hsym : SymmetricOn _ H) (S : Finset ℕ) (c : ℕ → ℂ) (d r : ℕ → ℝ)
    (hdiag : ∀ i ∈ S, d i ≤ (entry b H i i).re)
    (hrow : ∀ i ∈ S, ∑ j ∈ S.erase i, ‖entry b H i j‖ ≤ r i) :
    ∑ i ∈ S, (d i - r i) * ‖c i‖ ^ 2 ≤ quadForm H (∑ i ∈ S, c i • bvec b i) := by
  classical
  set N : ℕ → ℝ := fun i => ‖c i‖ ^ 2 with hN
  set A : ℕ → ℕ → ℝ := fun i j => ‖entry b H i j‖ with hA
  have hNnonneg : ∀ i, 0 ≤ N i := fun i => sq_nonneg _
  have hAnonneg : ∀ i j, 0 ≤ A i j := fun i j => norm_nonneg _
  set f : ℕ → ℕ → ℝ := fun i j => ((starRingEnd ℂ) (c i) * c j * entry b H i j).re with hf
  have hre : quadForm H (∑ i ∈ S, c i • bvec b i) = ∑ i ∈ S, ∑ j ∈ S, f i j := by
    rw [quadForm_sum]
    simp [Complex.re_sum, hf]
  have hdiagval : ∀ i, f i i = N i * (entry b H i i).re := by
    intro i
    have hz : (starRingEnd ℂ) (c i) * c i = ((N i : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp only [hf]
    rw [hz, Complex.re_ofReal_mul]
  have hoff : ∀ i j, -(A i j * (N i + N j) / 2) ≤ f i j := by
    intro i j
    have h1 : |f i j| ≤ ‖(starRingEnd ℂ) (c i) * c j * entry b H i j‖ :=
      Complex.abs_re_le_norm _
    have h2 : ‖(starRingEnd ℂ) (c i) * c j * entry b H i j‖ = ‖c i‖ * ‖c j‖ * A i j := by
      simp [hA]
    rw [h2] at h1
    have h3 : -(‖c i‖ * ‖c j‖ * A i j) ≤ f i j := by linarith [(abs_le.mp h1).1]
    have h4 : 2 * (‖c i‖ * ‖c j‖) ≤ N i + N j := by
      have := sq_nonneg (‖c i‖ - ‖c j‖)
      simp only [hN]
      nlinarith
    nlinarith [hAnonneg i j]
  have hrowlb : ∀ i ∈ S, N i * d i - (∑ j ∈ S.erase i, A i j * (N i + N j) / 2)
      ≤ ∑ j ∈ S, f i j := by
    intro i hi
    have hsplit : ∑ j ∈ S, f i j = f i i + ∑ j ∈ S.erase i, f i j := by
      rw [← Finset.sum_erase_add S _ hi]; ring
    have h1 : N i * d i ≤ f i i := by
      rw [hdiagval i]
      exact mul_le_mul_of_nonneg_left (hdiag i hi) (hNnonneg i)
    have h2 : -(∑ j ∈ S.erase i, A i j * (N i + N j) / 2) ≤ ∑ j ∈ S.erase i, f i j := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun j _ => hoff i j
    rw [hsplit]; linarith
  have hsum1 : ∑ i ∈ S, (N i * d i - (∑ j ∈ S.erase i, A i j * (N i + N j) / 2))
      ≤ ∑ i ∈ S, ∑ j ∈ S, f i j := Finset.sum_le_sum hrowlb
  have hexp : ∀ i, (∑ j ∈ S.erase i, A i j * (N i + N j) / 2)
      = (∑ j ∈ S.erase i, A i j * N i) / 2 + (∑ j ∈ S.erase i, A i j * N j) / 2 := by
    intro i
    have hterm : ∀ j, A i j * (N i + N j) / 2 = A i j * N i / 2 + A i j * N j / 2 :=
      fun j => by ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
  have hT2 : ∑ i ∈ S, (∑ j ∈ S.erase i, A i j * N i) ≤ ∑ i ∈ S, r i * N i := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i hi) (hNnonneg i)
  have hT3 : ∑ i ∈ S, (∑ j ∈ S.erase i, A i j * N j) ≤ ∑ i ∈ S, r i * N i := by
    rw [sum_off_diag_comm S (fun i j => A i j * N j)]
    refine Finset.sum_le_sum fun j hj => ?_
    have hswap : ∀ i, A i j = A j i := fun i => norm_entry_symm b H hsym i j
    calc ∑ i ∈ S.erase j, A i j * N j = (∑ i ∈ S.erase j, A j i) * N j := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by rw [hswap i]
      _ ≤ r j * N j := mul_le_mul_of_nonneg_right (hrow j hj) (hNnonneg j)
  rw [hre]
  have hlhs : ∑ i ∈ S, (d i - r i) * ‖c i‖ ^ 2 = ∑ i ∈ S, N i * d i - ∑ i ∈ S, r i * N i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [hN]; ring
  have hrhs : ∑ i ∈ S, (N i * d i - (∑ j ∈ S.erase i, A i j * (N i + N j) / 2))
      = ∑ i ∈ S, N i * d i
        - ((∑ i ∈ S, (∑ j ∈ S.erase i, A i j * N i)) / 2
           + (∑ i ∈ S, (∑ j ∈ S.erase i, A i j * N j)) / 2) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hexp i
  rw [hlhs]
  rw [hrhs] at hsum1
  linarith

/-- **Gershgorin on a basis-span.**  Diagonal dominance with margin `μ` on the index set `T`
gives the form bound `⟪v, H v⟫ ≥ μ‖v‖²` on the span of `{bᵢ | i ∈ T}`. -/
theorem quadForm_ge_of_gershgorin_on (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn _ H) (T : Set ℕ) {mu : ℝ}
    (d r : ℕ → ℝ)
    (hdiag : ∀ i ∈ T, d i ≤ (entry b H i i).re)
    (hrow : ∀ i ∈ T, ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ T → i ∉ S →
      ∑ j ∈ S, ‖entry b H i j‖ ≤ r i)
    (hgap : ∀ i ∈ T, mu ≤ d i - r i)
    (v : finiteModeDomain b) (hv : (v : F) ∈ Submodule.span ℂ (b '' T)) :
    mu * ‖(v : F)‖ ^ 2 ≤ quadForm H v := by
  classical
  obtain ⟨S, c, hST, hvc⟩ := exists_repr_of_mem_span_image b T hv
  have hvsum : v = ∑ i ∈ S, c i • bvec b i := by
    refine Subtype.ext ?_
    rw [hvc]
    push_cast
    rfl
  have hdiagS : ∀ i ∈ S, d i ≤ (entry b H i i).re := fun i hi => hdiag i (hST hi)
  have hrowS : ∀ i ∈ S, ∑ j ∈ S.erase i, ‖entry b H i j‖ ≤ r i := by
    intro i hi
    refine hrow i (hST hi) (S.erase i) ?_ ?_
    · intro j hj
      have hj' : j ∈ S.erase i := Finset.mem_coe.mp hj
      exact hST (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hj'))
    · simp
  have hmain := quadForm_sum_ge b H hsym S c d r hdiagS hrowS
  have hnorm : ‖(v : F)‖ ^ 2 = ∑ i ∈ S, ‖c i‖ ^ 2 := by
    rw [hvc]; exact norm_sq_sum b S c
  have hle : mu * ‖(v : F)‖ ^ 2 ≤ ∑ i ∈ S, (d i - r i) * ‖c i‖ ^ 2 := by
    rw [hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    exact mul_le_mul_of_nonneg_right (hgap i (hST hi)) (sq_nonneg _)
  calc mu * ‖(v : F)‖ ^ 2 ≤ ∑ i ∈ S, (d i - r i) * ‖c i‖ ^ 2 := hle
    _ ≤ quadForm H (∑ i ∈ S, c i • bvec b i) := hmain
    _ = quadForm H v := by rw [← hvsum]

/-- **Gershgorin on the whole core.** -/
theorem quadForm_ge_of_gershgorin (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn _ H) {mu : ℝ} (d r : ℕ → ℝ)
    (hdiag : ∀ i, d i ≤ (entry b H i i).re)
    (hrow : ∀ i, ∀ S : Finset ℕ, i ∉ S → ∑ j ∈ S, ‖entry b H i j‖ ≤ r i)
    (hgap : ∀ i, mu ≤ d i - r i) (v : finiteModeDomain b) :
    mu * ‖(v : F)‖ ^ 2 ≤ quadForm H v := by
  refine quadForm_ge_of_gershgorin_on b H hsym Set.univ d r (fun i _ => hdiag i)
    (fun i _ S _ hiS => hrow i S hiS) (fun i _ => hgap i) v ?_
  have : (b '' Set.univ) = Set.range b := Set.image_univ
  rw [this]
  exact v.2

/-- **Tail coercivity from the entries** — the first analytic input of
`TruncationGapLift.gap_of_level_gap_and_tail`, now a theorem about the recorded matrix. -/
theorem tail_coercive_of_gershgorin (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn _ H) {m : ℕ} {mu : ℝ}
    (d r : ℕ → ℝ)
    (hdiag : ∀ i, m ≤ i → d i ≤ (entry b H i i).re)
    (hrow : ∀ i, m ≤ i → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) → i ∉ S →
      ∑ j ∈ S, ‖entry b H i j‖ ≤ r i)
    (hgap : ∀ i, m ≤ i → mu ≤ d i - r i)
    (w : finiteModeDomain b) (hw : (w : F) ∈ tailSpan b m) :
    mu * ‖(w : F)‖ ^ 2 ≤ quadForm H w :=
  quadForm_ge_of_gershgorin_on b H hsym {i | m ≤ i} d r (fun i hi => hdiag i hi)
    (fun i hi S hS hiS => hrow i hi S (fun _ hj => hS hj) hiS) (fun i hi => hgap i hi) w hw

/-! ## 3. The Schur test: the coupling across the split -/

/-- **The Schur test on the off-diagonal block.**  If every row sum and every column sum of
the block `{i < m} × {m ≤ j}` is at most `ε`, the coupling of the two blocks is bounded by
`ε‖x‖‖w‖`. -/
theorem abs_inner_block_le (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    {m : ℕ} {eps : ℝ}
    (hrow : ∀ i, i < m → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) →
      ∑ j ∈ S, ‖entry b H i j‖ ≤ eps)
    (hcol : ∀ j, m ≤ j → ∀ S : Finset ℕ, (∀ i ∈ S, i < m) →
      ∑ i ∈ S, ‖entry b H i j‖ ≤ eps)
    (x w : finiteModeDomain b) (hx : (x : F) ∈ galerkinSpan b m)
    (hw : (w : F) ∈ tailSpan b m) :
    ‖(inner ℂ (x : F) (H w) : ℂ)‖ ≤ eps * ‖(x : F)‖ * ‖(w : F)‖ := by
  classical
  rcases eq_or_ne ((x : F)) 0 with hx0 | hxne
  · simp [hx0]
  rcases eq_or_ne ((w : F)) 0 with hw0 | hwne
  · have hwz : w = 0 := Subtype.ext hw0
    simp [hwz]
  obtain ⟨S, cx, hSsub, hxc⟩ := exists_repr_of_mem_span_image b {i | i < m} hx
  obtain ⟨T, cw, hTsub, hwc⟩ := exists_repr_of_mem_span_image b {j | m ≤ j} hw
  have hwsum : w = ∑ j ∈ T, cw j • bvec b j := by
    refine Subtype.ext ?_
    rw [hwc]
    push_cast
    rfl
  set A : ℕ → ℕ → ℝ := fun i j => ‖entry b H i j‖ with hA
  set X : ℝ := ‖(x : F)‖ with hX
  set W : ℝ := ‖(w : F)‖ with hW
  have hXpos : 0 < X := norm_pos_iff.mpr hxne
  have hWpos : 0 < W := norm_pos_iff.mpr hwne
  have hXsq : X ^ 2 = ∑ i ∈ S, ‖cx i‖ ^ 2 := by rw [hX, hxc]; exact norm_sq_sum b S cx
  have hWsq : W ^ 2 = ∑ j ∈ T, ‖cw j‖ ^ 2 := by rw [hW, hwc]; exact norm_sq_sum b T cw
  -- the pairing, in matrix elements
  have hpair : (inner ℂ (x : F) (H w) : ℂ)
      = ∑ i ∈ S, ∑ j ∈ T, (starRingEnd ℂ) (cx i) * cw j * entry b H i j := by
    rw [hxc, hwsum]
    exact inner_sum_apply_sum b H S T cx cw
  -- the triangle inequality
  have hbound1 : ‖(inner ℂ (x : F) (H w) : ℂ)‖
      ≤ ∑ i ∈ S, ∑ j ∈ T, ‖cx i‖ * ‖cw j‖ * A i j := by
    rw [hpair]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    simp [hA]
  -- the two Schur sums
  set P : ℝ := ∑ i ∈ S, ∑ j ∈ T, A i j * ‖cx i‖ ^ 2 with hPdef
  set Q : ℝ := ∑ i ∈ S, ∑ j ∈ T, A i j * ‖cw j‖ ^ 2 with hQdef
  have hP : P ≤ eps * X ^ 2 := by
    rw [hPdef, hXsq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact hrow i (hSsub hi) T (fun j hj => hTsub hj)
  have hQ : Q ≤ eps * W ^ 2 := by
    rw [hQdef, Finset.sum_comm, hWsq, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact hcol j (hTsub hj) S (fun i hi => hSsub hi)
  -- the weighted arithmetic–geometric mean, with the optimal weight
  set t : ℝ := W / X with ht
  have htpos : 0 < t := div_pos hWpos hXpos
  set t2 : ℝ := t / 2 with ht2
  set s2 : ℝ := t⁻¹ / 2 with hs2
  have hterm : ∀ i j, ‖cx i‖ * ‖cw j‖ * A i j
      ≤ t2 * (A i j * ‖cx i‖ ^ 2) + s2 * (A i j * ‖cw j‖ ^ 2) := by
    intro i j
    have hA0 : 0 ≤ A i j := norm_nonneg _
    have hkey : 2 * (‖cx i‖ * ‖cw j‖) ≤ t * ‖cx i‖ ^ 2 + t⁻¹ * ‖cw j‖ ^ 2 := by
      have h0 : 0 ≤ (t * ‖cx i‖ - ‖cw j‖) ^ 2 := sq_nonneg _
      have hid : t * (t * ‖cx i‖ ^ 2 + t⁻¹ * ‖cw j‖ ^ 2 - 2 * (‖cx i‖ * ‖cw j‖))
          = (t * ‖cx i‖ - ‖cw j‖) ^ 2 := by
        field_simp
        ring
      nlinarith [htpos, h0, hid]
    have hmul := mul_le_mul_of_nonneg_left hkey hA0
    rw [ht2, hs2]
    nlinarith [hmul]
  have hsum : ∑ i ∈ S, ∑ j ∈ T, ‖cx i‖ * ‖cw j‖ * A i j
      ≤ ∑ i ∈ S, ∑ j ∈ T, (t2 * (A i j * ‖cx i‖ ^ 2) + s2 * (A i j * ‖cw j‖ ^ 2)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  have hsplit : ∑ i ∈ S, ∑ j ∈ T, (t2 * (A i j * ‖cx i‖ ^ 2) + s2 * (A i j * ‖cw j‖ ^ 2))
      = t2 * P + s2 * Q := by
    rw [hPdef, hQdef, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hfinal : t2 * (eps * X ^ 2) + s2 * (eps * W ^ 2) = eps * X * W := by
    rw [ht2, hs2, ht]
    field_simp
    ring
  have hlast : t2 * P + s2 * Q ≤ eps * X * W := by
    rw [← hfinal]
    have h1 : t2 * P ≤ t2 * (eps * X ^ 2) :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    have h2 : s2 * Q ≤ s2 * (eps * W ^ 2) :=
      mul_le_mul_of_nonneg_left hQ (by positivity)
    linarith
  calc ‖(inner ℂ (x : F) (H w) : ℂ)‖
      ≤ ∑ i ∈ S, ∑ j ∈ T, ‖cx i‖ * ‖cw j‖ * A i j := hbound1
    _ ≤ ∑ i ∈ S, ∑ j ∈ T, (t2 * (A i j * ‖cx i‖ ^ 2) + s2 * (A i j * ‖cw j‖ ^ 2)) := hsum
    _ = t2 * P + s2 * Q := hsplit
    _ ≤ eps * X * W := hlast

/-- **The coupling bound of the lift, from the entries** — the second analytic input of
`TruncationGapLift.gap_of_level_gap_and_tail`. -/
theorem coupling_bound_of_schur (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    {m : ℕ} {eps : ℝ}
    (hrow : ∀ i, i < m → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) →
      ∑ j ∈ S, ‖entry b H i j‖ ≤ eps)
    (hcol : ∀ j, m ≤ j → ∀ S : Finset ℕ, (∀ i ∈ S, i < m) →
      ∑ i ∈ S, ‖entry b H i j‖ ≤ eps)
    (x w : finiteModeDomain b) (hx : (x : F) ∈ galerkinSpan b m)
    (hw : (w : F) ∈ tailSpan b m) :
    |(inner ℂ (x : F) (H w) : ℂ).re| ≤ eps * ‖(x : F)‖ * ‖(w : F)‖ :=
  (Complex.abs_re_le_norm _).trans (abs_inner_block_le b H hrow hcol x w hx hw)

/-! ## 4. The composed criterion -/

/-- **The certified truncated gap plus checkable matrix data give the core form gap.** -/
theorem gap_of_level_gap_and_matrix_bounds (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn _ H) {m : ℕ} {mu eps : ℝ}
    (heps : 0 ≤ eps) (d r : ℕ → ℝ)
    (htrunc : ∀ x : finiteModeDomain b, (x : F) ∈ galerkinSpan b m →
      mu * ‖(x : F)‖ ^ 2 ≤ quadForm H x)
    (hdiag : ∀ i, m ≤ i → d i ≤ (entry b H i i).re)
    (hrow : ∀ i, m ≤ i → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) → i ∉ S →
      ∑ j ∈ S, ‖entry b H i j‖ ≤ r i)
    (hgap : ∀ i, m ≤ i → mu ≤ d i - r i)
    (hblockrow : ∀ i, i < m → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) →
      ∑ j ∈ S, ‖entry b H i j‖ ≤ eps)
    (hblockcol : ∀ j, m ≤ j → ∀ S : Finset ℕ, (∀ i ∈ S, i < m) →
      ∑ i ∈ S, ‖entry b H i j‖ ≤ eps)
    (v : finiteModeDomain b) : (mu - eps) * ‖(v : F)‖ ^ 2 ≤ quadForm H v :=
  gap_of_level_gap_and_tail b H hsym heps htrunc
    (tail_coercive_of_gershgorin b H hsym d r hdiag hrow hgap)
    (fun x w hx hw => coupling_bound_of_schur b H hblockrow hblockcol x w hx hw) v

/-- **QYM-1 task 3, in the form the chain consumes.**  With `ε < μ` the matrix data give
*strict* positivity of the one-particle energy on the core: `λ₁(H₁|core) ≥ μ − ε > 0`. -/
theorem strict_pos_of_matrix_bounds (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn _ H) {m : ℕ} {mu eps : ℝ}
    (heps : 0 ≤ eps) (hlt : eps < mu) (d r : ℕ → ℝ)
    (htrunc : ∀ x : finiteModeDomain b, (x : F) ∈ galerkinSpan b m →
      mu * ‖(x : F)‖ ^ 2 ≤ quadForm H x)
    (hdiag : ∀ i, m ≤ i → d i ≤ (entry b H i i).re)
    (hrow : ∀ i, m ≤ i → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) → i ∉ S →
      ∑ j ∈ S, ‖entry b H i j‖ ≤ r i)
    (hgap : ∀ i, m ≤ i → mu ≤ d i - r i)
    (hblockrow : ∀ i, i < m → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) →
      ∑ j ∈ S, ‖entry b H i j‖ ≤ eps)
    (hblockcol : ∀ j, m ≤ j → ∀ S : Finset ℕ, (∀ i ∈ S, i < m) →
      ∑ i ∈ S, ‖entry b H i j‖ ≤ eps)
    (v : finiteModeDomain b) (hv : (v : F) ≠ 0) : 0 < quadForm H v := by
  have hle := gap_of_level_gap_and_matrix_bounds b H hsym heps d r htrunc hdiag hrow hgap
    hblockrow hblockcol v
  have hpos : 0 < ‖(v : F)‖ ^ 2 := by
    have := norm_pos_iff.mpr hv
    positivity
  nlinarith

/-! ## 5. The Yang–Mills instantiation -/

variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)


/-- **The conditional Yang–Mills nested-Fock mass gap from matrix-element data.** -/
theorem ym_fock_mass_gap_of_truncated_gap_and_matrix_bounds {m : ℕ} {mu eps : ℝ}
    (heps : 0 ≤ eps) (hmueps : eps < mu) (d r : ℕ → ℝ)
    (htrunc : ∀ x : finiteModeDomain (coreBasis e),
      (x : L2d 99) ∈ galerkinSpan (coreBasis e) m →
      mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x)
    (hdiag : ∀ i, m ≤ i →
      d i ≤ (entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i i).re)
    (hrow : ∀ i, m ≤ i → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) → i ∉ S →
      ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ r i)
    (hgap : ∀ i, m ≤ i → mu ≤ d i - r i)
    (hblockrow : ∀ i, i < m → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) →
      ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ eps)
    (hblockcol : ∀ j, m ≤ j → ∀ S : Finset ℕ, (∀ i ∈ S, i < m) →
      ∑ i ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ eps) :
    (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
        IsPositiveSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) A) ∧
      dGamma (ymFockCol e fabc) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 → u ≠ 0 →
        0 < (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re :=
  ym_fock_mass_gap_of_one_particle_form_gap e fabc (by linarith)
    (gap_of_level_gap_and_matrix_bounds (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc)
      (ymHamiltonian_symmetricOn (coreRepBasis e) fabc) heps d r htrunc hdiag hrow hgap
      hblockrow hblockcol)

/-! ## 6. Axiom audit -/

section Audit

#print axioms entry_conj
#print axioms norm_entry_symm
#print axioms exists_repr_of_mem_span_image
#print axioms norm_sq_sum
#print axioms inner_sum_apply_sum
#print axioms quadForm_sum
#print axioms sum_off_diag_comm
#print axioms quadForm_sum_ge
#print axioms quadForm_ge_of_gershgorin_on
#print axioms quadForm_ge_of_gershgorin
#print axioms tail_coercive_of_gershgorin
#print axioms abs_inner_block_le
#print axioms coupling_bound_of_schur
#print axioms gap_of_level_gap_and_matrix_bounds
#print axioms strict_pos_of_matrix_bounds
#print axioms ym_fock_mass_gap_of_truncated_gap_and_matrix_bounds

end Audit

end BookProof.SchurGershgorin

end


