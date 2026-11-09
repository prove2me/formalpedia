-- Prove2me | Definitions.Def_ChapterFockSchurEsa
-- name    : ChapterFockSchurEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-08T07:50:46.298246+00:00
-- url     : https://prove2.me/theorems/5ac859d2-f2c3-470d-a0c2-ead29eb6aad3
-- title:
--   ChapterFockSchurEsa
-- statement:
--   ChapterFockSchurEsa

import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosure
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Theorems.Thm_BookProof_FockSecondQuantization_support_up
import Theorems.Thm_BookProof_FockSecondQuantization_support_dn
import Theorems.Thm_BookProof_FockSecondQuantization_dn_of_ne
import Theorems.Thm_BookProof_FockSecondQuantization_annA_apply
import Theorems.Thm_BookProof_FockSecondQuantization_creA_apply
import Theorems.Thm_BookProof_FockSecondQuantization_creVec_apply
import Theorems.Thm_BookProof_FockSecondQuantization_dGamma_eq_sum
import Theorems.Thm_BookProof_FockSecondQuantization_inner_toLp_of_subset
import Definitions.Def_ChapterDegKatoEsa
import Theorems.Thm_BookProof_FockSecondQuantization_up_dn
import Theorems.Thm_BookProof_FockSecondQuantization_support_subset_modes
import Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_left
import Theorems.Thm_BookProof_FockSecondQuantization_modes_left_subset_closure
import Theorems.Thm_BookProof_FockSecondQuantization_modes_right_subset_closure
import Theorems.Thm_BookProof_FockSecondQuantization_toLpL_apply
import Theorems.Thm_BookProof_FockSecondQuantization_coe_fockEquiv_symm
import Theorems.Thm_BookProof_FockSecondQuantization_coe_dGammaOp
import Theorems.Thm_BookProof_FockSecondQuantization_dGammaOp_symmetricOn
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Theorems.Thm_BookProof_EsaClosure_positiveExtension_eq_closure_of_esa
import Theorems.Thm_BookProof_FockSecondQuantization_col_support_subset_closure
import Theorems.Thm_BookProof_FockSecondQuantization_finiteOccupation_dense
import Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_symm
import Theorems.Thm_BookProof_FockSecondQuantization_inner_toLp
import Theorems.Thm_BookProof_FockSecondQuantization_support_annA
import Theorems.Thm_BookProof_FockSecondQuantization_up_of_ne
import Theorems.Thm_BookProof_FockSecondQuantization_up_self
import Theorems.Thm_BookProof_FockSecondQuantization_dn_self
import Theorems.Thm_BookProof_FockSecondQuantization_dn_up


/-!
# `dΓ(A)` for a Schur-class one-particle matrix: the number bound and essential
# self-adjointness on the finite-occupation core

`BookProof.ChapterFockDifferingBasesEsa` proves essential self-adjointness of a second
quantized Hamiltonian under the **unweighted `ℓ¹` gate** `∑ₖ ‖gₖ‖ < ∞` on its matrix
elements — a genuine restriction: a one-particle operator as simple as the
nearest-neighbour hopping `A_{jk} = 1` for `|j − k| = 1` has infinitely many entries of
modulus one and is not covered.

The gate that the physics actually asks for is the **Schur bound**

```text
∀ k, ∑_j |⟪e_j, A e_k⟫| ≤ K,
```

the classical criterion for boundedness of the one-particle operator `A`.  This module
proves that under that gate alone the second quantization `dΓ(A)` of
`BookProof.ChapterFockSecondQuantization` obeys the **number bound**

```text
‖dΓ(A) u‖ ≤ K ‖𝒩 u‖
```

on the finite-occupation core, that it **conserves the particle number** exactly, and
that it is therefore essentially self-adjoint there — with no diagonalizing basis and no
summability of the entries.

## What is proved

* `ndeg`, `numSym`, `InSector` — the particle number of a configuration, the comparison
  symbol `σ(α) = |α| + 1` and the sectors of the Fock space.
* `annA_inSector`, `creA_inSector`, `dGamma_inSector` — the ladder operators shift the
  sector by one, so `dΓ(A)` **preserves** it: second quantization conserves the particle
  number.
* `sum_normSq_annA` — `∑ₖ ‖a_k u‖² = ⟪u, 𝒩u⟫`, the identity behind the number bound.
* `schur_test` — the elementary (finite) Schur test `∑_{k,j} |A_{kj}| x_k y_j ≤ K‖x‖‖y‖`.
* **`norm_dGamma_le_of_sector`** — on the `n`-particle sector, `‖dΓ(A)u‖ ≤ K n ‖u‖`.
* **`norm_dGamma_le`** — hence `‖dΓ(A)u‖ ≤ K‖𝒩u‖` on the whole core, by orthogonality of
  the sectors.
* **`dGamma_essentiallySelfAdjointOn_core`** — the headline: for a Hermitian
  column-finite matrix with a Schur bound, `dΓ(A)` is essentially self-adjoint on the
  finite-occupation core, through
  `BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm`.
* `dGamma_stone_flow`, `dGamma_positiveExtension_eq_closure` — the unique self-adjoint
  realization, its unitary group (Stone), and — for a positive matrix — the identification
  of the Friedrichs extension with the closure.
* `hopCol`, `isHermCol_hopCol`, `schurBound_hopCol`, `hopCol_not_summable`,
  **`hop_essentiallySelfAdjointOn_core`** — non-vacuity: the nearest-neighbour hopping
  matrix satisfies the Schur gate with `K = 2` while its entries are *not* summable, so
  the statement is strictly outside the `ℓ¹` gate of `ChapterFockDifferingBasesEsa`.

## Honest boundary

The one-particle matrix must be **column-finite** (each `A e_k` a finite combination of
basis states) — that is what makes `dΓ(A)` map the finite-occupation core into itself —
and Hermitian, and it must satisfy the Schur bound, which forces `A` itself to be
*bounded*.  Nothing here covers an unbounded one-particle operator: for those the number
operator is not a comparison operator and `dΓ` needs a different gate.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.FockSecondQuantization
open BookProof.DegKatoEsa

end BookProof.FockSecondQuantization

namespace BookProof.FockSchur

open BookProof.FockSecondQuantization BookProof.CoreBounds
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.YangMillsFriedrichs

noncomputable section

/-! ## 1. Particle number and sectors -/

/-- The **particle number** `|α| = ∑ᵢ αᵢ` of a configuration. -/
def ndeg (α : Conf) : ℕ := α.sum fun _ n => n

/-- The comparison symbol `σ(α) = |α| + 1`: the number operator plus one. -/
def numSym (α : Conf) : ℝ := (ndeg α : ℝ) + 1

theorem numSym_nonneg (α : Conf) : 0 ≤ numSym α := by
  have : (0:ℝ) ≤ (ndeg α : ℝ) := Nat.cast_nonneg _
  simp only [numSym]; linarith

/-- The particle number as a finite sum over any set of modes containing the support. -/
theorem ndeg_eq_sum {α : Conf} {S : Finset ℕ} (h : α.support ⊆ S) : ndeg α = ∑ i ∈ S, α i :=
  Finsupp.sum_of_support_subset α h _ (by simp)

theorem up_apply' (j : ℕ) (α : Conf) (i : ℕ) : up j α i = α i + if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp [up_self]
  · simp [up_of_ne _ h, h]

theorem ndeg_up (j : ℕ) (α : Conf) : ndeg (up j α) = ndeg α + 1 := by
  classical
  have h1 : (up j α).support ⊆ insert j α.support := support_up j α
  have h2 : α.support ⊆ insert j α.support := Finset.subset_insert _ _
  rw [ndeg_eq_sum h1, ndeg_eq_sum h2,
    Finset.sum_congr rfl (fun i _ => up_apply' j α i), Finset.sum_add_distrib]
  congr 1
  simp

theorem ndeg_dn (j : ℕ) {α : Conf} (h : 1 ≤ α j) : ndeg (dn j α) + 1 = ndeg α := by
  classical
  have hj : j ∈ α.support := Finsupp.mem_support_iff.mpr (by omega)
  have h1 : (dn j α).support ⊆ α.support := support_dn j α
  rw [ndeg_eq_sum h1, ndeg_eq_sum (Finset.Subset.refl α.support),
    ← Finset.add_sum_erase _ (fun i => (dn j α) i) hj,
    ← Finset.add_sum_erase _ (fun i => α i) hj]
  have hoff : ∀ i ∈ α.support.erase j, dn j α i = α i := fun i hi =>
    dn_of_ne _ (Finset.ne_of_mem_erase hi)
  rw [Finset.sum_congr rfl hoff, dn_self]
  have heq : (α.support.erase j).sum ⇑α = ∑ x ∈ α.support.erase j, α x := rfl
  omega

theorem ndeg_eq_zero_iff {α : Conf} : ndeg α = 0 ↔ α = 0 := by
  classical
  constructor
  · intro h
    ext i
    have hsum : ∑ i ∈ α.support, α i = 0 := by
      rw [← ndeg_eq_sum (Finset.Subset.refl α.support), h]
    by_cases hi : i ∈ α.support
    · simp [(Finset.sum_eq_zero_iff.mp hsum) i hi]
    · simp [Finsupp.notMem_support_iff.mp hi]
  · intro h; subst h; simp [ndeg]

/-- A state of the **`n`-particle sector**: every configuration it excites has `n`
quanta. -/
def InSector (n : ℕ) (u : FockAlg) : Prop := ∀ α ∈ u.support, ndeg α = n

theorem inSector_zero_op (n : ℕ) : InSector n (0 : FockAlg) := by
  intro α hα; simp at hα

theorem inSector_add {n : ℕ} {u v : FockAlg} (hu : InSector n u) (hv : InSector n v) :
    InSector n (u + v) := by
  intro α hα
  rcases Finset.mem_union.mp (Finsupp.support_add hα) with h | h
  · exact hu α h
  · exact hv α h

theorem inSector_smul {n : ℕ} {u : FockAlg} (c : ℂ) (hu : InSector n u) :
    InSector n (c • u) := fun α hα => hu α (Finsupp.support_smul hα)

theorem inSector_sum {n : ℕ} {κ : Type*} (S : Finset κ) (f : κ → FockAlg)
    (hf : ∀ k ∈ S, InSector n (f k)) : InSector n (∑ k ∈ S, f k) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using inSector_zero_op n
  | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      exact inSector_add (hf a (Finset.mem_insert_self a S))
        (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

theorem annA_inSector {n : ℕ} {u : FockAlg} (hu : InSector (n + 1) u) (j : ℕ) :
    InSector n (annA j u) := by
  intro α hα
  have hne : (annA j u) α ≠ 0 := Finsupp.mem_support_iff.mp hα
  rw [annA_apply] at hne
  have hu' : u (up j α) ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have := hu _ (Finsupp.mem_support_iff.mpr hu')
  rw [ndeg_up] at this
  omega

theorem creA_inSector {n : ℕ} {u : FockAlg} (hu : InSector n u) (j : ℕ) :
    InSector (n + 1) (creA j u) := by
  intro α hα
  have hne : (creA j u) α ≠ 0 := Finsupp.mem_support_iff.mp hα
  rw [creA_apply] at hne
  have hj : α j ≠ 0 := by
    intro h
    rw [h] at hne
    simp at hne
  have hu' : u (dn j α) ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have hd := hu _ (Finsupp.mem_support_iff.mpr hu')
  have := ndeg_dn j (α := α) (by omega)
  omega

theorem creVec_inSector {n : ℕ} {u : FockAlg} (hu : InSector n u) (v : ℕ →₀ ℂ) :
    InSector (n + 1) (creVec v u) := by
  rw [creVec_apply]
  exact inSector_sum _ _ fun j _ => inSector_smul _ (creA_inSector hu j)

theorem annA_eq_zero_of_inSector_zero {u : FockAlg} (hu : InSector 0 u) (j : ℕ) :
    annA j u = 0 := by
  refine Finsupp.ext fun α => ?_
  rw [annA_apply]
  have hz : u (up j α) = 0 := by
    by_contra hc
    have := hu _ (Finsupp.mem_support_iff.mpr hc)
    rw [ndeg_up] at this
    omega
  rw [hz, mul_zero]
  simp

/-- **Second quantization conserves the particle number.** -/
theorem dGamma_inSector (col : ℕ → (ℕ →₀ ℂ)) {n : ℕ} {u : FockAlg} (hu : InSector n u) :
    InSector n (dGamma col u) := by
  classical
  rw [dGamma_eq_sum col (Finset.Subset.refl (modes u))]
  cases n with
  | zero =>
      refine inSector_sum _ _ fun k _ => ?_
      rw [annA_eq_zero_of_inSector_zero hu k, map_zero]
      exact inSector_zero_op 0
  | succ m =>
      exact inSector_sum _ _ fun k _ => creVec_inSector (annA_inSector hu k) (col k)

/-! ## 2. Norms of finitely supported states -/

theorem normSq_toLp_of_subset {u : FockAlg} {S : Finset Conf} (hs : u.support ⊆ S) :
    ‖toLp u‖ ^ 2 = ∑ α ∈ S, ‖u α‖ ^ 2 := by
  have h := inner_toLp_of_subset hs u
  have hnorm : (inner ℂ (toLp u) (toLp u) : ℂ) = ((‖toLp u‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hnorm] at h
  have h2 : ∀ α : Conf, (starRingEnd ℂ) (u α) * u α = ((‖u α‖ ^ 2 : ℝ) : ℂ) := by
    intro α
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl (fun α _ => h2 α)] at h
  exact_mod_cast h

theorem normSq_toLp (u : FockAlg) : ‖toLp u‖ ^ 2 = ∑ α ∈ u.support, ‖u α‖ ^ 2 :=
  normSq_toLp_of_subset (Finset.Subset.refl _)

/-- States of different sectors are orthogonal. -/
theorem inner_toLp_eq_zero_of_ne_sector {n m : ℕ} {u v : FockAlg} (hu : InSector n u)
    (hv : InSector m v) (hnm : n ≠ m) : (inner ℂ (toLp u) (toLp v) : ℂ) = 0 := by
  rw [inner_toLp]
  refine Finset.sum_eq_zero fun α hα => ?_
  have hvz : v α = 0 := by
    by_contra hc
    have h1 := hu α hα
    have h2 := hv α (Finsupp.mem_support_iff.mpr hc)
    exact hnm (h1 ▸ h2 ▸ rfl)
  rw [hvz, mul_zero]

/-- **`∑ₖ ‖a_k u‖² = ⟪u, 𝒩u⟫`.** -/
theorem normSq_annA (k : ℕ) (u : FockAlg) :
    ‖toLp (annA k u)‖ ^ 2 = ∑ α ∈ u.support, ((α k : ℝ)) * ‖u α‖ ^ 2 := by
  classical
  set T : Finset Conf := u.support.filter (fun β => 1 ≤ β k) with hT
  set f : Conf → ℝ := fun α => ((α k : ℝ) + 1) * ‖u (up k α)‖ ^ 2 with hf
  have hsupp : (annA k u).support ⊆ u.support.image (dn k) := support_annA k u
  have h1 : ‖toLp (annA k u)‖ ^ 2 = ∑ α ∈ u.support.image (dn k), f α := by
    rw [normSq_toLp_of_subset hsupp]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [annA_apply, hf]
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  have hTsub : T.image (dn k) ⊆ u.support.image (dn k) :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have h2 : ∑ α ∈ u.support.image (dn k), f α = ∑ α ∈ T.image (dn k), f α := by
    refine (Finset.sum_subset hTsub ?_).symm
    intro α _ hα
    have hz : u (up k α) = 0 := by
      by_contra hc
      refine hα (Finset.mem_image.mpr ⟨up k α, ?_, dn_up k α⟩)
      refine Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hc, ?_⟩
      rw [up_self]; omega
    rw [hf]
    simp [hz]
  have hinj : ∀ x ∈ T, ∀ y ∈ T, dn k x = dn k y → x = y := by
    intro x hx y hy hxy
    have hx1 : 1 ≤ x k := (Finset.mem_filter.mp hx).2
    have hy1 : 1 ≤ y k := (Finset.mem_filter.mp hy).2
    rw [← up_dn k hx1, ← up_dn k hy1, hxy]
  have h3 : ∑ α ∈ T.image (dn k), f α = ∑ β ∈ T, f (dn k β) := Finset.sum_image hinj
  have h4 : ∑ β ∈ T, f (dn k β) = ∑ β ∈ T, ((β k : ℝ)) * ‖u β‖ ^ 2 := by
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hb1 : 1 ≤ β k := (Finset.mem_filter.mp hβ).2
    rw [hf]
    simp only
    rw [up_dn k hb1, dn_self]
    congr 1
    rw [Nat.cast_sub hb1]
    ring
  have h5 : ∑ β ∈ T, ((β k : ℝ)) * ‖u β‖ ^ 2 = ∑ β ∈ u.support, ((β k : ℝ)) * ‖u β‖ ^ 2 := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro β hβu hβ
    have hz : β k = 0 := by
      by_contra hc
      exact hβ (Finset.mem_filter.mpr ⟨hβu, by omega⟩)
    simp [hz]
  rw [h1, h2, h3, h4, h5]

/-- Summing over the modes gives the number operator. -/
theorem sum_normSq_annA {u : FockAlg} {L : Finset ℕ} (hL : modes u ⊆ L) :
    ∑ k ∈ L, ‖toLp (annA k u)‖ ^ 2 = ∑ α ∈ u.support, (ndeg α : ℝ) * ‖u α‖ ^ 2 := by
  classical
  rw [Finset.sum_congr rfl (fun k _ => normSq_annA k u), Finset.sum_comm]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hsub : α.support ⊆ L := fun i hi => hL (support_subset_modes hα hi)
  rw [← Finset.sum_mul, ndeg_eq_sum hsub]
  push_cast
  ring

theorem sum_normSq_annA_of_sector {n : ℕ} {u : FockAlg} (hu : InSector n u) {L : Finset ℕ}
    (hL : modes u ⊆ L) : ∑ k ∈ L, ‖toLp (annA k u)‖ ^ 2 = (n : ℝ) * ‖toLp u‖ ^ 2 := by
  rw [sum_normSq_annA hL, normSq_toLp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α hα => by rw [hu α hα]

/-! ## 3. The Schur test -/

/-- The **Schur gate**: the columns of the one-particle matrix are uniformly summable. -/
def SchurBound (col : ℕ → (ℕ →₀ ℂ)) (K : ℝ) : Prop :=
  ∀ k, ∑ j ∈ (col k).support, ‖(col k) j‖ ≤ K

theorem sum_norm_col_le {col : ℕ → (ℕ →₀ ℂ)} {K : ℝ} (hK : SchurBound col K) (k : ℕ)
    (L : Finset ℕ) : ∑ j ∈ L, ‖(col k) j‖ ≤ K := by
  classical
  have h1 : ∑ j ∈ L, ‖(col k) j‖ = ∑ j ∈ L ∩ (col k).support, ‖(col k) j‖ := by
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro j hj hjn
    have hz : (col k) j = 0 := by
      by_contra hc
      exact hjn (Finset.mem_inter.mpr ⟨hj, Finsupp.mem_support_iff.mpr hc⟩)
    simp [hz]
  rw [h1]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right ?_) (hK k)
  intro j _ _
  exact norm_nonneg _

/-- **The Schur test** (finite form): a non-negative matrix with row and column sums
bounded by `K` defines a bilinear form bounded by `K` times the two `ℓ²` norms. -/
theorem schur_test {L : Finset ℕ} {m : ℕ → ℕ → ℝ} {x y : ℕ → ℝ} {K : ℝ}
    (hm : ∀ k j, 0 ≤ m k j) (hx : ∀ k, 0 ≤ x k) (hy : ∀ j, 0 ≤ y j) (hK0 : 0 ≤ K)
    (hrow : ∀ k, ∑ j ∈ L, m k j ≤ K) (hcol : ∀ j, ∑ k ∈ L, m k j ≤ K) :
    ∑ k ∈ L, ∑ j ∈ L, m k j * (x k * y j)
      ≤ K * (Real.sqrt (∑ k ∈ L, x k ^ 2) * Real.sqrt (∑ j ∈ L, y j ^ 2)) := by
  classical
  set A : ℝ := ∑ k ∈ L, x k ^ 2 with hAdef
  set B : ℝ := ∑ j ∈ L, y j ^ 2 with hBdef
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun j _ => sq_nonneg _
  set S : ℝ := ∑ k ∈ L, ∑ j ∈ L, m k j * (x k * y j) with hSdef
  have hSnn : 0 ≤ S :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hm k j) (mul_nonneg (hx k) (hy j))
  set a : ℕ × ℕ → ℝ := fun p => Real.sqrt (m p.1 p.2) * x p.1 with hadef
  set b : ℕ × ℕ → ℝ := fun p => Real.sqrt (m p.1 p.2) * y p.2 with hbdef
  have hprod : S = ∑ p ∈ L ×ˢ L, a p * b p := by
    rw [hSdef, Finset.sum_product]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    have hsq : Real.sqrt (m k j) * Real.sqrt (m k j) = m k j := Real.mul_self_sqrt (hm k j)
    simp only [hadef, hbdef]
    rw [show (Real.sqrt (m k j) * x k) * (Real.sqrt (m k j) * y j)
        = (Real.sqrt (m k j) * Real.sqrt (m k j)) * (x k * y j) from by ring, hsq]
  have hAsum : ∑ p ∈ L ×ˢ L, a p ^ 2 ≤ K * A := by
    have hstep : ∑ p ∈ L ×ˢ L, a p ^ 2 = ∑ k ∈ L, (x k ^ 2 * ∑ j ∈ L, m k j) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsq : Real.sqrt (m k j) ^ 2 = m k j := Real.sq_sqrt (hm k j)
      simp only [hadef]
      rw [mul_pow, hsq]
      ring
    rw [hstep, hAdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [mul_comm K (x k ^ 2)]
    exact mul_le_mul_of_nonneg_left (hrow k) (sq_nonneg _)
  have hBsum : ∑ p ∈ L ×ˢ L, b p ^ 2 ≤ K * B := by
    have hstep : ∑ p ∈ L ×ˢ L, b p ^ 2 = ∑ j ∈ L, (y j ^ 2 * ∑ k ∈ L, m k j) := by
      rw [Finset.sum_product_right]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsq : Real.sqrt (m k j) ^ 2 = m k j := Real.sq_sqrt (hm k j)
      simp only [hbdef]
      rw [mul_pow, hsq]
      ring
    rw [hstep, hBdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_comm K (y j ^ 2)]
    exact mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg _)
  have hCS : S ^ 2 ≤ (∑ p ∈ L ×ˢ L, a p ^ 2) * (∑ p ∈ L ×ˢ L, b p ^ 2) := by
    rw [hprod]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ a b
  have hAnn' : (0:ℝ) ≤ ∑ p ∈ L ×ˢ L, a p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hBnn' : (0:ℝ) ≤ ∑ p ∈ L ×ˢ L, b p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hS2 : S ^ 2 ≤ (K * A) * (K * B) := by
    refine hCS.trans ?_
    exact mul_le_mul hAsum hBsum hBnn' (le_trans hAnn' hAsum)
  have hRnn : 0 ≤ K * (Real.sqrt A * Real.sqrt B) :=
    mul_nonneg hK0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hR2 : (K * (Real.sqrt A * Real.sqrt B)) ^ 2 = (K * A) * (K * B) := by
    have h1 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hAnn
    have h2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hBnn
    rw [show (K * (Real.sqrt A * Real.sqrt B)) ^ 2
        = K ^ 2 * (Real.sqrt A ^ 2 * Real.sqrt B ^ 2) from by ring, h1, h2]
    ring
  nlinarith [hS2, hR2, hSnn, hRnn]

/-! ## 4. The number bound -/

variable {col : ℕ → (ℕ →₀ ℂ)} {K : ℝ}

/-- **The number bound on one sector**: on the `n`-particle sector `dΓ(A)` is bounded by
`K n`. -/
theorem norm_dGamma_le_of_sector (hK : SchurBound col K) (hherm : IsHermCol col) (hK0 : 0 ≤ K)
    {n : ℕ} {u : FockAlg} (hu : InSector n u) :
    ‖toLp (dGamma col u)‖ ≤ K * n * ‖toLp u‖ := by
  classical
  set v : FockAlg := dGamma col u with hv
  have hvsec : InSector n v := dGamma_inSector col hu
  set L : Finset ℕ := closureModes col u v with hLdef
  have hexp : (inner ℂ (toLp v) (toLp v) : ℂ)
      = ∑ k ∈ L, ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
          * inner ℂ (toLp (annA k u)) (toLp (annA j v)) :=
    inner_dGamma_left col u v (modes_left_subset_closure col u v)
      (col_support_subset_closure col u v)
  have hbound : ‖toLp v‖ ^ 2 ≤ ∑ k ∈ L, ∑ j ∈ L,
      ‖(col k) j‖ * (‖toLp (annA k u)‖ * ‖toLp (annA j v)‖) := by
    have h0 : ((‖toLp v‖ ^ 2 : ℝ) : ℂ) = ∑ k ∈ L, ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
        * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
      rw [← hexp, inner_self_eq_norm_sq_to_K]
      norm_cast
    have h1 : ‖toLp v‖ ^ 2 = ‖(∑ k ∈ L, ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
        * inner ℂ (toLp (annA k u)) (toLp (annA j v)) : ℂ)‖ := by
      rw [← h0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [h1]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
  have hschur := schur_test (L := L) (m := fun k j => ‖(col k) j‖)
    (x := fun k => ‖toLp (annA k u)‖) (y := fun j => ‖toLp (annA j v)‖) (K := K)
    (fun k j => norm_nonneg _) (fun k => norm_nonneg _) (fun j => norm_nonneg _) hK0
    (fun k => sum_norm_col_le hK k L)
    (fun j => by
      have hcongr : ∑ k ∈ L, ‖(col k) j‖ = ∑ k ∈ L, ‖(col j) k‖ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hherm j k]
        simp
      rw [hcongr]
      exact sum_norm_col_le hK j L)
  have hsu : ∑ k ∈ L, ‖toLp (annA k u)‖ ^ 2 = (n : ℝ) * ‖toLp u‖ ^ 2 :=
    sum_normSq_annA_of_sector hu (modes_left_subset_closure col u v)
  have hsv : ∑ j ∈ L, ‖toLp (annA j v)‖ ^ 2 = (n : ℝ) * ‖toLp v‖ ^ 2 :=
    sum_normSq_annA_of_sector hvsec (modes_right_subset_closure col u v)
  have hsqrtu : Real.sqrt ((n : ℝ) * ‖toLp u‖ ^ 2) = Real.sqrt n * ‖toLp u‖ := by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (norm_nonneg _)]
  have hsqrtv : Real.sqrt ((n : ℝ) * ‖toLp v‖ ^ 2) = Real.sqrt n * ‖toLp v‖ := by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (norm_nonneg _)]
  rw [hsu, hsv, hsqrtu, hsqrtv] at hschur
  have hnn : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hkey : ‖toLp v‖ ^ 2 ≤ K * (n : ℝ) * ‖toLp u‖ * ‖toLp v‖ := by
    refine le_trans hbound (le_trans hschur (le_of_eq ?_))
    have : (Real.sqrt n * ‖toLp u‖) * (Real.sqrt n * ‖toLp v‖)
        = (Real.sqrt n * Real.sqrt n) * (‖toLp u‖ * ‖toLp v‖) := by ring
    rw [this, hnn]
    ring
  rcases eq_or_lt_of_le (norm_nonneg (toLp v)) with hz | hpos
  · rw [← hz]
    have h1 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (0:ℝ) ≤ ‖toLp u‖ := norm_nonneg _
    positivity
  · have := hkey
    nlinarith [hpos]

/-! ## 5. Sector decomposition and the number bound on the core -/

/-- The part of a state in the `n`-particle sector. -/
def sectorPart (n : ℕ) (u : FockAlg) : FockAlg := u.filter fun α => ndeg α = n

theorem sectorPart_inSector (n : ℕ) (u : FockAlg) : InSector n (sectorPart n u) := by
  classical
  intro α hα
  rw [sectorPart, Finsupp.support_filter] at hα
  exact (Finset.mem_filter.mp hα).2

theorem sectorPart_apply (n : ℕ) (u : FockAlg) (α : Conf) :
    sectorPart n u α = if ndeg α = n then u α else 0 := by
  classical
  simp [sectorPart, Finsupp.filter_apply]

theorem sum_sectorPart (u : FockAlg) :
    ∑ n ∈ u.support.image ndeg, sectorPart n u = u := by
  classical
  refine Finsupp.ext fun α => ?_
  rw [Finset.sum_apply']
  have hterm : ∀ n ∈ u.support.image ndeg,
      sectorPart n u α = if ndeg α = n then u α else 0 := fun n _ => sectorPart_apply n u α
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  by_cases hu : α ∈ u.support
  · rw [if_pos (Finset.mem_image_of_mem ndeg hu)]
  · rw [Finsupp.notMem_support_iff.mp hu]
    simp

/-- States of pairwise different sectors add in norm squared. -/
theorem normSq_sum_of_sectors {D : Finset ℕ} (f : ℕ → FockAlg)
    (hf : ∀ n ∈ D, InSector n (f n)) :
    ‖toLp (∑ n ∈ D, f n)‖ ^ 2 = ∑ n ∈ D, ‖toLp (f n)‖ ^ 2 := by
  classical
  have hmap : toLp (∑ n ∈ D, f n) = ∑ n ∈ D, toLp (f n) := by
    rw [← toLpL_apply, map_sum]
    rfl
  have hinner : (inner ℂ (toLp (∑ n ∈ D, f n)) (toLp (∑ n ∈ D, f n)) : ℂ)
      = ∑ n ∈ D, ∑ m ∈ D, (inner ℂ (toLp (f n)) (toLp (f m)) : ℂ) := by
    rw [hmap, sum_inner]
    exact Finset.sum_congr rfl fun n _ => inner_sum _ _ _
  have hdiag : ∀ n ∈ D, ∑ m ∈ D, (inner ℂ (toLp (f n)) (toLp (f m)) : ℂ)
      = ((‖toLp (f n)‖ ^ 2 : ℝ) : ℂ) := by
    intro n hn
    rw [Finset.sum_eq_single n]
    · rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    · intro m hm hmn
      exact inner_toLp_eq_zero_of_ne_sector (hf n hn) (hf m hm) (Ne.symm hmn)
    · intro hcon
      exact absurd hn hcon
  rw [Finset.sum_congr rfl hdiag] at hinner
  have hlhs : (inner ℂ (toLp (∑ n ∈ D, f n)) (toLp (∑ n ∈ D, f n)) : ℂ)
      = ((‖toLp (∑ n ∈ D, f n)‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hlhs, ← Complex.ofReal_sum] at hinner
  exact_mod_cast hinner

/-- **The number bound.**  `‖dΓ(A)u‖ ≤ K‖𝒩u‖` on the finite-occupation core. -/
theorem norm_dGamma_le (hK : SchurBound col K) (hherm : IsHermCol col) (hK0 : 0 ≤ K)
    (u : FockAlg) :
    ‖toLp (dGamma col u)‖ ^ 2 ≤ K ^ 2 * ∑ α ∈ u.support, ((ndeg α : ℝ)) ^ 2 * ‖u α‖ ^ 2 := by
  classical
  set D : Finset ℕ := u.support.image ndeg with hD
  have hsplit : dGamma col u = ∑ n ∈ D, dGamma col (sectorPart n u) := by
    conv_lhs => rw [← sum_sectorPart u]
    rw [map_sum]
  have hsec : ∀ n ∈ D, InSector n (dGamma col (sectorPart n u)) := fun n _ =>
    dGamma_inSector col (sectorPart_inSector n u)
  rw [hsplit, normSq_sum_of_sectors _ hsec]
  have hterm : ∀ n ∈ D, ‖toLp (dGamma col (sectorPart n u))‖ ^ 2
      ≤ K ^ 2 * ((n : ℝ) ^ 2 * ‖toLp (sectorPart n u)‖ ^ 2) := by
    intro n _
    have h := norm_dGamma_le_of_sector hK hherm hK0 (sectorPart_inSector n u)
    have h0 : 0 ≤ ‖toLp (dGamma col (sectorPart n u))‖ := norm_nonneg _
    have h1 : 0 ≤ ‖toLp (sectorPart n u)‖ := norm_nonneg _
    nlinarith [h, h0, h1]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (sq_nonneg K)
  have hnorm : ∀ n : ℕ, ‖toLp (sectorPart n u)‖ ^ 2
      = ∑ α ∈ u.support.filter (fun α => ndeg α = n), ‖u α‖ ^ 2 := by
    intro n
    have hsub : (sectorPart n u).support ⊆ u.support.filter (fun α => ndeg α = n) := by
      rw [sectorPart, Finsupp.support_filter]
    rw [normSq_toLp_of_subset hsub]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [sectorPart_apply, if_pos (Finset.mem_filter.mp hα).2]
  calc ∑ n ∈ D, (n : ℝ) ^ 2 * ‖toLp (sectorPart n u)‖ ^ 2
      = ∑ n ∈ D, ∑ α ∈ u.support.filter (fun α => ndeg α = n),
          ((ndeg α : ℝ)) ^ 2 * ‖u α‖ ^ 2 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hnorm n, Finset.mul_sum]
        exact Finset.sum_congr rfl fun α hα => by rw [(Finset.mem_filter.mp hα).2]
    _ = ∑ α ∈ u.support, ((ndeg α : ℝ)) ^ 2 * ‖u α‖ ^ 2 :=
        Finset.sum_fiberwise_of_maps_to (fun α hα => Finset.mem_image_of_mem ndeg hα) _

/-! ## 6. Essential self-adjointness on the finite-occupation core -/

/-- The comparison operator `𝒩 + 1` applied to a finitely supported state. -/
def numWeight (u : FockAlg) : FockAlg :=
  Finsupp.onFinset u.support (fun α => (numSym α : ℂ) * u α) (by
    intro α hα
    by_contra hc
    have hz : u α = 0 := Finsupp.notMem_support_iff.mp hc
    simp only [hz, mul_zero, ne_eq, not_true_eq_false] at hα)

theorem numWeight_apply (u : FockAlg) (α : Conf) :
    numWeight u α = (numSym α : ℂ) * u α := rfl

theorem diagMax_numSym_eq (x : lpFiniteModes Conf) :
    (diagMax numSym (inclC numSym x) : Fock) = toLp (numWeight (fockEquiv.symm x)) := by
  refine lp.ext (funext fun α => ?_)
  rw [diagMax_coe]
  have hx : ((x : Fock) : Conf → ℂ) α = (fockEquiv.symm x) α := by
    rw [coe_fockEquiv_symm x]
    rfl
  rw [inclC_coe, hx]
  rfl

/-- The relative bound against the comparison operator, on the core. -/
theorem dGammaOp_coreRelBound (hK : SchurBound col K) (hherm : IsHermCol col) (hK0 : 0 ≤ K) :
    CoreRelBound numSym (dGammaOp col) K := by
  classical
  intro x
  set u : FockAlg := fockEquiv.symm x with hu
  have h1 : (dGammaOp col x : Fock) = toLp (dGamma col u) := coe_dGammaOp col x
  have h2 : (diagMax numSym (inclC numSym x) : Fock) = toLp (numWeight u) :=
    diagMax_numSym_eq x
  have hsupp : (numWeight u).support ⊆ u.support := Finsupp.support_onFinset_subset
  have hN : ‖toLp (numWeight u)‖ ^ 2 = ∑ α ∈ u.support, (numSym α) ^ 2 * ‖u α‖ ^ 2 := by
    rw [normSq_toLp_of_subset hsupp]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [numWeight_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  have hmono : ∑ α ∈ u.support, ((ndeg α : ℝ)) ^ 2 * ‖u α‖ ^ 2
      ≤ ∑ α ∈ u.support, (numSym α) ^ 2 * ‖u α‖ ^ 2 := by
    refine Finset.sum_le_sum fun α _ => ?_
    have h0 : (0:ℝ) ≤ (ndeg α : ℝ) := Nat.cast_nonneg _
    have hle : (ndeg α : ℝ) ≤ numSym α := by simp only [numSym]; linarith
    have hsq : ((ndeg α : ℝ)) ^ 2 ≤ (numSym α) ^ 2 := by nlinarith [h0, hle]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖u α‖)
  have hbound := norm_dGamma_le hK hherm hK0 u
  have hsq : ‖toLp (dGamma col u)‖ ^ 2 ≤ (K * ‖toLp (numWeight u)‖) ^ 2 := by
    rw [mul_pow, hN]
    refine le_trans hbound ?_
    exact mul_le_mul_of_nonneg_left hmono (sq_nonneg K)
  have hR : 0 ≤ K * ‖toLp (numWeight u)‖ := mul_nonneg hK0 (norm_nonneg _)
  have hL : 0 ≤ ‖toLp (dGamma col u)‖ := norm_nonneg _
  rw [h1, h2]
  nlinarith [hsq, hR, hL]

/-- **The commutator form vanishes**: `dΓ(A)` conserves the particle number. -/
theorem dGammaOp_commForm_zero (hherm : IsHermCol col) (x : lpFiniteModes Conf) :
    (inner ℂ (dGammaOp col x) ((diagMax numSym (inclC numSym x) : Fock)) : ℂ).im = 0 := by
  classical
  set w : FockAlg := fockEquiv.symm x with hw
  rw [coe_dGammaOp col x, diagMax_numSym_eq x]
  set D : Finset ℕ := w.support.image ndeg with hD
  have hnum : numWeight w = ∑ n ∈ D, ((n : ℂ) + 1) • sectorPart n w := by
    refine Finsupp.ext fun α => ?_
    rw [numWeight_apply, Finset.sum_apply']
    have hterm : ∀ n ∈ D, (((n : ℂ) + 1) • sectorPart n w) α
        = if ndeg α = n then ((ndeg α : ℂ) + 1) * w α else 0 := by
      intro n _
      rw [Finsupp.smul_apply, sectorPart_apply, smul_eq_mul]
      by_cases h : ndeg α = n
      · rw [if_pos h, if_pos h, h]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    by_cases hα : α ∈ w.support
    · rw [if_pos (Finset.mem_image_of_mem ndeg hα)]
      simp only [numSym]
      push_cast
      ring
    · rw [Finsupp.notMem_support_iff.mp hα]
      simp
  have hXsum : toLp (dGamma col w) = ∑ n ∈ D, toLp (dGamma col (sectorPart n w)) := by
    conv_lhs => rw [← sum_sectorPart w]
    rw [map_sum, ← toLpL_apply, map_sum]
    rfl
  have hNsum : toLp (numWeight w) = ∑ n ∈ D, ((n : ℂ) + 1) • toLp (sectorPart n w) := by
    rw [hnum, ← toLpL_apply, map_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [map_smul, toLpL_apply]
  rw [hXsum, hNsum, sum_inner]
  have hterm : ∀ n ∈ D, (inner ℂ (toLp (dGamma col (sectorPart n w)))
        (∑ m ∈ D, ((m : ℂ) + 1) • toLp (sectorPart m w)) : ℂ)
      = ((n : ℂ) + 1)
        * inner ℂ (toLp (dGamma col (sectorPart n w))) (toLp (sectorPart n w)) := by
    intro n hn
    rw [inner_sum, Finset.sum_eq_single n]
    · rw [inner_smul_right]
    · intro m hm hmn
      rw [inner_smul_right,
        inner_toLp_eq_zero_of_ne_sector (dGamma_inSector col (sectorPart_inSector n w))
          (sectorPart_inSector m w) (Ne.symm hmn), mul_zero]
    · intro hcon
      exact absurd hn hcon
  rw [Finset.sum_congr rfl hterm, Complex.im_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  have hre : (inner ℂ (toLp (dGamma col (sectorPart n w))) (toLp (sectorPart n w)) : ℂ).im
      = 0 := by
    have hsymm := inner_dGamma_symm hherm (sectorPart n w) (sectorPart n w)
    have hconj := inner_conj_symm (𝕜 := ℂ) (toLp (sectorPart n w))
      (toLp (dGamma col (sectorPart n w)))
    have hz : (starRingEnd ℂ) (inner ℂ (toLp (dGamma col (sectorPart n w)))
        (toLp (sectorPart n w)) : ℂ)
        = inner ℂ (toLp (dGamma col (sectorPart n w))) (toLp (sectorPart n w)) := by
      rw [hconj, ← hsymm]
    exact Complex.conj_eq_iff_im.mp hz
  simp [Complex.mul_im, hre]

/-- **The headline.**  The second quantization of a Hermitian, column-finite one-particle
matrix satisfying the Schur bound `∑_j |A_{jk}| ≤ K` is essentially self-adjoint on the
finite-occupation core of the Fock space.  No basis diagonalizes `A`, and the entries need
not be summable. -/
theorem dGamma_essentiallySelfAdjointOn_core (hK : SchurBound col K) (hherm : IsHermCol col)
    (hK0 : 0 ≤ K) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp col) := by
  refine essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm numSym numSym_nonneg
    (dGammaOp col) K ?_ (dGammaOp_coreRelBound hK hherm hK0) (dGammaOp_commForm_zero hherm)
  intro u v
  exact dGammaOp_symmetricOn hherm u v

/-! ## 7. Non-vacuity: nearest-neighbour hopping -/

/-- The **nearest-neighbour hopping** matrix `A_{jk} = 1` for `|j − k| = 1`, presented by
its columns. -/
def hopCol (k : ℕ) : ℕ →₀ ℂ :=
  if k = 0 then Finsupp.single 1 (1 : ℂ)
  else Finsupp.single (k + 1) (1 : ℂ) + Finsupp.single (k - 1) (1 : ℂ)

theorem hopCol_apply (k j : ℕ) : (hopCol k) j = if j = k + 1 ∨ k = j + 1 then 1 else 0 := by
  classical
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hcond : (j = 0 + 1 ∨ 0 = j + 1) ↔ (1 = j) := by omega
    rw [hopCol, if_pos rfl, Finsupp.single_apply, if_congr hcond rfl rfl]
  · have hcond : (j = k + 1 ∨ k = j + 1) ↔ (k + 1 = j ∨ k - 1 = j) := by omega
    rw [hopCol, if_neg (by omega), Finsupp.add_apply, Finsupp.single_apply,
      Finsupp.single_apply, if_congr hcond rfl rfl]
    by_cases h1 : k + 1 = j
    · have h2 : ¬ (k - 1 = j) := by omega
      simp [h1, h2]
    · by_cases h2 : k - 1 = j
      · simp [h1, h2]
      · simp [h1, h2]

theorem isHermCol_hopCol : IsHermCol hopCol := by
  intro j k
  rw [hopCol_apply, hopCol_apply]
  by_cases h : k = j + 1 ∨ j = k + 1
  · have h' : j = k + 1 ∨ k = j + 1 := h.symm
    simp [h, h']
  · have h' : ¬ (j = k + 1 ∨ k = j + 1) := fun hc => h hc.symm
    simp [h, h']

theorem support_hopCol_subset (k : ℕ) : (hopCol k).support ⊆ {k + 1, k - 1} := by
  classical
  intro j hj
  have hne : (hopCol k) j ≠ 0 := Finsupp.mem_support_iff.mp hj
  rw [hopCol_apply] at hne
  by_cases h : j = k + 1 ∨ k = j + 1
  · rcases h with h | h
    · simp [h]
    · have : j = k - 1 := by omega
      simp [this]
  · rw [if_neg h] at hne
    exact absurd rfl hne

theorem schurBound_hopCol : SchurBound hopCol 2 := by
  classical
  intro k
  have hle : ∀ j, ‖(hopCol k) j‖ ≤ 1 := by
    intro j
    rw [hopCol_apply]
    by_cases h : j = k + 1 ∨ k = j + 1 <;> simp [h]
  calc ∑ j ∈ (hopCol k).support, ‖(hopCol k) j‖
      ≤ ∑ j ∈ ({k + 1, k - 1} : Finset ℕ), ‖(hopCol k) j‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (support_hopCol_subset k)
          (fun j _ _ => norm_nonneg _)
    _ ≤ ∑ _j ∈ ({k + 1, k - 1} : Finset ℕ), (1:ℝ) := Finset.sum_le_sum fun j _ => hle j
    _ ≤ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        have : (({k + 1, k - 1} : Finset ℕ)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans
          (by simp)
        exact_mod_cast this

/-- The entries of the hopping matrix are **not** summable: the gate of
`ChapterFockDifferingBasesEsa` does not cover it. -/
theorem hopCol_not_summable : ¬ Summable fun k : ℕ => ‖(hopCol k) (k + 1)‖ := by
  intro hsum
  have hone : ∀ k : ℕ, ‖(hopCol k) (k + 1)‖ = 1 := by
    intro k
    rw [hopCol_apply, if_pos (Or.inl rfl)]
    simp
  have h := hsum.tendsto_atTop_zero
  simp only [hone] at h
  have h3 := tendsto_nhds_unique h (tendsto_const_nhds (x := (1:ℝ)) (f := Filter.atTop))
  norm_num at h3



/-! ## 8. The unique self-adjoint realization and its unitary group -/

/-- **The second-quantized dynamics.**  A Schur-class Hermitian one-particle matrix gives a
second quantization with a unique self-adjoint realization, and that realization generates a
complete unitary group (Stone). -/
theorem dGamma_stone_flow (hK : SchurBound col K) (hherm : IsHermCol col) (hK0 : 0 ≤ K) :
    ∃ (T : UnboundedSelfAdjoint Fock) (U : ℝ → (Fock →L[ℂ] Fock)),
      IsSelfAdjointExtension (dGammaOp col) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ finiteOccupation_dense (dGammaOp_symmetricOn hherm)
    (dGamma_essentiallySelfAdjointOn_core hK hherm hK0)

/-- **For a positive Schur-class matrix the Friedrichs extension of `dΓ(A)` is the
closure**: there is nothing to select. -/
theorem dGamma_positiveExtension_eq_closure (hK : SchurBound col K) (hherm : IsHermCol col)
    (hK0 : 0 ≤ K) {Dom : Submodule ℂ Fock} {A : Dom →ₗ[ℂ] Fock}
    (hA : IsPositiveSelfAdjointExtension (dGammaOp col) A) :
    Dom = clDom (dGammaOp col) ∧
      ∀ (x : Fock) (h : x ∈ Dom) (h' : x ∈ clDom (dGammaOp col)),
        A ⟨x, h⟩ = clExt (dGammaOp col) finiteOccupation_dense
          (dGammaOp_symmetricOn hherm) ⟨x, h'⟩ :=
  positiveExtension_eq_closure_of_esa finiteOccupation_dense (dGammaOp_symmetricOn hherm)
    (dGamma_essentiallySelfAdjointOn_core hK hherm hK0) hA

/-- **The unitary group of the hopping Hamiltonian.** -/
theorem hop_stone_flow :
    ∃ (T : UnboundedSelfAdjoint Fock) (U : ℝ → (Fock →L[ℂ] Fock)),
      IsSelfAdjointExtension (dGammaOp hopCol) T.op ∧ IsStoneFlow T U :=
  dGamma_stone_flow schurBound_hopCol isHermCol_hopCol (by norm_num)

end

end BookProof.FockSchur


