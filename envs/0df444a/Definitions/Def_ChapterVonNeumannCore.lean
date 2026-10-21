-- Prove2me | Definitions.Def_ChapterVonNeumannCore
-- name    : ChapterVonNeumannCore
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-20T16:33:41.788473+00:00
-- url     : https://prove2.me/theorems/8c3c554e-fa9c-4c0f-88e5-c1ede5e4213a
-- title:
--   The Lean 4 theorem `inner_fst_add_self` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterVonNeumannCore.lean`): generated def bundle for ChapterVonNeumannCore. See BookProof/ChapterVonNeumannCore.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterVonNeumannCore.lean

import Theorems.Thm_BookProof_FriedrichsSquare_frDom_le_clDom

import Theorems.Thm_BookProof_ClosureUniqueness_factorGraph_quadForm
import Theorems.Thm_BookProof_ClosureUniqueness_adjGraph_eq_adjPairs_clGraph

import Theorems.Thm_BookProof_FriedrichsSquare_exists_mem_factorRel_add



import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Theorems.Thm_BookProof_ClosureUniqueness_opGraph_clExt
import Theorems.Thm_BookProof_ClosureUniqueness_adjGraph_eq_of_clGraph_eq
import Theorems.Thm_BookProof_ClosureUniqueness_factorGraph_eq_of_clGraph_eq


/-!
# von Neumann's core theorem: `D(A* Ā)` is a core of `Ā`, and `(1 + A* Ā)⁻¹`

`BookProof.ChapterFriedrichsSquareFactorization` proves that the composite
`A* Ā` — the relation `factorRel A` — is the Friedrichs extension of `A²` for a
densely defined symmetric operator `A` with invariant domain, and that
`1 + A* Ā` is *surjective* (`exists_mem_factorRel_add`).  Two classical
complements of that theorem are proved here.

## The bounded inverse `(1 + A* Ā)⁻¹`

The solution of `x + A* Ā x = h` is also **unique**
(`eq_of_mem_factorRel_add_eq`), because the quadratic form of `A* Ā` is `‖Āx‖²`:
pairing `x + A* Ā x = h` with `x` gives `⟪x, h⟫ = ‖x‖² + ‖Āx‖²`, whence

* `‖x‖ ≤ ‖h‖` and `‖Āx‖ ≤ ‖h‖` (`norm_le_of_mem_factorRel_add`),
* `x = 0` when `h = 0` (`eq_zero_of_mem_factorRel_add_eq_zero`).

So `h ↦ x` is a well-defined linear map `resLin A`, everywhere defined, bounded
by `1` — the continuous operator **`resCLM A`** with `‖resCLM A‖ ≤ 1` — and it
is a two-sided inverse of `1 + A* Ā` (`resLin_left_inverse`,
`resLin_right_inverse`).  In particular `D(A* Ā)`, the domain `frDom A`, is
**dense** (`frDom_dense`): a vector orthogonal to it is orthogonal to `x` for the
solution of `x + A* Ā x = h` with `h` the vector itself, and the same quadratic
form kills it.

## The core theorem

**`topologicalClosure_coreGraph`** — the part of the closed graph of `Ā` lying
over `D(A* Ā)`, i.e. `coreGraph A = clGraph A ⊓ (frDom A ×  F)`, is dense in the
whole closed graph.  Equivalently, in operator form, `Ā` restricted to `D(A* Ā)`
(`coreRes A`) has the same closure as `A` (`clGraph_coreRes`) and is a core of
the closure `clExt A` (`isCoreOf_coreRes`).

The proof is von Neumann's: work in the Hilbert direct sum `F ⊕₂ F`, where the
graph inner product is the ambient one.  If `q = (x, w)` lies in the closed graph
and is orthogonal to the graph over `D(A* Ā)`, then for every `(a, z) ∈ A* Ā`
with `(a, y) ∈ clGraph A` orthogonality reads `⟪a, x⟫ + ⟪y, w⟫ = 0`, and the
adjoint relation `(y, z)` turns `⟪y, w⟫` into `⟪z, x⟫`; hence
`⟪a + z, x⟫ = 0`.  Since `1 + A* Ā` is surjective, `a + z` runs over the whole
space, so `x = 0`, and then `w = 0` by closability
(`eq_zero_of_mem_clLp_of_orthogonal`).  A trivial orthogonal-projection argument
turns that into density (`clLp_le_topologicalClosure_coreLp`), and the
homeomorphism `F ⊕₂ F ≅ F × F` transports the statement back to `F × F`.

Combined with `BookProof.ClosureUniqueness.factorGraph_eq_of_clGraph_eq`, the
Friedrichs extension of `A²` may therefore be computed from the core `D(A* Ā)`
itself (`factorGraph_coreRes`).

Hypotheses: `F` is a complex Hilbert space, `A` is symmetric on a dense domain
`D`.  No invariance of `D` is needed anywhere in this module — `A²` never
appears; only the closure `Ā`, the adjoint `A*` and their composite do.
-/

namespace BookProof.VonNeumannCore

open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness
open BookProof.FriedrichsSquare

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

/-- The quadratic-form identity for `1 + A* Ā`. -/
theorem inner_fst_add_self {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorRel A) :
    ∃ y : F, (p.1, y) ∈ clGraph A ∧
      (inner ℂ p.1 (p.1 + p.2) : ℂ) = ((‖p.1‖ ^ 2 + ‖y‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨y, hy, hval⟩ := factorGraph_quadForm (A := A) (p := p) hp
  refine ⟨y, hy, ?_⟩
  have h1 : (inner ℂ p.1 p.1 : ℂ) = ((‖p.1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [inner_add_right, h1, hval, ← Complex.ofReal_add]

theorem eq_zero_of_mem_factorRel_add_eq_zero {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorRel A)
    (hsum : p.1 + p.2 = 0) : p = 0 := by
  obtain ⟨y, -, hval⟩ := inner_fst_add_self hp
  rw [hsum, inner_zero_right] at hval
  have hre : (0 : ℝ) = ‖p.1‖ ^ 2 + ‖y‖ ^ 2 := by
    have h0 := congrArg Complex.re hval
    rwa [Complex.zero_re, Complex.ofReal_re] at h0
  have h1 : p.1 = 0 := by
    have : ‖p.1‖ = 0 := by nlinarith [norm_nonneg p.1, norm_nonneg y]
    simpa using this
  have h2 : p.2 = 0 := by
    have := hsum
    rw [h1, zero_add] at this
    exact this
  exact Prod.ext h1 h2

/-- Uniqueness of the solution of `x + A* Ā x = h`. -/
theorem eq_of_mem_factorRel_add_eq {A : D →ₗ[ℂ] F} {p q : F × F} (hp : p ∈ factorRel A)
    (hq : q ∈ factorRel A) {h : F} (hps : p.1 + p.2 = h) (hqs : q.1 + q.2 = h) : p = q := by
  have hsub : p - q ∈ factorRel A := (factorRel A).sub_mem hp hq
  have hsum : (p - q).1 + (p - q).2 = 0 := by
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [show p.1 - q.1 + (p.2 - q.2) = (p.1 + p.2) - (q.1 + q.2) by abel, hps, hqs, sub_self]
  have := eq_zero_of_mem_factorRel_add_eq_zero hsub hsum
  exact sub_eq_zero.1 this

/-- `‖(1 + A* Ā)⁻¹ h‖ ≤ ‖h‖` and `‖Ā (1 + A* Ā)⁻¹ h‖ ≤ ‖h‖`. -/
theorem norm_le_of_mem_factorRel_add {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorRel A) {h : F}
    (hsum : p.1 + p.2 = h) :
    ‖p.1‖ ≤ ‖h‖ ∧ ∃ y : F, (p.1, y) ∈ clGraph A ∧ ‖y‖ ≤ ‖h‖ := by
  obtain ⟨y, hy, hval⟩ := inner_fst_add_self hp
  rw [hsum] at hval
  have hkey : ‖p.1‖ ^ 2 + ‖y‖ ^ 2 ≤ ‖p.1‖ * ‖h‖ := by
    have hre : (inner ℂ p.1 h : ℂ).re = ‖p.1‖ ^ 2 + ‖y‖ ^ 2 := by
      rw [hval, Complex.ofReal_re]
    have hle : (inner ℂ p.1 h : ℂ).re ≤ ‖p.1‖ * ‖h‖ := by
      simpa using re_inner_le_norm (𝕜 := ℂ) p.1 h
    rw [hre] at hle
    linarith
  have h1 : ‖p.1‖ ≤ ‖h‖ := by
    rcases eq_or_lt_of_le (norm_nonneg p.1) with hz | hz
    · rw [← hz]; exact norm_nonneg h
    · nlinarith [norm_nonneg y]
  refine ⟨h1, y, hy, ?_⟩
  have hsq : ‖y‖ ^ 2 ≤ ‖h‖ ^ 2 := by nlinarith [norm_nonneg p.1, norm_nonneg h]
  nlinarith [norm_nonneg y, norm_nonneg h]

/-- The witness of the factorization, together with the quadratic form. -/
theorem factorRel_witness {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorRel A) :
    ∃ y : F, (p.1, y) ∈ clGraph A ∧ (y, p.2) ∈ adjGraph A ∧
      (inner ℂ p.1 p.2 : ℂ) = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨y, hy, hz⟩ := hp
  refine ⟨y, hy, hz, ?_⟩
  rw [adjGraph_eq_adjPairs_clGraph] at hz
  have h1 : (inner ℂ y y : ℂ) = inner ℂ p.1 p.2 := hz (p.1, y) hy
  rw [← h1, inner_self_eq_norm_sq_to_K]
  norm_cast

section Complete

variable [CompleteSpace F]

/-! ## The bounded inverse `(1 + A* Ā)⁻¹` -/

/-- The unique solution pair of `x + A* Ā x = h`. -/
noncomputable def resPair (A : D →ₗ[ℂ] F) (h : F) : F × F :=
  Classical.choose (exists_mem_factorRel_add A h)

theorem resPair_mem (A : D →ₗ[ℂ] F) (h : F) : resPair A h ∈ factorRel A :=
  (Classical.choose_spec (exists_mem_factorRel_add A h)).1

theorem resPair_add (A : D →ₗ[ℂ] F) (h : F) : (resPair A h).1 + (resPair A h).2 = h :=
  (Classical.choose_spec (exists_mem_factorRel_add A h)).2

theorem resPair_unique {A : D →ₗ[ℂ] F} {h : F} {p : F × F} (hp : p ∈ factorRel A)
    (hsum : p.1 + p.2 = h) : resPair A h = p :=
  eq_of_mem_factorRel_add_eq (resPair_mem A h) hp (resPair_add A h) hsum

/-- `(1 + A* Ā)⁻¹` as a linear map. -/
noncomputable def resLin (A : D →ₗ[ℂ] F) : F →ₗ[ℂ] F where
  toFun h := (resPair A h).1
  map_add' h k := by
    have : resPair A (h + k) = resPair A h + resPair A k := by
      refine resPair_unique ((factorRel A).add_mem (resPair_mem A h) (resPair_mem A k)) ?_
      have h1 := resPair_add A h
      have h2 := resPair_add A k
      simp only [Prod.fst_add, Prod.snd_add]
      rw [show (resPair A h).1 + (resPair A k).1 + ((resPair A h).2 + (resPair A k).2)
          = ((resPair A h).1 + (resPair A h).2) + ((resPair A k).1 + (resPair A k).2) by abel,
        h1, h2]
    rw [this]
    rfl
  map_smul' c h := by
    have : resPair A (c • h) = c • resPair A h := by
      refine resPair_unique ((factorRel A).smul_mem c (resPair_mem A h)) ?_
      simp only [Prod.smul_fst, Prod.smul_snd, ← smul_add, resPair_add A h]
    rw [this]
    rfl

theorem resLin_apply (A : D →ₗ[ℂ] F) (h : F) : resLin A h = (resPair A h).1 := rfl

theorem resLin_mem_factorRel (A : D →ₗ[ℂ] F) (h : F) :
    (resLin A h, h - resLin A h) ∈ factorRel A := by
  have hmem := resPair_mem A h
  have hsum := resPair_add A h
  have : (resLin A h, h - resLin A h) = resPair A h := by
    rw [resLin_apply, Prod.ext_iff]
    exact ⟨rfl, (eq_sub_of_add_eq' hsum).symm⟩
  rw [this]; exact hmem

theorem norm_resLin_le (A : D →ₗ[ℂ] F) (h : F) : ‖resLin A h‖ ≤ ‖h‖ :=
  (norm_le_of_mem_factorRel_add (resPair_mem A h) (resPair_add A h)).1

/-- **`(1 + A* Ā)⁻¹` is everywhere defined and a contraction.** -/
noncomputable def resCLM (A : D →ₗ[ℂ] F) : F →L[ℂ] F :=
  (resLin A).mkContinuous 1 (fun h => by simpa using norm_resLin_le A h)

theorem resCLM_apply (A : D →ₗ[ℂ] F) (h : F) : resCLM A h = resLin A h := rfl

theorem norm_resCLM_le_one (A : D →ₗ[ℂ] F) : ‖resCLM A‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The resolvent lands in the domain of `A* Ā`, and inverts `1 + A* Ā`. -/
theorem resCLM_mem_frDom (A : D →ₗ[ℂ] F) (h : F) : resCLM A h ∈ frDom A :=
  mem_frDom_iff.2 ⟨_, resLin_mem_factorRel A h⟩

/-- `(1 + A* Ā)⁻¹` is a left inverse of `1 + A* Ā`. -/
theorem resLin_left_inverse (A : D →ₗ[ℂ] F) (x : frDom A) :
    resLin A ((x : F) + frFun A x) = (x : F) := by
  rw [resLin_apply, resPair_unique (frFun_spec A x) rfl]

/-- `(1 + A* Ā)⁻¹` is a right inverse of `1 + A* Ā`. -/
theorem resLin_right_inverse (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) (h : F) :
    resLin A h + frFun A ⟨resLin A h, resCLM_mem_frDom A h⟩ = h := by
  have hval : frFun A ⟨resLin A h, resCLM_mem_frDom A h⟩ = h - resLin A h :=
    frFun_unique hdense hsym (resLin_mem_factorRel A h)
  rw [hval]
  abel

/-! ## The domain of `A* Ā` is dense -/

theorem eq_zero_of_inner_frDom_eq_zero (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) {x : F}
    (hx : ∀ u ∈ frDom A, (inner ℂ u x : ℂ) = 0) : x = 0 := by
  obtain ⟨p, hp, hsum⟩ := exists_mem_factorRel_add A x
  obtain ⟨y, hy, hz, hval⟩ := factorRel_witness hp
  have hx1 : (inner ℂ p.1 x : ℂ) = 0 := hx p.1 (mem_frDom_iff.2 ⟨p.2, hp⟩)
  have hquad : (inner ℂ p.1 (p.1 + p.2) : ℂ) = ((‖p.1‖ ^ 2 + ‖y‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : (inner ℂ p.1 p.1 : ℂ) = ((‖p.1‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [inner_add_right, h1, hval, ← Complex.ofReal_add]
  rw [hsum, hx1] at hquad
  have hre : (0 : ℝ) = ‖p.1‖ ^ 2 + ‖y‖ ^ 2 := by
    have h0 := congrArg Complex.re hquad
    rwa [Complex.zero_re, Complex.ofReal_re] at h0
  have hp1 : p.1 = 0 := by
    have : ‖p.1‖ = 0 := by nlinarith [norm_nonneg p.1, norm_nonneg y]
    simpa using this
  have hy0 : y = 0 := by
    have : ‖y‖ = 0 := by nlinarith [norm_nonneg p.1, norm_nonneg y]
    simpa using this
  have hp2 : p.2 = 0 := by
    rw [mem_adjGraph_iff] at hz
    refine Dense.eq_zero_of_inner_right ℂ hdense fun v hv => ?_
    have hv' := hz ⟨v, hv⟩
    simp only [hy0, inner_zero_right] at hv'
    exact hv'.symm
  rw [← hsum, hp1, hp2, add_zero]

/-- **`D(A* Ā)` is dense.** -/
theorem frDom_dense (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) :
    Dense ((frDom A : Submodule ℂ F) : Set F) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro x hx
  exact eq_zero_of_inner_frDom_eq_zero A hdense fun u hu => hx u hu

/-! ## von Neumann's core theorem -/

end Complete

/-- The graph of `Ā` restricted to the domain of `A* Ā`. -/
def coreGraph (A : D →ₗ[ℂ] F) : Submodule ℂ (F × F) :=
  clGraph A ⊓ (frDom A).comap (LinearMap.fst ℂ F F)

theorem mem_coreGraph_iff {A : D →ₗ[ℂ] F} {p : F × F} :
    p ∈ coreGraph A ↔ p ∈ clGraph A ∧ p.1 ∈ frDom A := Iff.rfl

theorem coreGraph_le_clGraph (A : D →ₗ[ℂ] F) : coreGraph A ≤ clGraph A := inf_le_left

/-- The same graph, inside the Hilbert direct sum `F ⊕₂ F`. -/
def coreLp (A : D →ₗ[ℂ] F) : Submodule ℂ (WithLp 2 (F × F)) :=
  (coreGraph A).comap (WithLp.linearEquiv 2 ℂ (F × F)).toLinearMap

/-- The closed graph, inside the Hilbert direct sum `F ⊕₂ F`. -/
def clLp (A : D →ₗ[ℂ] F) : Submodule ℂ (WithLp 2 (F × F)) :=
  (clGraph A).comap (WithLp.linearEquiv 2 ℂ (F × F)).toLinearMap

theorem mem_coreLp_iff {A : D →ₗ[ℂ] F} {p : WithLp 2 (F × F)} :
    p ∈ coreLp A ↔ WithLp.ofLp p ∈ coreGraph A := Iff.rfl

theorem mem_clLp_iff {A : D →ₗ[ℂ] F} {p : WithLp 2 (F × F)} :
    p ∈ clLp A ↔ WithLp.ofLp p ∈ clGraph A := Iff.rfl

theorem coreLp_le_clLp (A : D →ₗ[ℂ] F) : coreLp A ≤ clLp A :=
  fun _ hp => (mem_coreGraph_iff.1 hp).1

theorem clLp_isClosed (A : D →ₗ[ℂ] F) :
    IsClosed ((clLp A : Submodule ℂ (WithLp 2 (F × F))) : Set (WithLp 2 (F × F))) := by
  have hcont : Continuous fun p : WithLp 2 (F × F) => WithLp.ofLp p := by fun_prop
  exact (clGraph_isClosed A).preimage hcont

section Complete2

variable [CompleteSpace F]

/-- **The heart of the core theorem**: an element of the closed graph that is
orthogonal, in the graph inner product, to the part of the graph over `D(A* Ā)`
is zero. -/
theorem eq_zero_of_mem_clLp_of_orthogonal (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) {q : WithLp 2 (F × F)} (hq : q ∈ clLp A)
    (horth : q ∈ (coreLp A)ᗮ) : q = 0 := by
  have hqG : ((WithLp.ofLp q).1, (WithLp.ofLp q).2) ∈ clGraph A := hq
  have hx : (WithLp.ofLp q).1 = 0 := by
    have hall : ∀ h : F, (inner ℂ h (WithLp.ofLp q).1 : ℂ) = 0 := by
      intro h
      obtain ⟨p, hp, hsum⟩ := exists_mem_factorRel_add A h
      obtain ⟨y, hy, hz, -⟩ := factorRel_witness hp
      have hu : (WithLp.toLp 2 (p.1, y)) ∈ coreLp A := by
        refine mem_coreLp_iff.2 ?_
        exact ⟨by simpa using hy, by simpa using mem_frDom_iff.2 ⟨p.2, hp⟩⟩
      have h0 := horth _ hu
      rw [WithLp.prod_inner_apply] at h0
      have hyw : (inner ℂ y (WithLp.ofLp q).2 : ℂ) = inner ℂ p.2 (WithLp.ofLp q).1 := by
        rw [adjGraph_eq_adjPairs_clGraph] at hz
        have hr := hz ((WithLp.ofLp q).1, (WithLp.ofLp q).2) hqG
        have := congrArg (starRingEnd ℂ) hr
        rwa [inner_conj_symm, inner_conj_symm] at this
      rw [hyw] at h0
      rw [← hsum, inner_add_left]
      exact h0
    have := hall (WithLp.ofLp q).1
    exact inner_self_eq_zero.1 this
  have hw : (WithLp.ofLp q).2 = 0 := by
    refine clGraph_snd_eq_zero_of_fst_eq_zero hdense hsym ?_
    rw [← hx]
    exact hqG
  have hz : WithLp.ofLp q = (0 : F × F) := Prod.ext hx hw
  have := congrArg (WithLp.toLp 2) hz
  simpa using this

/-- **von Neumann's core theorem**, in the Hilbert direct sum. -/
theorem clLp_le_topologicalClosure_coreLp (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) : clLp A ≤ (coreLp A).topologicalClosure := by
  haveI : CompleteSpace ((coreLp A).topologicalClosure) :=
    (coreLp A).isClosed_topologicalClosure.completeSpace_coe
  haveI : ((coreLp A).topologicalClosure).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  intro v hv
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Submodule.exists_add_mem_mem_orthogonal (K := (coreLp A).topologicalClosure) v
  have hKle : (coreLp A).topologicalClosure ≤ clLp A :=
    Submodule.topologicalClosure_minimal _ (coreLp_le_clLp A) (clLp_isClosed A)
  have hbcl : b ∈ clLp A := by
    have hb' : b = v - a := by rw [hab]; abel
    rw [hb']
    exact (clLp A).sub_mem hv (hKle ha)
  have hborth : b ∈ (coreLp A)ᗮ :=
    Submodule.orthogonal_le (Submodule.le_topologicalClosure _) hb
  have hb0 : b = 0 := eq_zero_of_mem_clLp_of_orthogonal A hdense hsym hbcl hborth
  rw [hab, hb0, add_zero]
  exact ha

/-- **von Neumann's core theorem**: `D(A* Ā)` is a core of `Ā` — the graph of `Ā`
over that domain is dense in the whole closed graph. -/
theorem topologicalClosure_coreGraph (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) : (coreGraph A).topologicalClosure = clGraph A := by
  refine le_antisymm
    (Submodule.topologicalClosure_minimal _ (coreGraph_le_clGraph A) (clGraph_isClosed A)) ?_
  intro p hp
  have hmem : (WithLp.toLp 2 p) ∈ (coreLp A).topologicalClosure :=
    clLp_le_topologicalClosure_coreLp A hdense hsym (by simpa [mem_clLp_iff] using hp)
  have hcont : Continuous fun z : WithLp 2 (F × F) => WithLp.ofLp z := by fun_prop
  have himg : (fun z : WithLp 2 (F × F) => WithLp.ofLp z) ''
      ((coreLp A : Submodule ℂ (WithLp 2 (F × F))) : Set (WithLp 2 (F × F)))
      = ((coreGraph A : Submodule ℂ (F × F)) : Set (F × F)) := by
    ext r
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hr
      exact ⟨WithLp.toLp 2 r, by simpa [mem_coreLp_iff] using hr, by simp⟩
  have hsub := image_closure_subset_closure_image (f := fun z : WithLp 2 (F × F) => WithLp.ofLp z)
    hcont (s := ((coreLp A : Submodule ℂ (WithLp 2 (F × F))) : Set (WithLp 2 (F × F))))
  rw [himg] at hsub
  have hpmem : p ∈ closure ((coreGraph A : Submodule ℂ (F × F)) : Set (F × F)) := by
    refine hsub ⟨WithLp.toLp 2 p, ?_, by simp⟩
    rw [← Submodule.topologicalClosure_coe]
    exact hmem
  rwa [← Submodule.topologicalClosure_coe] at hpmem

/-! ## Operator form -/

/-- `Ā` restricted to the domain of `A* Ā`. -/
noncomputable def coreRes (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    frDom A →ₗ[ℂ] F :=
  (clExt A hdense hsym).comp (Submodule.inclusion (frDom_le_clDom A))

theorem coreRes_apply (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A)
    (x : frDom A) : coreRes A hdense hsym x = clFun A ⟨(x : F), frDom_le_clDom A x.2⟩ := rfl

theorem opGraph_coreRes (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    opGraph (coreRes A hdense hsym) = coreGraph A := by
  refine le_antisymm ?_ ?_
  · rintro p ⟨x, rfl⟩
    exact ⟨clFun_spec A ⟨(x : F), frDom_le_clDom A x.2⟩, x.2⟩
  · intro p hp
    obtain ⟨hpc, hpd⟩ := mem_coreGraph_iff.1 hp
    refine ⟨⟨p.1, hpd⟩, ?_⟩
    have hval : clFun A ⟨p.1, frDom_le_clDom A hpd⟩ = p.2 :=
      clFun_unique hdense hsym (by simpa using hpc)
    simp [coreRes_apply, hval]

/-- **`D(A* Ā)` is a core of `Ā`**, in operator form. -/
theorem clGraph_coreRes (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    clGraph (coreRes A hdense hsym) = clGraph A := by
  unfold clGraph
  rw [opGraph_coreRes A hdense hsym]
  exact topologicalClosure_coreGraph A hdense hsym

theorem isCoreOf_coreRes (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    IsCoreOf (coreRes A hdense hsym) (clExt A hdense hsym) := by
  constructor
  · intro x
    refine ⟨frDom_le_clDom A x.2, ?_⟩
    rw [coreRes_apply]
    rfl
  · rw [clGraph_coreRes A hdense hsym, opGraph_clExt A hdense hsym]

/-- The adjoint is the same whether taken from `A` or from `Ā` on `D(A* Ā)`. -/
theorem adjGraph_coreRes (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    adjGraph (coreRes A hdense hsym) = adjGraph A :=
  adjGraph_eq_of_clGraph_eq (clGraph_coreRes A hdense hsym)

/-- **The Friedrichs extension of `A²` may be computed from the core `D(A* Ā)`.** -/
theorem factorGraph_coreRes (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) : factorGraph (coreRes A hdense hsym) = factorGraph A :=
  factorGraph_eq_of_clGraph_eq (clGraph_coreRes A hdense hsym)

end Complete2

end BookProof.VonNeumannCore


