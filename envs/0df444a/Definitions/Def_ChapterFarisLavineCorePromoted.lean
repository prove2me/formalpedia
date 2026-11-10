-- Prove2me | Definitions.Def_ChapterFarisLavineCorePromoted
-- name    : ChapterFarisLavineCorePromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-09T09:36:31.246015+00:00
-- url     : https://prove2.me/theorems/b3dcb30f-b2e8-45e6-a5d2-af46b9e746b8
-- title:
--   Faris-Lavine core: deficiency spaces, the criterion and its closure
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFarisLavineCore.lean`): the platform's served `Def_ChapterFarisLavineCore` copy is a skeleton (it declares only the headline statement form, so consumers that cite `hasZeroDeficiencyOn_of_farisLavine`, the deficiency-space API and the core lemmas die with `unknown identifier`), and published bundles are immutable, so the fix is a new bundle name that keeps the original namespace (the new-name route, PIPELINE_PLAN §2.13). This bundle re-carries the chapter's full body in `BookProof.FarisLavine`: the deficient subspace `DeficiencySpace`, the zero-deficiency predicate `HasZeroDeficiencyOn` and its equivalence with `EssentiallySelfAdjointOn` for symmetric operators, the Faris–Lavine criterion with a relative bound `a < 1`, and the closure results that let a proof be transferred to a larger domain. Consumers add a single `import Definitions.Def_ChapterFarisLavineCorePromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- §2.13 new-name route (Session 40): the platform's served `Def_ChapterFarisLavineCore` copy is a
-- skeleton (no declarations at all), so `open BookProof.FarisLavine` in every consumer statement
-- dies with `unknown namespace`.  `submit-definition` cannot update an existing
-- name, so this bundle carries the chapter's DEFINITIONS in the original
-- namespace; its theorem facts stay problem nodes.  Consumers add a single
-- `import Definitions.Def_ChapterFarisLavineCorePromoted`.
import Mathlib


/-!
# The Faris–Lavine commutator criterion for essential self-adjointness

This module formalizes and **proves** the abstract theorem of

> W. G. Faris and R. B. Lavine, *Commutators and self-adjointness of Hamiltonian
> operators*, Commun. Math. Phys. **35** (1974), 39–48, Theorem 1,

which elsewhere in this project (`BookProof.ChapterNavierStokesFlow`) had to be
carried as a named hypothesis.  The statement of the paper is:

> Let `H` be a Hermitian operator and `N ≥ 0` a positive self-adjoint operator
> with (i) `𝒟(N) ⊆ 𝒟(H)` and (ii) `± i[H, N] ≤ c N` for some `c < ∞`.  Then `H`
> is essentially self-adjoint.

## How the statement is rendered here

* The Hilbert space is a complex inner-product space `F` which is complete.
* `H` and `N` are linear maps `D →ₗ[ℂ] F` on a common domain `D`, which plays the
  role of `𝒟(N)`; hypothesis (i) of the paper is built into this — `H` is defined
  wherever `N` is.  (The conclusion is about the restriction of `H` to `𝒟(N)`,
  which by the last remark of §2 of the paper is the stronger statement: any
  symmetric extension of an essentially self-adjoint operator has the same
  closure.)
* Symmetry is `SymmetricOn`, the quadratic form of `N` is `quadForm`, and
  `commForm H N x = ⟪x, i[H, N] x⟫` is the commutator form; that this is a real
  number is `commForm_eq`.  Hypothesis (ii) is `|commForm H N x| ≤ c * quadForm N x`,
  which is exactly the two-sided bound `± i[H, N] ≤ c N` of the paper.
* Essential self-adjointness is rendered, as everywhere in this project, by the
  vanishing of the deficiency spaces of the adjoint: `EssentiallySelfAdjointOn D H`
  says that no `w ≠ 0` satisfies `⟪H v, w⟫ = ⟪v, ± i w⟫` for all `v ∈ D`.
* Self-adjointness of `N` is used in the paper at exactly one place: it makes
  `N + 1` a bijection of `𝒟(N)` onto the whole space, so that `(N+1)⁻¹ f` is an
  admissible test vector.  That consequence — surjectivity of `N + 1` — is what
  is assumed here (`hNsurj`), so no spectral theory for unbounded operators is
  needed and the criterion applies verbatim to any `N` for which `-1` is in the
  resolvent set.

## Contents

* `deficiencyTrivialAt_of_farisLavine` — the computation of the paper: under the
  Faris–Lavine hypotheses the deficiency space at `d i` vanishes whenever
  `2|d| > c`.  This is the displayed inequality `± 2 d ⟪f, N⁻¹f⟫ ≤ c ⟪f, N⁻¹f⟫`
  of the original proof.
* `exists_weak_graph_limit` — the closure of a symmetric operator with dense
  range of `H - d i` hits every vector: given `y`, there are `u, z` in the closure
  of the graph with `z - d i u = y`.  Proved by hand from the identity
  `‖H x - d i x‖² = ‖H x‖² + d²‖x‖²`, which makes the approximating sequence and
  its image Cauchy.
* `deficiencyTrivialAt_of_dense_range` — the classical basic criterion: for a
  symmetric operator, vanishing of the deficiency spaces at one conjugate pair
  `± d i` (`d ≠ 0`) forces vanishing at *every* non-real point.  This is the step
  that upgrades the paper's "for `|d|` large" to essential self-adjointness.
* `essentiallySelfAdjointOn_of_farisLavine` — **Theorem 1 of Faris–Lavine.**
* `hasZeroDeficiencyOn_of_farisLavine` — the same conclusion in the predicate
  `BookProof.NavierStokesFlow.HasZeroDeficiencyOn` used by the Navier–Stokes
  chapters, for an operator that leaves its domain invariant.
* `not_farisLavine_criterion_of_relative_bound` — a caveat, and the reason the
  hypotheses above are what they are: the *unrestricted* form of the criterion
  (relative bound `‖Hv‖ ≤ a‖Nv‖` plus commutator bound, with no positivity and no
  self-adjointness required of `N`) is **false**; taking `N = H` for the
  limit-circle Jacobi operator of `BookProof.ChapterNavierStokesDeficiency`
  satisfies both inequalities while essential self-adjointness fails.
* `essentiallySelfAdjointOn_of_bounded_symmetric` and
  `multiplication_essentiallySelfAdjoint` — the hypotheses are satisfiable: the
  first in the everywhere-defined case, the second for the (unbounded)
  multiplication operator by an arbitrary real sequence on its maximal domain in
  `ℓ²(ℕ)`.

Nothing here is assumed: the module contains no `axiom`, and every result is
proved from Mathlib.
-/

namespace BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

/-! ## Basic notions -/

/-- `T` is symmetric (Hermitian) on the domain `D`: `⟪T x, y⟫ = ⟪x, T y⟫`. -/
def SymmetricOn (D : Submodule ℂ F) (T : D →ₗ[ℂ] F) : Prop :=
  ∀ x y : D, (inner ℂ (T x) (y : F) : ℂ) = inner ℂ (x : F) (T y)

/-- The deficiency space of the adjoint of `T` at `z` is trivial: the only `w`
with `⟪T v, w⟫ = ⟪v, z w⟫` for all `v` in the domain is `w = 0`.  Equivalently,
the range of `T - z̄` is dense. -/
def DeficiencyTrivialAt (D : Submodule ℂ F) (T : D →ₗ[ℂ] F) (z : ℂ) : Prop :=
  ∀ w : F, (∀ v : D, (inner ℂ (T v) w : ℂ) = z * inner ℂ (v : F) w) → w = 0

/-- **Essential self-adjointness** of a symmetric operator defined on `D`: both
deficiency spaces of the adjoint, at `i` and at `-i`, vanish. -/
def EssentiallySelfAdjointOn (D : Submodule ℂ F) (T : D →ₗ[ℂ] F) : Prop :=
  DeficiencyTrivialAt D T Complex.I ∧ DeficiencyTrivialAt D T (-Complex.I)

/-- The quadratic form `⟪x, N x⟫` of `N` (a real number when `N` is symmetric,
see `quadForm_im`). -/
noncomputable def quadForm (N : D →ₗ[ℂ] F) (x : D) : ℝ := (inner ℂ (x : F) (N x) : ℂ).re

/-- The commutator form `⟪x, i[H, N] x⟫ = i(⟪H x, N x⟫ - ⟪N x, H x⟫)`, which for
symmetric `H` and `N` is the quadratic form of the (formal) operator `i[H, N]`.
It is real: see `commForm_eq`. -/
noncomputable def commForm (H N : D →ₗ[ℂ] F) (x : D) : ℝ :=
  (Complex.I * ((inner ℂ (H x) (N x) : ℂ) - (inner ℂ (N x) (H x) : ℂ))).re

theorem inner_im_swap (a b : F) : (inner ℂ b a : ℂ).im = -(inner ℂ a b : ℂ).im := by
  rw [← inner_conj_symm (𝕜 := ℂ) a b, Complex.conj_im, neg_neg]

/-- The expectation of a symmetric operator is real. -/
theorem inner_apply_self_im (T : D →ₗ[ℂ] F) (hT : SymmetricOn D T) (x : D) :
    (inner ℂ (T x) (x : F) : ℂ).im = 0 := by
  have h := congrArg Complex.im (hT x x)
  rw [inner_im_swap (T x) (x : F)] at h
  linarith

/-- The quadratic form of a symmetric operator is real. -/
theorem quadForm_im (N : D →ₗ[ℂ] F) (hN : SymmetricOn D N) (x : D) :
    (inner ℂ (x : F) (N x) : ℂ).im = 0 := by
  rw [inner_im_swap (N x) (x : F), inner_apply_self_im N hN x, neg_zero]

/-- The commutator form is `-2 Im ⟪H x, N x⟫`; in particular it is real, and the
Faris–Lavine hypothesis `± i[H, N] ≤ c N` is the bound `|commForm| ≤ c quadForm`. -/
theorem commForm_eq (H N : D →ₗ[ℂ] F) (x : D) :
    commForm H N x = -2 * (inner ℂ (H x) (N x) : ℂ).im := by
  rw [commForm, Complex.mul_re]
  simp [Complex.sub_im, inner_im_swap (H x) (N x)]
  ring

/-! ## The computation of Faris–Lavine

With `N` replaced by `N + 1` (which changes neither the commutator form, since
`⟪H x, x⟫` is real, nor the validity of the bound, since the form of `N` only
grows), the vector `g = (N+1)⁻¹ w` is admissible, and the deficiency identity at
`d i` reads `Im ⟪H g, (N+1) g⟫ = d ⟪g, (N+1) g⟫`.  The commutator bound turns
this into `2|d| t ≤ c t` with `t = ⟪g, (N+1)g⟫ ≥ ‖g‖²`, so `t = 0` as soon as
`2|d| > c`. -/

/-- **The Faris–Lavine estimate.**  Under the hypotheses of Theorem 1 the
deficiency space of `H*` at `d i` is trivial for every real `d` with `2|d| > c`;
equivalently the range of `H + d i` is dense. -/
theorem deficiencyTrivialAt_of_farisLavine
    (H N : D →ₗ[ℂ] F) (c d : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x)
    (hd : c < 2 * |d|) :
    DeficiencyTrivialAt D H ((d : ℂ) * Complex.I) := by
  intro w hw
  obtain ⟨g, hg⟩ := hNsurj w
  have key := hw g
  rw [← hg, inner_add_right, inner_add_right] at key
  have him := congrArg Complex.im key
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_re] at him
  have hBim : (inner ℂ (H g) (g : F) : ℂ).im = 0 := inner_apply_self_im H hH g
  have hPim : (inner ℂ (g : F) (N g) : ℂ).im = 0 := quadForm_im N hN g
  have hQim : (inner ℂ (g : F) (g : F) : ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) (g : F)
  have hQre : (inner ℂ (g : F) (g : F) : ℂ).re = ‖(g : F)‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (g : F)
  set t : ℝ := quadForm N g + ‖(g : F)‖ ^ 2 with ht
  have hAim : (inner ℂ (H g) (N g) : ℂ).im = d * t := by
    rw [hBim, hPim, hQim, hQre] at him
    simp only [quadForm, ht]
    linarith [him]
  have htnn : 0 ≤ t := by have := hNpos g; positivity
  have habs : |commForm H N g| = 2 * |d| * t := by
    rw [commForm_eq, hAim, abs_mul, abs_mul, abs_of_nonneg htnn]
    norm_num
    ring
  have h1 : 2 * |d| * t ≤ c * quadForm N g := habs ▸ hcomm g
  have h2 : c * quadForm N g ≤ c * t := by
    have hle : quadForm N g ≤ t := by rw [ht]; nlinarith [sq_nonneg ‖(g : F)‖]
    exact mul_le_mul_of_nonneg_left hle hc
  have ht0 : t = 0 := by nlinarith
  have hgz : (g : F) = 0 := by
    have hnn := hNpos g
    have h4 : ‖(g : F)‖ ^ 2 = 0 := by rw [ht] at ht0; nlinarith [sq_nonneg ‖(g : F)‖]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (g : F)])
  have hg0 : g = 0 := Subtype.ext hgz
  rw [← hg, hg0]
  simp

/-! ## From dense ranges at one conjugate pair to essential self-adjointness -/

/-- The Pythagoras identity for a symmetric operator: `H x` and `d i x` are
orthogonal, because `⟪H x, x⟫` is real. -/
theorem norm_sub_smul_sq (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (d : ℝ) (x : D) :
    ‖H x - ((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = ‖H x‖ ^ 2 + d ^ 2 * ‖(x : F)‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  have h1 : (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ)
      = ((d : ℂ) * Complex.I) * inner ℂ (H x) (x : F) := inner_smul_right _ _ _
  have h2 : RCLike.re (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ) = 0 := by
    rw [h1]; simp [inner_apply_self_im H hH x]
  have h3 : ‖((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = d ^ 2 * ‖(x : F)‖ ^ 2 := by
    rw [norm_smul]; simp [mul_pow, sq_abs]
  rw [h2, h3]; ring

/-- Triviality of a deficiency space is the same as weak density of a range, and
for a complete space weak density is density. -/
theorem dense_range_of_deficiencyTrivialAt [CompleteSpace F] (H : D →ₗ[ℂ] F) (w₀ : ℂ)
    (h : DeficiencyTrivialAt D H (starRingEnd ℂ w₀)) :
    Dense (Set.range fun x : D => H x - w₀ • (x : F)) := by
  set K : Submodule ℂ F := LinearMap.range (H - w₀ • D.subtype) with hK
  have hset : (K : Set F) = Set.range fun x : D => H x - w₀ • (x : F) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp [LinearMap.sub_apply]⟩
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp [LinearMap.sub_apply]⟩
  rw [← hset, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  refine h f fun v => ?_
  have hv := (Submodule.mem_orthogonal K f).mp hf (H v - w₀ • (v : F))
    ⟨v, by simp [LinearMap.sub_apply]⟩
  rw [inner_sub_left, inner_smul_left, sub_eq_zero] at hv
  exact hv

/-- **The graph closure of a symmetric operator with dense range hits every
vector.**  If the range of `H - d i` is dense (`d ≠ 0` real), then for every `y`
there are `u, z` in the closure of the graph of `H` — that is, `⟪H v, u⟫ = ⟪v, z⟫`
for all `v` in the domain, with `⟪z, u⟫` still real — such that `z - d i u = y`.

This is the only place where completeness of the space is used.  The proof is
the classical one: the identity `‖H x - d i x‖² = ‖H x‖² + d²‖x‖²` makes both an
approximating sequence and its image Cauchy. -/
theorem exists_weak_graph_limit [CompleteSpace F] (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H)
    (d : ℝ) (hd : d ≠ 0)
    (hdense : Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)))
    (y : F) :
    ∃ u z : F, (∀ v : D, (inner ℂ (H v) u : ℂ) = inner ℂ (v : F) z) ∧
      z - ((d : ℂ) * Complex.I) • u = y ∧ (inner ℂ z u : ℂ).im = 0 := by
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have hchoice : ∀ n : ℕ, ∃ x : D, ‖(H x - ((d : ℂ) * Complex.I) • (x : F)) - y‖ < 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨p, hp1, x, hx⟩ := Metric.dense_iff.mp hdense y (1 / (n + 1)) hpos
    refine ⟨x, ?_⟩
    rw [← hx] at hp1
    simpa [dist_eq_norm] using hp1
  choose x hx using hchoice
  set Y : ℕ → F := fun n => H (x n) - ((d : ℂ) * Complex.I) • ((x n : F)) with hY
  have hYtend : Filter.Tendsto Y Filter.atTop (nhds y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hx n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hYcauchy : CauchySeq Y := hYtend.cauchySeq
  have hest : ∀ m n : ℕ, |d| * ‖(x m : F) - (x n : F)‖ ≤ ‖Y m - Y n‖ ∧
      ‖H (x m) - H (x n)‖ ≤ ‖Y m - Y n‖ := by
    intro m n
    have hsplit : Y m - Y n = H (x m - x n) - ((d : ℂ) * Complex.I) • ((x m - x n : D) : F) := by
      simp [hY, map_sub, smul_sub]
      abel
    have hsq := norm_sub_smul_sq H hH d (x m - x n)
    rw [← hsplit] at hsq
    have hcoe : ((x m - x n : D) : F) = (x m : F) - (x n : F) := rfl
    rw [hcoe, map_sub] at hsq
    constructor
    · nlinarith [norm_nonneg (Y m - Y n), norm_nonneg ((x m : F) - (x n : F)),
        norm_nonneg (H (x m) - H (x n)), sq_abs d, sq_nonneg (‖H (x m) - H (x n)‖)]
    · nlinarith [norm_nonneg (Y m - Y n), norm_nonneg ((x m : F) - (x n : F)),
        norm_nonneg (H (x m) - H (x n)), sq_nonneg d, sq_nonneg (d * ‖(x m : F) - (x n : F)‖)]
  have hxcauchy : CauchySeq (fun n => (x n : F)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hYcauchy (ε * |d|) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := (hest m n).1
    have h2 := hN m hm n hn
    rw [dist_eq_norm] at h2 ⊢
    nlinarith
  have hHxcauchy : CauchySeq (fun n => H (x n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hYcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := (hest m n).2
    have h2 := hN m hm n hn
    rw [dist_eq_norm] at h2 ⊢
    linarith
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hxcauchy
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hHxcauchy
  refine ⟨u, z, ?_, ?_, ?_⟩
  · intro v
    have h1 : Filter.Tendsto (fun n => (inner ℂ (H v) (x n : F) : ℂ)) Filter.atTop
        (nhds (inner ℂ (H v) u)) := Filter.Tendsto.inner tendsto_const_nhds hu
    have h2 : Filter.Tendsto (fun n => (inner ℂ (v : F) (H (x n)) : ℂ)) Filter.atTop
        (nhds (inner ℂ (v : F) z)) := Filter.Tendsto.inner tendsto_const_nhds hz
    have heq : ∀ n, (inner ℂ (H v) (x n : F) : ℂ) = inner ℂ (v : F) (H (x n)) := fun n => hH v (x n)
    exact tendsto_nhds_unique (by simpa [heq] using h1) h2
  · have hlim : Filter.Tendsto Y Filter.atTop (nhds (z - ((d : ℂ) * Complex.I) • u)) := by
      simpa [hY] using hz.sub (Filter.Tendsto.const_smul hu ((d : ℂ) * Complex.I))
    exact tendsto_nhds_unique hlim hYtend
  · have h1 : Filter.Tendsto (fun n => (inner ℂ (H (x n)) (x n : F) : ℂ)) Filter.atTop
        (nhds (inner ℂ z u)) := Filter.Tendsto.inner hz hu
    have h2 : Filter.Tendsto (fun n => (inner ℂ (H (x n)) (x n : F) : ℂ).im) Filter.atTop
        (nhds ((inner ℂ z u : ℂ).im)) := (Complex.continuous_im.tendsto _).comp h1
    have h3 : ∀ n, (inner ℂ (H (x n)) (x n : F) : ℂ).im = 0 :=
      fun n => inner_apply_self_im H hH (x n)
    simp only [h3] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds

/-- **The basic criterion.**  For a symmetric operator, if the deficiency space
at one point `e i` (`e ≠ 0` real) vanishes and the range of `H - e i` is dense,
then the deficiency space at *every* non-real point vanishes.  This is what turns
the Faris–Lavine estimate — valid only for `2|d| > c` — into essential
self-adjointness. -/
theorem deficiencyTrivialAt_of_dense_range [CompleteSpace F] (H : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (e : ℝ) (he : e ≠ 0) (σ : ℂ) (hσ : σ.im ≠ 0)
    (hdense : Dense (Set.range fun x : D => H x - ((e : ℂ) * Complex.I) • (x : F)))
    (hdef : DeficiencyTrivialAt D H ((e : ℂ) * Complex.I)) :
    DeficiencyTrivialAt D H σ := by
  intro w hw
  obtain ⟨u, z, hu, hzy, him⟩ :=
    exists_weak_graph_limit H hH e he hdense ((σ - (e : ℂ) * Complex.I) • w)
  have hzeq : z = ((e : ℂ) * Complex.I) • u + (σ - (e : ℂ) * Complex.I) • w := by
    rw [← hzy]; abel
  have hs : ∀ v : D, (inner ℂ (H v) (w - u) : ℂ)
      = ((e : ℂ) * Complex.I) * inner ℂ (v : F) (w - u) := by
    intro v
    rw [inner_sub_right, inner_sub_right, hw v, hu v, hzeq, inner_add_right,
      inner_smul_right, inner_smul_right]
    ring
  have hwu : w = u := sub_eq_zero.mp (hdef (w - u) hs)
  have hzs : z = σ • w := by rw [hzeq, ← hwu]; module
  have hinner : (inner ℂ z u : ℂ) = starRingEnd ℂ σ * ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [hzs, ← hwu, inner_smul_left, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hinner, Complex.mul_im] at him
  simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.conj_im, mul_zero, zero_add] at him
  have hnorm : ‖w‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd (by linarith [neg_eq_zero.mp h] : σ.im = 0) hσ
    · exact h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])

/-! ## Theorem 1 of Faris–Lavine -/

/-- **Theorem 1 (Faris–Lavine 1974).**  Let `H` be a Hermitian operator and `N`
a positive operator on a common dense domain `D` of a Hilbert space, such that

* `± i[H, N] ≤ c N` as quadratic forms on `D` (hypothesis (ii) of the paper), and
* `N + 1` maps `D` onto the whole space — the one consequence of "`N ≥ 0` is
  self-adjoint" that the argument uses.

Then `H` is essentially self-adjoint: both deficiency spaces of its adjoint
vanish.

Hypothesis (i) of the paper, `𝒟(N) ⊆ 𝒟(H)`, is built into the statement by
giving `H` and `N` the same domain; the conclusion is about the restriction of
`H` to `𝒟(N)`, which is the sharper statement.  Density of `D` is not needed as a
hypothesis: it follows from surjectivity of `N + 1`. -/
theorem essentiallySelfAdjointOn_of_farisLavine [CompleteSpace F]
    (H N : D →ₗ[ℂ] F) (c : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x) :
    EssentiallySelfAdjointOn D H := by
  set d : ℝ := c + 1 with hdd
  have hdpos : 0 < d := by simp [hdd]; linarith
  have hdabs : |d| = d := abs_of_pos hdpos
  have hd0 : d ≠ 0 := ne_of_gt hdpos
  have hdgt : c < 2 * |d| := by rw [hdabs, hdd]; linarith
  have hplus : DeficiencyTrivialAt D H ((d : ℂ) * Complex.I) :=
    deficiencyTrivialAt_of_farisLavine H N c d hH hN hc hNpos hNsurj hcomm hdgt
  have hminus : DeficiencyTrivialAt D H (((-d : ℝ) : ℂ) * Complex.I) := by
    refine deficiencyTrivialAt_of_farisLavine H N c (-d) hH hN hc hNpos hNsurj hcomm ?_
    rwa [abs_neg]
  have hconj : starRingEnd ℂ ((d : ℂ) * Complex.I) = ((-d : ℝ) : ℂ) * Complex.I := by
    simp
  have hdense : Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)) :=
    dense_range_of_deficiencyTrivialAt H ((d : ℂ) * Complex.I) (by rw [hconj]; exact hminus)
  exact ⟨deficiencyTrivialAt_of_dense_range H hH d hd0 Complex.I (by simp) hdense hplus,
    deficiencyTrivialAt_of_dense_range H hH d hd0 (-Complex.I) (by simp) hdense hplus⟩

/-- The everywhere-defined case, as a sanity check that the hypotheses of
Theorem 1 are satisfiable: take `N = 1`, whose commutator with anything vanishes.
A bounded (indeed any) symmetric operator defined on the whole space is
essentially self-adjoint. -/
theorem essentiallySelfAdjointOn_top_of_symmetric [CompleteSpace F]
    (H : (⊤ : Submodule ℂ F) →ₗ[ℂ] F) (hH : SymmetricOn ⊤ H) :
    EssentiallySelfAdjointOn (⊤ : Submodule ℂ F) H := by
  refine essentiallySelfAdjointOn_of_farisLavine H (⊤ : Submodule ℂ F).subtype 0 hH
    (fun x y => rfl) le_rfl (fun x => ?_)
    (fun f => ⟨⟨(2 : ℂ)⁻¹ • f, trivial⟩, ?_⟩) (fun x => ?_)
  · have hq : quadForm (⊤ : Submodule ℂ F).subtype x = ‖(x : F)‖ ^ 2 := by
      simp only [quadForm, Submodule.subtype_apply]
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (x : F)
    rw [hq]; positivity
  · change (2 : ℂ)⁻¹ • f + (2 : ℂ)⁻¹ • f = f
    rw [← add_smul]
    norm_num
  · have h : (inner ℂ (H x) ((⊤ : Submodule ℂ F).subtype x) : ℂ).im = 0 :=
      inner_apply_self_im H hH x
    rw [commForm_eq, h]
    simp

/-! ## Corollary 1.1: the criterion on a core

The paper's Corollary 1.1 weakens the hypotheses to a linear subspace `C` which
is a core: the estimates are only required on `C`, and the conclusion is that the
restriction of `H` to `C` is already essentially self-adjoint.  Here the core
property is stated as it is used — every vector of `𝒟(N)` is approximated by
vectors of `C` *together with* their images under `N` (the graph norm of `N`) —
and the relative bound `‖Hf‖² ≤ a‖Nf‖² + b‖f‖²` transports the approximation from
the graph of `N` to the graph of `H`. -/

/-- If every vector of the domain `D` is approximated, in the graph norm of `H`,
by vectors of a subspace `C ≤ D`, then a deficiency vector for the restriction of
`H` to `C` is one for `H` itself.  (Restricting an operator can only enlarge its
deficiency spaces; a core is exactly what makes the enlargement trivial.) -/
theorem essentiallySelfAdjointOn_restrict_of_graph_core
    {C : Submodule ℂ F} (hCD : C ≤ D) (H : D →ₗ[ℂ] F)
    (hcore : ∀ (x : D) (ε : ℝ), 0 < ε → ∃ y : D, (y : F) ∈ C ∧
      ‖(y : F) - (x : F)‖ < ε ∧ ‖H y - H x‖ < ε)
    (hdef : EssentiallySelfAdjointOn D H) :
    EssentiallySelfAdjointOn C (H.comp (Submodule.inclusion hCD)) := by
  have main : ∀ σ : ℂ, DeficiencyTrivialAt D H σ →
      DeficiencyTrivialAt C (H.comp (Submodule.inclusion hCD)) σ := by
    intro σ hσ w hw
    refine hσ w fun x => ?_
    have hzero : ∀ ε : ℝ, 0 < ε →
        ‖(inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w‖ ≤ ε * (1 + ‖σ‖) * ‖w‖ := by
      intro ε hε
      obtain ⟨y, hyC, hy1, hy2⟩ := hcore x ε hε
      have hwy := hw ⟨(y : F), hyC⟩
      have hHy : (H.comp (Submodule.inclusion hCD)) ⟨(y : F), hyC⟩ = H y := by
        simp only [LinearMap.comp_apply]
        congr 1
      rw [hHy] at hwy
      have hsplit : (inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w
          = (inner ℂ (H x - H y) w : ℂ) + σ * inner ℂ ((y : F) - (x : F)) w := by
        rw [inner_sub_left, inner_sub_left, hwy]
        push_cast
        ring
      calc ‖(inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w‖
          ≤ ‖(inner ℂ (H x - H y) w : ℂ)‖ + ‖σ * (inner ℂ ((y : F) - (x : F)) w : ℂ)‖ := by
            rw [hsplit]; exact norm_add_le _ _
        _ ≤ ‖H x - H y‖ * ‖w‖ + ‖σ‖ * (‖(y : F) - (x : F)‖ * ‖w‖) := by
            gcongr
            · exact norm_inner_le_norm _ _
            · rw [norm_mul]
              gcongr
              exact norm_inner_le_norm _ _
        _ ≤ ε * (1 + ‖σ‖) * ‖w‖ := by
            have h1 : ‖H x - H y‖ ≤ ε := by
              rw [← norm_neg]; simpa [neg_sub] using hy2.le
            have h2 : ‖(y : F) - (x : F)‖ ≤ ε := hy1.le
            have hA : ‖H x - H y‖ * ‖w‖ ≤ ε * ‖w‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg w)
            have hB : ‖σ‖ * (‖(y : F) - (x : F)‖ * ‖w‖) ≤ ‖σ‖ * (ε * ‖w‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg w))
                (norm_nonneg σ)
            have hsum : ε * ‖w‖ + ‖σ‖ * (ε * ‖w‖) = ε * (1 + ‖σ‖) * ‖w‖ := by ring
            linarith
    have hnn : ‖(inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w‖ ≤ 0 := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have hpos : 0 < δ / ((1 + ‖σ‖) * (1 + ‖w‖)) := by positivity
      have := hzero _ hpos
      have hbound : δ / ((1 + ‖σ‖) * (1 + ‖w‖)) * (1 + ‖σ‖) * ‖w‖ ≤ δ := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg w, norm_nonneg σ, hδ.le]
      linarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hnn)
  exact ⟨main _ hdef.1, main _ hdef.2⟩

/-- **Corollary 1.1 of Faris–Lavine.**  The Faris–Lavine hypotheses on `𝒟(N)`,
together with the relative bound `‖Hf‖² ≤ a‖Nf‖² + b‖f‖²` and a subspace `C` that
is a core for `N` (approximation in the graph norm of `N`), give essential
self-adjointness of the restriction of `H` to `C`. -/
theorem essentiallySelfAdjointOn_core_of_farisLavine [CompleteSpace F]
    {C : Submodule ℂ F} (hCD : C ≤ D) (H N : D →ₗ[ℂ] F) (a b c : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x)
    (hrel : ∀ x : D, ‖H x‖ ^ 2 ≤ a * ‖N x‖ ^ 2 + b * ‖(x : F)‖ ^ 2)
    (hNcore : ∀ (x : D) (ε : ℝ), 0 < ε → ∃ y : D, (y : F) ∈ C ∧
      ‖(y : F) - (x : F)‖ < ε ∧ ‖N y - N x‖ < ε) :
    EssentiallySelfAdjointOn C (H.comp (Submodule.inclusion hCD)) := by
  refine essentiallySelfAdjointOn_restrict_of_graph_core hCD H (fun x ε hε => ?_)
    (essentiallySelfAdjointOn_of_farisLavine H N c hH hN hc hNpos hNsurj hcomm)
  set K : ℝ := |a| + |b| + 1 with hK
  have hKpos : 0 < K := by positivity
  set δ : ℝ := min ε (ε / Real.sqrt K) with hδ
  have hδpos : 0 < δ := by
    refine lt_min hε ?_
    positivity
  obtain ⟨y, hyC, hy1, hy2⟩ := hNcore x δ hδpos
  refine ⟨y, hyC, lt_of_lt_of_le hy1 (min_le_left _ _), ?_⟩
  have hdiff : H y - H x = H (y - x) := by rw [map_sub]
  have hNdiff : N y - N x = N (y - x) := by rw [map_sub]
  have hcoe : ((y - x : D) : F) = (y : F) - (x : F) := rfl
  have hsq := hrel (y - x)
  rw [← hdiff, ← hNdiff, hcoe] at hsq
  have hb1 : ‖N y - N x‖ ≤ δ := hy2.le
  have hb2 : ‖(y : F) - (x : F)‖ ≤ δ := hy1.le
  have hδK : δ ^ 2 * K ≤ ε ^ 2 := by
    have h1 : δ ≤ ε / Real.sqrt K := min_le_right _ _
    have hsqrt : Real.sqrt K ^ 2 = K := Real.sq_sqrt hKpos.le
    have hsqrtpos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hKpos
    have h2 : δ * Real.sqrt K ≤ ε := by
      rw [le_div_iff₀ hsqrtpos] at h1
      exact h1
    have h3 : (δ * Real.sqrt K) ^ 2 ≤ ε ^ 2 := by
      nlinarith [mul_nonneg hδpos.le hsqrtpos.le]
    calc δ ^ 2 * K = (δ * Real.sqrt K) ^ 2 := by rw [mul_pow, hsqrt]
      _ ≤ ε ^ 2 := h3
  have hfinal : ‖H y - H x‖ ^ 2 < ε ^ 2 := by
    have hnn1 : 0 ≤ ‖N y - N x‖ := norm_nonneg _
    have hnn2 : 0 ≤ ‖(y : F) - (x : F)‖ := norm_nonneg _
    have hle : a * ‖N y - N x‖ ^ 2 + b * ‖(y : F) - (x : F)‖ ^ 2 ≤ (|a| + |b|) * δ ^ 2 := by
      have hs1 : ‖N y - N x‖ ^ 2 ≤ δ ^ 2 := by nlinarith
      have hs2 : ‖(y : F) - (x : F)‖ ^ 2 ≤ δ ^ 2 := by nlinarith
      have ha : a * ‖N y - N x‖ ^ 2 ≤ |a| * δ ^ 2 :=
        le_trans (by nlinarith [le_abs_self a, sq_nonneg ‖N y - N x‖])
          (mul_le_mul_of_nonneg_left hs1 (abs_nonneg a))
      have hbb : b * ‖(y : F) - (x : F)‖ ^ 2 ≤ |b| * δ ^ 2 :=
        le_trans (by nlinarith [le_abs_self b, sq_nonneg ‖(y : F) - (x : F)‖])
          (mul_le_mul_of_nonneg_left hs2 (abs_nonneg b))
      linarith
    have hstrict : (|a| + |b|) * δ ^ 2 < ε ^ 2 := by
      have : δ ^ 2 * K = (|a| + |b|) * δ ^ 2 + δ ^ 2 := by rw [hK]; ring
      nlinarith [pow_pos hδpos 2]
    linarith
  have hεpos : (0 : ℝ) < ε := hε
  nlinarith [norm_nonneg (H y - H x)]

end BookProof.FarisLavine


