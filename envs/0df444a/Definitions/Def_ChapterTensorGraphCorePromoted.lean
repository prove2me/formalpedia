-- Prove2me | Definitions.Def_ChapterTensorGraphCorePromoted
-- name    : ChapterTensorGraphCorePromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-09T10:20:56.812114+00:00
-- url     : https://prove2.me/theorems/0e90103d-a592-4bc0-8e45-814c565c52a4
-- title:
--   Tensor powers: a one-particle core is a core for the sector derivation
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterTensorGraphCore.lean`): the platform's served `Def_ChapterTensorGraphCore` copy is a skeleton (no declarations), so consumers that cite `inclPow_tmul`, `derPow_tmul`, `sectorCore_le_sectorDom` and the core lemmas of the `n`-particle sector die with `unknown identifier`, and published bundles are immutable, so the fix is a new bundle name that keeps the original namespace (the new-name route, PIPELINE_PLAN §2.13). This bundle re-carries the chapter's full body in `BookProof.TensorCore`: the tensor power `Hs.pow n`, its dense subspace `D^{⊗n}`, the lifted inclusion and derivation `inclPow`/`derPow` together with their elementary-tensor identities, and the theorem that a one-particle graph core is a graph core for the sector derivation `dΓ(A)⁽ⁿ⁾` on the full tensor power. Consumers add a single `import Definitions.Def_ChapterTensorGraphCorePromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterTensorGraphCore.lean

-- §2.13 new-name route (Session 40): the platform's served `Def_ChapterTensorGraphCore` copy is a
-- skeleton (no declarations at all), so `open BookProof.TensorCore` in every consumer statement
-- dies with `unknown namespace`.  `submit-definition` cannot update an existing
-- name, so this bundle carries the chapter's DEFINITIONS in the original
-- namespace; its theorem facts stay problem nodes.  Consumers add a single
-- `import Definitions.Def_ChapterTensorGraphCorePromoted`.
import Definitions.Def_ChapterGraphCoreTransferPromoted
import Mathlib


/-!
# Tensor powers: a one-particle core is a core for the sector derivation

Let `A` be a symmetric operator with domain `D₂` in a complex inner product space `H`, and
let `D ≤ D₂` be a **core** for `A` in the graph-norm sense of
`BookProof.GraphCore.IsGraphCore`.  The `n`-particle sector of the second quantization of
`A` carries the *derivation*

`dΓ(A)⁽ⁿ⁾ (x₁ ⊗ ⋯ ⊗ xₙ) = Σⱼ x₁ ⊗ ⋯ ⊗ A xⱼ ⊗ ⋯ ⊗ xₙ`,

defined on the algebraic tensor power `D₂^{⊗n}`.  This module proves the **multilinear core
estimate**: the algebraic tensor power `D^{⊗n}` of the one-particle core is again a core, now
for the sector derivation.  Together with the core transfer principle
(`BookProof.GraphCore.essentiallySelfAdjointOn_of_graphCore`) this is what allows the
hypothesis "`A` is self-adjoint on `D`" to be weakened to "`A` is essentially self-adjoint on
`D`" in the second quantization theorem: one never needs `D` to be invariant under the
unitary group, nor a resolvent of `A` on `D`.

## Contents

* `IPSpace` — a bundled complex inner product space, and `IPSpace.pow` its `n`-fold
  algebraic tensor power (`Mathlib` gives the tensor product of two inner product spaces its
  inner product, so the powers are inner product spaces by recursion).
* `inclPow` — the isometric inclusion `D₂^{⊗n} → H^{⊗n}`.
* `derPow` — the sector derivation `dΓ(A)⁽ⁿ⁾` on `D₂^{⊗n}`, defined by the Leibniz recursion
  `dΓ⁽ⁿ⁺¹⁾ = A ⊗ 1 + 1 ⊗ dΓ⁽ⁿ⁾`.
* `corePow` — the algebraic tensor power `D^{⊗n}` of the one-particle core.
* `exists_core_approx` — **the multilinear core estimate**: every vector of `D₂^{⊗n}` is
  approximated in the graph norm of `dΓ(A)⁽ⁿ⁾` by vectors of `D^{⊗n}`.
* `sectorDom`, `sectorCore`, `sectorOp` — the same data seen inside `H^{⊗n}`, and
  `isGraphCore_sectorCore`, the core estimate in the form used by the transfer principle.
* `essentiallySelfAdjointOn_sectorCore` — if the sector derivation is essentially
  self-adjoint on `D₂^{⊗n}`, it is essentially self-adjoint on `D^{⊗n}`.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.TensorCore

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

/-! ## Tensor powers of an inner product space -/

/-- A bundled complex inner product space.  Bundling is what makes the recursion defining
the tensor powers (and their inner products) possible. -/
structure IPSpace where
  /-- the underlying type -/
  carrier : Type
  [nacg : NormedAddCommGroup carrier]
  [ips : InnerProductSpace ℂ carrier]

attribute [instance] IPSpace.nacg IPSpace.ips

instance : CoeSort IPSpace Type := ⟨IPSpace.carrier⟩

/-- The `n`-fold algebraic tensor power `E^{⊗n}`, with `E^{⊗0} = ℂ`. -/
@[reducible] def IPSpace.pow (E : IPSpace) : ℕ → IPSpace
  | 0 => ⟨ℂ⟩
  | (n + 1) => ⟨E.carrier ⊗[ℂ] (E.pow n).carrier⟩

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)

/-- The domain of the one-particle operator, as an inner product space in its own right. -/
@[reducible] def domSpace : IPSpace := ⟨D₂⟩

/-- The isometric inclusion `D₂^{⊗n} → H^{⊗n}`. -/
def inclPow : ∀ n : ℕ, ((domSpace Hs D₂).pow n) →ₗᵢ[ℂ] (Hs.pow n)
  | 0 => LinearIsometry.id
  | (n + 1) => TensorProduct.mapIsometry D₂.subtypeₗᵢ (inclPow n)

@[simp] theorem inclPow_tmul (n : ℕ) (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    inclPow Hs D₂ (n + 1) (a ⊗ₜ[ℂ] b) = (a : Hs.carrier) ⊗ₜ[ℂ] inclPow Hs D₂ n b := rfl

variable (A : D₂ →ₗ[ℂ] Hs.carrier)

/-- The **sector derivation** `dΓ(A)⁽ⁿ⁾` on the algebraic tensor power `D₂^{⊗n}`, defined by
the Leibniz recursion `dΓ⁽ⁿ⁺¹⁾ = A ⊗ 1 + 1 ⊗ dΓ⁽ⁿ⁾`.  On elementary tensors it is
`Σⱼ x₁ ⊗ ⋯ ⊗ A xⱼ ⊗ ⋯ ⊗ xₙ`. -/
def derPow : ∀ n : ℕ, ((domSpace Hs D₂).pow n) →ₗ[ℂ] (Hs.pow n)
  | 0 => 0
  | (n + 1) => TensorProduct.map A (inclPow Hs D₂ n).toLinearMap
      + TensorProduct.map D₂.subtype (derPow n)

@[simp] theorem derPow_zero (x : ((domSpace Hs D₂).pow 0)) : derPow Hs D₂ A 0 x = 0 := rfl

@[simp] theorem derPow_tmul (n : ℕ) (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    derPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)
      = (A a) ⊗ₜ[ℂ] inclPow Hs D₂ n b + (a : Hs.carrier) ⊗ₜ[ℂ] derPow Hs D₂ A n b := rfl

variable (D : Submodule ℂ Hs.carrier)

/-- The algebraic tensor power `D^{⊗n}` of the one-particle core, as a subspace of
`D₂^{⊗n}`. -/
def corePow : ∀ n : ℕ, Submodule ℂ ((domSpace Hs D₂).pow n)
  | 0 => ⊤
  | (n + 1) =>
      Submodule.span ℂ
        {t | ∃ a : D₂, (a : Hs.carrier) ∈ D ∧ ∃ b ∈ corePow n, a ⊗ₜ[ℂ] b = t}

theorem tmul_mem_corePow {n : ℕ} {a : D₂} (ha : (a : Hs.carrier) ∈ D)
    {b : ((domSpace Hs D₂).pow n)} (hb : b ∈ corePow Hs D₂ D n) :
    a ⊗ₜ[ℂ] b ∈ corePow Hs D₂ D (n + 1) :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

/-! ## The multilinear core estimate -/

/-- The graph map `x ↦ (x, dΓ(A)⁽ⁿ⁾ x)` of the sector derivation, with values in
`H^{⊗n} × H^{⊗n}`.  Density in the graph norm is density of the range of this map. -/
def graphPow (n : ℕ) : ((domSpace Hs D₂).pow n) →ₗ[ℂ] (Hs.pow n) × (Hs.pow n) :=
  (inclPow Hs D₂ n).toLinearMap.prod (derPow Hs D₂ A n)

@[simp] theorem graphPow_apply (n : ℕ) (x : ((domSpace Hs D₂).pow n)) :
    graphPow Hs D₂ A n x = (inclPow Hs D₂ n x, derPow Hs D₂ A n x) := rfl

/-- The elementary bilinear estimate behind the telescoping sum: an elementary tensor moves
by at most the sum of the moves of its two factors. -/
theorem norm_tmul_sub_le {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (x x' : E) (y y' : F) :
    ‖x ⊗ₜ[ℂ] y - x' ⊗ₜ[ℂ] y'‖ ≤ ‖x - x'‖ * ‖y‖ + ‖x'‖ * ‖y - y'‖ := by
  have hid : x ⊗ₜ[ℂ] y - x' ⊗ₜ[ℂ] y' = (x - x') ⊗ₜ[ℂ] y + x' ⊗ₜ[ℂ] (y - y') := by
    rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
  rw [hid]
  refine le_trans (norm_add_le _ _) ?_
  simp [TensorProduct.norm_tmul]

/-- **The telescoping step.**  If the graph of the `n`-sector derivation is approximated from
the core, then so is the graph of the `(n+1)`-sector derivation at every elementary tensor:
moving the head factor into the one-particle core costs `‖a - a'‖ + ‖A a - A a'‖`, moving the
tail costs the `n`-level graph distance, and the two costs add. -/
theorem graphPow_tmul_mem_closure (hcore : IsGraphCore D A) (n : ℕ)
    (ih : ∀ b : ((domSpace Hs D₂).pow n), graphPow Hs D₂ A n b ∈
      (Submodule.map (graphPow Hs D₂ A n) (corePow Hs D₂ D n)).topologicalClosure)
    (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    graphPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b) ∈
      (Submodule.map (graphPow Hs D₂ A (n + 1))
        (corePow Hs D₂ D (n + 1))).topologicalClosure := by
  change graphPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b) ∈
    closure ((Submodule.map (graphPow Hs D₂ A (n + 1)) (corePow Hs D₂ D (n + 1))) : Set _)
  refine Metric.mem_closure_iff.mpr ?_
  intro ε hε
  set u : (Hs.pow n).carrier := inclPow Hs D₂ n b with hu
  set w : (Hs.pow n).carrier := derPow Hs D₂ A n b with hw
  set na : ℝ := ‖(a : Hs.carrier)‖ with hna
  set nAa : ℝ := ‖A a‖ with hnAa
  set C : ℝ := na + nAa + ‖u‖ + ‖w‖ + 2 with hC
  have hna0 : 0 ≤ na := norm_nonneg _
  have hnAa0 : 0 ≤ nAa := norm_nonneg _
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
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
  -- approximate the head factor inside the one-particle core
  obtain ⟨a', ha'D, ha'₁, ha'₂⟩ := hcore a δ hδpos
  -- approximate the tail inside the core tensor power
  obtain ⟨z, hz, hzd⟩ := Metric.mem_closure_iff.mp (ih b) δ hδpos
  obtain ⟨b', hb', rfl⟩ := hz
  set u' : (Hs.pow n).carrier := inclPow Hs D₂ n b' with hu'
  set w' : (Hs.pow n).carrier := derPow Hs D₂ A n b' with hw'
  have hzd' := max_lt_iff.mp (by simpa [Prod.dist_eq, dist_eq_norm] using hzd)
  have hb₁ : ‖u - u'‖ < δ := by simpa [hu, hu'] using hzd'.1
  have hb₂ : ‖w - w'‖ < δ := by simpa [hw, hw'] using hzd'.2
  have ha'norm : ‖(a' : Hs.carrier)‖ ≤ na + δ := by
    have h1 := norm_sub_norm_le (a' : Hs.carrier) (a : Hs.carrier)
    have h2 : ‖(a' : Hs.carrier) - (a : Hs.carrier)‖ < δ := by rw [norm_sub_rev]; exact ha'₁
    rw [hna]; linarith
  have hAa'norm : ‖A a'‖ ≤ nAa + δ := by
    have h1 := norm_sub_norm_le (A a') (A a)
    have h2 : ‖A a' - A a‖ < δ := by rw [norm_sub_rev]; exact ha'₂
    rw [hnAa]; linarith
  refine ⟨graphPow Hs D₂ A (n + 1) (a' ⊗ₜ[ℂ] b'),
    ⟨a' ⊗ₜ[ℂ] b', tmul_mem_corePow Hs D₂ D ha'D hb', rfl⟩, ?_⟩
  -- the three elementary moves
  have hmove₁ : ‖(a : Hs.carrier) ⊗ₜ[ℂ] u - (a' : Hs.carrier) ⊗ₜ[ℂ] u'‖
      ≤ δ * ‖u‖ + (na + δ) * δ := by
    refine le_trans (norm_tmul_sub_le (a : Hs.carrier) (a' : Hs.carrier) u u') ?_
    refine add_le_add (mul_le_mul_of_nonneg_right ha'₁.le hu0) ?_
    exact mul_le_mul ha'norm hb₁.le (norm_nonneg _) (by linarith)
  have hmove₂ : ‖(A a) ⊗ₜ[ℂ] u - (A a') ⊗ₜ[ℂ] u'‖ ≤ δ * ‖u‖ + (nAa + δ) * δ := by
    refine le_trans (norm_tmul_sub_le (A a) (A a') u u') ?_
    refine add_le_add (mul_le_mul_of_nonneg_right ha'₂.le hu0) ?_
    exact mul_le_mul hAa'norm hb₁.le (norm_nonneg _) (by linarith)
  have hmove₃ : ‖(a : Hs.carrier) ⊗ₜ[ℂ] w - (a' : Hs.carrier) ⊗ₜ[ℂ] w'‖
      ≤ δ * ‖w‖ + (na + δ) * δ := by
    refine le_trans (norm_tmul_sub_le (a : Hs.carrier) (a' : Hs.carrier) w w') ?_
    refine add_le_add (mul_le_mul_of_nonneg_right ha'₁.le hw0) ?_
    exact mul_le_mul ha'norm hb₂.le (norm_nonneg _) (by linarith)
  -- the two budgets
  have hbudget₁ : δ * ‖u‖ + (na + δ) * δ ≤ δ * C := by
    have hfac : δ * C - (δ * ‖u‖ + (na + δ) * δ) = δ * (nAa + ‖w‖ + 2 - δ) := by rw [hC]; ring
    have hnn : 0 ≤ δ * (nAa + ‖w‖ + 2 - δ) := mul_nonneg hδpos.le (by linarith)
    linarith
  have hbudget₂ :
      (δ * ‖u‖ + (nAa + δ) * δ) + (δ * ‖w‖ + (na + δ) * δ) ≤ δ * C := by
    have hfac : δ * C - ((δ * ‖u‖ + (nAa + δ) * δ) + (δ * ‖w‖ + (na + δ) * δ))
        = 2 * (δ * (1 - δ)) := by rw [hC]; ring
    have hnn : 0 ≤ 2 * (δ * (1 - δ)) := by
      have : 0 ≤ δ * (1 - δ) := mul_nonneg hδpos.le (by linarith)
      linarith
    linarith
  -- assemble the two components
  rw [Prod.dist_eq]
  refine max_lt ?_ ?_
  · rw [dist_eq_norm]
    have hcomp : (graphPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)).1
        - (graphPow Hs D₂ A (n + 1) (a' ⊗ₜ[ℂ] b')).1
        = (a : Hs.carrier) ⊗ₜ[ℂ] u - (a' : Hs.carrier) ⊗ₜ[ℂ] u' := rfl
    rw [hcomp]
    exact lt_of_le_of_lt (le_trans hmove₁ hbudget₁) hδC
  · rw [dist_eq_norm]
    have hcomp : (graphPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)).2
        - (graphPow Hs D₂ A (n + 1) (a' ⊗ₜ[ℂ] b')).2
        = ((A a) ⊗ₜ[ℂ] u - (A a') ⊗ₜ[ℂ] u')
          + ((a : Hs.carrier) ⊗ₜ[ℂ] w - (a' : Hs.carrier) ⊗ₜ[ℂ] w') := by
      change ((A a) ⊗ₜ[ℂ] u + (a : Hs.carrier) ⊗ₜ[ℂ] w)
          - ((A a') ⊗ₜ[ℂ] u' + (a' : Hs.carrier) ⊗ₜ[ℂ] w') = _
      abel
    rw [hcomp]
    refine lt_of_le_of_lt (norm_add_le _ _) ?_
    exact lt_of_le_of_lt (le_trans (add_le_add hmove₂ hmove₃) hbudget₂) hδC

/-- **The graph of the sector derivation is the closure of the graph of its restriction to
the core.**  This is the multilinear (telescoping) estimate in its topological form. -/
theorem graphPow_range_le_closure (hcore : IsGraphCore D A) (n : ℕ) :
    LinearMap.range (graphPow Hs D₂ A n)
      ≤ (Submodule.map (graphPow Hs D₂ A n) (corePow Hs D₂ D n)).topologicalClosure := by
  induction n with
  | zero =>
      have h0 : corePow Hs D₂ D 0 = ⊤ := rfl
      rw [h0, Submodule.map_top]
      exact Submodule.le_topologicalClosure _
  | succ n ih =>
      rintro y ⟨x, rfl⟩
      have hx : x ∈ Submodule.span ℂ
          {t : (D₂ ⊗[ℂ] ((domSpace Hs D₂).pow n).carrier) |
            ∃ (p : D₂) (q : ((domSpace Hs D₂).pow n)), p ⊗ₜ[ℂ] q = t} := by
        rw [TensorProduct.span_tmul_eq_top]; trivial
      induction hx using Submodule.span_induction with
      | mem t ht =>
          obtain ⟨p, q, rfl⟩ := ht
          exact graphPow_tmul_mem_closure Hs D₂ A D hcore n (fun c => ih ⟨c, rfl⟩) p q
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add s t _ _ hs ht => rw [map_add]; exact Submodule.add_mem _ hs ht
      | smul c s _ hs => rw [map_smul]; exact Submodule.smul_mem _ c hs

/-- **The multilinear core estimate.**  If `D` is a core for `A`, then the algebraic tensor
power `D^{⊗n}` is a core for the sector derivation `dΓ(A)⁽ⁿ⁾` on `D₂^{⊗n}`: every vector of
`D₂^{⊗n}` is approximated by vectors of `D^{⊗n}` simultaneously in the norm and in the norm
of its image under `dΓ(A)⁽ⁿ⁾`. -/
theorem exists_core_approx (hcore : IsGraphCore D A) (n : ℕ)
    (x : ((domSpace Hs D₂).pow n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ corePow Hs D₂ D n,
      ‖inclPow Hs D₂ n x - inclPow Hs D₂ n y‖ < ε ∧
        ‖derPow Hs D₂ A n x - derPow Hs D₂ A n y‖ < ε := by
  have hmem : graphPow Hs D₂ A n x ∈
      (Submodule.map (graphPow Hs D₂ A n) (corePow Hs D₂ D n)).topologicalClosure :=
    graphPow_range_le_closure Hs D₂ A D hcore n ⟨x, rfl⟩
  have hmem' : graphPow Hs D₂ A n x ∈
      closure ((Submodule.map (graphPow Hs D₂ A n) (corePow Hs D₂ D n)) : Set _) := hmem
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hmem' ε hε
  obtain ⟨y, hy, rfl⟩ := hz
  refine ⟨y, hy, ?_, ?_⟩
  · have := (max_lt_iff.mp (by simpa [Prod.dist_eq, dist_eq_norm] using hdist)).1
    simpa using this
  · have := (max_lt_iff.mp (by simpa [Prod.dist_eq, dist_eq_norm] using hdist)).2
    simpa using this

/-! ## The sector inside `H^{⊗n}` -/

/-- The image of `D₂^{⊗n}` inside `H^{⊗n}`: the domain of the sector derivation. -/
def sectorDom (n : ℕ) : Submodule ℂ (Hs.pow n) :=
  LinearMap.range (inclPow Hs D₂ n).toLinearMap

/-- The image of the core tensor power `D^{⊗n}` inside `H^{⊗n}`. -/
def sectorCore (n : ℕ) : Submodule ℂ (Hs.pow n) :=
  Submodule.map (inclPow Hs D₂ n).toLinearMap (corePow Hs D₂ D n)

theorem sectorCore_le_sectorDom (n : ℕ) :
    sectorCore Hs D₂ D n ≤ sectorDom Hs D₂ n := by
  rintro x ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

/-- The sector derivation `dΓ(A)⁽ⁿ⁾` as an operator on the subspace `sectorDom` of
`H^{⊗n}`. -/
def sectorOp (n : ℕ) : sectorDom Hs D₂ n →ₗ[ℂ] (Hs.pow n) :=
  derPow Hs D₂ A n ∘ₗ
    (LinearEquiv.ofInjective (inclPow Hs D₂ n).toLinearMap
      (inclPow Hs D₂ n).injective).symm.toLinearMap

theorem sectorOp_apply (n : ℕ) (x : sectorDom Hs D₂ n) (x₀ : ((domSpace Hs D₂).pow n))
    (hx : (x : Hs.pow n) = inclPow Hs D₂ n x₀) :
    sectorOp Hs D₂ A n x = derPow Hs D₂ A n x₀ := by
  have hxx : (LinearEquiv.ofInjective (inclPow Hs D₂ n).toLinearMap
      (inclPow Hs D₂ n).injective) x₀ = x := by
    apply Subtype.ext; rw [hx]; rfl
  have h2 : (LinearEquiv.ofInjective (inclPow Hs D₂ n).toLinearMap
      (inclPow Hs D₂ n).injective).symm x = x₀ := by
    rw [← hxx]; simp
  exact congrArg (fun z => derPow Hs D₂ A n z) h2

/-- **The core estimate in the form used by the transfer principle.** -/
theorem isGraphCore_sectorCore (hcore : IsGraphCore D A) (n : ℕ) :
    IsGraphCore (sectorCore Hs D₂ D n) (sectorOp Hs D₂ A n) := by
  intro x ε hε
  obtain ⟨x₀, hx₀⟩ := x.2
  have hx : (x : Hs.pow n) = inclPow Hs D₂ n x₀ := hx₀.symm
  obtain ⟨y₀, hy₀, hy₁, hy₂⟩ := exists_core_approx Hs D₂ A D hcore n x₀ hε
  refine ⟨⟨inclPow Hs D₂ n y₀, ⟨y₀, rfl⟩⟩, ⟨y₀, hy₀, rfl⟩, ?_, ?_⟩
  · simpa [hx] using hy₁
  · rw [sectorOp_apply Hs D₂ A n x x₀ hx,
      sectorOp_apply Hs D₂ A n ⟨inclPow Hs D₂ n y₀, ⟨y₀, rfl⟩⟩ y₀ rfl]
    exact hy₂

/-! ## Symmetry of the sector derivation -/

/-- The inner product of two elementary tensors in `H^{⊗(n+1)}` factors. -/
theorem inner_tmul_pow (n : ℕ) (x x' : Hs.carrier) (y y' : (Hs.pow n).carrier) :
    (inner ℂ (x ⊗ₜ[ℂ] y : (Hs.pow (n + 1)).carrier) (x' ⊗ₜ[ℂ] y') : ℂ)
      = inner ℂ x x' * inner ℂ y y' := TensorProduct.inner_tmul ℂ x x' y y'

/-- The pure-tensor computation behind symmetry: on elementary tensors the two halves of the
Leibniz rule pair up, the head by symmetry of `A` and the tail by induction. -/
theorem derPow_symm_tmul (hA : SymmetricOn D₂ A) (n : ℕ)
    (ih : ∀ x y : ((domSpace Hs D₂).pow n),
      (inner ℂ (derPow Hs D₂ A n x) (inclPow Hs D₂ n y) : ℂ)
        = inner ℂ (inclPow Hs D₂ n x) (derPow Hs D₂ A n y))
    (a c : D₂) (b d : ((domSpace Hs D₂).pow n)) :
    (inner ℂ (derPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)) (inclPow Hs D₂ (n + 1) (c ⊗ₜ[ℂ] d)) : ℂ)
      = inner ℂ (inclPow Hs D₂ (n + 1) (a ⊗ₜ[ℂ] b)) (derPow Hs D₂ A (n + 1) (c ⊗ₜ[ℂ] d)) := by
  rw [derPow_tmul, inclPow_tmul, inclPow_tmul, derPow_tmul]
  rw [inner_add_left, inner_add_right]
  rw [inner_tmul_pow Hs n (A a) ((c : Hs.carrier)),
    inner_tmul_pow Hs n ((a : Hs.carrier)) ((c : Hs.carrier)),
    inner_tmul_pow Hs n ((a : Hs.carrier)) (A c),
    inner_tmul_pow Hs n ((a : Hs.carrier)) ((c : Hs.carrier)),
    hA a c, ih b d]

/-- **The sector derivation is symmetric** whenever the one-particle operator is. -/
theorem derPow_symm (hA : SymmetricOn D₂ A) (n : ℕ) :
    ∀ x y : ((domSpace Hs D₂).pow n),
      (inner ℂ (derPow Hs D₂ A n x) (inclPow Hs D₂ n y) : ℂ)
        = inner ℂ (inclPow Hs D₂ n x) (derPow Hs D₂ A n y) := by
  induction n with
  | zero => intro x y; simp [derPow]
  | succ n ih =>
      have hlinL : ∀ (x y : (Hs.pow (n + 1)).carrier) (r : ℂ),
          inner ℂ (r • x) y = star r * inner ℂ x y := fun x y r => inner_smul_left x y r
      -- first: `x` an elementary tensor, `y` arbitrary
      have hpure : ∀ (a : D₂) (b : ((domSpace Hs D₂).pow n))
          (y : ((domSpace Hs D₂).pow (n + 1))),
          (inner ℂ (derPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)) (inclPow Hs D₂ (n + 1) y) : ℂ)
            = inner ℂ (inclPow Hs D₂ (n + 1) (a ⊗ₜ[ℂ] b)) (derPow Hs D₂ A (n + 1) y) := by
        intro a b y
        have hy : y ∈ Submodule.span ℂ
            {t : (D₂ ⊗[ℂ] ((domSpace Hs D₂).pow n).carrier) |
              ∃ (p : D₂) (q : ((domSpace Hs D₂).pow n)), p ⊗ₜ[ℂ] q = t} := by
          rw [TensorProduct.span_tmul_eq_top]; trivial
        have hlin : ∀ (x y : (Hs.pow (n + 1)).carrier) (r : ℂ),
            inner ℂ x (r • y) = r * inner ℂ x y := fun x y r => inner_smul_right x y r
        induction hy using Submodule.span_induction with
        | mem t ht =>
            obtain ⟨c, d, rfl⟩ := ht
            exact derPow_symm_tmul Hs D₂ A hA n ih a c b d
        | zero => simp
        | add s t _ _ hs ht => simp only [map_add, inner_add_right, hs, ht]
        | smul r s _ hs => rw [map_smul, map_smul, hlin, hlin, hs]
      -- then: `x` arbitrary
      intro x y
      have hx : x ∈ Submodule.span ℂ
          {t : (D₂ ⊗[ℂ] ((domSpace Hs D₂).pow n).carrier) |
            ∃ (p : D₂) (q : ((domSpace Hs D₂).pow n)), p ⊗ₜ[ℂ] q = t} := by
        rw [TensorProduct.span_tmul_eq_top]; trivial
      induction hx using Submodule.span_induction with
      | mem t ht =>
          obtain ⟨a, b, rfl⟩ := ht
          exact hpure a b y
      | zero => simp
      | add s t _ _ hs ht => simp only [map_add, inner_add_left, hs, ht]
      | smul r s _ hs => rw [map_smul, map_smul, hlinL, hlinL, hs]

/-- The sector derivation, as an operator on `sectorDom` inside `H^{⊗n}`, is symmetric. -/
theorem symmetricOn_sectorOp (hA : SymmetricOn D₂ A) (n : ℕ) :
    SymmetricOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n) := by
  intro x y
  obtain ⟨x₀, hx₀⟩ := x.2
  obtain ⟨y₀, hy₀⟩ := y.2
  have hx : (x : Hs.pow n) = inclPow Hs D₂ n x₀ := hx₀.symm
  have hy : (y : Hs.pow n) = inclPow Hs D₂ n y₀ := hy₀.symm
  rw [sectorOp_apply Hs D₂ A n x x₀ hx, sectorOp_apply Hs D₂ A n y y₀ hy, hx, hy]
  exact derPow_symm Hs D₂ A hA n x₀ y₀

/-! ## Non-vacuity -/

/-- The construction is not empty: a nonzero vector of the one-particle core gives a nonzero
vector of the one-particle sector core. -/
theorem exists_ne_zero_mem_sectorCore_one (hD : D ≤ D₂) {a : Hs.carrier} (haD : a ∈ D)
    (ha0 : a ≠ 0) : ∃ x ∈ sectorCore Hs D₂ D 1, x ≠ 0 := by
  refine ⟨inclPow Hs D₂ 1 ((⟨a, hD haD⟩ : D₂) ⊗ₜ[ℂ] (1 : ℂ)),
    ⟨(⟨a, hD haD⟩ : D₂) ⊗ₜ[ℂ] (1 : ℂ),
      tmul_mem_corePow Hs D₂ D (by simpa using haD) (by trivial), rfl⟩, ?_⟩
  have hnorm : ‖inclPow Hs D₂ 1 ((⟨a, hD haD⟩ : D₂) ⊗ₜ[ℂ] (1 : ℂ))‖ = ‖a‖ := by
    rw [inclPow_tmul]
    change ‖a ⊗ₜ[ℂ] inclPow Hs D₂ 0 (1 : ℂ)‖ = ‖a‖
    have h1 : inclPow Hs D₂ 0 (1 : ℂ) = (1 : ℂ) := rfl
    rw [h1, TensorProduct.norm_tmul]
    change ‖a‖ * ‖(1 : ℂ)‖ = ‖a‖
    simp
  intro hzero
  rw [hzero, norm_zero] at hnorm
  exact ha0 (norm_eq_zero.mp hnorm.symm)

/-- **Essential self-adjointness descends to the core sector.**  If the sector derivation is
essentially self-adjoint on `D₂^{⊗n}` — the situation of a self-adjoint one-particle
operator — then it is essentially self-adjoint on `D^{⊗n}` for every core `D` of `A`. -/
theorem essentiallySelfAdjointOn_sectorCore (hcore : IsGraphCore D A) (n : ℕ)
    (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)) :
    EssentiallySelfAdjointOn (sectorCore Hs D₂ D n)
      (restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n)) :=
  essentiallySelfAdjointOn_of_graphCore _ _ (isGraphCore_sectorCore Hs D₂ A D hcore n) hesa

end

end BookProof.TensorCore


