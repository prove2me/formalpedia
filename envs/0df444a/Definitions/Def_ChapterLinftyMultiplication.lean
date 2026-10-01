-- Prove2me | Definitions.Def_ChapterLinftyMultiplication
-- name    : ChapterLinftyMultiplication
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:16:32.281042+00:00
-- url     : https://prove2.me/theorems/8c4d1652-1ad0-4090-a18e-e6cf7dea5dc6
-- title:
--   Chapter LinftyMultiplication
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLinftyMultiplication.lean`): generated def bundle for ChapterLinftyMultiplication. See BookProof/ChapterLinftyMultiplication.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLinftyMultiplication.lean

import Mathlib


/-!
# The `L∞(μ)` class of the abelian von Neumann classification

The classification of abelian von Neumann algebras quoted in the book lists
three kinds of model: the finite diagonal algebras `ℓ∞(n)` (proved in
`ChapterAbelianDiagonal` / `ChapterAbelianVonNeumannFinite`), the countable
diagonal algebra `ℓ∞(ℕ)` acting on `ℓ²(ℕ)` (proved in
`ChapterAbelianDiagonalCountable`), and the **diffuse** model `L∞(μ)` acting on
`L²(μ)` by multiplication.  Only the last was missing; this module builds it.

For a measure `μ` on `α` and an essentially bounded `φ : α → ℂ`
(`MemLp φ ⊤ μ`), the multiplication operator

  `multOp φ : L²(μ) →L[ℂ] L²(μ)`,  `f ↦ φ · f`

is constructed and shown to make `φ ↦ multOp φ` a **unital, multiplicative,
`ℂ`-linear, star-preserving and commuting** representation of the essentially
bounded functions:

* `multOp_coeFn` — its defining a.e. formula `(multOp φ f)(x) = φ(x)·f(x)`;
* `norm_multOp_le` — the operator-norm bound by the essential supremum;
* `multOp_add`, `multOp_smul`, `multOp_mul`, `multOp_one` — `φ ↦ multOp φ` is a
  unital algebra homomorphism;
* `multOp_comm` — **the algebra is abelian**;
* `multOp_inner_adjoint` — `multOp (conj φ)` is the adjoint of `multOp φ`, so
  the family is star-closed and the self-adjoint elements are the real-valued
  `φ`;
* `multOp_eq_zero_iff` (finite `μ`) — the representation is **faithful**:
  `multOp φ = 0` iff `φ = 0` a.e., so `L∞(μ)` embeds into `B(L²(μ))`;
* `vonNeumann_abelian_class_Linfty` — the bundled statement, and
  `unitInterval_atomless` — for `μ = ` Lebesgue measure on `[0,1]` the model is
  *diffuse* (`μ{x} = 0` for every point), which is exactly what distinguishes it
  from the atomic `ℓ∞` models.

**Documented gap (unchanged).**  That every abelian von Neumann algebra is
*exhausted* by this list is not claimed here; it needs von-Neumann-algebra
machinery unavailable in this toolchain.  What is proved is that the `L∞(μ)`
item of the list is a genuine abelian, faithful, star-closed operator algebra.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

open MeasureTheory ENNReal Complex

namespace BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ## The multiplication operator -/

/-- Multiplying an `L²` function by an essentially bounded function stays in
`L²` (Hölder with exponents `∞, 2, 2`). -/
theorem mul_memLp_two {φ : α → ℂ} (hφ : MemLp φ ⊤ μ) (f : Lp ℂ 2 μ) :
    MemLp (fun x => φ x * (f : α → ℂ) x) 2 μ :=
  MemLp.smul (Lp.memLp f) hφ

theorem eLpNorm_mul_le {φ : α → ℂ} (hφ : MemLp φ ⊤ μ) (f : Lp ℂ 2 μ) :
    eLpNorm (fun x => φ x * (f : α → ℂ) x) 2 μ ≤ eLpNorm φ ⊤ μ * eLpNorm (f : α → ℂ) 2 μ := by
  have h : eLpNorm (φ • (f : α → ℂ)) 2 μ ≤ eLpNorm φ ⊤ μ * eLpNorm (f : α → ℂ) 2 μ :=
    eLpNorm_smul_le_mul_eLpNorm (p := ⊤) (q := 2) (r := 2)
      (Lp.memLp f).aestronglyMeasurable hφ.aestronglyMeasurable
  exact h

/-- The multiplication operator as a linear map on `L²(μ)`. -/
def multLin (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (mul_memLp_two hφ f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (mul_memLp_two hφ (f + g)),
      Lp.coeFn_add ((mul_memLp_two hφ f).toLp _) ((mul_memLp_two hφ g).toLp _),
      MemLp.coeFn_toLp (mul_memLp_two hφ f), MemLp.coeFn_toLp (mul_memLp_two hφ g),
      Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply]
    ring
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (mul_memLp_two hφ (c • f)),
      MemLp.coeFn_toLp (mul_memLp_two hφ f),
      Lp.coeFn_smul c ((mul_memLp_two hφ f).toLp _),
      Lp.coeFn_smul c f] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply, smul_eq_mul]
    ring

theorem norm_multLin_le {φ : α → ℂ} (hφ : MemLp φ ⊤ μ) (f : Lp ℂ 2 μ) :
    ‖multLin φ hφ f‖ ≤ (eLpNorm φ ⊤ μ).toReal * ‖f‖ := by
  change ‖(mul_memLp_two hφ f).toLp _‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  have h1 : eLpNorm φ ⊤ μ ≠ ⊤ := hφ.eLpNorm_lt_top.ne
  have h2 : eLpNorm (f : α → ℂ) 2 μ ≠ ⊤ := (Lp.memLp f).eLpNorm_lt_top.ne
  calc (eLpNorm (fun x => φ x * (f : α → ℂ) x) 2 μ).toReal
      ≤ (eLpNorm φ ⊤ μ * eLpNorm (f : α → ℂ) 2 μ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top h1 h2) (eLpNorm_mul_le hφ f)
    _ = (eLpNorm φ ⊤ μ).toReal * (eLpNorm (f : α → ℂ) 2 μ).toReal := ENNReal.toReal_mul

/-- **The multiplication operator** `M_φ : L²(μ) → L²(μ)`, `f ↦ φ·f`, for an
essentially bounded `φ`. -/
def multOp (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (multLin φ hφ).mkContinuous (eLpNorm φ ⊤ μ).toReal (norm_multLin_le hφ)





/-! ## The algebraic structure -/















/-! ## Faithfulness and diffuseness -/







end BookProof.ChapterLinftyMultiplication

end


