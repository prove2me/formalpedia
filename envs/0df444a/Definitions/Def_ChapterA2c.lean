-- Prove2me | Definitions.Def_ChapterA2c
-- name    : ChapterA2c
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T07:05:02.61804+00:00
-- url     : https://prove2.me/theorems/08c0d22a-b95f-4e9b-a201-0be4570742c8
-- title:
--   The Lean 4 theorem `mulI_mul_mulI` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA2c.lean`): generated def bundle for ChapterA2c. See BookProof/ChapterA2c.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA2c.lean

import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA2
import Definitions.Def_ChapterA2b
import Mathlib


/-!
# Chapter A, §A.2 — the commutant classification, R-complex and R-pseudoreal cases
(work-package N2 residue)

This file continues work-package **N2** of `FORMALIZATION_ROADMAP.md` (§A.2, the
commutant classification ℝ / ℂ / ℍ).  `ChapterA2b.lean` established **Prop 17**
(the R-real commutant is `ℝ`).  Here we formalize the remaining two entries of
the trichotomy:

* **Prop 18 (R-complex commutant `≅ ℂ`)** and
* **Prop 19 (R-pseudoreal commutant `≅ ℍ`)**.

## The setup

For a complex system `(M, V)` we work with the **real commutant** — the
continuous **`ℝ`-linear** operators on `V` commuting with every `m ∈ M`
(`RealCommutes`).  Two canonical real operators live inside it:

* `mulI` — multiplication by `i` (`ℂ`-linear, hence always commutes with `M`),
  with `mulI * mulI = -1`;
* `thetaR θ` — the real-linear operator underlying a commuting anti-unitary `θ`
  (conjugate-linear), which commutes with `M` exactly when `θ` does.

Since `mulI * mulI = -1`, the pair `(ℝ, mulI)` gives an `ℝ`-algebra embedding
`ℂ →ₐ[ℝ] (V →L[ℝ] V)` (`cembed`).  When additionally `θ² = -1` (the
R-pseudoreal / quaternionic anti-unitary), the triple `mulI, thetaR θ,
mulI·thetaR θ` satisfies the quaternion relations `i² = j² = -1`, `ij = -ji`,
giving an `ℝ`-algebra embedding `ℍ →ₐ[ℝ] (V →L[ℝ] V)` (`qembed`).

The classification results say these embeddings are **onto the real commutant**:

* Prop 18: if the linear commutant is `ℂ` (`IsSchurFull`) and there is **no**
  nonzero commuting `ℂ`-antilinear operator (`NoAntilinearCommutant`, the precise
  algebraic content of C-complex), then the real commutant is exactly the image
  of `cembed`, i.e. `≅ ℂ`.
* Prop 19: if the linear commutant is `ℂ` (`IsSchurFull`) and `θ` is a commuting
  anti-unitary with `θ² = -1`, then the real commutant is exactly the image of
  `qembed`, i.e. `≅ ℍ` (the antilinear part is `ℂ·θ` by the Schur argument, so the
  four generators `1, i, θ, iθ` span the commutant).

The engine of both reverse inclusions is the **linear/antilinear decomposition**
of a real-linear operator `S = Plin S + Qanti S`, where `Plin S` commutes with
`mulI` (so is `ℂ`-linear, hence a scalar by `IsSchurFull`) and `Qanti S`
anticommutes with `mulI` (so is `ℂ`-antilinear).

Schur's lemma for the representation (flagged `EXTERNAL` for unitary reps by the
roadmap) enters only through the named hypothesis `IsSchurFull` (see
`ChapterA2b.lean`), never as an `axiom`.
-/

open scoped ComplexConjugate InnerProductSpace Quaternion

namespace BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ## Real-linear incarnations of `i` and of an anti-unitary -/

/-- The real-linear continuous operator underlying a conjugate-linear continuous
map. -/
noncomputable def toRealCLM (f : V →SL[starRingEnd ℂ] V) : V →L[ℝ] V where
  toLinearMap :=
  { toFun := f
    map_add' := f.map_add
    map_smul' := by
      intro r x
      simp only [RingHom.id_apply]
      have := f.map_smulₛₗ (r : ℂ) x
      simpa [Complex.coe_smul, Complex.conj_ofReal] using this }
  cont := f.continuous

omit [CompleteSpace V] in
@[simp] lemma toRealCLM_apply (f : V →SL[starRingEnd ℂ] V) (x : V) :
    toRealCLM f x = f x := rfl

/-- The real-linear operator underlying an anti-unitary `θ`. -/
noncomputable def thetaR (θ : AntiUnitary V) : V →L[ℝ] V :=
  toRealCLM (θ.toContinuousLinearEquiv.toContinuousLinearMap)

omit [CompleteSpace V] in
@[simp] lemma thetaR_apply (θ : AntiUnitary V) (x : V) : thetaR θ x = θ x := rfl

/-- Multiplication by `i`, as a real-linear continuous operator. -/
noncomputable def mulI : V →L[ℝ] V :=
  ContinuousLinearMap.restrictScalars ℝ ((Complex.I : ℂ) • (1 : V →L[ℂ] V))

omit [CompleteSpace V] in
@[simp] lemma mulI_apply (x : V) : (mulI : V →L[ℝ] V) x = (Complex.I : ℂ) • x := rfl

omit [CompleteSpace V] in
lemma mulI_mul_mulI : (mulI : V →L[ℝ] V) * mulI = -1 := by
  ext x
  simp only [ContinuousLinearMap.mul_apply, mulI_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.one_apply]
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

/-! ## The real commutant -/

/-- An `ℝ`-linear operator `S` **commutes with** the complex system `M` iff it
commutes with every `m ∈ M` (as functions).  This is the *real commutant*. -/
def RealCommutes (M : System ℂ V) (S : V →L[ℝ] V) : Prop :=
  ∀ m ∈ M.ops, ∀ x, S (m x) = m (S x)

















/-! ## Prop 18 (partial) — the `ℂ`-embedding into the real commutant -/

/-- The `ℝ`-algebra embedding `ℂ →ₐ[ℝ] (V →L[ℝ] V)` determined by
`i ↦ mulI` (`mulI² = -1`).  Its image is the `ℝ`-span of `1` and `mulI`, i.e. the
complex scalars viewed as real operators. -/
noncomputable def cembed : ℂ →ₐ[ℝ] (V →L[ℝ] V) :=
  Complex.lift ⟨mulI, mulI_mul_mulI⟩

omit [CompleteSpace V] in
@[simp] lemma cembed_I : cembed (Complex.I : ℂ) = (mulI : V →L[ℝ] V) := by
  rw [cembed, Complex.lift_apply, Complex.liftAux_apply]; simp







/-! ## Prop 19 (partial) — the `ℍ`-embedding into the real commutant -/

/-- The quaternion basis `(i, j, k) = (mulI, thetaR θ, mulI·thetaR θ)` on the
real operator algebra, valid when `θ² = -1`.  Verifies `i² = -1`, `j² = -1`,
`ij = k`, `ji = -k`. -/
noncomputable def qbasis (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = -x) :
    QuaternionAlgebra.Basis (V →L[ℝ] V) (-1 : ℝ) (0 : ℝ) (-1 : ℝ) where
  i := mulI
  j := thetaR θ
  k := mulI * thetaR θ
  i_mul_i := by ext x; simp [ContinuousLinearMap.mul_apply, smul_smul, Complex.I_mul_I]
  j_mul_j := by ext x; simp [ContinuousLinearMap.mul_apply, hθ]
  i_mul_j := rfl
  j_mul_i := by
    ext x
    simp only [ContinuousLinearMap.mul_apply, thetaR_apply, mulI_apply]
    rw [θ.map_smulₛₗ]; simp

/-- The `ℝ`-algebra embedding `ℍ →ₐ[ℝ] (V →L[ℝ] V)` for an R-pseudoreal
anti-unitary `θ` (`θ² = -1`), sending `i, j, k` to `mulI, thetaR θ,
mulI·thetaR θ`. -/
noncomputable def qembed (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = -x) :
    (Quaternion ℝ) →ₐ[ℝ] (V →L[ℝ] V) :=
  QuaternionAlgebra.lift (qbasis θ hθ)







/-! ## The linear / antilinear decomposition -/

/-- A real-linear operator commuting with `mulI` is complex-linear. -/
noncomputable def cplxify (T : V →L[ℝ] V)
    (hT : ∀ x, T (Complex.I • x) = Complex.I • T x) : V →L[ℂ] V where
  toLinearMap :=
  { toFun := T
    map_add' := T.map_add
    map_smul' := by
      intro c x
      simp only [RingHom.id_apply]
      have hre : ∀ (r : ℝ) (y : V), T ((r : ℂ) • y) = (r : ℂ) • T y := by
        intro r y
        have := T.map_smul r y
        simp only [Complex.coe_smul]; exact this
      calc T (c • x) = T (((c.re : ℂ) + (c.im : ℂ) * Complex.I) • x) := by
                        rw [Complex.re_add_im]
        _ = (c.re : ℂ) • T x + (c.im : ℂ) • (Complex.I • T x) := by
                        rw [add_smul, mul_smul, map_add, hre, hre, hT]
        _ = c • T x := by rw [smul_smul, ← add_smul, Complex.re_add_im] }
  cont := T.continuous

omit [CompleteSpace V] in
@[simp] lemma cplxify_apply (T : V →L[ℝ] V)
    (hT : ∀ x, T (Complex.I • x) = Complex.I • T x) (x : V) : cplxify T hT x = T x := rfl



/-- The `ℂ`-linear part of a real-linear operator. -/
noncomputable def Plin (S : V →L[ℝ] V) : V →L[ℝ] V :=
  (2⁻¹ : ℝ) • (S - mulI * S * mulI)

/-- The `ℂ`-antilinear part of a real-linear operator. -/
noncomputable def Qanti (S : V →L[ℝ] V) : V →L[ℝ] V :=
  (2⁻¹ : ℝ) • (S + mulI * S * mulI)















/-! ## Prop 18 — the R-complex commutant is `ℂ` -/

/-- **No antilinear commutant.**  The precise algebraic content of the C-complex
type: no nonzero `ℂ`-antilinear continuous operator commutes with `M`.  (An
anti-unitary is a nonzero commuting antilinear operator, so this implies
`IsCComplex`; see `noAntilinearCommutant_isCComplex`.) -/
def NoAntilinearCommutant (M : System ℂ V) : Prop :=
  ∀ T : V →L[ℝ] V,
    (∀ x, T (Complex.I • x) = -(Complex.I • T x)) → RealCommutes M T → T = 0





/-! ## Prop 19 — the R-pseudoreal commutant is `ℍ` -/



end BookProof.ChapterA


