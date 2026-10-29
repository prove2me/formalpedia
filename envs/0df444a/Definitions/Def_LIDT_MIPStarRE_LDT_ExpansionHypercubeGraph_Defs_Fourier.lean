-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
-- name    : LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:33:41.231112+00:00
-- url     : https://prove2.me/theorems/036ef4b8-9d6e-4718-abbe-45fa6e7884e5
-- title:
--   LIDT definitions: LDT / ExpansionHypercubeGraph / Defs / Fourier
-- statement:
--   This bundle defines the Fourier objects used to analyze local and global variance on the hypercube graph. It introduces additive characters, finite-field dot products, normalized Fourier basis vectors and projectors, and packaged trace witnesses for the local and global variance rewrites.
--
--   Principal definitions:
--   - `addCharFq`: the additive character of the coded finite field.
--   - `dotProductFq`: the finite-field dot product of two points.
--   - `fourierBasisState`: the normalized Fourier basis vector indexed by a frequency.
--   - `dotProductZMod`: the same dot product computed in `ZMod`.
--   - `fourierBasisProjector`: the rank-one projector associated with a Fourier basis vector.
--   - `localVarianceTraceWitness`: the trace witness for the local-variance rewrite.
--   - `GlobalVarianceDecomposition`: the packaged decomposition used by the global-variance rewrite.
--   - `globalVarianceTraceWitness`: the trace witness for the global-variance rewrite.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Fourier.lean#L37-L638

-- Generated from MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Fourier.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

/-!
# Section 7 hypercube graph: Fourier basis

Additive characters and the Fourier basis of `ℂ^{F_q^m}` used to diagonalize
the hypercube adjacency matrix `K`.

## References

- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch05_expansion.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Fourier analysis on the hypercube `F_q^m`

The Fourier basis of `ℂ^{F_q^m}` consists of the character vectors
`φ_α(u) = (1/√M) · ω^{⟨u, α⟩}` for `α ∈ F_q^m`,
where `ω = exp(2πi/q)` and `⟨u, α⟩ = ∑ᵢ uᵢ · αᵢ (mod q)`.

These are eigenvectors of the adjacency matrix `K` with known eigenvalues
(`prop:eigenvectors` in the paper). -/

/-- The additive character `χ_q : F_q → ℂ` sending `a ↦ exp(2πi · a / q)`. -/
noncomputable def addCharFq (params : Parameters) (a : Fq params) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / (params.q : ℂ))

/-- The dot product `⟨u, α⟩ = ∑ᵢ uᵢ · αᵢ` in `F_q`, computed via natural number
arithmetic and reduced mod `q`. -/
def dotProductFq (params : Parameters) (u α : Point params) : Fq params :=
  ⟨(∑ i : Fin params.m, (u i).val * (α i).val) % params.q,
    Nat.mod_lt _ params.hq⟩

/-- The Fourier basis vector `φ_α : Point params → ℂ`, defined by
`φ_α(u) = (1/√M) · exp(2πi ⟨u, α⟩ / q)`. -/
noncomputable def fourierBasisState (params : Parameters)
    (α : Point params) : Point params → ℂ :=
  fun u => ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
    addCharFq params (dotProductFq params u α)

/-- The same dot product as `dotProductFq`, but computed directly in `ZMod q`. -/
noncomputable def dotProductZMod (params : Parameters) (u α : Point params) : ZMod params.q :=
  ∑ i : Fin params.m, ((u i).val : ZMod params.q) * ((α i).val : ZMod params.q)

lemma addCharFq_eq_stdAddChar (params : Parameters) (a : Fq params) :
    addCharFq params a = ZMod.stdAddChar (N := params.q) (a.val : ZMod params.q) := by
  simpa [addCharFq] using (ZMod.stdAddChar_coe (N := params.q) a.val).symm

lemma addCharFq_dotProduct_eq_stdAddChar_dotProductZMod (params : Parameters)
    (u α : Point params) :
    addCharFq params (dotProductFq params u α) =
      ZMod.stdAddChar (N := params.q) (dotProductZMod params u α) := by
  rw [addCharFq_eq_stdAddChar]
  change ZMod.stdAddChar (N := params.q)
      ((((∑ i : Fin params.m, (u i).val * (α i).val) % params.q : ℕ) : ZMod params.q)) = _
  congr
  simp [dotProductZMod]

lemma dotProductZMod_update (params : Parameters) (u α : Point params)
    (i : Fin params.m) (x : Fq params) :
    dotProductZMod params (Function.update u i x) α =
      dotProductZMod params u α +
        (((x.val : ZMod params.q) - (u i).val) * ((α i).val : ZMod params.q)) := by
  classical
  unfold dotProductZMod
  have hfun :
      (fun j : Fin params.m =>
        ((Function.update u i x j).val : ZMod params.q) * ((α j).val : ZMod params.q)) =
        (fun j : Fin params.m => ((u j).val : ZMod params.q) * ((α j).val : ZMod params.q)) +
          Pi.single i (((x.val : ZMod params.q) - (u i).val) * ((α i).val : ZMod params.q)) := by
    ext j
    by_cases h : j = i
    · subst h
      simp [Function.update]
      ring_nf
    · simp [Function.update, h]
  rw [hfun]
  simp_rw [Pi.add_apply]
  rw [Finset.sum_add_distrib]
  simp

lemma sum_stdAddChar_mul_fin (params : Parameters) (a : ZMod params.q) :
    ∑ x : Fq params, ZMod.stdAddChar (N := params.q) (((x.val : ZMod params.q) * a)) =
      if a = 0 then params.q else 0 := by
  let e : Fq params ≃ ZMod params.q :=
    { toFun := fun x => (x.val : ZMod params.q)
      invFun := fun z => ⟨z.val, z.val_lt⟩
      left_inv := fun x => Fin.ext (ZMod.val_natCast_of_lt x.2)
      right_inv := ZMod.natCast_zmod_val }
  calc
    ∑ x : Fq params, ZMod.stdAddChar (N := params.q) (((x.val : ZMod params.q) * a))
      = ∑ x : Fq params, ZMod.stdAddChar (N := params.q) ((e x) * a) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          simp [e]
    _ = ∑ z : ZMod params.q, ZMod.stdAddChar (N := params.q) (z * a) := by
          exact Fintype.sum_equiv e
            (fun x => ZMod.stdAddChar (N := params.q) ((e x) * a))
            (fun z => ZMod.stdAddChar (N := params.q) (z * a))
            (fun x => rfl)
    _ = if a = 0 then Fintype.card (ZMod params.q) else 0 := by
          simpa using (AddChar.sum_mulShift (R := ZMod params.q) (R' := ℂ)
            (ψ := ZMod.stdAddChar (N := params.q)) a (ZMod.isPrimitive_stdAddChar params.q))
    _ = if a = 0 then params.q else 0 := by
          simp

lemma fourierBasisState_update_sum (params : Parameters) (u α : Point params)
    (i : Fin params.m) :
    ∑ x : Fq params, fourierBasisState params α (Function.update u i x) =
      ((if α i = (0 : Fq params) then params.q else 0 : ℕ) : ℂ) *
        fourierBasisState params α u := by
  let ψ := ZMod.stdAddChar (N := params.q)
  let ai : ZMod params.q := ((α i).val : ZMod params.q)
  let ui : ZMod params.q := ((u i).val : ZMod params.q)
  have hchar (x : Fq params) :
      ψ (dotProductZMod params (Function.update u i x) α) =
        ψ (dotProductZMod params u α - ui * ai) * ψ ((x.val : ZMod params.q) * ai) := by
    calc
      ψ (dotProductZMod params (Function.update u i x) α) =
          ψ ((dotProductZMod params u α - ui * ai) + ((x.val : ZMod params.q) * ai)) := by
            rw [dotProductZMod_update]
            simp [ui, ai]
            ring_nf
      _ = ψ (dotProductZMod params u α - ui * ai) * ψ ((x.val : ZMod params.q) * ai) := by
            rw [AddChar.map_add_eq_mul]
  have hsum :
      ∑ x : Fq params, fourierBasisState params α (Function.update u i x) =
        (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
          ψ (dotProductZMod params u α - ui * ai)) *
            ∑ x : Fq params, ψ ((x.val : ZMod params.q) * ai) := by
    unfold fourierBasisState
    simp_rw [addCharFq_dotProduct_eq_stdAddChar_dotProductZMod]
    change ∑ x : Fq params,
        (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
          ψ (dotProductZMod params (Function.update u i x) α)) = _
    simp_rw [hchar]
    rw [← Finset.mul_sum]
    calc
      ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
          ∑ x : Fq params,
            ψ (dotProductZMod params u α - ui * ai) *
              ψ ((x.val : ZMod params.q) * ai)
        = ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
            (ψ (dotProductZMod params u α - ui * ai) *
              ∑ x : Fq params, ψ ((x.val : ZMod params.q) * ai)) := by
            rw [← Finset.mul_sum]
      _ = (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
            ψ (dotProductZMod params u α - ui * ai)) *
            ∑ x : Fq params, ψ ((x.val : ZMod params.q) * ai) := by
            ring_nf
  rw [hsum, sum_stdAddChar_mul_fin]
  by_cases hαi : α i = (0 : Fq params)
  · simp [ai, ui, ψ, hαi, fourierBasisState,
      addCharFq_dotProduct_eq_stdAddChar_dotProductZMod, mul_comm]
  · have hai : ai ≠ 0 := by
      intro hai0
      apply hαi
      ext
      have hval := congrArg ZMod.val hai0
      simpa [ai, Nat.mod_eq_of_lt (α i).2] using hval
    simp [ai, ui, ψ, hαi, hai, fourierBasisState,
      addCharFq_dotProduct_eq_stdAddChar_dotProductZMod, mul_comm]

/-- The Fourier basis projector `|φ_α⟩⟨φ_α|` as a matrix on `Point params`. -/
noncomputable def fourierBasisProjector (params : Parameters)
    (α : Point params) : MIPStarRE.Quantum.Op (Point params) :=
  Matrix.vecMulVec (fourierBasisState params α)
    (star (fourierBasisState params α))

/-- Paper origin: `references/ldt-paper/expansion.tex:145-154`
(`\label{lem:local-rewrite}`); trace witness for the local-variance rewrite. -/
noncomputable def localVarianceTraceWitness (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    MIPStarRE.Quantum.Op ι :=
  let Acombine := combinedOperator params A
  let liftedLaplacianState :
      Matrix (combinedColumnIndex params ι) (combinedColumnIndex params ι) ℂ :=
    Matrix.kronecker (laplacian params) ψ.density
  Acombineᴴ * (liftedLaplacianState * Acombine)

/-- A packaged decomposition for `lem:global-rewrite`.

The Lean witness stores the pointwise average `A_avg = E_u A^u` together with the
full residual family `u ↦ A^u - A_avg`. This carries the same geometric content as
writing `A_combine = |φ₀⟩ ⊗ A₀ + |φ_⊥⟩ ⊗ A_⊥`, but it does not force
the orthogonal part to be rank one on `Point params ⊗ ι`. -/
structure GlobalVarianceDecomposition (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) where
  averageComponent : MIPStarRE.Quantum.Op ι
  orthogonalComponent : Point params → MIPStarRE.Quantum.Op ι
  averageComponent_eq :
    averageComponent = ((hypercubeVertexCount params : ℂ)⁻¹) • ∑ u, A u
  orthogonal_sum_zero :
    ∑ u, orthogonalComponent u = 0
  decomposition :
    ∀ u, A u = averageComponent + orthogonalComponent u







/-- Paper origin: `references/ldt-paper/expansion.tex:179-190`
(`\label{lem:global-rewrite}`); trace witness for the global-variance rewrite.
This uses the orthogonal residual family supplied by the decomposition. -/
noncomputable def globalVarianceTraceWitness (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι)
    (decomp : GlobalVarianceDecomposition params A) : MIPStarRE.Quantum.Op ι :=
  let orthogonalCombine := combinedOperator params decomp.orthogonalComponent
  let liftedState :
      Matrix (combinedColumnIndex params ι) (combinedColumnIndex params ι) ℂ :=
    Matrix.kronecker (1 : MIPStarRE.Quantum.Op (Point params)) ψ.density
  orthogonalCombineᴴ * (liftedState * orthogonalCombine)

/-- The local-variance trace expression from `lem:local-rewrite`. -/
noncomputable def localVarianceTraceForm (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Error :=
  Complex.re (MIPStarRE.Quantum.normalizedTrace (localVarianceTraceWitness params A ψ))

/-- The global-variance trace expression from `lem:global-rewrite`.

The prefactor `1 / hypercubeVertexCount params` is the paper's `1 / M`
normalization from Section 7. -/
noncomputable def globalVarianceTraceForm (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι)
    (decomp : GlobalVarianceDecomposition params A) : Error :=
  (1 / (hypercubeVertexCount params : Error)) *
    Complex.re (MIPStarRE.Quantum.normalizedTrace (globalVarianceTraceWitness params A ψ decomp))

/-- The number of nonzero coordinates of a frequency `α ∈ F_q^m`. -/
noncomputable def frequencyWeight (params : Parameters) (α : Point params) : ℕ :=
  (Finset.univ.filter (fun i : Fin params.m => α i ≠ ⟨0, params.hq⟩)).card

/-- The number of nonzero coordinates of `α` is at most `m`. -/
lemma frequencyWeight_le_m (params : Parameters) (α : Point params) :
    frequencyWeight params α ≤ params.m := by
  exact le_trans (Finset.card_filter_le _ _)
    (by simp [Finset.card_univ, Fintype.card_fin])

lemma zeroCoordinateCount_eq (params : Parameters) (α : Point params) :
    (Finset.univ.filter (fun i : Fin params.m => α i = (0 : Fq params))).card =
      params.m - frequencyWeight params α := by
  rw [frequencyWeight]
  apply Nat.eq_sub_of_add_eq
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin params.m)))
    (p := fun i : Fin params.m => α i = (0 : Fq params))
  rw [Finset.card_univ, Fintype.card_fin] at h
  convert h using 1
  congr 1

lemma zeroCoordinateContributionSum (params : Parameters) (α : Point params) :
    ∑ i : Fin params.m, (((if α i = (0 : Fq params) then params.q else 0 : ℕ) : ℂ)) =
      (((params.m - frequencyWeight params α : ℕ) : ℂ) * (params.q : ℂ)) := by
  calc
    ∑ i : Fin params.m, (((if α i = (0 : Fq params) then params.q else 0 : ℕ) : ℂ))
      = ((Finset.univ.filter (fun i : Fin params.m => α i = (0 : Fq params))).card : ℂ) *
          (params.q : ℂ) := by
            rw [← Nat.cast_sum, Finset.sum_ite]
            simp [mul_comm]
    _ = (((params.m - frequencyWeight params α : ℕ) : ℂ) * (params.q : ℂ)) := by
          rw [zeroCoordinateCount_eq]

lemma fourierBasisState_total_update_sum (params : Parameters) (u α : Point params) :
    ∑ i : Fin params.m, ∑ x : Fq params, fourierBasisState params α (Function.update u i x) =
      ((((params.m - frequencyWeight params α : ℕ) : ℂ) * (params.q : ℂ)) *
        fourierBasisState params α u) := by
  calc
    ∑ i : Fin params.m, ∑ x : Fq params, fourierBasisState params α (Function.update u i x)
      = ∑ i : Fin params.m,
          (((if α i = (0 : Fq params) then params.q else 0 : ℕ) : ℂ) *
            fourierBasisState params α u) := by
              congr 1 with i
              exact fourierBasisState_update_sum params u α i
    _ = (∑ i : Fin params.m,
          (((if α i = (0 : Fq params) then params.q else 0 : ℕ) : ℂ))) *
          fourierBasisState params α u := by
            rw [Finset.sum_mul]
    _ = ((((params.m - frequencyWeight params α : ℕ) : ℂ) * (params.q : ℂ)) *
          fourierBasisState params α u) := by
            rw [zeroCoordinateContributionSum]



/-- The additive character on `Point params` indexed by a frequency `α`. -/
noncomputable def pointAddChar (params : Parameters) (α : Point params) :
    AddChar (Point params) ℂ where
  toFun u := ZMod.stdAddChar (N := params.q) (dotProductZMod params u α)
  map_zero_eq_one' := by
    simp [dotProductZMod]
  map_add_eq_mul' := by
    intro u v
    have hdot :
        dotProductZMod params (u + v) α =
          dotProductZMod params u α + dotProductZMod params v α := by
      unfold dotProductZMod
      calc
        ∑ i, (((u + v) i).val : ZMod params.q) * ((α i).val : ZMod params.q)
          = ∑ i,
              ((((u i).val : ZMod params.q) + ((v i).val : ZMod params.q)) *
                ((α i).val : ZMod params.q)) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  have hcast :
                      ((((u + v) i).val : ZMod params.q)) =
                        ((u i).val : ZMod params.q) + ((v i).val : ZMod params.q) := by
                    simp [Fin.val_add]
                  rw [hcast]
        _ = ∑ i,
              (((u i).val : ZMod params.q) * ((α i).val : ZMod params.q) +
                ((v i).val : ZMod params.q) * ((α i).val : ZMod params.q)) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  ring
        _ = dotProductZMod params u α + dotProductZMod params v α := by
              simp [dotProductZMod, Finset.sum_add_distrib]
    rw [hdot, AddChar.map_add_eq_mul]

/-- The additive character on the frequency space obtained by fixing a point `u`. -/
noncomputable def pointAddCharRight (params : Parameters) (u : Point params) :
    AddChar (Point params) ℂ where
  toFun α := ZMod.stdAddChar (N := params.q) (dotProductZMod params u α)
  map_zero_eq_one' := by
    simp [dotProductZMod]
  map_add_eq_mul' := by
    intro α β
    have hdot :
        dotProductZMod params u (α + β) =
          dotProductZMod params u α + dotProductZMod params u β := by
      unfold dotProductZMod
      calc
        ∑ i, ((u i).val : ZMod params.q) * (((α + β) i).val : ZMod params.q)
          = ∑ i,
              (((u i).val : ZMod params.q) *
                (((α i).val : ZMod params.q) + ((β i).val : ZMod params.q))) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  have hcast :
                      ((((α + β) i).val : ZMod params.q)) =
                        ((α i).val : ZMod params.q) + ((β i).val : ZMod params.q) := by
                    simp [Fin.val_add]
                  rw [hcast]
        _ = ∑ i,
              (((u i).val : ZMod params.q) * ((α i).val : ZMod params.q) +
                ((u i).val : ZMod params.q) * ((β i).val : ZMod params.q)) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  ring
        _ = dotProductZMod params u α + dotProductZMod params u β := by
              simp [dotProductZMod, Finset.sum_add_distrib]
    rw [hdot, AddChar.map_add_eq_mul]

/-- Updating the zero point at coordinate `i` with the field element `1` yields the
standard basis vector `e_i`, whose `ZMod q` dot product with `α` is the `i`-th
coordinate of `α`. -/
lemma dotProductZMod_single_one (params : Parameters) (α : Point params) (i : Fin params.m) :
    dotProductZMod params
      (Function.update (0 : Point params) i ⟨1 % params.q, Nat.mod_lt 1 params.hq⟩) α =
        ((α i).val : ZMod params.q) := by
  unfold dotProductZMod
  rw [Finset.sum_eq_single i]
  · simp [Function.update]
  · intro j _ hji
    simp [Function.update, hji]
  · simp

/-- `pointAddChar params α` is trivial exactly when `α = 0`.

Here the `0` on the left is the `Zero` instance on `AddChar`, i.e. the trivial
character `u ↦ 1`, not the pointwise-zero function. -/
lemma pointAddChar_eq_zero_iff (params : Parameters) (α : Point params) :
    pointAddChar params α = 0 ↔ α = 0 := by
  constructor
  · intro h
    funext i
    let e : Point params :=
      Function.update (0 : Point params) i ⟨1 % params.q, Nat.mod_lt 1 params.hq⟩
    have hchar :
        ZMod.stdAddChar (N := params.q) (((α i).val : ZMod params.q)) = 1 := by
      simpa [pointAddChar, e, dotProductZMod_single_one] using
        (congrArg (fun ψ : AddChar (Point params) ℂ => ψ e) h)
    have hz : (((α i).val : ZMod params.q)) = 0 := by
      exact (AddChar.IsPrimitive.zmod_char_eq_one_iff params.q
        (ZMod.isPrimitive_stdAddChar params.q) _).mp hchar
    apply Fin.ext
    have hval := congrArg ZMod.val hz
    simpa [Nat.mod_eq_of_lt (α i).2] using hval
  · rintro rfl
    ext u
    simp [pointAddChar, dotProductZMod]

/-- The actual Fourier inner product equals the Kronecker delta.
This proves `∑_u conj(φ_α(u)) * φ_β(u) = if α = β then 1 else 0`. -/
lemma fourierBasisState_inner_product (params : Parameters) (α β : Point params) :
    ∑ u : Point params, star (fourierBasisState params α u) * fourierBasisState params β u =
      if α = β then 1 else 0 := by
  have hcard :
      Fintype.card (Point params) = hypercubeVertexCount params := by
    simp [hypercubeVertexCount, Fintype.card_fin]
  have hMpos : 0 < (hypercubeVertexCount params : ℝ) := by
    exact_mod_cast (pow_pos params.hq params.m)
  have hM_nonneg : 0 ≤ (hypercubeVertexCount params : ℝ) := by
    positivity
  have hnormR :
      (Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ *
          (Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ =
        (hypercubeVertexCount params : ℝ)⁻¹ := by
    rw [← mul_inv_rev, ← sq, Real.sq_sqrt hM_nonneg]
  have hnorm :
      (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
          ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ)) =
        ((Fintype.card (Point params) : ℂ)⁻¹) := by
    rw [hcard]
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hnormR
  calc
    ∑ u : Point params, star (fourierBasisState params α u) * fourierBasisState params β u
      = ∑ u : Point params,
          ((Fintype.card (Point params) : ℂ)⁻¹) *
            (star (pointAddChar params α u) * pointAddChar params β u) := by
              refine Finset.sum_congr rfl ?_
              intro u _
              unfold fourierBasisState pointAddChar
              rw [addCharFq_dotProduct_eq_stdAddChar_dotProductZMod,
                addCharFq_dotProduct_eq_stdAddChar_dotProductZMod]
              calc
                star ((((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
                    ZMod.stdAddChar (N := params.q) (dotProductZMod params u α))) *
                    ((((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
                      ZMod.stdAddChar (N := params.q) (dotProductZMod params u β)))
                  = ((((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
                      ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ)) *
                      (star (ZMod.stdAddChar (N := params.q) (dotProductZMod params u α)) *
                        ZMod.stdAddChar (N := params.q) (dotProductZMod params u β))) := by
                          simp [mul_assoc, mul_left_comm, mul_comm]
                _ = ((Fintype.card (Point params) : ℂ)⁻¹) *
                      (star (ZMod.stdAddChar (N := params.q) (dotProductZMod params u α)) *
                        ZMod.stdAddChar (N := params.q) (dotProductZMod params u β)) := by
                          rw [hnorm]
    _ = ((Fintype.card (Point params) : ℂ)⁻¹) *
          ∑ u : Point params, pointAddChar params (β - α) u := by
          rw [← Finset.mul_sum]
          apply congrArg (fun z : ℂ => ((Fintype.card (Point params) : ℂ)⁻¹) * z)
          refine Finset.sum_congr rfl ?_
          intro u _
          have hstar :
              star (pointAddChar params α u) = (pointAddChar params α u)⁻¹ := by
            simpa [Complex.star_def] using
              (AddChar.inv_apply_eq_conj (ψ := pointAddChar params α) u).symm
          calc
            star (pointAddChar params α u) * pointAddChar params β u
              = (pointAddChar params α u)⁻¹ * pointAddChar params β u := by rw [hstar]
            _ = pointAddChar params β u / pointAddChar params α u := by
                  rw [div_eq_mul_inv, mul_comm]
            _ = pointAddChar params (β - α) u := by
                  simpa [pointAddChar, pointAddCharRight] using
                    (AddChar.map_sub_eq_div (ψ := pointAddCharRight params u) β α).symm
    _ = 𝔼 u : Point params, pointAddChar params (β - α) u := by
          rw [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
          simp [mul_comm]
    _ = if pointAddChar params (β - α) = 0 then 1 else 0 := by
          simpa using AddChar.expect_eq_ite (pointAddChar params (β - α))
    _ = if α = β then 1 else 0 := by
          by_cases h0 : pointAddChar params (β - α) = 0
          · have hab : α = β := by
              have hsub : β - α = 0 := (pointAddChar_eq_zero_iff params (β - α)).mp h0
              exact (sub_eq_zero.mp hsub).symm
            have hzero : pointAddChar params (0 : Point params) = 0 :=
              (pointAddChar_eq_zero_iff params (0 : Point params)).2 rfl
            simp [hab, hzero]
          · have hab : α ≠ β := by
              intro hab
              apply h0
              apply (pointAddChar_eq_zero_iff params (β - α)).2
              simp [hab]
            simp [h0, hab]



/-- The eigenvalue of `K` on `φ_α`. -/
noncomputable def adjacencyEigenvalue (params : Parameters) (α : Point params) : Error :=
  (1 / (hypercubeVertexCount params : Error)) *
    (((params.m - frequencyWeight params α : ℕ) : Error) / (params.m : Error))

/-- The eigenvalue of `L` on `φ_α`. -/
noncomputable def laplacianEigenvalue (params : Parameters) (α : Point params) : Error :=
  (frequencyWeight params α : Error) /
    ((params.m : Error) * (hypercubeVertexCount params : Error))

/-- The spectral gap `1 / (m M)` from `cor:laplacian-spectral-gap`. -/
noncomputable def hypercubeSpectralGap (params : Parameters) : Error :=
  1 / ((params.m : Error) * (hypercubeVertexCount params : Error))



/-- `prop:eigenvectors`, item 2: each `|φ_α⟩` is an eigenvector of the
adjacency matrix `K` with eigenvalue `λ_α`. -/
theorem eigenvectors (params : Parameters) (α : Point params) :
    (matrixAdjacencyOperator params).mulVec (fourierBasisState params α) =
      ((adjacencyEigenvalue params α : ℝ) : ℂ) • fourierBasisState params α := by
  ext u
  change Point params at u
  let c : ℂ := (((params.m : ℂ) * (params.q : ℂ) * (hypercubeVertexCount params : ℂ))⁻¹)
  have hmul :
      (matrixAdjacencyOperator params).mulVec (fourierBasisState params α) u =
        c * ∑ i : Fin params.m, ∑ x : Fq params,
          fourierBasisState params α (Function.update u i x) := by
    calc
      (matrixAdjacencyOperator params).mulVec (fourierBasisState params α) u
        = c * ∑ p : Fin params.m × Fq params,
            fourierBasisState params α (Function.update u p.1 p.2) := by
              change ∑ v : Point params,
                  (c * ∑ p : Fin params.m × Fq params,
                    if Function.update u p.1 p.2 = v then (1 : ℂ) else 0) *
                    fourierBasisState params α v =
                c * ∑ p : Fin params.m × Fq params,
                  fourierBasisState params α (Function.update u p.1 p.2)
              simp_rw [mul_assoc]
              rw [← Finset.mul_sum]
              apply congrArg (fun z : ℂ => c * z)
              calc
                ∑ v : Point params,
                    (∑ p : Fin params.m × Fq params,
                      if Function.update u p.1 p.2 = v then (1 : ℂ) else 0) *
                      fourierBasisState params α v
                  = ∑ v : Point params, ∑ p : Fin params.m × Fq params,
                      (if Function.update u p.1 p.2 = v then (1 : ℂ) else 0) *
                        fourierBasisState params α v := by
                          refine Finset.sum_congr rfl ?_
                          intro v _
                          rw [Finset.sum_mul]
                _ = ∑ p : Fin params.m × Fq params, ∑ v : Point params,
                      (if Function.update u p.1 p.2 = v then (1 : ℂ) else 0) *
                        fourierBasisState params α v := by
                          rw [Finset.sum_comm]
                _ = ∑ p : Fin params.m × Fq params,
                      fourierBasisState params α (Function.update u p.1 p.2) := by
                          refine Finset.sum_congr rfl ?_
                          intro p _
                          simp [eq_comm]
      _ = c * ∑ i : Fin params.m, ∑ x : Fq params,
            fourierBasisState params α (Function.update u i x) := by
              rw [Fintype.sum_prod_type]
  rw [hmul, fourierBasisState_total_update_sum]
  have hw := frequencyWeight_le_m params α
  have hm : (params.m : ℂ) ≠ 0 := by
    exact_mod_cast params.hm.ne'
  have hq : (params.q : ℂ) ≠ 0 := by
    exact_mod_cast params.hq.ne'
  have hM : (hypercubeVertexCount params : ℂ) ≠ 0 := by
    exact_mod_cast (pow_pos params.hq params.m).ne'
  simp only [mul_inv_rev, adjacencyEigenvalue, one_div, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_div, Pi.smul_apply,
    smul_eq_mul, c]
  rw [Nat.cast_sub hw]
  field_simp [hm, hq, hM]

/-- `cor:laplacian-spectral-gap`, eigenvalue relation: `λ_L(α) = 1/M − λ_K(α)`. -/
theorem laplacianEigenvalue_eq (params : Parameters) (α : Point params) :
    laplacianEigenvalue params α =
      (1 / (hypercubeVertexCount params : Error)) - adjacencyEigenvalue params α := by
  simp only [laplacianEigenvalue, adjacencyEigenvalue, hypercubeVertexCount]
  have hm : (params.m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr params.hm.ne'
  have hM : (↑(params.q ^ params.m) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_pos params.hq params.m).ne'
  have hw := frequencyWeight_le_m params α
  rw [Nat.cast_sub hw]
  field_simp [hm, hM]
  ring_nf

/-- `cor:laplacian-spectral-gap`, spectral gap bound: for `α ≠ 0`, the
spectral gap `1/(mM)` lower-bounds the Laplacian eigenvalue `λ_L(α)`. -/
theorem hypercubeSpectralGap_le_laplacianEigenvalue (params : Parameters) (α : Point params)
    (hα : 0 < frequencyWeight params α) :
    hypercubeSpectralGap params ≤ laplacianEigenvalue params α := by
  simp only [hypercubeSpectralGap, laplacianEigenvalue, hypercubeVertexCount]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hα



end MIPStarRE.LDT.ExpansionHypercubeGraph

end

end LIDT


