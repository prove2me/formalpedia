-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
-- name    : LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:32:02.913594+00:00
-- url     : https://prove2.me/theorems/73c7e03a-0548-4128-be07-6a1e2d0b7a1d
-- title:
--   LIDT definitions: LDT / ExpansionHypercubeGraph / Defs / Core
-- statement:
--   This bundle defines the finite hypercube graph and its rerandomized-coordinate sampling used in expansion and variance estimates. It provides the vertex geometry, edge predicate, and explicit finite sample space for ordered edges.
--
--   Principal definitions:
--   - `hypercubeVertexCount`: the number of vertices in the point hypercube, `q^m`.
--   - `coordinateDisagreementSet`: the coordinates on which two points differ.
--   - `coordinateDisagreementCount`: the cardinality of the disagreement set.
--   - `IsHypercubeEdge`: the relation saying that two points differ in at most one coordinate.
--   - `instDecidableIsHypercubeEdge`: decidability of the hypercube edge relation.
--   - `instDecidablePredHypercubeEdgePair`: decidability of the edge predicate on ordered point pairs.
--   - `rerandomizeCoordWeight`: the explicit weight of an ordered edge obtained by rerandomizing one coordinate.
--   - `RerandomizeCoordSample`: the finite sample consisting of a point, a coordinate, and a replacement field value.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Core.lean#L27-L310

-- Generated from MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Core.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

/-!
# Section 7 hypercube graph: core definitions

Vertex-set cardinality and the hypercube graph edge relation on `F_q^m`.

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

/-- The number of vertices in the hypercube graph `C`. -/
def hypercubeVertexCount (params : Parameters) : ℕ :=
  params.q ^ params.m

/-- The set of coordinates on which two points disagree. -/
def coordinateDisagreementSet (params : Parameters)
    (u v : Point params) : Finset (Fin params.m) :=
  Finset.univ.filter (fun i => u i ≠ v i)

/-- The number of coordinates on which two points disagree. -/
def coordinateDisagreementCount (params : Parameters)
    (u v : Point params) : ℕ :=
  (coordinateDisagreementSet params u v).card

/-- The hypercube edge relation: two points differ in at most one coordinate. -/
def IsHypercubeEdge (params : Parameters) (u v : Point params) : Prop :=
  coordinateDisagreementCount params u v ≤ 1

/-- Decidability of the hypercube edge relation, obtained from the finite
coordinate disagreement count. -/
instance instDecidableIsHypercubeEdge (params : Parameters) (u v : Point params) :
    Decidable (IsHypercubeEdge params u v) := by
  unfold IsHypercubeEdge
  infer_instance

/-- Decidable predicate form of the hypercube edge relation on ordered pairs of
vertices. -/
instance instDecidablePredHypercubeEdgePair (params : Parameters) :
    DecidablePred (fun uv : Point params × Point params => IsHypercubeEdge params uv.1 uv.2) := by
  intro uv
  infer_instance

/-- Edge sampling by rerandomizing a single coordinate.
This is the Section 7.1 distribution:
pick `u ∈ F_q^m`, `i ∈ {1, ..., m}`, and `x ∈ F_q` uniformly,
then set `v = u[i ↦ x]`. -/
noncomputable def rerandomizeCoordWeight (params : Parameters)
    (u v : Point params) : Error :=
  (((∑ p : Fin params.m × Fq params,
      if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) : ℕ) : Error) /
    (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)

/-- The finite sample space for a rerandomized hypercube edge:
a point, a coordinate, and the new value placed in that coordinate. -/
abbrev RerandomizeCoordSample (params : Parameters) :=
  (Point params × Fin params.m) × Fq params

/-- The map from a rerandomization sample to the corresponding ordered edge. -/
def rerandomizeCoordSampleToPair (params : Parameters)
    (sample : RerandomizeCoordSample params) : Point params × Point params :=
  (sample.1.1, Function.update sample.1.1 sample.1.2 sample.2)

/-- The probability distribution on ordered edges of the hypercube graph used in
the paper's local variance.  It samples a vertex `u`, a coordinate, and a new
coordinate value, then records the ordered pair `(u, v)`. -/
noncomputable def rerandomizeCoord (params : Parameters) :
    Distribution (Point params × Point params) :=
  Distribution.map (uniformDistribution (RerandomizeCoordSample params))
    (rerandomizeCoordSampleToPair params)







/-- Averaging over `rerandomizeCoord` is the same as averaging over the uniform
sample space of a point, a coordinate, and a replacement coordinate value. -/
theorem avgOver_rerandomizeCoord_eq_uniform_sample (params : Parameters)
    (f : Point params × Point params → Error) :
    avgOver (rerandomizeCoord params) f =
      avgOver (uniformDistribution (RerandomizeCoordSample params))
        (fun sample => f (rerandomizeCoordSampleToPair params sample)) := by
  simpa [rerandomizeCoord] using
    Distribution.avgOver_map
      (uniformDistribution (RerandomizeCoordSample params))
      (rerandomizeCoordSampleToPair params) f

/-- The push-forward presentation of `rerandomizeCoord` has the same averages as
the explicit counting coefficient `rerandomizeCoordWeight`.

The explicit coefficient remains useful for the matrix calculation of the
hypercube adjacency and Laplacian.  This lemma identifies its weighted sum with
the probability-side push-forward average. -/
theorem avgOver_rerandomizeCoord_eq_weight_sum (params : Parameters)
    (f : Point params × Point params → Error) :
    avgOver (rerandomizeCoord params) f =
      ∑ uv : Point params × Point params,
        rerandomizeCoordWeight params uv.1 uv.2 * f uv := by
  classical
  have hcard :
      (Fintype.card (RerandomizeCoordSample params) : Error) =
        (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error) := by
    simp [RerandomizeCoordSample, hypercubeVertexCount, Fintype.card_fin]
  rw [avgOver_rerandomizeCoord_eq_uniform_sample]
  rw [avgOver_uniform_eq_pmf_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [hcard]
  symm
  calc
    ∑ uv : Point params × Point params,
        (((∑ p : Fin params.m × Fq params,
            if Function.update uv.1 p.1 p.2 = uv.2 then (1 : ℕ) else 0) : ℕ) : Error) *
          ((((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)⁻¹) *
          f uv
      = ∑ x : Point params,
          ∑ y : Point params,
            (((∑ p : Fin params.m × Fq params,
              if Function.update x p.1 p.2 = y then (1 : ℕ) else 0) : ℕ) : Error) *
              ((((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)⁻¹) *
              f (x, y) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ x : Point params,
          ∑ p : Fin params.m × Fq params,
            (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)⁻¹ *
              f (x, Function.update x p.1 p.2) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          calc
            ∑ y : Point params,
                (((∑ p : Fin params.m × Fq params,
                  if Function.update x p.1 p.2 = y then (1 : ℕ) else 0) : ℕ) : Error) *
                  ((((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) :
                    Error)⁻¹) *
                  f (x, y)
              = ∑ y : Point params,
                  ∑ p : Fin params.m × Fq params,
                    (if Function.update x p.1 p.2 = y then
                      ((((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) :
                        Error)⁻¹) * f (x, y)
                    else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro y _
                  have hcast :
                      (((∑ p : Fin params.m × Fq params,
                        if Function.update x p.1 p.2 = y then (1 : ℕ) else 0) :
                        ℕ) : Error) =
                      ∑ p : Fin params.m × Fq params,
                        if Function.update x p.1 p.2 = y then (1 : Error) else 0 := by
                    simp
                  rw [hcast]
                  rw [Finset.sum_ite]
                  simp only [Finset.sum_const_zero]
                  rw [Finset.sum_ite]
                  simp only [Finset.sum_const_zero]
                  simp [Finset.sum_const, nsmul_eq_mul]
                  ring
              _ = ∑ p : Fin params.m × Fq params,
                  ∑ y : Point params,
                    (if Function.update x p.1 p.2 = y then
                      ((((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) :
                        Error)⁻¹) * f (x, y)
                    else 0) := by
                  rw [Finset.sum_comm]
              _ = ∑ p : Fin params.m × Fq params,
                  (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) :
                    Error)⁻¹ *
                    f (x, Function.update x p.1 p.2) := by
                  refine Finset.sum_congr rfl ?_
                  intro p _
                  simp
    _ = ∑ x : Point params,
          ∑ i : Fin params.m,
            ∑ a : Fq params,
              (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) :
                Error)⁻¹ *
                f (x, Function.update x i a) := by
          simp [Fintype.sum_prod_type]
    _ = ∑ sample : RerandomizeCoordSample params,
          (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)⁻¹ *
            f (rerandomizeCoordSampleToPair params sample) := by
          simp [RerandomizeCoordSample, rerandomizeCoordSampleToPair, Fintype.sum_prod_type]

/-- The product distribution on two independently sampled hypercube vertices,
used in the paper's global variance. -/
noncomputable def independentPointPair (params : Parameters) :
    Distribution (Point params × Point params) :=
  uniformDistribution (Point params × Point params)

/-- An honest finite matrix register for the hypercube vertices. -/
@[reducible] def pointHilbertSpace (params : Parameters) : FiniteHilbertSpace where
  carrier := Point params
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

/-- The paper's normalized adjacency weight for an ordered pair of vertices.
This update-sum is equivalent to the older case-split via
`coordinateDisagreementCount`: when `u ≠ v`, each differing coordinate
contributes the unique update sending `u i` to `v i`, while when `u = v`
the `q` self-loop updates contribute once for each coordinate. -/
noncomputable def hypercubeAdjacencyWeight (params : Parameters)
    (u v : Point params) : ℂ :=
  (((params.m : ℂ) * (params.q : ℂ) * (hypercubeVertexCount params : ℂ))⁻¹) *
    ∑ p : Fin params.m × Fq params,
      if Function.update u p.1 p.2 = v then (1 : ℂ) else 0

/-- The actual adjacency matrix of the edge-graph on `F_q^m`. -/
noncomputable def matrixAdjacencyOperator (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  fun u v => hypercubeAdjacencyWeight params u v

/-- The actual Laplacian matrix `(1 / M) I - K` on the vertex register. -/
noncomputable def matrixLaplacianOperator (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  ((hypercubeVertexCount params : ℂ)⁻¹) • (1 : MatrixOperator (pointHilbertSpace params)) -
    matrixAdjacencyOperator params



/-- The Laplacian `L = (1/M) I - K` on the hypercube vertex space,
as a matrix indexed by `Point params` directly. -/
noncomputable def laplacian (params : Parameters) : MIPStarRE.Quantum.Op (Point params) :=
  matrixLaplacianOperator params



/-- The squared difference operator `(A^u - A^v)ᴴ(A^u - A^v)`. -/
noncomputable def pointDifferenceSquaredOperator {params : Parameters}
    (A : Point params → MIPStarRE.Quantum.Op ι) (u v : Point params) : MIPStarRE.Quantum.Op ι :=
  (A u - A v)ᴴ * (A u - A v)

/-- The local variance from `def:local-and-variance`. -/
noncomputable def localVariance (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Error :=
  (1 / (2 : Error)) *
    avgOver (rerandomizeCoord params)
      (fun uv => ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2))

/-- The global variance from `def:local-and-variance`. -/
noncomputable def globalVariance (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Error :=
  (1 / (2 : Error)) *
    avgOver (independentPointPair params)
      (fun uv => ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2))



/-- The column-space indices for `A_combine`. -/
abbrev combinedColumnIndex (params : Parameters) (ι : Type*) := Point params × ι

/-- The combined column operator used for the trace rewrites.
Its `u`-th block is `(A^u)ᴴ`, so that the resulting trace expands to
`τ(ρ · (A^u - A^v)ᴴ (A^u - A^v))` for arbitrary operator families. -/
noncomputable def combinedOperator (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) :
    Matrix (combinedColumnIndex params ι) ι ℂ :=
  fun ui j => star (A ui.1 j ui.2)

end MIPStarRE.LDT.ExpansionHypercubeGraph

end

end LIDT


