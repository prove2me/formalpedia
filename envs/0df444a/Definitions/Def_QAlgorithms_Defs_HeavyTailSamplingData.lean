-- Prove2me | Definitions.Def_QAlgorithms_Defs_HeavyTailSamplingData
-- name    : QAlgorithms_Defs_HeavyTailSamplingData
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T04:12:07.469001+00:00
-- url     : https://prove2.me/theorems/cb93f17f-fca7-48c3-8bba-5bec7465632c
-- title:
--   prove2quantum library: Defs.HeavyTailSamplingData
-- statement:
--   Shared definitions of the prove2quantum Lean library (`QAlgorithms.Defs.HeavyTailSamplingData`), reused by its paper formalizations.
--
--   - `FixedPointVectorData`: A positive dimension, public fixed-point coordinate encoding on a finite computational-basis value register and a probability mass function on its labels. Distinct represented values decode injectively. The fixed zero reference label need not have positive probability. Compute X and μ from these data, keeping the unknown probabilities/mean out of the algorithm constructor. Allow adequate workspace/no overflow. One coherent sampler is the access interface, not separate probability and value oracles. Source: arxiv-2607.25492v2 PDF p.4; arxiv-2607.25492v2 PDF p.5; arxiv-2607.25492v2 PDF p.16.
--   - `decodedVector`: Computational-basis value decoded coordinatewise from the public positional fixed-point format, in EuclideanSpace Real (Fin d). Mean uses the finite probability law, never an algorithm constructor parameter exposing the unknown mean. Source: arxiv-2607.25492v2 PDF p.4; arxiv-2607.25492v2 PDF p.5; arxiv-2607.25492v2 PDF p.16.
--   - `centralMoment`: Sum P(label)·Real.rpow(||decode(label)−μ||_2,p), with computed μ. Bound it by Real.rpow(σ,p) for 1<p≤2 and σ>0. Finite support ensures integrability of every expectation. Do not replace p by a natural exponent or impose an origin-centered moment or bounded-variance hypothesis. Source: arxiv-2607.25492v2 PDF p.5; arxiv-2607.25492v2 PDF p.22.
--   - `IsSamplingOracle`: Unitary O on value×auxiliary registers with O|0,0>=Σ_x sqrt(p_X(x)) ket x⊗ψ_x and ||ψ_x||=1 for each represented value. Quantify over arbitrary normalized auxiliary states and every compatible unitary extension; adjoints are available. Do not require garbage-free preparation, a coherent seed/probability oracle, a separate value oracle or a canonical extension. Source: arxiv-2607.25492v2 PDF p.4; arxiv-2607.25492v2 PDF p.16; arxiv-2607.25492v2 PDF p.18.
-- source:
--   prove2quantum Lean library, module QAlgorithms.Defs.HeavyTailSamplingData

import Definitions.Def_QAlgorithms_Defs_FiniteVectorMoments
import Definitions.Def_QAlgorithms_Defs_LinearSystemAccess

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.HeavyTail

/-- A positive dimension, public fixed-point coordinate encoding on a finite computational-basis value register and a probability mass function on its labels. Distinct represented values decode injectively. The fixed zero reference label need not have positive probability. Compute X and μ from these data, keeping the unknown probabilities/mean out of the algorithm constructor. Allow adequate workspace/no overflow. One coherent sampler is the access interface, not separate probability and value oracles. Source: arxiv-2607.25492v2 PDF p.4; arxiv-2607.25492v2 PDF p.5; arxiv-2607.25492v2 PDF p.16. -/
structure FixedPointVectorData (d b : ℕ) where
  dim_pos : 0 < d
  format : LinearSystemAccess.BinaryComplexFormat
  width : format.componentBits = b
  P : (Fin d → Qubits b) → ℝ
  distribution : Learning.IsDistribution P
  canonical : ∀ z, P z ≠ 0 → ∀ j,
    bitsToNat (Fin.init (fun i => z j (Fin.cast width i))) = 0 →
      z j (Fin.cast width (Fin.last (format.integerBits+format.fractionBits))) = false

/-- Computational-basis value decoded coordinatewise from the public positional fixed-point format, in EuclideanSpace Real (Fin d). Mean uses the finite probability law, never an algorithm constructor parameter exposing the unknown mean. Source: arxiv-2607.25492v2 PDF p.4; arxiv-2607.25492v2 PDF p.5; arxiv-2607.25492v2 PDF p.16. -/
def decodedVector {d b : ℕ} (V : FixedPointVectorData d b) (z : Fin d → Qubits b) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun j => V.format.realValue (fun i => z j (Fin.cast V.width i))

/-- Sum P(label)·Real.rpow(||decode(label)−μ||_2,p), with computed μ. Bound it by Real.rpow(σ,p) for 1<p≤2 and σ>0. Finite support ensures integrability of every expectation. Do not replace p by a natural exponent or impose an origin-centered moment or bounded-variance hypothesis. Source: arxiv-2607.25492v2 PDF p.5; arxiv-2607.25492v2 PDF p.22. -/
def centralMoment {d b : ℕ} (V : FixedPointVectorData d b) (p : ℝ) : ℝ :=
  ∑ z, V.P z * ‖decodedVector V z - FiniteVectorMoments.mean V.P V.distribution (decodedVector V)‖ ^ p

/-- Unitary O on value×auxiliary registers with O|0,0>=Σ_x sqrt(p_X(x)) ket x⊗ψ_x and ||ψ_x||=1 for each represented value. Quantify over arbitrary normalized auxiliary states and every compatible unitary extension; adjoints are available. Do not require garbage-free preparation, a coherent seed/probability oracle, a separate value oracle or a canonical extension. Source: arxiv-2607.25492v2 PDF p.4; arxiv-2607.25492v2 PDF p.16; arxiv-2607.25492v2 PDF p.18. -/
def IsSamplingOracle {d b w : ℕ} (V : FixedPointVectorData d b)
    (O : Matrix ((Fin d → Qubits b) × Qubits w) ((Fin d → Qubits b) × Qubits w) ℂ) : Prop :=
  O ∈ Matrix.unitaryGroup _ ℂ ∧
    ∃ garbage : (Fin d → Qubits b) → EuclideanSpace ℂ (Qubits w),
      (∀ z, IsState (garbage z)) ∧ ∀ z a,
      act O (ket (0,0)) (z,a) = (Real.sqrt (V.P z) : ℂ) * garbage z a

example {d b : ℕ} (V : FixedPointVectorData d b) : decodedVector V 0 = 0 := by
  ext j
  simp [decodedVector,LinearSystemAccess.BinaryComplexFormat.realValue,bitsToNat,Fin.init]

end QAlgorithms.HeavyTail


