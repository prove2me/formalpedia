-- Prove2me | Definitions.Def_RandomOracleUnitarySynthesis_synthesis_matrix_model
-- name    : RandomOracleUnitarySynthesis_synthesis_matrix_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:44.930576+00:00
-- url     : https://prove2.me/theorems/03a358c6-ece8-4a25-956b-000ce0a0b53e
-- title:
--   Computational registers, channel coordinates, diamond distance, and Haar probability
-- statement:
--   The computational basis is the full set of binary words, and operators are complex matrices. Channels are represented by their values on matrix units, with the usual finite-dimensional Borel structure. This representation identifies maps independently of their Kraus decompositions. For channels $F,G$ the distance is
--
--   $$D_\diamond(F,G)=\sup_{b,\rho}\tfrac12\|(F\otimes\operatorname{id}_b)(\rho)-(G\otimes\operatorname{id}_b)(\rho)\|_1,$$
--
--   where $b$ ranges over every finite reference dimension and $\rho$ over all joint density operators. Haar probability is normalized on the full compact group $U(2^n)$. The normalized trace correlation is $2^{-n}\operatorname{Re}\operatorname{tr}(CU^\dagger Q U)$. A contraction has spectral norm at most one.
--
--   These interfaces supply the shared matrix and probability conventions for the mission. Published definitions supply the density predicate, spectral and Frobenius norms, trace norm, Pauli family, and partial trace; no purity or cleanliness convention is imported.
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), §2.1, printed pp. 10–11 (PDF pp. 12–13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_DirectFidelity_State_Setting

open scoped Matrix ComplexConjugate
open MeasureTheory
noncomputable section

namespace RandomOracleUnitarySynthesis

/-! Huang–Ramkumar–Wright, STOC 2027 submission #157 (October 2026),
§2.1, printed pp.10–11 (PDF pp.12–13). Matrices use the full complex computational basis.
The generic register, norm, density, Pauli and partial-trace concepts are published imports.
Channel matrices below are coordinates of linear maps, not a choice of Kraus representation. -/
abbrev synthesis_Bits := DirectFidelity.State.Q
abbrev synthesis_Pauli := DirectFidelity.State.P
abbrev synthesis_Mat (n : ℕ) := Matrix (synthesis_Bits n) (synthesis_Bits n) ℂ
abbrev synthesis_Unitary (n : ℕ) := Matrix.unitaryGroup (synthesis_Bits n) ℂ
abbrev synthesis_Channel (n : ℕ) :=
  Matrix (synthesis_Bits n × synthesis_Bits n) (synthesis_Bits n × synthesis_Bits n) ℂ

instance synthesis_channelMeasurable (n : ℕ) : MeasurableSpace (synthesis_Channel n) := borel _
instance synthesis_channelBorel (n : ℕ) : BorelSpace (synthesis_Channel n) := ⟨rfl⟩

/-- Matrix-unit coordinates of a linear operation: row = output matrix entry,
column = input matrix entry. No complete-positivity premise is hidden in the coordinates. -/
def synthesis_coordinates {n : ℕ} (F : synthesis_Mat n → synthesis_Mat n) :
    synthesis_Channel n :=
  fun a b => F (Matrix.single b.1 b.2 1) a.1 a.2

/-- The linear map represented by its matrix-unit coefficients. -/
def synthesis_apply {n : ℕ} (F : synthesis_Channel n) (ρ : synthesis_Mat n) :
    synthesis_Mat n :=
  fun a b => ∑ p, F (a,b) p * ρ p.1 p.2

/-- Apply to the system factor of a state with a reference of arbitrary dimension `b`. -/
def synthesis_amplify {n : ℕ} (F : synthesis_Channel n) (b : ℕ)
    (ρ : Matrix (synthesis_Bits n × Fin b) (synthesis_Bits n × Fin b) ℂ) :
    Matrix (synthesis_Bits n × Fin b) (synthesis_Bits n × Fin b) ℂ :=
  Matrix.of fun a c => synthesis_apply F
    (Matrix.of fun i j => ρ (i,a.2) (j,c.2)) a.1 c.1

/-- Half the trace norm, optimized over ALL finite references and ALL mixed densities.
On channels the optimization set is nonempty and lies in [0,1]. It is not the pure-state
fixed-reference convention of QuantumPRC.diamondDist. -/
def synthesis_diamond {n : ℕ} (F G : synthesis_Channel n) : ℝ :=
  sSup {z : ℝ | ∃ (b : ℕ)
    (ρ : Matrix (synthesis_Bits n × Fin b) (synthesis_Bits n × Fin b) ℂ),
    WildeQIT.IsDensityOperator ρ ∧ z =
      WildeQIT.traceNorm (synthesis_amplify F b ρ - synthesis_amplify G b ρ) / 2}

/-- A unitary channel, in coordinates, retaining phase invariance of the actual map. -/
def synthesis_unitaryChannel {n : ℕ} (U : synthesis_Unitary n) : synthesis_Channel n :=
  synthesis_coordinates (fun ρ => (U : synthesis_Mat n) * ρ * (U : synthesis_Mat n)ᴴ)

instance synthesis_unitaryMeasurable (n : ℕ) : MeasurableSpace (synthesis_Unitary n) := borel _
instance synthesis_unitaryBorel (n : ℕ) : BorelSpace (synthesis_Unitary n) := ⟨rfl⟩

/-- Compactness of the full unitary group; this is a structural proof required to
construct normalized Haar probability, not a theorem from the mission's proof chain. -/
instance synthesis_unitaryCompact (n : ℕ) : CompactSpace (synthesis_Unitary n) := by
  have hclosed : IsClosed (Matrix.unitaryGroup (synthesis_Bits n) ℂ : Set (synthesis_Mat n)) :=
    isClosed_unitary
  open scoped Matrix.Norms.Elementwise in
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : synthesis_Mat n) 1).of_isClosed_subset hclosed
  intro U hU
  simpa [Metric.mem_closedBall, dist_zero_right] using entrywise_sup_norm_bound_of_unitary hU

/-- Borel Haar probability on U(2^n), normalized on the whole compact group. -/
def synthesis_haar (n : ℕ) : Measure (synthesis_Unitary n) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance synthesis_haarProbability (n : ℕ) : IsProbabilityMeasure (synthesis_haar n) := by
  constructor
  exact Measure.haarMeasure_self

/-- Uniform finite expectation; used only on nonempty finite types. -/
def synthesis_average {A : Type} [Fintype A] (h : A → ℝ) : ℝ :=
  (∑ a, h a) / Fintype.card A

/-- Normalized real trace correlation. For Hermitian C and Q the trace is real,
since conjugating it and cycling the two factors leaves it unchanged. -/
def synthesis_correlation {n : ℕ} (C : synthesis_Mat n) (Q : synthesis_Pauli n)
    (U : synthesis_Unitary n) : ℝ :=
  (C * ((U : synthesis_Mat n)ᴴ * DirectFidelity.State.W Q *
    (U : synthesis_Mat n))).trace.re / (2 : ℝ)^n

/-- Operator-norm contraction, using the explicit spectral norm (never an entrywise norm). -/
def synthesis_IsContraction {n : ℕ} (C : synthesis_Mat n) : Prop := QAlgorithms.specNorm C ≤ 1

end RandomOracleUnitarySynthesis


