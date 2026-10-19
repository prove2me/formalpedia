-- Prove2me | Definitions.Def_QAlgorithms_Defs_JointLowRankGibbsData
-- name    : QAlgorithms_Defs_JointLowRankGibbsData
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:22:26.659795+00:00
-- url     : https://prove2.me/theorems/7bdc50f7-daf6-4543-be69-a95894aca04e
-- title:
--   JointLowRankGibbsData
-- statement:
--   JointLowRankGibbsData
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\JointLowRankGibbsData.lean

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

open scoped Matrix
namespace QAlgorithms.LowRankGibbs

/-- Indexed PSD parts APlus,AMinus : Fin m→Matrix (Fin n) (Fin n) ℂ with nonempty dimensions; differences are computed. Preserve arbitrary PSD decompositions and the normalized-state domain of D.2. Keep ambient SDP contraction/rank/trace promises separate from the standalone Gibbs promise. Source: arxiv-1710.02581v3 PDF p.21; arxiv-1710.02581v3 PDF p.38. -/
structure PSDInputFamily (n m : ℕ) where
  n_pos : 0 < n
  m_pos : 0 < m
  plus : Fin m → Matrix (Fin n) (Fin n) ℂ
  minus : Fin m → Matrix (Fin n) (Fin n) ℂ
  psdPlus : ∀ j, (plus j).PosSemidef
  psdMinus : ∀ j, (minus j).PosSemidef

/-- Public unsigned positional binary format with explicit integer/fraction widths and decoder bitsToNat(z)/2^fractionBits. The source supplies binary trace values; this names their positional convention without asserting representability of arbitrary real traces or adding a bit-cost theorem. Source: arxiv-1710.02581v3 PDF p.5; arxiv-1710.02581v3 PDF p.21. -/
structure TraceBinaryFormat where
  integerBits : ℕ
  fractionBits : ℕ

/-- Implementation helper; source: arxiv-1710.02581v3 PDF p.21. -/
def TraceBinaryFormat.width (F : TraceBinaryFormat) : ℕ := F.integerBits + F.fractionBits

/-- Implementation helper; source: arxiv-1710.02581v3 PDF p.21. -/
def TraceBinaryFormat.decode (F : TraceBinaryFormat) (z : Qubits F.width) : ℝ :=
  (bitsToNat z : ℝ) / (2 : ℝ) ^ F.fractionBits

/-- D.1: unitary on label×two finite binary answer registers, inverse available, retaining j and writing the two trace representations from initialized zeros. Name the positional binary format and its supplied-precision convention; do not use arbitrary real decoders or prescribe an unmentioned XOR rule on nonzero answers. The theorem belongs to the supplied oracle/gate model, not a uniform bit-time model. Source: arxiv-1710.02581v3 PDF p.5; arxiv-1710.02581v3 PDF p.21. -/
def IsTraceInputOracle {n m : ℕ} (A : PSDInputFamily n m) (F : TraceBinaryFormat)
    (O : Matrix (Fin m × (Qubits F.width × Qubits F.width))
      (Fin m × (Qubits F.width × Qubits F.width)) ℂ) : Prop :=
  O ∈ Matrix.unitaryGroup _ ℂ ∧ ∃ plus minus : Fin m → Qubits F.width,
    (∀ j, F.decode (plus j) = (A.plus j).trace.re ∧ F.decode (minus j) = (A.minus j).trace.re) ∧
    ∀ j, act O (ket (j,(0,0))) = ket (j,(plus j,minus j))

/-- D.2 on Fin m×((Fin n×Fin n)×(Fin n×Fin n)), with adjoint access. For each initialized basis label, density equality jointly yields two arbitrary normalized purifications whose reduced densities are the two normalized PSD parts. Normalize each nonzero PSD component; a zero component has arbitrary normalized purification, since the source proof weights it by its zero trace (pp.26,27,29). Retain global-phase freedom; no arbitrary action on unused states or separate sign control is asserted. Source: arxiv-1710.02581v3 PDF p.5; arxiv-1710.02581v3 PDF p.21. -/
def IsJointPurificationInputOracle {n m : ℕ} (A : PSDInputFamily n m)
    (O : Matrix (Fin m × ((Fin n × Fin n) × (Fin n × Fin n)))
      (Fin m × ((Fin n × Fin n) × (Fin n × Fin n))) ℂ) : Prop :=
  O ∈ Matrix.unitaryGroup _ ℂ ∧ ∀ j,
    ∃ pp pm : EuclideanSpace ℂ (Fin n × Fin n), IsState pp ∧ IsState pm ∧
      ((A.plus j).trace ≠ 0 → traceRight (pureDensity pp) = ((A.plus j).trace)⁻¹ • A.plus j) ∧
      ((A.minus j).trace ≠ 0 → traceRight (pureDensity pm) = ((A.minus j).trace)⁻¹ • A.minus j) ∧
      conjSuperop O (pureDensity (ket (j,((⟨0,A.n_pos⟩,⟨0,A.n_pos⟩),(⟨0,A.n_pos⟩,⟨0,A.n_pos⟩))))) =
        Matrix.kronecker (pureDensity (ket j)) (Matrix.kronecker (pureDensity pp) (pureDensity pm))

/-- KPlus=sum_{j in S} c_j APlus_j, computed from public S, including empty S and the shared positive coefficients. Source: arxiv-1710.02581v3 PDF p.22; arxiv-1710.02581v3 PDF p.26. -/
def weightedPlus {n m : ℕ} (A : PSDInputFamily n m) (S : Finset (Fin m))
    (c : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℂ := ∑ j ∈ S, (c j : ℂ) • A.plus j

/-- KMinus=sum_{j in S} c_j AMinus_j, computed with the SAME S and coefficients as KPlus; not spectral negative part. Source: arxiv-1710.02581v3 PDF p.22; arxiv-1710.02581v3 PDF p.26. -/
def weightedMinus {n m : ℕ} (A : PSDInputFamily n m) (S : Finset (Fin m))
    (c : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℂ := ∑ j ∈ S, (c j : ℂ) • A.minus j

/-- K=weightedPlus-weightedMinus. Separate PSD,rank and combined-trace promises concern the computed parts, not rank(K). Source: arxiv-1710.02581v3 PDF p.22; arxiv-1710.02581v3 PDF p.26. -/
def weightedHamiltonian {n m : ℕ} (A : PSDInputFamily n m) (S : Finset (Fin m))
    (c : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℂ := weightedPlus A S c - weightedMinus A S c

/-- Public S (possibly empty) and positive coefficients compute KPlus,KMinus,K. Include D.1/D.2 promises, rank of each part≤r_K and combined trace≤B_K. Lemma 11 constructs normalized K parts by probability proportional to c_j Tr(A_j±), at |S| trace calls and one joint preparation call; free K-part oracles must not replace this charged reduction. Normalized K-part preparation applies only when that part has positive trace; zero parts are never sampled. Empty support gives K=0 without a normalized K-part preparation. Source: arxiv-1710.02581v3 PDF p.22; arxiv-1710.02581v3 PDF p.26. -/
structure WeightedHamiltonianAccess (n m : ℕ) (F : TraceBinaryFormat) where
  data : PSDInputFamily n m
  S : Finset (Fin m)
  coefficients : Fin m → ℝ
  positive : ∀ j ∈ S, 0 < coefficients j
  rankBound : ℕ
  traceBound : ℝ
  rankPlus : (weightedPlus data S coefficients).rank ≤ rankBound
  rankMinus : (weightedMinus data S coefficients).rank ≤ rankBound
  traceBounded : (weightedPlus data S coefficients).trace.re +
    (weightedMinus data S coefficients).trace.re ≤ traceBound
  traceOracle : Matrix (Fin m × (Qubits F.width × Qubits F.width))
    (Fin m × (Qubits F.width × Qubits F.width)) ℂ
  preparationOracle : Matrix (Fin m × ((Fin n × Fin n) × (Fin n × Fin n)))
    (Fin m × ((Fin n × Fin n) × (Fin n × Fin n))) ℂ
  traces : IsTraceInputOracle data F traceOracle
  preparations : IsJointPurificationInputOracle data preparationOracle

example (F : TraceBinaryFormat) : F.decode 0 = 0 := by
  simp [TraceBinaryFormat.decode,bitsToNat]

example {n m : ℕ} (A : PSDInputFamily n m) (c : Fin m → ℝ) : weightedHamiltonian A ∅ c = 0 := by
  simp [weightedHamiltonian,weightedPlus,weightedMinus]

example : IsJointPurificationInputOracle
    (⟨by decide, by decide, fun _ => 0, fun _ => 0,
      fun _ => Matrix.PosSemidef.zero, fun _ => Matrix.PosSemidef.zero⟩ : PSDInputFamily 1 1)
    1 := by
  refine ⟨one_mem _, ?_⟩
  intro j
  refine ⟨ket (0,0), ket (0,0), by simp [IsState,ket], by simp [IsState,ket],
    by simp, by simp, ?_⟩
  ext x y
  have hx : x = (j,((0,0),(0,0))) := Subsingleton.elim _ _
  have hy : y = (j,((0,0),(0,0))) := Subsingleton.elim _ _
  subst x; subst y
  simp [conjSuperop,pureDensity,ket,Matrix.kronecker]

end QAlgorithms.LowRankGibbs


