-- Prove2me | Definitions.Def_QAlgorithms_Defs_SparsePauliNoiseData
-- name    : QAlgorithms_Defs_SparsePauliNoiseData
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:25:34.151672+00:00
-- url     : https://prove2.me/theorems/66c533cd-6d26-499f-9bdd-9f5dc1b71711
-- title:
--   SparsePauliNoiseData
-- statement:
--   SparsePauliNoiseData
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SparsePauliNoiseData.lean

import Definitions.Def_QAlgorithms_Defs_NoisyEigenvaluePrograms
import Definitions.Def_QAlgorithms_Defs_PauliNoiseFourier
noncomputable section

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.SparsePauliNoise

/-- Conditional rates on an exact size-s support, with positive lower signal bound
(2007.07901 p.7, Assumptions A1,A3). No distribution over magnitudes is invented. -/
structure AdmissibleRates (n s : ℕ) (K : Finset (Label n)) (epsilon0 : ℝ) where
  size : K.card = s
  positiveLowerBound : 0 < epsilon0
  rate : Label n → ℝ
  distribution : Learning.IsDistribution rate
  exactSupport : ∀ a, rate a ≠ 0 ↔ a ∈ K
  signal : ∀ a ∈ K, epsilon0 ≤ rate a

/-- Uniformly chosen size-s subsets, rather than s draws with replacement
(2007.07901 p.7, Assumption A1). A feasible cardinality is required. -/
def supportLaw (n s : ℕ) (_positive : 0 < s)
    (feasible : s ≤ Fintype.card (Label n)) : PMF {K : Finset (Label n) // K.card = s} :=
  letI : Nonempty {K : Finset (Label n) // K.card = s} := by
    obtain ⟨K,_,hK⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Label n))) (by simpa using feasible)
    exact ⟨⟨K,hK⟩⟩
  PMF.uniformOfFintype _

/-- A single indexed observation vector with independent Gaussian coordinates
(2007.07901 p.7, Assumption A2; p.11, Eq.(10)). Its mean is the computed WHT.
Variance zero is Dirac; repeated program reads reuse this same sampled vector. -/
def noisyEigenvalueLaw {n : ℕ} (p : Label n → ℝ)
    (_lawful : Learning.IsDistribution p) (xi : ℝ) (_hxi : 0 ≤ xi) :
    Measure (Label n → ℝ) :=
  Measure.pi fun a => gaussianReal (eigenvalueWHT p a) (Real.toNNReal (xi^2))

example {n : ℕ} (p : Label n → ℝ) (lawful : Learning.IsDistribution p)
    (xi : ℝ) (hxi : 0 ≤ xi) : noisyEigenvalueLaw p lawful xi hxi Set.univ = 1 := by
  unfold noisyEigenvalueLaw
  rw [Measure.pi_univ]
  simp only [measure_univ,Finset.prod_const_one]

example {n : ℕ} (p : Label n → ℝ) (lawful : Learning.IsDistribution p) :
    noisyEigenvalueLaw p lawful 0 (by norm_num) =
      Measure.pi (fun a => Measure.dirac (eigenvalueWHT p a)) := by
  unfold noisyEigenvalueLaw
  simp [gaussianReal_zero_var]


/-- Public hash matrices, random/coded offsets and a concrete binary decoder.
Only syntax and source parameter domains are fields; decoding correctness and
linear time are conclusions (2007.07901 pp.11-12,14-15). -/
structure RecoveryDesign (n : ℕ) where
  b : ℕ
  b_pos : 0 < b
  b_le : b ≤ 2*n
  groups : ℕ
  groups_pos : 0 < groups
  P1 : ℕ
  P2 : ℕ
  P1_pos : 0 < P1
  P2_pos : 0 < P2
  hashMatrix : Fin groups → Matrix (Fin (n+n)) (Fin b) (ZMod 2)
  randomOffsets : Fin groups → Fin P1 → Label n
  code : Matrix (Fin P2) (Fin (n+n)) (ZMod 2)
  decoder : OracleProgram n
  decoderQueryFree : decoder.QueryFree
  decoderWorkspace : ℕ
  decoderFits : P2+(n+n) ≤ decoderWorkspace
  decoderConfined : decoder.Confined decoderWorkspace
  iterations : ℕ
  gamma1 : ℝ
  gamma2 : ℝ
  gamma1_range : 0 < gamma1 ∧ gamma1 < 1
  gamma2_range : 0 < gamma2 ∧ gamma2 < 1

/-- Split a flat source-order binary label into X then Z coordinates
(2007.07901 p.2, Eq.(1); p.12, Definition 1). -/
def splitLabel {n : ℕ} (v : Fin (n+n) → ZMod 2) : Label n :=
  (fun i => v (Fin.castAdd n i),fun i => v (Fin.natAdd n i))

/-- Actual offsets: independent random rows followed by the public code-generator
rows, common to the coded decoder (2007.07901 p.12, Definition 1).
Offsets have 2n bits, as required by Eq.(13), correcting the printed n-bit length. -/
def RecoveryDesign.offset {n : ℕ} (D : RecoveryDesign n) (c : Fin D.groups) :
    Fin (D.P1+D.P2) → Label n :=
  Fin.addCases (D.randomOffsets c) (fun t => splitLabel (D.code t))

example {n : ℕ} (D : RecoveryDesign n) (c : Fin D.groups) (t : Fin D.P1) :
    D.offset c (Fin.castAdd D.P2 t) = D.randomOffsets c t := by
  simp [RecoveryDesign.offset]

end QAlgorithms.SparsePauliNoise


