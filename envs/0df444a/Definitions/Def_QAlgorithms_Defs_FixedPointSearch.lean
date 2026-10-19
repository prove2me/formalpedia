-- Prove2me | Definitions.Def_QAlgorithms_Defs_FixedPointSearch
-- name    : QAlgorithms_Defs_FixedPointSearch
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:17:43.802881+00:00
-- url     : https://prove2.me/theorems/ec309606-6676-40f9-a00c-2d5955596a43
-- title:
--   FixedPointSearch
-- statement:
--   FixedPointSearch
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\FixedPointSearch.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- For normalized T on Qubits n, U on data × Bool is unitary and U=I⊗I+pureDensity(T)⊗(pauliX−I): flip the ancilla on span(T), identity on every orthogonal vector. Source: arxiv-1409.3305v2 PDF p.1. -/
def IsTargetFlipOracle {n : ℕ} (T : EuclideanSpace ℂ (Qubits n))
    (U : Matrix (Qubits n × Bool) (Qubits n × Bool) ℂ) : Prop :=
  IsState T ∧ U ∈ Matrix.unitaryGroup _ ℂ ∧ U = 1 + Matrix.kronecker (pureDensity T) (pauliX - 1)

/-- S_s(α)=I−(1−exp(−iα))•pureDensity(s), s=act A (zeroKet n). Source: arxiv-1409.3305v2 PDF p.2. -/
def sourcePhaseReflection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : EuclideanSpace ℂ ι) (alpha : ℝ) : Matrix ι ι ℂ :=
  1 - (1 - Complex.exp (-Complex.I * (alpha : ℂ))) • pureDensity s

/-- S_t(β)=I−(1−exp(iβ))•pureDensity(T), Equation (7). Source: arxiv-1409.3305v2 PDF p.2. -/
def targetPhaseReflection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : EuclideanSpace ℂ ι) (beta : ℝ) : Matrix ι ι ℂ :=
  1 - (1 - Complex.exp (Complex.I * (beta : ℂ))) • pureDensity T

/-- G(α,β)=−S_s(α)*S_t(β); apply target reflection first, retaining the minus sign. Source: arxiv-1409.3305v2 PDF p.2. -/
def generalizedGroverIterate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s T : EuclideanSpace ℂ ι) (alpha beta : ℝ) : Matrix ι ι ℂ :=
  -(sourcePhaseReflection s alpha * targetPhaseReflection T beta)

/-- For L=2l+1, gamma=cosh(arcosh(1/δ)/(L:ℝ))^(−1) when δ>0, and gamma=0 at δ=0 by continuity. Source: arxiv-1409.3305v2 PDF p.2; arxiv-1409.3305v2 PDF p.3; arxiv-1409.3305v2 PDF p.4. -/
def fixedPointGamma (l : ℕ) (delta : ℝ) : ℝ :=
  if delta = 0 then 0 else (Real.cosh (Real.arcosh delta⁻¹ / (2 * l + 1)))⁻¹

/-- For j=1,…,l, α_j=2*(π/2−arctan(tan(2πj/(2l+1))*sqrt(1−gamma²))), β_j=−α_{l−j+1}, Equation (11). Source: arxiv-1409.3305v2 PDF p.3. -/
def fixedPointPhases (l : ℕ) (delta : ℝ) : (Fin l → ℝ) × (Fin l → ℝ) :=
  let alpha : Fin l → ℝ := fun j =>
    2 * (Real.pi / 2 - Real.arctan (Real.tan (2 * Real.pi * ((j : ℕ) + 1) / (2 * l + 1)) *
      Real.sqrt (1 - fixedPointGamma l delta ^ 2)))
  (alpha, fun j => -alpha (Fin.rev j))

/-- Construct G(α_l,β_l)⋯G(α_1,β_1), Equation (10), using the matched phases and s=A|0⟩. Source: arxiv-1409.3305v2 PDF p.3. -/
def fixedPointSequence {n : ℕ} (l : ℕ) (delta : ℝ)
    (A : Matrix (Qubits n) (Qubits n) ℂ) (T : EuclideanSpace ℂ (Qubits n)) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  orderedProd fun j : Fin l => generalizedGroverIterate (act A (zeroKet n)) T
    ((fixedPointPhases l delta).1 j) ((fixedPointPhases l delta).2 j)

/-- For positive δ, P_L(λ,δ)=1−δ²*((Polynomial.Chebyshev.T ℝ (L:ℤ)).eval(sqrt(1−λ)/gamma))². Source: arxiv-1409.3305v2 PDF p.1; arxiv-1409.3305v2 PDF p.3; arxiv-1409.3305v2 PDF p.4. -/
def fixedPointProfile (l : ℕ) (lam delta : ℝ) : ℝ :=
  if delta = 0 then 1 - (1 - lam) ^ (2 * l + 1)
  else 1 - delta ^ 2 * ((Polynomial.Chebyshev.T ℝ ((2 * l + 1 : ℕ) : ℤ)).eval
    (Real.sqrt (1 - lam) / fixedPointGamma l delta)) ^ 2

/-- w_L(δ)=1−gamma², including w_L(0)=1. Source: arxiv-1409.3305v2 PDF p.2. -/
def fixedPointWidth (l : ℕ) (delta : ℝ) : ℝ := 1 - fixedPointGamma l delta ^ 2

/-- Arbitrary unitary single-qubit matrices via Gate.ofMatrix1, together with Gate.ofMatrix2 cnot, as counted in Fig.2. Source: arxiv-1409.3305v2 PDF p.3. -/
def singleQubitCnotGateSet : Set Gate :=
  {g | ∃ M : Matrix Bool Bool ℂ, M ∈ Matrix.unitaryGroup Bool ℂ ∧ g = Gate.ofMatrix1 M} ∪
    {Gate.ofMatrix2 cnot}

/-- Sanity test. Source: arxiv-1409.3305v2 PDF p.1. -/
example {n : ℕ} (delta : ℝ) (A : Matrix (Qubits n) (Qubits n) ℂ)
    (T : EuclideanSpace ℂ (Qubits n)) : fixedPointSequence 0 delta A T = 1 := by
  simp [fixedPointSequence, orderedProd]

/-- Sanity test. Source: arxiv-1409.3305v2 PDF p.1. -/
example (l : ℕ) (lam : ℝ) : fixedPointProfile l lam 0 = 1 - (1 - lam) ^ (2 * l + 1) := by
  simp [fixedPointProfile]

/-- Sanity test. Source: arxiv-1409.3305v2 PDF p.1. -/
example (l : ℕ) : fixedPointWidth l 0 = 1 := by simp [fixedPointWidth, fixedPointGamma]

end QAlgorithms


