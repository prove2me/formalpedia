-- Prove2me | Definitions.Def_LindbladTolerant_Testing_algorithm
-- name    : LindbladTolerant_Testing_algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:08:09.902103+00:00
-- url     : https://prove2.me/theorems/696f265a-ea07-420c-bb32-f27074fcbd68
-- title:
--   Algorithm 1 and the uniform two-sided resource contracts
-- statement:
--   For fixed $k$ and known $n,\Lambda,\varepsilon_1,\varepsilon_2$, set $\Delta=\varepsilon_2-\varepsilon_1$, $q_k=\sqrt{1+(2^k+1)/2}$, $\delta=\Delta/(32\varepsilon_2)$, and
--   $$R=\lceil C_k\delta^{-2}\rceil,\quad T=32q_k^2R/\varepsilon_2,\quad
--   M=\lceil\max\{1,2\Lambda T,32\Lambda^2T^2\}\rceil,\quad t=T/M.$$
--   Algorithm 1 makes exactly $M$ independent maximally entangled preparations and forward calls. Its binary projection preserves coherence in the success subspace. The actual success block is $B_t=\Pi J(e^{t\mathcal L})\Pi$. It counts all successes $K$, retains the first $R$, and sets $\widehat\Gamma=K/T$. It returns YES below the low rate cutoff $\varepsilon_2/(2q_k)$, NO above the high cutoff $2\varepsilon_2$, and otherwise applies the fixed functional estimator to stored outputs and compares $\widehat\Gamma\sqrt{1+\widehat h}$ with $(\varepsilon_1+\varepsilon_2)/2$.
--
--   The output law is computed from the physical success probabilities, the corresponding conditional physical states, and the fixed measurement routine. It does not substitute ideal jump states for physical finite-time states. The implementation's realization by one admissible protocol, its uniform success, its sufficient storage in the intermediate branch, and its time bound are conclusions of the upper contract.
--
--   Choose the explicit source-derived coefficients
--   $$A_k=32768q_k^2(C_k+1),\qquad c=\sqrt2\log(9/8).$$
--   The uniform upper contract fixes $A_k$ before $n,\Lambda$ and thresholds. The lower contract quantifies over every admissible protocol and gives both Eq.(119) and its consequence $T\ge c\varepsilon_2/\Delta^2$. Both cover $n,k\ge1$, $0\le\varepsilon_1<\varepsilon_2\le\Lambda/\sqrt2$, and $\Lambda>0$.
--
--   **Formalization Note** A zero success-probability preparation uses a raw zero dummy only inside zero-mass histories. It is not assigned a physical jump state. The insufficient-storage fallback defines the routine on arbitrary parameters; its impossibility on every intermediate branch in the stated domain is a theorem obligation.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Algorithm 1 and Theorems 5.1–5.2 proofs, pp.25–30, PDF pp.25–30, Eqs.(94)–(119)

import Definitions.Def_LindbladTolerant_Testing_estimator
import Definitions.Def_LindbladTolerant_Testing_protocols

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix

namespace LindbladTolerant.Testing
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Algorithm 1, p.26: parameters depend only on the known input. -/
def qConstant (k : ℕ) : ℝ := Real.sqrt (1 + functionalBound k)
def testAccuracy (eps1 eps2 : ℝ) : ℝ := (eps2-eps1)/(32*eps2)
def retainedCount (k : ℕ) (eps1 eps2 : ℝ) : ℕ :=
  ⌈copyConstant k * (testAccuracy eps1 eps2)⁻¹^2⌉₊
def totalTime (k : ℕ) (eps1 eps2 : ℝ) : ℝ :=
  32 * (qConstant k)^2 * (retainedCount k eps1 eps2 : ℝ) / eps2
def attemptCount (k : ℕ) (bound eps1 eps2 : ℝ) : ℕ :=
  let T := totalTime k eps1 eps2
  ⌈max 1 (max (2*bound*T) (32*bound^2*T^2))⌉₊
def attemptTime (k : ℕ) (bound eps1 eps2 : ℝ) : ℝ :=
  totalTime k eps1 eps2 / (attemptCount k bound eps1 eps2 : ℝ)
def upperConstant (k : ℕ) : ℝ := 32768 * (qConstant k)^2 * (copyConstant k+1)
def lowerConstant : ℝ := Real.sqrt 2 * Real.log (9/8)

variable {n M : ℕ}

/-- The coherent success block of the actual finite-time preparation (94). -/
def preparedBlock (g : Super (Qubits n) (Qubits n)) (t : ℝ) :
    Op (Qubits n × Qubits n) :=
  orthogonalProjector * choi (evolution g t) * orthogonalProjector

/-- A raw dummy zero is used only on zero-probability success histories; it is
not asserted to be a physical state, and never supplies a jump state at rate 0. -/
def preparedConditional (g : Super (Qubits n) (Qubits n)) (t : ℝ) :
    Op (Qubits n × Qubits n) :=
  let B := preparedBlock g t
  if 0 < B.trace.re then (B.trace.re : ℂ)⁻¹ • B else 0

def successCount (f : Fin M → Bool) : ℕ :=
  (Finset.univ.filter (fun j => f j = true)).card

def flagsWeight (p : ℝ) (f : Fin M → Bool) : ℝ :=
  ∏ j, if f j then p else 1-p

/-- Exact Algorithm-1 postprocessing on its counted flags and stored outputs.
The impossible insufficient-storage case is totalized explicitly, not assumed
away; the time-upper-bound statement must establish it cannot occur. -/
def flagDecisionProbability (k : ℕ) (eps1 eps2 : ℝ)
    (sigma : Op (Qubits n × Qubits n)) (f : Fin M → Bool) (yes : Bool) : ℝ :=
  let estimate := (successCount f : ℝ) / totalTime k eps1 eps2
  if estimate ≤ eps2 / (2 * qConstant k) then if yes then 1 else 0
  else if 2*eps2 ≤ estimate then if yes then 0 else 1
  else if retainedCount k eps1 eps2 ≤ successCount f then
    estimatorProbability sigma k (testAccuracy eps1 eps2) (fun h =>
      (decide (estimate * Real.sqrt (1+h) ≤ (eps1+eps2)/2)) = yes)
  else if yes then 1 else 0

/-- Composition of the actual flagged preparation with the fixed copy estimator.
All M attempts are charged, and the first R successes are retained. Conditional
on a flag sequence the independent successful states have this same Born law. -/
def algorithmProbability (k : ℕ) (bound eps1 eps2 : ℝ)
    (g : Super (Qubits n) (Qubits n)) (yes : Bool) : ℝ :=
  let t := attemptTime k bound eps1 eps2
  let B := preparedBlock g t
  ∑ f : Fin (attemptCount k bound eps1 eps2) → Bool,
    flagsWeight B.trace.re f *
      flagDecisionProbability k eps1 eps2 (preparedConditional g t) f yes

/-- Uniform constructive upper-bound contract. Realization of the explicit
Born-law algorithm is a conclusion, never an input assumption. -/
def UpperContract (k n : ℕ) (bound eps1 eps2 : ℝ) : Prop :=
  ∃ p : Protocol n ℕ, Admissible p ∧
    p.queries = attemptCount k bound eps1 eps2 ∧
    TimeAtMost p (totalTime k eps1 eps2) ∧
    totalTime k eps1 eps2 ≤ upperConstant k * eps2 / (eps2-eps1)^2 ∧
    Solves p k bound eps1 eps2 ∧
    (∀ g, SourceClass k bound g → ∀ b : Bool,
      outputProbability p g b = ENNReal.ofReal (algorithmProbability k bound eps1 eps2 g b)) ∧
    (∀ f : Fin (attemptCount k bound eps1 eps2) → Bool,
      eps2 / (2 * qConstant k) < (successCount f : ℝ) / totalTime k eps1 eps2 →
      (successCount f : ℝ) / totalTime k eps1 eps2 < 2*eps2 →
      retainedCount k eps1 eps2 ≤ successCount f)

def UniformUpper : Prop :=
  ∀ k : ℕ, 1 ≤ k → 0 < upperConstant k ∧
    ∀ n : ℕ, 1 ≤ n → ∀ bound eps1 eps2 : ℝ,
      0 < bound → 0 ≤ eps1 → eps1 < eps2 → eps2 ≤ bound / Real.sqrt 2 →
      UpperContract k n bound eps1 eps2

def UniformLower : Prop :=
  0 < lowerConstant ∧ ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 1 ≤ n →
    ∀ bound eps1 eps2 : ℝ, 0 < bound → 0 ≤ eps1 → eps1 < eps2 →
      eps2 ≤ bound / Real.sqrt 2 → ∀ (Ω : Type) (mΩ : MeasurableSpace Ω),
      letI := mΩ
      ∀ (p : Protocol n Ω) (T : ℝ), Admissible p → TimeAtMost p T →
        Solves p k bound eps1 eps2 →
        lowerConstant * (Real.sqrt eps2 + Real.sqrt eps1)^2 / (eps2-eps1)^2 ≤ T ∧
        lowerConstant * eps2 / (eps2-eps1)^2 ≤ T

end LindbladTolerant.Testing


