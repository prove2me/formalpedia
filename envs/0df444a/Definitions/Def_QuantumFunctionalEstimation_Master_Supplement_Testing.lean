-- Prove2me | Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Testing
-- name    : QuantumFunctionalEstimation_Master_Supplement_Testing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:56:25.40163+00:00
-- url     : https://prove2.me/theorems/cc09243a-d234-453d-a61c-2189ef57a14d
-- title:
--   Two-sided promise testing, Schmidt rank, and open-boundary MPS
-- statement:
--   A Boolean collective POVM accepts every state in the yes class with probability at least $2/3$ and rejects every state in the no class with probability at least $2/3$. There is no condition in the promise gap. For rank testing these classes are $\operatorname{rank}(\rho)\le r$ and $\Delta_r(\rho)\ge\varepsilon$.
--
--   For a unit bipartite vector $\psi$, its Schmidt rank is the matrix rank of $\operatorname{tr}_B|\psi\rangle\langle\psi|$. Being $\varepsilon$-far means trace distance at least $\varepsilon$ from every unit vector of Schmidt rank at most $r$.
--
--   For positive site dimensions $d_1,\ldots,d_n$, an open-boundary matrix product state has coefficients
--   $$\psi_{i_1\cdots i_n}=A^{(1)}_{i_1}\cdots A^{(n)}_{i_n},$$
--   with bond dimensions $1,r,\ldots,r,1$. Contraction sums the internal bond indices in site order. Only normalized vectors enter the testing classes. All bonds at most $r$ are represented by zero padding, and site dimensions may vary. Being far from this class is a universal comparison of pure-projector trace distances, equivalent to the infimum definition because the approximation class is nonempty in every theorem regime.
--
--   These are unrestricted two-sided promise predicates. Lower bounds without an ambient dimension parameter quantify over testers handling every positive finite dimension with the same copy budget.
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed pp. 33–36 (PDF pp. 35–38), equation (38), §§5.7–5.9

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Observables
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Boolean collective POVM. True denotes acceptance of the yes class. -/
def PromiseSuccessful {ι : Type} [Fintype ι] [DecidableEq ι]
    (yes no : Set (Matrix ι ι ℂ)) (N : ℕ)
    (E : QAlgorithms.Measurements.OperatorPOVM (Fin N → ι) Bool) : Prop :=
  (∀ ρ ∈ yes, (2 / 3 : ℝ) ≤
    QAlgorithms.effectProb (E.operator {true}) (QAlgorithms.piKron N ρ)) ∧
  (∀ ρ ∈ no, (2 / 3 : ℝ) ≤
    QAlgorithms.effectProb (E.operator {false}) (QAlgorithms.piKron N ρ))

def RankSuccessful (d r N : ℕ) (ε : ℝ)
    (E : QAlgorithms.Measurements.OperatorPOVM (Fin N → Fin d) Bool) : Prop :=
  PromiseSuccessful {ρ | QAlgorithms.IsDensityMatrix ρ ∧ ρ.rank ≤ r}
    {ρ | QAlgorithms.IsDensityMatrix ρ ∧ ε ≤ rankTail r ρ} N E

abbrev UnitVector (ι : Type) [Fintype ι] := {ψ : EuclideanSpace ℂ ι // ‖ψ‖ = 1}

def reducedA {a b : ℕ} (ψ : UnitVector (Fin a × Fin b)) : Matrix (Fin a) (Fin a) ℂ :=
  fun i j => ∑ k : Fin b, QAlgorithms.pureDensity ψ.val (i, k) (j, k)

def schmidtRank {a b : ℕ} (ψ : UnitVector (Fin a × Fin b)) : ℕ := (reducedA ψ).rank

/-- Universal distance comparison is equivalent to the infimum formulation; no inf default. -/
def SchmidtFar {a b : ℕ} (r : ℕ) (ε : ℝ) (ψ : UnitVector (Fin a × Fin b)) : Prop :=
  ∀ φ : UnitVector (Fin a × Fin b), schmidtRank φ ≤ r →
    ε ≤ QAlgorithms.traceDistance (QAlgorithms.pureDensity ψ.val) (QAlgorithms.pureDensity φ.val)

def SchmidtSuccessful (a b r N : ℕ) (ε : ℝ)
    (E : QAlgorithms.Measurements.OperatorPOVM (Fin N → Fin a × Fin b) Bool) : Prop :=
  PromiseSuccessful
    {ρ | ∃ ψ : UnitVector (Fin a × Fin b), schmidtRank ψ ≤ r ∧ ρ = QAlgorithms.pureDensity ψ.val}
    {ρ | ∃ ψ : UnitVector (Fin a × Fin b), SchmidtFar r ε ψ ∧ ρ = QAlgorithms.pureDensity ψ.val} N E

abbrev Sites {n : ℕ} (dims : Fin n → ℕ) := (i : Fin n) → Fin (dims i)

/-- Endpoint bonds have size one; all interior bonds have size r, allowing zero padding. -/
def bondSize (n r j : ℕ) : ℕ := if j = 0 ∨ j = n then 1 else r

structure MPSTensors {n : ℕ} (dims : Fin n → ℕ) (r : ℕ) where
  tensor : (i : Fin n) → Fin (dims i) →
    Matrix (Fin (bondSize n r i.val)) (Fin (bondSize n r (i.val + 1))) ℂ

/-- Contraction in site order. Every bond index is summed, including the singleton endpoints. -/
def mpsAmplitude {n r : ℕ} {dims : Fin n → ℕ} (A : MPSTensors dims r) (x : Sites dims) : ℂ :=
  ∑ β : (j : Fin (n + 1)) → Fin (bondSize n r j.val),
    ∏ i : Fin n, A.tensor i (x i) (β i.castSucc) (β i.succ)

def IsMPS {n : ℕ} {dims : Fin n → ℕ} (r : ℕ) (ψ : UnitVector (Sites dims)) : Prop :=
  ∃ A : MPSTensors dims r, ∀ x, ψ.val x = mpsAmplitude A x

def MPSFar {n : ℕ} {dims : Fin n → ℕ} (r : ℕ) (ε : ℝ) (ψ : UnitVector (Sites dims)) : Prop :=
  ∀ φ : UnitVector (Sites dims), IsMPS r φ →
    ε ≤ QAlgorithms.traceDistance (QAlgorithms.pureDensity ψ.val) (QAlgorithms.pureDensity φ.val)

def MPSSuccessful {n : ℕ} (dims : Fin n → ℕ) (r N : ℕ) (ε : ℝ)
    (E : QAlgorithms.Measurements.OperatorPOVM (Fin N → Sites dims) Bool) : Prop :=
  PromiseSuccessful
    {ρ | ∃ ψ : UnitVector (Sites dims), IsMPS r ψ ∧ ρ = QAlgorithms.pureDensity ψ.val}
    {ρ | ∃ ψ : UnitVector (Sites dims), MPSFar r ε ψ ∧ ρ = QAlgorithms.pureDensity ψ.val} N E

end QuantumFunctionalEstimation.Master.Supplement


