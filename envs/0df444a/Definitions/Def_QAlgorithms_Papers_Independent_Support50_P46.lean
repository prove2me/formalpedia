-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P46
-- name    : QAlgorithms_Papers_Independent_Support50_P46
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T23:56:13.27699+00:00
-- url     : https://prove2.me/theorems/b0eef94d-da1a-4dc4-a138-9c2933f8f9c9
-- title:
--   Definitions for Holographic Mutual Information is Monogamous
-- statement:
--   The objects the formalized statements of *Holographic Mutual Information is Monogamous* (arXiv:1107.2940) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SubsystemBasis`: PDF pp.3,5,17–18: computational basis of the subsystem consisting of exactly the qubits in s. In particular the empty subsystem has one basis vector.
--   - `reducedMatrix`: PDF pp.3,5,17–18: actual partial trace onto any union of qubit factors. For given retained row and column, the traced coordinates must agree. The double sum counts each complementary assignment exactly once.
--   - `tripartiteInformation`: PDF p.3, (1.5): I3 with its positive singleton convention. Subsystems are unions of fixed party factors, not new tensor factorizations. Frozen subsystemEntropy uses the retained and complementary coordinate restrictions and the accepted finite von Neumann entropy in bits.
--   - `threeMarginal`: PDF pp.5,17–18: ordered three-qubit marginal. All uses below select the three distinct wires 0,2,4; the output order is A,B,C.
--   - `redundantClassical`: PDF p.5, (2.1): (|000><000|+|111><111|)/2 in party order ABC.
--   - `xorClassical`: PDF p.5, (2.2): the equal mixture of 000,011,101,110 in order ABC.
--   - `copiedSixVector`: PDF p.17, (5.13) specialized to (2.2): party order AA-copy BB-copy CC-copy. Four independent choices of x,y have amplitude 1/2; z=x xor y.
--   - `copiedSixDensity`: PDF p.17, (5.13): actual rank-one density matrix of the six-party vector.
--   - `copiedFiveVector`: PDF p.18, (5.14): party order AA-copy BB-copy C. Four terms, amplitude 1/2, with z=x xor y; there is no copied C factor.
--   - `copiedFiveDensity`: PDF p.18, (5.14): actual pure five-party density matrix.
--   - `alternatingInformation`: PDF p.18, (6.2): the printed alternating subset sum, including the empty subset. This is the negative of the I3 convention in (1.5) when S(empty)=0.
--   - `localDivergence`: PDF pp.18–19: a local UV term sees only the incident regions at its junction. The empty union carries no entropy contribution when f(empty)=0.
-- source:
--   Holographic Mutual Information is Monogamous, arXiv:1107.2940v2, https://arxiv.org/abs/1107.2940v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

/-!
Statements from Hayden, Headrick and Maloney, arXiv:1107.2940v2.
Only the explicitly finite examples and the local-divergence cancellation
interface are represented here. All other nodes are accounted for in HARD.md.
Entropy is in bits for the finite examples; (6.2) uses the printed sign.
Compilation is pending the separate batch check.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P46

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Gap48.P20 (subsystemEntropy)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF pp.3,5,17–18: computational basis of the subsystem consisting of
exactly the qubits in s. In particular the empty subsystem has one basis vector. -/
abbrev SubsystemBasis {n : ℕ} (s : Finset (Fin n)) :=
  {i : Fin n // i ∈ s} → Bool

/-- PDF pp.3,5,17–18: actual partial trace onto any union of qubit factors.
For given retained row and column, the traced coordinates must agree.
The double sum counts each complementary assignment exactly once. -/
def reducedMatrix {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (s : Finset (Fin n)) : Matrix (SubsystemBasis s) (SubsystemBasis s) ℂ :=
  fun u v => ∑ x : Qubits n, ∑ y : Qubits n,
    if (∀ i : {i : Fin n // i ∈ s}, x i.val = u i) ∧
        (∀ i : {i : Fin n // i ∈ s}, y i.val = v i) ∧
        (∀ i : Fin n, i ∉ s → x i = y i) then rho x y else 0

/-- PDF p.3, (1.5): I3 with its positive singleton convention.
Subsystems are unions of fixed party factors, not new tensor factorizations.
Frozen subsystemEntropy uses the retained and complementary coordinate restrictions
and the accepted finite von Neumann entropy in bits. -/
def tripartiteInformation {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (a b c : Finset (Fin n)) : ℝ :=
  let S := fun s : Finset (Fin n) =>
    subsystemEntropy rho
      (fun x => fun i : {i : Fin n // i ∈ s} => x i.val)
      (fun x => fun i : {i : Fin n // i ∉ s} => x i.val)
  S a + S b + S c - S (a ∪ b) - S (b ∪ c) - S (a ∪ c) + S (a ∪ b ∪ c)

/-- PDF pp.5,17–18: ordered three-qubit marginal. All uses below select the
three distinct wires 0,2,4; the output order is A,B,C. -/
def threeMarginal {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (p : Fin 3 → Fin n) : Matrix (Qubits 3) (Qubits 3) ℂ :=
  fun u v => ∑ x : Qubits n, ∑ y : Qubits n,
    if (∀ j : Fin 3, x (p j) = u j) ∧
        (∀ j : Fin 3, y (p j) = v j) ∧
        (∀ i : Fin n, (∀ j : Fin 3, p j ≠ i) → x i = y i)
    then rho x y else 0

/-- PDF p.5, (2.1): (|000><000|+|111><111|)/2 in party order ABC. -/
def redundantClassical : Matrix (Qubits 3) (Qubits 3) ℂ :=
  fun u v => if u = v ∧ u 0 = u 1 ∧ u 1 = u 2 then 1 / 2 else 0

/-- PDF p.5, (2.2): the equal mixture of 000,011,101,110 in order ABC. -/
def xorClassical : Matrix (Qubits 3) (Qubits 3) ℂ :=
  fun u v => if u = v ∧ u 2 = Bool.xor (u 0) (u 1) then 1 / 4 else 0

/-- PDF p.17, (5.13) specialized to (2.2): party order AA-copy BB-copy CC-copy.
Four independent choices of x,y have amplitude 1/2; z=x xor y. -/
def copiedSixVector : EuclideanSpace ℂ (Qubits 6) :=
  WithLp.toLp 2 (fun u =>
    if u 0 = u 1 ∧ u 2 = u 3 ∧ u 4 = u 5 ∧
        u 4 = Bool.xor (u 0) (u 2) then (1 / 2 : ℂ) else 0)

/-- PDF p.17, (5.13): actual rank-one density matrix of the six-party vector. -/
def copiedSixDensity : Matrix (Qubits 6) (Qubits 6) ℂ :=
  pureDensity copiedSixVector

/-- PDF p.18, (5.14): party order AA-copy BB-copy C. Four terms, amplitude
1/2, with z=x xor y; there is no copied C factor. -/
def copiedFiveVector : EuclideanSpace ℂ (Qubits 5) :=
  WithLp.toLp 2 (fun u =>
    if u 0 = u 1 ∧ u 2 = u 3 ∧ u 4 = Bool.xor (u 0) (u 2)
    then (1 / 2 : ℂ) else 0)

/-- PDF p.18, (5.14): actual pure five-party density matrix. -/
def copiedFiveDensity : Matrix (Qubits 5) (Qubits 5) ℂ :=
  pureDensity copiedFiveVector

/-- PDF p.18, (6.2): the printed alternating subset sum, including the empty
subset. This is the negative of the I3 convention in (1.5) when S(empty)=0. -/
def alternatingInformation (n : ℕ) (s : Finset (Fin n) → ℝ) : ℝ :=
  ∑ sigma : Finset (Fin n), (-1 : ℝ) ^ sigma.card * s sigma

/-- PDF pp.18–19: a local UV term sees only the incident regions at its junction.
The empty union carries no entropy contribution when f(empty)=0. -/
def localDivergence {n : ℕ} (incident : Finset (Fin n))
    (f : Finset (Fin n) → ℝ) (sigma : Finset (Fin n)) : ℝ :=
  f (sigma ∩ incident)

example : redundantClassical (fun _ => false) (fun _ => false) = 1 / 2 := by
  simp [redundantClassical]

example : xorClassical (fun _ => false) (fun _ => false) = 1 / 4 := by
  simp [xorClassical]

example : copiedSixVector (fun _ => false) = 1 / 2 := by
  simp [copiedSixVector]

example : copiedFiveVector (fun _ => false) = 1 / 2 := by
  simp [copiedFiveVector]

example {n : ℕ} (s : Finset (Fin n)) :
    reducedMatrix (0 : Matrix (Qubits n) (Qubits n) ℂ) s = 0 := by
  ext u v
  simp [reducedMatrix]

example {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (u v : SubsystemBasis (∅ : Finset (Fin n))) :
    reducedMatrix rho ∅ u v = rho.trace := by
  classical
  have heq (x y : Qubits n) : (∀ i, x i = y i) ↔ x = y := by
    constructor
    · exact fun h => funext h
    · exact fun h i => congrFun h i
  simp [reducedMatrix, heq, Matrix.trace]

example {n : ℕ} (incident : Finset (Fin n)) (f : Finset (Fin n) → ℝ) :
    localDivergence incident f ∅ = f ∅ := by
  simp [localDivergence]

end QAlgorithms.Papers.Independent.Support50.P46


