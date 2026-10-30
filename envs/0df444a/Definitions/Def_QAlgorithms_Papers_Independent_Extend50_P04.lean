-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04
-- name    : QAlgorithms_Papers_Independent_Extend50_P04
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T13:07:31.539377+00:00
-- url     : https://prove2.me/theorems/1d6bf5fd-bda4-4f18-84f8-8bc0e3579053
-- title:
--   Definitions for Square-root measurements and degradation of the resource state in port-based teleportation scheme
-- statement:
--   The objects the formalized statements of *Square-root measurements and degradation of the resource state in port-based teleportation scheme* (arXiv:2105.14886) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Alice`: PDF p.5: Alice's N ports followed by input A0.
--   - `Whole`: PDF pp.14,19: Alice/input followed by Bob/reference, retaining every subsystem.
--   - `pbtBellProjector`: PDF p.5: normalized Bell projector on selected port/input, identity on spectators.
--   - `pbtSignal`: PDF p.5, (5): actual signal state; the spectator normalization is d^{-(N-1)}.
--   - `signalSum`: PDF p.5, (7): signal sum, of trace N rather than one.
--   - `inverseRoot`: PDF pp.5,9: spectral inverse square root, extended by zero on the kernel.
--   - `supportEffect`: PDF pp.5,9, (7),(29): support-only effect, before the nullspace completion.
--   - `pbtSupportComplement`: PDF p.5, (8): missing support projection.
--   - `fullEffect`: PDF p.5, (9): full POVM effect, including an equal share of the missing projection.
--   - `positiveRoot`: PDF pp.10,14: positive functional-calculus square root, never an arbitrary square root.
--   - `transposeInput`: PDF p.6, (13): transpose the input factor only, without complex conjugation.
--   - `pbtInputSwap`: PDF p.6: the physical swap of Alice port a with the input.
--   - `transposedSwap`: PDF p.6, (14): partially transposed swap on the actual tensor registers.
--   - `portPermutation`: PDF p.6, (11): port permutation, with identity on input.
--   - `pbtCollectiveAction`: PDF p.6, (10): U on every Alice port and conjugate U on input.
--   - `extendInput`: PDF pp.5,22: extend an operation on Alice's N ports by identity on input.
--   - `deletePort`: PDF pp.14,22: spectator coordinates in increasing order, deleting selected port a.
--   - `extendUnused`: PDF pp.22-24: embed the (N-1)-port operation only on unconsumed Alice ports.
--   - `initialState`: PDF pp.4,14: Bell input/reference and resource (O tensor I)|Phi+>, in all registers.
--   - `idealState`: PDF p.14, (73), p.22: ideal pairings, with O on the unused Alice ports only.
--   - `pbtLuedersBranch`: PDF p.14, (74): actual unnormalized branch from the full Lueders instrument.
--   - `normalizedBranch`: PDF pp.14,19: normalize a nonzero branch; the zero vector at zero probability carries zero weight.
--   - `recyclingFidelity`: PDF p.14, (75): Born-weighted UNSQUARED overlaps of entire ideal/output states. The physical source operations have Tr(O dagger O)=d^N, making initial/ideal vectors unit vectors.
--   - `nonoptimalFidelity`: PDF p.14: unoptimized one-round resource has O_N=I and O_(N-1)=I.
--   - `irrepDimension`: PDF pp.7-8: symmetric-group irrep dimension from the actual regular Young ideal.
--   - `pbtOneBoxSuccessor`: PDF p.7: one-box branching means containment between diagrams of the specified successive sizes.
--   - `forbiddenDimension`: PDF pp.7,10: removed height-(d+1) successor dimension, zero when no such shape occurs. Summing the independently constructed Specht dimensions avoids an unspecified theta parameter.
--   - `successorSum`: PDF pp.11-12: sum over physical successors only; the forbidden successor is not included.
--   - `overlapFormula`: PDF p.12, (57): explicit two-regime full-space trace expression.
--   - `qubitBracket`: PDF pp.12-13: binomial bracket; all coefficient subtraction occurs in the reals.
--   - `qubitOverlapSum`: PDF pp.12-13: sum with k=floor((N-1)/2); n=N-1 is used to avoid truncated N-1.
--   - `resourceOperation`: PDF p.16, (84): resource operation from nonnegative normalized shape coefficients.
--   - `teleportationObjective`: PDF p.5, (6): physical entanglement fidelity objective, not the recycling root fidelity.
--   - `IsOptimalCoefficients`: PDF pp.5,16,21: coefficients selected by the actual optimized deterministic channel objective. No unspecified teleportation matrix is supplied. The zero-port case is the normalized empty resource.
--   - `resourceState`: PDF p.17, (89): normalized entire bipartite resource, retaining both halves.
--   - `resourceFidelity`: PDF pp.17,26: unsquared pure-state overlap between unoptimized and optimized resources.
--   - `qubitRaw`: PDF pp.17,25: raw trigonometric entries (87)/(E5), before Euclidean normalization. The N=0 extension is the single empty shape, not division by sin(0).
--   - `qubitVector`: PDF p.25: the explicit Euclidean normalization required after (E5).
--   - `qubitMatrix`: PDF p.25, (E2)-(E4): concrete tridiagonal matrix, including the printed 1/4 scale. At the one-dimensional N=1 boundary use the first diagonal entry 1/4.
--   - `qubitCoefficient`: PDF p.17: invalid successor coefficients are zero; valid terminal coefficients are retained.
--   - `qubitCoefficients`: PDF pp.16-17: in dimension two a physical shape is uniquely labelled by its second-row length.
--   - `rowCoefficient`: PDF p.17, (90): read the coefficient of a given second-row length from a shape vector.
--   - `spinFormula`: PDF p.26, (G6): twice-spin t=2j indexing retains parity and integral factorial arguments. The real exponent N-2 avoids truncated natural subtraction at N=1.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, https://arxiv.org/abs/2105.14886v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_SchurCharacters

/-!
Statements from Studzinski, Mozrzymas, Kopszak, arXiv:2105.14886v4.
All page numbers below are PDF pages. Local constructions use the fixed computational basis.
`n` in recycling statements means N-1, so there is always at least one port.
Source corrections and deferred PRIR/multiround targets are recorded in the unit artifacts.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF p.5: Alice's N ports followed by input A0. -/
abbrev Alice (d N : ℕ) := (Fin N → Fin d) × Fin d

/-- PDF pp.14,19: Alice/input followed by Bob/reference, retaining every subsystem. -/
abbrev Whole (d N : ℕ) := Alice d N × Alice d N

/-- PDF p.5: normalized Bell projector on selected port/input, identity on spectators. -/
def pbtBellProjector (d N : ℕ) (a : Fin N) : Matrix (Alice d N) (Alice d N) ℂ :=
  fun x y => if x.1 a = x.2 ∧ y.1 a = y.2 ∧ ∀ i, i ≠ a → x.1 i = y.1 i
    then (d : ℂ)⁻¹ else 0

/-- PDF p.5, (5): actual signal state; the spectator normalization is d^{-(N-1)}. -/
def pbtSignal (d N : ℕ) (a : Fin N) : Matrix (Alice d N) (Alice d N) ℂ :=
  ((d : ℂ) ^ (N - 1))⁻¹ • pbtBellProjector d N a

/-- PDF p.5, (7): signal sum, of trace N rather than one. -/
def signalSum (d N : ℕ) : Matrix (Alice d N) (Alice d N) ℂ :=
  ∑ a, pbtSignal d N a

/-- PDF pp.5,9: spectral inverse square root, extended by zero on the kernel. -/
def inverseRoot (d N : ℕ) : Matrix (Alice d N) (Alice d N) ℂ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (signalSum d N)

/-- PDF pp.5,9, (7),(29): support-only effect, before the nullspace completion. -/
def supportEffect (d N : ℕ) (a : Fin N) : Matrix (Alice d N) (Alice d N) ℂ :=
  inverseRoot d N * pbtSignal d N a * inverseRoot d N

/-- PDF p.5, (8): missing support projection. -/
def pbtSupportComplement (d N : ℕ) : Matrix (Alice d N) (Alice d N) ℂ :=
  1 - ∑ a, supportEffect d N a

/-- PDF p.5, (9): full POVM effect, including an equal share of the missing projection. -/
def fullEffect (d N : ℕ) (a : Fin N) : Matrix (Alice d N) (Alice d N) ℂ :=
  supportEffect d N a + (N : ℂ)⁻¹ • pbtSupportComplement d N

/-- PDF pp.10,14: positive functional-calculus square root, never an arbitrary square root. -/
def positiveRoot {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc Real.sqrt A

/-- PDF p.6, (13): transpose the input factor only, without complex conjugation. -/
def transposeInput {d N : ℕ} (A : Matrix (Alice d N) (Alice d N) ℂ) :
    Matrix (Alice d N) (Alice d N) ℂ :=
  fun x y => A (x.1, y.2) (y.1, x.2)

/-- PDF p.6: the physical swap of Alice port a with the input. -/
def pbtInputSwap (d N : ℕ) (a : Fin N) : Matrix (Alice d N) (Alice d N) ℂ :=
  fun x y => if x = (Function.update y.1 a y.2, y.1 a) then 1 else 0

/-- PDF p.6, (14): partially transposed swap on the actual tensor registers. -/
def transposedSwap (d N : ℕ) (a : Fin N) : Matrix (Alice d N) (Alice d N) ℂ :=
  transposeInput (pbtInputSwap d N a)

/-- PDF p.6, (11): port permutation, with identity on input. -/
def portPermutation (d N : ℕ) (pi : Equiv.Perm (Fin N)) : Matrix (Alice d N) (Alice d N) ℂ :=
  Matrix.kronecker (Schur.tensorPermutation d N pi) 1

/-- PDF p.6, (10): U on every Alice port and conjugate U on input. -/
def pbtCollectiveAction (d N : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Alice d N) (Alice d N) ℂ :=
  fun x y => (∏ i, U (x.1 i) (y.1 i)) * star (U x.2 y.2)

/-- PDF pp.5,22: extend an operation on Alice's N ports by identity on input. -/
def extendInput {d N : ℕ} (O : Matrix ((Fin N → Fin d)) ((Fin N → Fin d)) ℂ) :
    Matrix (Alice d N) (Alice d N) ℂ :=
  Matrix.kronecker O 1

/-- PDF pp.14,22: spectator coordinates in increasing order, deleting selected port a. -/
def deletePort {d n : ℕ} (a : Fin (n + 1)) (x : (Fin (n + 1) → Fin d)) : (Fin n → Fin d) :=
  fun i => x (a.succAbove i)

/-- PDF pp.22-24: embed the (N-1)-port operation only on unconsumed Alice ports. -/
def extendUnused {d n : ℕ} (a : Fin (n + 1)) (O : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ) :
    Matrix (Alice d (n + 1)) (Alice d (n + 1)) ℂ :=
  fun x y => if x.1 a = y.1 a ∧ x.2 = y.2
    then O (deletePort a x.1) (deletePort a y.1) else 0

/-- PDF pp.4,14: Bell input/reference and resource (O tensor I)|Phi+>, in all registers. -/
def initialState (d N : ℕ) (O : Matrix ((Fin N → Fin d)) ((Fin N → Fin d)) ℂ) :
    EuclideanSpace ℂ (Whole d N) :=
  WithLp.toLp 2 fun x => if x.1.2 = x.2.2
    then O x.1.1 x.2.1 / (Real.sqrt ((d : ℝ) ^ (N + 1)) : ℂ) else 0

/-- PDF p.14, (73), p.22: ideal pairings, with O on the unused Alice ports only. -/
def idealState (d n : ℕ) (a : Fin (n + 1)) (O : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ) :
    EuclideanSpace ℂ (Whole d (n + 1)) :=
  WithLp.toLp 2 fun x => if x.1.1 a = x.1.2 ∧ x.2.1 a = x.2.2 then
    O (deletePort a x.1.1) (deletePort a x.2.1) /
      ((d : ℂ) * (Real.sqrt ((d : ℝ) ^ n) : ℂ)) else 0

/-- PDF p.14, (74): actual unnormalized branch from the full Lueders instrument. -/
def pbtLuedersBranch (d N : ℕ) (O : Matrix ((Fin N → Fin d)) ((Fin N → Fin d)) ℂ) (a : Fin N) :
    EuclideanSpace ℂ (Whole d N) :=
  act (Matrix.kronecker (positiveRoot (fullEffect d N a)) 1) (initialState d N O)

/-- PDF pp.14,19: normalize a nonzero branch; the zero vector at zero probability carries zero weight. -/
def normalizedBranch (d N : ℕ) (O : Matrix ((Fin N → Fin d)) ((Fin N → Fin d)) ℂ) (a : Fin N) :
    EuclideanSpace ℂ (Whole d N) :=
  ((‖pbtLuedersBranch d N O a‖ : ℂ)⁻¹) • pbtLuedersBranch d N O a

/-- PDF p.14, (75): Born-weighted UNSQUARED overlaps of entire ideal/output states.
The physical source operations have Tr(O dagger O)=d^N, making initial/ideal vectors unit vectors. -/
def recyclingFidelity (d n : ℕ) (O : Matrix ((Fin (n + 1) → Fin d)) ((Fin (n + 1) → Fin d)) ℂ)
    (R : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ) : ℝ :=
  ∑ a : Fin (n + 1), ‖pbtLuedersBranch d (n + 1) O a‖ ^ 2 *
    ‖inner ℂ (idealState d n a R) (normalizedBranch d (n + 1) O a)‖

/-- PDF p.14: unoptimized one-round resource has O_N=I and O_(N-1)=I. -/
def nonoptimalFidelity (d n : ℕ) : ℝ := recyclingFidelity d n 1 1

/-- PDF pp.7-8: symmetric-group irrep dimension from the actual regular Young ideal. -/
def irrepDimension {d N : ℕ} (mu : Schur.Partition d N) : ℕ :=
  Module.finrank ℂ (Schur.spechtSpace mu)

/-- PDF p.7: one-box branching means containment between diagrams of the specified successive sizes. -/
def pbtOneBoxSuccessor {d e n : ℕ} (alpha : Schur.Partition d n) (mu : Schur.Partition e (n + 1)) : Prop :=
  alpha.val ≤ mu.val

/-- PDF pp.7,10: removed height-(d+1) successor dimension, zero when no such shape occurs.
Summing the independently constructed Specht dimensions avoids an unspecified theta parameter. -/
def forbiddenDimension {d n : ℕ} (alpha : Schur.Partition d n) : ℝ :=
  ∑ theta : Schur.Partition (d + 1) (n + 1),
    if pbtOneBoxSuccessor alpha theta ∧ theta.val.colLen 0 = d + 1 then irrepDimension theta else 0

/-- PDF pp.11-12: sum over physical successors only; the forbidden successor is not included. -/
def successorSum {d n : ℕ} (alpha : Schur.Partition d n) : ℝ :=
  ∑ nu : Schur.Partition d (n + 1),
    if pbtOneBoxSuccessor alpha nu then Real.sqrt (Schur.schurDimension nu * irrepDimension nu) else 0

/-- PDF p.12, (57): explicit two-regime full-space trace expression. -/
def overlapFormula (d n : ℕ) : ℝ :=
  ∑ alpha : Schur.Partition d n,
    if alpha.val.colLen 0 < d then (successorSum alpha) ^ 2 / (n + 1 : ℝ)
    else Real.sqrt (irrepDimension alpha) * (successorSum alpha) ^ 2 /
      (Real.sqrt ((n + 1 : ℝ) * irrepDimension alpha - forbiddenDimension alpha) *
        Real.sqrt (n + 1 : ℝ))

/-- PDF pp.12-13: binomial bracket; all coefficient subtraction occurs in the reals. -/
def qubitBracket (N l : ℕ) : ℝ :=
  ((N : ℝ) - 2 * l + 1) * Real.sqrt ((Nat.choose (N + 1) l : ℝ) / (N + 1 : ℝ)) +
  ((N : ℝ) - 2 * l - 1) * Real.sqrt ((Nat.choose (N + 1) (l + 1) : ℝ) / (N + 1 : ℝ))

/-- PDF pp.12-13: sum with k=floor((N-1)/2); n=N-1 is used to avoid truncated N-1. -/
def qubitOverlapSum (n : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (n / 2 + 1),
    Real.sqrt (((n + 2 : ℝ) - l) * (l + 1 : ℝ) / (n + 2 : ℝ)) *
      qubitBracket (n + 1) l ^ 2

/-- PDF p.16, (84): resource operation from nonnegative normalized shape coefficients. -/
def resourceOperation (d N : ℕ) (v : Schur.Partition d N → ℝ) :
    Matrix ((Fin N → Fin d)) ((Fin N → Fin d)) ℂ :=
  (Real.sqrt ((d : ℝ) ^ N) : ℂ) • ∑ mu,
    ((v mu / Real.sqrt (irrepDimension mu * Schur.schurDimension mu) : ℝ) : ℂ) •
      Schur.isotypicProjector mu

/-- PDF p.5, (6): physical entanglement fidelity objective, not the recycling root fidelity. -/
def teleportationObjective (d N : ℕ) (O : Matrix ((Fin N → Fin d)) ((Fin N → Fin d)) ℂ)
    (M : Fin N → Matrix (Alice d N) (Alice d N) ℂ) : ℝ :=
  (∑ a, ((extendInput O)ᴴ * M a * extendInput O * pbtSignal d N a).trace.re) / (d : ℝ) ^ 2

/-- PDF pp.5,16,21: coefficients selected by the actual optimized deterministic channel objective.
No unspecified teleportation matrix is supplied. The zero-port case is the normalized empty resource. -/
def IsOptimalCoefficients (d N : ℕ) (v : Schur.Partition d N → ℝ) : Prop :=
  (∀ mu, 0 ≤ v mu) ∧ (∑ mu, v mu ^ 2) = 1 ∧
    (0 < N → ∀ (O : Matrix ((Fin N → Fin d)) ((Fin N → Fin d)) ℂ)
      (M : Fin N → Matrix (Alice d N) (Alice d N) ℂ),
      (Oᴴ * O).trace = (d : ℂ) ^ N →
      (∀ a, (M a).PosSemidef) → (∑ a, M a) = 1 →
      teleportationObjective d N O M ≤
        teleportationObjective d N (resourceOperation d N v) (fullEffect d N))

/-- PDF p.17, (89): normalized entire bipartite resource, retaining both halves. -/
def resourceState (d N : ℕ) (O : Matrix ((Fin N → Fin d)) ((Fin N → Fin d)) ℂ) :
    EuclideanSpace ℂ ((Fin N → Fin d) × (Fin N → Fin d)) :=
  WithLp.toLp 2 fun x => O x.1 x.2 / (Real.sqrt ((d : ℝ) ^ N) : ℂ)

/-- PDF pp.17,26: unsquared pure-state overlap between unoptimized and optimized resources. -/
def resourceFidelity (d N : ℕ) (O : Matrix ((Fin N → Fin d)) ((Fin N → Fin d)) ℂ) : ℝ :=
  ‖inner ℂ (resourceState d N 1) (resourceState d N O)‖

/-- PDF pp.17,25: raw trigonometric entries (87)/(E5), before Euclidean normalization.
The N=0 extension is the single empty shape, not division by sin(0). -/
def qubitRaw (N : ℕ) (l : Fin (N / 2 + 1)) : ℝ :=
  if N = 0 then 1 else
  if N % 2 = 0 then
    (-1 : ℝ) ^ (N / 2 - l.val) *
      (Real.sin ((((N : ℝ) + 2) / 2 - l.val) * N * Real.pi / (N + 2)) -
        Real.sin (((N : ℝ) / 2 - l.val) * N * Real.pi / (N + 2))) /
      Real.sin ((N : ℝ) * Real.pi / (N + 2))
  else
    (-1 : ℝ) ^ ((N - 1) / 2 - l.val) *
      Real.sin ((((N : ℝ) + 1) / 2 - l.val) * N * Real.pi / (N + 2)) /
      Real.sin ((N : ℝ) * Real.pi / (N + 2))

/-- PDF p.25: the explicit Euclidean normalization required after (E5). -/
def qubitVector (N : ℕ) (l : Fin (N / 2 + 1)) : ℝ :=
  qubitRaw N l / Real.sqrt (∑ j, qubitRaw N j ^ 2)

/-- PDF p.25, (E2)-(E4): concrete tridiagonal matrix, including the printed 1/4 scale.
At the one-dimensional N=1 boundary use the first diagonal entry 1/4. -/
def qubitMatrix (N : ℕ) : Matrix (Fin (N / 2 + 1)) (Fin (N / 2 + 1)) ℝ :=
  fun i j => (1 / 4 : ℝ) * (if i = j then
    2 - (if i.val = 0 then 1 else 0) - (if N % 2 = 0 ∧ i.val = N / 2 then 1 else 0)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0)

/-- PDF p.17: invalid successor coefficients are zero; valid terminal coefficients are retained. -/
def qubitCoefficient (N l : ℕ) : ℝ :=
  if h : l < N / 2 + 1 then qubitVector N ⟨l, h⟩ else 0

/-- PDF pp.16-17: in dimension two a physical shape is uniquely labelled by its second-row length. -/
def qubitCoefficients (N : ℕ) (mu : Schur.Partition 2 N) : ℝ :=
  qubitCoefficient N (mu.val.rowLen 1)

/-- PDF p.17, (90): read the coefficient of a given second-row length from a shape vector. -/
def rowCoefficient (N : ℕ) (v : Schur.Partition 2 N → ℝ) (l : ℕ) : ℝ :=
  ∑ mu, if mu.val.rowLen 1 = l then v mu else 0

/-- PDF p.26, (G6): twice-spin t=2j indexing retains parity and integral factorial arguments.
The real exponent N-2 avoids truncated natural subtraction at N=1. -/
def spinFormula (N : ℕ) : ℝ :=
  Real.sqrt ((N.factorial : ℝ) / ((2 : ℝ) ^ ((N : ℝ) - 2) * (N + 2 : ℝ))) *
    ∑ t ∈ (Finset.range (N + 1)).filter (fun t => t % 2 = N % 2),
      (t + 1 : ℝ) * Real.sin (Real.pi * (t + 1 : ℝ) / (N + 2 : ℝ)) /
        Real.sqrt ((((N - t) / 2).factorial : ℝ) * (((N + t) / 2 + 1).factorial : ℝ))

/-! Sanity examples pin indexing and total-function boundary behavior; no theorem proofs. -/

example {d N : ℕ} (M : Matrix (Alice d N) (Alice d N) ℂ) :
    transposeInput (transposeInput M) = M := rfl

example (d N : ℕ) (a : Fin N) :
    fullEffect d N a = supportEffect d N a + (N : ℂ)⁻¹ • pbtSupportComplement d N := rfl

example {d : ℕ} (x : (Fin 1 → Fin d)) (i : Fin 0) : deletePort (0 : Fin 1) x i = x ((0 : Fin 1).succAbove i) := rfl

example {d : ℕ} (O : Matrix ((Fin 0 → Fin d)) ((Fin 0 → Fin d)) ℂ)
    (x : Whole d 1) :
    idealState d 0 (0 : Fin 1) O x =
      if x.1.1 0 = x.1.2 ∧ x.2.1 0 = x.2.2 then
        O (deletePort 0 x.1.1) (deletePort 0 x.2.1) / (d : ℂ) else 0 := by
  simp [idealState]

example : qubitRaw 0 (0 : Fin 1) = 1 := by simp [qubitRaw]

example : qubitCoefficient 1 1 = 0 := by simp [qubitCoefficient]

example : qubitMatrix 1 (0 : Fin 1) 0 = (1 / 4 : ℝ) := by norm_num [qubitMatrix]

end QAlgorithms.Papers.Independent.Extend50.P04


