-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P39
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T09:42:29.758187+00:00
-- url     : https://prove2.me/theorems/2ff888f5-5b84-40ee-af1a-333f8ffcad62
-- title:
--   Definitions for Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates
-- statement:
--   The objects the formalized statements of *Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates* (arXiv:0712.3227) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `traceFidelity`: PDF p.5, Eq. (14): the phase-sensitive real trace fidelity.
--   - `quality`: PDF p.5, Eq. (13): scalar quality in the independent relaxation model.
--   - `specialUnitaryTangent`: PDF p.4: actual real tangent space of the special unitary group.
--   - `tensorLeftTangent`: PDF p.4, Eq. (5): tangent image of SU(a) tensor identity_b.
--   - `tensorRightTangent`: PDF p.4, Eq. (6): tangent image of identity_a tensor SU(b).
--   - `OneFactorQuotient`: PDF p.4: quotient tangent space for the one-factor tensor subgroup.
--   - `TwoFactorQuotient`: PDF p.4: quotient tangent space for the two-factor tensor subgroup. The differential image is the sum of the two tensor-factor tangent images.
--   - `marginalDemand`: PDF p.5, Eqs. (11)-(12): residual demand in the two-overhead parameter-count lower envelope. Arithmetic is real, without truncated subtraction.
--   - `marginalIncrement`: PDF pp.4-5: effective coset parameter increment for balanced even m.
--   - `marginalGateBound`: PDF p.5, Eq. (11): balanced parameter-count lower envelope used in the asymptotic comparison. This is a numerical threshold, not an algorithm.
--   - `marginalSlotBound`: PDF p.5, Eq. (12): balanced parameter-count slot lower envelope.
--   - `firstHalf`: PDF pp.9,19: extracting the two ordered halves of a 2m-wire block.
--   - `secondHalf`: PDF pp.9,19: extracting the second half, in most significant bit order.
--   - `exchangeHalves`: PDF pp.9,19: exchanging two contiguous, internally ordered blocks.
--   - `cpSwap`: PDF p.9, Figs.6-7: phase-distance cp-swap of type j, on two m-bit blocks. First apply exp(2 pi i ab / 2^((j+1)m)), then exchange blocks.
--   - `truncatedCpSwap`: PDF pp.10,19, Fig.17: delete exactly those pair phases whose angle is strictly smaller than pi/2^cutoff. The equality case is retained.
--   - `blockSwap`: PDF pp.9,19: the pure block permutation, without a phase.
--   - `BlockStep`: PDF pp.9,19: a block-circuit instruction with its actual wire offset. Phase-swap width is the half-width; j specifies the phase distance.
--   - `placeBlock`: PDF pp.9,19: placing a block on contiguous wires. Invalid placements return identity; every circuit in the results below has valid placements.
--   - `BlockStep.matrix`: PDF pp.9,19: the matrix specified by one placed module.
--   - `blockCircuitMatrix`: PDF pp.9,19: chronological circuit semantics, retaining the full permutation and phase. No target QFT is used in this definition.
--   - `qftInsertion`: PDF p.9, Fig.7: process one more input block. Its successive exchanges with the processed blocks have types t,t-1,...,1, followed by QFT on the new leading block.
--   - `qftAssembly`: PDF p.9, Fig.7: the explicit scalable QFT circuit, starting with the first m-wire QFT and inserting successive input blocks in chronological order.
--   - `fourierCount`: PDF p.9: number of actual Fourier block occurrences.
--   - `phaseCount`: PDF p.9: number of actual phase-swap occurrences of a given type.
--   - `phaseTotal`: PDF pp.9,19: total number of phase-swap module occurrences.
--   - `halfBlockExpansion`: PDF p.19, Fig.16: resolve a phase-swap on two 2h-bit blocks into four phase-swaps on pairs of h-bit blocks, preserving chronological order.
--   - `qftAssemblyII`: PDF p.19, Appendix A: the explicit variant-II half-block circuit.
--   - `truncateBlockStep`: PDF p.10: replace each phase module by its strict-cutoff version. If even its largest pair phase is deleted, the resulting module is a pure block swap. Fourier blocks and already specified swap modules are retained.
--   - `truncatedQftAssembly`: PDF p.10, Eq.(27): the actual approximating block circuit obtained by truncating phase rotations in the Fig.7 assembly.
--   - `blockQuality`: PDF pp.5,10, Eqs. (26)-(27): product of occurrence fidelities of an actual block list, times relaxation for its assigned elapsed duration.
--   - `panelStep`: PDF p.19, Fig.17: an adjacent phase rotation followed by SWAP, or just SWAP when the indicated rotation is deleted.
--   - `panelA`: PDF p.19: panel (a), all 25 crossings, with angles pi/2 through pi/512. Each next second-block bit moves left across the five first-block bits.
--   - `panelB`: PDF p.19: panel (b), retaining precisely the triangular set a+b<=4, whose angles are pi/64 through pi/1024.
--   - `panelC`: PDF p.19: panel (c), the block exchange after every phase is deleted.
--   - `fittedInteriorCost`: PDF p.13, Eq. (35): fitted interior-block cost, with the printed regression decimals treated as exact rationals defining this surrogate.
--   - `jordanMatrix`: PDF p.13, Eq. (36): the printed transposed bidiagonal array, as a column-vector matrix. The lower off-diagonal is one.
--   - `endpointMatrix`: PDF p.13, Eq. (38): identity plus the bottom-left endpoint entry.
--   - `bitCnot`: PDF p.13, Fig.12: CNOT on designated distinct wires, acting on every basis word, including arbitrary values of all intermediate wires.
--   - `ascendingSweep`: PDF p.13, Fig.12: ascending neighboring CNOT sweep.
--   - `descendingSweep`: PDF p.13, Fig.12: the opposite neighboring CNOT sweep. The reverse chronological list implements I plus the lower one-step shift.
--   - `endpointCnot`: PDF p.13, Fig.12: the endpoint CNOT, preserving every intermediate bit.
-- source:
--   Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates, arXiv:0712.3227v2, https://arxiv.org/abs/0712.3227v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Fourier

/-!
Statements from Schulte-Herbrueggen, Spoerl and Glaser, arXiv:0712.3227v2.
Wire zero is the most significant bit. Lists are chronological; their reverse
matrix product acts on column vectors. Physical timing observations are not
assumed in exact circuit identities. See the unit's HARD.md for deferred nodes.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P39

open scoped BigOperators

/-- PDF p.5, Eq. (14): the phase-sensitive real trace fidelity. -/
noncomputable def traceFidelity {n : ℕ}
    (U V : Matrix (Qubits n) (Qubits n) ℂ) : ℝ :=
  (Matrix.trace (star V * U)).re / (2 : ℝ) ^ n

/-- PDF p.5, Eq. (13): scalar quality in the independent relaxation model. -/
noncomputable def quality (F T TR : ℝ) : ℝ := F * Real.exp (-T / TR)

example (F TR : ℝ) : quality F 0 TR = F := by simp [quality]

example (n : ℕ) : traceFidelity (0 : Matrix (Qubits n) (Qubits n) ℂ) 0 = 0 := by
  simp [traceFidelity]

/-- PDF p.4: actual real tangent space of the special unitary group. -/
def specialUnitaryTangent (ι : Type*) [Fintype ι] :
    Submodule ℝ (Matrix ι ι ℂ) where
  carrier := {A | star A = -A ∧ Matrix.trace A = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    constructor
    · simp [star_add, hA.1, hB.1, add_comm]
    · simp [Matrix.trace_add, hA.2, hB.2]
  smul_mem' := by
    intro r A hA
    constructor
    · simp [star_smul, hA.1]
    · simp [Matrix.trace_smul, hA.2]

/-- PDF p.4, Eq. (5): tangent image of SU(a) tensor identity_b. -/
noncomputable def tensorLeftTangent (a b : ℕ) :
    Submodule ℝ (Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :=
  Submodule.span ℝ ((fun A : Matrix (Fin a) (Fin a) ℂ =>
    Matrix.kronecker A (1 : Matrix (Fin b) (Fin b) ℂ)) ''
      (specialUnitaryTangent (Fin a) : Set (Matrix (Fin a) (Fin a) ℂ)))

/-- PDF p.4, Eq. (6): tangent image of identity_a tensor SU(b). -/
noncomputable def tensorRightTangent (a b : ℕ) :
    Submodule ℝ (Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :=
  Submodule.span ℝ ((fun B : Matrix (Fin b) (Fin b) ℂ =>
    Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) B) ''
      (specialUnitaryTangent (Fin b) : Set (Matrix (Fin b) (Fin b) ℂ)))

/-- PDF p.4: quotient tangent space for the one-factor tensor subgroup. -/
abbrev OneFactorQuotient (a b : ℕ) :=
  (specialUnitaryTangent (Fin a × Fin b)) ⧸
    ((tensorLeftTangent a b).comap (specialUnitaryTangent (Fin a × Fin b)).subtype)

/-- PDF p.4: quotient tangent space for the two-factor tensor subgroup.
The differential image is the sum of the two tensor-factor tangent images. -/
abbrev TwoFactorQuotient (a b : ℕ) :=
  (specialUnitaryTangent (Fin a × Fin b)) ⧸
    ((tensorLeftTangent a b ⊔ tensorRightTangent a b).comap
      (specialUnitaryTangent (Fin a × Fin b)).subtype)

example : (0 : Matrix (Fin 1) (Fin 1) ℂ) ∈ specialUnitaryTangent (Fin 1) :=
  (specialUnitaryTangent (Fin 1)).zero_mem

example (a b : ℕ) : (0 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ∈
    tensorLeftTangent a b := (tensorLeftTangent a b).zero_mem

example (a b : ℕ) : (0 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ∈
    tensorRightTangent a b := (tensorRightTangent a b).zero_mem

/-- PDF p.5, Eqs. (11)-(12): residual demand in the two-overhead
parameter-count lower envelope. Arithmetic is real, without truncated subtraction. -/
noncomputable def marginalDemand (n m : ℕ) : ℝ :=
  (4 : ℝ) ^ n + 1 - 2 * (4 : ℝ) ^ (m - m / 2) -
    (n / m : ℕ) * ((4 : ℝ) ^ m - 1)

/-- PDF pp.4-5: effective coset parameter increment for balanced even m. -/
noncomputable def marginalIncrement (m : ℕ) : ℝ :=
  (4 : ℝ) ^ m - (4 : ℝ) ^ (m / 2) - (4 : ℝ) ^ (m - m / 2) + 1

/-- PDF p.5, Eq. (11): balanced parameter-count lower envelope used in
the asymptotic comparison. This is a numerical threshold, not an algorithm. -/
noncomputable def marginalGateBound (n m : ℕ) : ℤ :=
  Int.ceil (marginalDemand n m / marginalIncrement m) + (n / m : ℕ)

/-- PDF p.5, Eq. (12): balanced parameter-count slot lower envelope. -/
noncomputable def marginalSlotBound (n m : ℕ) : ℤ :=
  1 + Int.ceil (marginalDemand n m / ((n / m : ℕ) * marginalIncrement m))

example : marginalDemand 2 2 = -6 := by norm_num [marginalDemand]

example : marginalIncrement 2 = 9 := by norm_num [marginalIncrement]

example : marginalGateBound 2 2 = 1 := by
  norm_num [marginalGateBound, marginalDemand, marginalIncrement]

example : marginalSlotBound 2 2 = 1 := by
  norm_num [marginalSlotBound, marginalDemand, marginalIncrement]

/-- PDF pp.9,19: extracting the two ordered halves of a 2m-wire block. -/
def firstHalf {m : ℕ} (x : Qubits (2 * m)) : Qubits m :=
  fun i => x ⟨i.val, by omega⟩

/-- PDF pp.9,19: extracting the second half, in most significant bit order. -/
def secondHalf {m : ℕ} (x : Qubits (2 * m)) : Qubits m :=
  fun i => x ⟨m + i.val, by omega⟩

/-- PDF pp.9,19: exchanging two contiguous, internally ordered blocks. -/
def exchangeHalves {m : ℕ} (x : Qubits (2 * m)) : Qubits (2 * m) :=
  fun i => if h : i.val < m then x ⟨m + i.val, by omega⟩
    else x ⟨i.val - m, by omega⟩

/-- PDF p.9, Figs.6-7: phase-distance cp-swap of type j, on two m-bit
blocks. First apply exp(2 pi i ab / 2^((j+1)m)), then exchange blocks. -/
noncomputable def cpSwap (m j : ℕ) :
    Matrix (Qubits (2 * m)) (Qubits (2 * m)) ℂ :=
  fun y x => if y = exchangeHalves x then
    Complex.exp (2 * Real.pi * Complex.I *
      (bitsToNat (firstHalf x) * bitsToNat (secondHalf x) : ℕ) /
        (2 : ℂ) ^ ((j + 1) * m)) else 0

/-- PDF pp.10,19, Fig.17: delete exactly those pair phases whose angle is
strictly smaller than pi/2^cutoff. The equality case is retained. -/
noncomputable def truncatedCpSwap (m j cutoff : ℕ) :
    Matrix (Qubits (2 * m)) (Qubits (2 * m)) ℂ :=
  fun y x => if y = exchangeHalves x then
    Complex.exp (Complex.I * (∑ a : Fin m, ∑ b : Fin m,
      if firstHalf x a && secondHalf x b then
        if (j - 1) * m + 1 + a.val + b.val ≤ cutoff then
          Real.pi / (2 : ℝ) ^ ((j - 1) * m + 1 + a.val + b.val)
        else 0
      else 0 : ℝ)) else 0

/-- PDF pp.9,19: the pure block permutation, without a phase. -/
def blockSwap (m : ℕ) : Matrix (Qubits (2 * m)) (Qubits (2 * m)) ℂ :=
  fun y x => if y = exchangeHalves x then 1 else 0

/-- PDF pp.9,19: a block-circuit instruction with its actual wire offset.
Phase-swap width is the half-width; j specifies the phase distance. -/
inductive BlockStep where
  | fourier (offset width : ℕ)
  | phaseSwap (offset halfWidth phaseIndex : ℕ)
  | truncatedPhaseSwap (offset halfWidth phaseIndex cutoff : ℕ)
  | swap (offset halfWidth : ℕ)
  deriving DecidableEq

/-- PDF pp.9,19: placing a block on contiguous wires. Invalid placements
return identity; every circuit in the results below has valid placements. -/
noncomputable def placeBlock {r : ℕ} (n offset : ℕ)
    (A : Matrix (Qubits r) (Qubits r) ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  if h : offset + r ≤ n then
    embedOp A ⟨(fun i => ⟨offset + i.val, by omega⟩),
      by
        intro i j hij
        have hval := congrArg Fin.val hij
        change offset + i.val = offset + j.val at hval
        exact Fin.ext (Nat.add_left_cancel hval)⟩
  else 1

/-- PDF pp.9,19: the matrix specified by one placed module. -/
noncomputable def BlockStep.matrix (n : ℕ) : BlockStep → Matrix (Qubits n) (Qubits n) ℂ
  | .fourier offset width => placeBlock n offset (qftQubits width)
  | .phaseSwap offset halfWidth phaseIndex => placeBlock n offset (cpSwap halfWidth phaseIndex)
  | .swap offset halfWidth => placeBlock n offset (blockSwap halfWidth)
  | .truncatedPhaseSwap offset halfWidth phaseIndex cutoff =>
      placeBlock n offset (truncatedCpSwap halfWidth phaseIndex cutoff)

/-- PDF pp.9,19: chronological circuit semantics, retaining the full
permutation and phase. No target QFT is used in this definition. -/
noncomputable def blockCircuitMatrix (n : ℕ) (c : List BlockStep) :
    Matrix (Qubits n) (Qubits n) ℂ := (c.map (BlockStep.matrix n)).reverse.prod

/-- PDF p.9, Fig.7: process one more input block. Its successive exchanges
with the processed blocks have types t,t-1,...,1, followed by QFT on the
new leading block. -/
def qftInsertion (m t : ℕ) : List BlockStep :=
  ((List.range t).reverse.map fun s => BlockStep.phaseSwap (s * m) m (s + 1)) ++
    [.fourier 0 m]

/-- PDF p.9, Fig.7: the explicit scalable QFT circuit, starting with the
first m-wire QFT and inserting successive input blocks in chronological order. -/
def qftAssembly (m k : ℕ) : List BlockStep :=
  (List.range k).flatMap (qftInsertion m)

/-- PDF p.9: number of actual Fourier block occurrences. -/
def fourierCount (c : List BlockStep) : ℕ :=
  c.countP fun s => match s with | .fourier _ _ => true | _ => false

/-- PDF p.9: number of actual phase-swap occurrences of a given type. -/
def phaseCount (j : ℕ) (c : List BlockStep) : ℕ :=
  c.countP fun s => match s with | .phaseSwap _ _ t => decide (t = j) | _ => false

/-- PDF pp.9,19: total number of phase-swap module occurrences. -/
def phaseTotal (c : List BlockStep) : ℕ :=
  c.countP fun s => match s with | .phaseSwap _ _ _ => true | _ => false

example : firstHalf (![true, false] : Qubits 2) = ![true] := by
  funext i; fin_cases i; rfl

example : secondHalf (![true, false] : Qubits 2) = ![false] := by
  funext i; fin_cases i; rfl

example : exchangeHalves (m := 1) (![true, false] : Qubits 2) = ![false, true] := by
  funext i; fin_cases i <;> rfl

example (m : ℕ) : qftAssembly m 0 = [] := rfl

example (m : ℕ) : qftInsertion m 0 = [.fourier 0 m] := rfl

example : fourierCount [.fourier 0 2, .phaseSwap 0 2 1] = 1 := by decide

example : phaseCount 1 [.fourier 0 2, .phaseSwap 0 2 1] = 1 := by decide

example : phaseTotal [.fourier 0 2, .phaseSwap 0 2 1] = 1 := by decide

example (n : ℕ) : blockCircuitMatrix n [] = 1 := rfl

example (n : ℕ) : BlockStep.matrix n (.swap 0 1) = placeBlock n 0 (blockSwap 1) := rfl

example (n : ℕ) (r : ℕ) (A : Matrix (Qubits r) (Qubits r) ℂ)
    (h : n < r) : placeBlock n 0 A = 1 := by simp [placeBlock, Nat.not_le.mpr h]

example (m j : ℕ) (x : Qubits (2 * m)) :
    cpSwap m j (exchangeHalves x) x =
      Complex.exp (2 * Real.pi * Complex.I *
        (bitsToNat (firstHalf x) * bitsToNat (secondHalf x) : ℕ) /
          (2 : ℂ) ^ ((j + 1) * m)) := by simp [cpSwap]

example (m : ℕ) (x : Qubits (2 * m)) : blockSwap m (exchangeHalves x) x = 1 :=
  if_pos rfl

/-- PDF p.19, Fig.16: resolve a phase-swap on two 2h-bit blocks into four
phase-swaps on pairs of h-bit blocks, preserving chronological order. -/
def halfBlockExpansion (s : BlockStep) : List BlockStep :=
  match s with
  | .phaseSwap offset width j =>
      let h := width / 2
      [.phaseSwap (offset + h) h (2 * j),
       .phaseSwap offset h (2 * j - 1),
       .phaseSwap (offset + 2 * h) h (2 * j + 1),
       .phaseSwap (offset + h) h (2 * j)]
  | _ => [s]

/-- PDF p.19, Appendix A: the explicit variant-II half-block circuit. -/
def qftAssemblyII (m k : ℕ) : List BlockStep :=
  (qftAssembly m k).flatMap halfBlockExpansion

example : halfBlockExpansion (.phaseSwap 0 2 1) =
    [.phaseSwap 1 1 2, .phaseSwap 0 1 1,
      .phaseSwap 2 1 3, .phaseSwap 1 1 2] := rfl

example (m : ℕ) : qftAssemblyII m 0 = [] := rfl

/-- PDF p.10: replace each phase module by its strict-cutoff version.
If even its largest pair phase is deleted, the resulting module is a pure
block swap. Fourier blocks and already specified swap modules are retained. -/
def truncateBlockStep (cutoff : ℕ) (s : BlockStep) : BlockStep :=
  match s with
  | .phaseSwap offset width j =>
      if cutoff < (j - 1) * width + 1 then .swap offset width
      else .truncatedPhaseSwap offset width j cutoff
  | _ => s

/-- PDF p.10, Eq.(27): the actual approximating block circuit obtained
by truncating phase rotations in the Fig.7 assembly. -/
def truncatedQftAssembly (m k cutoff : ℕ) : List BlockStep :=
  (qftAssembly m k).map (truncateBlockStep cutoff)

example : truncateBlockStep 10 (.phaseSwap 0 5 3) = .swap 0 5 := rfl

example : truncateBlockStep 10 (.phaseSwap 0 5 2) = .truncatedPhaseSwap 0 5 2 10 := rfl

example (m cutoff : ℕ) : truncatedQftAssembly m 0 cutoff = [] := rfl

/-- PDF pp.5,10, Eqs. (26)-(27): product of occurrence fidelities of an
actual block list, times relaxation for its assigned elapsed duration. -/
noncomputable def blockQuality (Fq : ℝ) (Fc : ℕ → ℝ) (T TR : ℝ)
    (c : List BlockStep) : ℝ :=
  quality ((c.map fun s => match s with
    | .fourier _ _ => Fq
    | .phaseSwap _ _ j => Fc j
    | .truncatedPhaseSwap _ _ j _ => Fc j
    | .swap _ _ => Fc 3).prod) T TR

example (Fq : ℝ) (Fc : ℕ → ℝ) (TR : ℝ) : blockQuality Fq Fc 0 TR [] = 1 := by
  simp [blockQuality, quality]

/-- PDF p.19, Fig.17: an adjacent phase rotation followed by SWAP, or just
SWAP when the indicated rotation is deleted. -/
def panelStep (offset anglePower cutoff : ℕ) : BlockStep :=
  if anglePower ≤ cutoff then .phaseSwap offset 1 anglePower else .swap offset 1

/-- PDF p.19: panel (a), all 25 crossings, with angles pi/2 through pi/512.
Each next second-block bit moves left across the five first-block bits. -/
def panelA : List BlockStep :=
  (List.range 5).flatMap fun b =>
    (List.range 5).reverse.map fun a => .phaseSwap (a + b) 1 (1 + a + b)

/-- PDF p.19: panel (b), retaining precisely the triangular set a+b<=4,
whose angles are pi/64 through pi/1024. -/
def panelB : List BlockStep :=
  (List.range 5).flatMap fun b =>
    (List.range 5).reverse.map fun a => panelStep (a + b) (6 + a + b) 10

/-- PDF p.19: panel (c), the block exchange after every phase is deleted. -/
def panelC : List BlockStep :=
  (List.range 5).flatMap fun b =>
    (List.range 5).reverse.map fun a => .swap (a + b) 1

example : panelStep 0 10 10 = .phaseSwap 0 1 10 := rfl

example : panelStep 0 11 10 = .swap 0 1 := rfl

example : panelA.length = 25 := by decide

example : panelB.length = 25 := by decide

example : panelC.length = 25 := by decide

example (m j cutoff : ℕ) (x : Qubits (2 * m)) :
    truncatedCpSwap m j cutoff (exchangeHalves x) x =
      Complex.exp (Complex.I * (∑ a : Fin m, ∑ b : Fin m,
        if firstHalf x a && secondHalf x b then
          if (j - 1) * m + 1 + a.val + b.val ≤ cutoff then
            Real.pi / (2 : ℝ) ^ ((j - 1) * m + 1 + a.val + b.val)
          else 0
        else 0 : ℝ)) := by simp [truncatedCpSwap]

/-- PDF p.13, Eq. (35): fitted interior-block cost, with the printed
regression decimals treated as exact rationals defining this surrogate. -/
noncomputable def fittedInteriorCost (k m : ℕ) : ℝ :=
  (13 * (k : ℝ) - 8) * (((m : ℝ) + 2) * (215 / 100) - 448 / 100) +
    (if m = 1 then 0 else 1) * (13 * (k : ℝ) + 3) *
      ((m : ℝ) * (69 / 100) + 6 / 100)

example (k : ℕ) : fittedInteriorCost k 1 = (13 * (k : ℝ) - 8) * (197 / 100) := by
  norm_num [fittedInteriorCost]

/-- PDF p.13, Eq. (36): the printed transposed bidiagonal array, as a
column-vector matrix. The lower off-diagonal is one. -/
def jordanMatrix (R : Type*) [Zero R] [One R] (ell : ℕ) :
    Matrix (Fin (ell + 1)) (Fin (ell + 1)) R :=
  fun i j => if i.val = j.val ∨ i.val = j.val + 1 then 1 else 0

/-- PDF p.13, Eq. (38): identity plus the bottom-left endpoint entry. -/
def endpointMatrix (ell : ℕ) : Matrix (Fin (ell + 1)) (Fin (ell + 1)) (ZMod 2) :=
  (1 : Matrix (Fin (ell + 1)) (Fin (ell + 1)) (ZMod 2)) +
    Matrix.of (fun i j => if i.val = ell ∧ j.val = 0 then 1 else 0)

/-- PDF p.13, Fig.12: CNOT on designated distinct wires, acting on every
basis word, including arbitrary values of all intermediate wires. -/
def bitCnot {n : ℕ} (control target : Fin n) (x : Qubits n) : Qubits n :=
  fun i => if i = target then xor (x i) (x control) else x i

/-- PDF p.13, Fig.12: ascending neighboring CNOT sweep. -/
def ascendingSweep (ell : ℕ) (x : Qubits (ell + 1)) : Qubits (ell + 1) :=
  (List.ofFn (fun i : Fin ell =>
    ((⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩) : Fin (ell + 1) × Fin (ell + 1)))).foldl
      (fun y ct => bitCnot ct.1 ct.2 y) x

/-- PDF p.13, Fig.12: the opposite neighboring CNOT sweep. The reverse
chronological list implements I plus the lower one-step shift. -/
def descendingSweep (ell : ℕ) (x : Qubits (ell + 1)) : Qubits (ell + 1) :=
  (List.ofFn (fun i : Fin ell =>
    ((⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩) : Fin (ell + 1) × Fin (ell + 1)))).reverse.foldl
      (fun y ct => bitCnot ct.1 ct.2 y) x

/-- PDF p.13, Fig.12: the endpoint CNOT, preserving every intermediate bit. -/
def endpointCnot (ell : ℕ) (x : Qubits (ell + 1)) : Qubits (ell + 1) :=
  bitCnot ⟨0, by omega⟩ ⟨ell, by omega⟩ x

example : jordanMatrix ℕ 0 = 1 := by
  ext i j; fin_cases i; fin_cases j; rfl

example (ell : ℕ) (i j : Fin (ell + 1)) :
    endpointMatrix ell i j = (1 : Matrix (Fin (ell + 1)) (Fin (ell + 1)) (ZMod 2)) i j +
      (if i.val = ell ∧ j.val = 0 then 1 else 0) := by
  exact Matrix.add_apply _ _ i j

example {n : ℕ} (c t : Fin n) (x : Qubits n) :
    bitCnot c t x t = xor (x t) (x c) := by simp [bitCnot]

example (x : Qubits 1) : ascendingSweep 0 x = x := rfl

example (x : Qubits 1) : descendingSweep 0 x = x := rfl

example (ell : ℕ) (x : Qubits (ell + 1)) :
    endpointCnot ell x = bitCnot ⟨0, by omega⟩ ⟨ell, by omega⟩ x := rfl

end QAlgorithms.Papers.Independent.Intakethird100.P39


