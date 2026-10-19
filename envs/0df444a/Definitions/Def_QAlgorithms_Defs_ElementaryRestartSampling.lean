-- Prove2me | Definitions.Def_QAlgorithms_Defs_ElementaryRestartSampling
-- name    : QAlgorithms_Defs_ElementaryRestartSampling
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:07.578797+00:00
-- url     : https://prove2.me/theorems/9ff9ca20-ce01-41f3-a34e-8b3f2efc1dc7
-- title:
--   ElementaryRestartSampling
-- statement:
--   ElementaryRestartSampling
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ElementaryRestartSampling.lean

import Definitions.Def_QAlgorithms_Defs_JointLowRankGibbsData
import Definitions.Def_QAlgorithms_Defs_CircuitResources
import Definitions.Def_QAlgorithms_Defs_LocCircuit
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

open scoped Matrix ENNReal
namespace QAlgorithms.LowRankGibbs

/-- Implementation helper; source: arxiv-1710.02581v3 PDF p.26. -/
inductive SamplingInstruction (a : Fin 2 → ℕ) (N : ℕ) where
  | halt
  | gate (g : GateApp oneTwoQubitGateSet N) (next : ℕ)
  | query (k : Fin 2) (adjoint : Bool) (wires : Fin (a k) ↪ Fin N) (next : ℕ)
  | measure (q : Fin N) (next : Bool → ℕ)
  | prepare (q : Fin N) (next : ℕ)
  | draw (size : ℕ) (weights : Fin size → ℝ) (valid : Learning.IsDistribution weights)
      (next : Fin size → ℕ)

/-- Operational adaptive sampler with ordinary one or two-qubit gates, calls/adjoints to the two quantum input oracles, standard measurements, fresh preparation/discard, classical random choices and repeat-until-success control. Public construction fixed before hidden PSD matrices/purifications/oracle implementations. Count actual elementary gates and calls under the paper's classically addressed sampling convention; derive density-copy simulation through preparation calls. Do not grant arbitrary hidden-matrix-dependent known gates, free arbitrary channels, or automatically controlled black-box oracles. Source: arxiv-1710.02581v3 PDF p.26; arxiv-1710.02581v3 PDF p.30; arxiv-1710.02581v3 PDF p.33; arxiv-1710.02581v3 PDF p.39. -/
structure SamplingProgram (a : Fin 2 → ℕ) (N n w : ℕ) where
  entry : ℕ
  instruction : ℕ → List ℕ → SamplingInstruction a N
  output_positive : 0 < n
  layout : Qubits N ≃ Qubits (Nat.clog 2 n) × Fin w

/-- Implementation helper; source: arxiv-1710.02581v3 PDF p.26. -/
structure Configuration (N : ℕ) where
  pc : ℕ
  record : List ℕ
  rho : Matrix (Qubits N) (Qubits N) ℂ
  cost : Fin 3 → ℕ

/-- Operational transition relation/law for known elementary gates, plain D.1/D.2 calls or adjoints, preparation/reset, discard, standard measurement and measured-data finite classical choices; update actual per-resource counters. Source: arxiv-1710.02581v3 PDF p.26; arxiv-1710.02581v3 PDF p.30; arxiv-1710.02581v3 PDF p.33; arxiv-1710.02581v3 PDF p.39. -/
def samplingTransitions {a : Fin 2 → ℕ} {N n w : ℕ} (P : SamplingProgram a N n w)
    (O : (k : Fin 2) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (s : Configuration N) : List (Configuration N) :=
  let advance := fun pc rho record cost => (⟨pc,record,rho,s.cost+cost⟩ : Configuration N)
  match P.instruction s.pc s.record with
  | .halt => []
  | .gate g next => [advance next (conjSuperop (embedOp g.gate.mat g.wires) s.rho) s.record (Pi.single 2 1)]
  | .query k adj wires next => [advance next
      (conjSuperop (embedOp (if adj then star (O k) else O k) wires) s.rho) s.record
      (Pi.single k.castSucc 1)]
  | .measure q next => [false,true].map fun b => advance (next b)
      (conjSuperop (qubitOp1 (measProj b) q) s.rho) (s.record ++ [if b then 1 else 0]) (Pi.single 2 1)
  | .prepare q next => [advance next (krausApply (fun b : Bool => qubitOp1 (resetKraus b) q) s.rho)
      s.record (Pi.single 2 1)]
  | .draw size weights _ next => (List.finRange size).map fun i =>
      advance (next i) ((weights i : ℂ) • s.rho) (s.record ++ [i.val]) 0

/-- Implementation helper; source: arxiv-1710.02581v3 PDF p.26. -/
def samplingFrontier {a : Fin 2 → ℕ} {N n w : ℕ} (P : SamplingProgram a N n w)
    (O : (k : Fin 2) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) : ℕ → List (Configuration N)
  | 0 => [⟨P.entry,[],pureDensity (zeroKet N),0⟩]
  | t+1 => (samplingFrontier P O t).flatMap (samplingTransitions P O)

/-- Computed halting branch subnormalized densities and structural counters at each execution time/classical transcript. Halting branches are counted once, not kept in future nonterminal frontiers. Source: arxiv-1710.02581v3 PDF p.26; arxiv-1710.02581v3 PDF p.33; arxiv-1710.02581v3 PDF p.38. -/
def terminalBranches {a : Fin 2 → ℕ} {N n w : ℕ} (P : SamplingProgram a N n w)
    (O : (k : Fin 2) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) (t : ℕ) : List (Configuration N) :=
  (samplingFrontier P O t).filter fun s => match P.instruction s.pc s.record with
    | .halt => true | _ => false

/-- ENNReal sum of nonnegative traces of all terminal branches; mass one expresses almost-sure termination, not a postselection assumption. Source: arxiv-1710.02581v3 PDF p.26; arxiv-1710.02581v3 PDF p.33; arxiv-1710.02581v3 PDF p.38. -/
def terminationMass {a : Fin 2 → ℕ} {N n w : ℕ} (P : SamplingProgram a N n w)
    (O : (k : Fin 2) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) : ℝ≥0∞ :=
  ∑' t, ((terminalBranches P O t).map fun s => ENNReal.ofReal s.rho.trace.re).sum

/-- Decode the padded output register and trace out workspace. Unused binary labels are discarded into the logical zero state; on the encoded physical subspace this is the exact partial trace. Source: arxiv-1710.02581v3 PDF p.26. -/
def outputTerm {a : Fin 2 → ℕ} {N n w : ℕ} (P : SamplingProgram a N n w)
    (O : (k : Fin 2) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) (t : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  let J := finiteRegisterEmbedding n
  ((terminalBranches P O t).map fun s =>
    let X := traceRight (s.rho.submatrix P.layout.symm P.layout.symm)
    Jᴴ * X * J + (X - J * Jᴴ * X).trace • pureDensity (ket ⟨0, P.output_positive⟩)).sum

/-- Unconditional sum of terminal branch densities after output decoding/partial trace. Carry convergence/summability before using a matrix tsum; neither renormalize success branches nor use default-zero divergent output. Source: arxiv-1710.02581v3 PDF p.26; arxiv-1710.02581v3 PDF p.33; arxiv-1710.02581v3 PDF p.38. -/
def outputDensity {a : Fin 2 → ℕ} {N n w : ℕ} (P : SamplingProgram a N n w)
    (O : (k : Fin 2) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (_convergent : Summable (outputTerm P O)) : Matrix (Fin n) (Fin n) ℂ := ∑' t, outputTerm P O t

/-- For each gate/D.1/D.2 resource, sum terminal branch probability times its ACTUAL counter in ENNReal; assign infinity if termination mass is not one. Source: arxiv-1710.02581v3 PDF p.26; arxiv-1710.02581v3 PDF p.33; arxiv-1710.02581v3 PDF p.38. -/
def expectedResources {a : Fin 2 → ℕ} {N n w : ℕ} (P : SamplingProgram a N n w)
    (O : (k : Fin 2) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) (resource : Fin 3) : ℝ≥0∞ :=
  if terminationMass P O = 1 then ∑' t,
    ((terminalBranches P O t).map fun s => ENNReal.ofReal s.rho.trace.re*s.cost resource).sum
  else ⊤

example {a : Fin 2 → ℕ} {N n w : ℕ} (P : SamplingProgram a N n w)
    (O : (k : Fin 2) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (h : terminationMass P O ≠ 1) (j : Fin 3) : expectedResources P O j = ⊤ := by
  simp [expectedResources,h]

example : Nonempty (SamplingProgram (fun _ : Fin 2 => 0) 2 3 1) := by
  refine ⟨⟨0, (fun _ _ => .halt), (by decide), ?_⟩⟩
  simpa only [show Nat.clog 2 3 = 2 by decide] using
    (Equiv.prodUnique (Qubits 2) (Fin 1)).symm

end QAlgorithms.LowRankGibbs


