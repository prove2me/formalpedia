-- Prove2me | Definitions.Def_DistributedMIS_LocalLowerBound_LocalPrograms
-- name    : DistributedMIS_LocalLowerBound_LocalPrograms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:38.226209+00:00
-- url     : https://prove2.me/theorems/0770d739-074d-463c-9d98-21d624a4628e
-- title:
--   Operational measurable LOCAL programs with infinite private tapes
-- statement:
--   A LOCAL program has an arbitrary state type, a common initialization function, a synchronous transition function and a selection-bit output function. Initialization sees n, fixed degree advice, the vertex identifier, its infinite private fair-bit tape, and its port-indexed neighbor identifiers. Each round supplies the neighboring states and both endpoint ports. All vertices use the same functions.
--
--   $$\mathbb P_n=\bigotimes_{v\in[n]}\operatorname{Bernoulli}(1/2)^{\otimes\mathbb N}.$$
--
--   Execution is defined by recursion for exactly T rounds. Legal finite inputs have arbitrary simple graphs, arbitrary bijective identifiers, and arbitrary legal port orderings. Success means independence and domination of every vertex simultaneously. Degree advice satisfies Δ≤Δ̂≤2Δ, including Δ̂=0 at Δ=0. Measurability concerns actual tape-dependent executions and contains no correctness assumption. Full-state communication represents arbitrary unbounded per-port messages, and the program itself is chosen after n.
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Theorem 1.1 and following clause, p. 3; §2.3, pp. 8–9; §3, pp. 9–10; Appendix A.2–A.3, pp. 33–34 (printed = PDF)

import Mathlib
open scoped ENNReal

noncomputable section

namespace DistributedMIS.LocalLowerBound

abbrev PrivateTape := ℕ → Bool

def fairBit : MeasureTheory.Measure Bool :=
  (1/2 : ℝ≥0∞) • MeasureTheory.Measure.dirac false +
  (1/2 : ℝ≥0∞) • MeasureTheory.Measure.dirac true

instance fairBit_isProbabilityMeasure : MeasureTheory.IsProbabilityMeasure fairBit := by
  constructor
  simp [fairBit, MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply, ENNReal.inv_two_add_inv_two]

def tapeMeasure : MeasureTheory.Measure PrivateTape :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => fairBit)

def privateTapes (n : ℕ) : MeasureTheory.Measure (Fin n → PrivateTape) :=
  MeasureTheory.Measure.pi (fun _ : Fin n => tapeMeasure)

/-- Full-state synchronous LOCAL program. All nodes use these same functions.
The initialization list consists of (local port, neighbor identifier).
Transitions receive (local port, sender port, sender state). -/
structure LocalProgram where
  State : Type
  initState : ℕ → ℕ → ℕ → PrivateTape → List (ℕ × ℕ) → State
  transition : ℕ → ℕ → ℕ → PrivateTape → State → List (ℕ × ℕ × State) → State
  select : ℕ → ℕ → ℕ → PrivateTape → State → Bool

def localState {V : Type} [DecidableEq V] (P : LocalProgram) (n advice : ℕ)
    (neighbors : V → List V) (ids : V → ℕ) (tapes : V → PrivateTape) : ℕ → V → P.State
  | 0, v => P.initState n advice (ids v) (tapes v)
      ((neighbors v).map (fun u => ((neighbors v).idxOf u, ids u)))
  | t+1, v => P.transition n advice (ids v) (tapes v)
      (localState P n advice neighbors ids tapes t v)
      ((neighbors v).map (fun u =>
        ((neighbors v).idxOf u, (neighbors u).idxOf v,
          localState P n advice neighbors ids tapes t u)))

def localOutput {V : Type} [DecidableEq V] (P : LocalProgram) (n advice T : ℕ)
    (neighbors : V → List V) (ids : V → ℕ) (tapes : V → PrivateTape) (v : V) : Bool :=
  P.select n advice (ids v) (tapes v) (localState P n advice neighbors ids tapes T v)

def LegalPorts {V : Type} [DecidableEq V] (G : SimpleGraph V) (neighbors : V → List V) : Prop :=
  ∀ v, (neighbors v).Nodup ∧ ∀ u, u ∈ neighbors v ↔ G.Adj v u

def IsMIS {V : Type} (G : SimpleGraph V) (out : V → Bool) : Prop :=
  (∀ u v, G.Adj u v → ¬ (out u = true ∧ out v = true)) ∧
  (∀ v, out v = true ∨ ∃ u, G.Adj v u ∧ out u = true)

def maximumDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.image (fun v => G.degree v)).sup id

def LegalAdvice {n : ℕ} (G : SimpleGraph (Fin n)) (advice : ℕ) : Prop :=
  maximumDegree G ≤ advice ∧ advice ≤ 2 * maximumDegree G

/-- Total measurable execution convention, also on repeated or malformed IDs.
This condition contains no correctness or round-complexity assertion. -/
def MeasurableProgram (P : LocalProgram) : Prop :=
  ∀ (m n advice T : ℕ) (neighbors : Fin m → List (Fin m)) (ids : Fin m → ℕ) (v : Fin m),
    Measurable (fun tapes : Fin m → PrivateTape =>
      localOutput P n advice T neighbors ids tapes v)

def successProbability (P : LocalProgram) (n advice T : ℕ)
    (G : SimpleGraph (Fin n)) (neighbors : Fin n → List (Fin n))
    (ids : Equiv.Perm (Fin n)) : ℝ :=
  (privateTapes n {tapes | IsMIS G
    (localOutput P n advice T neighbors (fun v => (ids v).val + 1) tapes)}).toReal

def CorrectAtAdvice (P : LocalProgram) (n advice T : ℕ) (σ : ℝ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) (neighbors : Fin n → List (Fin n)) (ids : Equiv.Perm (Fin n)),
    LegalPorts G neighbors → σ ≤ successProbability P n advice T G neighbors ids

def CorrectWithAdvice (P : LocalProgram) (n T : ℕ) (σ : ℝ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) (neighbors : Fin n → List (Fin n))
    (ids : Equiv.Perm (Fin n)) (advice : ℕ), LegalPorts G neighbors → LegalAdvice G advice →
      σ ≤ successProbability P n advice T G neighbors ids

end DistributedMIS.LocalLowerBound


