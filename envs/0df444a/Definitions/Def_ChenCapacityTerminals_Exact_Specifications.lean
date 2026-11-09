-- Prove2me | Definitions.Def_ChenCapacityTerminals_Exact_Specifications
-- name    : ChenCapacityTerminals_Exact_Specifications
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:06.797022+00:00
-- url     : https://prove2.me/theorems/bac3646c-4049-4368-a100-2b0f7d4be04d
-- title:
--   Uniform terminal, pinning, batching and headline resource predicates
-- statement:
--   These predicates express the conclusions of the target theorems, using the independently defined network and execution semantics. They are not fields of an input model.
--
--   The terminal specification includes the exact additive mass term and expansion coefficient:
--   $$|P|\le C\frac nd\log(2+m)+\frac W{t+1},\qquad b(X)\le C_dt\frac{f(X)}L.$$
--   The unit-mass specialization is included explicitly. Pinning uses $t_d=\lceil Md/n\rceil$, preserves every surviving original cut and has rate $L/(C_dt_d)$. Batching bounds actual network volume by $C[M_D+k(1+U/\eta)(1+\log k)]$ and charges outside work up to a polylogarithmic factor.
--
--   The headline predicates require both modes on every valid integer input, including zero optima. They distinguish coalesced support size from raw input length. The flow reduction must satisfy total volume, outside-work, call-count, per-call vertex and per-call arc bounds for every lawful oracle tie policy. A separate ordinary scalar program must satisfy the unconditional running-time assertion. For each fixed polynomial input/capacity class and each $\varepsilon>0$, its bound is uniform in the instance; the program precedes all these quantifiers.
--
--   No scalar-value-only oracle or presumed optimal-cut input is used.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 1, 3, 7–10, PDF p. 2, 4, 8–11, Theorems 1.1, 2.1, 3.2; Corollary 4.1; §4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=2, 4, 8–11

import Definitions.Def_ChenCapacityTerminals_Exact_Construction
import Definitions.Def_ChenCapacityTerminals_Exact_ExactExecution

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

def terminalWords (G : IntegerInput) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ) : List ℤ :=
  [(G.n : ℤ), (G.arcs.length : ℤ), (r : ℤ), (d : ℤ), (t : ℤ), L.num, (L.den : ℤ)] ++
  arcWords G.arcs ++ (List.range G.n).map (fun v => (b v : ℤ))

def TerminalParameters (G : IntegerInput) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ) : Prop :=
  G.Valid ∧ Prepared G.network r ∧ 1 ≤ d ∧ d ≤ G.n ∧ 0 < L ∧ 1 ≤ t ∧
    0 < mass b G.network.vertices

def NumericClass (G : IntegerInput) (L : ℚ) (b : ℕ → ℕ) (t p q h : ℕ) : Prop :=
  G.polynomial p q ∧ t ≤ G.n ^ h ∧ mass b G.network.vertices ≤ G.n ^ h ∧
    L.num.natAbs ≤ G.n ^ h ∧ L.den ≤ G.n ^ h

def TerminalShape (C : ℝ) (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (c : Construction) : Prop :=
  let P := c.terminals G r ((L : ℝ) / (4 * d)) b t
  P ⊆ G.vertices \ {r} ∧
  (P.card : ℝ) ≤ C * ((G.vertices.card : ℝ) / d) * Real.log (2 + (G.arcs.length : ℝ)) +
    (mass b G.vertices : ℝ) / (t + 1 : ℕ) ∧
  (RootLowerBound G r L → ∀ X ⊆ G.vertices \ (P ∪ {r}),
    (mass b X : ℝ) ≤ (terminalCoefficient G.vertices.card d : ℝ) * t * cut G X / L) ∧
  ((∀ v ∈ G.vertices, b v = 1) → t = d → RootLowerBound G r L →
    ∀ X ⊆ G.vertices \ (P ∪ {r}),
      (X.card : ℝ) ≤ (terminalCoefficient G.vertices.card d : ℝ) * d * cut G X / L)

def TerminalRun (P : List TrulySubcubicAPSP.Instr) (W time : ℕ) (G : IntegerInput)
    (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ) : Prop :=
  ∃ ticks m c, TrulySubcubicAPSP.exec P ticks 0
    (TrulySubcubicAPSP.loadWords W (terminalWords G r d L b t)) = some (true, m) ∧
    LegalConstruction G.network r d L b t c ∧
    (∀ v < G.n, (m ((terminalWords G r d L b t).length + v : ℕ)).toNat ≤ 1) ∧
    wordShore m (terminalWords G r d L b t).length G.n =
      c.terminals G.network r ((L : ℝ) / (4 * d)) b t ∧
    time = ticks + (terminalWords G r d L b t).length + G.n

def TerminalTime (P : List TrulySubcubicAPSP.Instr) : Prop :=
  ∀ p q h : ℕ, ∃ B : ℕ, ∃ C : ℝ, ∃ k : ℕ, 0 < B ∧ 0 < C ∧
    ∀ (G : IntegerInput) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ),
      TerminalParameters G r d L b t → NumericClass G L b t p q h →
      ∀ W ≥ B * (Nat.log2 G.n + 1), ∃ time : ℕ,
        (time : ℝ) ≤ C * d * (G.n + G.arcs.length : ℕ) * polylog G.n G.arcs.length k ∧
        TerminalRun P W time G r d L b t

def PinningShape (C : ℝ) (k : ℕ) (G : Network) (r d : ℕ) (L : ℚ) (c : Construction) : Prop :=
  let b := indegreeMass G r
  let t := separatorThreshold G d
  let P := c.terminals G r ((L : ℝ) / (4 * d)) b t
  (P.card : ℝ) ≤ C * ((G.vertices.card : ℝ) / d) * polylog G.vertices.card G.arcs.length k ∧
  (RootLowerBound G r L → ∀ S ⊆ G.vertices \ (P ∪ {r}),
    Conditioned (restrict G r S) r b ((L : ℝ) /
      ((terminalCoefficient G.vertices.card d : ℝ) * t))) ∧
  (∀ S ⊆ G.vertices \ (P ∪ {r}), ∀ X ⊆ S, cut (restrict G r S) X = cut G X)

def PinningTime (P : List TrulySubcubicAPSP.Instr) : Prop :=
  ∀ p q h : ℕ, ∃ B : ℕ, ∃ C : ℝ, ∃ k : ℕ, 0 < B ∧ 0 < C ∧
    ∀ (G : IntegerInput) (r d : ℕ) (L : ℚ),
      TerminalParameters G r d L (indegreeMass G.network r) (separatorThreshold G.network d) →
      G.polynomial p q → L.num.natAbs ≤ G.n ^ h → L.den ≤ G.n ^ h →
      ∀ W ≥ B * (Nat.log2 G.n + 1), ∃ time : ℕ,
        (time : ℝ) ≤ C * d * (G.n + G.arcs.length : ℕ) * polylog G.n G.arcs.length k ∧
        TerminalRun P W time G r d L (indegreeMass G.network r) (separatorThreshold G.network d)

/-- Source-side coalescing overhead is charged separately from the reduced support size. -/
noncomputable def supportSize (G : IntegerInput) : ℕ :=
  G.n + (coalesce G.network G.n).arcs.length

def BatchParameters (G : Network) (r : ℕ) (b : ℕ → ℕ) (J : Finset ℕ) (U η : ℝ) : Prop :=
  G.Valid ∧ G.vertices = Finset.range G.vertices.card ∧ r ∈ G.vertices ∧
  (∀ v ∈ G.vertices \ {r}, 1 + indegree G v ≤ b v) ∧ Conditioned G r b η ∧
  J.Nonempty ∧ J ⊆ G.vertices \ {r} ∧ 0 < U ∧ 0 < η

noncomputable def batchBudget (G : Network) (J : Finset ℕ) (U η : ℝ) : ℝ :=
  G.size + J.card * (1 + U / η) * (1 + Real.log (J.card : ℝ))

def BatchAlgorithm (P : ExactProgram) (C : ℝ) (k B : ℕ) : Prop :=
  ∀ (G : Network) (r : ℕ) (b : ℕ → ℕ) (J : Finset ℕ) (U η : ℝ),
    BatchParameters G r b J U η →
    ∀ W ≥ B * (Nat.log2 (2 + G.size) + 1),
      ∀ O, LawfulExactOracle O → ∃ time trace out,
        ExactRun P O W 0 (batchingInput G r J U) time trace out ∧
        batchingOutput G r J U out ∧
        (exactVolume trace : ℝ) ≤ C * batchBudget G J U η ∧
        (time + 4 + 3 * G.arcs.length + 3 * J.card + G.vertices.card : ℕ) ≤
          C * batchBudget G J U η *
          (Real.log (2 + batchBudget G J U η)) ^ k

/-- The reduction program is uniform over all polynomial arc-count/capacity classes.
The quantified oracle must return a flow and a partition, and every lawful tie policy works. -/
def HeadlineReduction (P : WordProgram) : Prop :=
  (∃ O, LawfulWordOracle O) ∧
  ∀ p q : ℕ, ∃ B : ℕ, ∃ C : ℝ, ∃ k : ℕ, 0 < B ∧ 0 < C ∧
    ∀ (G : IntegerInput) (mode : Option ℕ), G.Valid → ValidMode G mode → G.polynomial p q →
      ∀ W ≥ B * (Nat.log2 G.n + 1), ∀ O, LawfulWordOracle O →
        ∃ time trace out,
          WordRun P O 0 (TrulySubcubicAPSP.loadWords W (inputWords G mode)) time trace out ∧
          WordOutput G mode out ∧
          (flowVolume trace : ℝ) ≤ C * supportSize G * Real.sqrt G.n * polylog G.n G.arcs.length k ∧
          (time + (inputWords G mode).length + G.n : ℕ) ≤
            C * ((supportSize G : ℝ) * Real.sqrt G.n + G.n + G.arcs.length) *
            polylog G.n G.arcs.length k ∧
          (trace.length : ℝ) ≤ C * Real.sqrt G.n * polylog G.n G.arcs.length k ∧
          (∀ Q ∈ trace, (Q.graph.n : ℝ) ≤ C * G.n ∧
            (Q.graph.arcs.length : ℝ) ≤ C * supportSize G)

/-- One plain program, before epsilon and before the instance; no fixed-pair primitive is a
hypothesis. Every epsilon has uniform constants on each polynomial-capacity/input class. -/
def HeadlineTime (P : List TrulySubcubicAPSP.Instr) : Prop :=
  ∀ p q : ℕ, ∃ B : ℕ, ∃ k : ℕ, 0 < B ∧
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (G : IntegerInput) (mode : Option ℕ), G.Valid → ValidMode G mode → G.polynomial p q →
        ∀ W ≥ B * (Nat.log2 G.n + 1), ∃ time : ℕ,
          (time : ℝ) ≤ C * ((supportSize G : ℝ) ^ (1 + ε) * Real.sqrt G.n +
            (G.n + G.arcs.length : ℕ) * polylog G.n G.arcs.length k) ∧
          PlainRun P W time G mode

end ChenCapacityTerminals.Exact


