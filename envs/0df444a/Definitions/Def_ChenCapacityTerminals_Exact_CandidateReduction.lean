-- Prove2me | Definitions.Def_ChenCapacityTerminals_Exact_CandidateReduction
-- name    : ChenCapacityTerminals_Exact_CandidateReduction
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T06:09:07.515801+00:00
-- url     : https://prove2.me/theorems/7b5455e2-1632-46e4-97b3-9a87aae7f658
-- title:
--   Two-orientation global candidate reduction with semantic witnesses
-- statement:
--   This intermediate realization has all guarantees of `HeadlineReduction`, with additional global-mode witnesses $X,Y$ for the rooted runs in $G$ and $G^{\mathrm{rev}}$. Its output is the indicator of the cheaper of $X$ and $V\setminus Y$. Rooted mode is unchanged. The extra witnesses expose exactly the semantic facts needed for the proved optimality of the two-orientation candidate.
-- source:
--   Thomas Y. Chen, STOC 2027 submission #665, proof of Theorem 1.1, global reversal wrapper, PDF p.10 (paper p.8); mission specifications for actual executions and traces. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=10

import Definitions.Def_ChenCapacityTerminals_Exact_RootedHeadline

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

/-- The output of the two-orientation wrapper together with its two intermediate shores. -/
def CandidateOutput {W : ℕ} (G : IntegerInput) (mode : Option ℕ) (m : ℤ → BitVec W) : Prop :=
  match mode with
  | some r => WordOutput G (some r) m
  | none =>
      ∃ X Y : Finset ℕ,
        OptimalRoot G.network 0 X ∧
        OptimalRoot (reverseNetwork G.network) 0 Y ∧
        ∀ v : ℕ, m ((inputWords G mode).length + v : ℕ) =
          BitVec.ofNat W (if v ∈
            (if cut G.network X ≤ cut G.network (G.network.vertices \ Y)
              then X else G.network.vertices \ Y) then 1 else 0)

/-- The same guarantees as the rooted headline, but in global mode the implementation
also supplies the semantic witnesses for the final comparison and its output vector. -/
def CandidateReduction (P : WordProgram) : Prop :=
  (∃ O, LawfulWordOracle O) ∧
  ∀ p q : ℕ, ∃ B : ℕ, ∃ C : ℝ, ∃ k : ℕ, 0 < B ∧ 0 < C ∧
    ∀ (G : IntegerInput) (mode : Option ℕ), G.Valid → ValidMode G mode →
      G.polynomial p q →
      ∀ W ≥ B * (Nat.log2 G.n + 1), ∀ O, LawfulWordOracle O →
        ∃ time trace out,
          WordRun P O 0 (TrulySubcubicAPSP.loadWords W (inputWords G mode)) time trace out ∧
          CandidateOutput G mode out ∧
          (flowVolume trace : ℝ) ≤ C * supportSize G * Real.sqrt G.n * polylog G.n G.arcs.length k ∧
          (time + (inputWords G mode).length + G.n : ℕ) ≤
            C * ((supportSize G : ℝ) * Real.sqrt G.n + G.n + G.arcs.length) *
            polylog G.n G.arcs.length k ∧
          (trace.length : ℝ) ≤ C * Real.sqrt G.n * polylog G.n G.arcs.length k ∧
          (∀ Q ∈ trace, (Q.graph.n : ℝ) ≤ C * G.n ∧
            (Q.graph.arcs.length : ℝ) ≤ C * supportSize G)

end ChenCapacityTerminals.Exact


