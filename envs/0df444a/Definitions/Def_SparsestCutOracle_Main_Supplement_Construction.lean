-- Prove2me | Definitions.Def_SparsestCutOracle_Main_Supplement_Construction
-- name    : SparsestCutOracle_Main_Supplement_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:47:26.074065+00:00
-- url     : https://prove2.me/theorems/64a5b545-48cc-4e82-8eae-250b35c929df
-- title:
--   Charged construction of a hierarchical congestion approximator
-- statement:
--   A construction program runs on the published randomized exact real RAM, with all instructions charged. Its input consists only of the vertex count, the edge-list size and endpoints in integer memory, the real capacities in edge order, and a real tradeoff parameter $\kappa$. It receives neither vertex weights nor a precomputed hierarchy or routing certificate. Its output is a finite height and $n$ integer cluster labels per level, decoded into partitions.
--
--   There are universal positive constants $c_1,c_2,C_q$. For every natural failure exponent $a$, one admissible program, a natural exponent $c$ and a positive time constant $C_t$ are chosen before any graph or $\kappa$. On every connected loopless $n\ge2$ vertex graph with real capacities at least one and $c_1/\ln n\le\kappa\le c_2$, it halts almost surely, its work is integrable, and
--   $$
--   \mathbb E[\mathrm{work}]\le C_t(m+n^{1+\kappa})(1+\ln W)(1+\ln n)^c.
--   $$
--   On a measurable set of tapes of probability at least $1-n^{-a}$, its decoded output is a complete hierarchy and a congestion approximator of quality at most
--   $$
--   C_q\ell\ell_2\sqrt{\ell/\kappa},\qquad\ell=1+\ln n,\quad\ell_2=1+\ln(1+\ln n).
--   $$
--   Here $m$ is the number of listed edges and $W$ their total capacity. The positive logarithms express the paper's asymptotic order at finite sizes, including $W=1$. This specification gives Theorem 2 computational content without a free algorithm instruction or a writable cost counter.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 4, Theorem 2; pp. 43–52, §8.2

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Supplement_Hierarchy

namespace SparsestCutOracle.Main.Supplement

/-- No vertex weights, certificates or oracle in the input: only the edge list and κ. -/
noncomputable def hierarchyInput {n : ℕ} (G : Graph n) (κ : ℝ) : State :=
  init (graphInts G) (G.map (fun e => (e.capacity : ℝ)) ++ [κ])

/-- Height is the integer in cell -1. Level i's n integer labels occupy cells
-2-i*n-v. Labels need not be consecutive. Empty labels are discarded. Invalid or
zero heights decode to an incomplete hierarchy and cannot satisfy the success predicate. -/
noncomputable def outputHierarchy (n : ℕ) (s : State) : Hierarchy n :=
  let L := (s.base.integerMemory (-1)).toNat
  (List.range L).map fun i =>
    Finset.univ.image fun v : Fin n =>
      Finset.univ.filter fun w : Fin n =>
        s.base.integerMemory (-2 - (i * n + v.val : ℕ)) =
        s.base.integerMemory (-2 - (i * n + w.val : ℕ))

noncomputable def hierarchyQuality (n : ℕ) (κ C : ℝ) : ℝ :=
  let ell := 1 + Real.log n
  let ell₂ := 1 + Real.log (1 + Real.log n)
  C * ell * ell₂ * Real.sqrt (ell / κ)

/-- Uniform construction on the published charged machine. Expected work includes
almost-sure halting and integrability. Success is a measurable set of random tapes. -/
def HierarchyConstruction : Prop :=
  ∃ c₁ c₂ Cq : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < Cq ∧
    ∀ a : ℕ, ∃ P : Program, Admissible P ∧
      ∃ (c : ℕ) (Ct : ℝ), 0 < Ct ∧
        ∀ (n : ℕ) (G : Graph n) (κ : ℝ),
          2 ≤ n → G.NoLoops → G.Connected → G.UnitLowerBound →
          c₁ / Real.log n ≤ κ → κ ≤ c₂ →
          ExpectedWork P (hierarchyInput G κ)
            (Ct * ((G.length : ℝ) + (n : ℝ) ^ (1 + κ)) *
              (1 + Real.log G.total) * (1 + Real.log n) ^ c) ∧
          HighProbability n a P (hierarchyInput G κ) (fun out =>
            Complete (outputHierarchy n out) ∧
            CongestionApproximator G (outputHierarchy n out) (hierarchyQuality n κ Cq))

end SparsestCutOracle.Main.Supplement


