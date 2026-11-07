-- Prove2me | Definitions.Def_ImpatientMatching_Input
-- name    : ImpatientMatching_Input
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:07.72991+00:00
-- url     : https://prove2.me/theorems/09273add-666e-4a08-a79d-452c51788fbc
-- title:
--   Rational matching inputs, their binary encoding, and the instance of a regime
-- statement:
--   A **matching input** consists of finite sets of supplier types and customer types, a bipartite compatibility graph between them, and positive rational arrival rates $\lambda_i$ and $\gamma_j$. Its total arrival rate is
--   $$\Lambda=\sum_i\lambda_i+\sum_j\gamma_j .$$
--   Inputs are encoded in binary, with self-delimiting natural numbers and rationals, since running time is measured in the binary input length.
--
--   Rewards are one on every compatible pair. In the **Finite-Finite** regime every agent has rate-one exponential patience. In the **Finite-Zero** regime suppliers have rate-one exponential patience, while a customer leaves at once if not matched on arrival. An input and a regime determine an instance of the published dynamic stochastic matching model: a compatible pair earns reward $1$, and any other pair, including two suppliers or two customers, earns $0$.
--
--   **Formalization Note** The published model superposes the independent Poisson streams into one marked stream of rate $\Lambda$, which has the same law. Unit rewards and patience are fixed by the regime, so they are not part of the encoded data.
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), §2.1, pp.6–7; §1.3, p.6

import Definitions.Def_DynStochMatching_Reward_Counts
import Definitions.Def_NSWApxHard_Reduction_CubicVC

open DynStochMatching.Reward

namespace ImpatientMatching

/-- The two hardness regimes of Yan–Varma, manuscript (sha256 7b1051b6…), §2.1, p.7.
`finiteFinite`: all supplier and customer types abandon with rate 1. `finiteZero`: all suppliers
abandon with rate 1 and all customers abandon if not matched as soon as they arrive. -/
inductive Regime
  | finiteFinite
  | finiteZero

/-- A rational matching input with unit rewards (Yan–Varma, manuscript (sha256 7b1051b6…), §2.1,
pp.6–7): supplier types `Fin nS`, customer types `Fin nC`, a bipartite compatibility graph `edge`,
and positive rational arrival rates.

**Formalization Note.** Unit rewards and the regime's patience are not data here, as they are
fixed by the regime in the hardness statements (p.7–8, "set all rewards to one"). -/
structure MatchInput where
  nS : ℕ
  nC : ℕ
  edge : Fin nS → Fin nC → Bool
  rateS : Fin nS → ℚ
  rateC : Fin nC → ℚ
  posS : ∀ i, 0 < rateS i
  posC : ∀ j, 0 < rateC j

/-- `Λ`, the total arrival rate (Yan–Varma, manuscript (sha256 7b1051b6…), §2.1, p.7). -/
noncomputable def totalRate (I : MatchInput) : ℝ :=
  ∑ i, (I.rateS i : ℝ) + ∑ j, (I.rateC j : ℝ)

/-- Self-delimiting binary code of a rational in lowest terms: the sign, the numerator's absolute
value and the denominator. It is injective on the rational's value. -/
def encRat (q : ℚ) : List Bool :=
  decide (0 ≤ q.num) :: (NSWApxHard.Reduction.natBits q.num.natAbs ++
    NSWApxHard.Reduction.natBits q.den)

/-- The binary encoding of an input (§1.3, p.6: running time is in the binary input length):
`nS`, `nC`, the adjacency bits row by row, then the rates. -/
def encInput (I : MatchInput) : List Bool :=
  NSWApxHard.Reduction.natBits I.nS ++ NSWApxHard.Reduction.natBits I.nC ++
    (List.ofFn fun i => List.ofFn fun j => I.edge i j).flatten ++
    (List.ofFn fun i => encRat (I.rateS i)).flatten ++
    (List.ofFn fun j => encRat (I.rateC j)).flatten

/-- The encoding of a promise-problem instance: an input and a rational threshold `b`. -/
def encPromise (p : MatchInput × ℚ) : List Bool :=
  encInput p.1 ++ encRat p.2

/-- Compatibility on the flat type index: supplier types are `Fin.castAdd`, customer types are
`Fin.natAdd`. Two suppliers or two customers are never compatible. -/
def compat (I : MatchInput) : Fin (I.nS + I.nC) → Fin (I.nS + I.nC) → Bool :=
  Fin.addCases
    (fun i => Fin.addCases (fun _ => false) (fun j => I.edge i j))
    (fun j => Fin.addCases (fun i => I.edge i j) (fun _ => false))

/-- The stochastic instance of an input in a regime (§2.1, pp.6–7): arrival rates are the input's,
suppliers have rate-one exponential patience, customers have rate-one exponential patience in
Finite-Finite and zero patience in Finite-Zero; a compatible pair earns reward one and any other
pair reward zero.

**Formalization Note.** Published `DynStochMatching.Reward.Instance` superposes the arrivals into
one marked Poisson stream of rate `Λ`, the same law as independent streams. The compatibility graph
of §2.1 is `reward ≠ 0`. -/
noncomputable def toInstance (r : Regime) (I : MatchInput) : Instance (I.nS + I.nC) where
  arrivalRate := Fin.addCases (fun i => (I.rateS i : ℝ)) (fun j => (I.rateC j : ℝ))
  positive := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) <;> simp
    · exact I.posS i
    · exact I.posC j
  lifetime := Fin.addCases (fun _ => Lifetime.exponential 1 one_pos)
    (fun _ => match r with
      | Regime.finiteFinite => Lifetime.exponential 1 one_pos
      | Regime.finiteZero => Lifetime.immediate)
  reward := fun a b => if compat I a b = true then 1 else 0
  symmetric := by
    intro a b
    have : compat I a b = compat I b a := by
      refine Fin.addCases (fun i => ?_) (fun j => ?_) a <;>
        refine Fin.addCases (fun i' => ?_) (fun j' => ?_) b <;> simp [compat]
    rw [this]

end ImpatientMatching


