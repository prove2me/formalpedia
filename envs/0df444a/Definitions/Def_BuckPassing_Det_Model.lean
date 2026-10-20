-- Prove2me | Definitions.Def_BuckPassing_Det_Model
-- name    : BuckPassing_Det_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:29.645779+00:00
-- url     : https://prove2.me/theorems/2b1314e4-1b90-4659-95de-a63314db4f46
-- title:
--   The deterministic buck-passing game
-- statement:
--   Let $G=(V,E)$ be a finite directed graph without loops in which every vertex has at least one out-neighbor. Each player $i\in V$ chooses one out-neighbor $s_i$. The resulting profile $s$ defines a map $f_s(i)=s_i$. An initial vertex is drawn from a probability distribution $\mu$ on $V$, and the buck follows the orbit of $f_s$. The cost of player $i$ is the expected limiting fraction of times $t=1,\ldots,T$ at which the buck is at $i$:
--
--   $$c_i(s)=\sum_{j\in V}\mu_j\lim_{T\to\infty}\frac1T\sum_{t=1}^T\mathbf1\{f_s^t(j)=i\}. $$
--
--   A **prior-free Nash equilibrium** is one profile that is a Nash equilibrium for every initial probability distribution. Nash equilibria and potentials use the separate cost-game definitions.
--
--   The definition file also names each directed cycle of $f_s$, its basin or unicycle, the initial mass of that basin, the cycle indicator, and the real-valued function $\Psi(s)=\sum_C(|V|-|C|)$, with one summand for each distinct cycle. These common definitions support the cost identity, potential theorem, and prior-free existence theorem.
--
--   **Formalization Note** The cost uses a limit operator on each deterministic orbit; the equation (6) milestone states convergence for every orbit. The empty vertex type is allowed. The paper's $\mu$ is encoded as a nonnegative real vector summing to one. Classical decidability is used to form finite sets of periodic points.
-- source:
--   Cominetti, Quattropani, Scarsini, The Buck-Passing Game, arXiv:1808.03206v4, pp. 5–9, §2, §3, Definitions 1 and 3, equations (3)–(5), (10)

import Mathlib
import Definitions.Def_BuckPassing_Det_CostGame

namespace BuckPassing.Det

open Classical Finset Filter

/- The paper's finite loopless digraph, with every out-neighbourhood nonempty. -/
structure BPGraph (V : Type*) where
  Adj : V → V → Prop
  [dec : DecidableRel Adj]
  loopless : ∀ i, ¬ Adj i i
  outNonempty : ∀ i, ∃ j, Adj i j

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The choices available to player `i`, namely her out-neighbours. -/
abbrev Strat (G : BPGraph V) (i : V) : Type _ := {j : V // G.Adj i j}

/-- The functional digraph induced by a pure strategy profile. -/
def toMap {G : BPGraph V} (s : ∀ i, Strat G i) : V → V := fun i => (s i).1

/-- A probability distribution on the vertices. -/
def IsDistribution (mu : V → ℝ) : Prop :=
  (∀ i, 0 ≤ mu i) ∧ ∑ i, mu i = 1

/-- The Cesàro frequency, with times numbered from 1 as in equation (3). -/
noncomputable def freq (f : V → V) (j i : V) : ℝ :=
  limUnder atTop (fun T : ℕ =>
    (((Finset.Icc 1 T).filter (fun t => f^[t] j = i)).card : ℝ) / T)

/-- Equation (3): expectation of the long-run visit frequency over the initial draw. -/
noncomputable def cost (G : BPGraph V) (mu : V → ℝ) :
    V → (∀ i, Strat G i) → ℝ :=
  fun i s => ∑ j, mu j * freq (toMap s) j i

/-- The vertices of the cycle containing a periodic vertex. -/
noncomputable def cycleOf (f : V → V) (i : V) : Finset V :=
  univ.filter (fun j => ∃ t : ℕ, f^[t] i = j)

/-- The distinct directed cycles of a functional digraph. -/
noncomputable def cycles (f : V → V) : Finset (Finset V) :=
  (univ.filter (fun i => i ∈ Function.periodicPts f)).image (cycleOf f)

/-- The unicycle containing cycle `C`: vertices whose orbits eventually enter `C`. -/
noncomputable def basin (f : V → V) (C : Finset V) : Finset V :=
  univ.filter (fun j => ∃ t : ℕ, f^[t] j ∈ C)

/-- Equation (4): initial mass of a unicycle. -/
noncomputable def basinMass (mu : V → ℝ) (f : V → V) (C : Finset V) : ℝ :=
  ∑ j ∈ basin f C, mu j

/-- Equation (5): one on cycle vertices, zero on transient vertices. -/
noncomputable def delta (f : V → V) (i : V) : ℝ :=
  if i ∈ Function.periodicPts f then 1 else 0

/-- Equation (10), summed once per distinct cycle and subtracted in the reals. -/
noncomputable def Psi (G : BPGraph V) (s : ∀ i, Strat G i) : ℝ :=
  ∑ C ∈ cycles (toMap s), ((Fintype.card V : ℝ) - C.card)

/-- Definition 3: the same profile is a Nash equilibrium for every initial law. -/
def IsPFNE (G : BPGraph V) (s : ∀ i, Strat G i) : Prop :=
  ∀ mu : V → ℝ, IsDistribution mu → IsNash (cost G mu) s

end BuckPassing.Det


