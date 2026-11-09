-- Prove2me | Definitions.Def_MultiNashRepair_Generation
-- name    : MultiNashRepair_Generation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:29:16.753021+00:00
-- url     : https://prove2.me/theorems/18e3da3e-99a7-4581-a911-e6572533a42b
-- title:
--   Stored repair generations, column certificates (5.15), and the certificate law of Lemma 5.2
-- statement:
--   A **repair generation** records, for a repair made at an earlier iteration $s$, its base profile $x^{(s)}$, its mixed deviations $b^{(s)}_i$, its activation law $\gamma^{(s)}$, its intensity $t^{(s)}$ and its current common mass $A^{(s,k)}$. Its **activation odds** are $\alpha^{(s)}_i=t^{(s)}\gamma^{(s)}_i/(1-t^{(s)}\gamma^{(s)}_i)$ and its **original columns** are $d^{(s)}_{ij}(y_j)=d_{i,b^{(s)}_i}(x^{(s)}[j\leftarrow y_j])$ (5.14). A generation is **legal** if $x^{(s)}$ and $b^{(s)}$ are mixed, $\gamma^{(s)}$ is a probability vector with $0\le t^{(s)}\gamma^{(s)}_i<1$, and $A^{(s,k)}\ge0$.
--
--   A list of generations satisfies the **column certificate** with constant $L$ if for every generation, every player $j$ and every mixed $y_j$
--   $$\sum_{i\ne j}\gamma^{(s)}_i\,d^{(s)}_{ij}(y_j)\le L/m\qquad(5.15).$$
--
--   It satisfies the **certificate law** at a profile $x$ if, for every pure profile $a$,
--   $$\sum_s\sum_i A^{(s,k)}\alpha^{(s)}_i\,\Pr_{x^{(s)}[i\leftarrow b^{(s)}_i]}(a)\le\Pr_x(a),$$
--   and, for every player $j$ and mixed $y_j$,
--   $$\sum_s\sum_{i\ne j}A^{(s,k)}\alpha^{(s)}_i\,\Pr_{x^{(s)}[i\leftarrow b^{(s)}_i,\,j\leftarrow y_j]}(a)\le\Pr_{x[j\leftarrow y_j]}(a).$$
--
--   **Formalization Note** The certificate law is Lemma 5.2 (C1), (C2), (C6) in measure form: disjoint certificate events with masses $A\alpha_i$ and these conditional laws exist exactly when the dominations hold (split the atoms of the finite pure-profile space). Generations are analysis-only data that the algorithm never reads.
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), §5.3, (5.13)–(5.15), pp.19, 23; Lemma 5.2 (C1), (C2), (C6), pp.19–20

import Mathlib
import Definitions.Def_MultiNashRepair_Regret

open NashAmplification.Filtering (Mixed Utility Tuple)
open Finset

noncomputable section

namespace MultiNashRepair

/-- **A stored repair generation** (Tang, Ding, Fang, arXiv:2611.06076, §5.3 pp.18–19,
(5.13)–(5.15)): the frozen record of the repair made at iteration `s` — its base profile
`x^{(s)}`, its mixed deviations `b^{(s)}_i`, its activation law `γ^{(s)}`, its intensity
`t^{(s)}` — together with the retained common mass `A^{(s,k)}`.

**Formalization Note.** Generations are analysis-only ("ghost") data: the algorithm never reads
them; the run relation only updates them. -/
structure Gen {m : ℕ} (n : Fin m → ℕ) where
  /-- the base profile `x^{(s)}` -/
  base : Mixed n
  /-- the mixed deviations `b^{(s)}_i` -/
  dev : Mixed n
  /-- the activation law `γ^{(s)}` -/
  γ : Fin m → ℝ
  /-- the activation intensity `t^{(s)}` -/
  t : ℝ
  /-- the retained common mass `A^{(s,k)}` -/
  A : ℝ

variable {m : ℕ} {n : Fin m → ℕ}

namespace Gen

/-- The activation odds `α^{(s)}_i = t^{(s)} γ^{(s)}_i / (1 − t^{(s)} γ^{(s)}_i)` ((5.13), p.19). -/
def odds (g : Gen n) (i : Fin m) : ℝ :=
  g.t * g.γ i / (1 - g.t * g.γ i)

/-- The original column `d^{(s)}_{ij}(y_j) = d_{i, b^{(s)}_i}(x^{(s)}[j ← y_j])` ((5.14), p.23). -/
def col (u : Utility n) (g : Gen n) (i j : Fin m) (y : Fin (n j) → ℝ) : ℝ :=
  deficitMix u (Function.update g.base j y) i (g.dev i)

end Gen

/-- A generation is legal: its base profile is a mixed profile, its deviations are lotteries,
its activation law is a probability vector with `0 ≤ t γ_i < 1`, and its mass is nonnegative
(the legality assumptions of Lemma 5.2, p.19). -/
def GenLegal (g : Gen n) : Prop :=
  AGT.IsMixedProfile g.base ∧ AGT.IsMixedProfile g.dev ∧ AGT.IsLottery g.γ ∧
    (∀ i, 0 ≤ g.t * g.γ i ∧ g.t * g.γ i < 1) ∧ 0 ≤ g.A

/-- The historical column certificate (5.15)/(5.54): for every stored generation, every player
`j` and every mixed `y_j`, `Σ_{i ≠ j} γ^{(s)}_i d^{(s)}_{ij}(y_j) ≤ L/m` (pp.23, 40). -/
def ColumnBound (u : Utility n) (gs : List (Gen n)) (L : ℝ) : Prop :=
  ∀ g ∈ gs, ∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y →
    ∑ i ∈ univ.erase j, g.γ i * g.col u i j y ≤ L / m

/-- **The certificate law of Lemma 5.2, in measure form** (pp.19–20, (C1), (C2), (C6)).

(a) The law of `x` dominates, pointwise on pure profiles, the sum over stored generations `s`
and players `i` of the mass `A^{(s,k)} α^{(s)}_i` times the law of `x^{(s)}[i ← b^{(s)}_i]`.
(b) For every player `j` and mixed `y_j`, the law of `x[j ← y_j]` dominates the same sum over
`i ≠ j` with the laws `x^{(s)}[i ← b^{(s)}_i, j ← y_j]` (opponent overrides).

**Formalization Note.** On the finite pure-profile space, pairwise disjoint events `E_{s,i}` with
masses `A α_i` and conditional laws `x^{(s)}[i ← b_i]` give (a); keeping the same events under
the override `X_j ← Y_j` gives (b); and conversely each domination splits the atoms into disjoint
pieces with the stated laws. The paper's single augmented space serving every override at once is
replaced by one domination per override, which is what the proofs of Lemmas 5.3, 5.4 and 5.12
use. -/
def CertLaw (x : Mixed n) (gs : List (Gen n)) : Prop :=
  (∀ a : Tuple n,
      (gs.map fun g => ∑ i, g.A * g.odds i *
        AGT.profileProb (Function.update g.base i (g.dev i)) a).sum ≤ AGT.profileProb x a) ∧
    ∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y → ∀ a : Tuple n,
      (gs.map fun g => ∑ i ∈ univ.erase j, g.A * g.odds i *
        AGT.profileProb (Function.update (Function.update g.base i (g.dev i)) j y) a).sum
        ≤ AGT.profileProb (Function.update x j y) a

end MultiNashRepair


