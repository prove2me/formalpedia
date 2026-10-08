-- Prove2me | Definitions.Def_VidalHGS_Elitism_SurvivorSelection
-- name    : VidalHGS_Elitism_SurvivorSelection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:24:14.74857+00:00
-- url     : https://prove2.me/theorems/f51e90e4-f710-40ba-b002-5c9825e1a2a9
-- title:
--   (7) and Section 4.6 — normalized ranks, Biased Fitness, clones, the set X and the survivor-selection procedure
-- statement:
--   This file sets up the population-management objects of the hybrid genetic algorithm HGSADC of Vidal, Crainic, Gendreau, Lahrichi and Rei. Only one subpopulation is considered; no routing object is involved.
--
--   Individuals are elements of a type $\alpha$ with decidable equality, and a (sub)population is a finite set $P \subseteq \alpha$ with $\mathit{nbIndiv} = |P|$ members. Each individual $I$ carries:
--
--   1. a penalized cost $c(I) \in \mathbb{R}$, its **fitness** (lower is better);
--   2. a pairwise distance $\delta(I_1, I_2) \in \mathbb{R}$ between individuals (the paper's $\delta_H$, equation (6));
--   3. a **diversity contribution** $\Delta_P(I) \in \mathbb{R}$, which depends on the current population $P$ (higher is better; the paper's equation (5) is one instance).
--
--   **Normalized ranks.** Relative to the current population $P$,
--   $$\mathit{fit}_P(I) = \frac{\#\{J \in P : c(J) < c(I)\}}{|P| - 1}, \qquad \mathit{dc}_P(I) = \frac{\#\{J \in P : \Delta_P(I) < \Delta_P(J)\}}{|P| - 1},$$
--   so the best individual has rank $0$ and, when the values are pairwise distinct, the worst has rank $1$.
--
--   **Biased Fitness** (equation (7)), for a parameter $\mathit{nbElit} \in \mathbb{N}$:
--   $$BF_P(I) = \mathit{fit}_P(I) + \Bigl(1 - \frac{\mathit{nbElit}}{|P| - 1}\Bigr) \times \mathit{dc}_P(I).$$
--
--   **Clones and the set $X$.** An individual $I$ is a *clone* in $P$ if some other $J \in P$, $J \neq I$, has $\delta(J, I) = 0$ or $c(J) = c(I)$. Given the current best solution $\mathit{best}$ (not required to lie in $P$),
--   $$X(P) = \{ I \in P : I \neq \mathit{best} \text{ and } I \text{ is a clone in } P\}.$$
--
--   **Survivor selection.** One removal step takes $P$ to $Q = P \setminus \{I\}$, where, with $X$, the ranks and $BF$ all computed on $P$: if $X(P) \neq \emptyset$, then $I \in X(P)$ has maximum $BF_P$ over $X(P)$; otherwise $I \in P$ has maximum $BF_P$ over $P$. The procedure performs $\lambda$ such steps in succession, recomputing everything on the current population each time ("Update the distance measures and $X$, and repeat"). Finally, $J$ is **among the $\mathit{nbElit}$ best individuals of $P$ in terms of fitness** when fewer than $\mathit{nbElit}$ members of $P$ have strictly smaller cost.
--
--   These objects are the vocabulary of the paper's elitism Proposition (Section 4.6) and of its proof.
--
--   **Formalization Note.** Ranks count strictly better individuals and divide by $|P| - 1$ in $\mathbb{R}$ (standard competition ranking; with distinct values it is exactly the paper's normalized rank, and ties share the better rank). The paper's "normalized ranks … where the best individual has rank 0 and the worst has rank 1" is made explicit this way. The diversity contribution $\Delta$ is an arbitrary real function of (population, individual), which covers the paper's (5). Ties in the maximum Biased Fitness are broken arbitrarily, so a removal step and a run of the procedure (`SurvivorRun n P R`, $n$ removals from $P$ ending at $R$) are relations, not functions.
-- source:
--   Vidal, Crainic, Gendreau, Lahrichi and Rei, A Hybrid Genetic Algorithm for Multi-Depot and Periodic Vehicle Routing Problems, CIRRELT-2010-34 (July 2010), pp. 11–12 and 16, Sections 4.3 and 4.6, (5)–(7) and the survivor-selection procedure

import Mathlib

namespace VidalHGS.Elitism

variable {α : Type*} [DecidableEq α]

/-- Normalized fitness rank `fit(I)` (Section 4.3, p. 12): the number of individuals of the
current population `P` with strictly smaller (better) cost `c`, divided by `nbIndiv − 1`, where
`nbIndiv = |P|`. The best individual has rank `0`; with pairwise distinct costs the worst has
rank `1`. Ties share the better rank. The division is in `ℝ`. -/
noncomputable def fitRank (c : α → ℝ) (P : Finset α) (I : α) : ℝ :=
  ((P.filter (fun J => c J < c I)).card : ℝ) / ((P.card : ℝ) - 1)

/-- Normalized diversity-contribution rank `dc(I)` (Section 4.3, p. 12): the number of
individuals of the current population `P` whose diversity contribution `Δ P J` is strictly
larger (better) than `Δ P I`, divided by `nbIndiv − 1`. The diversity contribution `Δ P`
is recomputed on the current population. -/
noncomputable def dcRank (Δ : Finset α → α → ℝ) (P : Finset α) (I : α) : ℝ :=
  ((P.filter (fun J => Δ P I < Δ P J)).card : ℝ) / ((P.card : ℝ) - 1)

/-- Biased Fitness (7), p. 12:
`BF(I) = fit(I) + (1 − nbElit / (nbIndiv − 1)) × dc(I)`, with `nbIndiv = |P|`. -/
noncomputable def biasedFitness (c : α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ)
    (P : Finset α) (I : α) : ℝ :=
  fitRank c P I + (1 - (nbElit : ℝ) / ((P.card : ℝ) - 1)) * dcRank Δ P I

/-- `I` is a clone in `P` (Section 4.6, p. 16): some other individual `J ∈ P`, `J ≠ I`, has the
same attributes as `I` (`δ J I = 0`) or the same fitness (`c J = c I`). -/
def IsClone (c : α → ℝ) (δ : α → α → ℝ) (P : Finset α) (I : α) : Prop :=
  ∃ J ∈ P, J ≠ I ∧ (δ J I = 0 ∨ c J = c I)

open Classical in
/-- The set `X` (Section 4.6, p. 16): the individuals of `P`, different from the current best
solution `best`, that have a clone in `P`. -/
noncomputable def cloneSet (c : α → ℝ) (δ : α → α → ℝ) (best : α) (P : Finset α) :
    Finset α :=
  P.filter (fun I => I ≠ best ∧ IsClone c δ P I)

/-- One removal of the survivor-selection procedure (Section 4.6, p. 16): `Q = P \ {I}` where,
with `X`, the ranks and the Biased Fitness all computed on the current population `P`,
* if `X ≠ ∅`, `I ∈ X` has maximum Biased Fitness over `X`;
* otherwise, `I ∈ P` has maximum Biased Fitness over `P`.
Ties in the maximum are broken arbitrarily. -/
def RemovalStep (c : α → ℝ) (δ : α → α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (best : α)
    (P Q : Finset α) : Prop :=
  ∃ I ∈ P, Q = P.erase I ∧
    ((cloneSet c δ best P).Nonempty →
      I ∈ cloneSet c δ best P ∧
        ∀ K ∈ cloneSet c δ best P, biasedFitness c Δ nbElit P K ≤ biasedFitness c Δ nbElit P I) ∧
    (cloneSet c δ best P = ∅ →
      ∀ K ∈ P, biasedFitness c Δ nbElit P K ≤ biasedFitness c Δ nbElit P I)

/-- `SurvivorRun … n P R`: the survivor-selection procedure removes `n` individuals from `P`,
one `RemovalStep` at a time ("Update the distance measures and X, and repeat"), ending at `R`. -/
inductive SurvivorRun (c : α → ℝ) (δ : α → α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ)
    (best : α) : ℕ → Finset α → Finset α → Prop
  | zero (P : Finset α) : SurvivorRun c δ Δ nbElit best 0 P P
  | succ {n : ℕ} {P Q R : Finset α} :
      RemovalStep c δ Δ nbElit best P Q → SurvivorRun c δ Δ nbElit best n Q R →
        SurvivorRun c δ Δ nbElit best (n + 1) P R

/-- `J` is among the `nbElit` best individuals of `P` in terms of fitness: fewer than `nbElit`
members of `P` have strictly smaller cost. -/
def IsElite (c : α → ℝ) (nbElit : ℕ) (P : Finset α) (J : α) : Prop :=
  (P.filter (fun K => c K < c J)).card < nbElit

end VidalHGS.Elitism


