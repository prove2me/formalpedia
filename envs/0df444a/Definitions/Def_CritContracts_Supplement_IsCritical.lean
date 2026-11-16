-- Prove2me | Definitions.Def_CritContracts_Supplement_IsCritical
-- name    : CritContracts_Supplement_IsCritical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:54:41.917992+00:00
-- url     : https://prove2.me/theorems/ae7056c9-4b1b-4f23-9b65-82d894678056
-- title:
--   Critical contracts, the equilibrium-selection optimum and the optimal equilibria $\mathrm{NE}^\star(\alpha)$
-- statement:
--   Fix an instance and write $\mathrm{NE}(\alpha)$ for the set of pure Nash equilibria of the game induced by the payment vector $\alpha$ and $u_P(\alpha,S)=(1-\sum_i\alpha_i)f(S)$ for the principal's utility.
--
--   1. A contract $\alpha\in[0,1]^n$ is **critical for** the profile $S$ if $S\in\mathrm{NE}(\alpha)$ and no contract $\alpha'\in[0,1]^n$ with $\alpha'\le\alpha$ coordinate-wise and $\alpha'\ne\alpha$ has $S\in\mathrm{NE}(\alpha')$ (Definition 2.3).
--   2. The **critical contracts of the instance** are the contracts in $[0,1]^n$ that are critical for some profile; "at most $K$ critical contracts in $[0,1]^n$" means that this set has at most $K$ elements.
--   3. The optimum of the **Equilibrium Selection Problem** at $\alpha$ (Definition 2.2) is $\mathrm{OPT}_{\mathrm{ES}}(\alpha)=\sup\{u_P(\alpha,S):S\in\mathrm{NE}(\alpha)\}$, a maximum over a finite set.
--   4. The answer of an **optimal equilibria query** (Definition 4.10) is the entire set
--   $$\mathrm{NE}^\star(\alpha)=\operatorname*{arg\,max}_{S\in\mathrm{NE}(\alpha)}u_P(\alpha,S),$$
--   ties included.
--
--   These notions state Theorems 3.9, 4.2 and 4.11.
--
--   **Formalization Note** The set of critical contracts is counted by its extended cardinality, so an infinite set would violate every finite bound (it is in fact always finite: each profile has at most one critical contract, Observation 3.11).
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Definition 2.2 and Definition 2.3, p.9 (PDF p.10); Observation 3.11, p.17; Definition 4.10, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_CritContracts_Model

set_option autoImplicit false

namespace CritContracts.Supplement

variable {ι T : Type} [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T]

/-- **Critical contracts** (Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial
Contracts*, STOC 2027 submission (manuscript sha256 430be35c…), Definition 2.3, p.9, PDF p.10): the contract
`α ∈ [0,1]^n` is critical for the profile `S` if it incentivizes `S` (`S ∈ NE(α)`) and is coordinate-wise minimal
among the contracts that incentivize `S`: no contract `α' ≤ α`, `α' ≠ α`, has `S ∈ NE(α')`. -/
def IsCritical (M : Model ι T) (α : ι → ℝ) (S : Finset T) : Prop :=
  IsContract α ∧ M.IsNE α S ∧ ∀ α' : ι → ℝ, IsContract α' → α' ≤ α → M.IsNE α' S → α' = α

/-- The set of **critical contracts of the instance** (Definition 2.3, p.9): the contracts `α ∈ [0,1]^n` that are
critical for some action profile. "At most `K` critical contracts in `[0,1]^n`" (Theorem 3.9, p.17) is
`(criticalContracts M).encard ≤ K`. -/
def criticalContracts (M : Model ι T) : Set (ι → ℝ) := {α | ∃ S, IsCritical M α S}

/-- The optimal value of the **Equilibrium Selection Problem** at the contract `α` (Definition 2.2, p.9):
`sup { u_P(α, S) : S ∈ NE(α) }`. The set is finite; the theorems use it only where it is nonempty (every contract
of the instances considered has a pure Nash equilibrium, p.9), so the supremum is the paper's maximum. -/
noncomputable def OPTES (M : Model ι T) (α : ι → ℝ) : ℝ :=
  sSup {u : ℝ | ∃ S : Finset T, M.IsNE α S ∧ u = M.principalUtil α S}

/-- The answer of an **optimal equilibria query** (Definition 4.10, p.26, PDF p.27):
`NE★(α) = argmax_{S ∈ NE(α)} u_P(α, S)`, the entire set of principal-optimal equilibria, ties included. -/
def NEstar (M : Model ι T) (α : ι → ℝ) : Set (Finset T) :=
  {S | M.IsNE α S ∧ ∀ S' : Finset T, M.IsNE α S' → M.principalUtil α S' ≤ M.principalUtil α S}

end CritContracts.Supplement


