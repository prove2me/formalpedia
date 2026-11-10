-- Prove2me | Definitions.Def_CritContracts_IsGreatestBR
-- name    : CritContracts_IsGreatestBR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:20.095438+00:00
-- url     : https://prove2.me/theorems/7284c5df-6424-48d2-804c-c9d2ff649f36
-- title:
--   Best responses, greatest best responses $\mathrm{BR}^+_i(t,S_{-i})$ and the greatest equilibrium $S^+(\alpha)$
-- statement:
--   Fix an instance, an agent $i$, a share $t$ and a set $X$ of the other agents' actions.
--
--   1. $D\subseteq T_i$ is a **best response** of agent $i$ at share $t$ to $X$ if it maximizes $t\,f(D'\cup X)-c(D')$ over all $D'\subseteq T_i$.
--   2. $D$ is the **greatest best response** $\mathrm{BR}^+_i(t,X)$ if it is a best response containing every best response.
--   3. $G$ is the **greatest equilibrium** $S^+(\alpha)$ of a payment vector $\alpha$ if $G\in\mathrm{NE}(\alpha)$ and $S\subseteq G$ for every $S\in\mathrm{NE}(\alpha)$.
--
--   For supermodular rewards these objects exist (Lemma 3.3 and the proof of Lemma 3.10); Lemma 3.10 states their monotonicity.
--
--   **Formalization Note** All three are predicates, not functions, so that no default value is chosen when the greatest element does not exist.
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), §3.1, p.11 (PDF p.12): S⁺(α); §3.3.1, p.17 (PDF p.18): BR⁺ᵢ(t, S₋ᵢ); Appendix D.1, p.48 (PDF p.49)

import Mathlib
import Definitions.Def_CritContracts_Model

set_option autoImplicit false

namespace CritContracts

namespace Model

variable {ι T : Type} [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T]

/-- `D` is a **best response** of agent `i` at share `t` to the other agents' actions `X` (Ezra–Feldman–Molina–
Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial Contracts*, STOC 2027 submission (manuscript
sha256 430be35c…), §3.1 and §3.3.1, pp.12 and 17, PDF pp.13 and 18): `D ⊆ Tᵢ` maximizes
`t · f(D' ⊎ X) − c(D')` over all `D' ⊆ Tᵢ`. -/
def IsBR (M : Model ι T) (i : ι) (t : ℝ) (X D : Finset T) : Prop :=
  (∀ j ∈ D, M.owner j = i) ∧
    ∀ D' : Finset T, (∀ j ∈ D', M.owner j = i) →
      t * M.f (D' ∪ X) - ∑ j ∈ D', M.c j ≤ t * M.f (D ∪ X) - ∑ j ∈ D, M.c j

/-- `D` is the **greatest best response** `BR⁺ᵢ(t, X)` (p.17): a best response containing every best response.

**Formalization Note** A predicate, not a function, so that no junk value is chosen when no greatest element
exists. -/
def IsGreatestBR (M : Model ι T) (i : ι) (t : ℝ) (X D : Finset T) : Prop :=
  M.IsBR i t X D ∧ ∀ D' : Finset T, M.IsBR i t X D' → D' ⊆ D

/-- `G` is the **greatest equilibrium** `S⁺(α)` of `α` (p.11): the greatest element of `NE(α)` under inclusion.

**Formalization Note** A predicate, as for `IsGreatestBR`. -/
def IsGreatestNE (M : Model ι T) (α : ι → ℝ) (G : Finset T) : Prop :=
  IsGreatest {S : Finset T | M.IsNE α S} G

end Model

end CritContracts


