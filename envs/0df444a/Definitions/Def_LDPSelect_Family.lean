-- Prove2me | Definitions.Def_LDPSelect_Family
-- name    : LDPSelect_Family
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:02.55499+00:00
-- url     : https://prove2.me/theorems/3a4a1337-f33a-4fca-ba90-743e1598391f
-- title:
--   Set families on an ordered ground set, down-closure, relabelling by an arrival order
-- statement:
--   The ground set is $E=\{1,\dots,n\}$, listed in arrival order. A **family** is a set $\mathcal F\subseteq 2^E$ of subsets of $E$. It is **nonempty and downward closed** if $\emptyset\in\mathcal F$ and every subset of a member of $\mathcal F$ is a member.
--
--   The file also fixes two constructions used throughout the mission.
--
--   1. For a permutation $\sigma$ of $E$, the **relabelled family** $\mathcal F^\sigma=\{S : \sigma(S)\in\mathcal F\}$ describes $\mathcal F$ when the element $\sigma(i)$ arrives in position $i$. Quantifying over all $\sigma$ and all priors on positions covers every arrival order.
--   2. For a list $C_1,\dots,C_r$ of sets, $\mathrm{fromMIS}(C_1,\dots,C_r)=\{S : C_j\not\subseteq S \text{ for all } j\}$ is the downward-closed family whose infeasible sets are those containing some $C_j$. When the list is an antichain of nonempty sets, the $C_j$ are exactly its minimally infeasible sets; the paper specifies its excluded minors this way.
--
--   **Formalization Note** $E$ is `Fin n`, with the paper's element $e$ as `Fin` value $e-1$. The empty ground set $n=0$ is allowed; then $\{\emptyset\}$ is the only downward-closed family.
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), §2, p.5 (pdf p.6); §1.1, p.1 (pdf p.2)

import Mathlib

namespace LDPSelect

/-!
# Set families on an ordered ground set

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), §2, p.5; §1.1, p.1.

**Formalization Note.** The ground set `E = {1, …, n}` of the paper, listed in arrival order, is
`Fin n`, with `Fin` value `e − 1` for the paper's element `e`. A family is a set of finite subsets.
`IsDownClosed` includes `∅ ∈ F`, which is the paper's "nonempty and downward closed". `n = 0` is
allowed: `{∅}` is then the only such family.
-/

/-- A family of subsets of the ground set `Fin n` (§2, p.5). -/
abbrev Family (n : ℕ) := Set (Finset (Fin n))

/-- `F` is nonempty and downward closed (§2, p.5). -/
def IsDownClosed {n : ℕ} (F : Family n) : Prop :=
  ∅ ∈ F ∧ ∀ S ∈ F, ∀ T, T ⊆ S → T ∈ F

/-- The family `F` read in the arrival order `σ`: position `i` holds element `σ i`, and a set `S`
of positions is feasible when the set of elements at those positions is in `F`. -/
def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (F : Family n) : Family n :=
  {S | S.map σ.toEmbedding ∈ F}

/-- The down-closed family whose infeasible sets are those containing a listed set. When the list is
an antichain of nonempty sets, its members are exactly the minimally infeasible sets. -/
def fromMIS {n : ℕ} (L : List (Finset (Fin n))) : Family n :=
  {S | ∀ C ∈ L, ¬ C ⊆ S}

instance {n : ℕ} (L : List (Finset (Fin n))) : DecidablePred (· ∈ fromMIS L) :=
  fun S => inferInstanceAs (Decidable (∀ C ∈ L, ¬ C ⊆ S))

end LDPSelect


