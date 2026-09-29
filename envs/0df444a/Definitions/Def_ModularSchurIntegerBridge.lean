-- Prove2me | Definitions.Def_ModularSchurIntegerBridge
-- name    : ModularSchurIntegerBridge
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-19T22:34:23.467276+00:00
-- url     : https://prove2.me/theorems/a39c86c6-1711-4762-b242-12b5fcf8e586
-- title:
--   Integer-level $\ell$-sum-freeness and $S_m(k,\ell)$
-- statement:
--   This bundle gives the integer-level form of the definitions, which is how the modular Schur number is stated in the literature.
--
--   Fix $m \ge 2$ and $\ell \ge 2$. A finite set $S \subseteq \mathbb{N}$ is **$\ell$-sum-free modulo $m$** when no $\ell$ elements of $S$, repetitions allowed, sum to an element of $S$ modulo $m$. A family $P_0, \dots, P_{k-1}$ of subsets of $\mathbb{N}$ is a **valid $k$-partition of $[1,N]$** when the $P_i$ cover $\{1, \dots, N\}$, are pairwise disjoint, lie inside $\{1, \dots, N\}$, and are each $\ell$-sum-free modulo $m$. The **modular Schur number** is
--
--   $$ S_m(k,\ell) = \max \{\, N \le m-1 : [1,N] \text{ admits a valid } k \text{-partition} \,\}. $$
--
--   Stating the problem over the integers is what makes $S_m(k,\ell)$ comparable with the classical Schur numbers and with the values tabulated in the literature, while the residue form is the one that is convenient to reason with. Keeping both, and proving them equal, is what lets a result proved about residues be quoted as a statement about integers.
--
--   **Formalization Note** As in the residue version the maximum is taken with `Nat.findGreatest` against $m-1$; the accompanying theorem `ModularSchur.schurMod_is_greatest` shows this cap loses no solutions.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, Definition 1.1 (integer form), with the $N \le m-1$ cap of Lemma 2.2. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/IntegerBridge.lean#L39-L45

-- Generated from lean/ModularSchur/IntegerBridge.lean by skeleton
-- subtraction: every declaration except the def-material below is deleted,
-- and project imports are rewritten to their platform Definitions bundles.
import Definitions.Def_ModularSchurPartition
import Mathlib

namespace ModularSchur

open Finset
variable {m : ℕ}

/-- Integer-level `ℓ`-sum-freeness mod `m`: for `S ⊆ ℕ`, no `ℓ`-tuple from `S`
    has sum congruent mod `m` to any `y ∈ S`. -/
def IsSumFreeIntMod (m ℓ : ℕ) (S : Finset ℕ) : Prop :=
  ∀ f : Fin ℓ → ℕ, (∀ i, f i ∈ S) → ∀ y ∈ S, (∑ i, f i) % m ≠ y % m

/-- A valid `k`-partition of `{1,…,N} ⊆ ℕ` into `ℓ`-sum-free-mod-`m` classes. -/
structure IsValidPartitionNat (m ℓ k N : ℕ) (P : Fin k → Finset ℕ) : Prop where
  covers   : ∀ x ∈ Finset.Ioc 0 N, ∃ i, x ∈ P i
  disjoint : ∀ i j, i ≠ j → Disjoint (P i) (P j)
  subset   : ∀ i, P i ⊆ Finset.Ioc 0 N
  sumFree  : ∀ i, IsSumFreeIntMod m ℓ (P i)

open Classical in
/-- Integer-level modular Schur number: greatest `N ≤ m-1` such that `{1,…,N}`
    admits a valid `k`-partition into `ℓ`-sum-free-mod-`m` classes.  This is
    the paper's Definition 1.1, with the `N ≤ m-1` cap from Lemma 2.2 baked in. -/
noncomputable def schurMod (m k ℓ : ℕ) : ℕ :=
  Nat.findGreatest
    (fun N => ∃ P : Fin k → Finset ℕ, IsValidPartitionNat m ℓ k N P) (m - 1)

end ModularSchur


