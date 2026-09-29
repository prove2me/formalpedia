-- Prove2me | Definitions.Def_ModularSchurPartition
-- name    : ModularSchurPartition
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-19T22:33:23.812382+00:00
-- url     : https://prove2.me/theorems/0c6df565-39e4-494f-b3d3-e9dd8d557605
-- title:
--   Valid $k$-partitions and the residue-level $S_m(k,\ell)$
-- statement:
--   This bundle defines the colouring problem for modular Schur numbers at the level of residues, together with the number it computes.
--
--   Fix $m \ge 2$, $\ell \ge 2$ and $k \ge 1$. Given a target set $T \subseteq \mathbb{Z}/m$, a family $P_0, \dots, P_{k-1}$ of subsets of $\mathbb{Z}/m$ is a **valid $k$-partition of $T$** when the $P_i$ cover $T$, are pairwise disjoint, each lies inside $T$, and each is $\ell$-sum-free modulo $m$. The residue set under consideration is
--
--   $$ \mathrm{stableResidues}(m, N) = \{\, \overline{1}, \overline{2}, \dots, \overline{N} \,\} \subseteq \mathbb{Z}/m, $$
--
--   the image of the integer interval $[1, N]$ under reduction modulo $m$. The **residue-level modular Schur number** is the greatest $N \le m-1$ for which $\mathrm{stableResidues}(m,N)$ admits a valid $k$-partition.
--
--   This is the object every bound in the mission is stated about. The cutoff at $m-1$ is not an approximation: the universal upper bound shows no larger $N$ can ever succeed, so searching past $m-1$ is provably pointless.
--
--   **Formalization Note** The greatest such $N$ is taken with `Nat.findGreatest` against the bound $m-1$, which makes the number total without a separate non-emptiness argument; the definition is noncomputable because the partition predicate is classical.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, Definition 1.1 with the residue counterpart of Lemma 2.1, and the $N \le m-1$ cap of Lemma 2.2. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/Partition.lean#L38-L44

-- Generated from lean/ModularSchur/Partition.lean by skeleton
-- subtraction: every declaration except the def-material below is deleted,
-- and project imports are rewritten to their platform Definitions bundles.
import Definitions.Def_ModularSchurBasic
import Mathlib

namespace ModularSchur

open Finset
variable {m : ℕ}

/-- A valid `k`-partition of a residue set `T ⊆ ZMod m` into `ℓ`-sum-free classes. -/
structure IsValidPartition (m ℓ k : ℕ) (T : Finset (ZMod m))
    (P : Fin k → Finset (ZMod m)) : Prop where
  covers     : ∀ x ∈ T, ∃ i, x ∈ P i
  disjoint   : ∀ i j, i ≠ j → Disjoint (P i) (P j)
  subset     : ∀ i, P i ⊆ T
  sumFree    : ∀ i, IsEllSumFree m ℓ (P i)

/-- The residue set of `{1,…,N}` in `ZMod m`. -/
def stableResidues (m N : ℕ) : Finset (ZMod m) :=
  (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)

open Classical in
/-- `schurModResidue m k ℓ` = greatest `N` such that `stableResidues m N` admits
    a valid `k`-partition, bounded above by `m - 1` per Lemma 2.2. -/
noncomputable def schurModResidue (m k ℓ : ℕ) : ℕ :=
  Nat.findGreatest
    (fun N => ∃ P : Fin k → Finset (ZMod m),
      IsValidPartition m ℓ k (stableResidues m N) P) (m - 1)

end ModularSchur


