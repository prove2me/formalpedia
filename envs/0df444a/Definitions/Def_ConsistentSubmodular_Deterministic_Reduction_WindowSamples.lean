-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_WindowSamples
-- name    : ConsistentSubmodular_Deterministic_Reduction_WindowSamples
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:11:21.279277+00:00
-- url     : https://prove2.me/theorems/3cd50fa3-bde8-4d21-bfd5-9bd2c5e23b3a
-- title:
--   Window samples: sampled entry and exit pieces with forced set and recourse cost
-- statement:
--   Let $W$ be a fractional window for $f$ with old set $\mathrm{old}$, buffers $Q(\cdot)$, core budget $\kappa$, grid parameter $N$, duration $T$, initial and terminal sets, level $\alpha$ and $S$ segments, and let $H\in\mathbb N$. Write $\mathrm{opt}(Q)=\mathrm{opt}_\kappa(\mathrm{old},Q)$ and $V=\mathrm{opt}_\kappa(\mathrm{old},\emptyset)$.
--
--   `WindowSamples W H` is a structure holding a sampled, not yet physically realized, version of the entry and exit paths:
--
--   - a forced set $D\subseteq\mathrm{old}$ with $|D|<H$;
--   - numbers of pieces $p,q$ and two sequences of sets $E_0,\dots,E_p$ (entry) and $X_0,\dots,X_q$ (exit), all contained in $\mathrm{old}$, with $E_0=\text{initial}$, $E_p=X_0$, $X_q=\text{terminal}$, and $|E_j|,|X_j|\le\kappa+\kappa/N$;
--   - total recourse cost $\sum_{j<p}\mathrm{rec}(E_j,E_{j+1})+\sum_{j<q}\mathrm{rec}(X_j,X_{j+1})\le 8S\kappa$;
--   - first-set guarantees: $f(Q(0)\cup(D\cup E_0))\ge(\alpha-2/N)\,\mathrm{opt}(Q(0))$ and $f(Q(T)\cup(D\cup X_0))\ge(\alpha-2/N)\,\mathrm{opt}(Q(T))$;
--   - intersection guarantees at the transitions: for each $j<p$, $f(Q(0)\cup(D\cup(E_j\cap E_{j+1})))\ge(\alpha-2/N)\,\mathrm{opt}(Q(0))$, and likewise for the exit pieces with $Q(T)$;
--   - checkpoint tests: for each retained time $r_i$ of $W$, $f(Q(r_i)\cup(D\cup E_p))\ge\alpha\,\mathrm{opt}(Q(r_i))-V/N$.
--
--   The intersection conditions ensure that a deletion-first realization of each transition from $E_j$ to $E_{j+1}$ (first removing $E_j\setminus E_{j+1}$, then adding) keeps a good value at every intermediate set.
--
--   These samples are the intermediate output of the concentration-based rounding of a fractional window; physically realizing them as set-operation paths gives the rounded windows.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/WindowSamples.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FractionalWindow
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_WindowCounts

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

structure WindowSamples {n κ N T S : ℕ} {α : ℝ} {f : Objective n}
    {old initial terminal : Finset (Fin n)} {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
    (W : FractionalWindow f old Q hQ κ N T initial terminal α S) (H : ℕ) where
  forced : Finset (Fin n)
  forced_subset : forced ⊆ old
  forced_card : forced.card < H
  entryPieces : ℕ
  exitPieces : ℕ
  entry : Fin (entryPieces + 1) → Finset (Fin n)
  exit : Fin (exitPieces + 1) → Finset (Fin n)
  entry_initial : entry 0 = initial
  join : entry (Fin.last entryPieces) = exit 0
  exit_terminal : exit (Fin.last exitPieces) = terminal
  entry_subset : ∀ j, entry j ⊆ old
  exit_subset : ∀ j, exit j ⊆ old
  entry_card : ∀ j, ((entry j).card : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N
  exit_card : ∀ j, ((exit j).card : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N
  cost : (∑ j : Fin entryPieces, (recourse (entry j.castSucc) (entry j.succ) : ℝ)) +
    (∑ j : Fin exitPieces, (recourse (exit j.castSucc) (exit j.succ) : ℝ)) ≤
      8 * (S : ℝ) * (κ : ℝ)
  entry_first_good : (α - 2 / N) * f.bufferedOptimum old (Q 0) κ ≤
    f.value (Q 0 ∪ (forced ∪ entry 0))
  exit_first_good : (α - 2 / N) * f.bufferedOptimum old (Q T) κ ≤
    f.value (Q T ∪ (forced ∪ exit 0))
  entry_intersection : ∀ j : Fin entryPieces,
    (α - 2 / N) * f.bufferedOptimum old (Q 0) κ ≤
      f.value (Q 0 ∪ (forced ∪ (entry j.castSucc ∩ entry j.succ)))
  exit_intersection : ∀ j : Fin exitPieces,
    (α - 2 / N) * f.bufferedOptimum old (Q T) κ ≤
      f.value (Q T ∪ (forced ∪ (exit j.castSucc ∩ exit j.succ)))
  checkpoint_tests : ∀ i, α * f.bufferedOptimum old (Q (W.retained i)) κ -
    f.bufferedOptimum old ∅ κ / N ≤
      f.value (Q (W.retained i) ∪ (forced ∪ entry (Fin.last entryPieces)))

end ConsistentSubmodular

end


