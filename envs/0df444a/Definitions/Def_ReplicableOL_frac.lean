-- Prove2me | Definitions.Def_ReplicableOL_frac
-- name    : ReplicableOL_frac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:33.661469+00:00
-- url     : https://prove2.me/theorems/23948a61-40ee-409c-8507-819227968720
-- title:
--   Fraction $P_j(h;s)$ on expert 1
-- statement:
--   The **fraction** of epoch $j$ played on expert 1 when the prefix is $h$ and the block is $s$. On a run, $p_j=P_j(S_{<j};S_j)$.
--
--   **Formalization Note** Lean's action `0` is the paper's expert 1. The theorems that read this quantity assume `1 ≤ L`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 4.1, p.15

import Mathlib
import Definitions.Def_ReplicableOL_EpochRule

namespace ReplicableOL

/-- **Fraction $P_j(h;s)$ on expert 1.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 4.1, p.15. `P_j(h; s) := (1/L) #{i ≤ L : Φ_j(h; s)_i = 1}`.

**Formalization Note.** Lean's action `0` is the paper's expert 1. The theorems that read this quantity assume `1 ≤ L`. -/
noncomputable def frac {k L : ℕ} (Φ : EpochRule k L) (j : Fin k) (h : Fin j → Block L)
    (s : Block L) : ℝ :=
  ((Finset.univ.filter fun i => Φ j h s i = 0).card : ℝ) / L

end ReplicableOL


