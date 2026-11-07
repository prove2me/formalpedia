-- Prove2me | Definitions.Def_ReplicableOL_pbar
-- name    : ReplicableOL_pbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:48:01.601903+00:00
-- url     : https://prove2.me/theorems/9024f51d-c2f9-4db9-bee9-dfe8bbdc7da3
-- title:
--   Predicted fraction $\bar p_j$
-- statement:
--   The prediction of the fraction of epoch $j$ from the past: $\bar p_j=\mathbb E[p_j\mid S_{<j}]=\int P_j(S_{<j};s)\,\bar\nu(ds)$.
--
--   **Formalization Note** This is the explicit version as a function of the prefix `h`. Lemma 4.1 (`lemma_4_1`) proves that it is a version of Mathlib's `condExp` on the four-run space.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.2, p.8; Lemma 4.1(d), p.15

import Mathlib
import Definitions.Def_ReplicableOL_frac
import Definitions.Def_ReplicableOL_avgWeight

namespace ReplicableOL

/-- **Predicted fraction $\bar p_j$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.2, p.8; Lemma 4.1(d), p.15. `p̄_j := E[p_j | S_{<j}]`, with explicit version `p̄_j = ∫ P_j(S_{<j}; s) ν̄(ds)`.

**Formalization Note.** This is the explicit version as a function of the prefix `h`. Lemma 4.1 (`lemma_4_1`) proves that it is a version of Mathlib's `condExp` on the four-run space. -/
noncomputable def pbar {k L : ℕ} (Δ : ℝ) (Φ : EpochRule k L) (j : Fin k) (h : Fin j → Block L) : ℝ :=
  ∑ s : Block L, avgWeight Δ s * frac Φ j h s

end ReplicableOL


