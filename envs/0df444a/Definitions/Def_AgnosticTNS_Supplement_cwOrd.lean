-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_cwOrd
-- name    : AgnosticTNS_Supplement_cwOrd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:32:07.989564+00:00
-- url     : https://prove2.me/theorems/00d469a2-47de-4c37-baca-a094be69d1fb
-- title:
--   Cutwidth $\mathrm{cw}(\pi)$ of a linear ordering
-- statement:
--   The **cutwidth** of a linear ordering $\pi:V\to[n]$ of the vertices of $G$ is the largest cut between a prefix and the remaining vertices:
--   $$
--   \mathrm{cw}(\pi) = \max_{i\in[n]} \big|\mathrm{cut}_G(\{v\in V:\pi(v)\le i\})\big| .
--   $$
--
--   **Formalization Note** Positions are $0$-based, so the prefixes are $\{v:\pi(v)\le i'\}$ for $i'=0,\dots,n-1$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 6.1, Eq. (6.1), p.48

import Mathlib
import Definitions.Def_AgnosticTNS_cut

namespace AgnosticTNS.Supplement

/-- **The cutwidth of a linear ordering** `cw(π) = max_{i ∈ [n]} |cut_G({v ∈ V : π(v) ≤ i})|`,
Eq. (6.1), Definition 6.1, p.48 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).

**Formalization Note** Positions are 0-based, so the paper's prefix `{v : π(v) ≤ i}` (`i ∈ [n]`) is
`{v : π v ≤ i'}` with `i' = i − 1 ∈ Fin n`. -/
noncomputable def cwOrd {n : ℕ} (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) : ℕ :=
  Finset.univ.sup fun i : Fin n => (cut G (Finset.univ.filter fun v => π v ≤ i)).card

end AgnosticTNS.Supplement


