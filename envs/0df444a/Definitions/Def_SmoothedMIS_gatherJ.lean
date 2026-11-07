-- Prove2me | Definitions.Def_SmoothedMIS_gatherJ
-- name    : SmoothedMIS_gatherJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:45.74226+00:00
-- url     : https://prove2.me/theorems/1104cc7f-1913-4d0e-bd8a-cc62d13823fa
-- title:
--   Step 2 of Algorithm 1: the set $J$, for an MIS rule $J_C$
-- statement:
--   Fix a rule that maps every graph $C$ whose vertices are identifiers to an MIS $J_C$ of $C$ (for example the greedy MIS in increasing order of identifier). With the notation of the active set, Step 2 runs $\mathrm{Gather}(\mathcal G,\mathcal A,\ell)$ and sets
--   $$
--   J=\{v\in\mathcal A:\ v\text{ outputs a graph }C\text{ and }\mathrm{ID}(v)\in J_C\}.
--   $$
--
--   Lemma 4.4 shows that $J$ is independent in $\mathcal G$ and dominates $\mathcal A$ under condition (1).
--
--   **Formalization Note** $J$ is defined through the output of the procedure $\mathrm{Gather}$ itself; the rule is any rule returning an MIS of every identifier-labelled graph.
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), §4.1, Step 2 and Algorithm 1 lines 8–9, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_SmoothedMIS_activeSet
import Definitions.Def_SmoothedMIS_gatherAlg

namespace SmoothedMIS

/-- A rule mapping every identifier-labelled graph `C` to an MIS `J_C` of it (§4.1, Step 2,
p.18: "Fix a deterministic rule that maps every graph C with vertex identifiers to an MIS J_C of
C, for example the greedy MIS in increasing order of identifier"). -/
def IsMISRule (rule : LGraph → Set ℕ) : Prop :=
  ∀ C : LGraph, rule C ⊆ C.V ∧ IsMIS (C.E.induce C.V) {x | x.1 ∈ rule C}

/-- **The set `J` of Step 2** (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed Analysis for
Distributed MIS* (manuscript, sha256 dc2131db…), Algorithm 1 lines 8–9, p.18):
`J = {v ∈ 𝒜 : v outputs a graph C in Gather(𝒢, 𝒜, ℓ) and ID(v) ∈ J_C}`.

**Formalization Note** The output is that of the procedure `gatherAlg ℓ` run on `𝒢` with input
membership in `𝒜` (not a closed formula for it); the procedure ignores the tapes, so a constant
tape is used. `rule` is any MIS-valued rule. -/
noncomputable def gatherJ {n : ℕ} (β : ℝ) (G : SimpleGraph (Fin n)) (ids : Fin n → ℕ)
    (rule : LGraph → Set ℕ) (ω : Coins n) : Set (Fin n) :=
  {v | v ∈ activeSet β G ω ∧ ∃ C, gatherOut (addSmooth G ω.1) (activeSet β G ω) ids (ell n)
      (fun _ _ => false) v = some C ∧ ids v ∈ rule C}

end SmoothedMIS


