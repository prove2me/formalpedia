-- Prove2me | Definitions.Def_PrivLittlestone_IsPhaseDecomposition
-- name    : PrivLittlestone_IsPhaseDecomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:12.666193+00:00
-- url     : https://prove2.me/theorems/8ba83c5c-a3e2-42bb-a896-aacac0c503b4
-- title:
--   Phase decomposition of a classifier transcript
-- statement:
--   A **phase decomposition** of a classifier transcript $(g_1, \dots, g_T)$ is a list of phases $(t_j, g^{(j)}, e_j)$: the first starts at the first round, each phase but the last ends with a crossing $e_j = (k_j, \mathrm{cross})$ and the next phase starts right after $k_j$, the last ends with a crossing or with $(T, \text{no-cross})$, and the transcript equals the phase aggregate $g^{(j)}$ on the rounds of phase $j$. The phase-start history $H_j$ consists of the start round, the past classifiers and $g^{(j)}$.
--
--   **Formalization Note** No completeness condition is imposed; runs reaching the cap end with a crossing and continue with the public fallback, which carries no threshold kernel.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma B.2, (25), p.22

import Mathlib

namespace PrivLittlestone

/-- A **phase decomposition** of a classifier transcript (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
Lemma B.2, (25), p.22: "Every complete augmented transcript `w`, with phase histories and
endpoints `(H_j, e_j)`"): a list of phases `(t_j, g_j, e_j)` with start rounds `t_j < T`, the
first at round `0`, each phase but the last ending in a crossing `e_j = (k_j, cross)` with
`t_j ≤ k_j < T` and the next starting at `k_j + 1`, the last ending in a crossing or in
`(T, no-cross)`, and the transcript `gs` equal to the phase aggregate `g_j` on the rounds of
phase `j`. The phase-start history `H_j` is `(t_j, gs, g_j)`.

**Formalization Note** No completeness condition (last phase at the horizon or at the cap) is
imposed; transcripts reaching the cap end with a crossing and continue with the public
fallback, which carries no threshold kernel. -/
def IsPhaseDecomposition {X : Type*} {T : ℕ} (gs : Fin T → X → Bool)
    (ph : List (ℕ × (X → Bool) × (ℕ × Bool))) : Prop :=
  (∀ p ∈ ph.head?, p.1 = 0) ∧
    ph.IsChain (fun p q => p.2.2.2 = true ∧ q.1 = p.2.2.1 + 1) ∧
    ∀ p ∈ ph, p.1 < T ∧
      ((p.2.2.2 = true ∧ p.1 ≤ p.2.2.1 ∧ p.2.2.1 < T) ∨ (p.2.2.2 = false ∧ p.2.2.1 = T)) ∧
      ∀ i : Fin T, p.1 ≤ (i : ℕ) → (i : ℕ) ≤ p.2.2.1 → gs i = p.2.1

end PrivLittlestone


