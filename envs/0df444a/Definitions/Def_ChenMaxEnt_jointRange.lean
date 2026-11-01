-- Prove2me | Definitions.Def_ChenMaxEnt_jointRange
-- name    : ChenMaxEnt_jointRange
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:32.361058+00:00
-- url     : https://prove2.me/theorems/1a8baf60-c557-494a-843b-e33f86fc0177
-- title:
--   The set $D_F$ of attainable measurement results
-- statement:
--   Let $F = (F_1,\dots,F_r)$ be observables on $\mathcal H = \mathbb C^n$ and let $\mathcal D$ be the set of all states (density matrices: positive semidefinite, trace one). The set of **attainable measurement results** is
--
--   $$
--   D_F = \bigl\{\alpha \in \mathbb R^r \;\big|\; \alpha = (\operatorname{tr}(\rho F_1), \dots, \operatorname{tr}(\rho F_r)) \text{ for some } \rho \in \mathcal D\bigr\},
--   $$
--
--   the image of $\mathcal D$ under the data map. It is a compact convex subset of $\mathbb R^r$ (the joint numerical range of the $F_i$), and the maximum entropy inference $\rho^*$ is a function on $D_F$.
--
--   **Formalization Note** States are the published `QAlgorithms.IsDensityMatrix`; the data map is `ChenMaxEnt.expectations` (real parts of traces).
-- source:
--   Chen et al., Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions, arXiv:1406.5046v2, §2.1, p.4 (definition of D_F)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_ChenMaxEnt_expectations

namespace ChenMaxEnt

/-- Chen et al., arXiv:1406.5046v2, §2.1, p.4: the set of all possible measurement results,
"DF = {α | α = (tr(ρF1), . . . , tr(ρFr)) for some ρ}", where `ρ` ranges over the set `D` of all
quantum states on `H`. It is the image of `D` under the data map (1) (`expectations F`), a compact
convex subset of `ℝ^r` (the joint numerical range of the `F_i`).

**Formalization Note.** A state is a density matrix (`QAlgorithms.IsDensityMatrix`: positive
semidefinite with trace one). -/
def jointRange {n ι : Type*} [Fintype n] (F : ι → Matrix n n ℂ) : Set (ι → ℝ) :=
  expectations F '' {ρ | QAlgorithms.IsDensityMatrix ρ}

end ChenMaxEnt


