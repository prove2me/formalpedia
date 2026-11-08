-- Prove2me | Definitions.Def_CompDesignBFM_M
-- name    : CompDesignBFM_M
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:33.119809+00:00
-- url     : https://prove2.me/theorems/e4b65663-0247-48d6-9d89-fdaf6f04f681
-- title:
--   Best affordable singleton value M
-- statement:
--   $M=\max\{v(\{i\}): c_i\le B\}$ is the maximum value of any affordable single agent.
--
--   **Formalization Note** $M$ is taken to be $0$ when no agent is affordable: the value of the singleton branch there, which selects $\emptyset$.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §3.1, p.13 (PDF 15)

import Mathlib

namespace CompDesignBFM

open Classical in
/-- `M = max {v {i} : cᵢ ≤ B}`, the maximum value of an affordable single agent
(Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §3.1, p.13, PDF 15).
**Formalization Note.** The value `0` when no agent is affordable is the encoding of the paper's
maximum: it is what the singleton branch achieves there when `v ∅ = 0` (Lemma 3.4's proof, p.17). -/
noncomputable def M {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) : ℝ :=
  if h : (Finset.univ.filter fun i : Fin n => c i ≤ B).Nonempty then
    (Finset.univ.filter fun i : Fin n => c i ≤ B).sup' h fun i => v {i}
  else 0

end CompDesignBFM


