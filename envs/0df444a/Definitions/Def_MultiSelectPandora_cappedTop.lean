-- Prove2me | Definitions.Def_MultiSelectPandora_cappedTop
-- name    : MultiSelectPandora_cappedTop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:09:51.867671+00:00
-- url     : https://prove2.me/theorems/4295edc9-825d-4fb1-b47f-6efdcc0065d3
-- title:
--   The expected top-$k$ sum of observed and capped values
-- statement:
--   For a set $U$ of boxes and a state $\alpha$, this is $\mathbb E\big[\sum_j\beta_j\big]$ with $\beta=\mathrm{top}_k(\alpha\cup\{\kappa_i\}_{i\in U})$, the closed form of Fact 2.1.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Fact 2.1, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_capped
import Definitions.Def_MultiSelectPandora_expect
import Definitions.Def_MultiSelectPandora_topSum

namespace MultiSelectPandora

/-- **`E[Σ_j β_j]`, where `β = top_k(α ∪ {κ_i}_{i ∈ U})`.** Beyhaghi–Han–Luqman manuscript, Fact 2.1, p.6 (PDF p.7). -/
noncomputable def cappedTop (I : Inst) {k : ℕ} (U : Finset (Fin I.n)) (α : Fin k → ℝ) : ℝ :=
  expect I U fun ω => topSum k (List.ofFn α ++ (Finset.univ : Finset U).toList.map fun i => capped I i.1 (ω i))

end MultiSelectPandora


