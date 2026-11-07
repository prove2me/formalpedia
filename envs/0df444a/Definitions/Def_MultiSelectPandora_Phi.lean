-- Prove2me | Definitions.Def_MultiSelectPandora_Phi
-- name    : MultiSelectPandora_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:09:21.097208+00:00
-- url     : https://prove2.me/theorems/7ed06a38-e948-4bef-93c0-eea455fcc207
-- title:
--   The proxy $\Phi(U,\alpha)$
-- statement:
--   For a set $U$ of boxes and a floor $a=\alpha_k$,
--   $$\Phi(U,\alpha):=\sum_{i\in U}E\big[(\kappa_i-\alpha_k)_+\big].$$
--   $\Phi$ is additive over $U$ and depends on the state only through its floor; it approximates the utility still to be collected once all entries are large.
--
--   **Formalization Note** The Lean function takes the floor rather than the state, so Remark 3.13 holds by definition.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.12, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_capped

namespace MultiSelectPandora

/-- **The proxy `Φ(U, α)`, through the floor `a = α_k`.** Beyhaghi–Han–Luqman manuscript, Definition 3.12, p.10 (PDF p.11):
`Φ(U, α) := Σ_{i ∈ U} E[(κ_i − α_k)_+]`.

**Formalization Note.** `Phi` takes the floor, not the state, so Remark 3.13 holds by definition. -/
noncomputable def Phi (I : Inst) (U : Finset (Fin I.n)) (a : ℝ) : ℝ :=
  ∑ i ∈ U, ∑ j, I.prob i j * max (capped I i j - a) 0

end MultiSelectPandora


