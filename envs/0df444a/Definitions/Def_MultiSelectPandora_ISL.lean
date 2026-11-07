-- Prove2me | Definitions.Def_MultiSelectPandora_ISL
-- name    : MultiSelectPandora_ISL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:24:21.0172+00:00
-- url     : https://prove2.me/theorems/eca183be-a3db-40ae-9087-ccfb70f14516
-- title:
--   The large-value discretization $I^{SL}$
-- statement:
--   $I^{SL}$ has the marginal reward of $I^S$, and the transition inserts $D^L(w_i)$ on opening and $b_i$ on a closed claim. Thus rounding affects the state only: the reward credits $w_i$, and the state receives $D^L(w_i)\ge w_i$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.23, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_DPData
import Definitions.Def_MultiSelectPandora_wVal
import Definitions.Def_MultiSelectPandora_bVal
import Definitions.Def_MultiSelectPandora_DL

namespace MultiSelectPandora

/-- **The program `I^SL`.** Beyhaghi–Han–Luqman manuscript, Definition 3.23, p.15 (PDF p.16): the marginal reward of `I^S`, and the
transition `sort(α_1, …, α_{k−1}, max{α_k, D^L(w_i)})`, with closed claims as in `I^S`.

**Formalization Note.** The state set is `Levels`; this structure does not mention it, and the rounding is in `x`. -/
noncomputable def ISL (I : Inst) (k : ℕ) (ε : ℝ) : DPData I.n I.s :=
  ⟨I.c, I.prob, wVal I k ε, fun i j => DL I k ε (wVal I k ε i j), bVal I k ε⟩

end MultiSelectPandora


