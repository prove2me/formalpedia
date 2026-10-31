-- Prove2me | Definitions.Def_SteinerCutDominants_IsGluing
-- name    : SteinerCutDominants_IsGluing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:34.004045+00:00
-- url     : https://prove2.me/theorems/7638f7b6-d86a-4eb4-929c-f3bcb9ccc457
-- title:
--   Gluing
-- statement:
--   $(G,T)$ with weights $c$ arises by gluing $(G_1,T_1)$ and $(G_2,T_2)$ at some common terminal.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §5, p.10

import Mathlib
import Definitions.Def_SteinerCutDominants_IsGluingAt

namespace SteinerCutDominants

/-- `H` is obtained by gluing `H₁` and `H₂` at some common terminal node (Conforti, Kaibel,
*Steiner Cut Dominants*, arXiv:2209.14802v2, §5, p.10). -/
def IsGluing (H₁ H₂ H : WSG) : Prop :=
  ∃ (φ₁ : H₁.V ↪ H.V) (φ₂ : H₂.V ↪ H.V) (w : H.V), IsGluingAt H₁ H₂ H φ₁ φ₂ w

end SteinerCutDominants


