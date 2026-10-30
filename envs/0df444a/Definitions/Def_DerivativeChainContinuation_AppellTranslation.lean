-- Prove2me | Definitions.Def_DerivativeChainContinuation_AppellTranslation
-- name    : DerivativeChainContinuation_AppellTranslation
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:30:58.724345+00:00
-- url     : https://prove2.me/theorems/40eeb0ac-8be4-490a-87bd-ffad34dc9fed
-- title:
--   Translated Appell rows
-- statement:
--   For an Appell row $A_m$, coefficient sequence $c$ and center $u\in\mathbb C$, define $A_{m,u}(X)=A_m(X-u)$. The definition preserves the actual derivative-tower normalization.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AppellTranslation.lean#L7-L8

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AppellRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial

noncomputable def translatedAppell (m : ℕ) (c : ℕ → ℂ) (u : ℂ) : Polynomial ℂ :=
  (appellRow m c).comp (X-C u)









end DerivativeChainContinuation


