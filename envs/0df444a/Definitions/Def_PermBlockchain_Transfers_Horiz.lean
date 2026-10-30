-- Prove2me | Definitions.Def_PermBlockchain_Transfers_Horiz
-- name    : PermBlockchain_Transfers_Horiz
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:42:26.024731+00:00
-- url     : https://prove2.me/theorems/60ee5b1f-f1b5-49b9-9d93-aaf1399ba8e8
-- title:
--   Horizontal type $q_i\in\{A,B\}$ (and consumer type $t_k$)
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The horizontal type is one of two labels,
--   $$q_i\in\{A,B\},$$
--   and each consumer $k$ also has a type $t_k\in\{A,B\}$ (with equal probability). A consumer prefers goods of her own horizontal type.
--
--   This finite type of two labels is shared by manufacturers and consumers.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, pp. 8–9 (PDF pp. 9–10), unnumbered

import Mathlib

namespace PermBlockchain.Transfers

/-- **Horizontal type `q_i ∈ {A, B}` of a manufacturer, and type `t_k` of a consumer.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 8 (PDF p. 9), unnumbered: "Each manufacturer i has a two-dimensional type
(q_i, ξ_i), where q_i ∈ {A, B} is related to horizontal differentiation"; p. 9 (PDF p. 10):
"Each consumer k ∈ [0, 1] also has type t_k ∈ {A, B} with equal probability". -/
inductive Horiz
  | A
  | B
  deriving DecidableEq

/-- `Horiz` is finite: its elements are `A` and `B`. -/
instance : Fintype Horiz :=
  ⟨{.A, .B}, fun x => by cases x <;> simp⟩

end PermBlockchain.Transfers


