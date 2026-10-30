-- Prove2me | Definitions.Def_PermBlockchain_Transfers_Vert
-- name    : PermBlockchain_Transfers_Vert
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:42:43.408072+00:00
-- url     : https://prove2.me/theorems/42aa70d4-7466-41cc-bf05-ec403af93763
-- title:
--   Vertical type $\xi_i\in\{h,l\}$
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The vertical type of a manufacturer is high or low,
--   $$\xi_i\in\{h,l\},$$
--   and a manufacturer of vertical type $h$ (resp. $l$) procures from the type $h$ (resp. $l$) vendor.
--
--   **Formalization Note** The labels are `hi` and `lo`; the numbers $h>l\ge0$ that the paper denotes by the same letters are separate real parameters.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 8 (PDF p. 9), unnumbered

import Mathlib

namespace PermBlockchain.Transfers

/-- **Vertical type `ξ_i ∈ {h, l}` of a manufacturer (and of the vendor it procures from).**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 8 (PDF p. 9), unnumbered: "ξ_i ∈ {h, l} corresponds to vertical
differentiation … manufacturers of the vertically differentiated type h (resp. l) procure from the
type h (resp. type l) vendor". `hi` is `h`, `lo` is `l`. -/
inductive Vert
  | hi
  | lo
  deriving DecidableEq

/-- `Vert` is finite: its elements are `hi` and `lo`. -/
instance : Fintype Vert :=
  ⟨{.hi, .lo}, fun x => by cases x <;> simp⟩

end PermBlockchain.Transfers


