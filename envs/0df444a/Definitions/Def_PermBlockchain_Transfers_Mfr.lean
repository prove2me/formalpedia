-- Prove2me | Definitions.Def_PermBlockchain_Transfers_Mfr
-- name    : PermBlockchain_Transfers_Mfr
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:43:37.942871+00:00
-- url     : https://prove2.me/theorems/da4c4b32-9d00-4662-a179-1a2855542780
-- title:
--   The set of manufacturers $M=\{1,\dots,4m\}$
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The set of manufacturers is
--   $$M=\{1,2,\dots,4m\},$$
--   with $m\ge2$ manufacturers of each of the four types.
--
--   **Formalization Note** Manufacturers are indexed by $\{0,\dots,4m-1\}$; the condition $m\ge2$ is a hypothesis of the theorems that need it.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 8 (PDF p. 9), unnumbered

import Mathlib

namespace PermBlockchain.Transfers

/-- **The set of manufacturers `M = {1, 2, …, 4m}`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 8 (PDF p. 9), unnumbered: "Let M := {1, 2, . . . , 4m} be the set of
manufacturers with m ≥ 2".

**Formalization Note.** Manufacturers are indexed by `Fin (4 * m)`; the hypothesis `m ≥ 2` is a
binder of every statement that needs it. -/
abbrev Mfr (m : ℕ) : Type := Fin (4 * m)

end PermBlockchain.Transfers


