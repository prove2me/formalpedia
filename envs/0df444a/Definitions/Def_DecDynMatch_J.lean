-- Prove2me | Definitions.Def_DecDynMatch_J
-- name    : DecDynMatch_J
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:09.347699+00:00
-- url     : https://prove2.me/theorems/bf7e864b-4645-4e2c-9226-c6a75005237b
-- title:
--   Protocol constants $J=K^2+5K+1$, $H=4J+4$, $U=2K^2+14K$
-- statement:
--   The SC-DA protocol on $K$ arms uses
--   $$
--   J=K^2+5K+1,\qquad H=4J+4,
--   $$
--   where $J$ is the length of a Work mode and the number of consecutive BUS acceptances that qualify a player for Sweep, and $H$ is a lower bound on replay lengths. The analysis bounds every maintenance window by
--   $$
--   U=2K^2+14K .
--   $$
--   These constants appear in every timing statement of the mission; $H\le 16K^2$ and $U\le 9K^2$ for $K\ge 2$.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), eq. (2), p.5; Lemma 8, p.19

import Mathlib

namespace DecDynMatch

/-- **Protocol constants.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*,
arXiv:2610.41912 (held version, sha256 6a27277e…), eq. (2), p.5: "J = K² + 5K + 1, H = 4J + 4";
Lemma 8, p.19: "U = 2K² + 14K". `J K` is the length of a Work mode and the number of consecutive BUS
acceptances that qualify for Sweep, `H K` the minimum replay length, `U K` the maintenance-window
bound. -/
def J (K : ℕ) : ℕ := K ^ 2 + 5 * K + 1

/-- `H = 4J + 4` (eq. (2), p.5). -/
def H (K : ℕ) : ℕ := 4 * J K + 4

/-- `U = 2K² + 14K` (Lemma 8, p.19). -/
def U (K : ℕ) : ℕ := 2 * K ^ 2 + 14 * K

end DecDynMatch


