-- Prove2me | Definitions.Def_MultimodularDocks_bikeMove
-- name    : MultimodularDocks_bikeMove
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:49.489841+00:00
-- url     : https://prove2.me/theorems/a27d7e18-bc81-48d1-9d0b-dc52daf1e650
-- title:
--   Move of a bike from $i$ to $j$
-- statement:
--   The **move of a bike** from station $i$ to station $j$ transforms $(\vec d,\vec b)$ into
--
--   $$
--   (\vec d+e_i-e_j,\ \vec b-e_i+e_j):
--   $$
--
--   station $i$ gains an empty dock and loses a bike, station $j$ the opposite. The number of docks at every station is unchanged.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, §3.1, p.18

import Mathlib
import Definitions.Def_MultimodularDocks_Instance

namespace MultimodularDocks

/-- **The move of a bike from `i` to `j`** (Freund, Henderson, Shmoys, arXiv:1611.09304v5,
p.18): `(d⃗ + e_i − e_j, b⃗ − e_i + e_j)`. It keeps the number of docks at every station. -/
def bikeMove {S : Type*} [DecidableEq S] (i j : S) (a : Alloc S) : Alloc S :=
  ⟨a.d + Pi.single i 1 - Pi.single j 1, a.b - Pi.single i 1 + Pi.single j 1⟩

end MultimodularDocks


