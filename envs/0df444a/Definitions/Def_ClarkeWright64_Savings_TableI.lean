-- Prove2me | Definitions.Def_ClarkeWright64_Savings_TableI
-- name    : ClarkeWright64_Savings_TableI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:39:30.196158+00:00
-- url     : https://prove2.me/theorems/ff2e55b2-dfa0-46b4-bb2a-5e20c7c38e2e
-- title:
--   Table I, p. 572, and the fleet of p. 573 — the numerical example with 12 customers
-- statement:
--   The numerical example of Clarke and Wright (the example of Dantzig and Ramser). There are $M=12$ customers. Their loads $Q$ (Table I, p. 572) are
--   $$
--   q = (1200, 1700, 1500, 1400, 1700, 1400, 1200, 1900, 1800, 1600, 1700, 1100),
--   $$
--   and the distances from the depot are $d_{0,j} = 9, 14, 21, 23, 22, 25, 32, 36, 38, 42, 50, 52$; the distances between customers are the lower right-hand entries of the cells of Table I. The fleet (p. 573) is an unlimited supply of trucks of capacity 4000 gallons, 3 trucks of capacity 5000 gallons and 4 trucks of capacity 6000 gallons.
--
--   This instance is the input of the worked example whose final solution has total distance 290 units.
--
--   **Formalization Note** The distance matrix is stored in full, symmetric with zero diagonal; every one of the 66 printed savings equals $d_{0,y}+d_{0,z}-d_{y,z}$ for these distances. The depot's load entry is set to $0$ and is never used.
-- source:
--   Clarke & Wright, Scheduling of vehicles from a central depot to a number of delivery points, Oper. Res. 12 (1964), p. 572, Table I; p. 573 (fleet)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance

namespace ClarkeWright64.Savings

/-- The distances of Table I, p. 572 (the lower right-hand entry `d(P_y : P_z)` of each cell and
the column `P₀`), as a symmetric matrix with zero diagonal; row and column `0` are the depot. -/
def tableIDist : Fin 13 → Fin 13 → ℝ :=
  ![![0, 9, 14, 21, 23, 22, 25, 32, 36, 38, 42, 50, 52],
    ![9, 0, 5, 12, 22, 21, 24, 31, 35, 37, 41, 49, 51],
    ![14, 5, 0, 7, 17, 16, 23, 26, 30, 36, 36, 44, 46],
    ![21, 12, 7, 0, 10, 21, 30, 27, 37, 43, 31, 37, 39],
    ![23, 22, 17, 10, 0, 19, 28, 25, 35, 41, 29, 31, 29],
    ![22, 21, 16, 21, 19, 0, 9, 10, 16, 22, 20, 28, 30],
    ![25, 24, 23, 30, 28, 9, 0, 7, 11, 13, 17, 25, 27],
    ![32, 31, 26, 27, 25, 10, 7, 0, 10, 16, 10, 18, 20],
    ![36, 35, 30, 37, 35, 16, 11, 10, 0, 6, 6, 14, 16],
    ![38, 37, 36, 43, 41, 22, 13, 16, 6, 0, 12, 12, 20],
    ![42, 41, 36, 31, 29, 20, 17, 10, 6, 12, 0, 8, 10],
    ![50, 49, 44, 37, 31, 28, 25, 18, 14, 12, 8, 0, 10],
    ![52, 51, 46, 39, 29, 30, 27, 20, 16, 20, 10, 10, 0]]

/-- The numerical example of pp. 572–576: twelve customers with the distances and the loads `Q`
of Table I (p. 572), and the fleet of p. 573: an unlimited supply of 4000-gallon trucks, 3 trucks
of 5000 gallons and 4 trucks of 6000 gallons. The depot's load entry is unused. -/
def tableI : Instance 12 2 where
  d := tableIDist
  q := ![0, 1200, 1700, 1500, 1400, 1700, 1400, 1200, 1900, 1800, 1600, 1700, 1100]
  C := ![4000, 5000, 6000]
  x := ![⊤, 3, 4]

end ClarkeWright64.Savings


