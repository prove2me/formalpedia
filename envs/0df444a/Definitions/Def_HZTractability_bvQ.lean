-- Prove2me | Definitions.Def_HZTractability_bvQ
-- name    : HZTractability_bvQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:08:28.012638+00:00
-- url     : https://prove2.me/theorems/a0a4d380-cd0a-49ad-8fd9-dfb0f4db9ce7
-- title:
--   Link populations and target supplies $b_v, c_v, S_L, S_M, S_H$ (display (17))
-- statement:
--   At a vertex $v$ with indegree $h_v$ and outdegree $o_v$, the lower-link population, upper-buyer population and the supplies of the low, middle and high target groups are
--   $$
--   b_v=b+1-3h_v,\quad c_v=o_v\gamma K-b,\quad S_L=o_vK+C,\quad S_M=a(c_v+C),\quad S_H=a^2(b-2C),
--   $$
--   with $C=16D^2$, $b=4C$ and $\gamma=a^2/(1-a^2)$.
--
--   These choices make the target revenue and link budgets satisfy the identities that cancel the unwanted terms of the residual $\Phi_v$.
--
--   **Formalization Note** The rational formulas; the market uses their natural-number ceilings, which equal them by Lemma A.1.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), display (17), p.16 (PDF p.18); (10), p.13

import Mathlib
import Definitions.Def_HZTractability_admissible
import Definitions.Def_HZTractability_Lp

namespace HZTractability

/-- **The link populations and target supplies** (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, display (17), p.16 (PDF 18)):
"b_v = b + 1 − 3h_v, c_v = o_vγK − b, S_L = o_vK + C, S_M = a(c_v + C), S_H = a²(b − 2C)".
This is `b_v` as a rational expression of the indegree `h = h_v`. -/
def bvQ (a : ℚ) (h : ℕ) : ℚ := (bb a : ℚ) + 1 - 3 * h

/-- `c_v = o_v γ K − b` (display (17), p.16), with `o = o_v`. -/
def cvQ (a : ℚ) (K o : ℕ) : ℚ := (o : ℚ) * gam a * K - bb a

/-- `S_L = o_v K + C` (display (17), p.16; also (10), p.13). -/
def SLQ (a : ℚ) (K o : ℕ) : ℚ := (o : ℚ) * K + Cc a

/-- `S_M = a (c_v + C)` (display (17), p.16). -/
def SMQ (a : ℚ) (K o : ℕ) : ℚ := a * (cvQ a K o + Cc a)

/-- `S_H = a² (b − 2C)` (display (17), p.16); the same at every vertex. -/
def SHQ (a : ℚ) : ℚ := a ^ 2 * ((bb a : ℚ) - 2 * Cc a)

end HZTractability


