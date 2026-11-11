-- Prove2me | Definitions.Def_HamSimTradeoff_AncillaDepth_Suzuki
-- name    : HamSimTradeoff_AncillaDepth_Suzuki
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:59.654211+00:00
-- url     : https://prove2.me/theorems/6a7439a5-884f-4b55-8f69-07599927c00d
-- title:
--   Suzuki product formulas with the source multiplication order
-- statement:
--   For a real step $h$, weights $\alpha_j$, and complex matrices $H_j$, define the symmetric second-order product formula by
--   $$S_2(h)=\left(\prod_{j=L}^{1}e^{-ih\alpha_jH_j/2}\right)\left(\prod_{j=1}^{L}e^{-ih\alpha_jH_j/2}\right).$$
--   For integers $k\ge2$, put $u_k=(4-4^{1/(2k-1)})^{-1}$ and
--   $$S_{2k}(h)=S_{2k-2}(u_kh)^2S_{2k-2}((1-4u_k)h)S_{2k-2}(u_kh)^2.$$
--   These formulas are the system operations used in every branch of the architecture. They are defined on raw matrix data; theorems impose the source's admissibility conditions.
--
--   **Formalization Note** An auxiliary level $q$ represents order $2(q+1)$; `suzuki k` uses level $k-1$ only under $k\ge1$. The unused value at $k=0$ equals the second-order formula. No theorem uses it. All ordered products are list products with the displayed leftmost factor.
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), pp.12–13, Eqs. (2.1)–(2.2); p.15, hard-family specialization

import Definitions.Def_HamSimTradeoff_AncillaDepth_Hermitian
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth
noncomputable section

/-- Leftmost half-step is the last Hamiltonian term, as in (2.1). -/
def secondOrder {L d : ℕ} (alpha : Fin L → ℝ) (H : Fin L → Mat d) (h : ℝ) : Mat d :=
  ((List.finRange L).reverse.map (fun j => evolution (H j) (h * alpha j / 2))).prod *
  ((List.finRange L).map (fun j => evolution (H j) (h * alpha j / 2))).prod

def u (k : ℕ) : ℝ := 1 / (4 - (4 : ℝ) ^ (1 / (2 * (k : ℝ) - 1)))

/-- Level q means order 2(q+1), so recursion never calls an order zero formula. -/
def suzukiLevel {L d : ℕ} (alpha : Fin L → ℝ) (H : Fin L → Mat d) : ℕ → ℝ → Mat d
  | 0, h => secondOrder alpha H h
  | q + 1, h =>
      suzukiLevel alpha H q (u (q + 2) * h) ^ 2 *
      suzukiLevel alpha H q ((1 - 4 * u (q + 2)) * h) *
      suzukiLevel alpha H q (u (q + 2) * h) ^ 2

def suzuki {L d : ℕ} (k : ℕ) (alpha : Fin L → ℝ) (H : Fin L → Mat d) (h : ℝ) : Mat d :=
  suzukiLevel alpha H (k - 1) h

end
end HamSimTradeoff.AncillaDepth


