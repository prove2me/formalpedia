-- Prove2me | Definitions.Def_SupplyChainCarbon_Necessity_Technology
-- name    : SupplyChainCarbon_Necessity_Technology
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:33:53.611417+00:00
-- url     : https://prove2.me/theorems/e3d197c0-04e9-400a-91d9-fdbf95f29807
-- title:
--   Convex abatement technology and own-effort profits
-- statement:
--   A supply-chain technology has positive finite firm, process and action counts, a real bound $A>0$, constants $\bar V_n$, and costs $c_n:E_n\to\mathbb R$. Each cost is differentiable and convex on its own box and strictly increases when any nonempty collection of effort coordinates increases with none decreasing. Profit depends only on the firm's own effort:
--
--   $$V_n(x)=\bar V_n-c_n(x).$$
--
--   Consequently each profit is differentiable, concave and componentwise nonincreasing on its own box. Each process footprint $f_i:E\to\mathbb R$ is differentiable, convex, componentwise nonincreasing and nonnegative on $E$. No separability between firms or actions is assumed. Zero effort is the baseline profile.
--
--   These data give the cost and production layer of the social and decentralized optimization problems. They impose neither a first-order condition nor an influence pattern. Differentiability means differentiability within the indicated domains, without any global extension requirement. The bound does not assert interiority for arbitrary payment rules; interiority of the named social optimizer is imposed separately.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, §3.1, p. 8; §3.2, p. 9

import Definitions.Def_SupplyChainCarbon_Necessity_Domains

namespace SupplyChainCarbon.Necessity

/-- The standing assumptions of §3.1, exclusively on the source domains. -/
structure Technology (N I : ℕ) (m : Fin N → ℕ) where
  firms_pos : 0 < N
  processes_pos : 0 < I
  actions_pos : ∀ n, 0 < m n
  bound : ℝ
  bound_pos : 0 < bound
  baselineProfit : Fin N → ℝ
  cost : (n : Fin N) → (Fin (m n) → ℝ) → ℝ
  cost_diff : ∀ n, DifferentiableOn ℝ (cost n) (firmBox m bound n)
  cost_convex : ∀ n, ConvexOn ℝ (firmBox m bound n) (cost n)
  cost_increasing : ∀ n, ∀ x ∈ firmBox m bound n, ∀ y ∈ firmBox m bound n,
    x ≤ y → x ≠ y → cost n x < cost n y
  footprint : Effort N m → Footprint I
  footprint_diff : ∀ i, DifferentiableOn ℝ (fun e => footprint e i) (effortBox m bound)
  footprint_convex : ∀ i, ConvexOn ℝ (effortBox m bound) (fun e => footprint e i)
  footprint_decreasing : ∀ i, AntitoneOn (fun e => footprint e i) (effortBox m bound)
  footprint_nonneg : ∀ e ∈ effortBox m bound, ∀ i, 0 ≤ footprint e i

/-- Own-effort profit, with constant operating revenues and abatement cost. -/
def profit {N I : ℕ} {m : Fin N → ℕ} (C : Technology N I m)
    (n : Fin N) (x : Fin (m n) → ℝ) : ℝ := C.baselineProfit n - C.cost n x

end SupplyChainCarbon.Necessity


