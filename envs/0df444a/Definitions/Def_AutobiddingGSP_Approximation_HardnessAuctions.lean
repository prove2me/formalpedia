-- Prove2me | Definitions.Def_AutobiddingGSP_Approximation_HardnessAuctions
-- name    : AutobiddingGSP_Approximation_HardnessAuctions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:27:37.9742+00:00
-- url     : https://prove2.me/theorems/16fd547c-84a0-4da2-88af-be9b85eb7125
-- title:
--   The auctions of the budget and ROI reductions, and the decodings (6) and (9)
-- statement:
--   $a=\lceil2/(1-\gamma)\rceil$.
--
--   **Budget (§7.1).** $c=a^{36}$, $D=22$, $k=a^{12}c^{D}$. Gate $g_I$: NOT/NOR at level $4I+1$; NPURIFY at levels $4I+1$ (output $v$) and $4I+3$ (output $w$). At each level the output bidder gets $k$ items of value $c^{\ell+2/3}$ and budget $kc^{\ell+1/12}$; every input occurrence gets one item $c^{\ell+1/3}$ (level $4I+1$) or $c^{\ell+2/9}$ (level $4I+3$) and budget $c^{\ell-1}$. A guard has items $c^t$, $t\in[T]$, $T=4m+4$, and budget $aTc^T$. $K=M$, all CTRs $1$. Decoding (6): $x[v]=0$ if $\alpha_v\le c^{-1/3}$, $1$ if $\alpha_v=1$, else $\bot$.
--
--   **ROI (§8.1).** $c=a^{128}$, $D=11$, $k=4a^{17}c^D$. NOT/NOR at level $2I$; NPURIFY at $2I$ and $2I+1$. Output block: $k$ items $a^{64}c^\ell$; input items $a^{16}c^\ell$ (level $2I$) or $a^4c^\ell$ (level $2I+1$). Two guards, each with $c,c^2,\dots,c^{2m+2},ac^{2m+2}$. $K=M$, CTRs $1$, cap $A_0$ of the instance. Decoding (9): $x[v]=0$ if $\alpha_v\le a^{24}$, $1$ if $\alpha_v\ge a^{64}$, else $\bot$.
--
--   All values are integer powers of $a$; vertices are bidders $0,\dots,n-1$, guards follow.
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], §7.1, pp. 30–31; §7.3 eq. (6), p. 34; §8.1, pp. 36–37; §8.3 eq. (9), p. 40

import Mathlib
import Definitions.Def_AutobiddingGSP_Approximation_Model
import Definitions.Def_AutobiddingGSP_Approximation_PureCircuit

namespace AutobiddingGSP.Approximation

/-- The constant `a = ⌈2 / ε⌉`, `ε = 1 − γ`, of both reductions (§7, p. 30; §8, p. 36). -/
noncomputable def paramA (γ : ℝ) : ℕ := ⌈2 / (1 - γ)⌉₊

/-- A list of rationals in nonincreasing order. -/
def sortDescQ (l : List ℚ) : List ℚ := l.mergeSort (fun x y => decide (y ≤ x))

/-! ### The budget reduction (§7.1, pp. 30–31)

With `c = a^36`, every value `c^{ℓ + θ/36}` is the integer `a^{36ℓ + θ}`. -/

/-- **The occupied levels of the budget construction** (§7.1, p. 31), one entry
`(ℓ, output bidder, input bidders, θ)` per level, where the input items at level `ℓ` have value
`c^{ℓ + θ/36}`: gate `g_I` (Lean position `I − 1`) of type `NOT(u; w)` or `NOR(u, v; w)` uses level
`4I + 1` with inputs `u` (and `v`, repeated if `u = v`), output `w` and `θ = 12` (offset `1/3`);
`NPURIFY(u; v, w)` uses level `4I + 1` (input `u`, output `v`, `θ = 12`) and level `4I + 3`
(input `u`, output `w`, `θ = 8`, offset `2/9`). -/
def budgetLevels (C : PCInstance) : List (ℕ × ℕ × List ℕ × ℕ) :=
  (C.gates.mapIdx (fun i g => match g with
    | PCGate.not u w => [(4 * (i + 1) + 1, w, [u], 12)]
    | PCGate.nor u v w => [(4 * (i + 1) + 1, w, [u, v], 12)]
    | PCGate.npurify u v w => [(4 * (i + 1) + 1, v, [u], 12), (4 * (i + 1) + 3, w, [u], 8)])).flatten

/-- `k = a^12 c^D` with `c = a^36`, `D = 4d + 2 = 22` (`d = 5`) (§7, p. 30). -/
def budgetK (a : ℕ) : ℕ := a ^ 12 * (a ^ 36) ^ 22

/-- The item values of the real bidder of vertex `v` (§7.1, p. 31): at every occupied level `ℓ`,
its output block of `k` items of value `c^{ℓ + 2/3} = a^{36ℓ + 24}` if `v` is that level's output,
and one item of value `c^{ℓ + θ/36}` per occurrence of `v` among that level's inputs. -/
def budgetBidderItems (a : ℕ) (C : PCInstance) (v : ℕ) : List ℚ :=
  (budgetLevels C).flatMap (fun e =>
    (if e.2.1 = v then List.replicate (budgetK a) ((a : ℚ) ^ (36 * e.1 + 24)) else []) ++
      (e.2.2.1.filter (fun u => u = v)).map (fun _ => (a : ℚ) ^ (36 * e.1 + e.2.2.2)))

/-- The budget of the real bidder of vertex `v` (§7.1, p. 31): `k c^{ℓ_v + 1/12} = k a^{36ℓ_v + 3}`
for its output block, plus `c^{ℓ − 1} = a^{36ℓ − 36}` per input occurrence at level `ℓ`. -/
def budgetBidderBudget (a : ℕ) (C : PCInstance) (v : ℕ) : ℚ :=
  ((budgetLevels C).map (fun e =>
    (if e.2.1 = v then (budgetK a : ℚ) * (a : ℚ) ^ (36 * e.1 + 3) else 0) +
      ((e.2.2.1.count v : ℕ) : ℚ) * (a : ℚ) ^ (36 * e.1 - 36))).sum

/-- **The auction of the budget reduction** (§7.1, pp. 30–31) built from a Pure-Circuit instance
with `m` gates and the constant `a`: one real bidder per vertex `v = 0, …, n − 1`
(`budgetBidderItems`, `budgetBidderBudget`), then a guard bidder with one item of value
`c^t = a^{36t}` for each `t ∈ [T]`, `T = 4m + 4`, and budget `a T c^T`. Every bidder's values are
listed in nonincreasing order; the number of slots equals the number of items and every
click-through rate is one. -/
def budgetAuction (a : ℕ) (C : PCInstance) : Auction :=
  let Tg := 4 * C.gates.length + 4
  let vals := (List.range C.nV).map (fun v => sortDescQ (budgetBidderItems a C v)) ++
    [sortDescQ ((List.range' 1 Tg).map (fun t => (a : ℚ) ^ (36 * t)))]
  { vals := vals
    K := vals.flatten.length
    ctr := List.replicate vals.flatten.length 1
    budgets := (List.range C.nV).map (budgetBidderBudget a C) ++
      [(a : ℚ) * (Tg : ℚ) * (a : ℚ) ^ (36 * Tg)] }

/-- **The decoding (6)** of the budget reduction (§7.3, p. 34): `x[v] = 0` if `α_v ≤ c^{−1/3}`
(`= a^{−12}`), `x[v] = 1` if `α_v = 1`, and `x[v] = ⊥` otherwise. -/
noncomputable def budgetDecode (a : ℕ) (α : ℕ → ℝ) (v : ℕ) : Tri := by
  classical
  exact if α v ≤ ((a : ℝ) ^ 12)⁻¹ then Tri.zero else if α v = 1 then Tri.one else Tri.bot

/-! ### The ROI reduction (§8.1, pp. 36–37)

With `c = a^128`, every value is an integer power of `a`. -/

/-- **The occupied levels of the ROI construction** (§8.1, p. 36), one entry
`(ℓ, output bidder, input bidders, θ)` per level, where the input items at level `ℓ` have value
`a^θ c^ℓ`: `NOT`/`NOR` gate `g_I` uses level `2I` with `θ = 16`; `NPURIFY(u; v, w)` uses level `2I`
(output `v`, `θ = 16`) and level `2I + 1` (output `w`, `θ = 4`). -/
def roiLevels (C : PCInstance) : List (ℕ × ℕ × List ℕ × ℕ) :=
  (C.gates.mapIdx (fun i g => match g with
    | PCGate.not u w => [(2 * (i + 1), w, [u], 16)]
    | PCGate.nor u v w => [(2 * (i + 1), w, [u, v], 16)]
    | PCGate.npurify u v w => [(2 * (i + 1), v, [u], 16), (2 * (i + 1) + 1, w, [u], 4)])).flatten

/-- `k = 4 a^17 c^D` with `c = a^128`, `D = 2d + 1 = 11` (§8, p. 36). -/
def roiK (a : ℕ) : ℕ := 4 * a ^ 17 * (a ^ 128) ^ 11

/-- The item values of the real bidder of vertex `v` (§8.1, p. 36): at every occupied level `ℓ`,
its output block of `k` items of value `a^64 c^ℓ` if `v` is that level's output, and one item of
value `a^θ c^ℓ` per occurrence of `v` among that level's inputs. -/
def roiBidderItems (a : ℕ) (C : PCInstance) (v : ℕ) : List ℚ :=
  (roiLevels C).flatMap (fun e =>
    (if e.2.1 = v then List.replicate (roiK a) ((a : ℚ) ^ (64 + 128 * e.1)) else []) ++
      (e.2.2.1.filter (fun u => u = v)).map (fun _ => (a : ℚ) ^ (e.2.2.2 + 128 * e.1)))

/-- The value list (7) of each guard (§8.1, p. 36): `c, c², …, c^{2m+2}, a c^{2m+2}`. -/
def roiGuardItems (a : ℕ) (C : PCInstance) : List ℚ :=
  (List.range' 1 (2 * C.gates.length + 2)).map (fun t => (a : ℚ) ^ (128 * t)) ++
    [(a : ℚ) * (a : ℚ) ^ (128 * (2 * C.gates.length + 2))]

/-- **The auction of the ROI reduction** (§8.1, pp. 36–37): one real bidder per vertex
`v = 0, …, n − 1` (`roiBidderItems`), then two guard bidders with the value list (7). Every bidder's
values are listed in nonincreasing order; the number of slots equals the number of items, every
click-through rate is one, and there are no budgets. The cap is the instance's own `A₀`
(`Auction.capA0`, which `IsApproxABER` uses). -/
def roiAuction (a : ℕ) (C : PCInstance) : Auction :=
  let vals := (List.range C.nV).map (fun v => sortDescQ (roiBidderItems a C v)) ++
    [sortDescQ (roiGuardItems a C), sortDescQ (roiGuardItems a C)]
  { vals := vals
    K := vals.flatten.length
    ctr := List.replicate vals.flatten.length 1
    budgets := [] }

/-- **The decoding (9)** of the ROI reduction (§8.3, p. 40): `x[v] = 0` if `α_v ≤ a^24`,
`x[v] = 1` if `α_v ≥ a^64`, and `x[v] = ⊥` otherwise. -/
noncomputable def roiDecode (a : ℕ) (α : ℕ → ℝ) (v : ℕ) : Tri := by
  classical
  exact if α v ≤ (a : ℝ) ^ 24 then Tri.zero else if (a : ℝ) ^ 64 ≤ α v then Tri.one else Tri.bot

end AutobiddingGSP.Approximation


