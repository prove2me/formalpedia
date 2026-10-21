-- Prove2me | Definitions.Def_MajorityAttack_NegCost_Model
-- name    : MajorityAttack_NegCost_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:19.465894+00:00
-- url     : https://prove2.me/theorems/2ac6b353-9bf1-4798-8d0c-e364abdd4552
-- title:
--   §2–§4 — mining profit, majority attack power, net cost (3), and incentive compatibility
-- statement:
--   Let $H>0$ be total incumbent hash power, $\tau>0$ the target time between blocks, and $D=\tau H$ the puzzle difficulty. A miner using nonnegative hash power $h$ with cost $c(h)$ and expected reward $\rho$ per block has flow profit
--
--   $$P_D(h,\rho,c)=\frac{h}{D}\rho-c(h).$$
--
--   If the miner previously supplied $h^*$, the lower bound on hash power for a majority attack is $h_A=\max\{H/2,H-h^*\}$. Let $\widetilde h_A$ maximize the attack-chain flow profit over nonnegative hash powers, and let $\widetilde\rho$ be the attack-chain reward per block. For an attack of expected duration $\mathcal L$, equation (3) defines the net cost
--
--   $$C_{\rm net}=\bigl(P_D(h^*,\rho,c)-P_D(\max\{\widetilde h_A,h_A\},\widetilde\rho,c)\bigr)\mathcal L.$$
--
--   The attack is incentive compatible with no attack when its private benefit $V_{\rm attack}$ does not exceed this net cost. A no-attack equilibrium requires that inequality for every miner satisfying the participation condition $P_D(h_i^*,R+\Phi,c_i)\ge0$.
--
--   **Formalization Note** Costs are monotone and convex on nonnegative hash power; convexity strengthens the page's weak quasi-convexity for the single-peaked profit model used in §4. The attack-chain maximizer is explicitly required to exist. The equilibrium predicate records the paper's attack incentive constraints at a given allocation; consistency $\sum_i h_i^*=H$ appears in the goal theorem.
-- source:
--   Gans & Halaburda, “Zero Cost” Majority Attacks on Permissionless Blockchains, arXiv:2308.06568v1, pp. 4–8, §2–§4, eqs. (1)–(3)

import Mathlib
import Definitions.Def_MajorityAttack_NegCost_Fees

namespace MajorityAttack.NegCost

/-- Expected mining profit per unit time with difficulty `D` and per-block reward `ρ` (p. 5). -/
noncomputable def flowProfit (D ρ : ℝ) (c : ℝ → ℝ) (h : ℝ) : ℝ :=
  h / D * ρ - c h

/-- The lower bound on the attacker's hash power (p. 6). -/
noncomputable def minAttackPower (H hstar : ℝ) : ℝ :=
  max (H / 2) (H - hstar)

/-- Net attack cost in equation (3), with `D = τH` (p. 8). -/
noncomputable def netCost (τ H L ρ ρt : ℝ) (c : ℝ → ℝ)
    (htil hstar : ℝ) : ℝ :=
  (flowProfit (τ * H) ρ c hstar -
    flowProfit (τ * H) ρt c (max htil (minAttackPower H hstar))) * L

/-- The paper's monotone cost convention, strengthened to convexity on nonnegative hash powers. -/
structure CostStanding (c : ℝ → ℝ) : Prop where
  mono : MonotoneOn c (Set.Ici 0)
  convex : ConvexOn ℝ (Set.Ici 0) c

/-- An attained optimizer of the attack-chain flow profit on nonnegative hash powers. -/
def IsAttackOptimum (D ρt : ℝ) (c : ℝ → ℝ) (htil : ℝ) : Prop :=
  0 ≤ htil ∧ IsMaxOn (flowProfit D ρt c) (Set.Ici 0) htil

/-- Every active miner satisfies incentive compatibility (3). -/
def NoAttackEquilibrium {ι : Type*} (τ H L R Φ Φt : ℝ)
    (c : ι → ℝ → ℝ) (htil hstar : ι → ℝ) (V : ℝ) : Prop :=
  ∀ j, 0 ≤ flowProfit (τ * H) (R + Φ) (c j) (hstar j) →
    V ≤ netCost τ H L (R + Φ) (R + Φt) (c j) (htil j) (hstar j)

end MajorityAttack.NegCost


