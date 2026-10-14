-- Prove2me | Definitions.Def_CommonOwnership_Governance_DiversionModel
-- name    : CommonOwnership_Governance_DiversionModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:44.820513+00:00
-- url     : https://prove2.me/theorems/e4aa4e0a-f506-4334-a2f2-cefcabd1b20e
-- title:
--   §7.1, (38), (42), (43), (45), PDF pp. 30–31 — diversion by the blockholder: deadweight loss, optimal diversion, joint surplus
-- statement:
--   This file sets up the variant of §7.1, in which managers no longer divert profits and the blockholder himself appropriates a fraction $a\in[0,1]$ of his firm's profit at a deadweight loss $D(a)$ per unit of profit.
--
--   **Blockholder's problem (38).** A blockholder who has sold the stake $s\in[0,\beta]$ to the investor earns, per unit of profit,
--   $$a+(\beta-s)(1-a)-D(a),$$
--   plus the price of the stake, which is fixed when $a$ is chosen. A function $a^*$ is an *optimal diversion rule* if, for every $s\in[0,\beta]$, $a^*(s)\in[0,1]$ maximizes this objective over $a\in[0,1]$. The quadratic specification (45) is $D(a)=\tfrac12\varphi a^2$.
--
--   **Joint surplus (42)–(43).** The large shareholders' payoff per unit of profit is
--   $$\nu^*(s)=a^*(s)+\beta[1-a^*(s)]-D[a^*(s)],$$
--   and the joint surplus is $S(s)=\nu^*(s)\,P(\lambda(s))$, with $\lambda$ the common-ownership weight (17) and $P$ industry profit as a function of $\lambda$.
--
--   These objects state Proposition 9: better corporate governance (larger $\varphi$) leads to more common ownership.
--
--   **Formalization Note** `divCost φ a` is (45), `divertObj D β s a` the objective (38) without the stake's price, `IsOptDiversion D β adiv` the optimality predicate on $s\in[0,\beta]$, `nuDiv` is (43) and `jointSurplusDiv` is (42). Equilibrium ownership reuses `IsEqOwnership` and `lam` from `CommonOwnership.Governance.Model`. The printed closed form (47) is not used.
-- source:
--   Denicolò & Panunzi, Common Ownership, Competition, and Corporate Governance, ECGI Finance Working Paper 927/2023 (SSRN 4523644, July 24, 2023; Management Science DOI 10.1287/mnsc.2023.03467), pp. 27–28 (PDF pp. 30–31), §7.1, (38), (42), (43), (45)

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model

namespace CommonOwnership.Governance

/-- (45), p. 28: the quadratic deadweight loss of diversion, `D(a) = ½ φ a²`. -/
noncomputable def divCost (φ a : ℝ) : ℝ := 1 / 2 * φ * a ^ 2

/-- (38), p. 27: the blockholder's payoff `a + (β − s)(1 − a) − D(a)` per unit of profit, without
the price `Pᵢ(sᵢ)` of the stake (fixed when `a` is chosen); `a` is the diverted fraction. -/
def divertObj (D : ℝ → ℝ) (β s a : ℝ) : ℝ := a + (β - s) * (1 - a) - D a

/-- §7.1, p. 27: `adiv s` is the blockholder's optimal diversion: for every stake `s ∈ [0, β]` sold
to the investor, `adiv s ∈ [0, 1]` maximizes `divertObj D β s` over `a ∈ [0, 1]`. -/
def IsOptDiversion (D : ℝ → ℝ) (β : ℝ) (adiv : ℝ → ℝ) : Prop :=
  ∀ s ∈ Set.Icc (0:ℝ) β, adiv s ∈ Set.Icc (0:ℝ) 1 ∧
    ∀ a ∈ Set.Icc (0:ℝ) 1, divertObj D β s a ≤ divertObj D β s (adiv s)

/-- (43), p. 28: `ν*(s) = a*(s) + β [1 − a*(s)] − D[a*(s)]`. -/
def nuDiv (D adiv : ℝ → ℝ) (β s : ℝ) : ℝ := adiv s + β * (1 - adiv s) - D (adiv s)

/-- (42), p. 28: the joint surplus `S = ν* Π*` of the §7.1 variant, with `Π*(s) = P(λ(s))`. -/
noncomputable def jointSurplusDiv (D adiv P : ℝ → ℝ) (θ β s : ℝ) : ℝ :=
  nuDiv D adiv β s * P (lam θ β s)

end CommonOwnership.Governance


