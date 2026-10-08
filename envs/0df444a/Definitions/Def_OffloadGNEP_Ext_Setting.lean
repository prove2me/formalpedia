-- Prove2me | Definitions.Def_OffloadGNEP_Ext_Setting
-- name    : OffloadGNEP_Ext_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:40:34.731759+00:00
-- url     : https://prove2.me/theorems/6e1a01fc-1358-482c-bf8b-fd0ace4a1009
-- title:
--   The offloading GNEP and its extended cloudlet-pricing game
-- statement:
--   A user allocates one unit of work among local execution, a cloudlet, and a remote cloud. The set $\widetilde K_u$ imposes nonnegative shares, a unit-sum equation, a bound $\chi$ on the total offloaded share, and the user's power budget. The product $\prod_u\widetilde K_u$ contains the private constraints. If $L(x)=n^{-1}\sum_u\delta_u x_{u,\mathrm{clet}}$, the shared constraint is $\Omega=\{x:L(x)\le U_{\max}\}$ and the original feasible set is $K=(\prod_u\widetilde K_u)\cap\Omega$.
--
--   The user's cost is the closed-form $\lambda_uR_u$ on p. 10, and $F$ is the displayed stack of partial gradients on p. 11. The extended game adds a manager's price $\rho\ge0$. Users minimize their cost plus $\rho(\delta_u/n)x_{u,\mathrm{clet}}$ over $\widetilde K_u$; the manager maximizes $\rho(L(x)-U_{\max})$. Its Nash equilibrium predicate states all $N+1$ best-response conditions. The associated VI has map $F_e(x,\rho)=(F(x)+\operatorname{price}(\rho),U_{\max}-L(x))$ and set $K_e=(\prod_u\widetilde K_u)\times\mathbb R_+$.
--
--   The definitions make the shared constraint and its price explicit so that the theorem can compare the two games.
--
--   **Formalization Note** The cost and $F$ are total Lean functions; their denominators are positive on $K$, and on the full product only under the stated load bound. User deviations in the extended game range over $\widetilde K_u$, without the shared constraint.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), pp. 10–11, (10)–(15), definitions of K and F; p. 15, extended game, F_e, K_e

import Mathlib
import Definitions.Def_OffloadGNEP_Ext_VI

namespace OffloadGNEP.Ext

noncomputable section

/-- Cloudlet utilization: the left side of (11). -/
def load {N : ℕ} (P : Params N) (x : Fin N → OffloadGNEP.Exist.Tier → ℝ) : ℝ :=
  (1 / (P.n : ℝ)) * ∑ v, P.delta v * x v .clet

/-- The denominator of the cloudlet response-time term. -/
def D {N : ℕ} (P : Params N) (x : Fin N → OffloadGNEP.Exist.Tier → ℝ) : ℝ :=
  1 - load P x

/-- User u's private feasible set, without the shared cloudlet constraint. -/
def Ktil {N : ℕ} (P : Params N) (u : Fin N) : Set (OffloadGNEP.Exist.Tier → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ y .m + y .clet + y .cloud = 1 ∧
    y .clet + y .cloud ≤ P.chi ∧
    P.alpha u * P.Pm u * y .m +
      P.beta u * P.Pt u * (y .clet + y .cloud) ≤ P.Pmax u}

/-- The product of private feasible sets. -/
def Kprod {N : ℕ} (P : Params N) : Set (Fin N → OffloadGNEP.Exist.Tier → ℝ) :=
  {x | ∀ u, x u ∈ Ktil P u}

/-- The shared utilization constraint (11). -/
def Omega {N : ℕ} (P : Params N) : Set (Fin N → OffloadGNEP.Exist.Tier → ℝ) :=
  {x | load P x ≤ P.Umax}

/-- The feasible set of the original variational inequality. -/
def K {N : ℕ} (P : Params N) : Set (Fin N → OffloadGNEP.Exist.Tier → ℝ) :=
  Kprod P ∩ Omega P

/-- The closed form of λ_u R_u on p. 10. Its denominators are positive on K. -/
def cost {N : ℕ} (P : Params N) (u : Fin N)
    (x : Fin N → OffloadGNEP.Exist.Tier → ℝ) : ℝ :=
  P.alpha u * x u .m / (1 - P.alpha u * x u .m) +
    P.beta u * x u .clet + P.gamma u * x u .cloud +
    P.delta u * x u .clet / D P x

/-- The displayed, stacked partial-gradient map F on p. 11. -/
def F {N : ℕ} (P : Params N)
    (x : Fin N → OffloadGNEP.Exist.Tier → ℝ) : Fin N → OffloadGNEP.Exist.Tier → ℝ :=
  fun u i => match i with
    | .m => P.alpha u / (1 - P.alpha u * x u .m) ^ 2
    | .clet => P.beta u + P.delta u *
        (1 - (1 / (P.n : ℝ)) *
          ∑ v ∈ Finset.univ.erase u, P.delta v * x v .clet) / D P x ^ 2
    | .cloud => P.gamma u

/-- The charge per unit of user u's cloudlet allocation. -/
def price {N : ℕ} (P : Params N) (ρ : ℝ) : Fin N → OffloadGNEP.Exist.Tier → ℝ :=
  fun u i => if i = OffloadGNEP.Exist.Tier.clet then ρ * (P.delta u / (P.n : ℝ)) else 0

/-- Nash equilibrium of the N users and the cloudlet manager (p. 15). -/
def IsExtNE {N : ℕ} (P : Params N)
    (xb : Fin N → OffloadGNEP.Exist.Tier → ℝ) (ρb : ℝ) : Prop :=
  (∀ u, xb u ∈ Ktil P u) ∧ 0 ≤ ρb ∧
    (∀ u, ∀ y ∈ Ktil P u,
      cost P u xb + ρb * (P.delta u / (P.n : ℝ) * xb u .clet) ≤
        cost P u (Function.update xb u y) +
          ρb * (P.delta u / (P.n : ℝ) * y .clet)) ∧
    ∀ ρ, 0 ≤ ρ →
      ρ * (load P xb - P.Umax) ≤ ρb * (load P xb - P.Umax)

/-- The VI map of the extended game (p. 15). -/
def Fe {N : ℕ} (P : Params N)
    (p : (Fin N → OffloadGNEP.Exist.Tier → ℝ) × ℝ) : (Fin N → OffloadGNEP.Exist.Tier → ℝ) × ℝ :=
  (F P p.1 + price P p.2, -load P p.1 + P.Umax)

/-- The product feasible set of the extended game. -/
def Ke {N : ℕ} (P : Params N) : Set ((Fin N → OffloadGNEP.Exist.Tier → ℝ) × ℝ) :=
  {p | p.1 ∈ Kprod P ∧ 0 ≤ p.2}

end
end OffloadGNEP.Ext


