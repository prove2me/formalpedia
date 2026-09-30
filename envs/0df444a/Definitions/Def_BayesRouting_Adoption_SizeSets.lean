-- Prove2me | Definitions.Def_BayesRouting_Adoption_SizeSets
-- name    : BayesRouting_Adoption_SizeSets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T15:17:51.428181+00:00
-- url     : https://prove2.me/theorems/ef8f158f-f959-448e-ba55-77746d95b36c
-- title:
--   Direction z^{ij}, the flow set ℱ†, the size-vector set Λ† of (30), and the adoption condition (31)
-- statement:
--   For populations $i,j$, the direction $z^{ij}\in\mathbb R^{\mathcal I}$ has $1$ in position $i$, $-1$ in position $j$ and $0$ elsewhere.
--
--   $\mathcal F^\dagger$ is the optimal solution set of
--   $$\min\ \widehat\Phi(f)\quad\text{s.t.}\quad\text{(14a), (14b) and (14c)},\tag{28}$$
--   that is, the equilibrium route-flow problem with every information impact constraint dropped. The set of size vectors
--   $$\Lambda^\dagger=\Big\{\lambda\ :\ \sum_{i\in\mathcal I}\lambda^i=1,\ \lambda^i\ge0\ \forall i,\ \exists f^\dagger\in\mathcal F^\dagger\ \text{with}\ \widehat J^i(f^\dagger)\le\lambda^iD\ \forall i\Big\}\tag{30}$$
--   collects the size vectors for which some unconstrained optimum satisfies all information impact constraints.
--
--   In the two-stage game where travelers first choose a TIS and then play $\Gamma(\lambda)$, a size vector $\lambda$ with equilibrium $q$ satisfies the **adoption condition**
--   $$\lambda^i>0\ \Longrightarrow\ C^{i*}(\lambda)=\min_{j\in\mathcal I}C^{j*}(\lambda)\qquad\text{for all } i\in\mathcal I,\tag{31}$$
--   i.e. every TIS that is used has the lowest equilibrium population cost; such a $\lambda$ is a vector of **equilibrium adoption rates**.
--
--   These are the objects of the mission's goal: the set of equilibrium adoption rates is $\Lambda^\dagger$.
--
--   **Formalization Note** The adoption condition is a predicate of a size vector together with a strategy profile (a BWE of $\Gamma(\lambda)$ in the theorems), since the equilibrium population costs are computed from an equilibrium. The population costs are the last form of (7), meaningful also for populations with $\lambda^i=0$. The set of populations is assumed nonempty.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 156 (direction z^{ij}), p. 160 eq. (28), p. 161 eqs. (30)-(31)

import Mathlib
import Definitions.Def_BayesRouting_Adoption_Game
import Definitions.Def_BayesRouting_Adoption_Potential
import Definitions.Def_BayesRouting_Adoption_Flows

open Finset

namespace BayesRouting.Adoption

variable {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
  [∀ i, DecidableEq (T i)] {S E R : Type} [Fintype S] [Fintype E] [DecidableEq E] [Fintype R]

/-- The pairwise direction `z^{ij}` (§5.1, p. 156): `1` in the `i`-th position, `-1` in the `j`-th
position, `0` elsewhere (the zero vector when `i = j`). -/
def pairDir (i j : I) : I → ℝ :=
  Pi.single i 1 - Pi.single j 1

/-- `ℱ†` (§6.1, p. 160): the optimal solution set of problem (28),
`min Φ̂(f) s.t. (14a), (14b) and (14c)`, i.e. (OPT-ℱ) with every (IIC) constraint dropped. -/
def optFlowsUnconstrained (G : Game I T S E R) : Set (R → ((i : I) → T i) → ℝ) :=
  flowArgmin G (flowBase G)

/-- `Λ†` (30) (p. 161): the size vectors `λ` in the simplex (`∑_i λ^i = 1`, `λ^i ≥ 0`) for which
some `f† ∈ ℱ†` satisfies every (IIC) constraint of `λ`: `Ĵ^i(f†) ≤ λ^i D` for all `i`. -/
def sizeIndepSet [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) : Set (I → ℝ) :=
  {lam | lam ∈ stdSimplex ℝ I ∧
    ∃ f ∈ optFlowsUnconstrained G, ∀ i, impact G i f ≤ lam i * G.D}

/-- Condition (31) (§6.2, p. 161) at a strategy profile `q` (a BWE of `Γ(λ)` in the theorems):
every TIS with a positive share `λ^i > 0` has the lowest equilibrium population cost,
`C^{i*}(λ) = min_{j ∈ 𝓘} C^{j*}(λ)`. A size vector satisfying it is a vector of equilibrium
adoption rates. -/
def IsAdoptionEq [Nonempty I] [Nonempty R] (G : Game I T S E R) (lam : I → ℝ)
    (q : (i : I) → T i → R → ℝ) : Prop :=
  ∀ i, 0 < lam i → popCost G q i = univ.inf' univ_nonempty (fun j => popCost G q j)

end BayesRouting.Adoption


