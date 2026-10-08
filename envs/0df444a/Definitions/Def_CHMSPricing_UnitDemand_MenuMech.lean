-- Prove2me | Definitions.Def_CHMSPricing_UnitDemand_MenuMech
-- name    : CHMSPricing_UnitDemand_MenuMech
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:32:17.053566+00:00
-- url     : https://prove2.me/theorems/483eb21b-6438-44e9-8972-3c07340f16b6
-- title:
--   The price-menu (multi-dimensional order-oblivious posted-price) mechanism and the multi-unit unit-demand constraint
-- statement:
--   Fix a unit-demand instance with services $J$, buyers $1,\dots,m$, a set system $\mathcal J$, prices $(p_j)_{j \in J}$ and an arrival order $\sigma$ of the buyers. The **price-menu mechanism** (§2.2, p. 5; proof of Theorem 4, p. 14) starts with $A = \emptyset$ and approaches the buyers in the order $\sigma$. When buyer $i$ arrives, it is offered the menu $\{p_j\}_{j \in J'_i}$, where
--   $$J'_i = \{ j \in J_i : A \cup \{j\} \in \mathcal J \}$$
--   is the set of its services that can still be feasibly allocated. The buyer chooses a service $j \in J'_i$ maximizing its utility $v_j - p_j$ among those with $p_j \le v_j$; the service is added to $A$ and the buyer pays $p_j$. If no service of the menu has $p_j \le v_j$, the buyer takes nothing and pays $0$. The mechanism allocates the final $A$.
--
--   For Theorem 14, with buyers $1,\dots,m$ and a finite set $K$ of items with $\mathrm{cap}(k)$ copies of item $k$, a service is a pair $(i,k)$ ("buyer $i$ receives a copy of item $k$"), owned by buyer $i$. A set of services is feasible iff it uses at most $\mathrm{cap}(k)$ copies of each item $k$ and gives each buyer at most one service: the intersection of two partition matroids on $\{1,\dots,m\} \times K$, one by item and one by buyer.
--
--   **Formalization Note** The paper says only that the buyer "chooses a service from the menu". To make the mechanism a function, ties between utility-maximizing services are broken towards the least index in a fixed enumeration of $J$; ties have probability zero under the densities of the model. A service of utility exactly $0$ is bought.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 5, §2.2 (OPMs in multi-dimensional settings); p. 14, App. B, proof of Theorem 4; p. 9, §6.1, Theorem 14 (multiple copies of items)

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_SetSystem
import Definitions.Def_CHMSPricing_UnitDemand_MultiMechanism

namespace CHMSPricing.UnitDemand

variable {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}

open Classical in
/-- The services buyer `i` may buy when it arrives with `A` already allocated, at (reported)
values `v` and prices `p`: services `j ∈ Jᵢ` on its menu `J′ᵢ` (those with `A ∪ {j} ∈ 𝒥`) that
give nonnegative utility (`p_j ≤ v_j`) and maximise its utility `v_j − p_j` among those. -/
noncomputable def menuBest (𝒥 : SetSystem J) (owner : J → Fin m) (p v : J → ℝ)
    (A : Finset J) (i : Fin m) : Finset J :=
  let C := Finset.univ.filter (fun j => owner j = i ∧ 𝒥.Feasible (insert j A) ∧ p j ≤ v j)
  C.filter (fun j => ∀ j' ∈ C, v j' - p j' ≤ v j - p j)

/-- Buyer `i`'s choice from its price menu (proof of Theorem 4, p. 14): a utility-maximising
service among those with nonnegative utility, ties broken towards the least index under the
fixed enumeration `Fintype.equivFin J`; `none` (no purchase) if no service on the menu has
`p_j ≤ v_j`. -/
noncomputable def menuChoice (𝒥 : SetSystem J) (owner : J → Fin m) (p v : J → ℝ)
    (A : Finset J) (i : Fin m) : Option J :=
  if h : (menuBest 𝒥 owner p v A i).Nonempty then
    some ((Fintype.equivFin J).symm
      (((menuBest 𝒥 owner p v A i).image (Fintype.equivFin J)).min' (h.image _)))
  else none

/-- One step of the price-menu mechanism: buyer `i` arrives with `A` already allocated and the
service it chooses (if any) is added to `A`. -/
noncomputable def menuStep (𝒥 : SetSystem J) (owner : J → Fin m) (p v : J → ℝ)
    (A : Finset J) (i : Fin m) : Finset J :=
  match menuChoice 𝒥 owner p v A i with
  | some j => insert j A
  | none => A

/-- The set of services allocated by the price-menu mechanism with arrival order `σ`
(`σ 0` arrives first) and prices `p` at reported values `v`. -/
noncomputable def menuAlloc (𝒥 : SetSystem J) (owner : J → Fin m) (σ : Equiv.Perm (Fin m))
    (p v : J → ℝ) : Finset J :=
  (List.finRange m).foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) ∅

/-- The (multi-dimensional) order-oblivious posted-price mechanism of the proof of Theorem 4
(§2.2, p. 5; App. B, p. 14): buyers arrive in the order `σ`; each buyer `i` is offered the
price menu `{p_j}_{j ∈ J′ᵢ}` over the services of `Jᵢ` that can still be feasibly allocated,
chooses a service (`menuChoice`), gets it and pays its price `p_j`; a buyer who buys nothing
pays `0`. -/
noncomputable def menuMech (𝒥 : SetSystem J) (owner : J → Fin m) (σ : Equiv.Perm (Fin m))
    (p : J → ℝ) : MultiMechanism J m where
  alloc v := menuAlloc 𝒥 owner σ p v
  pay v i := ∑ j ∈ (menuAlloc 𝒥 owner σ p v).filter (fun j => owner j = i), p j

/-- The feasibility constraint of Theorem 14 (§6.1, p. 9): `m` unit-demand buyers and items
`K`, with `cap k` copies of item `k`. A service is a pair `(i, k)` (buyer `i` gets a copy of
item `k`), and a set of services is feasible iff it uses at most `cap k` copies of each item `k`
and gives each buyer at most one service. It is the intersection of two partition matroids
on `Fin m × K` (by item, and by buyer). -/
def unitDemandSystem {K : Type*} [Fintype K] [DecidableEq K] (cap : K → ℕ) :
    SetSystem (Fin m × K) :=
  twoPartitionSystem Prod.snd cap Prod.fst (fun _ => 1)

end CHMSPricing.UnitDemand


