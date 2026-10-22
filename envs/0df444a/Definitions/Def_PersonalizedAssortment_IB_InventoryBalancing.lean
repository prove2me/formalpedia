-- Prove2me | Definitions.Def_PersonalizedAssortment_IB_InventoryBalancing
-- name    : PersonalizedAssortment_IB_InventoryBalancing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T01:44:34.07398+00:00
-- url     : https://prove2.me/theorems/5eeefb1c-8158-44c5-acb9-9c1168635bce
-- title:
--   The inventory-balancing algorithm, the inventory process and its expected revenue
-- statement:
--   Let $c_{\min}=\min_i c_i$. Write $I_i$ for the remaining inventory of product $i$, and let $\Psi$ be a penalty function. For a customer with choice model $\varphi$, the **inventory-balancing index** of an assortment $S$ is
--   $$\sum_{i\in S}\Psi(I_i/c_i)\,r_i\,\varphi_i(S).$$
--   An **inventory-balancing selection rule** assigns to each period $t$ and each inventory vector $I$ an assortment $S^t(I)\in\mathcal S$ with two properties:
--
--   1. $S^t(I)$ maximizes the index of $\varphi^{z_t}$ over $\mathcal S$;
--   2. among the maximizers, $S^t(I)$ has the fewest products.
--
--   **Inventory dynamics.** The inventory starts at $I^0=c$. In period $t$ the assortment $S^t=S^t(I^{t-1})$ is offered. The customer buys product $i\in S^t$ with probability $\varphi_i^{z_t}(S^t)$, and then $I_i^t=\max\{I_i^{t-1}-1,0\}$ while the other coordinates are unchanged. With probability $1-\sum_{i\in S^t}\varphi_i^{z_t}(S^t)$ the customer buys nothing and $I^t=I^{t-1}$. Choices in different periods are independent given the inventory. $\mathbb E[f(I^t)]$ denotes the expectation of a function of the inventory at the end of period $t$ under this process.
--
--   **Expected revenue (Definition 1).** A sale of product $i$ earns $r_i$ only when that product is still in stock. The expected revenue of the rule over the horizon is therefore
--   $$\mathrm{Rev}=\sum_{t=1}^T\mathbb E\Big[\sum_{i=1}^n r_i\,\varphi_i^{z_t}\big(S^t(I^{t-1})\big)\,\mathbb 1[I_i^{t-1}>0]\Big].$$
--   The item also defines the dual certificate of the paper's proof. The first variable is $\lambda^t=\sum_{i\in S^t}r_i\Psi(I_i^{t-1}/c_i)\varphi_i^{z_t}(S^t)$, a function of $I^{t-1}$. The second is $\theta_i=r_i(1-\Psi(I_i^T/c_i))$, a function of the final inventory $I^T$.
--
--   **Formalization Note** Periods are indexed from $0$. Inventories are natural-number vectors, and truncated subtraction implements $\max\{I-1,0\}$. The expectation is defined recursively by conditioning on the previous inventory: $\mathbb E[f(I^0)]=f(c)$ and $\mathbb E[f(I^{t})]=\mathbb E[g(I^{t-1})]$, where $g(I)$ is the one-step conditional expectation of $f$. It is a finite sum, and no measure theory is involved. The selection rule is a deterministic function of the period and the current inventory.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1536, Definition 1; p. 1537, Section 3 (inventory dynamics, boxed algorithm, tie-breaking rule); p. 1538, Theorem 1 (c_min); p. 1548, Section A.3 (dual solution)

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel

namespace PersonalizedAssortment.IB

variable {n : ℕ} {Z : Type*} {T : ℕ}

/-- `c_min = min_{i=1,…,n} c_i` (Theorem 1, p. 1538); needs at least one product. -/
def cMin (c : Fin n → ℕ) (hn : 0 < n) : ℕ :=
  Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ c

/-- The inventory-balancing index of an assortment `S` (§3, p. 1537), for a customer whose choice
model is `φ` and remaining inventories `I`:
`∑_{i ∈ S} Ψ(I_i / c_i) r_i φ_i(S)`. -/
noncomputable def ibIndex (Ψ : ℝ → ℝ) (r : Fin n → ℝ) (c : Fin n → ℕ) (φ : ChoiceModel n)
    (I : Fin n → ℕ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, Ψ ((I i : ℝ) / (c i : ℝ)) * r i * φ.prob S i

/-- `sel` is an inventory-balancing selection rule with penalty function `Ψ` (the boxed algorithm
and the tie-breaking sentence after it, p. 1537). Periods are indexed by `Fin T` (period `t` of
the paper is `t - 1` here) and `sel t I` is the assortment offered in that period when the
remaining inventories at the start of the period are `I` (the paper's `I^{t-1}`). For every period
and every inventory vector:
* `sel t I ∈ 𝒮`;
* `sel t I` maximizes `S ↦ ∑_{i ∈ S} Ψ(I_i/c_i) r_i φ_i^{z_t}(S)` over `S ∈ 𝒮`;
* among the maximizers, `sel t I` has the smallest number of products. -/
def IsIBRule (Ψ : ℝ → ℝ) (r : Fin n → ℝ) (c : Fin n → ℕ) (𝒮 : Finset (Finset (Fin n)))
    (φ : Z → ChoiceModel n) (z : Fin T → Z) (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) :
    Prop :=
  ∀ (t : Fin T) (I : Fin n → ℕ),
    sel t I ∈ 𝒮 ∧
    (∀ S ∈ 𝒮, ibIndex Ψ r c (φ (z t)) I S ≤ ibIndex Ψ r c (φ (z t)) I (sel t I)) ∧
    (∀ S ∈ 𝒮, ibIndex Ψ r c (φ (z t)) I S = ibIndex Ψ r c (φ (z t)) I (sel t I) →
      (sel t I).card ≤ S.card)

/-- One step of the inventory dynamics (§3, p. 1537), as a conditional expectation: if the
inventories are `I` and the assortment `S` is offered to a customer with choice model `φ`, the
customer buys product `i ∈ S` with probability `φ_i(S)`, after which the inventory of `i` becomes
`max{I_i - 1, 0}` (natural-number subtraction) and the others are unchanged, and buys nothing
with probability `1 - ∑_{i ∈ S} φ_i(S)`, after which `I` is unchanged. `stepExpect φ S I f` is
the expected value of `f` at the next inventory vector. -/
noncomputable def stepExpect (φ : ChoiceModel n) (S : Finset (Fin n)) (I : Fin n → ℕ)
    (f : (Fin n → ℕ) → ℝ) : ℝ :=
  (1 - ∑ i ∈ S, φ.prob S i) * f I +
    ∑ i ∈ S, φ.prob S i * f (Function.update I i (I i - 1))

/-- `expectInv φ z sel c t ht f = 𝔼[f(I^t)]`, the expectation of `f` at the inventory vector
`I^t` at the end of the paper's period `t` (so `I^0 = c`), when in each period the assortment
`sel` is offered and the customers of types `z` choose independently according to their choice
models. It is defined by conditioning on `I^{t-1}`:
`𝔼[f(I^0)] = f(c)` and `𝔼[f(I^{t+1})] = 𝔼[g(I^t)]` with
`g(I) = 𝔼[f(I^{t+1}) | I^t = I] = stepExpect (φ z_{t+1}) (S^{t+1}(I)) I f`. -/
noncomputable def expectInv (φ : Z → ChoiceModel n) (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (c : Fin n → ℕ) :
    (t : ℕ) → t ≤ T → ((Fin n → ℕ) → ℝ) → ℝ
  | 0, _, f => f c
  | t + 1, h, f =>
      expectInv φ z sel c t (Nat.le_of_succ_le h)
        (fun I => stepExpect (φ (z ⟨t, h⟩)) (sel ⟨t, h⟩ I) I f)

/-- `Rev(sel, {z_t})` (Definition 1, p. 1536) for the algorithm that offers `sel`: the expected
revenue collected over the `T` periods. In the period with index `t` (the paper's period `t + 1`)
the inventories are `I = I^t`, the offer is `sel t I`, and product `i` earns `r_i` exactly when the
customer picks it and it is still in stock (`0 < I_i`), which happens with probability
`φ_i^{z}(sel t I)`. -/
noncomputable def ibRevenue (r : Fin n → ℝ) (c : Fin n → ℕ) (φ : Z → ChoiceModel n)
    (z : Fin T → Z) (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) : ℝ :=
  ∑ t : Fin T, expectInv φ z sel c t.val t.isLt.le
    (fun I => ∑ i : Fin n, r i * (φ (z t)).prob (sel t I) i * (if 0 < I i then 1 else 0))

/-- The dual variable `λ^t = ∑_{i ∈ S^t} r_i Ψ(I_i^{t-1}/c_i) φ_i^{z_t}(S^t)` of §A.3, p. 1548, as
a function of the inventories `I = I^{t-1}` at the start of the period with index `t`
(`S^t = sel t I`). -/
noncomputable def lamIB (Ψ : ℝ → ℝ) (r : Fin n → ℝ) (c : Fin n → ℕ) (φ : Z → ChoiceModel n)
    (z : Fin T → Z) (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (t : Fin T)
    (I : Fin n → ℕ) : ℝ :=
  ibIndex Ψ r c (φ (z t)) I (sel t I)

/-- The dual variable `θ_i = r_i (1 - Ψ(I_i^T / c_i))` of §A.3, p. 1548, as a function of the
final inventories `I = I^T`. -/
noncomputable def thetaIB (Ψ : ℝ → ℝ) (r : Fin n → ℝ) (c : Fin n → ℕ) (I : Fin n → ℕ)
    (i : Fin n) : ℝ :=
  r i * (1 - Ψ ((I i : ℝ) / (c i : ℝ)))

end PersonalizedAssortment.IB


