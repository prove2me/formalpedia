-- Prove2me | Definitions.Def_LinearChoresCLS_CompletedMarket
-- name    : LinearChoresCLS_CompletedMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:49:03.945219+00:00
-- url     : https://prove2.me/theorems/3e933962-9d54-4ac2-a45c-259b63663c3b
-- title:
--   The completed market $f(I)$ with $L$-layer Maximum–Minimum gadget chains
-- statement:
--   For every pair $0\le j<j'\le n$ of basic chores the market contains an $L$-layer chain of Maximum–Minimum gadgets. Layer $k$ of chain $(j,j')$ adds agents $a^{\max}_{(j,j'),k},a^{(1)}_{(j,j'),k},a^{(2)}_{(j,j'),k}$ with earning requirement $B_{(j,j'),k}$ and output chores $p^{+}_{(j,j'),k},p^{-}_{(j,j'),k}$ with supply $S_{(j,j'),k}$. The ordered inputs of layer $0$ are $(j,j')$; those of layer $k\ge1$ are $(p^+_{(j,j'),k-1},p^-_{(j,j'),k-1})$. The basic agents and chores have
--   $$
--   B_{a_j}=1-\frac32\sum_{k<L}\sum_{j'\ne j}B_{(j,j'),k}-\frac{\alpha}{t}c_j,\qquad S_j=1-\sum_{k<L}\sum_{j'\ne j}S_{(j,j'),k}.
--   $$
--   Disutilities: $a_j$ has $1$ on $\{0,j\}$, $1+t$ on the other basic chores and $(1+t)^2$ on auxiliary chores; $a^{\max}$ has $q_k$ on both inputs and $1$ on the plus output; $a^{(1)}$ has $1/q_k$ on the first input and $1$ on the minus output; $a^{(2)}$ has $1/q_k$ on the second input and $1$ on the minus output; every other entry is $(1+t)^2$. The entries other than $(1+t)^2$ are the agent's **designated choices**. The completed market $f(I)$ uses $t$ and $L$ from (7.1). Also defined: the set $N^\sigma_{\mathrm{out},k}$ of agents outside a gadget who use its output $p^\sigma$, and $p_{\max}$, $p_{\min}$.
--
--   **Formalization Note** Agents are `Fin (n+1) ⊕ (Pair n × Fin L × Fin 3)` (roles $0,1,2$ = $a^{\max},a^{(1)},a^{(2)}$), chores are `Fin (n+1) ⊕ (Pair n × Fin L × Bool)` (`true` = plus). `chainMarket` takes a general real $t$ and $L$; `completedMarket` is its instance at (7.1). The sums over $j'\ne j$ range over the pairs incident to $j$ (symmetric convention). "Uses" is $z_{a\ell}>0$.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Definition 6.1, p.18; Definition 6.4, p.21; Section 7.1 (i)–(iv), pp.30–31; Lemma 7.2, p.33

import Mathlib
import Definitions.Def_LinearChoresCLS_Psi
import Definitions.Def_LinearChoresCLS_Params

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- The agents of the completed market (arXiv:2611.06589, held version sha256 85d34a9e…,
Section 7.1 (i), p.31): the basic agents `a_j`, `j = 0, …, n` (`Sum.inl j`), and for every pair
`0 ≤ j < j′ ≤ n` and layer `0 ≤ k < L` the three gadget agents `a^max_{(j,j′),k}`,
`a^{(1)}_{(j,j′),k}`, `a^{(2)}_{(j,j′),k}` (`Sum.inr (π, k, 0)`, `(π, k, 1)`, `(π, k, 2)`). -/
abbrev Agent (n L : ℕ) := Fin (n + 1) ⊕ (Pair n × Fin L × Fin 3)

/-- The chores of the completed market (arXiv:2611.06589, Section 7.1 (i), p.31): the basic chores
`0, …, n` (`Sum.inl j`) and, for every pair `π = (j, j′)` and layer `k < L`, the plus and minus
output chores `p^+_{(j,j′),k}` (`Sum.inr (π, k, true)`) and `p^−_{(j,j′),k}`
(`Sum.inr (π, k, false)`). -/
abbrev Chore (n L : ℕ) := Fin (n + 1) ⊕ (Pair n × Fin L × Bool)

instance {n L : ℕ} : Nonempty (Chore n L) := ⟨Sum.inl 0⟩

variable {n L : ℕ}

/-- The **first ordered input** of layer `k` of the chain on `π = (j, j′)` (arXiv:2611.06589,
Definition 6.4, p.21, and Section 7.1 (i), p.31): chore `j` for `k = 0`, and the plus output
`p^+_{(j,j′),k−1}` for `k ≥ 1`. -/
def firstIn (π : Pair n) (k : Fin L) : Chore n L :=
  if h : k.val = 0 then Sum.inl π.1.1 else Sum.inr (π, ⟨k.val - 1, by omega⟩, true)

/-- The **second ordered input** of layer `k` of the chain on `π = (j, j′)`: chore `j′` for
`k = 0`, and the minus output `p^−_{(j,j′),k−1}` for `k ≥ 1` (arXiv:2611.06589, Definition 6.4,
p.21). -/
def secondIn (π : Pair n) (k : Fin L) : Chore n L :=
  if h : k.val = 0 then Sum.inl π.1.2 else Sum.inr (π, ⟨k.val - 1, by omega⟩, false)

/-- The **market with `L`-layer gadget chains** for the instance `(A, c)` and a parameter `t`
(arXiv:2611.06589, Sections 5–6 and the specification of Section 7.1 (i)–(iv), pp.30–31):

* gadget layer `k` of chain `(j, j′)`: three agents with earning requirement
  `B_{(j,j′),k} = w_{jj′} t (1/2 − 4t)^k` and two output chores with supply
  `S_{(j,j′),k} = (1 − 4t) B_{(j,j′),k}` (6.9);
* basic agent `a_j`: `B_{a_j} = 1 − (3/2) ∑_{k<L} ∑_{j′≠j} B_{(j,j′),k} − (α/t) c_j`; basic chore
  `j`: `S_j = 1 − ∑_{k<L} ∑_{j′≠j} S_{(j,j′),k}` (Section 7.1 (iii), p.31, with (6.12), (6.19));
* disutilities (Section 7.1 (iv), p.31): basic agent `a_j` has `1` on chores `{0, j}`, `1 + t` on
  the other basic chores and `(1 + t)²` on every auxiliary chore; at layer `k`, `a^max` has `q_k`
  on both inputs and `1` on the plus output, `a^{(1)}` has `1/q_k` on the first input and `1` on the
  minus output, `a^{(2)}` has `1/q_k` on the second input and `1` on the minus output, and every
  other entry is `(1 + t)²`.

**Formalization Note.** `α = λt²` is (5.5) and `w_{jj′}` is (5.4) with `α/t² = λ`. For the
completed market of Section 7, `t` and `L` are those of (7.1) (`completedMarket`). The sums over
`j′ ≠ j` are sums over the pairs incident to `j`. -/
noncomputable def chainMarket (P : Quadratic n) (t : ℝ) (L : ℕ) :
    ChoresMarket (Agent n L) (Chore n L) where
  disutil a ℓ :=
    match a with
    | Sum.inl j =>
      match ℓ with
      | Sum.inl j'' => if j'' = 0 ∨ j'' = j then 1 else 1 + t
      | Sum.inr _ => (1 + t) ^ 2
    | Sum.inr (π, k, r) =>
      if r = 0 then
        (if ℓ = firstIn π k ∨ ℓ = secondIn π k then qPar t k.val
          else if ℓ = Sum.inr (π, k, true) then 1 else (1 + t) ^ 2)
      else if r = 1 then
        (if ℓ = firstIn π k then 1 / qPar t k.val
          else if ℓ = Sum.inr (π, k, false) then 1 else (1 + t) ^ 2)
      else
        (if ℓ = secondIn π k then 1 / qPar t k.val
          else if ℓ = Sum.inr (π, k, false) then 1 else (1 + t) ^ 2)
  earn a :=
    match a with
    | Sum.inl j => 1 - 3 / 2 * ∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val
        - alpha P t / t * cExt P j
    | Sum.inr (π, k, _) => gadgetEarn P t π k.val
  supply ℓ :=
    match ℓ with
    | Sum.inl j => 1 - ∑ k : Fin L, ∑ π ∈ incident j, gadgetSupply P t π k.val
    | Sum.inr (π, k, _) => gadgetSupply P t π k.val

/-- The **completed market** `F = f(I)` of the instance `I = (A, c, ε)` (arXiv:2611.06589,
Section 7, pp.30–32): `chainMarket` with `t = 2^{−L}` and `L` chosen by (7.1). -/
noncomputable def completedMarket (P : Quadratic n) (ε : ℚ) :
    ChoresMarket (Agent n (chainLength P ε)) (Chore n (chainLength P ε)) :=
  chainMarket P (tParam P ε) (chainLength P ε)

/-- The **designated choices** of an agent (arXiv:2611.06589, Definition 6.1, p.19; Section 7.1,
proof plan, p.32): the basic chores for a basic agent; the two inputs and the plus output for
`a^max`; the first input and the minus output for `a^{(1)}`; the second input and the minus output
for `a^{(2)}`. Every other agent–chore pair is an undesignated choice. -/
def Designated : Agent n L → Chore n L → Prop
  | Sum.inl _, ℓ => ∃ j, ℓ = Sum.inl j
  | Sum.inr (π, k, r), ℓ =>
      (r = 0 ∧ (ℓ = firstIn π k ∨ ℓ = secondIn π k ∨ ℓ = Sum.inr (π, k, true))) ∨
      (r = 1 ∧ (ℓ = firstIn π k ∨ ℓ = Sum.inr (π, k, false))) ∨
      (r = 2 ∧ (ℓ = secondIn π k ∨ ℓ = Sum.inr (π, k, false)))

open Classical in
/-- `N^σ_{out,k}`: the agents **outside** the layer-`k` gadget of chain `π` who use (`z_{aℓ} > 0`)
its output chore `p^σ_{π,k}` (arXiv:2611.06589, Section 6.3, p.22, and p.33). -/
noncomputable def outUsers (z : Agent n L → Chore n L → ℝ) (π : Pair n) (k : Fin L)
    (σ : Bool) : Finset (Agent n L) :=
  Finset.univ.filter (fun a => (∀ r : Fin 3, a ≠ Sum.inr (π, k, r)) ∧
    0 < z a (Sum.inr (π, k, σ)))

/-- The largest price `p_max` among all chores (arXiv:2611.06589, Lemma 7.2, p.33). -/
noncomputable def pmax {M : Type*} [Fintype M] [Nonempty M] (p : M → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty p

/-- The smallest price `p_min` among all chores (arXiv:2611.06589, Lemma 7.2, p.33). -/
noncomputable def pmin {M : Type*} [Fintype M] [Nonempty M] (p : M → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty p

end LinearChoresCLS


