-- Prove2me | Definitions.Def_TwoSidedPI_Prices
-- name    : TwoSidedPI_Prices
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:27.613473+00:00
-- url     : https://prove2.me/theorems/52980cac-34e4-487b-9780-cc28077a2c5c
-- title:
--   Buyer and seller thresholds and the price $p_{i,j}(A_B,r)=\frac13(p_i(A_B,r)+p_j)$
-- statement:
--   Let the agents be buyers $B$ and sellers $S$, agent $a$'s value for an item having law $\mathcal D_a$ on $\mathbb R$, independently across agents, so that a profile $\tilde{\mathbf v}$ has the product law $\mathcal D$. Buyer $i$'s **threshold** is
--   $$
--   p_i(A_B,r)=\mathbf E_{\tilde{\mathbf v}\sim\mathcal D}\big[p_i(A_B,r,\tilde{\mathbf v})\big],
--   $$
--   which is $\infty$ when $A_B\cup\{i\}\notin\mathcal I_B$ or $|A_B\cup\{i\}|>r$. Seller $j$'s threshold is the mean of her value, $p_j=\mathbf E_{\tilde v_j\sim\mathcal D_j}[\tilde v_j]$. The **price** for a trade between buyer $i$ and seller $j$ is
--   $$
--   p_{i,j}(A_B,r)=\frac13\big(p_i(A_B,r)+p_j\big),
--   $$
--   which is $\infty$ when buyer $i$ cannot be feasibly added.
--
--   These prices are the posted prices of Mechanism 1; their monotonicity (Lemmas 6 and 7) drives its incentive properties and its welfare guarantee.
--
--   **Formalization Note** `thrBReal` and `priceReal` are the finite values; `thrB` and `price` take values in `WithTop ℝ` with $\infty=\top$. The factor $\frac13$ is fixed. Expectations are Bochner integrals, so the theorems assume integrable laws.
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, §3, p.10 (p_i(A_B, r), p_j, p_{i,j}(A_B, r)); proof of Lemma 4, p.28

import Mathlib
import Definitions.Def_TwoSidedPI_OptB

open MeasureTheory

namespace TwoSidedPI

/-- The expectation `E_{ṽ∼𝒟}[v(OPT_B(ṽ | A_B, r)) − v(OPT_B(ṽ | A_B ∪ {i}, r))]`, the finite value
of buyer `i`'s threshold `p_i(A_B, r)` (Braun, Kesselheim, arXiv:2105.15032v1, §3, p.10).

**Formalization Note** The agents are `B ⊕ S`; `D a` is the law of agent `a`'s value for an
item, and the valuation profile `ṽ` has the product law `Measure.pi D` (independent agents).
Only the buyers' coordinates `ṽ ∘ Sum.inl` enter. -/
noncomputable def thrBReal {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S]
    (M : Matroid B) (D : B ⊕ S → Measure ℝ) (AB : Finset B) (r : ℕ) (i : B) : ℝ :=
  ∫ v, (optB M (fun k => v (Sum.inl k)) AB r - optB M (fun k => v (Sum.inl k)) (insert i AB) r)
    ∂(Measure.pi D)

/-- Buyer `i`'s threshold `p_i(A_B, r) = E_{ṽ∼𝒟}[p_i(A_B, r, ṽ)]` (Braun, Kesselheim,
arXiv:2105.15032v1, §3, p.10): `∞` if `A_B ∪ {i} ∉ ℐ_B` or `|A_B ∪ {i}| > r`, else the
expectation `thrBReal`.

**Formalization Note** Feasibility does not depend on `ṽ`, so the expectation of `p_i(A_B, r, ṽ)`
is `∞` exactly when `i` cannot be added; `∞` is `⊤ : WithTop ℝ`. -/
noncomputable def thrB {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S]
    (M : Matroid B) (D : B ⊕ S → Measure ℝ) (AB : Finset B) (r : ℕ) (i : B) : WithTop ℝ := by
  classical
  exact if CanAdd M AB r i then (thrBReal M D AB r i : WithTop ℝ) else ⊤

/-- Seller `j`'s threshold `p_j = E_{ṽ_j∼𝒟_j}[ṽ_j]`, the mean of her value for her item
(Braun, Kesselheim, arXiv:2105.15032v1, §3, p.10). -/
noncomputable def thrS {B S : Type*} (D : B ⊕ S → Measure ℝ) (j : S) : ℝ :=
  ∫ x, x ∂(D (Sum.inr j))

/-- The finite value `(1/3)(p_i(A_B, r) + p_j)` of the price for a trade between buyer `i` and
seller `j` (Braun, Kesselheim, arXiv:2105.15032v1, §3, p.10). -/
noncomputable def priceReal {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S]
    (M : Matroid B) (D : B ⊕ S → Measure ℝ) (AB : Finset B) (r : ℕ) (i : B) (j : S) : ℝ :=
  (1 / 3 : ℝ) * (thrBReal M D AB r i + thrS D j)

/-- The price `p_{i,j}(A_B, r) := (1/3)(p_i(A_B, r) + p_j)` for a trade between buyer `i` and
seller `j` (Braun, Kesselheim, arXiv:2105.15032v1, §3, p.10, and proof of Lemma 4, p.28): `∞`
when buyer `i` cannot be feasibly added to `A_B` with `r` items, else `priceReal`.

**Formalization Note** `∞` is `⊤ : WithTop ℝ`; the factor `1/3` is fixed, as printed. -/
noncomputable def price {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S]
    (M : Matroid B) (D : B ⊕ S → Measure ℝ) (AB : Finset B) (r : ℕ) (i : B) (j : S) :
    WithTop ℝ := by
  classical
  exact if CanAdd M AB r i then (priceReal M D AB r i j : WithTop ℝ) else ⊤

end TwoSidedPI


