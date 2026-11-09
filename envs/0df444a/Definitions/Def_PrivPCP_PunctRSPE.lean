-- Prove2me | Definitions.Def_PrivPCP_PunctRSPE
-- name    : PrivPCP_PunctRSPE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:19.467194+00:00
-- url     : https://prove2.me/theorems/56447e55-9aef-475d-9e32-5d32d0cd4f64
-- title:
--   The product-expansion property of Conjecture 4.2
-- statement:
--   For an integer $r\ge 2$ and reals $\eta,\beta,\rho$, $\mathrm{PunctRSPE}(r,\eta,\beta,\rho)$ is the statement: for every prime $q$, all multiplicative subgroups $S_1,\dots,S_r\le\mathbb F_q^\times$ of pairwise coprime orders $s_i=|S_i|$ with
--   $$\beta^{-1}\le s_i/s_j\le\beta\qquad(i,j\in[r]),$$
--   all integers $t_i$ with $1\le t_i\le(1-\eta)s_i$, and all invertible diagonal matrices $\Lambda_i$ indexed by $S_i$, the tuple $(\Lambda_i\,\mathrm{RS}(S_i,t_i))_{i=1}^r$ is $\rho$-product-expanding.
--
--   Here $\mathrm{RS}(S,t)=\{(f(\alpha))_{\alpha\in S}: \deg f<t\}$, and a tuple $(C_i)_{i}$ is $\rho$-product-expanding (Definition 4.1) if every $M\in\sum_i L_i(C_i)$ has a decomposition $M=\sum_i M_i$, $M_i\in L_i(C_i)$, with $\mathrm{wt}(M)\ge\rho\sum_i s_i\,\ell_i(M_i)$, where $L_i(C_i)$ is the space of words on $\prod_i S_i$ whose $i$-axis lines lie in $C_i$ and $\ell_i(M_i)$ is the number of nonzero $i$-axis lines of $M_i$.
--
--   **Conjecture 4.2** asserts that for every $\eta\in(0,1)$, $\beta\ge 1$ and $r\ge 2$ there is $\rho\in(0,1]$ with $\mathrm{PunctRSPE}(r,\eta,\beta,\rho)$. Theorem 4.11 proves the case $r=2$. The predicate is the hypothesis of the goal for $k>2$.
--
--   **Formalization Note** Product expansion is the published `GoodQLTC.IsProductExpanding`, which includes $\rho>0$; every use in this mission has $\rho\in(0,1]$.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Conjecture 4.2, p.14 (PDF p.16); Definition 4.1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_GoodQLTC_IsProductExpanding
import Definitions.Def_GoodQLTC_rsCode
import Definitions.Def_PrivPCP_subgroupSet

namespace PrivPCP

/-- **The predicate of Conjecture 4.2 (product expansion of punctured Reed–Solomon codes)** at arity `r`, rate
margin `η`, balance `β` and constant `ρ` (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC 2027
submission manuscript (sha256 c2cac1e0…), Conjecture 4.2, p.14; Definition 4.1, p.12). For every prime `q`,
every family of multiplicative subgroups `S_1, …, S_r ⩽ 𝔽_q^×` of pairwise coprime orders `s_i = |S_i|` with
`β^{−1} ⩽ s_i/s_j ⩽ β`, all integers `t_i` with `1 ⩽ t_i ⩽ (1 − η)s_i` and all invertible diagonal matrices
`Λ_i` indexed by `S_i`, the tuple `(Λ_i RS(S_i, t_i))_{i=1}^r` is `ρ`-product-expanding.

**Formalization Note** `ρ`-product expansion is the published `GoodQLTC.IsProductExpanding`, which is
Definition 4.1 (axis codes `L_i`, line counts `ℓ_i`, weights `s_i`) and includes `0 < ρ`. `RS(S, t)` is
`GoodQLTC.rsCode` on the set `S ⊆ 𝔽_q`, and `Λ_i RS(S_i, t_i)` is its image under the diagonal map
`GoodQLTC.monomialImage (Equiv.refl _) Λ_i`. Conjecture 4.2 asserts that for all `r ⩾ 2`, `η ∈ (0,1)`,
`β ⩾ 1` there is `ρ ∈ (0,1]` with `PunctRSPE r η β ρ`. -/
def PunctRSPE (r : ℕ) (η β ρ : ℝ) : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (S : Fin r → Subgroup (ZMod q)ˣ),
    (∀ i j, i ≠ j → Nat.Coprime (Nat.card (S i)) (Nat.card (S j))) →
    (∀ i j, β⁻¹ ≤ (Nat.card (S i) : ℝ) / Nat.card (S j) ∧ (Nat.card (S i) : ℝ) / Nat.card (S j) ≤ β) →
    ∀ t : Fin r → ℕ, (∀ i, 1 ≤ t i ∧ (t i : ℝ) ≤ (1 - η) * Nat.card (S i)) →
    ∀ Λ : ∀ i, ↥((subgroupSet (S i) : Finset (ZMod q)) : Set (ZMod q)) → (ZMod q)ˣ,
      GoodQLTC.IsProductExpanding ρ (fun i => GoodQLTC.monomialImage (Equiv.refl _) (Λ i)
        (GoodQLTC.rsCode ((subgroupSet (S i) : Finset (ZMod q)) : Set (ZMod q)) (t i)))

end PrivPCP


