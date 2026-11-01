-- Prove2me | Definitions.Def_RandAssort_Model
-- name    : RandAssort_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:30:30.406996+00:00
-- url     : https://prove2.me/theorems/ac384495-b788-4fa5-88ca-501c88d34249
-- title:
--   Robust assortment instance $(\mathcal N,\mathcal S,\mathfrak C,\mathcal U,r)$, $R^\star_{\mathrm{det}}$, $R^\star_{\mathrm{rand}}$ and randomization-proofness (Definition 1)
-- statement:
--   These are the objects of the robust assortment optimization problem of Wang, Peura and Wiesemann (§3, pp.7–8).
--
--   1. **Instance.** An instance is a tuple $(\mathcal N,\mathcal S,\mathfrak C,\mathcal U,r)$. The products are $\mathcal N=\{1,\dots,n\}$, and $\mathcal N_0=\mathcal N\cup\{0\}$ adds the no-purchase alternative $0$. The family $\mathcal S\subseteq\{S: S\subseteq\mathcal N\}$ collects the admissible assortments. The uncertainty set $\mathcal U$ is a subset of a finite-dimensional real space. The choice model gives, for each assortment $S\in\mathcal S$ and realization $u\in\mathcal U$, the probability $\mathfrak C(i\mid S,u)$ that a customer chooses $i\in\mathcal N_0$. The price of product $i$ is $r_i$, and the no-purchase option has price $r_0=0$.
--   2. **Standing assumptions** (p.7). $\mathcal S$ and $\mathcal U$ are nonempty, $\mathcal U$ is compact, and $r_i>0$ for every $i$. For every $S\in\mathcal S$ and $u\in\mathcal U$, $\mathfrak C(\cdot\mid S,u)$ is a probability distribution on $\mathcal N_0$, and $\mathfrak C(i\mid S,u)=0$ for every $i\in\mathcal N\setminus S$.
--   3. **Revenues** (pp.7–8). The expected revenue of $S$ under $u$ and its worst case over $\mathcal U$ are
--   $$
--   R(S,u)=\sum_{i\in S}r_i\,\mathfrak C(i\mid S,u),\qquad R^\star(S)=\min_{u\in\mathcal U}R(S,u),
--   $$
--   and the deterministic robust value is $R^\star_{\mathrm{det}}(\mathcal U)=\max_{S\in\mathcal S}R^\star(S)$.
--   4. **Randomized assortments** (p.8). A randomized assortment is a probability vector $p\in\Delta(\mathcal S)=\{p\in\mathbb R^{|\mathcal S|}_+:\sum_{S}p_S=1\}$ over the admissible assortments. Its expected revenue is $R(p,u)=\sum_{S\in\mathcal S}p_S\,R(S,u)$ and its worst case is $R^\star(p)=\min_{u\in\mathcal U}R(p,u)$. The randomized robust value is
--   $$
--   R^\star_{\mathrm{rand}}(\mathcal U)=\max_{p\in\Delta(\mathcal S)}R^\star(p).
--   $$
--   5. **Definition 1** (p.8). An instance is *randomization-receptive* if $R^\star_{\mathrm{rand}}(\mathcal U)>R^\star_{\mathrm{det}}(\mathcal U)$, and *randomization-proof* otherwise.
--
--   Every statement of the mission is about these objects. The values $R^\star_{\mathrm{det}}$ and $R^\star_{\mathrm{rand}}$ are the primal max–min values; neither is defined through a dual.
--
--   **Formalization Note** Products are `Fin n` and $\mathcal N_0$ is `Option (Fin n)`, with `none` the no-purchase alternative. Assortments are `Finset (Fin n)` and $\mathcal S$ is a `Finset` of them. The choice model is a total function `C i S u`; only its values at $S\in\mathcal S$, $u\in\mathcal U$ enter any quantity. The price $r_0=0$ is not stored, because revenues sum over offered products only. The assumptions are the separate predicate `Instance.IsValid`; finite-dimensionality is a hypothesis on the ambient space in the theorems. Minima and maxima are written as real infima and suprema (`⨅`, `⨆`). They are bounded for valid instances ($0\le R\le\sum_i r_i$), and the theorems state attainment where it is used. $\Delta(\mathcal S)$ is `stdSimplex ℝ 𝒮`, vectors indexed by the members of $\mathcal S$ only.
-- source:
--   Wang–Peura–Wiesemann, Randomized Assortment Optimization, Oper. Res. (2024), doi:10.1287/opre.2022.0129, §3 (Nominal, Deterministic Robust, Randomized Robust), pp.7–8; Δ(X), Notation, p.4; Definition 1, p.8

import Mathlib

namespace RandAssort

/-- A **robust assortment optimization instance** `(𝒩, 𝒮, ℭ, 𝒰, r)`, §3, p.7 of
Z. Wang, H. Peura, W. Wiesemann, *Randomized Assortment Optimization*, Operations Research (2024),
doi:10.1287/opre.2022.0129.

* the products are `𝒩 = {1, …, n}`, encoded as `Fin n`; the extended set `𝒩₀ = 𝒩 ∪ {0}` is
  `Option (Fin n)`, with `none` the no-purchase alternative `0` and `some i` product `i`;
* `S` is the family `𝒮 ⊆ {S : S ⊆ 𝒩}` of admissible assortments;
* `U` is the uncertainty set `𝒰`, a subset of the ambient space `E`;
* `C i S u` is the choice probability `ℭ(i | S, u)` of alternative `i ∈ 𝒩₀` when assortment `S` is
  offered and the uncertain parameter is `u`;
* `r i` is the price `r_i` of product `i ∈ 𝒩`.

**Formalization Note** The fields are bare data; the paper's assumptions on them are the separate
predicate `Instance.IsValid`. `C` is a total function, but only its values at `S ∈ 𝒮`, `u ∈ 𝒰`
enter any quantity below. The price `r₀ = 0` of the no-purchase option is not stored: revenues sum
over the offered products only, which is the same as giving alternative `0` the price `0`. -/
structure Instance (n : ℕ) (E : Type*) where
  /-- The admissible assortments `𝒮`. -/
  S : Finset (Finset (Fin n))
  /-- The uncertainty set `𝒰`. -/
  U : Set E
  /-- The choice model: `C i S u = ℭ(i | S, u)`, `i ∈ 𝒩₀ = Option (Fin n)`. -/
  C : Option (Fin n) → Finset (Fin n) → E → ℝ
  /-- The product prices `r_i`, `i ∈ 𝒩`. -/
  r : Fin n → ℝ

variable {n : ℕ} {E : Type*}

/-- The standing assumptions on an instance, §3, p.7:

1. `𝒮` is nonempty and `𝒰` is nonempty (otherwise `max_{S ∈ 𝒮}` and `min_{u ∈ 𝒰}` are undefined);
2. `𝒰` is compact ("we assume that `𝒰` is a compact subset of a finite-dimensional space"; the
   finite-dimensionality is a hypothesis on the ambient space `E` in the theorems);
3. every price is positive, `r_i > 0`;
4. for every `S ∈ 𝒮` and `u ∈ 𝒰`, `ℭ(· | S, u) ∈ Δ(𝒩₀)`: nonnegative and summing to `1`;
5. `ℭ(i | S, u) = 0` for all `i ∈ 𝒩 \ S`, `S ∈ 𝒮`, `u ∈ 𝒰`. -/
structure Instance.IsValid [TopologicalSpace E] (I : Instance n E) : Prop where
  S_nonempty : I.S.Nonempty
  U_nonempty : I.U.Nonempty
  U_compact : IsCompact I.U
  r_pos : ∀ i : Fin n, 0 < I.r i
  C_nonneg : ∀ S ∈ I.S, ∀ u ∈ I.U, ∀ i : Option (Fin n), 0 ≤ I.C i S u
  C_sum : ∀ S ∈ I.S, ∀ u ∈ I.U, ∑ i : Option (Fin n), I.C i S u = 1
  C_off : ∀ S ∈ I.S, ∀ u ∈ I.U, ∀ i : Fin n, i ∉ S → I.C (some i) S u = 0

/-- The expected revenue `R(S, u) = ∑_{i ∈ S} r_i · ℭ(i | S, u)` of assortment `S` under the
parameter realization `u`, p.8. -/
def Instance.R (I : Instance n E) (S : Finset (Fin n)) (u : E) : ℝ :=
  ∑ i ∈ S, I.r i * I.C (some i) S u

/-- The worst-case expected revenue `R⋆(S) = min_{u ∈ 𝒰} R(S, u)` of an assortment, p.8.

**Formalization Note** Written as the real infimum `⨅ u : 𝒰, R(S, u)`. For a valid instance the
family is nonempty and bounded below by `0`; the theorems that need the minimum to be attained
assume `u ↦ R(S, u)` lower semicontinuous on `𝒰` and state the attainment. -/
noncomputable def Instance.Rstar (I : Instance n E) (S : Finset (Fin n)) : ℝ :=
  ⨅ u : I.U, I.R S u

/-- The optimal value of the **deterministic robust** problem,
`R⋆_det(𝒰) = max_{S ∈ 𝒮} R⋆(S)`, (Deterministic Robust), p.7.

**Formalization Note** Written as the real supremum over the finite family `𝒮` (nonempty for a
valid instance), which is the maximum. -/
noncomputable def Instance.Rdet (I : Instance n E) : ℝ :=
  ⨆ S : I.S, I.Rstar S

/-- The expected revenue `R(p, u) = ∑_{S ∈ 𝒮} p_S · R(S, u)` of a randomized assortment `p`, a
vector indexed by the admissible assortments, under the realization `u`, p.8. -/
def Instance.Rp (I : Instance n E) (p : I.S → ℝ) (u : E) : ℝ :=
  ∑ S : I.S, p S * I.R S u

/-- The worst-case expected revenue `R⋆(p) = min_{u ∈ 𝒰} R(p, u)` of a randomized assortment,
p.8.

**Formalization Note** Written as the real infimum `⨅ u : 𝒰, R(p, u)`, as for `Rstar`. -/
noncomputable def Instance.RstarP (I : Instance n E) (p : I.S → ℝ) : ℝ :=
  ⨅ u : I.U, I.Rp p u

/-- The optimal value of the **randomized robust** problem,
`R⋆_rand(𝒰) = max_{p ∈ Δ(𝒮)} R⋆(p)`, (Randomized Robust), p.8, where
`Δ(𝒮) = {p ∈ ℝ^{|𝒮|}_+ : ∑_S p_S = 1}` (Notation, p.4) is the probability simplex over the
admissible assortments.

**Formalization Note** `Δ(𝒮)` is `stdSimplex ℝ 𝒮`, vectors indexed by the members of `𝒮` only
(not by all subsets of `𝒩`). The maximum is written as the real supremum
`⨆ p ∈ Δ(𝒮), R⋆(p)`; for a valid instance the family is bounded above by `∑_i r_i`. -/
noncomputable def Instance.Rrand (I : Instance n E) : ℝ :=
  ⨆ p : stdSimplex ℝ I.S, I.RstarP p

/-- **Definition 1** (randomization-receptiveness/proofness), p.8: an instance is
*randomization-receptive* if `R⋆_rand(𝒰) > R⋆_det(𝒰)`. -/
def Instance.RandomizationReceptive (I : Instance n E) : Prop :=
  I.Rrand > I.Rdet

/-- **Definition 1** (randomization-receptiveness/proofness), p.8: an instance is
*randomization-proof* if it is not randomization-receptive, i.e. if `R⋆_rand(𝒰) > R⋆_det(𝒰)`
fails. -/
def Instance.RandomizationProof (I : Instance n E) : Prop :=
  ¬ (I.Rrand > I.Rdet)

end RandAssort


