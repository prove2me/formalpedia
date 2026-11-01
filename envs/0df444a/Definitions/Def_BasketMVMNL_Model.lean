-- Prove2me | Definitions.Def_BasketMVMNL_Model
-- name    : BasketMVMNL_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:30:12.704474+00:00
-- url     : https://prove2.me/theorems/70e1e8a6-cf78-4cbe-8ae6-0deb4b3957f8
-- title:
--   §3–§4, pp.6–9 — the MVMNL basket-choice model: instances, bundles, the choice rule (3) and the expected revenue (4)
-- statement:
--   There are $J$ groups of products, each with $I$ products; $(i,j)$ is product $i$ of group $j$. A customer buys a **bundle** $y=(y_j)_{j=1}^J$: $y_j=i$ means product $i$ of group $j$ is bought and $y_j=0$ means nothing is bought from group $j$. An **assortment** is $x\in\{0,1\}^{JI}$, and a bundle is **permissible** under $x$ when every product it buys is offered; $\mathcal Y$ denotes the permissible bundles.
--
--   The instance consists of weights $v_{i,j}=e^{\theta_{i,j}}>0$, the weight $v_0=e^{\mu_0}$ of the global outside option, revenues $r_{i,j}$ and interaction terms $\psi_{(i,j),(i',j')}$. The utility of a bundle is $\mu(0)=\mu_0$ and, for $y\neq0$,
--   $$
--   \mu(y)=\sum_{i,j}\theta_{i,j}z_{i,j}+\sum_{i',i,j'>j}\psi_{(i,j),(i',j')}z_{i,j}z_{i',j'},\qquad z_{i,j}=\mathbb 1\{y_j=i\}.
--   $$
--   The choice probability and the expected total revenue are
--   $$
--   P(Y=y)=\frac{e^{\mu(y)}}{\sum_{y'\in\mathcal Y}e^{\mu(y')}},\qquad R(x)=\frac{\sum_{y\in\mathcal Y}r(y)\,e^{\mu(y)}}{\sum_{y'\in\mathcal Y}e^{\mu(y')}},\qquad r(y)=\sum_{i,j}r_{i,j}z_{i,j},
--   $$
--   and $P_{i,j}(x)$ is the probability that product $(i,j)$ is purchased.
--
--   The **standing assumptions** of §4 are $v_{i,j}>0$, $v_0>1$, revenues non-increasing in $i$ within each group (the paper's ordering without loss of generality), $J,I\ge1$, and $r_{i,j}\ge0$. **No interaction terms** means $\psi_{(i,j),(i',j')}=0$ for $j\neq j'$. Every other object of the mission is built on these.
--
--   **Formalization Note** Groups are `Fin J`, products `Fin I` (0-based), assortments `Fin J → Fin I → Bool`, bundles `Fin J → Option (Fin I)` with `none` for $y_j=0$. The data are $v$ and $v_0$ themselves, so $\theta=\log v$ and $\mu_0=\log v_0$; the empty bundle has weight $e^{\mu_0}=v_0$, as the denominator of Lemma 1 requires. `prob` is $0$ on non-permissible bundles. The sign $r_{i,j}\ge0$ is a reading: the paper calls $r_{i,j}$ a revenue and never states its sign.
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, §3, pp.6–7, (1)–(4); §4, p.9 (standing assumptions, no interaction terms, Pᵢ,ⱼ(x))

import Mathlib

namespace BasketMVMNL

open Finset

/-- **An MVMNL instance.** Jasin, Lyu, Najafi, Zhang, *Assortment Optimization with Multi-Item
Basket Purchase under Multivariate MNL Model*, SSRN 3818886, §3, pp.6–7 and §4, p.9.

There are `J` groups of `I` products each. `v j i` is the preference weight
`vᵢ,ⱼ = exp θᵢ,ⱼ` of product `i` in group `j`, `v0` is `v₀ = exp μ₀`, the weight of the global
outside option, `r j i` is the revenue `rᵢ,ⱼ`, and `ψ j i j' i'` is the interaction term
`ψ_{(i,j),(i',j')}` of (2).

**Formalization Note.** Groups are `Fin J` and products `Fin I`, 0-based; all arrays are stored
group first. The data are the weights `v = exp θ` and `v₀ = exp μ₀` themselves, so `θ = log v`
and `μ₀ = log v₀`. -/
structure Instance (J I : ℕ) where
  v : Fin J → Fin I → ℝ
  v0 : ℝ
  r : Fin J → Fin I → ℝ
  ψ : Fin J → Fin I → Fin J → Fin I → ℝ

/-- An assortment `x = (xᵢ,ⱼ)`: `x j i = true` iff product `i` of group `j` is offered, §4, p.9. -/
abbrev Assortment (J I : ℕ) := Fin J → Fin I → Bool

/-- A bundle `y = (yⱼ)`, §3, p.6: `y j = some i` is the paper's `yⱼ = i` (product `i` of group `j`
is bought) and `y j = none` is `yⱼ = 0` (nothing is bought from group `j`). -/
abbrev Bundle (J I : ℕ) := Fin J → Option (Fin I)

/-- The empty bundle `y = 0`: nothing is bought from any group. -/
def emptyBundle (J I : ℕ) : Bundle J I := fun _ => none

/-- The real value `1` of `true` and `0` of `false`: `xᵢ,ⱼ` as a number. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

namespace Instance

variable {J I : ℕ} (P : Instance J I)

/-- **The standing assumptions of §4, p.9**: `vᵢ,ⱼ = exp θᵢ,ⱼ > 0`, `v₀ > 1` ("Since we assume a
positive no-purchase utility, v₀ > 1"), revenues non-increasing in `i` within each group ("Without
loss of generality, we assume that the products in each group are ordered in such a way that the
revenues {rᵢ,ⱼ} are non-increasing in i for each j"), and `J ≥ 1`, `I ≥ 1` ("There are J groups of
products and each group consists of I different products", p.6).

**Formalization Note.** `0 ≤ rᵢ,ⱼ` is a reading: the paper calls `rᵢ,ⱼ` "the revenue of product i
in group j" and never states its sign; with a negative revenue Theorem 1 fails. -/
structure Standing : Prop where
  one_le_J : 1 ≤ J
  one_le_I : 1 ≤ I
  v_pos : ∀ j i, 0 < P.v j i
  one_lt_v0 : 1 < P.v0
  r_nonneg : ∀ j i, 0 ≤ P.r j i
  r_antitone : ∀ j, Antitone (P.r j)

end Instance

variable {J I : ℕ}

/-- **No interaction terms**, §4, p.9: `ψ_{(i,j),(i',j')} = 0` for all `i, i'` and `j ≠ j'`. -/
def NoInteraction (P : Instance J I) : Prop :=
  ∀ j i j' i', j ≠ j' → P.ψ j i j' i' = 0

/-- A bundle `y` is permissible under the assortment `x` when every product it buys is offered:
`y` belongs to the set `𝒴` of permissible bundles of (3), p.7. -/
def Permissible (x : Assortment J I) (y : Bundle J I) : Prop :=
  ∀ j i, y j = some i → x j i = true

instance (x : Assortment J I) : DecidablePred (Permissible x) := fun y => by
  unfold Permissible; infer_instance

/-- `𝒴`, the finite set of bundles permissible under `x`. -/
def bundles (x : Assortment J I) : Finset (Bundle J I) :=
  univ.filter (Permissible x)

/-- **The systematic utility `μ(y)`**, (1)–(2), p.7: `μ₀ = log v₀` for the empty bundle, and
`μ(y) = Σ_{i,j} θᵢ,ⱼ zᵢ,ⱼ + Σ_{i',i,j'>j} ψ_{(i,j),(i',j')} zᵢ,ⱼ z_{i',j'}` otherwise, with
`θᵢ,ⱼ = log vᵢ,ⱼ` and `zᵢ,ⱼ = 1{yⱼ = i}`.

**Formalization Note.** (3)–(4) write `exp{μ(y)}` for every permissible bundle, including
`y = 0`; the denominator `v₀ + …` of Lemma 1 shows that the empty bundle's weight is
`exp μ₀ = v₀`, which is what this definition gives. The interaction sum runs over ordered pairs of
groups `j < j'`, each unordered pair once, as in (2). -/
noncomputable def mu (P : Instance J I) (y : Bundle J I) : ℝ :=
  if y = emptyBundle J I then Real.log P.v0
  else (∑ j, ∑ i, if y j = some i then Real.log (P.v j i) else 0) +
    ∑ j, ∑ i, ∑ j', ∑ i',
      if j < j' ∧ y j = some i ∧ y j' = some i' then P.ψ j i j' i' else 0

/-- `r(y) = Σ_{i,j} rᵢ,ⱼ zᵢ,ⱼ`, the total revenue of bundle `y`, p.7. -/
noncomputable def bundleRev (P : Instance J I) (y : Bundle J I) : ℝ :=
  ∑ j, ∑ i, if y j = some i then P.r j i else 0

/-- **The choice probability (3)**, p.7: `P(Y = y) = exp μ(y) / Σ_{y'∈𝒴} exp μ(y')` for a
permissible bundle `y`, and `0` for a bundle that buys a product not offered. -/
noncomputable def prob (P : Instance J I) (x : Assortment J I) (y : Bundle J I) : ℝ :=
  if Permissible x y then
    Real.exp (mu P y) / ∑ y' ∈ bundles x, Real.exp (mu P y')
  else 0

/-- **The expected total revenue (4)**, p.7:
`R(x) = Σ_{y∈𝒴} r(y) exp μ(y) / Σ_{y'∈𝒴} exp μ(y')`. -/
noncomputable def R (P : Instance J I) (x : Assortment J I) : ℝ :=
  (∑ y ∈ bundles x, bundleRev P y * Real.exp (mu P y)) / ∑ y ∈ bundles x, Real.exp (mu P y)

/-- `Pᵢ,ⱼ(x)`, the probability that product `i` of group `j` is purchased under `x`, §4, p.9: the
total probability (3) of the permissible bundles with `yⱼ = i`. -/
noncomputable def Pij (P : Instance J I) (x : Assortment J I) (j : Fin J) (i : Fin I) : ℝ :=
  ∑ y ∈ (bundles x).filter (fun y => y j = some i), prob P x y

end BasketMVMNL


