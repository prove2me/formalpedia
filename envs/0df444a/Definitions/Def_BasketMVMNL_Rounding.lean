-- Prove2me | Definitions.Def_BasketMVMNL_Rounding
-- name    : BasketMVMNL_Rounding
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:30:51.714105+00:00
-- url     : https://prove2.me/theorems/181cb74a-9265-4c62-aa1a-6a34376b36ec
-- title:
--   (7), p.12, and §4.2, p.13 — $\gamma_j$, $\Gamma$, $R_j$, revenue-ordered assortments, the rounding $\bar\gamma_j$, $\bar\Gamma$, $\bar R$, $M$ and $\beta$
-- statement:
--   For an assortment $x$ and a group $j$ let
--   $$
--   \gamma_j(x_j)=1+\sum_i v_{i,j}x_{i,j},\qquad \Gamma(x)=\prod_j\gamma_j(x_j),\qquad \Lambda_j(x_j)=\sum_i r_{i,j}v_{i,j}x_{i,j},\qquad R_j(x)=\frac{\Lambda_j(x_j)}{\big[\frac{v_0-1}{\Gamma(x)}+1\big]\gamma_j(x_j)}.
--   $$
--   An assortment is **revenue-ordered** when each local assortment is a prefix: for each $j$ there is $i(j)$ with $x_{i,j}=1$ iff $i\le i(j)$.
--
--   Given $\epsilon'>0$, the **rounding exponent** of $\gamma\ge1$ is the least integer $m\ge1$ with $\gamma\le(1+\epsilon')^m$; for $\gamma>1$ this is the $m_j$ with $(1+\epsilon')^{m_j-1}<\gamma_j(x_j)\le(1+\epsilon')^{m_j}$, and for $x_j=0$ it is $m_j=1$. Then
--   $$
--   \bar\gamma_j(x_j)=(1+\epsilon')^{m_j},\qquad \bar\Gamma(x)=\prod_j\bar\gamma_j(x_j),\qquad \bar R(x)=\sum_j\bar R_j(x),\quad \bar R_j(x)=\frac{\Lambda_j(x_j)}{\big[\frac{v_0-1}{\bar\Gamma(x)}+1\big]\bar\gamma_j(x_j)},
--   $$
--   that is, every $\gamma$ and $\Gamma$ of (7) is replaced by $\bar\gamma$ and $\bar\Gamma$. Finally $M=\max_j\lceil\log_{1+\epsilon'}(1+\sum_i v_{i,j})\rceil$ and $\beta=\max_j(1+\sum_i v_{i,j})$.
--
--   These are the quantities on which Algorithm U1 and its analysis are built.
--
--   **Formalization Note** $M$ is written as $\max_j m(1+\sum_i v_{i,j})$, which equals the ceiling of the logarithm because $1+\sum_i v_{i,j}>1$. Revenue-ordered is "for each $j$ some $t\le I$ with $x_j\,i$ true iff $i<t$" (0-based). The rounding exponent is `1` when no $m$ exists (only for $\epsilon'\le0$, which no statement uses). $\beta$ is $1$ and $M$ is $0$ when $J=0$, which the standing assumptions exclude.
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, (7), p.12; §4.2, p.13 (rounding, R̄, M); Lemma 2, p.10 (revenue-ordered); Theorem 1, p.14 (β)

import Mathlib
import Definitions.Def_BasketMVMNL_Model

namespace BasketMVMNL

open Finset

variable {J I : ℕ}

/-- `γⱼ(xⱼ) = 1 + Σᵢ vᵢ,ⱼ xᵢ,ⱼ`, (7), p.12. -/
noncomputable def γ (P : Instance J I) (x : Assortment J I) (j : Fin J) : ℝ :=
  1 + ∑ i, P.v j i * bit (x j i)

/-- `Γ(x) = ∏ⱼ γⱼ(xⱼ)`, (7), p.12. -/
noncomputable def Γ (P : Instance J I) (x : Assortment J I) : ℝ :=
  ∏ j, γ P x j

/-- `Λⱼ(xⱼ) = Σᵢ rᵢ,ⱼ vᵢ,ⱼ xᵢ,ⱼ`, the numerator of the summand of (7), p.12 (the paper names it
`Λⱼ` in §5.1, p.14). -/
noncomputable def Λ (P : Instance J I) (x : Assortment J I) (j : Fin J) : ℝ :=
  ∑ i, P.r j i * P.v j i * bit (x j i)

/-- `Rⱼ(x) = Σᵢ rᵢ,ⱼ vᵢ,ⱼ xᵢ,ⱼ / ([(v₀ − 1)/Γ(x) + 1] γⱼ(xⱼ))`, the `j`-th summand of (7), p.12. -/
noncomputable def Rj (P : Instance J I) (x : Assortment J I) (j : Fin J) : ℝ :=
  Λ P x j / (((P.v0 - 1) / Γ P x + 1) * γ P x j)

/-- **Revenue-ordered** ("RO"), Lemma 2, p.10 and p.13: every local assortment `xⱼ` is a prefix of
the products, `xᵢ,ⱼ = 1` iff `i ≤ i(j)`.

**Formalization Note.** Products are 0-based, so the paper's `i ≤ i(j)` is `i < t` with
`t = i(j) ∈ {0, …, I}`; `t = 0` is the empty local assortment. -/
def IsRO (x : Assortment J I) : Prop :=
  ∀ j, ∃ t ≤ I, ∀ i : Fin I, x j i = true ↔ i.val < t

/-- **The rounding exponent** `m(γ)`, §4.2, p.13: the least integer `m ≥ 1` with
`γ ≤ (1 + ϵ′)^m`. For `γ > 1` it is the paper's `mⱼ` with
`(1 + ϵ′)^{mⱼ−1} < γⱼ(xⱼ) ≤ (1 + ϵ′)^{mⱼ}`; for `γ = 1` (that is, `xⱼ = 0`) it is the paper's
"If xⱼ = 0, we let mⱼ = 1".

**Formalization Note.** This is the analysis object; Algorithm U1 computes the exponent by a
multiplication loop (`BasketMVMNL.roundUp`). When no such `m` exists (only if `ϵ′ ≤ 0`) the value is
`1`, a junk value no statement uses. -/
noncomputable def mexp (ε' g : ℝ) : ℕ :=
  open Classical in
  if h : ∃ m : ℕ, 1 ≤ m ∧ g ≤ (1 + ε') ^ m then Nat.find h else 1

/-- `γ̄ⱼ(xⱼ) = (1 + ϵ′)^{mⱼ}`, γⱼ(xⱼ) rounded up to an integer power of `1 + ϵ′`, p.13. -/
noncomputable def γbar (ε' : ℝ) (P : Instance J I) (x : Assortment J I) (j : Fin J) : ℝ :=
  (1 + ε') ^ mexp ε' (γ P x j)

/-- `Γ̄(x) = ∏ⱼ γ̄ⱼ(xⱼ)`, p.13. -/
noncomputable def Γbar (ε' : ℝ) (P : Instance J I) (x : Assortment J I) : ℝ :=
  ∏ j, γbar ε' P x j

/-- `R̄ⱼ(x)`: the summand of (7) with every `γ` and `Γ` replaced by `γ̄` and `Γ̄` ("we simply replace
all γ's and Γ in (7) with γ̄'s and Γ̄", p.13). -/
noncomputable def Rbarj (ε' : ℝ) (P : Instance J I) (x : Assortment J I) (j : Fin J) : ℝ :=
  Λ P x j / (((P.v0 - 1) / Γbar ε' P x + 1) * γbar ε' P x j)

/-- `R̄(x) = Σⱼ R̄ⱼ(x)`, the approximated expected total revenue, p.13. -/
noncomputable def Rbar (ε' : ℝ) (P : Instance J I) (x : Assortment J I) : ℝ :=
  ∑ j, Rbarj ε' P x j

/-- `M = maxⱼ ⌈log_{1+ϵ′}(1 + Σᵢ vᵢ,ⱼ)⌉`, p.13, written as `maxⱼ m(1 + Σᵢ vᵢ,ⱼ)`.

**Formalization Note.** For `ϵ′ > 0` and `1 + Σᵢ vᵢ,ⱼ > 1` (which `Standing` gives) the least integer
`m ≥ 1` with `1 + Σᵢ vᵢ,ⱼ ≤ (1 + ϵ′)^m` is `⌈log_{1+ϵ′}(1 + Σᵢ vᵢ,ⱼ)⌉`. The maximum over the empty set
of groups is `0`; `Standing` has `J ≥ 1`. -/
noncomputable def Mcap (ε' : ℝ) (P : Instance J I) : ℕ :=
  univ.sup fun j => mexp ε' (1 + ∑ i, P.v j i)

/-- `β = maxⱼ (1 + Σᵢ vᵢ,ⱼ)`, Theorem 1, p.14.

**Formalization Note.** The maximum is over the nonempty set of groups (`Standing` has `J ≥ 1`);
with no groups the value is `1`. -/
noncomputable def β (P : Instance J I) : ℝ :=
  if h : (univ : Finset (Fin J)).Nonempty then univ.sup' h (fun j => 1 + ∑ i, P.v j i) else 1

end BasketMVMNL


