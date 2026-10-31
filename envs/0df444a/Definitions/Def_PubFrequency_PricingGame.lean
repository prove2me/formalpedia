-- Prove2me | Definitions.Def_PubFrequency_PricingGame
-- name    : PubFrequency_PricingGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:41.826995+00:00
-- url     : https://prove2.me/theorems/2782be53-514b-48bc-b71c-ce5031bb057f
-- title:
--   The pricing game: information value $q$ (1), $v$ (2), utility $U$ (3), choices $d^*$ (4), $\tilde d^*$ (7), $\tilde w^*$, profits (8)
-- statement:
--   This module defines the customers' problem and the pricing game of Chen and Roels's duopoly of information publishers (§3.1 and §3.3, pp. 7–11).
--
--   **Information.** Information arrives at rate $1$ and decays linearly at rate $\alpha>0$. The net amount accumulated over $\tau$ periods is, eq. (1),
--   $$q(\tau)=\int_0^\tau\bigl(1-\min\{1,\alpha t\}\bigr)\,dt,$$
--   and a publication with cycle $u$ of which a fraction $\varphi$ carries new content is worth, per period, $v(u,\varphi)=q(\varphi u)/u$ (eq. (2)).
--
--   **Cycles and the consumption grid.** Firm 1 is the fast publisher with cycle $u_1>0$; the slow publisher's cycle is $u_2=n\,u_1$ with $n\in\mathbb N$ (the paper restricts cycles to integer multiples of each other). Customers buy a fraction $d\in D=\{i/n\mid i=0,\dots,n\}$ of the fast firm's issues ("dailies") and $w\in\{0,1\}$ of the slow firm's ("weekly").
--
--   **Utility and choices.** At prices $r=(r_1,r_2)$:
--   1. utility, eq. (3): $U(d,w;r)=d\,(v(u_1,1)-r_1)+w\,(v(u_2,1-d)-r_2)$;
--   2. exact dailies choice: $d^*(w;r)$ is the **largest** maximizer of $d\mapsto U(d,w;r)$ over $D$ (the tie rule of (4));
--   3. approximate choice, eq. (7): if $w=1$, $\partial U(0,1;r)/\partial d\ge 0$ and $U(1,1;r)<U(1-1/n,1;r)$, then $\tilde d^*(1;r)=j^*/n$, where $j^*$ is the **largest** minimizer of $j\mapsto|\partial U(j/n,1;r)/\partial d|$ over the real interval $[0,n]$; otherwise $\tilde d^*(w;r)=d^*(w;r)$;
--   4. weekly choice: $\tilde w^*(r)=1$ if $U(\tilde d^*(1;r),1;r)\ge U(\tilde d^*(0;r),0;r)$ and $0$ otherwise (ties go to the weekly), and $\tilde d^*(r)=\tilde d^*(\tilde w^*(r);r)$.
--
--   **Profits, eq. (8).** With a fixed cost $k>0$ per issue,
--   $$\Pi_1(r_1;r_2)=r_1\,\tilde d^*(r)-\frac{k}{u_1},\qquad \Pi_2(r_2;r_1)=r_2\,\tilde w^*(r)-\frac{k}{u_2}.$$
--
--   These are the payoffs of the pricing game whose pure and mixed equilibria are the subject of Lemmas EC.2 and EC.5.
--
--   **Formalization Note** $q$ is defined by the integral, not by its closed form. $\partial U/\partial d$ is Lean's `deriv` of $d\mapsto U(d,1;r)$, a $C^1$ map; no closed form (such as (EC.27)) is substituted. (7) writes the minimizing count $j$; following the proof of Lemma EC.10 (EC.27) it is scaled by $u_1/u_2=1/n$, and the largest minimizer is chosen (footnote 9, p. ec1). For $w=0$ the paper states no tie rule for $d^*$; the same largest-maximizer rule is used. Choices and sets are defined with `sSup` of the (finite, resp. compact) maximizer or minimizer set.
-- source:
--   Chen–Roels, Fast or Slow? Competing on Publication Frequency, SSRN 3986163 (INSEAD WP 2021/74/TOM, 2021), §3.1 eqs. (1)–(4), pp.7–9, and §3.3 eqs. (7)–(8), p.11 (PDF 8–12); footnote 9, p.ec1 (PDF 30)

import Mathlib
import Definitions.Def_PubFrequency_MixedEquilibrium

open Classical

namespace PubFrequency

/-- **Undecayed information, eq. (1)**, Chen–Roels, *Fast or Slow? Competing on Publication
Frequency*, SSRN 3986163 (INSEAD WP 2021/74/TOM), §3.1, p. 7 (PDF 8): information arrives at rate
1 and decays linearly at rate `α`, so the net amount accumulated over `τ` periods is
`q(τ) = ∫₀^τ (1 − min{1, α t}) dt`.

**Formalization Note.** Defined by the integral, as in the paper; the paper's closed form
(`τ(1 − ατ/2)` for `τ ≤ 1/α`, `1/(2α)` otherwise) is a consequence, not the definition. -/
noncomputable def q (α τ : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..τ, (1 - min 1 (α * t))

/-- **Time-average information value, eq. (2)**, Chen–Roels, SSRN 3986163, §3.1, p. 8 (PDF 9):
`v(u, φ) := q(φ u) / u` for a publication cycle `u` of which a fraction `φ` carries new
content. -/
noncomputable def v (α u φ : ℝ) : ℝ :=
  q α (φ * u) / u

/-- **The consumption grid `D`**, Chen–Roels, SSRN 3986163, §3.1, p. 9 (PDF 10):
`D = {i · u₁/u₂ | i = 0, 1, …, u₂/u₁}`.

**Formalization Note.** The slow cycle is `u₂ = n · u₁` with `n : ℕ` ("we restrict the firms'
publication cycles to be integer multiple of each other", p. 9), so `D = {i / n | i = 0, …, n}`. -/
def gridD (n : ℕ) : Set ℝ :=
  {d | ∃ i : ℕ, i ≤ n ∧ d = (i : ℝ) / n}

/-- **Customers' time-average utility, eq. (3)**, Chen–Roels, SSRN 3986163, §3.1, p. 9 (PDF 10):
consuming a fraction `d` of the fast firm's issues ("dailies") and `w ∈ {0, 1}` of the slow
firm's ("weekly"), at prices `r₁, r₂`,
`U(d, w; r, u) = d (v(u₁, 1) − r₁) + w (v(u₂, 1 − d) − r₂)`, with `u₂ = n u₁`.
Firm 1 is the fast publisher. -/
noncomputable def U (α u₁ : ℝ) (n : ℕ) (r₁ r₂ d w : ℝ) : ℝ :=
  d * (v α u₁ 1 - r₁) + w * (v α ((n : ℝ) * u₁) (1 - d) - r₂)

/-- **Exact dailies choice `d*(w; r, u) := argmax_{d ∈ D} U(d, w; r, u)`**, Chen–Roels,
SSRN 3986163, §3.3, p. 11 (PDF 12), with the tie-breaking rule of (4), p. 9 ("the one that contains
the largest number of dailies"): the **largest** maximizer of `d ↦ U(d, w)` over the finite grid
`D`.

**Formalization Note.** For `w = 0` the paper states no tie rule for `d*`; the same "more to
less" rule (footnote 9, p. ec1) is used. The grid is finite and nonempty, so the maximizer set
is finite and nonempty and its `sSup` is its largest element. -/
noncomputable def dStar (α u₁ : ℝ) (n : ℕ) (r₁ r₂ w : ℝ) : ℝ :=
  sSup {d | d ∈ gridD n ∧ ∀ d' ∈ gridD n, U α u₁ n r₁ r₂ d' w ≤ U α u₁ n r₁ r₂ d w}

/-- **Marginal utility of dailies with the weekly, `∂U(d, 1; r, u)/∂d`**, Chen–Roels,
SSRN 3986163, (7), p. 11 (PDF 12).

**Formalization Note.** Lean's `deriv` of the map `d ↦ U(d, 1; r, u)`; this map is `C¹`
(`v(u₂, ·)` has derivative `max{0, 1 − α φ u₂}`), so the derivative exists everywhere. No
closed form is substituted. -/
noncomputable def dU (α u₁ : ℝ) (n : ℕ) (r₁ r₂ d : ℝ) : ℝ :=
  deriv (fun x => U α u₁ n r₁ r₂ x 1) d

/-- **The region of (7)** where the approximation applies, Chen–Roels, SSRN 3986163, p. 11
(PDF 12): `∂U(0, 1)/∂d ≥ 0` and `U(1, 1) < U(1 − u₁/u₂, 1)` (here `u₁/u₂ = 1/n`). -/
def ApproxRegion (α u₁ : ℝ) (n : ℕ) (r₁ r₂ : ℝ) : Prop :=
  0 ≤ dU α u₁ n r₁ r₂ 0 ∧ U α u₁ n r₁ r₂ 1 1 < U α u₁ n r₁ r₂ (1 - 1 / (n : ℝ)) 1

/-- **The count `j*` of (7)**, Chen–Roels, SSRN 3986163, p. 11 (PDF 12):
`argmin_{j ∈ [0, u₂/u₁]} |∂U(j u₁/u₂, 1; r, u)/∂d|`, a minimizer over the **real** interval
`[0, n]`; when it is not unique, the **largest** one (footnote 9, p. ec1: "we select the largest
one"). The minimizer set of a continuous function on a compact interval is nonempty and
compact, and `sSup` is its largest element. -/
noncomputable def jStar (α u₁ : ℝ) (n : ℕ) (r₁ r₂ : ℝ) : ℝ :=
  sSup {j | j ∈ Set.Icc (0 : ℝ) n ∧
    ∀ j' ∈ Set.Icc (0 : ℝ) n, |dU α u₁ n r₁ r₂ (j / n)| ≤ |dU α u₁ n r₁ r₂ (j' / n)|}

/-- **The approximate dailies choice `d̃*(w; r, u)`, eq. (7)**, Chen–Roels, SSRN 3986163, p. 11
(PDF 12): if `w = 1` and the region of (7) holds, `d̃* = (u₁/u₂) · j* = j*/n`; otherwise
`d̃* = d*(w; r, u)`.

**Formalization Note.** (7) writes the argmin `j` itself; the proof of Lemma EC.10 (EC.27),
p. ec9, scales it by `u₁/u₂` to a fraction of dailies, which is the reading used. -/
noncomputable def dTildeW (α u₁ : ℝ) (n : ℕ) (r₁ r₂ w : ℝ) : ℝ :=
  if w = 1 ∧ ApproxRegion α u₁ n r₁ r₂ then jStar α u₁ n r₁ r₂ / n else dStar α u₁ n r₁ r₂ w

/-- **The weekly choice `w̃*(r, u) := argmax_{w ∈ {0,1}} U(d̃*(w; r, u), w; r, u)`**,
Chen–Roels, SSRN 3986163, p. 11 (PDF 12), with the tie-breaking rule of (4), p. 9: on a tie the
portfolio with the weekly is selected. -/
noncomputable def wTilde (α u₁ : ℝ) (n : ℕ) (r₁ r₂ : ℝ) : ℝ :=
  if U α u₁ n r₁ r₂ (dTildeW α u₁ n r₁ r₂ 0) 0 ≤ U α u₁ n r₁ r₂ (dTildeW α u₁ n r₁ r₂ 1) 1
  then 1 else 0

/-- **`d̃*(r, u) := d̃*(w̃*(r, u); r, u)`**, Chen–Roels, SSRN 3986163, p. 11 (PDF 12). -/
noncomputable def dTilde (α u₁ : ℝ) (n : ℕ) (r₁ r₂ : ℝ) : ℝ :=
  dTildeW α u₁ n r₁ r₂ (wTilde α u₁ n r₁ r₂)

/-- **The fast firm's profit in the pricing game, eq. (8)**, Chen–Roels, SSRN 3986163, p. 11
(PDF 12): `Π₁(r₁; r₂, u) = r₁ · d̃*(r, u) − k/u₁`. -/
noncomputable def profit1 (α k u₁ : ℝ) (n : ℕ) (r₁ r₂ : ℝ) : ℝ :=
  r₁ * dTilde α u₁ n r₁ r₂ - k / u₁

/-- **The slow firm's profit in the pricing game, eq. (8)**, Chen–Roels, SSRN 3986163, p. 11
(PDF 12): `Π₂(r₂; r₁, u) = r₂ · w̃*(r, u) − k/u₂`, with `u₂ = n u₁`. Note the argument order:
own price `r₂` first. -/
noncomputable def profit2 (α k u₁ : ℝ) (n : ℕ) (r₂ r₁ : ℝ) : ℝ :=
  r₂ * wTilde α u₁ n r₁ r₂ - k / ((n : ℝ) * u₁)

end PubFrequency


