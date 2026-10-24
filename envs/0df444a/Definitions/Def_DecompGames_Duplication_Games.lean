-- Prove2me | Definitions.Def_DecompGames_Duplication_Games
-- name    : DecompGames_Duplication_Games
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:36:36.566827+00:00
-- url     : https://prove2.me/theorems/4428b8f2-e2bc-4338-a914-2c63bc253958
-- title:
--   Games, measure and co-measure vectors, the classes NSG, μ-NoG, γ-PG, (μ,γ)-HG, the inner products (2.13)–(2.15) and the (μ,γ)-decomposition (Definitions 2.1–2.2, pp. 7–10)
-- statement:
--   This module sets up the objects of Sections 2.1–2.4.
--
--   1. **Games** (p. 7). There is a finite set $N$ of players; player $i$ has a finite set $S^i$ of strategies, and $S=\prod_{i\in N}S^i$ is the set of strategy profiles $s=(s^i)_{i\in N}$. A game is a vector $g=(g^i)_{i\in N}$ of payoff functions $g^i:S\to\mathbb R$. For a profile $s$, $s^{-i}$ is its subprofile without player $i$ and $(t^i,s^{-i})$ is $s$ with player $i$'s strategy replaced by $t^i$.
--   2. **Measure vectors** (p. 7). $\mu=(\mu^i)_{i\in N}$ with each $\mu^i$ a strictly positive measure on $S^i$; the product measure is $\mu(s)=\prod_{i\in N}\mu^i(s^i)$ (2.1), the total mass is $\mu^i(S^i)=\sum_{t^i\in S^i}\mu^i(t^i)$, and the normalization is $\bar\mu^i(s^i)=\mu^i(s^i)/\mu^i(S^i)$ (2.3).
--   3. **Co-measure vectors** (Definition 2.1). $\gamma=(\gamma^i)_{i\in N}$ with each $\gamma^i$ a strictly positive measure on $S^{-i}$, i.e. a positive function $\gamma^i(s^{-i})$.
--   4. **The four classes** (Definition 2.2). A game $g$ is
--      - *nonstrategic* ($g\in\mathsf{NSG}$) if each $g^i(s^i,s^{-i})=\ell^i(s^{-i})$ does not depend on $s^i$ (2.4);
--      - *$\mu$-normalized* ($g\in\mu\text{-}\mathsf{NoG}$) if $\sum_{s^i\in S^i}\mu^i(s^i)g^i(s^i,s^{-i})=0$ for all $i$ and $s^{-i}$ (2.5);
--      - *$\gamma$-potential* ($g\in\gamma\text{-}\mathsf{PG}$) if there is $\Psi:S\to\mathbb R$ with $\gamma^i(s^{-i})\big(g^i(t^i,s^{-i})-g^i(s^i,s^{-i})\big)=\Psi(t^i,s^{-i})-\Psi(s^i,s^{-i})$ for all $i$, $s^i,t^i$, $s^{-i}$ (2.6);
--      - *$(\mu,\gamma)$-harmonic* ($g\in(\mu,\gamma)\text{-}\mathsf{HG}$) if for every $s\in S$
--      $$\sum_{i\in N}\sum_{t^i\in S^i}\mu^i(t^i)\gamma^i(s^{-i})\big(g^i(s^i,s^{-i})-g^i(t^i,s^{-i})\big)=0. \qquad (2.7)$$
--   5. **Inner products** (p. 10). On $C_0=\{h:S\to\mathbb R\}$, $\langle h,f\rangle_0=\sum_{s\in S}\mu(s)h(s)f(s)$ (2.13); $(\gamma^ih)(s)=\gamma^i(s^{-i})h(s)$ (2.14); on games
--   $$\langle g_1,g_2\rangle_{\mu,\gamma}=\sum_{i\in N}\mu^i(S^i)\,\langle\gamma^ig_1^i,\gamma^ig_2^i\rangle_0. \qquad (2.15)$$
--   6. **The $(\mu,\gamma)$-decomposition** (p. 10). $(n,p,h)$ is a $(\mu,\gamma)$-decomposition of $g$ if $n\in\mathsf{NSG}$, $p\in\mu\text{-}\mathsf{NoG}\cap\gamma\text{-}\mathsf{PG}$, $h\in\mu\text{-}\mathsf{NoG}\cap(\mu,\gamma)\text{-}\mathsf{HG}$ and $g=n+p+h$; in the paper's notation $n=g_{(\mu,\gamma)\text{-NS}}$, $p=g_{(\mu,\gamma)\text{-P}}$, $h=g_{(\mu,\gamma)\text{-H}}$ (2.18).
--
--   These are the objects of the paper's generalization of the Candogan–Menache–Ozdaglar–Parrilo decomposition of games, and of every result of this mission.
--
--   **Formalization Note** Players form a finite type `ι` and strategy sets are finite types `S i`; a profile is `∀ i, S i` and $(t^i,s^{-i})$ is `Function.update s i t`. A game is `ι → (∀ i, S i) → ℝ`, so sums of games are pointwise. A measure vector is its point-mass function `μ i : S i → ℝ`; positivity is the separate predicate `IsMeasureVec`. A co-measure $\gamma^i$ is a function of the full profile, and `IsCoMeasureVec` requires positivity and invariance under changing coordinate $i$, so `γ i s` is $\gamma^i(s^{-i})$. Conditions "for all $s^{-i}$" quantify over full profiles whose $i$-th coordinate is ignored. The standing assumptions $n\ge2$ and $|S^i|\ge2$ are not imposed. Junk value: `normalized μ i a` divides by $\mu^i(S^i)$, which is positive whenever $S^i$ is nonempty and $\mu^i>0$. The printed misprints of Definition 2.2 ("co-measure on $S^i$" for $S^{-i}$; $g$ for $g^i$ in (2.5)) are read as intended.
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, pp. 7–8, Definitions 2.1–2.2, (2.1)–(2.7); p. 10, (2.13)–(2.15), (2.18)

import Mathlib

namespace DecompGames.Duplication

open Finset

/-- A game with player set `ι` and strategy sets `S i` (p. 7): the vector of payoff functions
`g = (gⁱ)_{i ∈ N}`, `gⁱ : S → ℝ`, with `S = ×_{i ∈ N} Sⁱ`; `g i s` is `gⁱ(s)`. -/
abbrev Game (ι : Type) (S : ι → Type) : Type := ι → (∀ i, S i) → ℝ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- `μ = (μⁱ)_{i ∈ N}` is a vector of strictly positive measures, `μⁱ` on `Sⁱ` (p. 7); a measure
on a finite set is given by its point masses `μ i a = μⁱ(a)`. -/
def IsMeasureVec (μ : ∀ i, S i → ℝ) : Prop :=
  ∀ i (a : S i), 0 < μ i a

/-- `γ = (γⁱ)_{i ∈ N}` is a co-measure vector (Definition 2.1, p. 7): each `γⁱ` is a strictly
positive measure on `S⁻ⁱ`. It is encoded as a function of the full profile `s` that does not depend
on player `i`'s own coordinate `sⁱ`, so `γ i s = γⁱ(s⁻ⁱ)`. -/
def IsCoMeasureVec (γ : ι → (∀ i, S i) → ℝ) : Prop :=
  (∀ i s, 0 < γ i s) ∧ ∀ i (s : ∀ j, S j) (a : S i), γ i (Function.update s i a) = γ i s

/-- The product measure `μ(s) = ∏_{i ∈ N} μⁱ(sⁱ)` (2.1). -/
def productMeasure (μ : ∀ i, S i → ℝ) (s : ∀ i, S i) : ℝ :=
  ∏ i, μ i (s i)

/-- The total mass `μⁱ(Sⁱ) = ∑_{tⁱ ∈ Sⁱ} μⁱ(tⁱ)`. -/
def mass (μ : ∀ i, S i → ℝ) (i : ι) : ℝ :=
  ∑ a, μ i a

/-- The normalization `μ̄ⁱ(sⁱ) = μⁱ(sⁱ) / ∑_{tⁱ} μⁱ(tⁱ)` (2.3). -/
noncomputable def normalized (μ : ∀ i, S i → ℝ) (i : ι) (a : S i) : ℝ :=
  μ i a / mass μ i

/-- Definition 2.2(a), (2.4): `g` is nonstrategic, i.e. each `gⁱ(sⁱ, s⁻ⁱ) = ℓⁱ(s⁻ⁱ)` does not
depend on player `i`'s own strategy. The class is `NSG`. -/
def IsNonstrategic (g : Game ι S) : Prop :=
  ∀ i (s : ∀ j, S j) (a : S i), g i (Function.update s i a) = g i s

/-- Definition 2.2(b), (2.5): `g` is `μ`-normalized, i.e.
`∑_{sⁱ ∈ Sⁱ} μⁱ(sⁱ) gⁱ(sⁱ, s⁻ⁱ) = 0` for every `i` and every `s⁻ⁱ` (here `s⁻ⁱ` is read off a
full profile `s`, whose own coordinate is ignored). The class is `μ-NoG`. -/
def IsNormalized (μ : ∀ i, S i → ℝ) (g : Game ι S) : Prop :=
  ∀ i (s : ∀ j, S j), ∑ a, μ i a * g i (Function.update s i a) = 0

/-- Definition 2.2(c), (2.6): `g` is `γ`-potential, i.e. there is `Ψ : S → ℝ` with
`γⁱ(s⁻ⁱ)(gⁱ(tⁱ, s⁻ⁱ) − gⁱ(sⁱ, s⁻ⁱ)) = Ψ(tⁱ, s⁻ⁱ) − Ψ(sⁱ, s⁻ⁱ)` for all `i`, `sⁱ, tⁱ`, `s⁻ⁱ`.
The class is `γ-PG`. -/
def IsPotential (γ : ι → (∀ i, S i) → ℝ) (g : Game ι S) : Prop :=
  ∃ Ψ : (∀ i, S i) → ℝ, ∀ i (s : ∀ j, S j) (a b : S i),
    γ i s * (g i (Function.update s i b) - g i (Function.update s i a)) =
      Ψ (Function.update s i b) - Ψ (Function.update s i a)

/-- Definition 2.2(d), (2.7): `g` is `(μ, γ)`-harmonic, i.e. for every `s ∈ S`,
`∑_{i ∈ N} ∑_{tⁱ ∈ Sⁱ} μⁱ(tⁱ) γⁱ(s⁻ⁱ) (gⁱ(sⁱ, s⁻ⁱ) − gⁱ(tⁱ, s⁻ⁱ)) = 0`.
The class is `(μ, γ)-HG`. -/
def IsHarmonic (μ : ∀ i, S i → ℝ) (γ : ι → (∀ i, S i) → ℝ) (g : Game ι S) : Prop :=
  ∀ s : ∀ j, S j, ∑ i, ∑ a, μ i a * γ i s * (g i s - g i (Function.update s i a)) = 0

/-- The inner product on `C₀ = {h : S → ℝ}` (2.13): `⟨h, f⟩₀ = ∑_{s ∈ S} μ(s) h(s) f(s)`, with the
(unnormalized) product measure `μ(s)`. -/
def ip0 (μ : ∀ i, S i → ℝ) (h f : (∀ i, S i) → ℝ) : ℝ :=
  ∑ s, productMeasure μ s * h s * f s

/-- `γⁱh` (2.14): `(γⁱh)(s) = γⁱ(s⁻ⁱ) h(s)`. -/
def coScale (γ : ι → (∀ i, S i) → ℝ) (i : ι) (h : (∀ i, S i) → ℝ) : (∀ i, S i) → ℝ :=
  fun s => γ i s * h s

/-- The inner product on games (2.15): `⟨g₁, g₂⟩_{μ,γ} = ∑_{i ∈ N} μⁱ(Sⁱ) ⟨γⁱg₁ⁱ, γⁱg₂ⁱ⟩₀`. -/
def ipGame (μ : ∀ i, S i → ℝ) (γ : ι → (∀ i, S i) → ℝ) (g₁ g₂ : Game ι S) : ℝ :=
  ∑ i, mass μ i * ip0 μ (coScale γ i (g₁ i)) (coScale γ i (g₂ i))

/-- `(n, p, h)` is a `(μ, γ)`-decomposition of `g` (Theorem 2.11 and (2.18), p. 10): `n ∈ NSG`,
`p ∈ μ-NoG ∩ γ-PG`, `h ∈ μ-NoG ∩ (μ, γ)-HG`, and `g = n + p + h`, i.e. `n = g_{(μ,γ)-NS}`,
`p = g_{(μ,γ)-P}`, `h = g_{(μ,γ)-H}`. -/
def IsDecomposition (μ : ∀ i, S i → ℝ) (γ : ι → (∀ i, S i) → ℝ) (g n p h : Game ι S) : Prop :=
  IsNonstrategic n ∧ (IsNormalized μ p ∧ IsPotential γ p) ∧
    (IsNormalized μ h ∧ IsHarmonic μ γ h) ∧ g = n + p + h

end DecompGames.Duplication


