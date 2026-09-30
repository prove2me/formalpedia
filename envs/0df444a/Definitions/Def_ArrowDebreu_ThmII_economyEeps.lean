-- Prove2me | Definitions.Def_ArrowDebreu_ThmII_economyEeps
-- name    : ArrowDebreu_ThmII_economyEeps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:15:41.76668+00:00
-- url     : https://prove2.me/theorems/d05654f6-d37e-4553-9fde-848efad323a0
-- title:
--   The abstract economies $E^\varepsilon$ and $\tilde E^\varepsilon$, the vector $\zeta'$ and the sets $\hat X'_i$, $\hat Y'_j$
-- statement:
--   Let $\pi$ be the number of elements of $\mathcal P$ and, for $\varepsilon>0$,
--   $$P^\varepsilon=\{p\in P : p_h\ge\varepsilon\text{ for all }h\in\mathcal P\}.$$
--
--   The abstract economy $E^\varepsilon$ has $m+n+1$ players. Consumer $i$ chooses $x_i\in X_i$, receives $u_i(x_i)$, and is constrained to
--   $$A_i(\bar x_i)=\Big\{x_i\in X_i : p\cdot x_i\le p\cdot\zeta_i+\max\Big[0,\sum_{j=1}^n\alpha_{ij}\,p\cdot y_j\Big]\Big\}.$$
--   Producer $j$ chooses $y_j\in Y_j$ and receives $p\cdot y_j$. The market participant chooses $p\in P^\varepsilon$ and receives $p\cdot z$ with $z=\sum_ix_i-\sum_jy_j-\zeta$. With $P$ in place of $P^\varepsilon$ this is the economy $E$ of the proof of Theorem I.
--
--   Given lower bounds $\xi_i$ of the $X_i$ (Assumption II) and $\xi=\sum_i\xi_i$, let
--   $$\zeta'_h=\zeta_h+\frac1\pi\sum_{k\in\mathcal P}(\zeta_k-\xi_k).$$
--   $\hat X'_i$ is the set of $x_i\in X_i$ that can be completed by $x_{i'}\in X_{i'}$ ($i'\neq i$) and $y_j\in Y_j$ with $x-y\leqq\zeta'$; $\hat Y'_j$ is defined likewise. For $c'>0$ let $C'=\{x : |x_h|\le c'\text{ for all }h\}$. The truncated economy $\tilde E^\varepsilon$ is $E^\varepsilon$ with $X_i$ replaced by $X_i\cap C'$ and $Y_j$ by $Y_j\cap C'$ everywhere.
--
--   These are the auxiliary economies through which the proof of Theorem II passes: the price floor $\varepsilon$ on labor keeps every consumer's income above the minimum expenditure, and the cube makes the action sets compact.
--
--   **Formalization Note** One constructor builds $E$, $E^\varepsilon$ and $\tilde E^\varepsilon$ from the action sets. $\zeta'$ takes the lower bounds $\xi_i$ as an argument. The paper prints "$\zeta'$ being the vector whose components are $\zeta_1,\dots,\zeta_l$", a misprint for $\zeta'_1,\dots,\zeta'_l$. If $\mathcal P$ were empty, which Assumption VII excludes, Lean's $1/0=0$ would give $\zeta'=\zeta$.
-- source:
--   Arrow & Debreu, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 274 (PDF p. 11) §3.1.0; p. 282 (PDF p. 19) §5.0, §5.1.0; p. 283 (PDF p. 20) §5.1.1 (ζ′); p. 284 (PDF p. 21) §5.2.0, §5.2.1

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmII

variable {l m n : ℕ}

/-- The `m + n + 1` participants of the abstract economies of §3.1.0 and §5.1.0 (p. 274, PDF p. 11;
p. 282, PDF p. 19): the consumption units `inl i`, the production units `inr (inl j)`, and the
market participant `inr (inr ())`, who chooses prices. -/
abbrev Player (m n : ℕ) := Fin m ⊕ Fin n ⊕ Unit

/-- The consumption vectors `x_i` of a profile. -/
def consOf (a : Player m n → Fin l → ℝ) : Fin m → Fin l → ℝ := fun i => a (Sum.inl i)

/-- The production plans `y_j` of a profile. -/
def prodOf (a : Player m n → Fin l → ℝ) : Fin n → Fin l → ℝ := fun j => a (Sum.inr (Sum.inl j))

/-- The price vector `p` of a profile (the market participant's action). -/
def priceOf (a : Player m n → Fin l → ℝ) : Fin l → ℝ := a (Sum.inr (Sum.inr ()))

/-- **The abstract economy of §3.1.0** (p. 274, PDF p. 11), built from consumption sets `X'`,
production sets `Y'` and a price domain `P'`:
`[X'_1, ⋯, X'_m, Y'_1, ⋯, Y'_n, P', u_1(x_1), ⋯, u_m(x_m), p·y_1, ⋯, p·y_n, p·z, A_1(x̄_1), ⋯, A_m(x̄_m), Y'_1, ⋯, Y'_n, P']`
where `z = Σ_i x_i − Σ_j y_j − Σ_i ζ_i` and
`A_i(x̄_i) = {x_i | x_i ∈ X'_i, p·x_i ≦ p·ζ_i + max[0, Σ_{j=1}^n α_{ij} p·y_j]}`.
Consumer `i` chooses `x_i ∈ X'_i` subject to `x_i ∈ A_i(x̄_i)` and receives `u_i(x_i)`; producer
`j` chooses `y_j ∈ Y'_j` (unconstrained by others) and receives `p·y_j`; the market participant
chooses `p ∈ P'` and receives `p·z`.

With `P' = P` this is the paper's `E` (§3.1.0); with `P' = P^ε` it is `E^ε` (§5.1.0, see
`economyEeps`); with `X'_i = X_i ∩ C'`, `Y'_j = Y_j ∩ C'`, `P' = P^ε` it is `Ẽ^ε` (§5.2.1, see
`economyEtildeEps`). -/
def economyE (E : Economy l m n) (X' : Fin m → Set (Fin l → ℝ)) (Y' : Fin n → Set (Fin l → ℝ))
    (P' : Set (Fin l → ℝ)) : AbstractEconomy (Player m n) l where
  act
    | Sum.inl i => X' i
    | Sum.inr (Sum.inl j) => Y' j
    | Sum.inr (Sum.inr _) => P'
  payoff
    | Sum.inl i => fun a => E.u i (a (Sum.inl i))
    | Sum.inr (Sum.inl j) => fun a => priceOf a ⬝ᵥ a (Sum.inr (Sum.inl j))
    | Sum.inr (Sum.inr _) => fun a => priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a)
  constr
    | Sum.inl i => fun a =>
        {x | x ∈ X' i ∧ priceOf a ⬝ᵥ x ≤
          priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j))}
    | Sum.inr (Sum.inl j) => fun _ => Y' j
    | Sum.inr (Sum.inr _) => fun _ => P'
  constr_indep := by
    intro i a b h
    rcases i with i | j | u
    · have hp : priceOf a = priceOf b := h _ (by simp)
      have hy : prodOf a = prodOf b := funext fun j => h _ (by simp)
      simp only [hp, hy]
    · rfl
    · rfl
  constr_subset := by
    intro i a _
    rcases i with i | j | u
    · exact fun x hx => hx.1
    · exact le_rfl
    · exact le_rfl

/-- The contracted price domain `P^ε = {p | p ∈ P, p_h ≧ ε for all h ∈ 𝒫}` (§5.0, p. 282,
PDF p. 19). The paper uses it for `0 < ε ≦ 1/(2π)`, `π` the number of elements of `𝒫`. -/
def priceSimplexEps (E : Economy l m n) (ε : ℝ) : Set (Fin l → ℝ) :=
  {p | p ∈ priceSimplex l ∧ ∀ h ∈ productive E, ε ≤ p h}

/-- **The abstract economy `E^ε`** (§5.1.0, p. 282, PDF p. 19):
`[X_1, ⋯, X_m, Y_1, ⋯, Y_n, P^ε, u_1(x_1), ⋯, u_m(x_m), p·y_1, ⋯, p·y_n, p·z, A_1(x̄_1), ⋯, A_m(x̄_m), Y_1, ⋯, Y_n, P^ε]`,
"the same as `E`, except that the price domain has been contracted to `P^ε`". -/
def economyEeps (E : Economy l m n) (ε : ℝ) : AbstractEconomy (Player m n) l :=
  economyE E E.X E.Y (priceSimplexEps E ε)

/-- The cube `C' = {x | |x_h| ≦ c' for all h}` (§5.2.0, p. 284, PDF p. 21; as §3.3.3). -/
def cube (l : ℕ) (c : ℝ) : Set (Fin l → ℝ) := {x | ∀ h, |x h| ≤ c}

/-- **The truncated abstract economy `Ẽ^ε`** (§5.2.1, p. 284, PDF p. 21): `E^ε` with `X_i` replaced
by `X̃'_i = X_i ∩ C'` and `Y_j` by `Ỹ'_j = Y_j ∩ C'` everywhere, `C' = cube l c'`. Its consumer
constraint sets are the paper's `Ã'_i(x̄_i)`. -/
def economyEtildeEps (E : Economy l m n) (ε c' : ℝ) : AbstractEconomy (Player m n) l :=
  economyE E (fun i => E.X i ∩ cube l c') (fun j => E.Y j ∩ cube l c') (priceSimplexEps E ε)

/-- The vector `ζ'` of §5.1.1 (p. 283, PDF p. 20):
`ζ'_h = ζ_h + (1/π) Σ_{k ∈ 𝒫} (ζ_k − ξ_k)`, where `ζ = Σ_i ζ_i`, `ξ = Σ_i ξ_i`, `π` is the number of
elements of `𝒫`, and `ξ_i` are the lower bounds of the consumption sets from Assumption II
(`ξ_i ≦ x_i` for all `x_i ∈ X_i`).

**Formalization Note.** The lower bounds `ξ_i` are an existential of Assumption II; `ζ'` takes
them as an argument `ξ`, and every statement about `ζ'` assumes `ξ i ≤ x` for all `x ∈ X i`. The
paper prints "`ζ'` being the vector whose components are `ζ_1, ⋯, ζ_l`", a misprint for
`ζ'_1, ⋯, ζ'_l`. When `𝒫` is empty (excluded by Assumption VII) Lean's `1/0 = 0` gives `ζ' = ζ`. -/
noncomputable def zetaPrime (E : Economy l m n) (ξ : Fin m → Fin l → ℝ) : Fin l → ℝ :=
  fun h => totalEndowment E h +
    (1 / ((productive E).card : ℝ)) * ∑ k ∈ productive E, (totalEndowment E k - ∑ i, ξ i k)

/-- The set `X̂'_i` (§5.2.0, p. 284, PDF p. 21):
`{x_i | x_i ∈ X_i, and there exist x_{i'} ∈ X_{i'} for all i' ≠ i, y_j ∈ Y_j for all j such that x − y ≦ ζ'}`,
where `x = Σ_i x_i`, `y = Σ_j y_j`. -/
def XhatPrime (E : Economy l m n) (ξ : Fin m → Fin l → ℝ) (i : Fin m) : Set (Fin l → ℝ) :=
  {xi | xi ∈ E.X i ∧ ∃ x : Fin m → Fin l → ℝ, ∃ y : Fin n → Fin l → ℝ,
    x i = xi ∧ (∀ i', x i' ∈ E.X i') ∧ (∀ j, y j ∈ E.Y j) ∧ ∑ i', x i' - ∑ j, y j ≤ zetaPrime E ξ}

/-- The set `Ŷ'_j` (§5.2.0, p. 284, PDF p. 21):
`{y_j | y_j ∈ Y_j, and there exist x_i ∈ X_i for all i, y_{j'} ∈ Y_{j'} for all j' ≠ j such that x − y ≦ ζ'}`. -/
def YhatPrime (E : Economy l m n) (ξ : Fin m → Fin l → ℝ) (j : Fin n) : Set (Fin l → ℝ) :=
  {yj | yj ∈ E.Y j ∧ ∃ x : Fin m → Fin l → ℝ, ∃ y : Fin n → Fin l → ℝ,
    y j = yj ∧ (∀ i, x i ∈ E.X i) ∧ (∀ j', y j' ∈ E.Y j') ∧ ∑ i, x i - ∑ j', y j' ≤ zetaPrime E ξ}

end ArrowDebreu.ThmII


