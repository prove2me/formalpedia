-- Prove2me | Definitions.Def_ArrowDebreu_ThmI_economyE
-- name    : ArrowDebreu_ThmI_economyE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:37:38.042408+00:00
-- url     : https://prove2.me/theorems/458c9d49-f699-43bf-82fc-f34225ec530f
-- title:
--   The abstract economies $E$ and $\tilde E$ of the proof of Theorem I, and the attainable sets $\hat X_i$, $\hat Y_j$
-- statement:
--   Fix an economy with data $Y_j, X_i, u_i, \zeta_i, \alpha_{ij}$ and let $P$ be the price simplex. Given sets $X_i'$ and $Y_j'$, the abstract economy $E[X', Y']$ has $m + n + 1$ players:
--
--   1. consumer $i$ chooses $x_i \in X_i'$, receives $u_i(x_i)$, and is constrained to
--   $$A_i(\bar x_i) = \Big\{x_i \in X_i' : p\cdot x_i \leqq p\cdot\zeta_i + \max\Big[0, \sum_{j=1}^n \alpha_{ij}\, p\cdot y_j\Big]\Big\};$$
--   2. producer $j$ chooses $y_j \in Y_j'$ without constraint from the others and receives $p\cdot y_j$;
--   3. the **market participant** chooses $p \in P$ without constraint and receives $p\cdot z$, where $z = \sum_i x_i - \sum_j y_j - \sum_i \zeta_i$.
--
--   The paper's abstract economy $E$ (§3.1.0) is $E[X, Y]$. For $c \in \mathbb R$ let $C = \{x : |x_h| \le c \text{ for all } h\}$; the truncated economy $\tilde E$ (§3.3.4) is $E[X \cap C, Y \cap C]$, i.e. $E$ with $X_i$ replaced by $\tilde X_i = X_i \cap C$ and $Y_j$ by $\tilde Y_j = Y_j \cap C$ everywhere, and its consumer constraint sets are the paper's $\tilde A_i(\bar x_i)$.
--
--   The **attainable sets** (§3.3.0) are
--   $$\hat X_i = \{x_i \in X_i : \exists\, x_{i'} \in X_{i'}\ (i' \ne i),\ y_j \in Y_j \text{ with } z \leqq 0\},\qquad \hat Y_j = \{y_j \in Y_j : \exists\, x_i \in X_i,\ y_{j'} \in Y_{j'}\ (j' \ne j) \text{ with } z \leqq 0\}.$$
--
--   Equilibrium points of $E$ are exactly competitive equilibria; $\tilde E$ is the compact version to which the equilibrium-existence lemma applies once $C$ is large enough to contain all $\hat X_i$ and $\hat Y_j$ in its interior.
--
--   **Formalization Note** Players are indexed by $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,n \oplus \mathrm{Unit}$; a profile lists $x_i$, $y_j$ and $p$, and `consOf`, `prodOf`, `priceOf` extract them. The same constructor builds $E$ and $\tilde E$.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, pp. 274–277 (PDF pp. 11–14), §3.1.0 (E and A_i), §3.3.0 (X̂_i, Ŷ_j), §3.3.3 (C, X̃_i, Ỹ_j), §3.3.4 (Ẽ, Ã_i)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

variable {l m n : ℕ}

/-- The `m + n + 1` participants of the abstract economy `E` of §3.1.0 (p. 274, PDF p. 11): the
consumption units `inl i`, the production units `inr (inl j)`, and the market participant
`inr (inr ())`, who chooses prices. -/
abbrev Player (m n : ℕ) := Fin m ⊕ Fin n ⊕ Unit

/-- The consumption vectors `x_i` of a profile of `E`. -/
def consOf (a : Player m n → Fin l → ℝ) : Fin m → Fin l → ℝ := fun i => a (Sum.inl i)

/-- The production plans `y_j` of a profile of `E`. -/
def prodOf (a : Player m n → Fin l → ℝ) : Fin n → Fin l → ℝ := fun j => a (Sum.inr (Sum.inl j))

/-- The price vector `p` of a profile of `E` (the market participant's action). -/
def priceOf (a : Player m n → Fin l → ℝ) : Fin l → ℝ := a (Sum.inr (Sum.inr ()))

/-- **The abstract economy of §3.1.0** (p. 274, PDF p. 11), built from consumption sets `X'` and
production sets `Y'`:
`[X'_1, ⋯, X'_m, Y'_1, ⋯, Y'_n, P, u_1(x_1), ⋯, u_m(x_m), p·y_1, ⋯, p·y_n, p·z, A_1(x̄_1), ⋯, A_m(x̄_m), Y'_1, ⋯, Y'_n, P]`
where `P` is the price simplex, `z = Σ_i x_i − Σ_j y_j − Σ_i ζ_i`, and
`A_i(x̄_i) = {x_i | x_i ∈ X'_i, p·x_i ≦ p·ζ_i + max[0, Σ_{j=1}^n α_{ij} p·y_j]}`.
Consumer `i` chooses `x_i ∈ X'_i` subject to `x_i ∈ A_i(x̄_i)` and receives `u_i(x_i)`; producer
`j` chooses `y_j ∈ Y'_j` (unconstrained by others) and receives `p·y_j`; the market participant
chooses `p ∈ P` and receives `p·z`.

`economyE E E.X E.Y` is the paper's `E` (§3.1.0); `economyE E (X_i ∩ C) (Y_j ∩ C)` is the
truncated economy `Ẽ` of §3.3.4 (see `economyEtilde`), in which "`X_i` is replaced by `X̃_i` and
`Y_j` by `Ỹ_j` everywhere". -/
def economyE (E : Economy l m n) (X' : Fin m → Set (Fin l → ℝ)) (Y' : Fin n → Set (Fin l → ℝ)) :
    AbstractEconomy (Player m n) l where
  act
    | Sum.inl i => X' i
    | Sum.inr (Sum.inl j) => Y' j
    | Sum.inr (Sum.inr _) => priceSimplex l
  payoff
    | Sum.inl i => fun a => E.u i (a (Sum.inl i))
    | Sum.inr (Sum.inl j) => fun a => priceOf a ⬝ᵥ a (Sum.inr (Sum.inl j))
    | Sum.inr (Sum.inr _) => fun a => priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a)
  constr
    | Sum.inl i => fun a =>
        {x | x ∈ X' i ∧ priceOf a ⬝ᵥ x ≤
          priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j))}
    | Sum.inr (Sum.inl j) => fun _ => Y' j
    | Sum.inr (Sum.inr _) => fun _ => priceSimplex l
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

/-- The cube `C = {x | |x_h| ≦ c for all h}` of §3.3.3 (p. 277, PDF p. 14). -/
def cube (l : ℕ) (c : ℝ) : Set (Fin l → ℝ) := {x | ∀ h, |x h| ≤ c}

/-- **The truncated abstract economy `Ẽ`** (§3.3.4, p. 277, PDF p. 14): `E` of §3.1.0 with `X_i`
replaced by `X̃_i = X_i ∩ C` and `Y_j` by `Ỹ_j = Y_j ∩ C` everywhere, `C = cube l c`; its
consumer constraint sets are the paper's `Ã_i(x̄_i)`. -/
def economyEtilde (E : Economy l m n) (c : ℝ) : AbstractEconomy (Player m n) l :=
  economyE E (fun i => E.X i ∩ cube l c) (fun j => E.Y j ∩ cube l c)

/-- The attainable consumption set `X̂_i` (§3.3.0, p. 276, PDF p. 13):
`{x_i | x_i ∈ X_i, there exist x_{i'} ∈ X_{i'} for each i' ≠ i and y_j ∈ Y_j for each j such that z ≦ 0}`. -/
def Xhat (E : Economy l m n) (i : Fin m) : Set (Fin l → ℝ) :=
  {xi | xi ∈ E.X i ∧ ∃ x : Fin m → Fin l → ℝ, ∃ y : Fin n → Fin l → ℝ,
    x i = xi ∧ (∀ i', x i' ∈ E.X i') ∧ (∀ j, y j ∈ E.Y j) ∧ excessDemand E x y ≤ 0}

/-- The attainable production set `Ŷ_j` (§3.3.0, p. 276, PDF p. 13):
`{y_j | y_j ∈ Y_j, there exist x_i ∈ X_i for each i, y_{j'} ∈ Y_{j'} for each j' ≠ j such that z ≦ 0}`. -/
def Yhat (E : Economy l m n) (j : Fin n) : Set (Fin l → ℝ) :=
  {yj | yj ∈ E.Y j ∧ ∃ x : Fin m → Fin l → ℝ, ∃ y : Fin n → Fin l → ℝ,
    y j = yj ∧ (∀ i, x i ∈ E.X i) ∧ (∀ j', y j' ∈ E.Y j') ∧ excessDemand E x y ≤ 0}

end ArrowDebreu.ThmI


