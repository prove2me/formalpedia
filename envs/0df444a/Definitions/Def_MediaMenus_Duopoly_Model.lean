-- Prove2me | Definitions.Def_MediaMenus_Duopoly_Model
-- name    : MediaMenus_Duopoly_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:11.257479+00:00
-- url     : https://prove2.me/theorems/be9a76f2-6aa9-4ef9-a308-c65c4879d122
-- title:
--   §2, §4.2, pp. 6–9, 18, 47 — duopoly of ad-supported platforms: two consumer types, two-item price/advertising menus, homing choice, Cournot ad price, revenue, equilibrium
-- statement:
--   This file fixes the duopoly model of DeValve and Pekeč (§2 and §4.2), the equilibrium concept used in the proof of their Proposition 3, and the closed-form quantities that appear in that proposition and its proof.
--
--   **Parameters.** A consumer has base value $v$ for content. She is of type $\theta\in\{L,H\}$ with advertising disutility $d^\theta$, where $d^H>d^L>0$; type $H$ occurs with probability $r\in(0,1)$ and type $L$ with probability $1-r$ (we write $r^L=1-r$, $r^H=r$). The two platforms are substitutes with parameter $\gamma\in(0,1)$, and $w$ is the maximum market value of advertising. The standing assumptions are
--   $$0<v,\quad 0<d^L<d^H,\quad d^L<w,\quad 0<r<1,\quad 0<\gamma<1 .$$
--
--   **Menus and choices.** Each platform $i\in\{1,2\}$ offers a two-item menu $\{(s^1_i,a^1_i),(s^2_i,a^2_i)\}$ of subscription prices $s\in\mathbb R$ (possibly negative) and advertising quantities $a\ge 0$; the two items may coincide. A consumer either abstains (utility $0$), single-homes on one platform with one of its items, or multi-homes with one item from each platform. Write $c^\theta(s,a)=d^\theta a+s$ for the cost of an item to type $\theta$.
--
--   **Utilities.** Single-homing with item $(s_i,a_i)$ and consumption $x_i\ge 0$ gives $v x_i-\tfrac12x_i^2-(d^\theta a_i+s_i)$, display (1); multi-homing with items $(s_1,a_1),(s_2,a_2)$ and consumptions $x_1,x_2\ge0$ gives
--   $$\sum_{i=1}^2\big(v x_i-\tfrac12 x_i^2-(d^\theta a_i+s_i)\big)-\gamma x_1x_2,$$
--   display (2). The utility of a choice is the supremum of the corresponding expression over nonnegative consumption.
--
--   **Revenue.** The advertising market clears per consumer type: if the consumer sees the ad quantities $a_i$ of the platforms she uses, the ad price is $p=w-\sum_i a_i$, display (3), and a platform she uses with item $(s_i,a_i)$ earns $s_i+p\,a_i$, display (4). A platform's expected revenue is the $r^L$/$r^H$-weighted sum over the two types.
--
--   **Equilibrium.** The paper does not define the term; its proofs use the following concept, which is written out here.
--   1. *Consumer optimality.* Each type chooses a utility-maximizing choice.
--   2. *Homing ties.* If some multi-homing choice is optimal, the consumer multi-homes (Lemma 4 C, p. 37, and constraint (19) are weak inequalities; on p. 53 type $H$ is indifferent and multi-homes). If some participating choice is optimal, she does not abstain.
--   3. *Deviations.* A menu profile with consumer choices is an equilibrium if the menus are admissible, the choices satisfy 1–2, and no platform $i$ has an admissible menu $M'$ and a consumer response to the deviated profile satisfying 1–2 and 4 under which its expected revenue strictly exceeds its current one (the deviating platform may select any such response, as the weak constraints (17), (18), (21) allow).
--   4. *Status quo on the rival.* A type that uses the non-deviating platform both before and after the deviation keeps her item there (p. 55: "platform 1 cannot incentivize the type L consumer to choose the type H menu item from platform 2").
--
--   **Closed forms.** $\rho=(1-\gamma)/(1+\gamma)$, display (6); $\alpha=\big(w-d^H-(1-r)(d^H-d^L)/r\big)^+$, display (5). The items of Proposition 3 are
--   $$(s^L,a^L)=\Big(\tfrac{\rho v^2}{2}-d^La^L-(d^H-d^L)a^H,\ \tfrac{w-d^L}{3}\Big),\qquad (s^H,a^H)=\Big(\tfrac{\rho v^2}{2}-d^Ha^H,\ \tfrac{\alpha}{3}\Big).$$
--   The best-response ad quantities (22), given the rival's ad quantities $a^L_j,a^H_j$, are
--   $$a^L_i=\Big(\max\Big(\tfrac{w-d^L-a^L_j}{2},\ \tfrac{w-d^H-(r^La^L_j+r^Ha^H_j)}{2}\Big)\Big)^+,\quad a^H_i=\Big(\min\Big(\tfrac{r^H(w-d^H-a^H_j)-r^L(d^H-d^L)}{2r^H},\ \tfrac{w-d^H-(r^La^L_j+r^Ha^H_j)}{2}\Big)\Big)^+,$$
--   and the best-response prices (24) are $s^L_i=\tfrac{(1-\gamma)v^2}{2(1+\gamma)}-d^La^L_i-(d^H-d^L)a^H_i$ and $s^H_i=\tfrac{(1-\gamma)v^2}{2(1+\gamma)}-d^Ha^H_i$.
--
--   The model is the object every statement of the mission is about; the equilibrium concept is what makes Proposition 3 a statement about a game rather than about an optimization program.
--
--   **Formalization Note.** Platforms are `Fin 2` (the paper's platforms 1, 2 are `0`, `1`), and `other i` is the rival. A menu is `Fin 2 → ℝ × ℝ` with entries `(s, a)`; the two-item strategy space is the paper's own after Lemma 7 (p. 47). A choice is `abstain`, `single i k` or `multi k₀ k₁` (item slot `k₀` on platform `0`, `k₁` on platform `1`). `utility` is `sSup` of the utility over consumption in `[0, ∞)` (or `[0, ∞)²`); these sets are bounded above because $\gamma<1$, and Lemma 6 A, B (separate milestones) give their closed forms. `IsResponse` is rules 1–2, `IsEquilibrium` is rules 1–4: the deviation clause requires the inequality for every response allowed by rules 1, 2 and 4, which is the same as letting the deviator pick the best of them. In `eqMenu` slot `0` holds the $L$ item and slot `1` the $H$ item, and `eqChoice` has type $L$ multi-home on slot `0` and type $H$ on slot `1` of both platforms. The added hypotheses $v>0$ and $w>d^L$ are explained in the goal theorem.
-- source:
--   DeValve & Pekeč, Optimal Price/Advertising Menus for Two-Sided Media Platforms, SSRN 2715531 (version of 2021-04-15), pp. 6–9 (§2, displays (1)–(4)), p. 12 (display (5)), p. 16 (display (6)), p. 47 (two-item menus), p. 57 (displays (22), (24)); equilibrium concept from Lemma 4 C (p. 37) and the proof of Proposition 3 (pp. 53–55)

import Mathlib

namespace MediaMenus.Duopoly

/-- The two consumer types: `L` (low advertising disutility) and `H` (high). -/
inductive Ty
  | L
  | H
  deriving DecidableEq

/-- The model parameters of §2: base value `v`, maximum ad value `w`, advertising
disutilities `dL < dH`, probability `r` of type `H`, substitutability `γ`. -/
structure Params where
  v : ℝ
  w : ℝ
  dL : ℝ
  dH : ℝ
  r : ℝ
  γ : ℝ

/-- Standing assumptions: `d^H > d^L > 0`, `r ∈ (0,1)`, `γ ∈ (0,1)` (pp. 6–7), and the
two disclosed additions `v > 0` and `w > d^L`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.v ∧ 0 < P.dL ∧ P.dL < P.dH ∧ P.dL < P.w ∧ 0 < P.r ∧ P.r < 1 ∧ 0 < P.γ ∧ P.γ < 1

/-- Advertising disutility of a type. -/
def Params.d (P : Params) : Ty → ℝ
  | .L => P.dL
  | .H => P.dH

/-- Probability of a type: `1 - r` for `L`, `r` for `H`. -/
def Params.prob (P : Params) : Ty → ℝ
  | .L => 1 - P.r
  | .H => P.r

/-- A menu item `(s, a)`: subscription price `s` and advertising quantity `a`. -/
abbrev Item := ℝ × ℝ

/-- A two-item menu (p. 47); the two items may coincide. -/
abbrev Menu := Fin 2 → Item

/-- A menu is admissible when every advertising quantity is nonnegative; prices are free (p. 9). -/
def Menu.Admissible (M : Menu) : Prop := ∀ k, 0 ≤ (M k).2

/-- A strategy profile: platform `i` (the paper's platform `i + 1`) offers menu `M i`. -/
abbrev Profile := Fin 2 → Menu

/-- The other platform. -/
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

/-- A consumer's homing and item choice. -/
inductive Choice
  | abstain
  /-- use platform `i` only, with item `k` of its menu -/
  | single (i : Fin 2) (k : Fin 2)
  /-- multi-home: item `k₀` on platform `0` and item `k₁` on platform `1` -/
  | multi (k₀ k₁ : Fin 2)
  deriving DecidableEq

/-- The cost `d^θ a + s` of an item to a type-`θ` consumer. -/
def cost (P : Params) (θ : Ty) (it : Item) : ℝ := P.d θ * it.2 + it.1

/-- Single-homing utility (1) at consumption `x`. -/
noncomputable def singleUtil (P : Params) (θ : Ty) (it : Item) (x : ℝ) : ℝ :=
  P.v * x - x ^ 2 / 2 - cost P θ it

/-- Multi-homing utility (2) at consumptions `x₀, x₁`. -/
noncomputable def multiUtil (P : Params) (θ : Ty) (it₀ it₁ : Item) (x₀ x₁ : ℝ) : ℝ :=
  (P.v * x₀ - x₀ ^ 2 / 2 - cost P θ it₀) + (P.v * x₁ - x₁ ^ 2 / 2 - cost P θ it₁)
    - P.γ * x₀ * x₁

/-- The utility of a choice: the supremum of (1) or (2) over nonnegative consumption;
the outside option gives `0`. -/
noncomputable def utility (P : Params) (θ : Ty) (M : Profile) : Choice → ℝ
  | .abstain => 0
  | .single i k => sSup (singleUtil P θ (M i k) '' Set.Ici 0)
  | .multi k₀ k₁ =>
      sSup ((fun x : ℝ × ℝ => multiUtil P θ (M 0 k₀) (M 1 k₁) x.1 x.2) ''
        (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)))

/-- The item slot a choice uses on platform `i`, if it uses platform `i`. -/
def Choice.itemOn (i : Fin 2) : Choice → Option (Fin 2)
  | .abstain => none
  | .single j k => if j = i then some k else none
  | .multi k₀ k₁ => some (if i = 0 then k₀ else k₁)

/-- The total advertising quantity `Σ_i a_i` the consumer sees under a choice. -/
def adsSeen (M : Profile) : Choice → ℝ
  | .abstain => 0
  | .single i k => (M i k).2
  | .multi k₀ k₁ => (M 0 k₀).2 + (M 1 k₁).2

/-- Platform `i`'s revenue (4) `s_i + p a_i` from a consumer making choice `c`,
at the ad price (3) `p = w - Σ a`; zero if the consumer does not use platform `i`. -/
def platRev (P : Params) (M : Profile) (i : Fin 2) (c : Choice) : ℝ :=
  match c.itemOn i with
  | none => 0
  | some k => (M i k).1 + (M i k).2 * (P.w - adsSeen M c)

/-- Platform `i`'s expected revenue when type `θ` makes choice `c θ`. -/
def expRev (P : Params) (M : Profile) (i : Fin 2) (c : Ty → Choice) : ℝ :=
  P.prob .L * platRev P M i (c .L) + P.prob .H * platRev P M i (c .H)

/-- `c` maximizes type `θ`'s utility among all choices. -/
def IsOptimal (P : Params) (θ : Ty) (M : Profile) (c : Choice) : Prop :=
  ∀ c', utility P θ M c' ≤ utility P θ M c

/-- `c` is a multi-homing choice. -/
def Choice.IsMulti : Choice → Prop
  | .multi _ _ => True
  | _ => False

/-- An admissible consumer response (tie rules 1–2): optimal; multi-homing whenever some
multi-homing choice is optimal; participation whenever some participating choice is optimal. -/
def IsResponse (P : Params) (θ : Ty) (M : Profile) (c : Choice) : Prop :=
  IsOptimal P θ M c ∧
  ((∃ k₀ k₁, IsOptimal P θ M (.multi k₀ k₁)) → c.IsMulti) ∧
  ((∃ c', c' ≠ .abstain ∧ IsOptimal P θ M c') → c ≠ .abstain)

/-- Equilibrium (tie rules 1–4): admissible menus, consumer responses, and no platform `i`
gains from any admissible deviation `M'` under any response `c'` of the consumers in which a
type that uses the rival platform both before and after keeps her item there. -/
def IsEquilibrium (P : Params) (M : Profile) (c : Ty → Choice) : Prop :=
  (∀ i, (M i).Admissible) ∧ (∀ θ, IsResponse P θ M (c θ)) ∧
  ∀ (i : Fin 2) (M' : Menu), M'.Admissible → ∀ c' : Ty → Choice,
    (∀ θ, IsResponse P θ (Function.update M i M') (c' θ)) →
    (∀ θ k k', (c θ).itemOn (other i) = some k → (c' θ).itemOn (other i) = some k' → k' = k) →
    expRev P (Function.update M i M') i c' ≤ expRev P M i c

/-- `ρ = (1 - γ)/(1 + γ)`, display (6). -/
noncomputable def rho (P : Params) : ℝ := (1 - P.γ) / (1 + P.γ)

/-- `α = (w - d^H - (1 - r)(d^H - d^L)/r)^+`, display (5). -/
noncomputable def alphaQ (P : Params) : ℝ :=
  max (P.w - P.dH - (1 - P.r) * (P.dH - P.dL) / P.r) 0

/-- The menu items of Proposition 3. -/
noncomputable def eqItem (P : Params) : Ty → Item
  | .L => (rho P * P.v ^ 2 / 2 - P.dL * ((P.w - P.dL) / 3) - (P.dH - P.dL) * (alphaQ P / 3),
           (P.w - P.dL) / 3)
  | .H => (rho P * P.v ^ 2 / 2 - P.dH * (alphaQ P / 3), alphaQ P / 3)

/-- The menu of Proposition 3: slot `0` holds the type-`L` item, slot `1` the type-`H` item. -/
noncomputable def eqMenu (P : Params) : Menu := ![eqItem P .L, eqItem P .H]

/-- The consumer choices of Proposition 3: type `L` multi-homes on slot `0` (the `L` item) of
both platforms, type `H` on slot `1` (the `H` item). -/
def eqChoice : Ty → Choice
  | .L => .multi 0 0
  | .H => .multi 1 1

/-- Best-response ad quantity for type `L`, display (22), given the rival's ad quantities
`aLj`, `aHj` for the two types. -/
noncomputable def brAdL (P : Params) (aLj aHj : ℝ) : ℝ :=
  max (max ((P.w - P.dL - aLj) / 2) ((P.w - P.dH - ((1 - P.r) * aLj + P.r * aHj)) / 2)) 0

/-- Best-response ad quantity for type `H`, display (22). -/
noncomputable def brAdH (P : Params) (aLj aHj : ℝ) : ℝ :=
  max (min ((P.r * (P.w - P.dH - aHj) - (1 - P.r) * (P.dH - P.dL)) / (2 * P.r))
    ((P.w - P.dH - ((1 - P.r) * aLj + P.r * aHj)) / 2)) 0

/-- Best-response price for type `L`, display (24), given the platform's own ad quantities. -/
noncomputable def brPriceL (P : Params) (aL aH : ℝ) : ℝ :=
  (1 - P.γ) * P.v ^ 2 / (2 * (1 + P.γ)) - P.dL * aL - (P.dH - P.dL) * aH

/-- Best-response price for type `H`, display (24). -/
noncomputable def brPriceH (P : Params) (aH : ℝ) : ℝ :=
  (1 - P.γ) * P.v ^ 2 / (2 * (1 + P.γ)) - P.dH * aH

end MediaMenus.Duopoly


