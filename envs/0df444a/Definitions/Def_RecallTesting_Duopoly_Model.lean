-- Prove2me | Definitions.Def_RecallTesting_Duopoly_Model
-- name    : RecallTesting_Duopoly_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:42.916553+00:00
-- url     : https://prove2.me/theorems/13d2a70a-e62a-46c3-b370-8ae8b116658e
-- title:
--   §3, pp. 7–12, Lemma 1, p. 14, proof of Prop. 2, pp. 36–37 — testing/recall duopoly: vertical-differentiation price game, recall costs, testing-game payoffs, cutoffs
-- statement:
--   This file sets up the two-period duopoly of Kim, Koenigsberg and Ofek, in which two identical firms decide whether to test an innovation before launching it.
--
--   **Primitives.** The mature product has quality $V$ and the innovation quality $V+B$. An untested innovation fails during the first period with probability $\theta$, independently across firms. A firm whose product fails pays the recall cost $\Delta=\rho+\delta\,\pi_1$, where $\pi_1$ is its first-period profit, and in the second period sells a recalled innovation of quality $(V+B)(1-\gamma)$. The standing assumptions are
--   $$V>0,\quad B>0,\quad \rho>0,\quad \delta\in(0,1],\quad \gamma\in(0,1),\quad \theta\in(0,1).$$
--
--   **Consumers and the price game.** In each period a new unit mass of consumers arrives, with tastes $\phi$ uniform on $[0,1]$. A consumer of taste $\phi$ gets utility $\phi\,q-p$ from a product of quality $q$ at price $p$, buys the product of greatest utility when that utility is nonnegative, and splits evenly between the two products when indifferent. The demand $d(q,p;q',p')$ of a product is the Lebesgue measure of the tastes that buy it (counting the indifferent ones with weight $\tfrac12$), and its one-period profit is $p\,d$ (marginal cost is zero). A pair of prices $(p,p')$ is a *price equilibrium* for qualities $(q,q')$ if both are nonnegative and each is a best response, among all nonnegative prices, to the other.
--
--   **Equilibrium prices and period profits.** The price used for quality $q$ against $q'$ is the one computed in the proof of Lemma 1:
--   $$p(q,q')=\begin{cases}\dfrac{2q(q-q')}{4q-q'} & q'<q,\\[2mm] \dfrac{q(q'-q)}{4q'-q} & q<q',\\[2mm] 0 & q=q'.\end{cases}$$
--   The period profit $\pi(q,q')$ is the profit of quality $q$ at these two prices, computed from consumer demand.
--
--   **Testing game.** Each firm chooses $QA\in\{0,1\}$ ($1$ = test). A tester sells the mature product at $t=1$ and the innovation at $t=2$. A non-tester sells the innovation at $t=1$ and, at $t=2$, the innovation if it did not fail or the recalled innovation if it did. The payoff $\Pi^{a,b}$ of a firm choosing $a$ against a rival choosing $b$ is the first-period profit, minus the expected recall cost $\theta(\rho+\delta\pi_1)$ if the firm did not test, plus the expected second-period profit over the four independent recall outcomes. A testing profile is an equilibrium if it is a pure Nash equilibrium of this symmetric $2\times 2$ game (weak best responses).
--
--   **Cutoffs.** With $b=(V+B)(1-\gamma)\gamma-(3+\gamma)^2\rho$, the file defines
--   $$\tilde\theta^{st}=\frac{4B(V+B)^2(3+\gamma)^2}{(V+B)\big(4B(V+B)(3+\gamma)^2\delta-(3V+4B)^2(1-\gamma)\gamma\big)+(3V+4B)^2(3+\gamma)^2\rho},$$
--   $$\underline{\tilde\theta}^{nt},\ \overline{\tilde\theta}^{nt}=\frac{b\mp\sqrt{b^2-\frac{4VB(V+B)^2(5-\gamma)\gamma(3+\gamma)^2}{(3V+4B)^2}}}{2(V+B)(5-\gamma)\gamma},$$
--   $$\tilde\rho^{st}=\frac{(V+B)\big(9V^2(1-\gamma)\gamma+4B^2(9+10\gamma-3\gamma^2-(3+\gamma)^2\delta)+4VB(9+12\gamma-5\gamma^2-(3+\gamma)^2\delta)\big)}{(3V+4B)^2(3+\gamma)^2},$$
--   $$\tilde\rho^{nt}=\frac{(V+B)(3V+4B)(1-\gamma)\gamma-2(V+B)(3+\gamma)\sqrt{VB(5-\gamma)\gamma}}{(3V+4B)(3+\gamma)^2}.$$
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Parameters are a structure `Params`, and `Params.Standing` bundles the standing assumptions; $V>0$ and $B>0$ are implicit on the page and made explicit. Testing decisions are `Bool` with `true` = test. The pure Nash condition is `AGT.IsPureNash` of the published `agt_games` vocabulary, applied to the game with players `Bool` in which player `i` earns $\Pi^{s_i,s_{\neg i}}$. The payoffs are not closed forms: they are built from the recall events and from demand, so the paper's payoff formulas and Lemma 1's profits are theorems. The untested firm's first-period objective in (A.1) is $(1-\theta\delta)\,p\,d-\theta\rho$, a positive affine transform of revenue, so the price equilibrium is posed on revenue $p\,d$; that Lemma 1's prices form a price equilibrium is what justifies using them in the payoffs. `thetaST` divides by its denominator `denST` and the roots take a real square root of `discNT`; every statement guards these with $0<$ `denST` and $0\le$ `discNT`.
-- source:
--   Kim, Koenigsberg & Ofek, I Don’t “Recall”, SSRN working paper 3492105 (Nov. 2019), pp. 7–14 (PDF 8–15), §3, eq. (1), Lemma 1; pp. 34–37 (PDF 35–38), (A.1), proofs of Lemma 1 and Proposition 2, (A.3)–(A.5)

import Mathlib
import Definitions.Def_agt_games

namespace RecallTesting.Duopoly

/-- The primitives of the testing/recall duopoly (Kim–Koenigsberg–Ofek, §3, pp. 7–10):
quality `V` of the mature product, quality improvement `B` of the innovation (so the
innovation has quality `V + B`), fixed recall cost `ρ`, revenue-proportional recall penalty
`δ`, reputation damage `γ` (a recalled innovation has quality `(V + B)(1 - γ)`), and failure
probability `θ` of an untested innovation. -/
structure Params where
  V : ℝ
  B : ℝ
  ρ : ℝ
  δ : ℝ
  γ : ℝ
  θ : ℝ

/-- The standing assumptions of §3: `V > 0`, `B > 0` (implicit on the page), `ρ > 0` (p. 9),
`δ ∈ (0,1]` (p. 9), `γ ∈ (0,1)` (p. 10), `θ ∈ (0,1)` (p. 9). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.V ∧ 0 < P.B ∧ 0 < P.ρ ∧ 0 < P.δ ∧ P.δ ≤ 1 ∧ 0 < P.γ ∧ P.γ < 1 ∧ 0 < P.θ ∧ P.θ < 1

/-- One-period demand for a product of quality `q` sold at price `p` against a rival product of
quality `q'` sold at price `p'` (§3.3, p. 10, and equation (1), p. 11). Consumers form a unit mass
with taste `ϕ` uniform on `[0,1]`; a consumer of taste `ϕ` gets utility `ϕ * q - p` from the
product, buys the product of greatest utility provided that utility is `≥ 0`, and splits evenly
between the two products when indifferent. -/
noncomputable def demand (q p q' p' : ℝ) : ℝ :=
  (MeasureTheory.volume
      {ϕ : ℝ | ϕ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ ϕ * q - p ∧ ϕ * q' - p' < ϕ * q - p}).toReal +
    (1 / 2 : ℝ) * (MeasureTheory.volume
      {ϕ : ℝ | ϕ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ ϕ * q - p ∧ ϕ * q - p = ϕ * q' - p'}).toReal

/-- One-period revenue (= profit, marginal cost being zero, p. 8). -/
noncomputable def revenue (q p q' p' : ℝ) : ℝ := p * demand q p q' p'

/-- `(p, p')` is a Nash equilibrium of the one-period price game between a firm of quality `q`
(price `p`) and a firm of quality `q'` (price `p'`): both prices are nonnegative and each is a
best response, among all nonnegative prices, to the other. -/
def IsPriceEq (q q' p p' : ℝ) : Prop :=
  0 ≤ p ∧ 0 ≤ p' ∧ (∀ x : ℝ, 0 ≤ x → revenue q x q' p' ≤ revenue q p q' p') ∧
    (∀ x : ℝ, 0 ≤ x → revenue q' x q p ≤ revenue q' p' q p)

/-- The equilibrium price of a product of quality `q` against a rival of quality `q'`, as computed
in the proof of Lemma 1 (p. 35): `2q(q - q')/(4q - q')` for the higher quality,
`q(q' - q)/(4q' - q)` for the lower quality, and `0` for equal qualities (Bertrand). -/
noncomputable def eqPrice (q q' : ℝ) : ℝ :=
  if q' < q then 2 * q * (q - q') / (4 * q - q')
  else if q < q' then q * (q' - q) / (4 * q' - q) else 0

/-- The one-period profit of quality `q` against quality `q'` at the prices `eqPrice`, computed
from consumer demand (not a closed form). -/
noncomputable def periodProfit (q q' : ℝ) : ℝ :=
  revenue q (eqPrice q q') q' (eqPrice q' q)

/-- Quality offered at `t = 1` under testing decision `a` (`true` = test, QA = 1): the mature
product `V` if testing, the innovation `V + B` otherwise. -/
def qual1 (P : Params) (a : Bool) : ℝ := if a then P.V else P.V + P.B

/-- Quality offered at `t = 2` under testing decision `a` and recall outcome `fail`: the
innovation `V + B`, unless the product was untested and recalled, when it is `(V + B)(1 - γ)`. -/
def qual2 (P : Params) (a fail : Bool) : ℝ :=
  if a then P.V + P.B else if fail then (P.V + P.B) * (1 - P.γ) else P.V + P.B

/-- Probability of recall outcome `fail` under testing decision `a`: a tested innovation never
fails; an untested one fails with probability `θ`, independently across firms. -/
def failProb (P : Params) (a fail : Bool) : ℝ :=
  if a then (if fail then 0 else 1) else (if fail then P.θ else 1 - P.θ)

/-- The expected two-period payoff `Π^{a,b}` of a firm choosing testing decision `a` against a
rival choosing `b`: first-period profit, minus the expected recall cost `θ(ρ + δ π₁)` if
untested, plus the expected second-period profit over the four independent recall outcomes. -/
noncomputable def payoff (P : Params) (a b : Bool) : ℝ :=
  periodProfit (qual1 P a) (qual1 P b)
    - (if a then 0 else P.θ * (P.ρ + P.δ * periodProfit (qual1 P a) (qual1 P b)))
    + ∑ f : Bool, ∑ g : Bool,
        failProb P a f * failProb P b g * periodProfit (qual2 P a f) (qual2 P b g)

/-- The testing game as a two-player strategic-form game: players `Bool`, each with strategies
`Bool` (`true` = test); player `i` earns `payoff P (s i) (s (!i))`. -/
noncomputable def testingGame (P : Params) : Bool → (Bool → Bool) → ℝ :=
  fun i s => payoff P (s i) (s (!i))

/-- The strategy profile in which player `true` plays `a` and player `false` plays `b`. -/
def profile (a b : Bool) : Bool → Bool := fun i => cond i a b

/-- `(a, b)` is a pure Nash equilibrium of the testing game. -/
def IsNE (P : Params) (a b : Bool) : Prop :=
  AGT.IsPureNash (S := fun _ => Bool) (testingGame P) (profile a b)

/-- The denominator of `θ̃st` in (A.4), p. 37. -/
def denST (P : Params) : ℝ :=
  (P.V + P.B) * (4 * P.B * (P.V + P.B) * (3 + P.γ) ^ 2 * P.δ
      - (3 * P.V + 4 * P.B) ^ 2 * (1 - P.γ) * P.γ)
    + (3 * P.V + 4 * P.B) ^ 2 * (3 + P.γ) ^ 2 * P.ρ

/-- The dual-firm-test cutoff `θ̃st` of (A.4), p. 37. -/
noncomputable def thetaST (P : Params) : ℝ :=
  4 * P.B * (P.V + P.B) ^ 2 * (3 + P.γ) ^ 2 / denST P

/-- `(V + B)(1 - γ)γ - (3 + γ)²ρ`, the linear coefficient in (A.3), p. 37. -/
def bNT (P : Params) : ℝ :=
  (P.V + P.B) * (1 - P.γ) * P.γ - (3 + P.γ) ^ 2 * P.ρ

/-- The discriminant under the square root in (A.3), p. 37. -/
noncomputable def discNT (P : Params) : ℝ :=
  bNT P ^ 2 - 4 * P.V * P.B * (P.V + P.B) ^ 2 * (5 - P.γ) * P.γ * (3 + P.γ) ^ 2
    / (3 * P.V + 4 * P.B) ^ 2

/-- The lower end of the no-firm-test interval `θ̃nt` in (A.3), p. 37. -/
noncomputable def thetaNTlo (P : Params) : ℝ :=
  (bNT P - Real.sqrt (discNT P)) / (2 * (P.V + P.B) * (5 - P.γ) * P.γ)

/-- The upper end of the no-firm-test interval `θ̃nt` in (A.3), p. 37. -/
noncomputable def thetaNThi (P : Params) : ℝ :=
  (bNT P + Real.sqrt (discNT P)) / (2 * (P.V + P.B) * (5 - P.γ) * P.γ)

/-- The recall-cost threshold `ρ̃st` of (A.5), p. 37. -/
noncomputable def rhoST (P : Params) : ℝ :=
  (P.V + P.B) * (9 * P.V ^ 2 * (1 - P.γ) * P.γ
      + 4 * P.B ^ 2 * (9 + 10 * P.γ - 3 * P.γ ^ 2 - (3 + P.γ) ^ 2 * P.δ)
      + 4 * P.V * P.B * (9 + 12 * P.γ - 5 * P.γ ^ 2 - (3 + P.γ) ^ 2 * P.δ))
    / ((3 * P.V + 4 * P.B) ^ 2 * (3 + P.γ) ^ 2)

/-- The recall-cost threshold `ρ̃nt` of (A.3), p. 37. -/
noncomputable def rhoNT (P : Params) : ℝ :=
  ((P.V + P.B) * (3 * P.V + 4 * P.B) * (1 - P.γ) * P.γ
      - 2 * (P.V + P.B) * (3 + P.γ) * Real.sqrt (P.V * P.B * (5 - P.γ) * P.γ))
    / ((3 * P.V + 4 * P.B) * (3 + P.γ) ^ 2)

end RecallTesting.Duopoly


