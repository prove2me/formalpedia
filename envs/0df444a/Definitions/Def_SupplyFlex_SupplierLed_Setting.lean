-- Prove2me | Definitions.Def_SupplyFlex_SupplierLed_Setting
-- name    : SupplyFlex_SupplierLed_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:09.028328+00:00
-- url     : https://prove2.me/theorems/80b1c3d8-c075-4a49-aa7e-8b3a3b2ecbcf
-- title:
--   §2, pp. 7–8; App. A2.1, PDF 40–43 — the supply-flexibility and price-only Stackelberg games, Assumptions 1–3, subgame-perfect equilibria, closed forms (1)–(4), problem (A2.8)
-- statement:
--   A buyer faces random demand $D$ with density $f$, sells at a fixed retail price $r$, and loses unmet demand at no further cost. A supplier produces at marginal cost $c$ per unit of input, but regular production is disrupted: an input of size $y$ yields $\alpha y$, where $\alpha \sim \mathrm{Bernoulli}(p)$. A reliable expedited source supplies any quantity at cost $s$ per unit.
--
--   **Standing assumptions** (the model $M = (r, c, s, p, f, \bar a)$ is *standard*):
--   1. $c > 0$ and $0 < p \le 1$;
--   2. Assumption 1: $\min\{s, r\} > c/p$;
--   3. Assumption 2: $f$ is a probability density, positive on $[0, \bar a)$ and zero outside it ($\bar a = \infty$ allowed), and the generalized failure rate $g(\xi) = \xi f(\xi)/\bar F(\xi)$ is non-decreasing on $[0, \bar a)$, where $\bar F(x) = \int_x^\infty f(t)\,dt$;
--   4. demand has a finite mean (Table A1.1);
--   5. $f$ is continuous on $[0, \bar a)$ (added, see below).
--
--   Write $G(q) = \bar F(q) - q f(q) = \bar F(q)\bigl[1 - q f(q)/\bar F(q)\bigr]$, the left-hand side of equations (1)–(3).
--
--   **The two games.** Write $b = \bar\beta = 1 - \beta$ for the *guaranteed fraction*: under a contract $(w, b)$ the supplier must deliver at least $b q$ of an order $q$ (the paper's flexibility fraction $\beta$ is not used). The supplier offers $(w, b)$ with $w > 0$; in the price-only contract $b = 1$, in the supply-flexibility contract $b \in [0, 1]$. The buyer orders $q \ge 0$; the supplier chooses an input $y \ge 0$; $\alpha$ is realized; the supplier delivers $z \in [bq, q]$, expediting any shortfall $(z - \alpha y)^+$; the buyer pays $wz$. Ex post, the supplier earns
--   $$\pi^S = w z - c y - s\,(z - \alpha y)^+,$$
--   and the buyer earns, in expectation over demand, $\pi^B = r\,\mathbb E\min(z, D) - w z$.
--
--   A strategy profile $\sigma$ consists of an offer $(w, b)$ and rules $Q(w, b)$, $Y(w, b, q)$, $Z(w, b, q, y, \alpha)$. It is a **subgame-perfect equilibrium** if, at every admissible history ($w > 0$, $b$ admissible, $q, y \ge 0$):
--   1. $Z$ is the *least* maximiser of $\pi^S$ over $z \in [bq, q]$ (Assumption 3: an indifferent supplier delivers the least quantity);
--   2. $Y$ maximises the supplier's expected profit $\mathbb E_\alpha \pi^S$ over $y \ge 0$;
--   3. $Q$ maximises the buyer's expected profit $\mathbb E_\alpha \pi^B$ over $q \ge 0$;
--   4. the offer is admissible and maximises the supplier's expected profit over all admissible offers.
--
--   Here $\mathbb E_\alpha h = p\,h(1) + (1-p)\,h(0)$. The buyer's and supplier's equilibrium profits $\Pi^B$, $\Pi^S$ are these expectations along the equilibrium path.
--
--   **Closed forms.** Given candidate roots $\tilde q$, $q^o$, $\hat q^*$, $\check q$ of (1)–(4) (p. 10),
--   $$w^o = \frac{r\bigl(p q^o \bar F(q^o) + (1-p)\hat q^* \bar F(\hat q^*)\bigr)}{p q^o + (1-p)\hat q^*},$$
--   $\kappa^* = q^o$ if $w^o \le s$; otherwise $\kappa^* = \check q$ if $\check q(ps - c) \ge \tilde q\bigl(r\bar F(\tilde q) - (1-p)s - c\bigr)$, and $\kappa^* = \tilde q$ otherwise. The equilibrium guaranteed fraction of Theorem 3 is $\bar\beta^* = 0$ if $s > r$; else $\bar\beta^* = 1$ if $s < w^o$ and $\check q(ps - c) < \tilde q\bigl(r\bar F(\tilde q) - (1-p)s - c\bigr)$; else $\bar\beta^* = \hat q^*/\kappa^*$. The equilibrium price is
--   $$w^* = \frac{r\bigl[p \bar F(\kappa^*) + (1-p)\bar\beta^* \bar F(\bar\beta^*\kappa^*)\bigr]}{p + (1-p)\bar\beta^*}.$$
--
--   **Problem (A2.8).** Over $(q, \hat q)$ with $0 \le \hat q \le q$ and $r\bigl[pq\bar F(q) + (1-p)\hat q \bar F(\hat q)\bigr] \le (pq + (1-p)\hat q)s$, maximise
--   $$\hat\Pi^S(q, \hat q) = r\bigl[pq\bar F(q) + (1-p)\hat q \bar F(\hat q)\bigr] - (1-p)s\hat q - cq.$$
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note.** The demand law is Lebesgue measure with density $f$, and $\mathbb E\min(z, D)$ is the published `SupplyChainTheory.expSales`. The disruption $\alpha$ is a `Bool`. The paper's "Stackelberg equilibrium" solved by backward induction is read as subgame perfection, with optimality required at every history, not only on the path. Two hypotheses are added and disclosed: continuity of $f$ on $[0, \bar a)$ (so that (1)–(4) have solutions; every distribution the paper names satisfies it), and $w > 0$ for offers (at $w \le 0$ the buyer's problem has no maximiser; Lemma A2.1 shows equilibria have $w > c/p$). The roots of (1)–(4) are not defined here: theorems take them as arguments with hypotheses saying they solve the equations.
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break (SSRN 3143238), pp. 7–10, §2, Assumptions 1–3, eqs. (1)–(4), w°, κ*, Theorem 3 (i)–(ii); App. A1 p. 1 (PDF 33), Table A1.1; App. A2 pp. 1–4 (PDF 40–43), A2.1.1–A2.1.4, (A2.8)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyFlex.SupplierLed

open MeasureTheory
open scoped ENNReal

/-- Model data of §2, pp. 7–8: retail price `r`, regular production cost `c` per unit of input,
expedited supply cost `s` per unit, reliability `p = P(α = 1)`, demand density `f`, and the
right end `abar` of the support `[0, ā)` of demand (`ā = ∞` allowed). -/
structure Model where
  r : ℝ
  c : ℝ
  s : ℝ
  p : ℝ
  f : ℝ → ℝ
  abar : ℝ≥0∞

/-- The support `[0, ā)` of the demand distribution (Assumption 2). -/
def supp (abar : ℝ≥0∞) : Set ℝ := {x | 0 ≤ x ∧ ENNReal.ofReal x < abar}

/-- The law of demand `D`: Lebesgue measure with density `f`. -/
noncomputable def demandLaw (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (f x))

/-- The survival function `F̄(x) = P(D > x) = ∫_x^∞ f`. -/
noncomputable def Fbar (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in Set.Ioi x, f t

/-- `G(q) = F̄(q)[1 − q f(q)/F̄(q)] = F̄(q) − q f(q)`, the left side of (1)–(3). -/
noncomputable def G (f : ℝ → ℝ) (q : ℝ) : ℝ := Fbar f q - q * f q

/-- Assumption 2's IGFR: the generalized failure rate `g(ξ) = ξ f(ξ) / F̄(ξ)` is increasing
(non-decreasing) on the support `[0, ā)`. -/
def IGFR (f : ℝ → ℝ) (abar : ℝ≥0∞) : Prop :=
  MonotoneOn (fun ξ => ξ * f ξ / Fbar f ξ) (supp abar)

/-- Standing assumptions: `c > 0`, `p ∈ (0, 1]`, Assumption 1 (`min{s, r} > c/p`), Assumption 2
(support `[0, ā)` with a positive density there, IGFR), a probability density with finite mean
(Table A1.1), and — added, disclosed — continuity of `f` on `[0, ā)`. -/
structure Model.Std (M : Model) : Prop where
  c_pos : 0 < M.c
  p_pos : 0 < M.p
  p_le_one : M.p ≤ 1
  assm1_s : M.c / M.p < M.s
  assm1_r : M.c / M.p < M.r
  abar_pos : 0 < M.abar
  f_meas : Measurable M.f
  f_pos : ∀ x ∈ supp M.abar, 0 < M.f x
  f_zero : ∀ x, x ∉ supp M.abar → M.f x = 0
  f_int : Integrable M.f ∧ ∫ x, M.f x = 1
  mean_fin : Integrable (fun x => x * M.f x)
  igfr : IGFR M.f M.abar
  f_cont : ContinuousOn M.f (supp M.abar)

/-- The two contracts. -/
inductive Regime
  | priceOnly
  | flex

/-- Admissible guaranteed fractions `b = β̄ = 1 − β`: the price-only contract forces `b = 1`,
the supply-flexibility contract allows any `b ∈ [0, 1]`. -/
def Regime.B : Regime → Set ℝ
  | .priceOnly => {1}
  | .flex => Set.Icc 0 1

/-- Expectation over the disruption `α ∼ Bernoulli(p)`; `α = true` means regular production
succeeds. -/
def Eα (p : ℝ) (h : Bool → ℝ) : ℝ := p * h true + (1 - p) * h false

/-- Supplier's ex-post profit: input `y`, output `α y`, delivery `z`, shortfall expedited at `s`. -/
def supplierExPost (M : Model) (w y z : ℝ) (α : Bool) : ℝ :=
  w * z - M.c * y - M.s * max (z - (if α then y else 0)) 0

/-- Buyer's profit given delivery `z`, in expectation over demand: `r E min(z, D) − w z`. -/
noncomputable def buyerExPost (M : Model) (w z : ℝ) : ℝ :=
  M.r * SupplyChainTheory.expSales (demandLaw M.f) z - w * z

/-- A strategy profile: the supplier's contract `(w, b)`, the buyer's order rule `Q(w, b)`, the
supplier's production rule `Y(w, b, q)` and delivery rule `Z(w, b, q, y, α)`. -/
structure Profile where
  w : ℝ
  b : ℝ
  Q : ℝ → ℝ → ℝ
  Y : ℝ → ℝ → ℝ → ℝ
  Z : ℝ → ℝ → ℝ → ℝ → Bool → ℝ

/-- Admissible contract offers: a positive wholesale price and an admissible guaranteed fraction. -/
def Admissible (k : Regime) (w b : ℝ) : Prop := 0 < w ∧ b ∈ k.B

/-- Supplier's expected profit from input `y`, given the delivery rule of `σ`. -/
def prodValue (M : Model) (σ : Profile) (w b q y : ℝ) : ℝ :=
  Eα M.p (fun α => supplierExPost M w y (σ.Z w b q y α) α)

/-- Buyer's expected profit from order `q`, given the production and delivery rules of `σ`. -/
noncomputable def orderValue (M : Model) (σ : Profile) (w b q : ℝ) : ℝ :=
  Eα M.p (fun α => buyerExPost M w (σ.Z w b q (σ.Y w b q) α))

/-- Supplier's expected profit from offering `(w, b)`, given the continuation of `σ`. -/
def contractValue (M : Model) (σ : Profile) (w b : ℝ) : ℝ :=
  prodValue M σ w b (σ.Q w b) (σ.Y w b (σ.Q w b))

/-- Subgame-perfect (Stackelberg) equilibrium, optimality at every admissible history:
(Z) the delivery is the least maximiser of the supplier's ex-post profit over `[b q, q]`
(Assumption 3); (Y) the input maximises the supplier's expected profit over `y ≥ 0`;
(Q) the order maximises the buyer's expected profit over `q ≥ 0`; (top) the offered contract is
admissible and maximises the supplier's expected profit over all admissible offers. -/
def IsSPE (M : Model) (k : Regime) (σ : Profile) : Prop :=
  (∀ w b q y : ℝ, ∀ α : Bool, Admissible k w b → 0 ≤ q → 0 ≤ y →
      IsLeast {z | z ∈ Set.Icc (b * q) q ∧
                   ∀ z' ∈ Set.Icc (b * q) q, supplierExPost M w y z' α ≤ supplierExPost M w y z α}
        (σ.Z w b q y α)) ∧
  (∀ w b q : ℝ, Admissible k w b → 0 ≤ q →
      0 ≤ σ.Y w b q ∧ ∀ y', 0 ≤ y' → prodValue M σ w b q y' ≤ prodValue M σ w b q (σ.Y w b q)) ∧
  (∀ w b : ℝ, Admissible k w b →
      0 ≤ σ.Q w b ∧ ∀ q', 0 ≤ q' → orderValue M σ w b q' ≤ orderValue M σ w b (σ.Q w b)) ∧
  Admissible k σ.w σ.b ∧
  ∀ w' b' : ℝ, Admissible k w' b' → contractValue M σ w' b' ≤ contractValue M σ σ.w σ.b

/-- The buyer's equilibrium expected profit `Π^B` of profile `σ`. -/
noncomputable def buyerProfit (M : Model) (σ : Profile) : ℝ :=
  orderValue M σ σ.w σ.b (σ.Q σ.w σ.b)

/-- The supplier's equilibrium expected profit `Π^S` of profile `σ`. -/
def supplierProfit (M : Model) (σ : Profile) : ℝ := contractValue M σ σ.w σ.b

/-- `w° = r(p q° F̄(q°) + (1 − p) q̂* F̄(q̂*)) / (p q° + (1 − p) q̂*)`, p. 10. -/
noncomputable def wo (M : Model) (qo qh : ℝ) : ℝ :=
  M.r * (M.p * qo * Fbar M.f qo + (1 - M.p) * qh * Fbar M.f qh) / (M.p * qo + (1 - M.p) * qh)

/-- `κ*`, p. 10: `q°` if `w° ≤ s`; otherwise `q̌` if `q̌(ps − c) ≥ q̃(r F̄(q̃) − (1 − p)s − c)`,
and `q̃` otherwise. -/
noncomputable def kappaStar (M : Model) (qt qo qh qc : ℝ) : ℝ :=
  if wo M qo qh ≤ M.s then qo
  else if qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c) ≤ qc * (M.p * M.s - M.c) then qc
  else qt

/-- `β̄*` of Theorem 3 (i), p. 10: `0` if `s > r`; otherwise `1` if `s < w°` and
`q̌(ps − c) < q̃(r F̄(q̃) − (1 − p)s − c)`; else `q̂*/κ*`. -/
noncomputable def betaStar (M : Model) (qt qo qh qc : ℝ) : ℝ :=
  if M.r < M.s then 0
  else if M.s < wo M qo qh ∧
      qc * (M.p * M.s - M.c) < qt * (M.r * Fbar M.f qt - (1 - M.p) * M.s - M.c) then 1
  else qh / kappaStar M qt qo qh qc

/-- The equilibrium wholesale price of Theorem 3 (ii), p. 10:
`w = r[p F̄(κ*) + (1 − p) β̄ F̄(β̄ κ*)] / (p + (1 − p) β̄)`. -/
noncomputable def wStar (M : Model) (qt qo qh qc : ℝ) : ℝ :=
  M.r * (M.p * Fbar M.f (kappaStar M qt qo qh qc) +
      (1 - M.p) * betaStar M qt qo qh qc *
        Fbar M.f (betaStar M qt qo qh qc * kappaStar M qt qo qh qc)) /
    (M.p + (1 - M.p) * betaStar M qt qo qh qc)

/-- Objective of problem (A2.8), App. A2 p. 4 (PDF 43), in `x = (q, q̂)`:
`r[p q F̄(q) + (1 − p) q̂ F̄(q̂)] − (1 − p) s q̂ − c q`. -/
noncomputable def a28Obj (M : Model) (x : ℝ × ℝ) : ℝ :=
  M.r * (M.p * x.1 * Fbar M.f x.1 + (1 - M.p) * x.2 * Fbar M.f x.2) -
    (1 - M.p) * M.s * x.2 - M.c * x.1

/-- Feasible set of problem (A2.8): `0 ≤ q̂ ≤ q` and
`r[p q F̄(q) + (1 − p) q̂ F̄(q̂)] ≤ (p q + (1 − p) q̂) s`. -/
def a28Feasible (M : Model) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.2 ∧ x.2 ≤ x.1 ∧
       M.r * (M.p * x.1 * Fbar M.f x.1 + (1 - M.p) * x.2 * Fbar M.f x.2) ≤
         (M.p * x.1 + (1 - M.p) * x.2) * M.s}

end SupplyFlex.SupplierLed


