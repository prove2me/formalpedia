-- Prove2me | Definitions.Def_CurtailLoan_BankLoan_Model
-- name    : CurtailLoan_BankLoan_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:39.416932+00:00
-- url     : https://prove2.me/theorems/6155efcc-04a3-440c-a828-a65684df0e29
-- title:
--   §3, §4.1, App. A.3.1, A.4.2–A.4.3 — capital-constrained newsvendor with bank loan and loan insurance, goodwill Stackelberg equilibrium, thresholds tk, wI, wII
-- statement:
--   The model of Wang and Cai (§3, pp. 7–10; Appendix A.3.1 and A.4.2–A.4.3) and the thresholds through which its equilibrium is described (§4.1, p. 11).
--
--   **Demand.** Consumer demand $\xi$ has CDF $F$, complementary CDF $\bar F = 1 - F$, density $f$ vanishing on $(-\infty, 0)$, and failure rate $h(x) = f(x)/\bar F(x)$. The retail price is normalized to $1$ and leftovers have no salvage value. The expected sales of an order $Q \ge 0$ are
--   $$S(Q) = \mathbb E\min(\xi, Q) = Q - \int_0^Q F(x)\,dx,$$
--   and $\bar F^{-1}(w)$ (the smallest $Q \ge 0$ with $\bar F(Q) \le w$) and $S^{-1}$ (the smallest $Q \ge 0$ with $S(Q) \ge y$) are the inverses used throughout.
--
--   **Firms and contracts.** A supplier with unit cost $c$ sets a wholesale price $w$. The buyer has initial capital $l$. A bank lends under a risk-control mechanism that lets the buyer spend at most $u + l - \tau$ on the order (the *initial loan limit* $u$) and charges a fixed fee $\tau$; an insurer raises the limit to $v + l - \tau - t$ (the *insured loan limit* $v$) for a fixed premium $t$. The buyer chooses one of three modes and an order $Q \ge 0$:
--
--   1. no loan: $wQ \le l$, profit $S(Q) - wQ$;
--   2. bank loan: $wQ \le u + l - \tau$, profit $S(Q) - wQ - \tau$;
--   3. insured bank loan: $wQ \le v + l - \tau - t$, profit $S(Q) - wQ - \tau - t$.
--
--   The supplier earns $\Pi_S = (w - c)Q$. The game is solved backwards with the paper's goodwill tie-breaking rule (p. 10): among its profit-maximizing choices the buyer picks one maximizing the supplier's profit, and among its profit-maximizing prices $w \in (0, 1]$ the supplier picks one maximizing the buyer's profit. An *equilibrium* is a triple (price, mode, order) produced this way; $\Pi^{I*}_S$ and $\Pi^{I*}_B$ are the firms' profits at it.
--
--   **Thresholds** (each is the paper's equation; "the two roots" of an equation are the two ends of the set where the left side is strictly exceeded, "the unique maximum" is a maximizer):
--
--   1. $w^E$ solves $w^E[1 - Q^E h(Q^E)] = c$ with $Q^E = \bar F^{-1}(w^E)$; $\hat w$ maximizes $w\bar F^{-1}(w)$.
--   2. $w^u_1 < w^u_2$ are the roots of $u + l - \tau = w\bar F^{-1}(w)$, and $w^l_1 < w^l_2$ those of $l = w\bar F^{-1}(w)$.
--   3. $\tau_0(w) = S(\bar F^{-1}(w)) - w\bar F^{-1}(w) - S(l/w) + l$, $\tau_1(w) = u + l - wS^{-1}(u + S(l/w))$, and $\tau_k$ is (A-3): $\tau_1$ on $(w^\alpha_1, w^\alpha_2)$, $\tau_0$ elsewhere, where $w^\alpha_1 < w^\alpha_2$ are the roots of $u = S(\bar F^{-1}(w)) - S(l/w)$ (both equal to its maximizer $w_\alpha$ when $u$ is not below the maximum).
--   4. $t_0(w) = S(\bar F^{-1}(w)) - w\bar F^{-1}(w) - \tau - S(\tfrac{u+l-\tau}{w}) + u + l$ and $t_1(w) = v + l - \tau - wS^{-1}\bigl(v + S(\tfrac{u+l-\tau}{w}) - u\bigr)$; $t_k$ is (A-7): $t_1$ on $(w^a_1, w^a_2)$, $t_0$ elsewhere, where $w^a_1 < w^a_2$ are the roots of $v = S(\bar F^{-1}(w)) - S(\tfrac{u+l-\tau}{w}) + u$ (both equal to its maximizer $w_a$ when $v$ is not below the maximum).
--   5. $w_{min}$ maximizes $t_k$ on $(w^u_1, w^u_2)$; $w_s$ is the smallest $w \in (w^u_1, w^u_2)$ with $(w - c)\min\bigl(S^{-1}(v + S(\tfrac{u+l-\tau}{w}) - u), \bar F^{-1}(w)\bigr) \ge (w^u_2 - c)\bar F^{-1}(w^u_2)$, the supplier's acceptable minimal wholesale price (Appendix p. 21).
--   6. $w_I = \max(w^a_2, w^E)$, $w_{II} = \max(w_s, w_{min})$, and $w^t_1 < w^t_2$ are the roots of $t_k(w) = t$.
--
--   **Assumptions.** The demand law is regular: a probability law with a density that is continuous and positive wherever $0 < x$ and $F(x) < 1$, with finite mean and the IGFR property ($x h(x)$ increases, p. 8). Throughout the paper (*Global*): $0 < c < 1$, $l \ge 0$, $t \ge 0$, $0 \le \tau \le \tau_0(\max(w^\alpha_2, w^E))$ (p. 9), $\tau < u$ (p. 9), $l < w^E Q^E$ (the buyer is capital constrained) and $u < v$. *Standing* adds Proposition 2's $u + l - \tau < w^E Q^E$. **Area II** (the insurance-cooperation region) is $t_k(w_I) < t \le t_k(w_{II})$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note**
--   1. $S$ is the published `SupplyChainTheory.expSales` ($\int \min(Q, d)\,dD$). IGFR is weak monotonicity of $xh(x)$ on the positive support, where $\bar F(x)>0$; the published `SupplyChainTheory.IGFR` compares points beyond a finite support using Lean’s $0/0=0$ and therefore cannot express the paper’s uniform-distribution example. For demand supported on $[0, \infty)$ and $Q \ge 0$ the first equals $Q - \int_0^Q F$.
--   2. The loan limits $u, v$ are primitive parameters, as in Propositions 1–2, which vary them directly; their value-at-risk derivation (p. 9, Lemmas A.5–A.6) is not modelled.
--   3. Added to the page, and disclosed: continuity and positivity of the density on the positive open support (needed for $\bar F^{-1}$, $S^{-1}$ and the paper's derivatives), finite mean (so that $S$ is finite), prices restricted to $(0, 1]$ (a price $w \le c$ never earns the supplier a positive profit).
--   4. Every root and maximizer is a real `sInf`/`sSup` of an explicitly named set. Under *Standing* the sets defining $w^E$, $w^u_{1,2}$, $w^l_{1,2}$, $w^\alpha_{1,2}$ and $w^a_{1,2}$ are nonempty; that the sets for $w_{min}$, $w_s$ and $w^t_{1,2}$ are nonempty in Area II is the content of milestones (Lemma A.7, Proposition 1), never an assumption. $t_k$ is only defined by the page on $(w^u_1, w^u_2)$ (§4.1) and every statement evaluates it there ($w^E$ lies in that interval under *Standing*); outside it the formula falls back to $t_0$. The roots $w^t_{1,2}$ are the ends of $\{t \le t_k\}$, so that $t = t_k(w_{min})$ gives $w^t_1 = w^t_2 = w_{min}$.
--   5. In the bank-loan mode the buyer may also spend less than $l$; with $\tau > 0$ this is dominated, as the page says ("if $l > wQ$ the buyer should not borrow").
--   6. In the equation for $w_s$, $S^{-1}(y)$ is interpreted as $+\infty$ if $y$ exceeds the range of expected sales. Thus the minimum with $\bar F^{-1}(w)$ is $\bar F^{-1}(w)$ there; a real `sInf` of the empty inverse set would incorrectly give zero.
-- source:
--   Wang & Cai, Curtailing bank loan and loan insurance under risk regulations in supply chain finance, SSRN 3760840 (forthcoming Management Science 2023; PDF of 2023-02-24), pp. 7–11 (PDF 7–11), §3, §4.1; Appendix pp. 12–13, 17–21 (PDF 45–46, 50–54), (A-2), (A-3), (A-7), A.3.1, A.4.2, A.4.3

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts

namespace CurtailLoan.BankLoan

open MeasureTheory ProbabilityTheory

/-- The data of the model (§3, pp. 7–10): the law `D` of the consumer demand `ξ` and its density `f`,
the supplier's unit cost `c` (the retail price is normalized to 1), the buyer's initial capital `l`,
the initial loan limit `u`, the insured loan limit `v`, the fixed bank fee `tau` (τ) and the fixed
insurance premium `t`. -/
structure Params where
  D : Measure ℝ
  f : ℝ → ℝ
  c : ℝ
  l : ℝ
  u : ℝ
  v : ℝ
  tau : ℝ
  t : ℝ

/-- The same data with the initial loan limit replaced by `x`. -/
def Params.withU (P : Params) (x : ℝ) : Params := { P with u := x }
/-- The same data with the fixed bank fee replaced by `x`. -/
def Params.withTau (P : Params) (x : ℝ) : Params := { P with tau := x }
/-- The same data with the initial capital replaced by `x`. -/
def Params.withL (P : Params) (x : ℝ) : Params := { P with l := x }
/-- The same data with the fixed insurance premium replaced by `x`. -/
def Params.withT (P : Params) (x : ℝ) : Params := { P with t := x }
/-- The same data with the supplier's unit cost replaced by `x`. -/
def Params.withC (P : Params) (x : ℝ) : Params := { P with c := x }

/-- The paper's IGFR condition on the positive support, where the failure rate is defined.
At and above a finite right endpoint `1 - F(x) = 0`, so those points are excluded. -/
def Params.IGFROnSupport (P : Params) : Prop :=
  MonotoneOn (fun x => x * P.f x / (1 - cdf P.D x))
    {x : ℝ | 0 < x ∧ cdf P.D x < 1}

/-- The demand law (p. 8, plus the disclosed regularity): `D` is a probability measure with
density `f`, `f` vanishes on `(−∞, 0)`, is continuous and positive on the positive open
support, demand has a finite mean, and `D` has the IGFR property there. -/
def Params.Regular (P : Params) : Prop :=
  IsProbabilityMeasure P.D ∧ Integrable (fun x : ℝ => x) P.D ∧
  P.D = volume.withDensity (fun x => ENNReal.ofReal (P.f x)) ∧
  (∀ x : ℝ, x < 0 → P.f x = 0) ∧
  ContinuousOn P.f {x : ℝ | 0 < x ∧ cdf P.D x < 1} ∧
  (∀ x : ℝ, 0 < x → cdf P.D x < 1 → 0 < P.f x) ∧ P.IGFROnSupport

/-- The complementary CDF `F̄(x) = 1 − F(x)`. -/
noncomputable def Fbar (P : Params) (x : ℝ) : ℝ := 1 - cdf P.D x

/-- Expected sales `S(Q) = E[min(ξ, Q)]` (= `Q − ∫₀^Q F` for `Q ≥ 0`). -/
noncomputable def S (P : Params) (Q : ℝ) : ℝ := SupplyChainTheory.expSales P.D Q

/-- `F̄^{-1}(w)`, the smallest `Q ≥ 0` with `F̄(Q) ≤ w` (read on `w ∈ (0, 1]`). -/
noncomputable def Finv (P : Params) (w : ℝ) : ℝ := sInf {Q : ℝ | 0 ≤ Q ∧ Fbar P Q ≤ w}

/-- `S^{-1}(y)`, the smallest `Q ≥ 0` with `y ≤ S(Q)` (read on `0 ≤ y < E ξ`). -/
noncomputable def Sinv (P : Params) (y : ℝ) : ℝ := sInf {Q : ℝ | 0 ≤ Q ∧ y ≤ S P Q}

/-- The failure rate `h(x) = f(x) / F̄(x)`. -/
noncomputable def hr (P : Params) (x : ℝ) : ℝ := P.f x / Fbar P x

/-- The buyer's three financing modes: own capital only, a bank loan, an insured bank loan. -/
inductive Mode
  | noLoan
  | loan
  | insured

/-- The most the buyer can spend on the order in each mode: `l`, `u + l − τ`, `v + l − τ − t`. -/
def cap (P : Params) : Mode → ℝ
  | .noLoan => P.l
  | .loan => P.u + P.l - P.tau
  | .insured => P.v + P.l - P.tau - P.t

/-- The fixed charges of each mode: none, the bank fee `τ`, the bank fee and the premium `τ + t`. -/
def fee (P : Params) : Mode → ℝ
  | .noLoan => 0
  | .loan => P.tau
  | .insured => P.tau + P.t

/-- The buyer's expected profit `S(Q) − wQ − fee` ((A-2), A.4.2). -/
noncomputable def buyerProfit (P : Params) (w : ℝ) (m : Mode) (Q : ℝ) : ℝ :=
  S P Q - w * Q - fee P m

/-- An order `Q` is feasible in mode `m` at price `w` when `0 ≤ Q` and `wQ ≤ cap m`. -/
def Feasible (P : Params) (w : ℝ) (m : Mode) (Q : ℝ) : Prop :=
  0 ≤ Q ∧ w * Q ≤ cap P m

/-- `(m, Q)` maximizes the buyer's profit over all modes and feasible orders. -/
def IsBuyerOpt (P : Params) (w : ℝ) (m : Mode) (Q : ℝ) : Prop :=
  Feasible P w m Q ∧ ∀ (m' : Mode) (Q' : ℝ), Feasible P w m' Q' →
    buyerProfit P w m' Q' ≤ buyerProfit P w m Q

/-- The buyer's response with the goodwill tie-break (p. 10): among the buyer's optima, one that
maximizes the supplier's profit `(w − c)Q`. -/
def IsResponse (P : Params) (w : ℝ) (m : Mode) (Q : ℝ) : Prop :=
  IsBuyerOpt P w m Q ∧ ∀ (m' : Mode) (Q' : ℝ), IsBuyerOpt P w m' Q' →
    (w - P.c) * Q' ≤ (w - P.c) * Q

/-- The buyer's optimal expected profit at price `w`. -/
noncomputable def buyerValue (P : Params) (w : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ (m : Mode) (Q : ℝ), Feasible P w m Q ∧ y = buyerProfit P w m Q}

/-- An outcome of the game: wholesale price, financing mode, order quantity. -/
structure Outcome where
  w : ℝ
  m : Mode
  Q : ℝ

/-- The supplier's profit `Π_S = (w − c)Q` (p. 11). -/
def PiS (P : Params) (o : Outcome) : ℝ := (o.w - P.c) * o.Q

/-- The buyer's profit at an outcome. -/
noncomputable def PiB (P : Params) (o : Outcome) : ℝ := buyerProfit P o.w o.m o.Q

/-- The supplier's optimal price: `w ∈ (0, 1]`, the buyer responds, and no other price with a
response gives the supplier more. -/
def IsSupplierOpt (P : Params) (o : Outcome) : Prop :=
  o.w ∈ Set.Ioc (0 : ℝ) 1 ∧ IsResponse P o.w o.m o.Q ∧
  ∀ o' : Outcome, o'.w ∈ Set.Ioc (0 : ℝ) 1 → IsResponse P o'.w o'.m o'.Q → PiS P o' ≤ PiS P o

/-- The goodwill Stackelberg equilibrium (p. 10): among the supplier's optima, one that maximizes
the buyer's profit. -/
def IsEquilibrium (P : Params) (o : Outcome) : Prop :=
  IsSupplierOpt P o ∧ ∀ o' : Outcome, IsSupplierOpt P o' → PiB P o' ≤ PiB P o

/-- `w^E`: the root of `w[1 − F̄^{-1}(w) h(F̄^{-1}(w))] = c` in `(0, 1]` (p. 8), as the smallest
price at which the left side reaches `c`. -/
noncomputable def wE (P : Params) : ℝ :=
  sInf {w : ℝ | w ∈ Set.Ioc (0 : ℝ) 1 ∧ P.c ≤ w * (1 - Finv P w * hr P (Finv P w))}

/-- `Q^E = F̄^{-1}(w^E)`. -/
noncomputable def QE (P : Params) : ℝ := Finv P (wE P)

/-- `ŵ`: the (largest) maximizer of `w F̄^{-1}(w)` on `(0, 1)` (p. 9). -/
noncomputable def what (P : Params) : ℝ :=
  sSup {w : ℝ | w ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∀ w' ∈ Set.Ioo (0 : ℝ) 1, w' * Finv P w' ≤ w * Finv P w}

/-- The loan cap `u + l − τ`. -/
def L (P : Params) : ℝ := P.u + P.l - P.tau

/-- `w^u_1`, `w^u_2`: the two roots of `u + l − τ = w F̄^{-1}(w)` (p. 9). -/
noncomputable def wu1 (P : Params) : ℝ := sInf {w : ℝ | w ∈ Set.Ioo (0 : ℝ) 1 ∧ L P < w * Finv P w}
noncomputable def wu2 (P : Params) : ℝ := sSup {w : ℝ | w ∈ Set.Ioo (0 : ℝ) 1 ∧ L P < w * Finv P w}

/-- `w^l_1`, `w^l_2`: the two roots of `l = w F̄^{-1}(w)` (Appendix p. 13). -/
noncomputable def wl1 (P : Params) : ℝ := sInf {w : ℝ | w ∈ Set.Ioo (0 : ℝ) 1 ∧ P.l < w * Finv P w}
noncomputable def wl2 (P : Params) : ℝ := sSup {w : ℝ | w ∈ Set.Ioo (0 : ℝ) 1 ∧ P.l < w * Finv P w}

/-- `S(F̄^{-1}(w)) − S(l/w)` (Appendix p. 13). -/
noncomputable def gAlpha (P : Params) (w : ℝ) : ℝ := S P (Finv P w) - S P (P.l / w)

/-- `w_α`: the (largest) maximizer of `S(F̄^{-1}(w)) − S(l/w)` on `(w^l_1, w^l_2)`. -/
noncomputable def wAlpha (P : Params) : ℝ :=
  sSup {w : ℝ | w ∈ Set.Ioo (wl1 P) (wl2 P) ∧
    ∀ w' ∈ Set.Ioo (wl1 P) (wl2 P), gAlpha P w' ≤ gAlpha P w}

open Classical in
/-- `w^α_1`: the smaller root of `u = S(F̄^{-1}(w)) − S(l/w)` when `u` is below the maximum,
otherwise `w_α` (Appendix p. 13). -/
noncomputable def wAlpha1 (P : Params) : ℝ :=
  if {w : ℝ | w ∈ Set.Ioo (wl1 P) (wl2 P) ∧ P.u < gAlpha P w}.Nonempty then
    sInf {w : ℝ | w ∈ Set.Ioo (wl1 P) (wl2 P) ∧ P.u < gAlpha P w}
  else wAlpha P

open Classical in
/-- `w^α_2`: the larger root of `u = S(F̄^{-1}(w)) − S(l/w)` when `u` is below the maximum,
otherwise `w_α` (Appendix p. 13). -/
noncomputable def wAlpha2 (P : Params) : ℝ :=
  if {w : ℝ | w ∈ Set.Ioo (wl1 P) (wl2 P) ∧ P.u < gAlpha P w}.Nonempty then
    sSup {w : ℝ | w ∈ Set.Ioo (wl1 P) (wl2 P) ∧ P.u < gAlpha P w}
  else wAlpha P

/-- `τ0(w) = S(F̄^{-1}(w)) − wF̄^{-1}(w) − S(l/w) + l` (Appendix p. 13). -/
noncomputable def tau0 (P : Params) (w : ℝ) : ℝ :=
  S P (Finv P w) - w * Finv P w - S P (P.l / w) + P.l

/-- `τ1(w) = u + l − wS^{-1}(u + S(l/w))` (Appendix p. 13). -/
noncomputable def tau1 (P : Params) (w : ℝ) : ℝ :=
  P.u + P.l - w * Sinv P (P.u + S P (P.l / w))

open Classical in
/-- `τk(w)`, (A-3): `τ1(w)` on `(w^α_1, w^α_2)`, `τ0(w)` otherwise. -/
noncomputable def tauk (P : Params) (w : ℝ) : ℝ :=
  if wAlpha1 P < w ∧ w < wAlpha2 P then tau1 P w else tau0 P w

/-- `S(F̄^{-1}(w)) − S((u+l−τ)/w) + u` (Appendix p. 19). -/
noncomputable def gA (P : Params) (w : ℝ) : ℝ := S P (Finv P w) - S P (L P / w) + P.u

/-- `w_a`: the (largest) maximizer of `gA` on `(w^u_1, w^u_2)` (Appendix p. 19). -/
noncomputable def wA (P : Params) : ℝ :=
  sSup {w : ℝ | w ∈ Set.Ioo (wu1 P) (wu2 P) ∧
    ∀ w' ∈ Set.Ioo (wu1 P) (wu2 P), gA P w' ≤ gA P w}

open Classical in
/-- `w^a_1`: the smaller root of `v = S(F̄^{-1}(w)) − S((u+l−τ)/w) + u` when `v` is below the
maximum, otherwise `w_a` (Appendix p. 19). -/
noncomputable def wa1 (P : Params) : ℝ :=
  if {w : ℝ | w ∈ Set.Ioo (wu1 P) (wu2 P) ∧ P.v < gA P w}.Nonempty then
    sInf {w : ℝ | w ∈ Set.Ioo (wu1 P) (wu2 P) ∧ P.v < gA P w}
  else wA P

open Classical in
/-- `w^a_2`: the larger root of `v = S(F̄^{-1}(w)) − S((u+l−τ)/w) + u` when `v` is below the
maximum, otherwise `w_a` (Appendix p. 19). -/
noncomputable def wa2 (P : Params) : ℝ :=
  if {w : ℝ | w ∈ Set.Ioo (wu1 P) (wu2 P) ∧ P.v < gA P w}.Nonempty then
    sSup {w : ℝ | w ∈ Set.Ioo (wu1 P) (wu2 P) ∧ P.v < gA P w}
  else wA P

/-- `t0(w) = S(F̄^{-1}(w)) − wF̄^{-1}(w) − τ − S((u+l−τ)/w) + u + l` (Appendix p. 19). -/
noncomputable def t0 (P : Params) (w : ℝ) : ℝ :=
  S P (Finv P w) - w * Finv P w - P.tau - S P (L P / w) + P.u + P.l

/-- `t1(w) = v + l − τ − wS^{-1}(v + S((u+l−τ)/w) − u)` (Appendix p. 19). -/
noncomputable def t1 (P : Params) (w : ℝ) : ℝ :=
  P.v + P.l - P.tau - w * Sinv P (P.v + S P (L P / w) - P.u)

open Classical in
/-- `tk(w)`, (A-7): `t1(w)` on `(w^a_1, w^a_2)`, `t0(w)` otherwise. Read on `(w^u_1, w^u_2)`. -/
noncomputable def tk (P : Params) (w : ℝ) : ℝ :=
  if wa1 P < w ∧ w < wa2 P then t1 P w else t0 P w

/-- `w_min`: the (largest) maximizer of `tk` on `(w^u_1, w^u_2)` (§4.1, Lemma A.7). -/
noncomputable def wmin (P : Params) : ℝ :=
  sSup {w : ℝ | w ∈ Set.Ioo (wu1 P) (wu2 P) ∧
    ∀ w' ∈ Set.Ioo (wu1 P) (wu2 P), tk P w' ≤ tk P w}

/-- The order threshold in the equation for `w_s`: the smaller of `F̄⁻¹(w)` and the
extended inverse of `S` at `v + S((u+l−τ)/w) − u`. The set still has a point when that
argument exceeds the range of `S`; then its infimum is `F̄⁻¹(w)`. -/
noncomputable def wsOrder (P : Params) (w : ℝ) : ℝ :=
  sInf {Q : ℝ | 0 ≤ Q ∧
    (P.v + S P (L P / w) - P.u ≤ S P Q ∨ Finv P w ≤ Q)}

/-- `w_s`, the supplier's acceptable minimal wholesale price (Appendix p. 21): the smallest
`w ∈ (w^u_1, w^u_2)` with
`(w − c) min(S^{-1}(v + S((u+l−τ)/w) − u), F̄^{-1}(w)) ≥ (w^u_2 − c) F̄^{-1}(w^u_2)`,
where an inverse above the range of `S` is interpreted as `+∞`. -/
noncomputable def ws (P : Params) : ℝ :=
  sInf {w : ℝ | w ∈ Set.Ioo (wu1 P) (wu2 P) ∧
    (wu2 P - P.c) * Finv P (wu2 P) ≤
      (w - P.c) * wsOrder P w}

/-- `w_I = max(w^a_2, w^E)`. -/
noncomputable def wI (P : Params) : ℝ := max (wa2 P) (wE P)

/-- `w_II = max(w_s, w_min)`. -/
noncomputable def wII (P : Params) : ℝ := max (ws P) (wmin P)

/-- `w^t_1`, `w^t_2`: the two roots of `tk(w) = t` (§4.1), as the ends of `{t ≤ tk}`. -/
noncomputable def wt1 (P : Params) : ℝ :=
  sInf {w : ℝ | w ∈ Set.Ioo (wu1 P) (wu2 P) ∧ P.t ≤ tk P w}
noncomputable def wt2 (P : Params) : ℝ :=
  sSup {w : ℝ | w ∈ Set.Ioo (wu1 P) (wu2 P) ∧ P.t ≤ tk P w}

/-- The assumptions in force throughout the paper: `0 < c < 1` (p. 8), `l ≥ 0`, `t ≥ 0`,
`0 ≤ τ ≤ τ0(max(w^α_2, w^E))` (p. 9 and Appendix p. 17, "throughout"), `τ < u` (p. 9), the buyer
is capital constrained, `l < w^E Q^E` (p. 8, Proposition 1), and `u < v` (Lemma A.7). -/
def Global (P : Params) : Prop :=
  0 < P.c ∧ P.c < 1 ∧ 0 ≤ P.l ∧ 0 ≤ P.t ∧ 0 ≤ P.tau ∧
  P.tau ≤ tau0 P (max (wAlpha2 P) (wE P)) ∧ P.tau < P.u ∧
  P.l < wE P * QE P ∧ P.u < P.v

/-- `u + l − τ < ŵ Q̂` with `Q̂ = F̄^{-1}(ŵ)`: the condition under which the page defines
`w^u_1 < w^u_2` (p. 9). -/
def RootsDefined (P : Params) : Prop := L P < what P * Finv P (what P)

/-- The standing assumptions of Propositions 1–2: `Global` and `u + l − τ < w^E Q^E`
(Proposition 2's preamble; Proposition 1 item 1's `u < w^E Q^E − l + τ`). -/
def Standing (P : Params) : Prop :=
  Global P ∧ L P < wE P * QE P

/-- Area II, the insurance-cooperation region: `tk(w_I) < t ≤ tk(w_II)`. -/
def AreaII (P : Params) : Prop := tk P (wI P) < P.t ∧ P.t ≤ tk P (wII P)

/-- The insured loan limit does not bind at `w^t_2`: `w^t_2 F̄^{-1}(w^t_2) ≤ v + l − τ − t`. -/
def InsuredSlack (P : Params) : Prop := wt2 P * Finv P (wt2 P) ≤ P.v + P.l - P.tau - P.t

end CurtailLoan.BankLoan


