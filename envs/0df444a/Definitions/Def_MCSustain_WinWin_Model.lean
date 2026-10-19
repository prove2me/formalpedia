-- Prove2me | Definitions.Def_MCSustain_WinWin_Model
-- name    : MCSustain_WinWin_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:10:45.894355+00:00
-- url     : https://prove2.me/theorems/c6b3a2b1-b0c9-4a8e-9f2b-c5c875daed5a
-- title:
--   §3–§5 and Table 2 — MP and hybrid (MP + MC) firms: reduced profit problems, optimal decisions, lifecycle environmental impact, win-win, thresholds and solution types
-- statement:
--   The model of Alptekinoğlu and Örsdemir's comparison of a **mass-producing (MP) firm** with a **hybrid firm** that adds **mass customization (MC)**.
--
--   **Parameters.** Consumers' ideal products are uniform on the Hotelling line $[0,1]$; a consumer at distance $d$ from a product priced $p$ gets utility $r-p-td$. The market size $M$ is random: $M=m_H$ with probability $\alpha$ and $M=m_L$ with probability $1-\alpha$, and
--   $$\mu=\alpha m_H+(1-\alpha)m_L,\qquad \beta=\mu/m_L .$$
--   Each unit costs $c$, offering $n$ variants costs $fn^2$, and a mass-customized product makes the consumer wait, at disutility $w$. The per-unit impacts of production, use, disposal and overproduction are $e_p,e_u,e_d,e_o$, and $E_s=e_p+e_u+e_d$ (sold unit), $E_l=e_p+e_o$ (leftover unit). The **standing assumptions** are $0<\alpha<1$, $m_H>m_L>0$, $c/\alpha<r$ (§3.1) and $c(\beta-1)(1-\alpha)/(\alpha\beta)<w<r-c$ (§4.2).
--
--   **MP firm (reduced form, p. 10).** A decision is $(n,\lambda,q)$: $n\ge0$ variants, market share $\lambda\ge0$ per variant with $n\lambda\le1$, stock $q\ge0$ per variant. The price is $p_{MP}=r-\tfrac t2\lambda$ (eq. (1)), and the expected profit is
--   $$\Pi(n,\lambda,q)=p_{MP}\,n\,\mathbb E[\min\{q,M\lambda\}]-(cnq+fn^2).$$
--
--   **Hybrid firm (p. 14).** A decision adds an MC price $p_{MC}$ and total MC share $\lambda_{MC}\ge0$ with $n\lambda+\lambda_{MC}\le1$; MC is bought only if $r-w-p_{MC}\ge0$. Its profit is
--   $$\Pi'=\Pi(n,\lambda,q)+p_{MC}\mu\lambda_{MC}-c\mu\lambda_{MC}.$$
--
--   **Impact (§5).** For the MP firm, $E_s\,n\,\mathbb E[\min\{q,M\lambda\}]+E_l\,n\,\mathbb E[(q-M\lambda)^+]$; the hybrid firm adds $E_s\mu\lambda_{MC}$ (MC is made to order, so it leaves no leftovers).
--
--   **Optimality and win-win.** A decision is optimal if it is feasible and maximizes profit over all feasible decisions. Adopting MC is a **win-win** if both problems have optimal decisions and every optimal hybrid decision has strictly higher profit and strictly lower expected impact than every optimal MP decision.
--
--   **Thresholds.** $\lambda_t=2(r-c/\alpha)/t$, $\lambda_L=(r-c)/t$, $\lambda_H=(r-c(\beta-1+\alpha)/(\alpha\beta))/t$ (p. 10), $\lambda'_H=(w-c(\beta-1)(1-\alpha)/(\alpha\beta))/t$, $\lambda'_L=(w\beta-(r-c)(\beta-1))/t$ (p. 15), and Table 2: $f_H=\lambda_H^3\mu t/4$, $f'_H=\lambda_H'^3\mu t/4$, $f_L=\lambda_L^3m_Lt/4$, $f'_L=\lambda_L'^3m_Lt/4$,
--   $$f_c=\tfrac{2}{27}\Big(\tfrac{\beta-1}{\beta^{2/3}-1}\Big)^3\lambda_t^3m_Lt,\quad \kappa_2=\frac{1-\alpha+\sqrt\beta}{\alpha\sqrt\beta},\quad \kappa_1=\frac{3-3(\alpha-1)\sqrt[3]\beta-3\alpha+4\beta^{2/3}+\beta^{4/3}+\beta}{\alpha(\beta^{2/3}+\sqrt[3]\beta+4)\beta^{2/3}},$$
--   $$w_1=\frac{\alpha(\beta+\sqrt\beta)r-c(\alpha(\beta-1)+\sqrt\beta+1)}{\alpha\beta},\quad w_2=\frac{(\beta^{2/3}+\sqrt[3]\beta+1)(\beta^{2/3}(4\alpha r-3\alpha c-c)-3(1-\alpha)c)}{3\alpha(\sqrt[3]\beta+1)\beta},$$
--   $$R=\frac{(1-n_H\lambda_H)\mu}{(m_H-\mu)(n_H\lambda_H-n'_H\lambda'_H)},\qquad n_H=\frac{\mu t\lambda_H^2}{4f},\ n'_H=\frac{\mu t\lambda_H'^2}{4f}.$$
--   $f_{cu}$ is the root on $(f_H,f_L]$ of $\lambda_L=\tfrac32(f/(2m_Lt))^{1/3}+\lambda_H^4\mu\beta t/(16f)$, and $f'_{cu}$ the root on $(f'_H,f'_L]$ of the same equation with $\lambda'_L,\lambda'_H$.
--
--   **Solution types** (eqs. (2)–(9)): $\mathbb H_u=(\mu t\lambda_H^2/(4f),\lambda_H,\lambda_Hm_H)$, $\mathbb H_c=(n^*,1/n^*,m_H/n^*)$ with $n^*=\sqrt[3]{t\mu/(4f)}$, $\mathbb L_u=(m_Lt\lambda_L^2/(4f),\lambda_L,\lambda_Lm_L)$, $\mathbb L_c=(n^*,1/n^*,m_L/n^*)$ with $n^*=\sqrt[3]{tm_L/(4f)}$; the hybrid $\mathbb H'_u,\mathbb L'_u$ use $\lambda'_H,\lambda'_L$ with $\lambda_{MC}=1-n^*\lambda^*$, and $\mathbb H'_c,\mathbb L'_c$ equal $\mathbb H_c,\mathbb L_c$ with $\lambda_{MC}=0$; all hybrid types set $p_{MC}=r-w$ (Lemma 2).
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** All quantities are real. The problems are stated in the paper's reduced form (p. 10): every per-product share lies in $[0,1]$ and the firm chooses market shares rather than prices, product locations are not modelled (equal spacing and uniform prices are optimal under uniform tastes, p. 9), and the number of variants $n$ is real (integrality relaxed, p. 9). In the hybrid problem the MP price is $r-t\lambda/2$ for every admissible $p_{MC}$; this is eq. (10) at the optimal $p_{MC}=r-w$. The expectation over $M$ is written out as $\alpha g(m_H)+(1-\alpha)g(m_L)$. Added to the standing assumptions: $t>0$, $c>0$, $f>0$ (the solution types divide by $f$), $e_p,e_u,e_d,e_o\ge0$, $E_s>0$ and $E_l>0$ (without $E_l>0$ the impacts in Proposition 3, part 1(b), tie). Cube roots are `Real.rpow` with exponent $1/3$ of positive bases. `fcu`/`fcup` are infima of the root sets on $(f_H,f_L]$ and $(f'_H,f'_L]$; the milestones `fcu_spec`, `fcup_spec` show the roots exist and are unique there.
-- source:
--   Alptekinoğlu & Örsdemir, Is Adopting Mass Customization a Path to Environmentally Sustainable Fashion?, accepted manuscript (MSOM, forthcoming; SSRN 3685235, Jan. 20, 2022), pp. 8–18 (PDF 8–18), §3.1 (p. 8–9), eq. (1) and thresholds (p. 10), eqs. (2)–(5) (pp. 10–11), §4.1–4.2 (pp. 13–14), eqs. (6)–(9) (p. 15), §5 (p. 17), win-win (p. 18); Table 2, p. a1 (PDF 33)

import Mathlib

namespace MCSustain.WinWin

noncomputable section

/-- The parameters of the model (§3.1, pp. 8–9; §4.1, p. 13; §5, p. 17): the probability `α` of the
high market size, the high and low market sizes `mH`, `mL`, the consumers' disutility `t` per unit
distance on the Hotelling line, the unit production cost `c`, the reservation price `r`, the
product-variety cost coefficient `f` (variety cost `f n²`), the waiting cost `w` of a
mass-customized product, and the per-unit environmental impacts `ep`, `eu`, `ed`, `eo` of the
production, use, disposal and overproduction lifecycle phases. -/
structure Params where
  α : ℝ
  mH : ℝ
  mL : ℝ
  t : ℝ
  c : ℝ
  r : ℝ
  f : ℝ
  w : ℝ
  ep : ℝ
  eu : ℝ
  ed : ℝ
  eo : ℝ

/-- Expected market size `µ = α m_H + (1 − α) m_L` (p. 8). -/
def Params.μ (P : Params) : ℝ := P.α * P.mH + (1 - P.α) * P.mL

/-- `β = µ / m_L` (p. 10). -/
def Params.β (P : Params) : ℝ := P.μ / P.mL

/-- Per-unit impact of sold clothing, `E_s = e_p + e_u + e_d` (p. 17). -/
def Params.Es (P : Params) : ℝ := P.ep + P.eu + P.ed

/-- Per-unit impact of unsold (leftover) clothing, `E_l = e_p + e_o` (p. 17). -/
def Params.El (P : Params) : ℝ := P.ep + P.eo

/-- The paper's standing assumptions: `0 < α < 1`, `m_H > m_L > 0` (p. 8), `c/α < r` (p. 9),
`c(β − 1)(1 − α)/(αβ) < w < r − c` (p. 14). Added (implicit in the paper): `t > 0`, `c > 0`,
`f > 0`, nonnegative lifecycle impacts, `E_s > 0` and `E_l > 0`. The bound `λ_L < 1`
is stated with the threshold definitions on p. 10. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.α ∧ P.α < 1 ∧ 0 < P.mL ∧ P.mL < P.mH ∧ 0 < P.t ∧ 0 < P.c ∧ P.c / P.α < P.r ∧
  0 < P.f ∧ (P.r - P.c) / P.t < 1 ∧
  P.c * (P.β - 1) * (1 - P.α) / (P.α * P.β) < P.w ∧ P.w < P.r - P.c ∧
  0 ≤ P.ep ∧ 0 ≤ P.eu ∧ 0 ≤ P.ed ∧ 0 ≤ P.eo ∧ 0 < P.Es ∧ 0 < P.El

/-- A decision of the mass-producing (MP) firm in the paper's reduced form (p. 10): the number
`n` of product variants (a real number, as the paper
relaxes n to be continuous), the market share `lam` (λ_MP) of each variant,
and the stocking quantity `q` (q_MP) of each variant. -/
structure MPDec where
  n : ℝ
  lam : ℝ
  q : ℝ

/-- A decision of the hybrid (MP + MC) firm: an MP decision plus the price `pMC` of the
mass-customized products and their total market share `lamMC` (λ_MC). -/
structure HybDec extends MPDec where
  pMC : ℝ
  lamMC : ℝ

/-- Feasibility of an MP decision: `n ≥ 0`, `0 ≤ λ ≤ 1` (the share is the length of a
subinterval of `[0,1]`), `nλ ≤ 1`, `q ≥ 0`. -/
def MPDec.Feasible (x : MPDec) : Prop :=
  0 ≤ x.n ∧ 0 ≤ x.lam ∧ x.lam ≤ 1 ∧ x.n * x.lam ≤ 1 ∧ 0 ≤ x.q

/-- Feasibility of a hybrid decision: a feasible MP part, `λ_MC ≥ 0`, `nλ_MP + λ_MC ≤ 1`
(p. 14), and consumers buy MC products only if their utility `r − w − p_MC` is nonnegative
(p. 13). -/
def HybDec.Feasible (P : Params) (y : HybDec) : Prop :=
  y.toMPDec.Feasible ∧ 0 ≤ y.lamMC ∧ y.n * y.lam + y.lamMC ≤ 1 ∧
    (0 < y.lamMC → y.pMC ≤ P.r - P.w)

/-- Expectation over the two-point market size `M` (`M = m_H` w.p. `α`, `m_L` w.p. `1 − α`). -/
def E (P : Params) (g : ℝ → ℝ) : ℝ := P.α * g P.mH + (1 - P.α) * g P.mL

/-- The MP price implied by the market share, `p_MP = r − (t/2) λ_MP` (eq. (1), p. 10). -/
def pMP (P : Params) (lam : ℝ) : ℝ := P.r - P.t / 2 * lam

/-- Expected total sales of mass-produced products, `n E[min{q, Mλ}]`. -/
def sales (P : Params) (x : MPDec) : ℝ := x.n * E P (fun M => min x.q (M * x.lam))

/-- Expected total leftover (overproduced) mass-produced inventory, `n E[(q − Mλ)⁺]`. -/
def leftover (P : Params) (x : MPDec) : ℝ := x.n * E P (fun M => max (x.q - M * x.lam) 0)

/-- Expected profit of the MP firm, `p_MP n E[min{q, Mλ}] − (c n q + f n²)` (p. 9). -/
def profitMP (P : Params) (x : MPDec) : ℝ :=
  pMP P x.lam * sales P x - (P.c * x.n * x.q + P.f * x.n ^ 2)

/-- Expected profit of the hybrid firm (p. 14): the MP profit plus `p_MC µ λ_MC − c µ λ_MC`. -/
def profitHyb (P : Params) (y : HybDec) : ℝ :=
  profitMP P y.toMPDec + y.pMC * P.μ * y.lamMC - P.c * P.μ * y.lamMC

/-- Expected environmental impact of the MP firm (§5): `E_s` times expected sales plus `E_l`
times expected leftovers. -/
def impactMP (P : Params) (x : MPDec) : ℝ := P.Es * sales P x + P.El * leftover P x

/-- Expected environmental impact of the hybrid firm (§5): MC is made to order, so its expected
volume `µ λ_MC` is all sold and leaves no leftovers. -/
def impactHyb (P : Params) (y : HybDec) : ℝ := impactMP P y.toMPDec + P.Es * (P.μ * y.lamMC)

/-- An optimal MP decision: feasible and profit-maximizing among feasible MP decisions. -/
def IsOptMP (P : Params) (x : MPDec) : Prop :=
  x.Feasible ∧ ∀ x' : MPDec, x'.Feasible → profitMP P x' ≤ profitMP P x

/-- An optimal hybrid decision: feasible and profit-maximizing among feasible hybrid decisions. -/
def IsOptHyb (P : Params) (y : HybDec) : Prop :=
  y.Feasible P ∧ ∀ y' : HybDec, y'.Feasible P → profitHyb P y' ≤ profitHyb P y

set_option linter.dupNamespace false in
/-- Adopting MC is a win-win (p. 18): both problems have optimal decisions, and every optimal
hybrid decision has strictly higher profit and strictly lower expected environmental impact than
every optimal MP decision. -/
def WinWin (P : Params) : Prop :=
  (∃ x, IsOptMP P x) ∧ (∃ y, IsOptHyb P y) ∧
    ∀ x y, IsOptMP P x → IsOptHyb P y →
      profitMP P x < profitHyb P y ∧ impactHyb P y < impactMP P x

/-! ### Market-share thresholds (p. 10, p. 15) -/

/-- `λ_t = 2(r − c/α)/t` (p. 10). -/
def lamT (P : Params) : ℝ := 2 * (P.r - P.c / P.α) / P.t

/-- `λ_L = (r − c)/t` (p. 10). -/
def lamL (P : Params) : ℝ := (P.r - P.c) / P.t

/-- `λ_H = (r − c(β − 1 + α)/(αβ))/t` (p. 10). -/
def lamH (P : Params) : ℝ := (P.r - P.c * (P.β - 1 + P.α) / (P.α * P.β)) / P.t

/-- `λ'_L = (wβ − (r − c)(β − 1))/t` (p. 15). -/
def lamLp (P : Params) : ℝ := (P.w * P.β - (P.r - P.c) * (P.β - 1)) / P.t

/-- `λ'_H = (w − c(β − 1)(1 − α)/(αβ))/t` (p. 15). -/
def lamHp (P : Params) : ℝ := (P.w - P.c * (P.β - 1) * (1 - P.α) / (P.α * P.β)) / P.t

/-! ### Table 2 (p. a1) -/

/-- `f_H = λ_H³ µ t / 4`. -/
def fH (P : Params) : ℝ := lamH P ^ 3 * P.μ * P.t / 4

/-- `f'_H = λ'_H³ µ t / 4`. -/
def fHp (P : Params) : ℝ := lamHp P ^ 3 * P.μ * P.t / 4

/-- `f_L = λ_L³ m_L t / 4`. -/
def fL (P : Params) : ℝ := lamL P ^ 3 * P.mL * P.t / 4

/-- `f'_L = λ'_L³ m_L t / 4`. -/
def fLp (P : Params) : ℝ := lamLp P ^ 3 * P.mL * P.t / 4

/-- `f_c = (2/27) ((β − 1)/(β^{2/3} − 1))³ λ_t³ m_L t`. -/
def fc (P : Params) : ℝ :=
  2 / 27 * ((P.β - 1) / (P.β ^ ((2 : ℝ) / 3) - 1)) ^ 3 * lamT P ^ 3 * P.mL * P.t

/-- `w₁ = [α(β + √β) r − c(α(β − 1) + √β + 1)]/(αβ)`. -/
def w1 (P : Params) : ℝ :=
  (P.α * (P.β + Real.sqrt P.β) * P.r - P.c * (P.α * (P.β - 1) + Real.sqrt P.β + 1)) /
    (P.α * P.β)

/-- `w₂ = [(β^{2/3} + ∛β + 1)(β^{2/3}(4αr − 3αc − c) − 3(1 − α)c)]/[3α(∛β + 1)β]`. -/
def w2 (P : Params) : ℝ :=
  ((P.β ^ ((2 : ℝ) / 3) + P.β ^ ((1 : ℝ) / 3) + 1) *
      (P.β ^ ((2 : ℝ) / 3) * (4 * P.α * P.r - 3 * P.α * P.c - P.c) - 3 * (1 - P.α) * P.c)) /
    (3 * P.α * (P.β ^ ((1 : ℝ) / 3) + 1) * P.β)

/-- `κ₁ = [3 − 3(α − 1)∛β − 3α + 4β^{2/3} + β^{4/3} + β]/[α(β^{2/3} + ∛β + 4)β^{2/3}]`. -/
def κ1 (P : Params) : ℝ :=
  (3 - 3 * (P.α - 1) * P.β ^ ((1 : ℝ) / 3) - 3 * P.α + 4 * P.β ^ ((2 : ℝ) / 3) +
      P.β ^ ((4 : ℝ) / 3) + P.β) /
    (P.α * (P.β ^ ((2 : ℝ) / 3) + P.β ^ ((1 : ℝ) / 3) + 4) * P.β ^ ((2 : ℝ) / 3))

/-- `κ₂ = (1 − α + √β)/(α√β)`. -/
def κ2 (P : Params) : ℝ := (1 - P.α + Real.sqrt P.β) / (P.α * Real.sqrt P.β)

/-- `n_H = µ t λ_H² / (4f)`, the variety of solution `ℍ_u` (eq. (2)). -/
def nH (P : Params) : ℝ := P.μ * P.t * lamH P ^ 2 / (4 * P.f)

/-- `n'_H = µ t λ'_H² / (4f)`, the variety of solution `ℍ'_u` (eq. (6)). -/
def nHp (P : Params) : ℝ := P.μ * P.t * lamHp P ^ 2 / (4 * P.f)

/-- `R = (1 − n_H λ_H) µ / [(m_H − µ)(n_H λ_H − n'_H λ'_H)]`. -/
def R (P : Params) : ℝ :=
  (1 - nH P * lamH P) * P.μ / ((P.mH - P.μ) * (nH P * lamH P - nHp P * lamHp P))

/-- `Φ(g) = λ_L − (3/2)(g/(2 m_L t))^{1/3} − λ_H⁴ µ β t/(16 g)`; `f_cu` is its root. -/
def Φ (P : Params) (g : ℝ) : ℝ :=
  lamL P - 3 / 2 * (g / (2 * P.mL * P.t)) ^ ((1 : ℝ) / 3) -
    lamH P ^ 4 * P.μ * P.β * P.t / (16 * g)

/-- `Φ'(g) = λ'_L − (3/2)(g/(2 m_L t))^{1/3} − λ'_H⁴ µ β t/(16 g)`; `f'_cu` is its root. -/
def Φp (P : Params) (g : ℝ) : ℝ :=
  lamLp P - 3 / 2 * (g / (2 * P.mL * P.t)) ^ ((1 : ℝ) / 3) -
    lamHp P ^ 4 * P.μ * P.β * P.t / (16 * g)

/-- `f_cu`: Table 2's "unique solution" of `Φ = 0`, taken on `(f_H, f_L]`, where it is unique for
moderate-value products (milestone `fcu_spec`). -/
def fcu (P : Params) : ℝ := sInf {g : ℝ | fH P < g ∧ g ≤ fL P ∧ Φ P g = 0}

/-- `f'_cu`: the root of `Φ' = 0` on `(f'_H, f'_L]` (milestone `fcup_spec`). -/
def fcup (P : Params) : ℝ := sInf {g : ℝ | fHp P < g ∧ g ≤ fLp P ∧ Φp P g = 0}

/-! ### Solution types (eqs. (2)–(9), pp. 10–11 and 15) -/

/-- `ℍ_u = (n* = µ t λ_H²/(4f), λ* = λ_H, q* = λ_H m_H)` (eq. (2)). -/
def Hu (P : Params) : MPDec := ⟨P.μ * P.t * lamH P ^ 2 / (4 * P.f), lamH P, lamH P * P.mH⟩

/-- `ℍ_c = (n* = ∛(tµ/(4f)), λ* = 1/n*, q* = m_H/n*)` (eq. (3)). -/
def Hc (P : Params) : MPDec :=
  ⟨(P.t * P.μ / (4 * P.f)) ^ ((1 : ℝ) / 3), 1 / (P.t * P.μ / (4 * P.f)) ^ ((1 : ℝ) / 3),
    P.mH / (P.t * P.μ / (4 * P.f)) ^ ((1 : ℝ) / 3)⟩

/-- `𝕃_u = (n* = m_L t λ_L²/(4f), λ* = λ_L, q* = λ_L m_L)` (eq. (4)). -/
def Lu (P : Params) : MPDec := ⟨P.mL * P.t * lamL P ^ 2 / (4 * P.f), lamL P, lamL P * P.mL⟩

/-- `𝕃_c = (n* = ∛(t m_L/(4f)), λ* = 1/n*, q* = m_L/n*)` (eq. (5)). -/
def Lc (P : Params) : MPDec :=
  ⟨(P.t * P.mL / (4 * P.f)) ^ ((1 : ℝ) / 3), 1 / (P.t * P.mL / (4 * P.f)) ^ ((1 : ℝ) / 3),
    P.mL / (P.t * P.mL / (4 * P.f)) ^ ((1 : ℝ) / 3)⟩

/-- `ℍ'_u = (n* = µ t λ'_H²/(4f), λ* = λ'_H, q* = λ'_H m_H, λ*_MC = 1 − n*λ'_H)` (eq. (6)),
with `p*_MC = r − w` (Lemma 2). -/
def Hup (P : Params) : HybDec :=
  { n := P.μ * P.t * lamHp P ^ 2 / (4 * P.f), lam := lamHp P, q := lamHp P * P.mH,
    pMC := P.r - P.w, lamMC := 1 - P.μ * P.t * lamHp P ^ 2 / (4 * P.f) * lamHp P }

/-- `ℍ'_c = (ℍ_c, λ*_MC = 0)` (eq. (7)), with `p*_MC = r − w`. -/
def Hcp (P : Params) : HybDec := { Hc P with pMC := P.r - P.w, lamMC := 0 }

/-- `𝕃'_u = (n* = m_L t λ'_L²/(4f), λ* = λ'_L, q* = λ'_L m_L, λ*_MC = 1 − n*λ'_L)` (eq. (8)),
with `p*_MC = r − w`. -/
def Lup (P : Params) : HybDec :=
  { n := P.mL * P.t * lamLp P ^ 2 / (4 * P.f), lam := lamLp P, q := lamLp P * P.mL,
    pMC := P.r - P.w, lamMC := 1 - P.mL * P.t * lamLp P ^ 2 / (4 * P.f) * lamLp P }

/-- `𝕃'_c = (𝕃_c, λ*_MC = 0)` (eq. (9)), with `p*_MC = r − w`. -/
def Lcp (P : Params) : HybDec := { Lc P with pMC := P.r - P.w, lamMC := 0 }

end

end MCSustain.WinWin


