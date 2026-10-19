-- Prove2me | Definitions.Def_OmniPool_BOPS_Setting
-- name    : OmniPool_BOPS_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:03.749658+00:00
-- url     : https://prove2.me/theorems/e1b45edb-7cfc-4204-a682-56c3bc79079c
-- title:
--   §3–§4, App. A, pp. 5–14, OA1–OA7 — profits (2), (4), fill rates, choice maps (A1), (A4), RE equilibria (Definitions A1, A2), Pareto dominance
-- statement:
--   This file sets up the BASE and BOPS models of Hu, Xu, Xue and Yang for a single retailer that sells through a brick-and-mortar (B&M) store and an online channel served by a distribution centre (DC).
--
--   **Market.** Customers come in two segments with random market sizes on a probability space $(\Omega,\mathcal F,\mathbb P)$: $D_s$ store-only customers and $D_m$ omni-customers. The parameters are the offline price $p_b$ and store unit cost $c_b$, the online price $p_o$ and DC unit cost $c_o$, the store visiting cost $k$, the online waiting cost $t$, and the base surpluses $u_o=v_o-p_o$ (online) and $u_b=v_b-p_b$ (offline). The indicator $\mathbf 1_{\{k\le t\}}$ records whether omni-customers prefer buy-online-pickup-at-store (BOPS).
--
--   **BASE (independent channels).** Given beliefs $\hat\phi_s,\hat\phi_m$ about the fractions of store-only and omni-customers who shop offline, the retailer's expected profit from a store order quantity $q$ is equation (2):
--   $$\pi_B(q)=p_b\,\mathbb E[\min(\hat\phi_mD_m+\hat\phi_sD_s,q)]-c_bq+(p_o-c_o)\,\mathbb E[(1-\hat\phi_m)D_m].$$
--   The store's fill rate is the Deneckere–Peck in-stock probability $\mathbb E[\min(D,q)]/\mathbb E[D]$ for the offline demand $D=\hat\phi_mD_m+\hat\phi_sD_s$, and it is $0$ when nobody shops offline. Given a fill-rate belief $\hat\zeta$, customers choose by (A1): omni-customers go offline iff $\hat\zeta u_b-k\ge u_o-t$ (otherwise online), store-only customers buy iff $\hat\zeta u_b-k\ge 0$ (otherwise exit). A **rational-expectations (RE) equilibrium** (Definition A1) is a tuple $(q,\zeta,\phi_s,\phi_m)$ such that $(\phi_s,\phi_m)$ is the (A1) choice at $\zeta$, $q\ge0$ maximizes $\pi_B$ over $q\ge 0$ for the beliefs $(\phi_s,\phi_m)$, and $\zeta$ is the fill rate that $q$ realizes. It is **Pareto-dominant** if the retailer's profit, the store-only customers' utility $\phi_s(\zeta u_b-k)$ and the omni-customers' utility $\phi_m(\zeta u_b-k)+(1-\phi_m)(u_o-t)$ are each at least as large as at every RE equilibrium.
--
--   **BOPS.** Store-only customers have priority on the store inventory; omni-customers who prefer BOPS take what is left and spill over to the online channel on a stockout. Given the belief $\hat\phi_s$, the expected profit is equation (4):
--   $$\pi_P(q)=p_b\mathbb E[\min(\hat\phi_sD_s,q)]+p_o\mathbb E[\min(\mathbf 1_{\{k\le t\}}D_m,(q-\hat\phi_sD_s)^+)]-c_bq+(p_o-c_o)\mathbb E[\mathbf 1_{\{k>t\}}D_m+(\mathbf 1_{\{k\le t\}}D_m-(q-\hat\phi_sD_s)^+)^+].$$
--   The store-only fill rate is $\mathbb E[\min(\hat\phi_sD_s,q)]/\mathbb E[D_s]$ ($0$ if $\hat\phi_s=0$); store-only customers buy iff $\hat\zeta u_b\ge k$ (A4). RE equilibria (Definition A2) and Pareto dominance are as for BASE, with the retailer and the store-only customers as the players.
--
--   **Optimal quantities.** $q_s$, $q_{sm}$, $q_p$ are the unique maximizers over $q\ge0$ of (2) at $(\hat\phi_s,\hat\phi_m)=(1,0)$, of (2) at $(1,1)$, and of (4) at $\hat\phi_s=1$; the thresholds are $\zeta_s=\mathbb E[\min(D_s,q_s)]/\mathbb E[D_s]$, $\zeta_{sm}=\mathbb E[\min(D_m+D_s,q_{sm})]/\mathbb E[D_m+D_s]$ and $\zeta_p=\mathbb E[\min(D_s,q_p)]/\mathbb E[D_s]$.
--
--   These objects are what Propositions 1–3 of the paper are about: the equilibria are fixed points, not the closed-form case tables of the propositions.
--
--   **Formalization Note.** Market sizes are arbitrary random variables; the theorems that use these definitions assume them nonnegative and integrable with positive means, replacing the paper's normal model, under which Proposition 3 is false (normal demand is negative with positive probability). Beliefs are real numbers that the choice maps only set to $0$ or $1$. The choice maps are written in the utility form of (1) and (3); they coincide with the ratio form of (A1)/(A4) when $u_b>0$. Definitions A1/A2 are read with the retailer's decision as an optimal order quantity given the beliefs (the paper derives (A2)/(A5) as that optimum) and with one copy of $\zeta$ and $\phi$ (condition (iii) built in). The paper defines no BOPS payoff for omni-customers, so BOPS Pareto dominance compares the retailer and the store-only customers. "The optimal order quantity" is read as the unique maximizer over $q\ge 0$.
-- source:
--   Hu, Xu, Xue & Yang, Demand Pooling in Omnichannel Operations, accepted manuscript (SSRN 3214047; Manage. Sci. 68(2):883–894, 2022, doi:10.1287/mnsc.2021.3964), §3–§4 and Appendix A, pp. 5–14, OA1–OA7: (1)–(4), (A1), (A2), (A4), (A5), Definitions A1–A2

import Mathlib

namespace OmniPool.BOPS

open MeasureTheory

/-- The primitive parameters of §3 (pp. 6–9): offline price `pb`, store unit cost `cb`,
online price `po`, DC unit cost `co`, store visiting cost `k`, online waiting cost `t`,
base online surplus `uo = vo - po` and base offline surplus `ub = vb - pb`. -/
structure Market where
  pb : ℝ
  cb : ℝ
  po : ℝ
  co : ℝ
  k : ℝ
  t : ℝ
  uo : ℝ
  ub : ℝ

/-- The indicator `1{k ≤ t}`: omni-customers prefer BOPS (p. 12). `1{k > t}` is `1 - bopsInd M`. -/
noncomputable def bopsInd (M : Market) : ℝ := if M.k ≤ M.t then 1 else 0

section Model

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The BASE expected profit (2), p. 10:
`π_B(q) = pb E[min(φm Dm + φs Ds, q)] - cb q + (po - co) E[(1 - φm) Dm]`. -/
noncomputable def profitB (M : Market) (P : Measure Ω) (Ds Dm : Ω → ℝ) (φs φm q : ℝ) : ℝ :=
  M.pb * ∫ ω, min (φm * Dm ω + φs * Ds ω) q ∂P - M.cb * q
    + (M.po - M.co) * ∫ ω, (1 - φm) * Dm ω ∂P

/-- The Deneckere–Peck fill rate of the B&M store under BASE, `E[min(D, q)] / E[D]` for the
offline demand `D = φm Dm + φs Ds` (p. 11); it is `0` when nobody shops offline ((A2), OA2). -/
noncomputable def fillB (P : Measure Ω) (Ds Dm : Ω → ℝ) (φs φm q : ℝ) : ℝ :=
  if φs = 0 ∧ φm = 0 then 0
  else (∫ ω, min (φm * Dm ω + φs * Ds ω) q ∂P) / ∫ ω, (φm * Dm ω + φs * Ds ω) ∂P

/-- The customers' channel choice (A1), OA2, in the utility form of (1): given the fill-rate
belief `ζ`, omni-customers go offline iff `ζ ub - k ≥ uo - t`, store-only customers buy iff
`ζ ub - k ≥ 0`. The result is `(φs, φm)`. -/
noncomputable def choiceB (M : Market) (ζ : ℝ) : ℝ × ℝ :=
  if M.uo - M.t ≤ ζ * M.ub - M.k then (1, 1)
  else if 0 ≤ ζ * M.ub - M.k then (1, 0) else (0, 0)

/-- A BASE outcome: order quantity `q`, fill rate `ζ` (realized = believed) and the
segment proportions `φs`, `φm` (realized = believed), Definition A1 with (iii) built in. -/
structure BaseOutcome where
  q : ℝ
  ζ : ℝ
  φs : ℝ
  φm : ℝ

/-- Definition A1 (RE equilibrium under BASE), OA2–OA3: customers' choices follow (A1)
given the fill rate; the order quantity is optimal (over `q ≥ 0`) for (2) given the
choices; and the fill rate is the one that quantity realizes. -/
def IsREE_B (M : Market) (P : Measure Ω) (Ds Dm : Ω → ℝ) (e : BaseOutcome) : Prop :=
  (e.φs, e.φm) = choiceB M e.ζ ∧ 0 ≤ e.q ∧
    (∀ q : ℝ, 0 ≤ q → profitB M P Ds Dm e.φs e.φm q ≤ profitB M P Ds Dm e.φs e.φm e.q) ∧
    e.ζ = fillB P Ds Dm e.φs e.φm e.q

/-- The retailer's equilibrium profit under BASE. -/
noncomputable def retailerB (M : Market) (P : Measure Ω) (Ds Dm : Ω → ℝ) (e : BaseOutcome) : ℝ :=
  profitB M P Ds Dm e.φs e.φm e.q

/-- A store-only customer's expected utility under BASE: `ζ ub - k` if buying, `0` if exiting. -/
def storeUtilB (M : Market) (e : BaseOutcome) : ℝ := e.φs * (e.ζ * M.ub - M.k)

/-- An omni-customer's expected utility under BASE: `ζ ub - k` offline, `uo - t` online. -/
def omniUtilB (M : Market) (e : BaseOutcome) : ℝ :=
  e.φm * (e.ζ * M.ub - M.k) + (1 - e.φm) * (M.uo - M.t)

/-- A Pareto-dominant RE equilibrium under BASE (OA3): an RE equilibrium that is weakly
better for the retailer, the store-only customers and the omni-customers than every
RE equilibrium. -/
def IsParetoREE_B (M : Market) (P : Measure Ω) (Ds Dm : Ω → ℝ) (e : BaseOutcome) : Prop :=
  IsREE_B M P Ds Dm e ∧ ∀ e' : BaseOutcome, IsREE_B M P Ds Dm e' →
    retailerB M P Ds Dm e' ≤ retailerB M P Ds Dm e ∧ storeUtilB M e' ≤ storeUtilB M e ∧
      omniUtilB M e' ≤ omniUtilB M e

/-- The BOPS expected profit (4), p. 13, term by term:
`π_P(q) = pb E[min(φs Ds, q)] + po E[min(1{k≤t} Dm, (q - φs Ds)^+)] - cb q
  + (po - co) E[1{k>t} Dm + (1{k≤t} Dm - (q - φs Ds)^+)^+]`. -/
noncomputable def profitP (M : Market) (P : Measure Ω) (Ds Dm : Ω → ℝ) (φs q : ℝ) : ℝ :=
  M.pb * ∫ ω, min (φs * Ds ω) q ∂P
    + M.po * ∫ ω, min (bopsInd M * Dm ω) (max (q - φs * Ds ω) 0) ∂P - M.cb * q
    + (M.po - M.co) * ∫ ω, ((1 - bopsInd M) * Dm ω
        + max (bopsInd M * Dm ω - max (q - φs * Ds ω) 0) 0) ∂P

/-- The store-only fill rate under BOPS, `E[min(φs Ds, q)] / E[Ds]` (p. 13); it is `0` when
store-only customers stay away ((A5), OA6). -/
noncomputable def fillP (P : Measure Ω) (Ds : Ω → ℝ) (φs q : ℝ) : ℝ :=
  if φs = 0 then 0 else (∫ ω, min (φs * Ds ω) q ∂P) / ∫ ω, Ds ω ∂P

/-- The store-only customers' choice (A4), OA6, in utility form: buy iff `ζ ub ≥ k`.
(The omni-customers' choice is `bopsInd M`.) -/
noncomputable def choiceP (M : Market) (ζ : ℝ) : ℝ := if M.k ≤ ζ * M.ub then 1 else 0

/-- A BOPS outcome: order quantity `q`, fill rate `ζ`, store-only proportion `φs`
(Definition A2 with (iii) built in). -/
structure BopsOutcome where
  q : ℝ
  ζ : ℝ
  φs : ℝ

/-- Definition A2 (RE equilibrium under BOPS), OA6. -/
def IsREE_P (M : Market) (P : Measure Ω) (Ds Dm : Ω → ℝ) (e : BopsOutcome) : Prop :=
  e.φs = choiceP M e.ζ ∧ 0 ≤ e.q ∧
    (∀ q : ℝ, 0 ≤ q → profitP M P Ds Dm e.φs q ≤ profitP M P Ds Dm e.φs e.q) ∧
    e.ζ = fillP P Ds e.φs e.q

/-- The retailer's equilibrium profit under BOPS. -/
noncomputable def retailerP (M : Market) (P : Measure Ω) (Ds Dm : Ω → ℝ) (e : BopsOutcome) : ℝ :=
  profitP M P Ds Dm e.φs e.q

/-- A store-only customer's expected utility under BOPS. -/
def storeUtilP (M : Market) (e : BopsOutcome) : ℝ := e.φs * (e.ζ * M.ub - M.k)

/-- A Pareto-dominant RE equilibrium under BOPS: weakly better for the retailer and the
store-only customers than every RE equilibrium. -/
def IsParetoREE_P (M : Market) (P : Measure Ω) (Ds Dm : Ω → ℝ) (e : BopsOutcome) : Prop :=
  IsREE_P M P Ds Dm e ∧ ∀ e' : BopsOutcome, IsREE_P M P Ds Dm e' →
    retailerP M P Ds Dm e' ≤ retailerP M P Ds Dm e ∧ storeUtilP M e' ≤ storeUtilP M e

/-- `x` is the unique maximizer of `f` over `[0, ∞)`. -/
def IsUniqueMaxNonneg (f : ℝ → ℝ) (x : ℝ) : Prop :=
  0 ≤ x ∧ ∀ q : ℝ, 0 ≤ q → q ≠ x → f q < f x

/-- `ζs = E[min(Ds, qs)] / E[Ds]` (p. 11). -/
noncomputable def zetaS (P : Measure Ω) (Ds Dm : Ω → ℝ) (qs : ℝ) : ℝ := fillB P Ds Dm 1 0 qs

/-- `ζsm = E[min(Dm + Ds, qsm)] / E[Dm + Ds]` (p. 11). -/
noncomputable def zetaSM (P : Measure Ω) (Ds Dm : Ω → ℝ) (qsm : ℝ) : ℝ := fillB P Ds Dm 1 1 qsm

/-- `ζp = E[min(Ds, qp)] / E[Ds]` (p. 13). -/
noncomputable def zetaP (P : Measure Ω) (Ds : Ω → ℝ) (qp : ℝ) : ℝ := fillP P Ds 1 qp

end Model

end OmniPool.BOPS


