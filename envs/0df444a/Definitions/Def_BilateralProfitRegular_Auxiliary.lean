-- Prove2me | Definitions.Def_BilateralProfitRegular_Auxiliary
-- name    : BilateralProfitRegular_Auxiliary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-13T19:18:35.113249+00:00
-- url     : https://prove2.me/theorems/b7311e5c-6bb9-4d98-a940-b5f378a9c554
-- title:
--   §6.1–6.2 — the triangle $\mathcal T$, $\mu^\star$, auxiliary profits $r_\lambda$, balancing parameters $\lambda_x$, candidates and their guarantees
-- statement:
--   Let $\mathcal T=\{(p,q)\in[0,1]^2:p\le q\}$, with interior $\mathrm{int}(\mathcal T)=\{0<p<q<1\}$. For an environment $E$ the following objects are defined:
--
--   1. the trade probability $P(p,q)=\Pr(s\le p,\ b\ge q)$ and the expected profit $\mu(p,q)=(q-p)P(p,q)$;
--   2. the optimum $\mu^\star=\sup_{(p,q)\in[0,1]^2}\mu(p,q)$;
--   3. the **balancing parameter** $\lambda_x=\sqrt{F_s(p)/(1-F_b(q))}$ of $x=(p,q)$;
--   4. the **auxiliary profit**
--   $$r_\lambda(p,q)=\frac{4(q-p)}{\big(\lambda/F_s(p)+\lambda^{-1}/(1-F_b(q))\big)^2}\qquad(\lambda>0),$$
--   which is eq. (38);
--   5. a **candidate** $(\mathcal K_i,w_i,\theta_i,\widehat P(w_i))$, which consists of a region, a root, an offset and a stored estimate, with parameter $\lambda_i=e^{\theta_i}\lambda_{w_i}$.
--
--   **Valid** collects what Lemma 6.4 asserts of each candidate on its high-probability event:
--
--   - $\mathcal K_i\subseteq\mathrm{int}(\mathcal T)$ is compact and convex and contains $w_i$;
--   - $r_{\lambda_ie^u}\ge0.99\mu^\star$ on $\mathcal K_i$ for $|u|\le10^{-3}$;
--   - for any two points of $\mathcal K_i$, both crosses lie in $\mathcal T$, and the trade probabilities of the two points and of their crosses lie in $[\widehat P(w_i)/10,10\widehat P(w_i)]$;
--   - $\delta\le\widehat P(w_i)\le1$, and $\delta/(q-p)\le10\widehat P(w_i)$ on $\mathcal K_i$.
--
--   **NearOpt** is Lemma 6.4(i)'s property of $i^\star$: $\max_{\mathcal K_i}r_{\lambda_ie^u}\ge\mu^\star-3\eta$ for $|u|\le10^{-3}\sqrt{\eta/\delta}$. **InitGuarantee** gathers $\eta<\delta$, $\delta\le\mu^\star<6\delta$, every candidate valid, and some candidate near-optimal. **CalibValid** is eq. (49): $\rho>0$ and $|\log(\rho\lambda_z/\lambda_i)|\le10^{-3}\sqrt{\eta/\delta}$.
--
--   **Formalization Note** $P$ and $\mu$ are computed from the joint law. That they factor as $F_s(p)(1-F_b(q))$ is a fact to be proved, not part of a definition. $r_\lambda$ and $\lambda_x$ match the paper only on $\mathrm{int}(\mathcal T)$, which is the only place the statements use them. "Max over $\mathcal K_i$" is written with $\forall$/$\exists$ over $\mathcal K_i$. Logarithms are natural.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), §2, p.4 (PDF 6); eq. (38), p.37 (PDF 39); crosses, p.38 (PDF 40); candidates, p.39 (PDF 41); Lemma 6.4, p.40 (PDF 42); eq. (49), p.41 (PDF 43)

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_MechanismDesign_BilateralTrade_Model

namespace BilateralProfitRegular

open BilateralProfit MechanismDesign.BilateralTrade

/-! # Auxiliary profits, balancing parameters, crosses and candidates (§6.1–6.2)

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…): the triangle `𝒯` and its
interior (§2, p.4), the optimum `µ⋆` (p.4), the auxiliary profit `r_λ` and the balancing parameter
`λ_x` (eq. (38), p.37 = PDF 39), crossed pairs (p.38 = PDF 40), candidates `(𝒦_i, w_i, θ_i, P̂(w_i))`
with parameter `λ_i = e^{θ_i} λ_{w_i}` (p.39 = PDF 41), and the guarantees Lemma 6.4 (p.40 = PDF
42) asserts of the candidates on its high-probability event, used as hypotheses by Lemmas 6.5
and 6.6.

**Formalization Note.** `F_s = E.cdfS`, `F_b = E.cdfB`; `P(p, q)` is the trade probability
`Ptrade E.prior (p, q)` computed from the joint law (it equals `F_s(p)(1 − F_b(q))` by
independence, a fact to be proved, not a definition), and `µ = muP E.prior`. `r_λ` and `λ_x` are
total Lean functions; their values are the paper's only on `int 𝒯 = {0 < p < q < 1}`, the only
place where the statements use them. "max over `𝒦`" of a continuous function on a compact set is
written as a `∀`/`∃` statement over `𝒦`. Logarithms are natural. -/

/-- The triangle `𝒯 = {(p, q) ∈ [0,1]² : p ≤ q}` (p.4). -/
def triT : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ x.1 ≤ x.2 ∧ x.2 ≤ 1}

/-- Its interior `int(𝒯) = {0 < p < q < 1}`. -/
def intT : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ x.1 < x.2 ∧ x.2 < 1}

/-- The trade probability `P(p, q) = Pr(s ≤ p, b ≥ q)` under the environment's joint law. -/
noncomputable def P (E : Environment) (a : ℝ × ℝ) : ℝ := Ptrade E.prior a

/-- The expected profit `µ(p, q) = (q − p) P(p, q)`. -/
noncomputable def mu (E : Environment) (a : ℝ × ℝ) : ℝ := muP E.prior a

/-- The optimal expected profit `µ⋆ = sup_{(p,q) ∈ [0,1]²} µ(p, q)` (p.4; a supremum of a
bounded nonempty set of reals). -/
noncomputable def muStar (E : Environment) : ℝ :=
  sSup (mu E '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))

/-- The balancing parameter `λ_x = √(F_s(p) / (1 − F_b(q)))` of `x = (p, q)` (eq. (38)). -/
noncomputable def balance (E : Environment) (x : ℝ × ℝ) : ℝ :=
  Real.sqrt (E.cdfS x.1 / (1 - E.cdfB x.2))

/-- The auxiliary profit `r_λ(p, q) = 4(q − p) / (λ/F_s(p) + λ⁻¹/(1 − F_b(q)))²` (eq. (38)). -/
noncomputable def auxProfit (E : Environment) (lam : ℝ) (x : ℝ × ℝ) : ℝ :=
  4 * (x.2 - x.1) / (lam / E.cdfS x.1 + lam⁻¹ / (1 - E.cdfB x.2)) ^ 2

/-- A candidate `(𝒦_i, w_i, θ_i, P̂(w_i))` (Algorithm 7, step 7, p.40). -/
structure Candidate where
  /-- the convex region `𝒦_i` -/
  region : Set (ℝ × ℝ)
  /-- the root `w_i` -/
  root : ℝ × ℝ
  /-- the offset `θ_i` -/
  offset : ℝ
  /-- the stored estimate `P̂(w_i)` -/
  est : ℝ

/-- The candidate's parameter `λ_i = e^{θ_i} λ_{w_i}` (p.39). -/
noncomputable def Candidate.param (E : Environment) (c : Candidate) : ℝ :=
  Real.exp c.offset * balance E c.root

/-- What Lemma 6.4 asserts of every candidate on its event (p.40): `𝒦_i ⊆ int 𝒯` compact and
convex containing `w_i`; (i) `r_{λ_i e^u} ≥ 0.99 µ⋆` on `𝒦_i` for `|u| ≤ 10⁻³`; (ii) for any two
points `(p, q), (u, v)` of `𝒦_i` both crosses `(p, v)`, `(u, q)` lie in `𝒯`, and their trade
probabilities and those of the two points lie in `[P̂(w_i)/10, 10 P̂(w_i)]`; `δ ≤ P̂(w_i) ≤ 1`
and `δ/(q − p) ≤ 10 P̂(w_i)` on `𝒦_i`. -/
def Candidate.Valid (E : Environment) (δ : ℝ) (c : Candidate) : Prop :=
  c.region ⊆ intT ∧ IsCompact c.region ∧ Convex ℝ c.region ∧ c.root ∈ c.region ∧
  (∀ u : ℝ, |u| ≤ 1 / 1000 → ∀ x ∈ c.region,
      99 / 100 * muStar E ≤ auxProfit E (c.param E * Real.exp u) x) ∧
  (∀ x ∈ c.region, ∀ y ∈ c.region,
      (x.1, y.2) ∈ triT ∧ (y.1, x.2) ∈ triT ∧
      ∀ e ∈ ({x, y, (x.1, y.2), (y.1, x.2)} : Set (ℝ × ℝ)),
        c.est / 10 ≤ P E e ∧ P E e ≤ 10 * c.est) ∧
  δ ≤ c.est ∧ c.est ≤ 1 ∧
  (∀ x ∈ c.region, δ / (x.2 - x.1) ≤ 10 * c.est)

/-- The near-optimal candidate `i⋆` of Lemma 6.4(i):
`max_{x ∈ 𝒦_{i⋆}} r_{λ_{i⋆} e^u}(x) ≥ µ⋆ − 3η` for `|u| ≤ 10⁻³ √(η/δ)`. -/
def Candidate.NearOpt (E : Environment) (η δ : ℝ) (c : Candidate) : Prop :=
  ∀ u : ℝ, |u| ≤ 1 / 1000 * Real.sqrt (η / δ) →
    ∃ x ∈ c.region, muStar E - 3 * η ≤ auxProfit E (c.param E * Real.exp u) x

/-- The guarantees of the high-probability event of Lemma 6.4 for a triggered output `(δ, cs)`
(p.40), apart from the count of candidates and the regret of initialization:
`η < δ`, `δ ≤ µ⋆ < 6δ`, every candidate valid, and some candidate near-optimal. -/
def InitGuarantee (E : Environment) (η δ : ℝ) (cs : List Candidate) : Prop :=
  η < δ ∧ δ ≤ muStar E ∧ muStar E < 6 * δ ∧ (∀ c ∈ cs, c.Valid E δ) ∧
  ∃ c ∈ cs, c.NearOpt E η δ

/-- A valid calibration (eq. (49), p.41): the multiplier `ρ > 0` for the reference `z` satisfies
`|log(ρ λ_z / λ_i)| ≤ 10⁻³ √(η/δ)`. -/
def CalibValid (E : Environment) (η δ : ℝ) (c : Candidate) (z : ℝ × ℝ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ |Real.log (ρ * balance E z / c.param E)| ≤ 1 / 1000 * Real.sqrt (η / δ)

end BilateralProfitRegular


