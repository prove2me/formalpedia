-- Prove2me | Definitions.Def_PostedPriceLimits_FullRevelation_Analysis
-- name    : PostedPriceLimits_FullRevelation_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:11.07707+00:00
-- url     : https://prove2.me/theorems/8c6b9477-7002-469e-bea6-41fe502e2125
-- title:
--   §5.3–5.6 analysis objects: strengthened fixed-order mechanism, $B_{t,p}$, $W_t$, $U_t$, $\Delta_t$, $V_{t,i}$ and the good event
-- statement:
--   **Analysis mechanism** (§5.3, Observation 5.2). The mechanism knows all $\psi_{t,\gamma},\xi_{t,\gamma}$ from the start and visits bidders in the fixed order. Before visiting bidder $i$ it proposes prices in $[0,\infty]^M$ as an arbitrary function of $\psi,\xi$ and of the records of the bidders $j$ visited before $i$: $\pi(j)$, all $\tau_t(j)$, all $N_{t,j}$ and the owner rank sets $Z_{\pi(j),k}$. Items already allocated are priced $+\infty$; bidder $i$ receives the lexicographically smallest utility-maximizing bundle of $v_i$. Nothing about unvisited bidders is available. A mechanism is *measurable* when its proposed prices are random variables.
--
--   **Relevance** (Definition 5.3). $(t,i)$ is relevant if $t\notin\pi([i-1])$.
--
--   **Analysis quantities** (§§5.4–5.6), for prices $p\in[0,\infty]^{Z_t}$:
--   1. $B_{t,p}(k,x)=(1-p_x/(2\mathrm{val}(k)))_+$ for $k\in[\kappa]$ ($0$ when $p_x=+\infty$).
--   2. $W_t(p)=\sum_{x\in Z_t}w_t(x)\mathbf 1(w_t(x)>p_x)$.
--   3. $U_t(\gamma,A,p)=|Z_t|^{-1}\max_{S\subseteq Z_t}\{u^{(t,\gamma,A)}(S)+u_0^{(t,\gamma,A)}\mathbf 1(S\ne\varnothing)-p(S)\}$, and the bias-free $U_t(\gamma,A,B)=|Z_t|^{-1}\sum_{x}\sum_{k\in[\kappa]}2\mathrm{val}(k)\mathbf 1(\psi_{t,\gamma}(x)=k)\mathbf 1(\xi_{t,\gamma}(x)\le1+A(k,x))B(k,x)$.
--   4. $\Delta_t(L,B)=\min_{A\in\mathcal A_{t,L}}\mathrm{Avg}[(A-B)^2]$.
--   5. $S_{t,i}(p)$ is the lexicographically smallest utility-maximizing set of $v_{t,i}$ and $V_{t,i}(p)=w_t(S_{t,i}(p))$.
--   6. $(\gamma,A)$ defines a utility-maximizing clause of $v_{t,i}$ at $p$ if $\gamma\in\Gamma_{t,i}$, $A\in\mathcal A_{t,\gamma}$ and $U_t(\gamma,A,p)\ge U_t(\gamma',A',p)$ for all clauses $(\gamma',A')$ of $v_{t,i}$.
--
--   **Good event** (Definition 5.4). $\mathcal E$ is the conjunction of the three clauses of Proposition A.2 and, at every relevant block-visit pair $(t,i)$ with the prices $p$ the mechanism posts on $Z_t$, the three clauses of Proposition A.3: (1) $|U_t(\gamma,A,B_{t,p})-(2\mathrm{Avg}[B_{t,p}]+2\mathrm{Avg}[AB_{t,p}])|\le2\varepsilon$ for $\gamma\in\Gamma_{t,i}$, $A\in\mathcal A_{t,\gamma}$; (2) $\Delta_t(L\cap\tau_t([i-1]),B_{t,p})-\Delta_t(L,B_{t,p})\le2\varepsilon$ for $L\subseteq N_{t,i}\setminus\tau_t(i)$ with $|L|\le n-1$; (3) $|\mathrm{Avg}[B_{t,p}(k,\cdot)\mid Z_{t,r}]-\mathrm{Avg}[B_{t,p}(k,\cdot)\mid Z_{t,r,[i-1]}]|\le3\varepsilon$ for $k,r\in[\kappa]$. It is defined from these formulas, not assumed.
--
--   **Formalization Note** Bidders are $\{0,\dots,n-1\}$; $[i-1]$ is the set of bidders before $i$ and $[i]$ the set up to $i$.
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), §5.3 Observation 5.2 and Definition 5.3, pp.17–18 (PDF 18–19); Definition 5.4 and §5.4, p.19 (PDF 20); §5.4 Δ_t, p.20 (PDF 21); §5.6, p.23 (PDF 24); Propositions A.2, A.3, pp.28–29 (PDF 29–30); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Model
import Definitions.Def_PostedPriceLimits_FullRevelation_Construction

open MeasureTheory
open scoped ENNReal

namespace PostedPriceLimits.FullRevelation

/-! ## The analysis of §§5.3–5.6: the strengthened fixed-order mechanism and the good event

In the analysis the mechanism knows all `ψ_{t,γ}, ξ_{t,γ}` from the start and visits the
bidders in the fixed order `0, 1, …, n−1` (Observation 5.2). After visiting bidder `j` it
additionally learns `π(j)`, every `τ_t(j)`, every `N_{t,j}` and the owner rank sets
`Z_{π(j),k}`; nothing about unvisited bidders. -/

variable {n : ℕ}

/-- The information disclosed after visiting a bidder `j`: `π(j)`, `(τ_t(j))_t`, `(N_{t,j})_t`
and `(Z_{π(j),k})_k`. -/
structure RevealedRecord (n : ℕ) where
  owned : Fin n
  names : Fin n → Fin (poolSize n)
  lists : Fin n → Finset (Fin (poolSize n))
  ownerRanks : ℕ → Finset (Fin (blockSize n))

/-- The record actually disclosed after visiting bidder `j` in the realisation `ω`. -/
noncomputable def revealed (ω : Latent n) (j : Fin n) : RevealedRecord n :=
  ⟨perm ω j, fun t => names ω t j, fun t => nameList ω t j, fun k => ownerRankSet ω (perm ω j) k⟩

/-- A deterministic mechanism in the strengthened analysis model of §5.3. Before visiting
bidder `i` it posts prices `p ∈ [0,∞]^M` as an arbitrary function of the public functions
`ψ, ξ` and of the records of the already visited bidders `j < i` (earlier valuations, prices and
bundles are computable from these). -/
structure AnalysisMech (n : ℕ) where
  price : (i : Fin n) → (Fin n → Ctx n → Fin (blockSize n) → ℕ) →
    (Fin n → Ctx n → Fin (blockSize n) → ℝ) → ((j : Fin n) → j < i → RevealedRecord n) →
    Fin (numItems n) → ℝ≥0∞

namespace AnalysisMech

/-- The price vector the mechanism proposes before visiting bidder `i`. -/
noncomputable def rawPrice (M : AnalysisMech n) (ω : Latent n) (i : Fin n) :
    Fin (numItems n) → ℝ≥0∞ :=
  M.price i (psi ω) (xi ω) (fun j _ => revealed ω j)

/-- The routine measurability of a mechanism: its proposed prices are random variables. -/
def PricesMeasurable (M : AnalysisMech n) : Prop :=
  ∀ i, Measurable (fun ω : Latent n => M.rawPrice ω i)

/-- The bundles after the first `k` visits (bidders `0, …, k−1`); each visited bidder receives
the lexicographically smallest utility-maximizing bundle of `v_i` at the posted prices, where
already allocated items are priced `+∞`. -/
noncomputable def bundlesUpTo (M : AnalysisMech n) (ω : Latent n) :
    ℕ → Fin n → Finset (Fin (numItems n))
  | 0 => fun _ => ∅
  | k + 1 =>
    let B := bundlesUpTo M ω k
    if h : k < n then
      Function.update B ⟨k, h⟩
        (demandSet (bidderVal ω ⟨k, h⟩)
          (fun x => if x ∈ Finset.univ.biUnion B then ⊤ else M.rawPrice ω ⟨k, h⟩ x))
    else B

/-- The prices `p ∈ [0,∞]^M` posted at the visit of bidder `i`: the proposed prices, with
`+∞` on the items allocated to bidders `j < i`. -/
noncomputable def postedPrice (M : AnalysisMech n) (ω : Latent n) (i : Fin n) :
    Fin (numItems n) → ℝ≥0∞ :=
  fun x => if x ∈ Finset.univ.biUnion (M.bundlesUpTo ω i) then ⊤ else M.rawPrice ω i x

/-- The final allocation `S_1, …, S_n` produced by the mechanism. -/
noncomputable def allocation (M : AnalysisMech n) (ω : Latent n) : Fin n → Finset (Fin (numItems n)) :=
  M.bundlesUpTo ω n

end AnalysisMech

/-- The bidders visited before `i`, i.e. `[i − 1]` in the paper's 1-based indexing. -/
def before (i : Fin n) : Finset (Fin n) := Finset.univ.filter (fun j => j < i)

/-- The bidders visited up to and including `i`, i.e. `[i]`. -/
def upTo (i : Fin n) : Finset (Fin n) := Finset.univ.filter (fun j => j ≤ i)

/-- Definition 5.3: the block-visit pair `(t, i)` is relevant if the owner of `Z_t` has not
been visited before `i`, i.e. `t ∉ π([i − 1])`. -/
def IsRelevant (ω : Latent n) (t i : Fin n) : Prop :=
  ∀ j, j < i → perm ω j ≠ t

/-- The restriction `p|_{Z_t}` of a price vector to block `t`. -/
def localPrice (p : Fin (numItems n) → ℝ≥0∞) (t : Fin n) : Fin (blockSize n) → ℝ≥0∞ :=
  fun j => p (blockItem n t j)

/-- `B_{t,p}(k, x) = (1 − p_x / (2 val(k)))₊` on `[κ] × Z_t` (`0` when `p_x = +∞`; `0` off
`[κ]`). -/
noncomputable def affordFn (n : ℕ) (p : Fin (blockSize n) → ℝ≥0∞) : ℕ → Fin (blockSize n) → ℝ :=
  fun k x => if k ∈ rankRange (kappa n) ∧ p x ≠ ⊤ then
    max 0 (1 - (p x).toReal / (2 * (val n k : ℝ))) else 0

/-- `W_t(p) = ∑_{x ∈ Z_t} w_t(x) 1(w_t(x) > p_x)`, the owner value affordable at prices `p`. -/
noncomputable def ownerAfford (ω : Latent n) (t : Fin n) (p : Fin (blockSize n) → ℝ≥0∞) : ℝ :=
  ∑ x, if ENNReal.ofReal (ownerItemVal ω t x) > p x then ownerItemVal ω t x else 0

/-- `U_t(γ, A, p) = |Z_t|⁻¹ max_{S ⊆ Z_t} {u^{(t,γ,A)}(S) + u₀^{(t,γ,A)} 1(S ≠ ∅) − p(S)}`, the
maximum taken over bundles avoiding `+∞`-priced items. -/
noncomputable def clauseUtil (ω : Latent n) (t : Fin n) (γ : Ctx n)
    (A : ℕ → Fin (blockSize n) → ℝ) (p : Fin (blockSize n) → ℝ≥0∞) : ℝ :=
  ((availableItems p).powerset.sup' (Finset.powerset_nonempty _)
    (fun S => ∑ x ∈ S, clauseCoef ω t γ A x + (if S = ∅ then 0 else clauseBias γ A) -
      ∑ x ∈ S, (p x).toReal)) / (blockSize n : ℝ)

/-- The second `U_t` of §5.4:
`U_t(γ, A, B) = |Z_t|⁻¹ ∑_{x ∈ Z_t} ∑_{k ∈ [κ]} 2 val(k) 1(ψ_{t,γ}(x) = k) 1(ξ_{t,γ}(x) ≤ 1 + A(k,x)) B(k,x)`. -/
noncomputable def clauseUtilB (ω : Latent n) (t : Fin n) (γ : Ctx n)
    (A B : ℕ → Fin (blockSize n) → ℝ) : ℝ :=
  (∑ x, ∑ k ∈ rankRange (kappa n),
    2 * (val n k : ℝ) * (if psi ω t γ x = k then 1 else 0) *
      (if xi ω t γ x ≤ 1 + A k x then 1 else 0) * B k x) / (blockSize n : ℝ)

/-- `Δ_t(L, B) = min_{A ∈ 𝒜_{t,L}} Avg[(A − B)²]` (a minimum over a finite nonempty set). -/
noncomputable def bestApprox (ω : Latent n) (t : Fin n) (L : Finset (Fin (poolSize n)))
    (B : ℕ → Fin (blockSize n) → ℝ) : ℝ :=
  sInf {r | ∃ A ∈ gridFns ω t L, r = avgRK n (fun k x => (A k x - B k x) ^ 2)}

/-- `S_{t,i}(p)`: the lexicographically smallest utility-maximizing set of `v_{t,i}` at `p`. -/
noncomputable def nonOwnerDemand (ω : Latent n) (t i : Fin n) (p : Fin (blockSize n) → ℝ≥0∞) :
    Finset (Fin (blockSize n)) :=
  demandSet (nonOwnerVal ω t i) p

/-- `V_{t,i}(p) = w_t(S_{t,i}(p))`, the owner value destroyed by the non-owner `i`. -/
noncomputable def destroyed (ω : Latent n) (t i : Fin n) (p : Fin (blockSize n) → ℝ≥0∞) : ℝ :=
  ownerVal ω t (nonOwnerDemand ω t i p)

/-- `(γ, A)` defines a utility-maximizing clause of `v_{t,i}` at prices `p`:
`γ ∈ Γ_{t,i}`, `A ∈ 𝒜_{t,γ}`, and `U_t(γ, A, p) ≥ U_t(γ', A', p)` for every clause `(γ', A')`
of `v_{t,i}`. -/
def IsUtilMaxClause (ω : Latent n) (t i : Fin n) (p : Fin (blockSize n) → ℝ≥0∞) (γ : Ctx n)
    (A : ℕ → Fin (blockSize n) → ℝ) : Prop :=
  γ ∈ ctxsOf ω t i ∧ A ∈ gridFns ω t (ctxRest γ) ∧
    ∀ γ' ∈ ctxsOf ω t i, ∀ A' ∈ gridFns ω t (ctxRest γ'), clauseUtil ω t γ' A' p ≤ clauseUtil ω t γ A p

/-- The event of Proposition A.2 (its three clauses). -/
def EventA2 (ω : Latent n) : Prop :=
  (∀ t, ∀ k ∈ rankRange (kappa n),
    |(val n k : ℝ) * (ownerRankSet ω t k).card - blockSize n| ≤ eps n * blockSize n) ∧
  (∀ t, ∀ k ∈ rankRange (kappa n), ∀ I : Finset (Fin n),
    ((zSet ω t k I).card : ℝ) ≥ (blockSize n : ℝ) / lam n) ∧
  (∀ t, ∀ k ∈ rankRange (kappa n), ∀ r ∈ rankRange (kappa n), ∀ I J : Finset (Fin n), I ⊆ J →
    ∀ A ∈ gridFns ω t (I.image (names ω t)),
      |avg (zSet ω t r I) (A k) - avg (zSet ω t r J) (A k)| ≤ eps n)

/-- The three clauses of Proposition A.3 for the block-visit pair `(t, i)` and the prices
`p ∈ [0,∞]^{Z_t}` posted at that visit. -/
def EventA3At (ω : Latent n) (t i : Fin n) (p : Fin (blockSize n) → ℝ≥0∞) : Prop :=
  (∀ γ ∈ ctxsOf ω t i, ∀ A ∈ gridFns ω t (ctxRest γ),
    |clauseUtilB ω t γ A (affordFn n p) -
      (2 * avgRK n (affordFn n p) + 2 * avgRK n (fun k x => A k x * affordFn n p k x))| ≤ 2 * eps n) ∧
  (∀ L ⊆ (nameList ω t i).erase (names ω t i), L.card ≤ n - 1 →
    bestApprox ω t (L ∩ (before i).image (names ω t)) (affordFn n p) -
      bestApprox ω t L (affordFn n p) ≤ 2 * eps n) ∧
  (∀ k ∈ rankRange (kappa n), ∀ r ∈ rankRange (kappa n),
    |avg (ownerRankSet ω t r) (affordFn n p k) - avg (zSet ω t r (before i)) (affordFn n p k)| ≤
      3 * eps n)

/-- Definition 5.4: the good event `ℰ` for the mechanism `M`: the event of Proposition A.2,
and the clauses of Proposition A.3 at every relevant block-visit pair with the prices the
mechanism actually posts there. -/
def GoodEvent (M : AnalysisMech n) (ω : Latent n) : Prop :=
  EventA2 ω ∧ ∀ t i, IsRelevant ω t i → EventA3At ω t i (localPrice (M.postedPrice ω i) t)

end PostedPriceLimits.FullRevelation


