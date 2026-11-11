-- Prove2me | Definitions.Def_MultiOmniRate_Lipschitz_Setting
-- name    : MultiOmniRate_Lipschitz_Setting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:21:48.19271+00:00
-- url     : https://prove2.me/theorems/672645dd-5063-48b7-8b70-6e48674dc4fe
-- title:
--   §2 setting: $\Delta_K$, losses with best responses, Bayes risk, $L_{\mathrm{All}}$, $L_{\mathrm{Lip}}$, $L_{\mathrm{prop}}$, $\mathrm{Unif}(\Delta_K)$
-- statement:
--   Fix $K\ge2$ labels $\mathcal Y=\{0,\dots,K-1\}$ and the probability simplex
--   $$\Delta_K=\Big\{p\in\mathbb R^K_{\ge0}:\ \textstyle\sum_{y=0}^{K-1}p_y=1\Big\}.$$
--   Write $e_y$ for the unit vector of label $y$, $\langle u,v\rangle=\sum_k u_kv_k$, $\|v\|_1=\sum_k|v_k|$, $\|v\|_2=(\sum_k v_k^2)^{1/2}$, and $e_y-q$ for the residual of a prediction $q\in\Delta_K$ at label $y$.
--
--   **Losses with best responses.** For an action space $\mathcal A$, a bounded decision loss is $\ell:\mathcal A\times\mathcal Y\to[-1,1]$ together with a fixed best response
--   $$\mathrm{BR}_\ell(p)\in\arg\min_{a\in\mathcal A}\ \mathbb E_{y\sim p}\,\ell(a,y)=\arg\min_{a}\ \langle p,\ell(a,\cdot)\rangle,\qquad p\in\Delta_K .$$
--   The paper fixes a *measurable* best response; `BRLoss.IsMeasurable` records that $a\mapsto\ell(a,y)$ and $\mathrm{BR}_\ell$ are measurable. The **properized loss** is $\ell^{\mathrm{pr}}(p,y)=\ell(\mathrm{BR}_\ell(p),y)$, the **discrete derivative** of a loss vector $v=\ell(a,\cdot)$ is $\Delta\ell(a)=(\ell(a,y)-\ell(a,0))_{y=0}^{K-1}$ (so $\Delta_0\ell=0$), and the **Bayes risk** is
--   $$L_\ell(p')=\min_{a\in\mathcal A}\mathbb E_{y\sim p'}\ell(a,y),$$
--   defined here as the infimum over actions for every vector $p'\in\mathbb R^K$ (it is attained at $\mathrm{BR}_\ell(p')$ when $p'\in\Delta_K$).
--
--   **Loss classes.** $\mathcal L_{\mathrm{All}}$ consists of all bounded decision losses with measurable best responses, on arbitrary measurable action spaces. $\mathcal L_{\mathrm{Lip}}$ consists of losses on $\Delta_K\times\mathcal Y$ with values in $[-1,1]$ and
--   $$|\ell(a,y)-\ell(a',y)|\le\|a-a'\|_2\qquad(a,a'\in\Delta_K,\ y\in\mathcal Y),$$
--   each with a measurable best response; the set contains every pair $(\ell,\mathrm{BR}_\ell)$, so a bound over it is a bound for every choice of measurable best responses. $\mathcal L_{\mathrm{prop}}$ consists of $[-1,1]$-valued proper losses on $\Delta_K\times\mathcal Y$: $\mathbb E_{y\sim p}\ell(p,y)\le\mathbb E_{y\sim p}\ell(a,y)$ for all $a,p\in\Delta_K$, measurable in the action.
--
--   **Uniform distribution.** $\mathrm{Unif}(\Delta_K)$ is the normalized $(K-1)$-dimensional Lebesgue measure on the simplex, written in the free coordinates $(p_1,\dots,p_{K-1})\in\{v\ge0,\ \sum v\le1\}$ with $p_0=1-\sum_{i\ge1}p_i$; for $K=2$ it is the uniform distribution on the segment. The mixture $(1-r)q+rz$ of two points of the simplex is the reporting rule's point for $0\le r\le1$.
--
--   **Upper expectation.** "$\mathbb E_\mu[f]\le c$" for a possibly non-measurable $f$ is read as an upper integral: some integrable $g\ge f$ has $\int g\,d\mu\le c$; for measurable integrable $f$ this is $\int f\,d\mu\le c$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** $\Delta_K$ is the subtype `Simplex K` of Mathlib's `stdSimplex ℝ (Fin K)`. `mix r q z` returns $q$ when $r\notin[0,1]$; every statement uses $0<r\le1/2$. `L_All` is the structure `AllLoss.{u} K` bundling an action type, its σ-algebra, the loss with its best response and the measurability proof.
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), pp. 18–19, §2 (prediction model, best responses, notable loss classes); p. 21 §2.2 (Δℓ, ℓ^pr); p. 23 §2.3 (Bayes risk); p. 25 (3.1) (Unif(Δ_K))

import Mathlib

set_option autoImplicit false

namespace MultiOmniRate.Lipschitz

open MeasureTheory ProbabilityTheory

noncomputable section

/-!
# The multi-class prediction setting (Rivkin–Okoroafor–Kim, §2, pp. 18–19)

Labels are `Y = {0, …, K − 1}`, encoded as `Fin K`. Predictions and Lipschitz/proper actions live
in the closed probability simplex `Δ_K = {p ∈ ℝ^K_{≥0} : Σ_y p_y = 1}` (`Simplex K`, the subtype of
Mathlib's `stdSimplex ℝ (Fin K)`). `e y` is the unit vector of label `y`. A bounded decision loss on
an action space `A` takes values in `[−1, 1]` and carries a fixed best response
`BR_ℓ(p) ∈ argmin_{a ∈ A} E_{y∼p} ℓ(a, y)`; the paper fixes a *measurable* best response
(`BRLoss.IsMeasurable`). `L_All` (`AllLoss`) is the class of all such losses on arbitrary action
spaces. `L_Lip` and `L_prop` are the Lipschitz and proper classes on `Δ_K × Y`.
-/

/-- The probability simplex `Δ_K ⊆ ℝ^K` (as a subtype of `Fin K → ℝ`). -/
abbrev Simplex (K : ℕ) : Type := ↥(stdSimplex ℝ (Fin K))

/-- The unit vector `e_y ∈ ℝ^K` of label `y`. -/
def e {K : ℕ} (y : Fin K) : Fin K → ℝ := Pi.single y 1

/-- The standard inner product `⟨u, v⟩ = Σ_k u_k v_k` on `ℝ^K`. -/
def dot {K : ℕ} (u v : Fin K → ℝ) : ℝ := ∑ k, u k * v k

/-- The `ℓ₁` norm `‖v‖₁ = Σ_k |v_k|`. -/
def l1 {K : ℕ} (v : Fin K → ℝ) : ℝ := ∑ k, |v k|

/-- The Euclidean norm `‖v‖₂ = (Σ_k v_k²)^{1/2}`. -/
def l2 {K : ℕ} (v : Fin K → ℝ) : ℝ := Real.sqrt (∑ k, v k ^ 2)

/-- The residual `e_y − q` of a prediction `q ∈ Δ_K` at label `y`. -/
def resid {K : ℕ} (y : Fin K) (q : Simplex K) : Fin K → ℝ := e y - (q : Fin K → ℝ)

/-- The vertex `e_0` of `Δ_K`. -/
def vertex0 (K : ℕ) [NeZero K] : Simplex K := ⟨e 0, single_mem_stdSimplex ℝ 0⟩

/-- The convex combination `(1 − r) q + r z` of two points of `Δ_K`, for `0 ≤ r ≤ 1`
(the reporting rule (3.1)); for `r ∉ [0, 1]` it returns `q` (never used). -/
noncomputable def mix {K : ℕ} (r : ℝ) (q z : Simplex K) : Simplex K :=
  if h : 0 ≤ r ∧ r ≤ 1 then
    ⟨(1 - r) • (q : Fin K → ℝ) + r • (z : Fin K → ℝ),
      convex_stdSimplex ℝ (Fin K) q.2 z.2 (sub_nonneg.2 h.2) h.1 (by ring)⟩
  else q

/-- The free coordinates `(p_1, …, p_{K−1})` region `{v ≥ 0, Σ v ≤ 1}`. -/
def paramSet (K : ℕ) [NeZero K] : Set ({i : Fin K // i ≠ 0} → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ 1}

/-- The point of `ℝ^K` with free coordinates `v` and `p_0 = 1 − Σ_{i ≥ 1} v_i`. -/
def liftCoords (K : ℕ) [NeZero K] (v : {i : Fin K // i ≠ 0} → ℝ) : Fin K → ℝ :=
  fun k => if h : k = 0 then 1 - ∑ i, v i else v ⟨k, h⟩

open Classical in
/-- `liftCoords` as a point of `Δ_K` (it lies in `Δ_K` exactly when `v ∈ paramSet K`). -/
noncomputable def toSimplex (K : ℕ) [NeZero K] (v : {i : Fin K // i ≠ 0} → ℝ) : Simplex K :=
  if h : liftCoords K v ∈ stdSimplex ℝ (Fin K) then ⟨liftCoords K v, h⟩ else vertex0 K

/-- `Unif(Δ_K)`: normalized `(K − 1)`-dimensional Lebesgue measure on the simplex, written in the
free coordinates `p_1, …, p_{K−1}` (uniform on `paramSet K`, pushed to `Δ_K`). For `K = 2` it is
the uniform distribution on the segment. -/
noncomputable def unifSimplex (K : ℕ) [NeZero K] : Measure (Simplex K) :=
  (ProbabilityTheory.cond (volume : Measure ({i : Fin K // i ≠ 0} → ℝ)) (paramSet K)).map
    (toSimplex K)

/-- A bounded decision loss `ℓ : A × Y → [−1, 1]` with a fixed best response
`BR_ℓ(p) ∈ argmin_{a ∈ A} E_{y∼p} ℓ(a, y)` for every `p ∈ Δ_K` (§2, p. 19). -/
structure BRLoss (K : ℕ) (A : Type*) where
  /-- the loss `ℓ(a, y)` -/
  loss : A → Fin K → ℝ
  /-- `ℓ` takes values in `[−1, 1]` -/
  bounded : ∀ a y, |loss a y| ≤ 1
  /-- the fixed best response -/
  BR : Simplex K → A
  /-- `BR_ℓ(p)` minimizes the expected loss `E_{y∼p} ℓ(a, y) = ⟨p, ℓ(a, ·)⟩` -/
  isBR : ∀ (p : Simplex K) (a : A), dot (p : Fin K → ℝ) (loss (BR p)) ≤ dot (p : Fin K → ℝ) (loss a)

/-- The paper's standing convention (§2, p. 19): the loss is measurable in the action and the
fixed best response is measurable. -/
def BRLoss.IsMeasurable {K : ℕ} {A : Type*} [MeasurableSpace A] (ℓ : BRLoss K A) : Prop :=
  (∀ y, Measurable fun a => ℓ.loss a y) ∧ Measurable ℓ.BR

/-- The properized loss `ℓ^pr(p, y) = ℓ(BR_ℓ(p), y)` (§2.2), as `p ↦ ℓ^pr(p, ·) ∈ ℝ^K`. -/
def BRLoss.pr {K : ℕ} {A : Type*} (ℓ : BRLoss K A) : Simplex K → Fin K → ℝ :=
  fun p => ℓ.loss (ℓ.BR p)

/-- The discrete derivative of a loss vector: `Δ v = (v_y − v_0)_{y=0}^{K−1}`. Applied to
`v = ℓ(a, ·)` it is `Δℓ(a)` (§2.2), so `Δ_0 ℓ(a) = 0`. -/
def dLoss {K : ℕ} [NeZero K] (v : Fin K → ℝ) : Fin K → ℝ := fun y => v y - v 0

/-- The Bayes risk `L_ℓ(p') = min_{a ∈ A} E_{y∼p'} ℓ(a, y)` (§2.3), defined for every vector `p'`
as the infimum `⨅_a ⟨p', ℓ(a, ·)⟩` (bounded below by `−‖p'‖₁`; attained at `BR_ℓ(p')` on `Δ_K`). -/
noncomputable def bayesRisk {K : ℕ} {A : Type*} (loss : A → Fin K → ℝ) (p : Fin K → ℝ) : ℝ :=
  ⨅ a, dot p (loss a)

universe u

/-- `L_All` (§2, p. 19): all bounded decision losses admitting (measurable) best responses, on an
arbitrary action space `A` (any measurable space in the universe `u`). -/
structure AllLoss (K : ℕ) : Type (u + 1) where
  /-- the action space -/
  A : Type u
  /-- its measurable structure -/
  mA : MeasurableSpace A
  /-- the loss with its fixed best response -/
  ℓ : BRLoss K A
  /-- measurability of the loss and of the best response -/
  meas : @BRLoss.IsMeasurable K A mA ℓ

/-- `ℓ` is 1-Lipschitz in the action for the Euclidean norm:
`|ℓ(a, y) − ℓ(a', y)| ≤ ‖a − a'‖₂` for all `a, a' ∈ Δ_K`, `y ∈ Y`. -/
def IsLipLoss {K : ℕ} (loss : Simplex K → Fin K → ℝ) : Prop :=
  ∀ (a a' : Simplex K) (y : Fin K), |loss a y - loss a' y| ≤ l2 ((a : Fin K → ℝ) - (a' : Fin K → ℝ))

/-- `L_Lip` (§2, p. 19): `[−1, 1]`-valued losses on `Δ_K × Y`, 1-Lipschitz in the action for the
Euclidean norm, each with its fixed measurable best response. The set contains every pair
`(ℓ, BR_ℓ)`, so a bound over it is a bound for every choice of measurable best responses. -/
def LLip (K : ℕ) : Set (BRLoss K (Simplex K)) :=
  {ℓ | IsLipLoss ℓ.loss ∧ ℓ.IsMeasurable}

/-- `L_prop` (§2, p. 19): `[−1, 1]`-valued proper losses on `Δ_K × Y`,
`E_{y∼p} ℓ(p, y) ≤ E_{y∼p} ℓ(a, y)` for all `a, p ∈ Δ_K`, measurable in the action. -/
def LProp (K : ℕ) : Set (Simplex K → Fin K → ℝ) :=
  {loss | (∀ a y, |loss a y| ≤ 1) ∧
    (∀ p a : Simplex K, dot (p : Fin K → ℝ) (loss p) ≤ dot (p : Fin K → ℝ) (loss a)) ∧
    ∀ y, Measurable fun a => loss a y}

/-- Upper expectation bound: `E_μ[f] ≤ c` read as an upper integral, i.e. some integrable `g ≥ f`
has `∫ g dμ ≤ c` (for measurable integrable `f` this is `∫ f dμ ≤ c`). -/
def UpperExpLE {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (c : ℝ) : Prop :=
  ∃ g : Ω → ℝ, Integrable g μ ∧ (∀ ω, f ω ≤ g ω) ∧ ∫ ω, g ω ∂μ ≤ c

end

end MultiOmniRate.Lipschitz


