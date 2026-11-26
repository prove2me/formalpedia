-- Prove2me | Definitions.Def_TwoStageMatch_Supplement_Pricing
-- name    : TwoStageMatch_Supplement_Pricing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:09:45.382833+00:00
-- url     : https://prove2.me/theorems/cc843450-dc3b-4642-bb0b-9314bb86f124
-- title:
--   Joint matching and pricing: instances, $w_i(p)$, $T_i(q)$, policies, market efficiency and $\mathrm{OPT}_{\text{offline-MP}}$
-- statement:
--   An instance of **two-stage stochastic joint matching and pricing** consists of a bipartite graph between demands $D_1\cup D_2$ and supplies $S$, supply weights $w_j\ge0$, the contributions $\hat w_i=w_i(p_i)\ge0$ of first-stage demands (which have already accepted their prices $p_i$), and for each $i\in D_2$ a value law $F_i$ on $[0,\infty)$; the values $v_i\sim F_i$ are independent. The instance is **regular** when every $F_i$ is atomless and has a finite mean.
--
--   1. $w_i(p)=\mathbb E_{v\sim F_i}[v\mid v\ge p]$ and the threshold $T_i(q)=\max\{t:1-F_i(t)\ge q\}$ (a supremum in general; attained for atomless $F_i$ and $q\in(0,1]$).
--   2. A deterministic policy picks a first-stage matching $M_1$ of $G[D_1,S]$, prices $p_i$ for $i\in D_2$, and a rule giving the second-stage matching $M_2$ between the accepting set $\tilde D_2=\{i:v_i\ge p_i\}$ and the supplies left by $M_1$.
--   3. Its market efficiency is $\mathbb E[\mathrm{OBJ}_{D_1\cup D_2}+\mathrm{OBJ}_S]$ with
--   $$\mathrm{OBJ}_{D_1\cup D_2}=\sum_{i\in D_1}\hat w_i\mathbb 1\{i\text{ matched by }M_1\}+\sum_{i\in D_2}v_i\mathbb 1\{v_i\ge p_i,\ i\text{ matched by }M_2\},\qquad \mathrm{OBJ}_S=\sum_{j\in S}w_j\mathbb 1\{j\text{ matched in }M_1\cup M_2\}.$$
--   4. $\mathrm{OPT}_{\text{offline-MP}}=\mathbb E_v[\text{Max-WeightMatch}^{\hat w}(D,S)]$ with vertex weights $\hat w_i$ on $D_1$, $v_i$ on $D_2$ and $w_j$ on $S$ (eq. (3)).
--
--   These are the objects of Lemma 4, Theorem 4 and Theorem EC.4.
--
--   **Formalization Note** Only $\hat w_i$ of a first-stage demand enters the problem, so it is recorded directly. A randomized policy is a mixture of deterministic ones, independent of the values. Lean's $0/0=0$ makes $w_i(p)=0$ for a price accepted with probability $0$.
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, §2 (ii), pp.8, 10–11, Definition 3 and eq. (3), p.11; §5.1, p.25

import Mathlib
import Definitions.Def_TwoStageMatch_Instance

open Finset MeasureTheory

namespace TwoStageMatch.Supplement

/-!
# Two-stage stochastic joint matching and pricing: instances, policies, `OPT_offline-MP`

Feng, Niazadeh & Saberi, arXiv:2210.11648v1, §2 (ii), pp.8 and 10–11: the values `v_i ∼ F_i`,
`w_i(p) ≜ 𝔼_{v∼F_i}[v | v ≥ p]`, market efficiency `OBJ_{D₁∪D₂} + OBJ_S` (Definition 3, p.11) and
the benchmark `OPT_offline-MP` of eq. (3), p.11; the threshold `T_i(q)` of §5.1, p.25.

**Formalization Note.**
* Demands are `D₁ ⊕ D₂`, as in `TwoStageMatch.Instance`. A first-stage demand `i ∈ D₁` has already
  accepted her price `p_i`; only her contribution `ŵ_i = w_i(p_i)` enters the problem, so the
  instance records `ŵ_i ≥ 0` directly (every such value is `w_i(p_i)` for some law and price, e.g.
  a point mass at `ŵ_i`).
* A second-stage demand `i ∈ D₂` has a value law `F_i`, a probability measure on `ℝ` carried by
  `[0, ∞)` (values of a service are non-negative); the values are independent, with joint law
  `Π_i F_i` on `D₂ → ℝ`. `MPInstance.Regular` adds that every `F_i` is atomless and has a finite
  mean, the premise under which the threshold `T_i` and the claim "accepts price `T_i(y)` with
  probability `y`" of §5 make sense.
* `w_i(p) = (∫_{[p,∞)} v dF_i) / F_i([p, ∞))` (Lean gives `0` when `F_i([p,∞)) = 0`, a price that
  is accepted with probability `0`). `T_i(q) = sup {t : 1 − F_i(t) ≥ q}` with `1 − F_i(t) =
  F_i((t, ∞))`; for an atomless law and `q ∈ (0, 1]` the supremum is attained, so it is the
  paper's `argmax`.
* A deterministic policy picks a first-stage matching `M₁` of `G[D₁, S]`, prices `p_i` for
  `i ∈ D₂`, and a rule giving the second-stage matching `M₂` between the accepting set
  `D̃₂ = {i : v_i ≥ p_i}` and the supplies left by `M₁` as a function of `D̃₂` (the platform sees
  who accepted, not the values). A randomized policy is a mixture of deterministic ones,
  independent of the values.
* The vertex-weighted weight of a matching is `Σ_{(i,j) ∈ M} (ŵ_i + ŵ_j)`.
-/

variable {D₁ D₂ S : Type*}

/-- An instance of the two-stage stochastic joint matching and pricing problem (§2 (ii)). -/
structure MPInstance (D₁ D₂ S : Type*) where
  /-- the edge relation `E` of `G = (D₁ ∪ D₂, S, E)` -/
  E : D₁ ⊕ D₂ → S → Prop
  /-- the supply weights `w_j` -/
  w : S → ℝ
  /-- the contribution `ŵ_i = w_i(p_i)` of a first-stage demand that accepted her price `p_i` -/
  ŵ₁ : D₁ → ℝ
  /-- the value law `F_i` of a second-stage demand -/
  F : D₂ → ProbabilityMeasure ℝ
  w_nonneg : ∀ j, 0 ≤ w j
  ŵ₁_nonneg : ∀ i, 0 ≤ ŵ₁ i
  F_nonneg : ∀ i, (F i : Measure ℝ) (Set.Iio 0) = 0

/-- The premise of §5 (Lemma 4, Theorem 4, Theorem EC.4): every second-stage value law is atomless
and has a finite mean. -/
def MPInstance.Regular (I : MPInstance D₁ D₂ S) : Prop :=
  ∀ i, NullSingletonClass (I.F i : Measure ℝ) ∧ Integrable (fun v : ℝ => v) (I.F i : Measure ℝ)

/-- `w_i(p) ≜ 𝔼_{v ∼ F_i}[v | v ≥ p]` (p.10). -/
noncomputable def condMean (μ : Measure ℝ) (p : ℝ) : ℝ :=
  (∫ v in Set.Ici p, v ∂μ) / (μ (Set.Ici p)).toReal

/-- The threshold `T_i(q) ≜ argmax {t : 1 − F_i(t) ≥ q}` (§5.1, p.25), as a supremum. -/
noncomputable def threshold (μ : Measure ℝ) (q : ℝ) : ℝ :=
  sSup {t : ℝ | q ≤ (μ (Set.Ioi t)).toReal}

/-- The joint law `Π_{i ∈ D₂} F_i` of the independent second-stage values. -/
noncomputable def valueLaw [Fintype D₂] (I : MPInstance D₁ D₂ S) : Measure (D₂ → ℝ) :=
  Measure.pi fun i => (I.F i : Measure ℝ)

/-- The vertex-weighted weight `Σ_{(i,j) ∈ M} (ŵ_i + ŵ_j)` of a matching `M`, for demand weights
`dw` and supply weights `sw`. -/
def vwWeight {U V : Type*} (dw : U → ℝ) (sw : V → ℝ) (M : Finset (U × V)) : ℝ :=
  ∑ e ∈ M, (dw e.1 + sw e.2)

/-- `Max-WeightMatch^ŵ(X, Y)`: the weight of a vertex-weighted maximum matching between `X` and
`Y` (p.11). -/
noncomputable def maxVWMatch {U V : Type*} [Fintype U] [Fintype V] (E : U → V → Prop)
    (dw : U → ℝ) (sw : V → ℝ) (X : Finset U) (Y : Finset V) : ℝ :=
  (matchings E X Y).sup' (matchings_nonempty E X Y) (vwWeight dw sw)

/-- The demand weights `ŵ_i = w_i(p_i)` on `D₁` and `ŵ_i = v_i` on `D₂`, for a value vector `v`. -/
def offlineWeight (I : MPInstance D₁ D₂ S) (v : D₂ → ℝ) : D₁ ⊕ D₂ → ℝ :=
  Sum.elim I.ŵ₁ v

/-- `OPT_offline-MP ≜ 𝔼_{v_i ∼ F_i, i ∈ D₂}[Max-WeightMatch^ŵ(D, S)]`, eq. (3), p.11. -/
noncomputable def optOfflineMP [Fintype D₁] [Fintype D₂] [Fintype S]
    (I : MPInstance D₁ D₂ S) : ℝ :=
  ∫ v, maxVWMatch I.E (offlineWeight I v) I.w Finset.univ Finset.univ ∂(valueLaw I)

/-- The accepting set `D̃₂ = {i ∈ D₂ : v_i ≥ p_i}`. -/
noncomputable def acceptSet [Fintype D₂] (p v : D₂ → ℝ) : Finset D₂ :=
  open Classical in Finset.univ.filter fun i => p i ≤ v i

/-- The realized market efficiency `OBJ_{D₁∪D₂} + OBJ_S` (Definition 3, p.11) of first-stage
matching `M₁`, prices `p`, second-stage rule `M₂` and values `v`:
`Σ_{i ∈ D₁} w_i(p_i) 𝟙{i matched by M₁} + Σ_{i ∈ D₂} v_i 𝟙{v_i ≥ p_i, i matched by M₂}
 + Σ_{j ∈ S} w_j 𝟙{j matched in M₁ ∪ M₂}`, where `M₂ = M₂(D̃₂)`. -/
noncomputable def marketEff [Fintype D₂] [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]
    (I : MPInstance D₁ D₂ S) (M₁ : Finset ((D₁ ⊕ D₂) × S))
    (M₂ : Finset D₂ → Finset ((D₁ ⊕ D₂) × S)) (p v : D₂ → ℝ) : ℝ :=
  ∑ e ∈ M₁, Sum.elim I.ŵ₁ (fun _ => 0) e.1 +
    ∑ e ∈ M₂ (acceptSet p v), Sum.elim (fun _ => 0) v e.1 +
    weight I.w (M₁ ∪ M₂ (acceptSet p v))

/-- A deterministic matching/pricing policy on the instance `I`. -/
structure DetPolicy [Fintype D₁] [Fintype S] [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]
    (I : MPInstance D₁ D₂ S) where
  /-- the first-stage matching, a matching of `G[D₁, S]` -/
  M₁ : Finset ((D₁ ⊕ D₂) × S)
  M₁_matching : IsMatching I.E firstStage Finset.univ M₁
  /-- the prices offered to the second-stage demands -/
  p : D₂ → ℝ
  /-- the second-stage matching as a function of the accepting set -/
  M₂ : Finset D₂ → Finset ((D₁ ⊕ D₂) × S)
  M₂_matching : ∀ A, IsMatching I.E (secondStage A) (Finset.univ \ matchedSupply M₁) (M₂ A)

/-- The expected market efficiency `𝔼_v[OBJ_{D₁∪D₂} + OBJ_S]` of a deterministic policy. -/
noncomputable def DetPolicy.efficiency [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁]
    [DecidableEq D₂] [DecidableEq S] {I : MPInstance D₁ D₂ S} (π : DetPolicy I) : ℝ :=
  ∫ v, marketEff I π.M₁ π.M₂ π.p v ∂(valueLaw I)

end TwoStageMatch.Supplement


