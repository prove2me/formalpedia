-- Prove2me | Definitions.Def_RestrictedAP_Counting_ProductFunctions
-- name    : RestrictedAP_Counting_ProductFunctions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:19:50.358965+00:00
-- url     : https://prove2.me/theorems/5975a396-557f-450b-94f9-fad49f42d9c3
-- title:
--   Product functions, order, $\mathrm{span}_{\mathbb N}$, symbolic distance, rank, softrank and the joint lifting
-- statement:
--   Let $\Sigma$ be a finite alphabet with a distinguished element $\sigma^\star$ and $\mathbb D=\{z\in\mathbb C:|z|=1\}$. A **product function** (Definition 2.1) is $P:\Sigma^n\to\mathbb D$ with $P(x)=\prod_{i=1}^nP_i(x_i)$, $P_i:\Sigma\to\mathbb D$; following §2.1 it is **normalized**: $P_i(\sigma^\star)=1$ for all $i$. The **projection** (Definition 2.2) is $P|_I(x)=\prod_{i\in I}P_i(x_i)$ and $\mathcal P|_I=\{P|_I:P\in\mathcal P\}$. The **order** $\mathrm{ord}(P)$ (Definition 2.3) is the least $k\ge1$ with $P^k\equiv1$ ($\infty$ if none); $P$ is **cyclic** if $\mathrm{ord}(P)=p^r$ for a prime $p$ and an integer $r\ge0$, and **$M$-discrete** if $\mathrm{ord}(P)\le M$ (Definition 2.4). For a collection $\mathcal P$, $\mathrm{span}_{\mathbb N}(\mathcal P)=\{\prod_{P\in\mathcal P}P^{\alpha_P}:\alpha_P\in\mathbb N\}$ (Definition 2.8).
--
--   The **symbolic distance** $\Delta_{\rm symbolic}(P,P')$ (Definition 2.9) is the smallest $k$ such that $P=\prod_iu_i(x_i)$ and $P'=\prod_iu'_i(x_i)$ with $u_i,u'_i:\Sigma\to\mathbb D$ and $u_i=u'_i$ for all but $k$ indices $i$; $\Delta_{\rm symbolic}(P,\mathrm{span}_{\mathbb N}(\mathcal P))=\min_{Q\in\mathrm{span}_{\mathbb N}(\mathcal P)}\Delta_{\rm symbolic}(P,Q)$ (Definition 2.10). $\mathcal P$ has **rank** $\mathrm{rk}(\mathcal P)\ge D$ (Definition 2.13) if for all integers $0\le\alpha_P<\mathrm{ord}(P)$, not all zero, $S=\prod_PP^{\alpha_P}$ has $\Delta_{\rm symbolic}(S,1)\ge D$; it has **soft-rank** $\mathrm{softrk}(\mathcal P)\ge D$ (Definition 2.14) if for all integers $\alpha_P$, $S=\prod_PP^{\alpha_P}$ is constant or $\Delta_{\rm symbolic}(S,1)\ge D$. For $\mu$ on $\Sigma\times\Gamma\times\Phi$ the **joint lifting** $D_\mu(\mathcal P,\mathcal Q,\mathcal R)$ (Definition 2.15) is the collection of functions on $\mathrm{supp}(\mu)^n$ consisting of $(x,y,z)\mapsto P(x)$, $Q(y)$, $R(z)$ for $P\in\mathcal P$, $Q\in\mathcal Q$, $R\in\mathcal R$, and $\mathrm{softrk}_\mu(\mathcal P)=\mathrm{softrk}(D_\mu(\mathcal P,\mathcal P,\mathcal P))$ (Definition 2.16).
--
--   **Formalization Note.** Functions $\Sigma^n\to\mathbb D$ are typed `(Fin n → Σ) → ℂ`, the modulus condition being part of `IsProductFunction σs P`. A collection is a `Finset`. `orderOf P` is $\mathrm{ord}(P)$ with $0$ encoding $\infty$. The normalized factor $P_i(a)$ is `component σs P i a` $=P(\sigma^\star,\dots,a,\dots,\sigma^\star)$. `symbolicDist` and `distToSpan` are natural-number infima; they are genuine minima whenever their arguments are product functions (every use), and the junk value $0$ otherwise. Rank and softrank thresholds are real numbers. $\mathrm{supp}(\mu)$ is the subtype `{t // μ t ≠ 0}`.
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), pp. 7–11, Definitions 2.1–2.4, 2.8–2.10, 2.13–2.16

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions

namespace RestrictedAP.Counting

/-!
# Product functions, order, span, symbolic distance, rank and softrank

Bhangale, Khot, Liu, Minzer, *A Counting Lemma for Somewhat Restricted 3-APs*,
arXiv:2608.17365 (copy sha256 de0b96c1…), pp. 7–11, Definitions 2.1–2.4, 2.8–2.10, 2.13–2.16.

* `D` is the unit circle of `ℂ`; functions `Σ^n → D` are typed `(Fin n → Ω) → ℂ` and the
  value constraint `‖·‖ = 1` is part of `IsProductFunction`.
* **Normalization (§2.1, p. 7).** "We fix a distinguished element `σ⋆ ∈ Σ`, and by default
  normalize so that `P(σ⋆,…,σ⋆) = 1` and `P_1(σ⋆) = … = P_n(σ⋆) = 1`. Unless specified
  otherwise, throughout this paper we will consider normalized product functions."
  `IsProductFunction σs P` says that `P` has such a normalized decomposition. The normalized
  decomposition is unique, and its `i`-th factor is `component σs P i a = P(σ⋆,…,a,…,σ⋆)`
  (`a` in position `i`); the projection `P|_I` of Definition 2.2 is `proj σs I P`.
* `ord(P)` (Definition 2.3) is `orderOf P` in the monoid of functions, with `orderOf P = 0`
  encoding `ord(P) = ∞`. Cyclic: `ord(P) = p^r`, `p` prime, `r ≥ 0`. `M`-discrete:
  `ord(P) ≤ M`, `ord(P)` finite.
* A collection of product functions is a `Finset` of functions; `|PP|` is its card.
* `symbolicDist P Q` (Definition 2.9) is the least `k` for which `P` and `Q` have product
  decompositions with factors in `D` that differ in at most `k` coordinates. It is an infimum
  over a set of naturals that is nonempty whenever `P` and `Q` are both product functions
  (every use below); on non-product functions the set is empty and the value is the junk `0`.
* `RankAtLeast PP D` is `rk(PP) ≥ D` (Definition 2.13); `SoftRankAtLeast PP D` is
  `softrk(PP) ≥ D` (Definition 2.14). Thresholds are real; symbolic distances are compared
  after casting to `ℝ`.
* `jointLift μ PP QQ RR` is `D_μ(PP, QQ, RR)` (Definition 2.15): functions on `supp(μ)^n`, where
  `supp(μ)` is the subtype `{t // μ t ≠ 0}`; `SoftRankMuAtLeast μ PP D` is
  `softrk_μ(PP) ≥ D` (Definition 2.16).
-/

open Classical

/-- `P : Σ^n → D` is a product function normalized at `σ⋆ = σs` (Definition 2.1 with the §2.1
normalization): `P(x) = ∏_i u_i(x_i)` with `|u_i| = 1` and `u_i(σ⋆) = 1` for every `i`. -/
def IsProductFunction {Ω : Type*} {n : ℕ} (σs : Ω) (P : (Fin n → Ω) → ℂ) : Prop :=
  ∃ u : Fin n → Ω → ℂ, (∀ i a, ‖u i a‖ = 1) ∧ (∀ i, u i σs = 1) ∧
    ∀ x, P x = ∏ i, u i (x i)

/-- The `i`-th factor of the normalized decomposition: `P(σ⋆,…,σ⋆,a,σ⋆,…,σ⋆)`. -/
def component {Ω : Type*} [DecidableEq Ω] {n : ℕ} (σs : Ω) (P : (Fin n → Ω) → ℂ)
    (i : Fin n) (a : Ω) : ℂ :=
  P (Function.update (fun _ => σs) i a)

/-- The projection `P|_I(x) = ∏_{i ∈ I} P_i(x_i)` (Definition 2.2), using the normalized
decomposition. -/
noncomputable def proj {Ω : Type*} [DecidableEq Ω] {n : ℕ} (σs : Ω) (I : Finset (Fin n))
    (P : (Fin n → Ω) → ℂ) : (Fin n → Ω) → ℂ :=
  fun x => ∏ i ∈ I, component σs P i (x i)

/-- The projected collection `PP|_I = {P|_I : P ∈ PP}` (Definition 2.2). -/
noncomputable def projColl {Ω : Type*} [DecidableEq Ω] {n : ℕ} (σs : Ω) (I : Finset (Fin n))
    (PP : Finset ((Fin n → Ω) → ℂ)) : Finset ((Fin n → Ω) → ℂ) :=
  PP.image (proj σs I)

/-- `P` is cyclic (Definition 2.4): `ord(P) = p^r` for a prime `p` and an integer `r ≥ 0`. -/
def IsCyclic {Ω : Type*} {n : ℕ} (P : (Fin n → Ω) → ℂ) : Prop :=
  ∃ p r : ℕ, p.Prime ∧ orderOf P = p ^ r

/-- `P` is `M`-discrete (Definition 2.4): `ord(P) ≤ M` (in particular `ord(P) < ∞`). -/
def IsDiscrete {Ω : Type*} {n : ℕ} (M : ℕ) (P : (Fin n → Ω) → ℂ) : Prop :=
  0 < orderOf P ∧ orderOf P ≤ M

/-- `span_ℕ(PP) = {∏_{P ∈ PP} P^{α_P} : α_P ∈ ℕ}` (Definition 2.8). -/
def spanN {Ω : Type*} {n : ℕ} (PP : Finset ((Fin n → Ω) → ℂ)) : Set ((Fin n → Ω) → ℂ) :=
  {Q | ∃ a : ((Fin n → Ω) → ℂ) → ℕ, Q = ∏ P ∈ PP, P ^ a P}

/-- `Δ_symbolic(P, Q)` (Definition 2.9): the least `k` such that `P = ∏ u_i(x_i)` and
`Q = ∏ u'_i(x_i)` with `u_i, u'_i : Ω → D` and `u_i = u'_i` for all but `k` coordinates. -/
noncomputable def symbolicDist {Ω : Type*} {n : ℕ} (P Q : (Fin n → Ω) → ℂ) : ℕ :=
  sInf {k | ∃ u v : Fin n → Ω → ℂ, (∀ i a, ‖u i a‖ = 1) ∧ (∀ i a, ‖v i a‖ = 1) ∧
    (∀ x, P x = ∏ i, u i (x i)) ∧ (∀ x, Q x = ∏ i, v i (x i)) ∧
    (Finset.univ.filter (fun i => u i ≠ v i)).card = k}

/-- `Δ_symbolic(P, span_ℕ(PP)) = min_{Q ∈ span_ℕ(PP)} Δ_symbolic(P, Q)` (Definition 2.10). -/
noncomputable def distToSpan {Ω : Type*} {n : ℕ} (P : (Fin n → Ω) → ℂ)
    (PP : Finset ((Fin n → Ω) → ℂ)) : ℕ :=
  sInf ((fun Q => symbolicDist P Q) '' spanN PP)

/-- `rk(PP) ≥ D` (Definition 2.13): for all integers `0 ≤ α_P < ord(P)` (any `α_P ≥ 0` when
`ord(P) = ∞`), not all zero, `S = ∏ P^{α_P}` has `Δ_symbolic(S, 1) ≥ D`. -/
def RankAtLeast {Ω : Type*} {n : ℕ} (PP : Finset ((Fin n → Ω) → ℂ)) (D : ℝ) : Prop :=
  ∀ a : ((Fin n → Ω) → ℂ) → ℕ,
    (∀ P ∈ PP, orderOf P = 0 ∨ a P < orderOf P) → (∃ P ∈ PP, a P ≠ 0) →
      D ≤ (symbolicDist (∏ P ∈ PP, P ^ a P) 1 : ℝ)

/-- `softrk(PP) ≥ D` (Definition 2.14): for all integers `α_P`, `S(x) = ∏ P(x)^{α_P}` is
constant or has `Δ_symbolic(S, 1) ≥ D`. -/
def SoftRankAtLeast {Ω : Type*} {n : ℕ} (PP : Finset ((Fin n → Ω) → ℂ)) (D : ℝ) : Prop :=
  ∀ a : ((Fin n → Ω) → ℂ) → ℤ,
    (∃ c : ℂ, ∀ x, (∏ P ∈ PP, (P x) ^ (a P)) = c) ∨
      D ≤ (symbolicDist (fun x => ∏ P ∈ PP, (P x) ^ (a P)) 1 : ℝ)

/-- The lift `P'(x, y, z) = P(x)` of `P : Sig^n → D` to `supp(μ)^n` (Definition 2.15). -/
def lift1 {Sig Γ Φ : Type*} {n : ℕ} (μ : Sig × Γ × Φ → ℝ) (P : (Fin n → Sig) → ℂ) :
    (Fin n → {t // μ t ≠ 0}) → ℂ :=
  fun t => P (fun i => (t i).1.1)

/-- The lift `Q'(x, y, z) = Q(y)` (Definition 2.15). -/
def lift2 {Sig Γ Φ : Type*} {n : ℕ} (μ : Sig × Γ × Φ → ℝ) (Q : (Fin n → Γ) → ℂ) :
    (Fin n → {t // μ t ≠ 0}) → ℂ :=
  fun t => Q (fun i => (t i).1.2.1)

/-- The lift `R'(x, y, z) = R(z)` (Definition 2.15). -/
def lift3 {Sig Γ Φ : Type*} {n : ℕ} (μ : Sig × Γ × Φ → ℝ) (R : (Fin n → Φ) → ℂ) :
    (Fin n → {t // μ t ≠ 0}) → ℂ :=
  fun t => R (fun i => (t i).1.2.2)

/-- The joint lifting `D_μ(PP, QQ, RR)` of Definition 2.15: a collection of product functions over
`supp(μ)^n`. -/
noncomputable def jointLift {Sig Γ Φ : Type*} {n : ℕ} (μ : Sig × Γ × Φ → ℝ)
    (PP : Finset ((Fin n → Sig) → ℂ)) (QQ : Finset ((Fin n → Γ) → ℂ))
    (RR : Finset ((Fin n → Φ) → ℂ)) : Finset ((Fin n → {t // μ t ≠ 0}) → ℂ) :=
  PP.image (lift1 μ) ∪ QQ.image (lift2 μ) ∪ RR.image (lift3 μ)

/-- `softrk_μ(PP) ≥ D`, i.e. `softrk(D_μ(PP, PP, PP)) ≥ D` (Definition 2.16). -/
def SoftRankMuAtLeast {Sig : Type*} {n : ℕ} (μ : Sig × Sig × Sig → ℝ)
    (PP : Finset ((Fin n → Sig) → ℂ)) (D : ℝ) : Prop :=
  SoftRankAtLeast (jointLift μ PP PP PP) D

end RestrictedAP.Counting


