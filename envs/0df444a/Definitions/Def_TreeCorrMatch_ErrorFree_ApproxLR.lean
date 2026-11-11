-- Prove2me | Definitions.Def_TreeCorrMatch_ErrorFree_ApproxLR
-- name    : TreeCorrMatch_ErrorFree_ApproxLR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:24:55.844859+00:00
-- url     : https://prove2.me/theorems/bc3f9855-6827-4d51-8e2e-cf90a6e0b170
-- title:
--   Randomized permanent approximators meeting guarantee (15), and the algorithm ApproxLR
-- statement:
--   A **randomized permanent approximator** is a function $\mathrm{App}(m,A,\delta,\eta;\omega)$ of an $m\times m$ real matrix $A$, an accuracy $\delta$, a failure probability $\eta$ and a random seed $\omega$ drawn from a probability space $(\Omega_0,\mu_0)$ (Remark 1: the algorithm is a deterministic function of its random bits). It **meets guarantee (15)** if for every entrywise nonnegative $A$ and all $\delta,\eta\in(0,\tfrac12)$ the output is a measurable, nonnegative function of the seed and
--
--   $$\mu_0\big((1-\delta)\,\mathrm{per}(A)\le \mathrm{App}(A,\delta,\eta)\le(1+\delta)\,\mathrm{per}(A)\big)\ge 1-\eta .$$
--
--   **ApproxLR** (§4.1, Algorithm 2). Input: trees $t,\tilde t$ of depth at most $d$, $\lambda>0$, $s\in(0,1]$, $\xi\in(0,\tfrac12)$, $d\ge0$. Step 1 computes once for the pair
--
--   $$D=\max\{2,\max_u|\mathrm{Ch}_t(u)|,\max_{\tilde v}|\mathrm{Ch}_{\tilde t}(\tilde v)|\},\qquad \delta=\frac1{64D^d},\qquad \eta=\frac{\xi}{(D+1)\sum_{j=0}^dD^{2j}} .$$
--
--   Step 2 sets $\hat\ell(u,\tilde v)=1$ for vertices at depth $d$. Step 3, for $h=1,\dots,d$ and vertices $u,\tilde v$ at depth $d-h$ with children $y_1,\dots,y_c$ and $\tilde y_1,\dots,\tilde y_{\tilde c}$, forms $\hat Z_{ij}=\frac s\lambda\hat\ell(y_i,\tilde y_j)$, sets $\hat S_0=1$ and $\hat S_q=\mathrm{App}(A_q(\hat Z),\delta,\eta)/((c-q)!(\tilde c-q)!)$ for $1\le q\le\min\{c,\tilde c\}$, and
--
--   $$\hat\ell(u,\tilde v)=e^{\lambda s}\sum_{q=0}^{\min\{c,\tilde c\}}(1-s)^{c+\tilde c-2q}\,\hat S_q(u,\tilde v)\qquad(0^0=1).$$
--
--   Step 4 outputs $\hat L_d(t,\tilde t)=\hat\ell(\rho,\tilde\rho)$ at the roots. Each call of the approximator uses its own seed.
--
--   **Formalization Note** Trees are ordered, and children are enumerated in list order. A vertex is identified by its position (the list of child indices from the root); the call for the vertex pair at positions $(p,\tilde p)$ and index $q$ uses the seed $\omega(p,\tilde p,q)$, so that distinct calls get distinct seeds. `lhat` is indexed by the remaining height $h$ (the paper's loop index), `zhat` is $\hat Z$ (17) and `shat` is $\hat S_q$ (18).
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 10, Lemma 3, eq. (15) and Remark 1; p. 11, §4.1 Steps 1–4 and eqs. (16)–(19) (PDF pp. 12–13); Algorithm 2, p. 32 (PDF p. 34)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_RootedTree
import Definitions.Def_TreeCorrMatch_ErrorFree_MatchingSum

/-!
Randomized permanent approximators meeting the guarantee (15) of Lemma 3, and the likelihood-ratio
approximation algorithm `ApproxLR` (§4.1, Algorithm 2).

Cheng, Wang, Ying, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), Lemma 3 and Remark 1, p. 10;
§4.1 Steps 1–4 and (16)–(19), p. 11; Algorithm 2, p. 32.
-/

namespace TreeCorrMatch.ErrorFree

open MeasureTheory

/-- A randomized permanent approximator: a deterministic function `App m A δ η ω` of an `m × m`
matrix `A`, the accuracy `δ`, the failure probability `η` and a random seed `ω` (Remark 1). -/
abbrev PermApprox (Ω₀ : Type) : Type := (m : ℕ) → Matrix (Fin m) (Fin m) ℝ → ℝ → ℝ → Ω₀ → ℝ

/-- The guarantee of Lemma 3 / (15): for every entrywise nonnegative square matrix `A` and
`δ, η ∈ (0, 1/2)`, the output is a nonnegative random variable of the seed `ω ∼ μ₀`, and
`P((1 - δ) per(A) ≤ App(A, δ, η) ≤ (1 + δ) per(A)) ≥ 1 - η`. -/
def IsPermApprox {Ω₀ : Type} [MeasurableSpace Ω₀] (μ₀ : Measure Ω₀) (App : PermApprox Ω₀) :
    Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ), (∀ i j, 0 ≤ A i j) →
    ∀ δ η : ℝ, 0 < δ → δ < 1 / 2 → 0 < η → η < 1 / 2 →
      Measurable (App m A δ η) ∧ (∀ ω, 0 ≤ App m A δ η ω) ∧
        1 - η ≤ (μ₀ {ω | (1 - δ) * A.permanent ≤ App m A δ η ω ∧
                          App m A δ η ω ≤ (1 + δ) * A.permanent}).toReal

/-- Index of one `ApproxPer` call inside one execution of `ApproxLR`: the positions (child-index
paths from the root) of the vertex pair `(u, ṽ)` in the two trees, and `q`. Each call has its own
seed, so the calls use independent random bits (Remark 1). -/
abbrev SeedIdx : Type := List ℕ × List ℕ × ℕ

/-- The matrix (17) at the vertex pair `(u, ṽ)` with positions `(p, p̃)`:
`Ẑ(u, ṽ)_{ij} = (s/λ) ℓ̂(y_i, ỹ_j)`, children enumerated in list order; `f` gives the values `ℓ̂`
one level below. -/
noncomputable def zhat (lam s : ℝ) (f : List ℕ → List ℕ → OTree → OTree → ℝ) (p p' : List ℕ)
    (u u' : OTree) : Matrix (Fin u.children.length) (Fin u'.children.length) ℝ :=
  fun i j => s / lam * f (p ++ [i.val]) (p' ++ [j.val]) (u.children.get i) (u'.children.get j)

/-- The value (18): `Ŝ_0 = 1` and, for `q ≥ 1`,
`Ŝ_q(u, ṽ) = ApproxPer(A_q(Ẑ(u, ṽ)), δ, η) / ((c - q)! (c̃ - q)!)`, the call indexed by `(p, p̃, q)`. -/
noncomputable def shat {Ω₀ : Type} (App : PermApprox Ω₀) (δ η : ℝ) (ω : SeedIdx → Ω₀)
    (p p' : List ℕ) {c c' : ℕ} (Z : Matrix (Fin c) (Fin c') ℝ) (q : ℕ) : ℝ :=
  if q = 0 then 1
  else App (c + c' - q) (augMatrix Z q) δ η (ω (p, p', q)) /
    ((c - q).factorial * (c' - q).factorial : ℝ)

/-- The values `ℓ̂` of Step 2–3: `ℓ̂ = 1` at remaining height `0`, and at remaining height `h + 1`,
(19): `ℓ̂(u, ṽ) = e^{λs} ∑_{q=0}^{min{c, c̃}} (1 - s)^{c + c̃ - 2q} Ŝ_q(u, ṽ)` (with `0^0 = 1`). -/
noncomputable def lhat {Ω₀ : Type} (App : PermApprox Ω₀) (lam s δ η : ℝ) (ω : SeedIdx → Ω₀) :
    ℕ → List ℕ → List ℕ → OTree → OTree → ℝ
  | 0, _, _, _, _ => 1
  | h + 1, p, p', u, u' =>
    Real.exp (lam * s) *
      ∑ q ∈ Finset.range (min u.children.length u'.children.length + 1),
        (1 - s) ^ (u.children.length + u'.children.length - 2 * q) *
          shat App δ η ω p p' (zhat lam s (lhat App lam s δ η ω h) p p' u u') q

/-- `D = max{2, max_u |Ch_t(u)|, max_ṽ |Ch_t̃(ṽ)|}` of (16). -/
def alrD (t t' : OTree) : ℕ := max 2 (max t.maxChildren t'.maxChildren)

/-- `δ = 1 / (64 D^d)` of (16). -/
noncomputable def alrDelta (d : ℕ) (t t' : OTree) : ℝ := 1 / (64 * (alrD t t' : ℝ) ^ d)

/-- `η = ξ / ((D + 1) ∑_{j=0}^d D^{2j})` of (16). -/
noncomputable def alrEta (ξ : ℝ) (d : ℕ) (t t' : OTree) : ℝ :=
  ξ / (((alrD t t' : ℝ) + 1) * ∑ j ∈ Finset.range (d + 1), (alrD t t' : ℝ) ^ (2 * j))

/-- `ApproxLR(t, t̃, λ, s, ξ, d)` (Algorithm 2) with seeds `ω`: `L̂_d(t, t̃) = ℓ̂(ρ, ρ̃)`, computed
with `D, δ, η` fixed once for the input pair (Step 1). -/
noncomputable def approxLR {Ω₀ : Type} (App : PermApprox Ω₀) (lam s ξ : ℝ) (d : ℕ) (t t' : OTree)
    (ω : SeedIdx → Ω₀) : ℝ :=
  lhat App lam s (alrDelta d t t') (alrEta ξ d t t') ω d [] [] t t'

end TreeCorrMatch.ErrorFree


