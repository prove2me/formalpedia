-- Prove2me | Definitions.Def_WalkTreeCluster_Laws
-- name    : WalkTreeCluster_Laws
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:52.713962+00:00
-- url     : https://prove2.me/theorems/2b2f7ea0-80da-41d3-8dba-8cda0c08a755
-- title:
--   The laws of $X_{u,i}$, $\mathrm{Keep}(u,i)$ and $X^{\rm keep}_{u,i}$ (Algorithms 1–5)
-- statement:
--   For a vertex $u$ and a stage $i$, $X_{u,i}\in\mathbb R^{\{L,H\}^i\times V}$ is the matrix of the walk tree $\mathcal T(u,i)$ (Definition 2.6) and $\mathrm{Keep}(u,i)$ its retention value (Algorithm 5). Their laws are defined by recursion on $i$, exactly as Algorithms 1–5 sample them:
--
--   1. $X_{u,0}=\mathbb 1_u$ (one row) and $\mathrm{Keep}(u,0)=1$.
--   2. For $i\ge1$, $X_{u,i}=\frac1q\sum_{\ell=1}^qZ_\ell$ for $q$ independent children. A child (Algorithm 2) takes, with probability $1-a$, the low-pass term: one walk block, then $Z=\frac{1}{1-a}\kappa\,(X\oplus0)$ with a fresh $X\sim X_{v,i-1}$ from the block's endpoint $v$; with probability $a/2$ the high-pass identity term $Z=\frac2a(0\oplus X)$, $X\sim X_{u,i-1}$; with probability $a/2$ a negative high-pass term: $s\ge1$ with probability $d_s$, $2s$ walk blocks, and $Z=-\frac2a\kappa_1\cdots\kappa_{2s}(0\oplus X)$ with $X\sim X_{v_{2s},i-1}$.
--   3. A walk block from $z$ (Algorithm 1) is discounted with probability $\delta$, and the child then contributes zero; otherwise it moves to $v$ with probability $(M^t)_{vz}$ and draws $\kappa\sim\mathrm{Keep}(v,i-1)$.
--   4. For $i\ge1$, $\mathrm{Keep}(u,i)=\kappa\,\tau_u(i)$ with $\kappa\sim\mathrm{Keep}(u,i-1)$ and
--   $$\tau_u(i)=\Big(1+\frac{64\alpha^{2i}}{B}\sum_{\ell=1}^B\langle X_\ell,X'_\ell\rangle_w^2\Big)^{-1/4}$$
--   for $2B$ independent copies $X_\ell,X'_\ell$ of $X_{u,i}$ (Eq. (20)).
--
--   All draws are independent. $X^{\rm keep}_{u,i}=\kappa X_{u,i}$ with an independent $\kappa\sim\mathrm{Keep}(u,i)$ (Definition 2.9). The joint law of the $2B$ samples of $\tau_u(i)$ is also recorded.
--
--   **Formalization Note.** A discounted block is represented by the zero matrix (anything after it is multiplied by $0$), which is how $\bot$ contributes nothing in Eq. (27). Every law is a probability measure (proved in the sanity files).
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Algorithms 1–5, pp.17–20; Definitions 2.6 and 2.9, pp.8, 13; Eqs. (20), (27), (31), pp.13, 24–25

import Mathlib
import Definitions.Def_WalkTreeCluster_Graph
import Definitions.Def_WalkTreeCluster_Params
import Definitions.Def_WalkTreeCluster_FilterPaths

open MeasureTheory

namespace WalkTreeCluster

/-!
# The laws of the filter path walks `X_{u,i}`, of `Keep(u, i)` and of `X^{keep}_{u,i}`

Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027
submission (manuscript sha256 638eeef1…), Algorithms 1–5 (WalkBlock, Child, WalkTree,
SampleCollision, Keep), pp.17–20; Definitions 2.6 and 2.9, pp.8, 13; the recursion (27) and (31),
pp.24–25.

For every stage `i` and vertex `u` this module defines, by one recursion on `i`,
* `walkLaw i u`, the law of `X_{u,i}` (the matrix of the walk tree `T(u, i)`, Definition 2.6), and
* `keepLaw i u`, the law of `Keep(u, i)` (Algorithm 5),
exactly as Algorithms 1–5 sample them:
* `X_{u,0} = 1_u` in the single row `∅`, and `Keep(u, 0) = 1`.
* For `i ≥ 1`, `X_{u,i} = (1/q) Σ_{ℓ=1}^{q} Z_ℓ` with `q` independent children `Z_ℓ` (Algorithm 3,
  and the factor `1/q` of Algorithm 2, line 1). A child (Algorithm 2) chooses
  - with probability `1 − a` the low-pass term: one walk block from `u`, then
    `Z = (1/(1 − a)) κ (X ⊕ 0)` with `X` a fresh `X_{v,i−1}` from the block's endpoint `v`;
  - with probability `a/2` the high-pass identity term: `Z = (2/a)(0 ⊕ X)`, `X` a fresh `X_{u,i−1}`;
  - with probability `a/2` a negative high-pass term: `s ≥ 1` with probability `d_s`, then `2s` walk
    blocks, and `Z = −(2/a) κ_1 ⋯ κ_{2s} (0 ⊕ X)` with `X` a fresh `X_{v_{2s},i−1}`.
  A walk block from `z` (Algorithm 1) is discounted with probability `δ` (the child is then `⊥` and
  contributes zero); otherwise it moves to `v ∼ M^t 1_z` and draws `κ ∼ Keep(v, i − 1)`.
* For `i ≥ 1`, `Keep(u, i) = κ · τ_u(i)` with `κ ∼ Keep(u, i − 1)` and
  `τ_u(i) = (1 + 64 α^{2i} (1/B) Σ_{ℓ=1}^{B} ⟨X_ℓ, X'_ℓ⟩²_w)^{−1/4}` for `2B` independent copies
  `X_ℓ, X'_ℓ` of `X_{u,i}` (Algorithm 5, Eq. (20)).
All the draws are independent.

**Formalization Note.**
* `blockTail j m u` is the law of `κ_1 ⋯ κ_m · X` after `m` walk blocks from `u` at stage `j + 1`,
  followed by a fresh stage-`j` sample `X` from the last endpoint; a discounted block gives the zero
  matrix (any continuation is multiplied by `0`, which is how `⊥` contributes nothing in (27)).
  `blockTail j 0 u` is the law of `X_{u,j}` itself.
* The choice of `s` is the countable mixture `Measure.sum` with masses `d_s`; mixtures are sums of
  measures scaled by `ENNReal.ofReal` of the probabilities.
* `M^t` is `(walkMatrix nbr) ^ tParam ϵ ϕ`, and the probability of moving from `z` to `w` in a block
  is `(M^t)(w, z)`.
* `keepWalkLaw i u`, the law of `X^{keep}_{u,i} = κ X_{u,i}` with `κ ∼ Keep(u, i)` independent
  (Definition 2.9).
* The parameters `a, q, α, δ, B, t` are those of the parameters module, computed from `ϵ, ϕ`.
-/

/-- The pair of stage-`i` laws: `walk u` is the law of `X_{u,i}`, `keep u` the law of `Keep(u, i)`. -/
structure StageLaws (n i : ℕ) where
  /-- The law of `X_{u,i}`. -/
  walk : Fin n → Measure (Mat n i)
  /-- The law of `Keep(u, i)`. -/
  keep : Fin n → Measure ℝ

/-- `τ_u(i) = (1 + 64 α^{2i} (1/B) Σ_ℓ ⟨X_ℓ, X'_ℓ⟩²_w)^{−1/4}` on the `2B` samples `Xs`
(Algorithm 5, line 5; Eq. (20)). -/
noncomputable def tauStat (ϵ ϕ : ℝ) {n : ℕ} (i : ℕ)
    (Xs : Fin (BParam ϵ ϕ) → Mat n i × Mat n i) : ℝ :=
  (1 + 64 * alphaParam ϵ ϕ ^ (2 * i) *
      ((1 / (BParam ϵ ϕ : ℝ)) * ∑ ℓ, (wInner (aParam ϵ ϕ) (Xs ℓ).1 (Xs ℓ).2) ^ 2)) ^ (-(1 / 4 : ℝ))

/-- The law of `κ_1 ⋯ κ_m · X` after `m` stage-`(j+1)` walk blocks from `u` (Algorithm 1), with a
fresh `X ∼ prevWalk` from the last endpoint; a discounted block (probability `δ`) yields `0`. -/
noncomputable def blockTail {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) {j : ℕ}
    (prevWalk : Fin n → Measure (Mat n j)) (prevKeep : Fin n → Measure ℝ) :
    ℕ → Fin n → Measure (Mat n j)
  | 0, u => prevWalk u
  | m + 1, u =>
      ENNReal.ofReal (deltaParam ϵ ϕ) • Measure.dirac 0 +
      ENNReal.ofReal (1 - deltaParam ϵ ϕ) •
        ∑ w : Fin n, ENNReal.ofReal (((walkMatrix nbr) ^ tParam ϵ ϕ) w u) •
          ((prevKeep w).prod (blockTail nbr ϵ ϕ prevWalk prevKeep m w)).map
            (fun p : ℝ × Mat n j => p.1 • p.2)

/-- The law of one child `Z` (before the division by `q`) of a node at vertex `u` with `j + 1` stages
remaining (Algorithm 2; Eq. (31)). -/
noncomputable def childLaw {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) {j : ℕ}
    (prevWalk : Fin n → Measure (Mat n j)) (prevKeep : Fin n → Measure ℝ) (u : Fin n) :
    Measure (Mat n (j + 1)) :=
  let a := aParam ϵ ϕ
  ENNReal.ofReal (1 - a) •
      (blockTail nbr ϵ ϕ prevWalk prevKeep 1 u).map (fun Y => (1 / (1 - a)) • lowBlock Y) +
    ENNReal.ofReal (a / 2) • (prevWalk u).map (fun Y => (2 / a) • highBlock Y) +
    ENNReal.ofReal (a / 2) •
      Measure.sum (fun s : ℕ => ENNReal.ofReal (seriesCoeff (s + 1)) •
        (blockTail nbr ϵ ϕ prevWalk prevKeep (2 * (s + 1)) u).map
          (fun Y => (-(2 / a)) • highBlock Y))

/-- The laws at every stage, by recursion on the stage (Algorithms 3 and 5). -/
noncomputable def laws {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) :
    (i : ℕ) → StageLaws n i
  | 0 => ⟨fun u => Measure.dirac (fun _ z => if z = u then 1 else 0), fun _ => Measure.dirac 1⟩
  | j + 1 =>
      let prev := laws nbr ϵ ϕ j
      let walk : Fin n → Measure (Mat n (j + 1)) := fun u =>
        (Measure.pi (fun _ : Fin (qParam ϵ ϕ) => childLaw nbr ϵ ϕ prev.walk prev.keep u)).map
          (fun Zs => (1 / (qParam ϵ ϕ : ℝ)) • ∑ ℓ, Zs ℓ)
      ⟨walk, fun u =>
        ((prev.keep u).prod
            (Measure.pi (fun _ : Fin (BParam ϵ ϕ) => (walk u).prod (walk u)))).map
          (fun p => p.1 * tauStat ϵ ϕ (j + 1) p.2)⟩

/-- The law of `X_{u,i}` (Definition 2.6; Algorithm 3). -/
noncomputable def walkLaw {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (i : ℕ) (u : Fin n) :
    Measure (Mat n i) :=
  (laws nbr ϵ ϕ i).walk u

/-- The law of `Keep(u, i)` (Algorithm 5). -/
noncomputable def keepLaw {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (i : ℕ) (u : Fin n) :
    Measure ℝ :=
  (laws nbr ϵ ϕ i).keep u

/-- The law of `X^{keep}_{u,i} = κ X_{u,i}`, `κ ∼ Keep(u, i)` independent (Definition 2.9). -/
noncomputable def keepWalkLaw {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (i : ℕ)
    (u : Fin n) : Measure (Mat n i) :=
  ((keepLaw nbr ϵ ϕ i u).prod (walkLaw nbr ϵ ϕ i u)).map (fun p : ℝ × Mat n i => p.1 • p.2)

/-- The law of the `2B` samples `(X_ℓ, X'_ℓ)_{ℓ ≤ B}` used by `τ_u(i)` (Algorithm 5, line 3). -/
noncomputable def tauSampleLaw {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (i : ℕ)
    (u : Fin n) : Measure (Fin (BParam ϵ ϕ) → Mat n i × Mat n i) :=
  Measure.pi (fun _ : Fin (BParam ϵ ϕ) => (walkLaw nbr ϵ ϕ i u).prod (walkLaw nbr ϵ ϕ i u))

end WalkTreeCluster


