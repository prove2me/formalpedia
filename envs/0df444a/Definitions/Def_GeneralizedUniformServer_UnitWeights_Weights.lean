-- Prove2me | Definitions.Def_GeneralizedUniformServer_UnitWeights_Weights
-- name    : GeneralizedUniformServer_UnitWeights_Weights
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:44.770232+00:00
-- url     : https://prove2.me/theorems/27df94b5-d601-4e79-9ed3-c8a243e3b512
-- title:
--   The weight update $T_r$ of equation (1), the weights $\phi_t$, $\Phi_t$ and the normalized law $\mu_t$
-- statement:
--   For a finitely supported $\phi:X\to[0,\infty)$ and a request $r$, equation (1) defines
--   $$(T_r\phi)(y)=\mathbf 1[y\in G(r)]\,\phi(y)+\frac1{2k}\sum_{x\notin G(r)}\sum_{i=1}^k\phi(x)\,\mathbf 1[y=R_i(x,r)].$$
--   Thus $T_r\phi$ keeps the weight of every configuration serving $r$, and every configuration $x$ failing $r$ passes $\phi(x)/(2k)$ to each of its $k$ repairs. Given the start $a$ and requests $r_1,r_2,\dots$, let
--   $$\phi_0=\mathbf 1_{\{a\}},\qquad \phi_t=T_{r_t}\phi_{t-1},\qquad \Phi_t=\|\phi_t\|=\sum_x\phi_t(x),\qquad \mu_t=\phi_t/\Phi_t .$$
--   The support of $\phi_t$ is finite even when the spaces are infinite, so $\mu_t$ is a probability distribution with finite support whenever $\Phi_t>0$.
--
--   These are the weights driving the algorithm of §3.2 and its analysis (Lemmas 3.1–3.3).
--
--   **Formalization Note** Weights are finitely supported functions `X →₀ ℝ≥0`; the inner sum over $x\notin G(r)$ runs over the support of $\phi$, where all its nonzero terms are. $\phi_t$ is a function of the prefix $(r_1,\dots,r_t)$ only. The sampler for $\mu_t$ returns a point mass at a supplied fallback configuration when $\Phi_t=0$; for $k\ge1$ this never happens (by equation (2), $\Phi_t\ge\Phi_{t-1}/2>0$), and the statement of Lemma 3.1 implies $\Phi_t\neq0$.
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 8, §3.1, equations (1)–(3)

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Model

open scoped NNReal

noncomputable section

namespace GeneralizedUniformServer.UnitWeights

variable {k : ℕ} {M : Fin k → Type*}

/-- The weight update `T_r` of equation (1) (source §3.1, p. 8), on finitely supported
nonnegative weights `ϕ : X →₀ ℝ≥0`:
`(T_r ϕ)(y) = 1[y ∈ G(r)] ϕ(y) + (1/(2k)) ∑_{x ∉ G(r)} ∑_{i=1}^k ϕ(x) 1[y = Rᵢ(x, r)]`.
The sum over `x ∉ G(r)` is taken over the (finite) support of `ϕ`, which loses nothing
since `ϕ` vanishes elsewhere. -/
def update (r : Config M) (ϕ : Config M →₀ ℝ≥0) : Config M →₀ ℝ≥0 := by
  classical
  exact ϕ.filter (fun y => Serves y r) +
    ∑ x ∈ ϕ.support.filter (fun x => ¬ Serves x r), ∑ i : Fin k,
      Finsupp.single (repair x r i) (ϕ x / (2 * (k : ℝ≥0)))

/-- The weights `ϕ_t` (source §3.1, p. 8): `ϕ₀ = 1_{a}` and `ϕ_t = T_{r_t} ϕ_{t-1}`;
`weights a ρ` is the weight after processing all requests of the finite prefix `ρ`. -/
def weights (a : Config M) (ρ : List (Config M)) : Config M →₀ ℝ≥0 :=
  ρ.foldl (fun ϕ r => update r ϕ) (Finsupp.single a 1)

/-- The total weight `Φ_t = ‖ϕ_t‖ = ∑ₓ ϕ_t(x)` (source §3.1, p. 8). -/
def totalWeight (a : Config M) (ρ : List (Config M)) : ℝ≥0 :=
  (weights a ρ).sum fun _ v => v

/-- The normalized weight `μ_t = ϕ_t / Φ_t` (source §3.1, p. 8), as a probability mass function.
Sampling is defined only when `Φ_t ≠ 0`; otherwise the point mass at `fallback` is returned.
(For `k ≥ 1` the source shows `Φ_t ≥ Φ_{t-1}/2 > 0`, so the fallback is never used; the
milestone stating that `X_t` has law `ϕ_t/Φ_t` is false unless `Φ_t ≠ 0`.) -/
def normalizedLaw (a : Config M) (ρ : List (Config M)) (fallback : Config M) :
    PMF (Config M) := by
  classical
  exact if h : totalWeight a ρ = 0 then PMF.pure fallback else
    PMF.ofFinset (fun y => ((weights a ρ y : ℝ≥0) : ENNReal) / ((totalWeight a ρ : ℝ≥0) : ENNReal))
      (weights a ρ).support
      (by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, ← ENNReal.ofNNReal_finsetSum]
        exact ENNReal.mul_inv_cancel (by simpa [totalWeight, Finsupp.sum] using h)
          ENNReal.coe_ne_top)
      (by
        intro y hy
        simp [Finsupp.notMem_support_iff.mp hy])

end GeneralizedUniformServer.UnitWeights


