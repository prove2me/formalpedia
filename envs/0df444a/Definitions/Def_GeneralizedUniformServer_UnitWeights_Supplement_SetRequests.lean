-- Prove2me | Definitions.Def_GeneralizedUniformServer_UnitWeights_Supplement_SetRequests
-- name    : GeneralizedUniformServer_UnitWeights_Supplement_SetRequests
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:40:00.241431+00:00
-- url     : https://prove2.me/theorems/df139dce-3f82-46e0-925f-8a5bf6b6c94a
-- title:
--   Set requests, their repairs and offline optimum, the weight update $T_P$, and the algorithm of §3.3
-- statement:
--   A **set request** $P$ specifies a finite set $P_i\subseteq M_i$ for every $i\in[k]$ (some $P_i$ may be empty); its size is $n(P)=\sum_i|P_i|$. A configuration $x$ **serves** $P$ if $x_i\in P_i$ for some $i$. The **repairs** of a configuration $x$ failing $P$ are the $n(P)$ configurations $x[i\mapsto p]$ obtained by moving one server $i$ to one point $p\in P_i$. Offline solutions, their unit Hamming cost and $\mathrm{OPT}(\rho)$ (the minimum cost of an offline solution with $o_0=a$) are defined as in §2 with this service relation.
--
--   For a finitely supported $\phi:X\to[0,\infty)$ the weight update is
--   $$(T_P\phi)(y)=\mathbf 1[y\text{ serves }P]\,\phi(y)+\frac1{2\,n(P)}\sum_{x\text{ fails }P}\ \sum_{i\in[k]}\sum_{p\in P_i}\phi(x)\,\mathbf 1[y=x[i\mapsto p]],$$
--   so every failing configuration passes the fraction $1/(2n(P))$ of its weight to each of its repairs. With $\phi_0=\mathbf 1_{\{a\}}$, $\phi_t=T_{P_t}\phi_{t-1}$, $\Phi_t=\|\phi_t\|$ and $\mu_t=\phi_t/\Phi_t$, the **algorithm of §3.3** starts at $X_0=a$ and, when $P_t$ arrives:
--   1. if $X_{t-1}$ serves $P_t$, it stays;
--   2. otherwise, with probability $1/2$ it moves to a uniformly random repair of $X_{t-1}$ for $P_t$, and with probability $1/2$ to a configuration drawn from $\mu_t$, independently of everything else.
--
--   These are the objects of §3.3, the set-request version of the algorithm of §3.2.
--
--   **Formalization Note** A set request is a dependent family of `Finset`s; the spaces $M_i$ are arbitrary. The uniform repair is drawn uniformly over the $n(P)$ pairs $(i,p)$, $p\in P_i$, which are in bijection with the repairs of a failing configuration. Two fallbacks are never reached under the hypothesis $n(P)\ge1$ of Theorem 3.5: if $n(P)=0$ the repair branch stays, and $\mu_t$ is a point mass if $\Phi_t=0$. OPT is an infimum in $\mathbb N$, attained whenever the feasible set is nonempty, which holds when every request has $n(P_t)\ge1$.
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 10, §3.3 (with §3.1–§3.2, pp. 8–9)

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Supplement_Online

open scoped NNReal

noncomputable section

namespace GeneralizedUniformServer.UnitWeights.Supplement

variable {k : ℕ} {M : Fin k → Type*}

/-- A request that specifies sets (source §3.3, p. 10): a finite set `Pᵢ ⊆ Mᵢ` for every
`i ∈ [k]` (some `Pᵢ` may be empty). -/
abbrev SetRequest (M : Fin k → Type*) : Type _ := (i : Fin k) → Finset (M i)

/-- The size `n(P) = ∑ᵢ |Pᵢ|` of a set request. -/
def reqSize (P : SetRequest M) : ℕ := ∑ i : Fin k, (P i).card

/-- `x` serves the set request `P` iff `xᵢ ∈ Pᵢ` for some `i` (source §3.3, p. 10). -/
def ServesSet (x : Config M) (P : SetRequest M) : Prop := ∃ i : Fin k, x i ∈ P i

/-- The pairs `(i, p)` with `p ∈ Pᵢ`, indexing the `n(P)` repairs of a configuration. -/
def repairPairs (P : SetRequest M) : Finset (Σ i : Fin k, M i) :=
  Finset.univ.sigma P

/-- The repair for the pair `(i, p)`: move server `i` of `x` to `p`, keep the others. -/
def setRepair (x : Config M) (s : Σ i : Fin k, M i) : Config M :=
  Function.update x s.1 s.2

/-- An offline solution for set requests `ρ = (P₁, …, P_T)` (source §3.3 with §2, p. 8, 10):
configurations `o₀, …, o_T` with `o_t` serving `P_t` for `t ≥ 1` (`P_t = ρ[t-1]`). -/
def IsSetOfflineSolution (ρ : List (SetRequest M)) (o : Fin (ρ.length + 1) → Config M) : Prop :=
  ∀ s : Fin ρ.length, ServesSet (o s.succ) ρ[s]

/-- The unit-distance cost `∑_{t=1}^T d(o_{t-1}, o_t)` of a set-request offline solution. -/
def setOfflineCost (ρ : List (SetRequest M)) (o : Fin (ρ.length + 1) → Config M) : ℕ :=
  ∑ s : Fin ρ.length, dist (o s.castSucc) (o s.succ)

/-- `OPT(ρ)` for set requests: the minimum unit-distance cost of an offline solution with
`o₀ = a`. Taken in `ℕ`; when every request has `n(P_t) ≥ 1` the feasible set is nonempty, so the
infimum is attained and is the minimum. -/
def setOptCost (a : Config M) (ρ : List (SetRequest M)) : ℕ :=
  sInf {C : ℕ | ∃ o : Fin (ρ.length + 1) → Config M,
    IsSetOfflineSolution ρ o ∧ o 0 = a ∧ setOfflineCost ρ o = C}

/-- The set-request weight update (source §3.3, p. 10, with equation (1) of §3.1):
`(T_P ϕ)(y) = 1[y serves P] ϕ(y) + (1/(2 n(P))) ∑_{x fails P} ∑_{(i,p), p ∈ Pᵢ} ϕ(x) 1[y = x[i ↦ p]]`,
on finitely supported `ϕ ≥ 0`; the sum over failing `x` runs over the support of `ϕ`. -/
def setUpdate (P : SetRequest M) (ϕ : Config M →₀ ℝ≥0) : Config M →₀ ℝ≥0 := by
  classical
  exact ϕ.filter (fun y => ServesSet y P) +
    ∑ x ∈ ϕ.support.filter (fun x => ¬ ServesSet x P), ∑ s ∈ repairPairs P,
      Finsupp.single (setRepair x s) (ϕ x / (2 * (reqSize P : ℝ≥0)))

/-- The weights `ϕ_t`: `ϕ₀ = 1_{a}` and `ϕ_t = T_{P_t} ϕ_{t-1}`, after the finite prefix `ρ`. -/
def setWeights (a : Config M) (ρ : List (SetRequest M)) : Config M →₀ ℝ≥0 :=
  ρ.foldl (fun ϕ P => setUpdate P ϕ) (Finsupp.single a 1)

/-- The total weight `Φ_t = ‖ϕ_t‖`. -/
def setTotalWeight (a : Config M) (ρ : List (SetRequest M)) : ℝ≥0 :=
  (setWeights a ρ).sum fun _ v => v

/-- The normalized weight `μ_t = ϕ_t / Φ_t` as a probability mass function; the point mass at
`fallback` is returned only if `Φ_t = 0` (which cannot happen when every request has
`n(P) ≥ 1`, since then `Φ_t ≥ Φ_{t-1}/2`). -/
def setNormalizedLaw (a : Config M) (ρ : List (SetRequest M)) (fallback : Config M) :
    PMF (Config M) := by
  classical
  exact if h : setTotalWeight a ρ = 0 then PMF.pure fallback else
    PMF.ofFinset
      (fun y => ((setWeights a ρ y : ℝ≥0) : ENNReal) / ((setTotalWeight a ρ : ℝ≥0) : ENNReal))
      (setWeights a ρ).support
      (by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, ← ENNReal.ofNNReal_finsetSum]
        exact ENNReal.mul_inv_cancel (by simpa [setTotalWeight, Finsupp.sum] using h)
          ENNReal.coe_ne_top)
      (by
        intro y hy
        simp [Finsupp.notMem_support_iff.mp hy])

/-- The algorithm of §3.3 (source p. 10, with §3.2, p. 9), started at `a`. When the set request
`P = P_t` arrives, with earlier requests `hist = (P₁, …, P_{t-1})` and current configuration
`x = X_{t-1}` (the head of the configuration history):
1. if `x` serves `P`, it stays: `X_t = x`;
2. otherwise a fresh fair coin is tossed: on one side it moves to the repair `x[i ↦ p]` for a
   pair `(i, p)`, `p ∈ Pᵢ`, uniform among the `n(P)` pairs; on the other it moves to a fresh draw
   from `μ_t`, the normalized set-request weights after `(P₁, …, P_t)`.
(If `n(P) = 0` no repair exists; the repair branch then stays, a case excluded by Theorem 3.5.) -/
def setAlg (a : Config M) : GenOnlineAlg M (SetRequest M) := fun hist path P => by
  classical
  exact
    let x := path.headD a
    if ServesSet x P then PMF.pure x else
      (PMF.uniformOfFintype Bool).bind fun b =>
        if b then
          (if h : (repairPairs P).Nonempty then
            (PMF.uniformOfFinset (repairPairs P) h).map (setRepair x)
          else PMF.pure x)
        else setNormalizedLaw a (hist ++ [P]) x

end GeneralizedUniformServer.UnitWeights.Supplement


