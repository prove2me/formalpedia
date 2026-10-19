-- Prove2me | Definitions.Def_LimitPoA_RegVar_Decomp
-- name    : LimitPoA_RegVar_Decomp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:32.804988+00:00
-- url     : https://prove2.me/theorems/242260c5-a514-4840-8be8-5da4e95820f6
-- title:
--   §3.3–3.4, pp. 19–23 — decomposable sequences, asymptotic decomposition (Definition 3.5), the bound PoA‾, K_reg, scalable by decomposition (Definition 3.6)
-- statement:
--   This file defines the asymptotic decomposition of §3.3–3.4.
--
--   **Decomposable sequences (p. 19).** A regular sequence $(d^{(n)})$ of a (sub)game with group set $\mathcal K'$ is decomposable if $d^{(n)}_k \to \infty$ for each $k \in \mathcal K'$ and $\lim_n d^{(n)}_k/d^{(n)}_{k'} \in [0,\infty]$ exists for all $k, k' \in \mathcal K'$. One writes $k \preceq k'$ if this limit is finite, $k \not\preceq k'$ if it is $\infty$, $k \prec k'$ if $k \preceq k'$ and $k' \not\preceq k$, and $k \sim k'$ if $k \preceq k'$ and $k' \preceq k$.
--
--   **Asymptotic decomposition (Definition 3.5, p. 20).** For a decomposable sequence, subgames $\Gamma_{|\mathcal K_1},\dots,\Gamma_{|\mathcal K_m}$ form an asymptotic decomposition $\Gamma \asymp_{d^{(n)}} \Gamma_{|\mathcal K_1}\oplus\cdots\oplus\Gamma_{|\mathcal K_m}$ w.r.t. scaling sequences $(g^{(u)}_n)_n$ if the classes $\mathcal K_u$ partition the groups and
--
--   1. (AD1) $k, k' \in \mathcal K_u$ implies $k \sim k'$;
--   2. (AD2) if $u < v$ then $k' \prec k$ for all $k \in \mathcal K_u$, $k' \in \mathcal K_v$;
--   3. (AD3) for each $u$, the sequence $(d^{(n)}_{|\mathcal K_u})_n$ is scalable w.r.t. $\Gamma_{|\mathcal K_u}$ with the scaling sequence $(g^{(u)}_n)_n$.
--
--   **The upper bound (pp. 20–21).** With $\tilde f^{(n)}$ an NE profile of $\Gamma$ for $d^{(n)}$ and $\tilde f^{(\mathcal K_u,n)}$ an NE profile of $\Gamma_{|\mathcal K_u}$ for $d^{(n)}_{|\mathcal K_u}$,
--   $$\overline{\mathrm{PoA}}(d^{(n)}) = \frac{C(\tilde f^{(n)})}{\sum_{u\in\mathcal M} C_{\Gamma_{|\mathcal K_u}}(\tilde f^{(\mathcal K_u,n)})}, \qquad \mathcal M = \{1,\dots,m\}.$$
--   For a profile $f$ of $\Gamma$, its restriction $f_{|\mathcal K'}$ has loads equal to the independent consumptions $f_{a|\mathcal K'} = \sum_{k\in\mathcal K'}\sum_{s\in\mathcal S_k: a\in s} f_s$, and the joint total cost of $\Gamma_{|\mathcal K'}$ is $\sum_{k\in\mathcal K'}\sum_{s\in\mathcal S_k} f_s\,\tau_s(f)$ (p. 19).
--
--   **Regular groups and Definition 3.6 (pp. 22–23).** For a regular sequence, $\mathcal K_{reg}$ is the set of groups with $d^{(n)}_k \to \infty$. A game is *scalable by decomposition* if each regular sequence has an infinite subsequence $(n_i)$ such that $(d^{(n_i)}_{|\mathcal K_{reg}})_i$ is decomposable and $\Gamma_{|\mathcal K_{reg}} \asymp \Gamma_{|\mathcal K_1}\oplus\cdots\oplus\Gamma_{|\mathcal K_m}$ for non-empty subsets $\mathcal K_1,\dots,\mathcal K_m$ of $\mathcal K_{reg}$.
--
--   **Formalization Note** Subgames are encoded by zero-padding: a demand vector of $\Gamma_{|\mathcal K'}$ is a demand vector of $\Gamma$ vanishing outside $\mathcal K'$, and the NE and SO costs of $\Gamma$ at such a vector are those of the subgame. The decomposition predicate includes the source's decomposability premise. The pairwise demand relations require their denominator to be eventually positive, as it is for every group of a decomposable sequence; this excludes Lean's $d_k/0=0$ value. Definition 3.5 as printed does not say that $\mathcal K_1,\dots,\mathcal K_m$ partition the groups; the text before it ("The partition of $\mathcal K$ is defined by putting equivalent groups into one class", p. 19) and Appendix A.5 ("a partition of $\mathcal K$ satisfying (AD1)–(AD2)") fix this intent, and without it Theorem 3.2 would be false, so the classes are required to be non-empty, pairwise disjoint and to cover the group set. The scaling sequences $g^{(u)}$ are explicit data of the decomposition, as Lemma 6 refers to them. Limits of ratios in $[0,\infty]$ are taken in `ℝ≥0∞` through `ENNReal.ofReal`. The independent consumption on p. 19 is printed with $\sum_{k\in\mathcal K}$; the intended $\sum_{k\in\mathcal K'}$ (the next sentence says $f_{a|\mathcal K'} \le f_a$) is used. $\overline{\mathrm{PoA}}$ is the worst NE cost of $\Gamma$ over the sum of the worst NE costs of the subgames (all NE profiles have equal cost).
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, pp. 19–23, decomposable sequences and ⪯, ∼, ≺ (p. 19), Definition 3.5 (AD1)–(AD3), (3.2), PoA‾ (pp. 20–21), K_reg (p. 22), Definition 3.6

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit

namespace LimitPoA.RegVar

open Filter Topology KellyStochasticNetworks ENNReal

variable (Γ : Game)

/-- p. 19: a regular sequence `d` of the subgame `Γ|K′` (vanishing outside `K′`) is decomposable if
`d_k^(n) → ∞` for each `k ∈ K′` and `lim_n d_k^(n)/d_{k′}^(n) ∈ [0, ∞]` exists for each `k, k′ ∈ K′`. -/
def IsDecomposable (K' : Finset (Fin Γ.Sd)) (d : ℕ → Fin Γ.Sd → ℝ) : Prop :=
  (∀ n k, k ∉ K' → d n k = 0) ∧ (∃ dInf, IsRegular Γ d dInf) ∧
    (∀ k ∈ K', Tendsto (fun n => d n k) atTop atTop) ∧
    ∀ k ∈ K', ∀ k' ∈ K', ∃ L : ℝ≥0∞,
      Tendsto (fun n => ENNReal.ofReal (d n k / d n k')) atTop (𝓝 L)

/-- p. 19: `k ⪯ k′` iff `lim_n d_k^(n)/d_{k′}^(n) < ∞`. -/
def GrpLe (d : ℕ → Fin Γ.Sd → ℝ) (k k' : Fin Γ.Sd) : Prop :=
  (∀ᶠ n in atTop, 0 < d n k') ∧
    ∃ L : ℝ≥0∞, L < ⊤ ∧ Tendsto (fun n => ENNReal.ofReal (d n k / d n k')) atTop (𝓝 L)

/-- p. 19: `k ⋠ k′` iff `lim_n d_k^(n)/d_{k′}^(n) = ∞`. -/
def GrpNotLe (d : ℕ → Fin Γ.Sd → ℝ) (k k' : Fin Γ.Sd) : Prop :=
  (∀ᶠ n in atTop, 0 < d n k') ∧
    Tendsto (fun n => ENNReal.ofReal (d n k / d n k')) atTop (𝓝 ⊤)

/-- p. 19: `k ≺ k′` iff `k ⪯ k′` and `k′ ⋠ k`. -/
def GrpLt (d : ℕ → Fin Γ.Sd → ℝ) (k k' : Fin Γ.Sd) : Prop :=
  GrpLe Γ d k k' ∧ GrpNotLe Γ d k' k

/-- p. 19: `k ∼ k′` iff `k ⪯ k′` and `k′ ⪯ k`. -/
def GrpEquiv (d : ℕ → Fin Γ.Sd → ℝ) (k k' : Fin Γ.Sd) : Prop :=
  GrpLe Γ d k k' ∧ GrpLe Γ d k' k

/-- Definition 3.5, p. 20: `Γ|K′ ≍_{d^(n)} Γ|K_1 ⊕ ⋯ ⊕ Γ|K_m` w.r.t. the scaling sequences
`g u = (g_n^(u))_n`. The classes `cls u = K_u` are non-empty and partition `K′` (the partition of p. 19);
(AD1), (AD2), and (AD3) with the scaling sequence `g u` of the class `K_u`. -/
def IsAsymDecomp (τ : Fin Γ.J → ℝ → ℝ) (K' : Finset (Fin Γ.Sd)) (d : ℕ → Fin Γ.Sd → ℝ)
    (m : ℕ) (cls : Fin m → Finset (Fin Γ.Sd)) (g : Fin m → ℕ → ℝ) : Prop :=
  IsDecomposable Γ K' d ∧
    (∀ u, (cls u).Nonempty) ∧ (∀ u v, u ≠ v → Disjoint (cls u) (cls v)) ∧
    (∀ k, k ∈ K' ↔ ∃ u, k ∈ cls u) ∧
    -- (AD1)
    (∀ u, ∀ k ∈ cls u, ∀ k' ∈ cls u, GrpEquiv Γ d k k') ∧
    -- (AD2)
    (∀ u v, u < v → ∀ k ∈ cls u, ∀ k' ∈ cls v, GrpLt Γ d k' k) ∧
    -- (AD3)
    ∀ u, ∃ (dInf : Fin Γ.Sd → ℝ) (τInf : Fin Γ.J → ℝ → ℝ≥0∞),
      IsLimitGame Γ τ (cls u) (fun n => restrict Γ (cls u) (d n)) (g u) dInf τInf

/-- p. 21: the upper bound `\overline{PoA}(d) = C(f̃) / Σ_u C_{Γ|K_u}(f̃^(K_u))`, the worst NE cost of `Γ`
over the sum of the NE costs of the subgames `Γ|K_u`. -/
noncomputable def PoABar (τ : Fin Γ.J → ℝ → ℝ) {m : ℕ} (cls : Fin m → Finset (Fin Γ.Sd))
    (d : Fin Γ.Sd → ℝ) : ℝ :=
  NECost Γ τ d / ∑ u, NECost Γ τ (restrict Γ (cls u) d)

/-- p. 19: the profile `f|K′` of the subgame `Γ|K′`: flows on strategies of groups outside `K′` set to 0.
Its loads are the independent consumptions `f_{a|K′} = Σ_{k ∈ K′} Σ_{s ∈ S_k, a ∈ s} f_s`. -/
noncomputable def restrictProfile (K' : Finset (Fin Γ.Sd)) (f : Fin Γ.R → ℝ) : Fin Γ.R → ℝ :=
  fun s => if Γ.grp s ∈ K' then f s else 0

/-- p. 19: the joint total cost `Σ_{k ∈ K′} Σ_{s ∈ S_k} f_s · τ_s(f)` of the subgame `Γ|K′`. -/
noncomputable def jointTotalCost (τ : Fin Γ.J → ℝ → ℝ) (K' : Finset (Fin Γ.Sd)) (f : Fin Γ.R → ℝ) : ℝ :=
  ∑ s, if Γ.grp s ∈ K' then f s * stratCost Γ τ f s else 0

open scoped Classical in
/-- p. 22: the set `K_reg` of regular groups, those with `d_k^(n) → ∞`. -/
noncomputable def Kreg (d : ℕ → Fin Γ.Sd → ℝ) : Finset (Fin Γ.Sd) :=
  Finset.univ.filter (fun k => Tendsto (fun n => d n k) atTop atTop)

/-- Definition 3.6, p. 23: `Γ` is scalable by decomposition if every regular sequence has an infinite
subsequence `(n_i)` along which `d|K_reg` is decomposable and `Γ|K_reg` has an asymptotic
decomposition into non-empty classes partitioning `K_reg`. -/
def IsScalableByDecomposition (τ : Fin Γ.J → ℝ → ℝ) : Prop :=
  ∀ (d : ℕ → Fin Γ.Sd → ℝ) (dInf : Fin Γ.Sd → ℝ), IsRegular Γ d dInf →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      IsDecomposable Γ (Kreg Γ d) (fun i => restrict Γ (Kreg Γ d) (d (φ i))) ∧
      ∃ (m : ℕ) (cls : Fin m → Finset (Fin Γ.Sd)) (g : Fin m → ℕ → ℝ),
        IsAsymDecomp Γ τ (Kreg Γ d) (fun i => restrict Γ (Kreg Γ d) (d (φ i))) m cls g

end LimitPoA.RegVar


