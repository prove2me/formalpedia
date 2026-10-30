-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_IsDependentRounding
-- name    : OfflineStochMatching_UnitPatience_IsDependentRounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:32:05.261097+00:00
-- url     : https://prove2.me/theorems/f0ff2802-4808-400e-9e2b-3d637938e528
-- title:
--   Dependent rounding of Gandhi et al.: marginals, degree bound and negative correlation (2)
-- statement:
--   Let $y\in\mathbb R^E$ and $V_2\subseteq V$. A function $\mu$ on $\{0,1\}^E$ is a **dependent rounding of $y$** (with negative correlation on the stars of $V_2$) if
--
--   1. $\mu$ is a probability distribution: $\mu(Y)\ge0$ and $\sum_Y\mu(Y)=1$;
--   2. marginals are preserved: $\Pr_\mu[Y_e=1]=y_e$ for every edge $e$;
--   3. degrees are rounded up at most: every $Y$ with $\mu(Y)>0$ satisfies $|\{e\in\delta(x):Y_e=1\}|\le\lceil\sum_{e\in\delta(x)}y_e\rceil$ at every vertex $x$;
--   4. negative correlation (2) holds on the stars of $V_2$: for every $v\in V_2$, $S\subseteq\delta(v)$ and $b\in\{0,1\}$,
--
--   $$
--   \Pr_\mu\Big[\bigcap_{e\in S}(Y_e=b)\Big]\le\prod_{e\in S}\Pr_\mu[Y_e=b].
--   $$
--
--   These are the properties of the rounding procedure of Gandhi, Khuller, Parthasarathy and Srinivasan that the algorithm of Section 4 uses: the degree bound gives $\sum_{e\in\delta(u)}Y_e\le1$ at the unit-patience vertices, and (2) drives Lemma 7.
--
--   **Formalization Note** The rounding is quantified over through these properties rather than defined as a procedure; the procedure of Gandhi et al. has all of them. Property (2), which the paper writes for the activeness $Z_e$ (p. 6), is put on the rounding indicators $Y_e$, as the proof of Lemma 7 (p. 17) applies it; it is required only at vertices of $V_2$, and only the upper half of degree preservation is required.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §4, p. 16 (rounding procedure of Gandhi et al. [25], Σ_{e∈δ(u)} Y_e ≤ 1); §1.2, p. 6, property (2); proof of Lemma 7, p. 17

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_incident

namespace OfflineStochMatching.UnitPatience

/-- **The dependent rounding of Gandhi et al., as the properties the paper uses.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §4, p. 16: "we run the rounding
procedure of Gandhi et al. [25] on `y_e` to get an integral solution `Y_e ∈ {0,1}`. This
guarantees that for each vertex `u ∈ V1` that `Σ_{e∈δ(u)} Y_e ≤ 1`"; §1.2, p. 6, property (2):
"`Pr[⋂_{e∈S}(Z_e = b)] ≤ Π_{e∈S} Pr[Z_e = b]  ∀S ⊆ δ(v), b ∈ {0,1}`"; proof of Lemma 7, p. 17:
"By the negative correlation property (2) of the dependent rounding [25], and the independence of
each `P_j` from both `P_j′` … and from `Y_j′` for all `j′`".

`IsDependentRounding G V2 y μ` says that `μ : (E → Bool) → ℝ` is a probability distribution on
rounded vectors `Y ∈ {0,1}^E` such that
1. (marginals) `Pr_μ[Y_e = 1] = y_e` for every edge `e`;
2. (degree) every `Y` in the support of `μ` has at most `⌈Σ_{e∈δ(x)} y_e⌉` edges of `δ(x)` with
   `Y_e = 1`, at every vertex `x`;
3. (negative correlation, property (2)) for every `v ∈ V2`, every `S ⊆ δ(v)` and `b ∈ {0,1}`,
   `Pr_μ[Y_e = b ∀ e ∈ S] ≤ Π_{e∈S} Pr_μ[Y_e = b]`.

**Formalization Note.** The rounding is quantified over through these properties rather than
defined as the procedure of [25]; that procedure has all of them (marginal preservation, degree
preservation `⌊d⌋ ≤ deg ≤ ⌈d⌉`, negative correlation on `δ(v)`). Property (2) is put on the
rounding indicators `Y_e`, as the proof of Lemma 7 (p. 17) uses it, and it is required only at
the vertices of `V2`; only the upper half of degree preservation is required. -/
def IsDependentRounding {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (G : StochGraph V E) (V2 : Finset V) (y : E → ℝ) (μ : (E → Bool) → ℝ) : Prop :=
  ((∀ Y, 0 ≤ μ Y) ∧ ∑ Y, μ Y = 1) ∧
  (∀ e, ∑ Y ∈ Finset.univ.filter (fun Y : E → Bool => Y e = true), μ Y = y e) ∧
  (∀ Y, μ Y ≠ 0 → ∀ x,
    ((((incident G x).filter (fun e => Y e = true)).card : ℕ) : ℤ) ≤
      ⌈∑ e ∈ incident G x, y e⌉) ∧
  (∀ v ∈ V2, ∀ S ⊆ incident G v, ∀ b : Bool,
    ∑ Y ∈ Finset.univ.filter (fun Y : E → Bool => ∀ e ∈ S, Y e = b), μ Y ≤
      ∏ e ∈ S, ∑ Y ∈ Finset.univ.filter (fun Y : E → Bool => Y e = b), μ Y)

end OfflineStochMatching.UnitPatience


