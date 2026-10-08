-- Prove2me | Definitions.Def_ClassifAgg_Aggregation_Setup
-- name    : ClassifAgg_Aggregation_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:16:46.801965+00:00
-- url     : https://prove2.me/theorems/0a10b758-a36e-4ce6-b8aa-882179c27b3d
-- title:
--   §3, pp. 143–144 — the n-indexed aggregation setup and the hypotheses (A3), (A4), N = O(n^β) of Theorem 3
-- statement:
--   The data and the hypotheses of Theorem 3.
--
--   In Section 3 the number of classes $N=N_n$, the classes $\mathcal G_1,\dots,\mathcal G_N$, their approximating sets $\mathcal N_j$, the complexities $\rho_j$, the net radii constants $a_j$ and the distribution classes $\mathcal P_j$ may all depend on the sample size $n$. An aggregation setup records all of them as functions of $n$ and $j$.
--
--   The hypotheses, with constants $\kappa$, $\rho_{\min}$, $\rho_{\max}$, $\beta$, $a$, $A$, $c_0$, $\varepsilon_0$, are:
--
--   1. $\kappa\ge1$, $0<\rho_{\min}\le\rho_{\max}<1$, $\beta>0$, $a>0$;
--   2. $N_n\ge1$ and $N_n=O(n^\beta)$ as $n\to\infty$;
--   3. **(A3)**: $\rho_1=\rho_{\min}$ and $\rho_{N}=\rho_{\max}$ for every $n$, and $\rho_1\le\rho_2\le\dots\le\rho_N$;
--   4. **Definition 4**: each $\mathcal P_j$ satisfies (A1) and (A2) for $\mathcal G_j$ with $\kappa$, $\rho_j$, $A$, $c_0$, $\varepsilon_0$, and $G^*_\pi\in\mathcal G_j$ for $\pi\in\mathcal P_j$;
--   5. the last clause of Definition 4, uniformly: $\varepsilon_0=1$, or condition (7) holds over the union of all classes $\mathcal P_j$ over all $n$;
--   6. **(A4)(i)**: for $n\ge1$, $0<a_j\le a$ and $\mathcal N_j$ is an $\varepsilon$-net on $\mathcal G_j$ with $\varepsilon=a_jn^{-1/(1+\rho_j)}$, for the pseudodistance $d_\triangle$ (of every distribution in $\mathcal P_j$) or for $d_{\triangle,e}$;
--   7. **(A4)(ii)**: $\mathcal N_1\subseteq\mathcal N_2\subseteq\dots\subseteq\mathcal N_N$;
--   8. **(A4)(iii)**: $\mathcal N_j$ has complexity bound $\rho_j$ with constant $A$ for the pseudodistance $d_\triangle$ of every distribution in every $\mathcal P_k$;
--   9. the members of the approximating sets are Borel sets.
--
--   **Formalization Note** Several readings make the page's uniformity explicit. One $A$, $c_0$, $\varepsilon_0$ serve every class: the page fixes $c_0,\varepsilon_0$ "without loss of generality" (p. 140), and the Appendix constants depend "only on $A,\rho_{\min},\rho_{\max}$" (p. 163). The constant of Theorem 3 does not depend on $n$ or $j$ (its use in the proof of Corollary 1 takes an $n$-dependent $j$), which requires the modulus in (7) to be uniform over the whole family, hence clause 5. The complexity bounds refer to $d_\triangle$, which depends on the unknown design law, so (A4)(iii) is required for the design law of every distribution in the family; the proof of Lemma 1 uses the bracketing of $\mathcal G_{j^*}\cup\mathcal N_k$ under the true $P_X$. The net conditions are required for $n\ge1$ only, where $n^{-1/(1+\rho_j)}$ is the page's radius. The page's condition $\mathcal G_j\ne\mathcal G_k$ plays no role and is not imposed.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, §3, p. 143 ((A3), (A4)); Theorem 3, p. 144; Definition 4, p. 140

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Procedure

namespace ClassifAgg.Aggregation

open MeasureTheory Filter Asymptotics

/-- The data of §3 (p. 143), indexed by the sample size `n` (the number of classes `N = Nₙ`, the
classes, nets, complexities, net radii and distribution classes may all depend on `n`):
* `N n = Nₙ`;
* `cls n j = 𝒢_j`, `net n j = 𝒩_j`, `ρ n j = ρ_j`, `a n j = a_j`, for `j = 1, …, Nₙ`;
* `P n j = 𝒫_j`, a set of joint distributions `π = (P_X, η)`. -/
structure AggSetup (d : ℕ) where
  N : ℕ → ℕ
  cls : ℕ → ℕ → Set (Set (E d))
  net : ℕ → ℕ → Set (Set (E d))
  ρ : ℕ → ℕ → ℝ
  a : ℕ → ℕ → ℝ
  P : ℕ → ℕ → Set (Measure (E d) × (E d → ℝ))

/-- The hypotheses of Theorem 3 (p. 144) on the setup `S`, with the explicit constants `κ ≥ 1`,
`ρ_min`, `ρ_max`, `β > 0`, `a = sup_j a_j`, and one `A, c₀, ε₀` for all classes:
1. parameter ranges `1 ≤ κ`, `0 < ρ_min ≤ ρ_max < 1`, `0 < β`, `0 < a`;
2. `Nₙ ≥ 1` and `Nₙ = O(n^β)`;
3. (A3): `ρ_1 = ρ_min`, `ρ_{Nₙ} = ρ_max` for every `n`, and `ρ_1 ≤ ρ_2 ≤ ⋯ ≤ ρ_{Nₙ}`;
4. Definition 4, core part: each `𝒫_j` satisfies (A1), (A2) and `G*_π ∈ 𝒢_j` with `κ, ρ_j, A, c₀, ε₀`;
5. Definition 4, last clause, uniformly: `ε₀ = 1`, or (7) holds over all `𝒫_j` of all `n` together;
6. (A4)(i): for `n ≥ 1`, `0 < a_j ≤ a`, and `𝒩_j` is an `a_j n^{-1/(1+ρ_j)}`-net on `𝒢_j` for `d_△`
   (of every distribution in `𝒫_j`) or for `d_{△,e}`;
7. (A4)(ii): `𝒩_1 ⊆ 𝒩_2 ⊆ ⋯ ⊆ 𝒩_{Nₙ}`;
8. (A4)(iii): `𝒩_j` has complexity bound `ρ_j` with constant `A` for `d_△` of every distribution in
   every `𝒫_k`;
9. members of the nets are Borel sets. -/
def AggAssumptions {d : ℕ} (S : AggSetup d) (κ ρmin ρmax β a A c0 ε0 : ℝ) : Prop :=
  (1 ≤ κ ∧ 0 < ρmin ∧ ρmin ≤ ρmax ∧ ρmax < 1 ∧ 0 < β ∧ 0 < a) ∧
  (∀ n, 1 ≤ S.N n) ∧
  ((fun n : ℕ => (S.N n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ β)) ∧
  (∀ n, S.ρ n 1 = ρmin ∧ S.ρ n (S.N n) = ρmax) ∧
  (∀ n j k, 1 ≤ j → j ≤ k → k ≤ S.N n → S.ρ n j ≤ S.ρ n k) ∧
  (∀ n j, 1 ≤ j → j ≤ S.N n → IsClassCore (S.P n j) (S.cls n j) κ (S.ρ n j) A c0 ε0) ∧
  (ε0 = 1 ∨ MarginMassVanishes (⋃ n, ⋃ j ∈ Set.Icc 1 (S.N n), S.P n j)) ∧
  (∀ n j, 1 ≤ n → 1 ≤ j → j ≤ S.N n →
    0 < S.a n j ∧ S.a n j ≤ a ∧
    ((∀ π ∈ S.P n j,
        IsNet π.1 (S.a n j * (n : ℝ) ^ (-1 / (1 + S.ρ n j))) (S.net n j) (S.cls n j)) ∨
      IsEmpNet n (S.a n j * (n : ℝ) ^ (-1 / (1 + S.ρ n j))) (S.net n j) (S.cls n j))) ∧
  (∀ n j k, 1 ≤ j → j ≤ k → k ≤ S.N n → S.net n j ⊆ S.net n k) ∧
  (∀ n j k, 1 ≤ j → j ≤ S.N n → 1 ≤ k → k ≤ S.N n →
    ∀ π ∈ S.P n k, HasComplexityBound π.1 (S.net n j) (S.ρ n j) A) ∧
  (∀ n j, 1 ≤ j → j ≤ S.N n → ∀ G ∈ S.net n j, MeasurableSet G)

end ClassifAgg.Aggregation


