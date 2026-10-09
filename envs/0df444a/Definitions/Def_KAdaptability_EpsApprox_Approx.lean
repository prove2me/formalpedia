-- Prove2me | Definitions.Def_KAdaptability_EpsApprox_Approx
-- name    : KAdaptability_EpsApprox_Approx
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:59:57.195016+00:00
-- url     : https://prove2.me/theorems/ee2fae24-bb3e-4397-8cdf-d39a8a21b7a0
-- title:
--   The K-adaptability objective of 𝒫_K, the sets Ξ(ℓ) and Ξ_ε(ℓ), problems (6) and (6_ε) and their effective domains
-- statement:
--   Fix an instance of the two-stage robust binary program (see the data definition) and a decision $(x,\{y^k\}_{k\in\mathcal K})$ with $K$ policies.
--
--   1. **Objective of the K-adaptability problem $\mathcal P_K$** (p. 8):
--   $$\varphi_{\mathcal P_K}(x,\{y^k\})=\sup_{\xi\in\Xi}\Big[\xi^\top Cx+\inf_{k\in\mathcal K}\{\xi^\top Qy^k : Tx+Wy^k\le H\xi\}\Big],$$
--   where an infimum over no feasible policy is $+\infty$ (the paper's convention on p. 8).
--   2. **Index set** $\mathcal L=\{0,\dots,L\}^K$. For $\ell\in\mathcal L$, $\ell_k=0$ records that policy $k$ is feasible and $\ell_k=l\in\{1,\dots,L\}$ records that it violates constraint $l$.
--   3. **Uncertainty sets** (Proposition 1, p. 16, and p. 18): for $\varepsilon>0$,
--   $$\Xi(\ell)=\Big\{\xi\in\Xi:\ Tx+Wy^k\le H\xi\ \ \forall k:\ell_k=0;\ \ [Tx+Wy^k]_{\ell_k}>[H\xi]_{\ell_k}\ \ \forall k:\ell_k\ne0\Big\},$$
--   $$\Xi_\varepsilon(\ell)=\Big\{\xi\in\Xi:\ Tx+Wy^k\le H\xi\ \ \forall k:\ell_k=0;\ \ [Tx+Wy^k]_{\ell_k}\ge[H\xi]_{\ell_k}+\varepsilon\ \ \forall k:\ell_k\ne0\Big\}.$$
--   4. **Objectives of (6) and $(6_\varepsilon)$** (pp. 16, 18):
--   $$\varphi(x,\{y^k\})=\sup_{\ell\in\mathcal L}\ \sup_{\xi\in\Xi(\ell)}\Big[\xi^\top Cx+\min_{k\in\mathcal K:\ \ell_k=0}\xi^\top Qy^k\Big],$$
--   and $\varphi_\varepsilon$ is the same expression with $\Xi_\varepsilon(\ell)$ in place of $\Xi(\ell)$. A minimum over the empty index set is $+\infty$, and a supremum over an empty set is $-\infty$.
--   5. **Effective domains** (Proposition 2, p. 18): $\mathrm{dom}(6)$ is the set of decisions in $\mathcal X\times\mathcal Y^K$ with $\varphi<+\infty$, and $\mathrm{dom}(6_\varepsilon)$ the set with $\varphi_\varepsilon<+\infty$.
--
--   These objects are what Propositions 1 and 2 and Lemma 1 of the paper are about: (6) is the reformulation of $\mathcal P_K$ in which feasibility of the policies is moved into the uncertainty sets, and $(6_\varepsilon)$ is its approximation by closed sets.
--
--   **Formalization Note** All objective values are extended reals (`EReal`); the paper's max and min are read as sup and inf (its Notation paragraph, p. 10). $\ell$ is a function `Fin K → Fin (L+1)`; the paper's row $l\in\{1,\dots,L\}$ is the Lean value `i.succ` for the row index `i : Fin L`, so "$[Tx+Wy^k]_{\ell_k}>[H\xi]_{\ell_k}$ for $\ell_k\ne0$" is written as "for every `i` with `ℓ k = i.succ`, the `i`-th row is violated". Decisions are pairs `(x, y)` with `y : Fin K → Fin M → ℝ`.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 8 (problem (P_K)), p. 16 (Proposition 1, problem (6), Ξ(ℓ)), p. 18 (problem (6_ε), Ξ_ε(ℓ), Proposition 2: dom(6), dom(6_ε)), p. 10 (Notation: max/min read as sup/inf)

import Definitions.Def_KAdaptability_EpsApprox_Problem

open Matrix

namespace KAdaptability.EpsApprox

namespace Problem

variable {N M L nQ R K : ℕ} (P : Problem N M L nQ R)

/-- The objective of the K-adaptability problem 𝒫_K (p. 8) at the decision `(x, {y^k}_{k∈𝒦})`:
`sup_{ξ∈Ξ} [ξ⊤Cx + inf_{k∈𝒦} {ξ⊤Qy^k : Tx + Wy^k ≤ Hξ}]`, in `EReal`. An infimum over no
feasible policy is `⊤ = +∞`, as the paper prescribes (p. 8). -/
noncomputable def objPK (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) : EReal :=
  ⨆ ξ ∈ P.Xi, (((P.firstCost ξ x : ℝ) : EReal) +
    ⨅ k ∈ {k : Fin K | P.lhs x (y k) ≤ P.rhs ξ}, ((P.secondCost ξ (y k) : ℝ) : EReal))

/-- The uncertainty set `Ξ(ℓ)` of Proposition 1 (p. 16), for `ℓ ∈ ℒ = {0,…,L}^K`, encoded as
`ℓ : Fin K → Fin (L+1)`. `ℓ_k = 0` means policy `k` satisfies every constraint; `ℓ_k = i + 1`
(`i : Fin L`, i.e. the paper's row `i + 1 ∈ {1,…,L}`) means policy `k` violates row `i + 1`:
`Ξ(ℓ) = {ξ ∈ Ξ : Tx + Wy^k ≤ Hξ ∀k : ℓ_k = 0;  [Tx + Wy^k]_{ℓ_k} > [Hξ]_{ℓ_k} ∀k : ℓ_k ≠ 0}`. -/
def XiL (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) :
    Set (EuclideanSpace ℝ (Fin nQ)) :=
  {ξ | ξ ∈ P.Xi ∧ (∀ k, ℓ k = 0 → P.lhs x (y k) ≤ P.rhs ξ) ∧
    ∀ k (i : Fin L), ℓ k = i.succ → P.rhs ξ i < P.lhs x (y k) i}

/-- The closed inner approximation `Ξ_ε(ℓ)` (p. 18):
`Ξ_ε(ℓ) = {ξ ∈ Ξ : Tx + Wy^k ≤ Hξ ∀k : ℓ_k = 0;  [Tx + Wy^k]_{ℓ_k} ≥ [Hξ]_{ℓ_k} + ε ∀k : ℓ_k ≠ 0}`,
with the same encoding of `ℓ` as `XiL`. -/
def XiEps (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) :
    Set (EuclideanSpace ℝ (Fin nQ)) :=
  {ξ | ξ ∈ P.Xi ∧ (∀ k, ℓ k = 0 → P.lhs x (y k) ≤ P.rhs ξ) ∧
    ∀ k (i : Fin L), ℓ k = i.succ → P.rhs ξ i + ε ≤ P.lhs x (y k) i}

/-- The bracket `ξ⊤Cx + min_{k∈𝒦 : ℓ_k = 0} ξ⊤Qy^k` of problems (6) and (6_ε), in `EReal`;
the minimum over the empty set (every `ℓ_k ≠ 0`) is `⊤ = +∞`. -/
noncomputable def bracket (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (ξ : EuclideanSpace ℝ (Fin nQ)) : EReal :=
  ((P.firstCost ξ x : ℝ) : EReal) +
    ⨅ k ∈ {k : Fin K | ℓ k = 0}, ((P.secondCost ξ (y k) : ℝ) : EReal)

/-- The objective of problem (6) (p. 16) at the decision `(x, {y^k})`:
`sup_{ℓ∈ℒ} sup_{ξ∈Ξ(ℓ)} [ξ⊤Cx + min_{k : ℓ_k = 0} ξ⊤Qy^k]`, in `EReal`. -/
noncomputable def obj6 (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) : EReal :=
  ⨆ ℓ : Fin K → Fin (L + 1), ⨆ ξ ∈ P.XiL x y ℓ, P.bracket x y ℓ ξ

/-- The objective of problem (6_ε) (p. 18) at the decision `(x, {y^k})`:
`sup_{ℓ∈ℒ} sup_{ξ∈Ξ_ε(ℓ)} [ξ⊤Cx + min_{k : ℓ_k = 0} ξ⊤Qy^k]`, in `EReal`. -/
noncomputable def obj6Eps (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) : EReal :=
  ⨆ ℓ : Fin K → Fin (L + 1), ⨆ ξ ∈ P.XiEps ε x y ℓ, P.bracket x y ℓ ξ

/-- The effective domain `dom(6)` (Proposition 2, p. 18): the decisions
`(x, {y^k}_{k∈𝒦}) ∈ 𝒳 × 𝒴^K` whose objective value in (6) is not `+∞`. -/
def dom6 (K : ℕ) : Set ((Fin N → ℝ) × (Fin K → Fin M → ℝ)) :=
  {d | P.IsDecision d.1 d.2 ∧ P.obj6 d.1 d.2 < ⊤}

/-- The effective domain `dom(6_ε)` (Proposition 2, p. 18): the decisions
`(x, {y^k}_{k∈𝒦}) ∈ 𝒳 × 𝒴^K` whose objective value in (6_ε) is not `+∞`. -/
def dom6Eps (K : ℕ) (ε : ℝ) : Set ((Fin N → ℝ) × (Fin K → Fin M → ℝ)) :=
  {d | P.IsDecision d.1 d.2 ∧ P.obj6Eps ε d.1 d.2 < ⊤}

end Problem

end KAdaptability.EpsApprox


