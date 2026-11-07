-- Prove2me | Definitions.Def_PlantedSubgraphLD_lowDegNormSq
-- name    : PlantedSubgraphLD_lowDegNormSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:21:20.809194+00:00
-- url     : https://prove2.me/theorems/2ec1bab8-0a57-40b7-a593-51b5849e2db3
-- title:
--   The low-degree norm $\|L_n^{\le D}\|^2_{L^2(Q_n)}$
-- statement:
--   For an integer $D\ge0$ let $\mathbb R[X]_{\le D}$ be the space of functions of a graph on $[n]$ that can be written as multilinear polynomials of degree at most $D$ in the edge indicators $\omega(e)$, $e\in\binom{[n]}2$; it is spanned by the monomials $\prod_{e\in S}\omega(e)$ with $|S|\le D$. The **degree-$D$ low-degree likelihood ratio** is the orthogonal projection in $L^2(Q_n)$
--
--   $$
--   L_n^{\le D}=\Pi^{Q_n}_{\le D}L_n,\qquad L_n=\frac{dP_n}{dQ_n},
--   $$
--
--   and the **low-degree norm** is $\|L_n^{\le D}\|^2_{L^2(Q_n)}$. Since $\langle L_n,f\rangle_{Q_n}=\langle L_n^{\le D},f\rangle_{Q_n}$ for $f\in\mathbb R[X]_{\le D}$, Cauchy–Schwarz gives
--
--   $$
--   \|L_n^{\le D}\|^2_{L^2(Q_n)}=\sup\Big\{\frac{\langle L_n,f\rangle_{Q_n}^2}{\|f\|^2_{L^2(Q_n)}}:\ f\in\mathbb R[X]_{\le D},\ \|f\|_{L^2(Q_n)}>0\Big\},
--   $$
--
--   the supremum being attained at $f=L_n^{\le D}$; this is the paper's identity (1.1) with the constant function kept. The condition $\|L_n^{\le D_n}\|^2=1+o(1)$ says that no degree-$D_n$ statistic distinguishes $P_n$ from $Q_n$ with non-vanishing advantage.
--
--   **Formalization Note** The definition is the variational form above (`projNormSq`), with $f$ ranging over the whole span, not over single monomials. For $n>c$ the null $Q_n$ has full support, so the set is nonempty ($f\equiv1$) and bounded and the supremum equals the squared norm of the projection; for $n\le c$ the value is junk, which no limit statement sees.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.3, pp.12–13 (PDF pp.14–15); (1.1), p.1 (PDF p.3)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_planted
import Definitions.Def_PlantedSubgraphLD_l2NormSq

open Classical

namespace PlantedSubgraphLD

/-- The monomial `ω ↦ ∏_{e ∈ S} ω(e)` in the edge indicators of a graph on `[n]`. -/
noncomputable def edgeMonomial {n : ℕ} (S : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n)) : ℝ :=
  ∏ p ∈ S, (if G.Adj p.1 p.2 then (1 : ℝ) else 0)

/-- `ℝ[X]_{≤D}`: the functions on graphs on `[n]` represented by multilinear polynomials of degree
at most `D` in the edge indicators, i.e. the real span of the monomials over sets of at most `D`
unordered pairs (§3.3, p.12). -/
noncomputable def lowDegSpace (n D : ℕ) : Submodule ℝ (SimpleGraph (Fin n) → ℝ) :=
  Submodule.span ℝ
    {f | ∃ S ⊆ LPCommunity.SBMRecovery.pairs n, S.card ≤ D ∧ f = edgeMonomial S}

/-- The squared `L²(ν)` norm of the orthogonal projection of `L` onto a subspace `W`, in its
variational form `sup_{f ∈ W, ‖f‖_ν > 0} ⟨L, f⟩_ν² / ‖f‖²_ν`. -/
noncomputable def projNormSq {α : Type*} [Fintype α] (ν L : α → ℝ) (W : Submodule ℝ (α → ℝ)) : ℝ :=
  sSup {r : ℝ | ∃ f ∈ W, 0 < l2NormSq ν f ∧
    r = (∑ x, ν x * L x * f x) ^ 2 / l2NormSq ν f}

/-- The squared low-degree norm `‖L_n^{≤D}‖²_{L²(Qₙ)}`, where `L_n^{≤D} = Π^{Qₙ}_{≤D} Lₙ` is the
orthogonal projection in `L²(Qₙ)` of the likelihood ratio `Lₙ = dPₙ/dQₙ` onto `ℝ[X]_{≤D}`.

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.3, pp.12–13: "let Π^{Qn}_{≤D} : L²(Qn) →
R[X]≤D denote the orthogonal projection with respect to the inner product ⟨·,·⟩Qn. Then, the
degree-D low-degree likelihood ratio is L≤D_n := Π^{Qn}_{≤D} Ln."

**Formalization Note** The squared norm of the projection is encoded variationally:
`sup { ⟨Lₙ, f⟩²_{Qₙ} / ‖f‖²_{Qₙ} : f ∈ ℝ[X]_{≤D}, ‖f‖_{Qₙ} > 0 }`. Since `ℝ[X]_{≤D}` is a
(finite-dimensional) subspace and `⟨Lₙ, f⟩ = ⟨Π Lₙ, f⟩` for `f` in it, Cauchy–Schwarz shows the
supremum equals `‖Π Lₙ‖²`, attained at `f = Π Lₙ`; this is the paper's (1.1), p.1, with the
constant function kept. `f` ranges over the whole span, not over monomials. For `n > c` the null
`Qₙ` has full support, the set contains the value at `f ≡ 1` and is bounded; for `n ≤ c` the value
is junk, which no limit statement sees. -/
noncomputable def lowDegNormSq (c : ℝ) (n : ℕ) {V : Type} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) (D : ℕ) : ℝ :=
  projNormSq (erdosRenyi c n) (likelihoodRatio (planted c n Γ) (erdosRenyi c n)) (lowDegSpace n D)

end PlantedSubgraphLD


