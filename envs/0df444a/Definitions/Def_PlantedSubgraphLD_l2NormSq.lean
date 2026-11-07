-- Prove2me | Definitions.Def_PlantedSubgraphLD_l2NormSq
-- name    : PlantedSubgraphLD_l2NormSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:35.654061+00:00
-- url     : https://prove2.me/theorems/10403b00-11ee-4196-9c42-9744e407718c
-- title:
--   Likelihood ratios and squared $L^2(\nu)$ norms on a finite set
-- statement:
--   Let $\nu$ be a law on a finite set $\Omega$. For a function $f:\Omega\to\mathbb R$,
--
--   $$
--   \|f\|_{L^2(\nu)}^2=\mathbb E_{\nu}[f^2]=\sum_{x\in\Omega}\nu(x)f(x)^2 ,
--   $$
--
--   and the inner product is $\langle f,g\rangle_\nu=\mathbb E_\nu[fg]$. For a second law $\mu$ the **likelihood ratio** is $d\mu/d\nu:x\mapsto\mu(x)/\nu(x)$.
--
--   The paper's central quantities are $\|L_n\|^2_{L^2(Q_n)}$ with $L_n=dP_n/dQ_n$ and $\|L_{n,\varepsilon}\|^2_{L^2(Q_n)}$ with $L_{n,\varepsilon}=d(T_\varepsilon P_n)/dQ_n$.
--
--   **Formalization Note** The likelihood ratio is the pointwise quotient (`likelihoodRatio`), which is the Radon–Nikodym derivative when $\nu$ has full support, as $Q_n$ does for $n>c$.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §1.1, p.3 (PDF p.5); §3.3, p.12 (PDF p.14)

import Mathlib

namespace PlantedSubgraphLD

/-- The likelihood ratio `dμ/dν` of two laws on a finite set, `x ↦ μ(x)/ν(x)`. -/
noncomputable def likelihoodRatio {α : Type*} (μ ν : α → ℝ) (x : α) : ℝ := μ x / ν x

/-- The squared `L²(ν)` norm `‖f‖²_{L²(ν)} = E_ν[f²] = ∑ₓ ν(x) f(x)²` on a finite set.

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.3, p.12: "⟨f, g⟩Qn := E_{G∼Qn}[f(G)g(G)],
‖f‖²_Qn := E_{G∼Qn}[f(G)²]"; `Lₙ = dPₙ/dQₙ` and `L_{n,ε} := d(T_εPₙ)/dQₙ` (§1.1, p.3).

**Formalization Note** Laws are real functions on a finite type and the likelihood ratio is the
pointwise quotient (`likelihoodRatio`); for a null law of full support (`Qₙ` with `n > c`) this
is the Radon–Nikodym derivative. -/
noncomputable def l2NormSq {α : Type*} [Fintype α] (ν f : α → ℝ) : ℝ := ∑ x, ν x * f x ^ 2

end PlantedSubgraphLD


