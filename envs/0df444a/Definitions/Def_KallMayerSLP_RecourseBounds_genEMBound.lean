-- Prove2me | Definitions.Def_KallMayerSLP_RecourseBounds_genEMBound
-- name    : KallMayerSLP_RecourseBounds_genEMBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:39.145116+00:00
-- url     : https://prove2.me/theorems/af2ddfbc-7090-4d57-9cbc-fcbb6a34f3ad
-- title:
--   Generalized E–M upper bound $\sum_\nu \varphi(v^\nu)\,\mathbb Q(v^\nu)$, (2.31)
-- statement:
--   For a function $\varphi$ on the box $\Xi=\times_{i=1}^r[a_i,b_i]$, the **generalized Edmundson–Madansky bound** is the expectation of $\varphi$ under the generalized E–M distribution $\mathbb Q$ of (2.30):
--   $$
--   \int_\Xi\varphi(\eta)\,\mathbb Q(d\eta)=\sum_{\nu=1}^{2^r}\varphi(v^\nu)\,\mathbb Q(v^\nu),
--   $$
--   the sum over the $2^r$ vertices $v^\nu$ of $\Xi$. It is the right-hand side of the generalized E–M inequality (2.31), and evaluated on the cells of a partition it gives the terms $\pi_k\int\varphi\,d\mathbb Q_k$ of (2.40).
--
--   **Formalization Note** Vertices are Boolean vectors and `boxVertex` maps them to points of $\Xi$; $\mathbb Q(v)$ is `genEMWeight`.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Lemma 2.7, (2.31), p.216 (PDF 225)

import Mathlib
import Definitions.Def_KallMayerSLP_RecourseBounds_genEMWeight

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **The generalized Edmundson–Madansky upper bound `Σ_ν φ(v^ν) Q(v^ν)`, (2.31).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Lemma 2.7, (2.31), printed p.216
(PDF 225): the right-hand side `Σ_{ν=1}^{2^r} φ(v^ν) Q(v^ν) = ∫_Ξ φ(η) Q(dη)` of the generalized
E–M inequality, the sum over the `2^r` vertices of the box `×ᵢ [aᵢ, bᵢ]`.

**Formalization Note.** Vertices are Boolean vectors (`NumStochOpt.Bounds.boxVertex`), `Q(v)` is
`genEMWeight μ a b v`. For `μ = IP_ξ.restrict Ξₖ` this is `πₖ ∫ φ dQ_k`, the `k`-th term of (2.40). -/
noncomputable def genEMBound {r : ℕ} (μ : Measure (Fin r → ℝ)) (a b : Fin r → ℝ)
    (φ : (Fin r → ℝ) → ℝ) : ℝ :=
  ∑ v : Fin r → Bool, genEMWeight μ a b v * φ (NumStochOpt.Bounds.boxVertex a b v)

end KallMayerSLP.RecourseBounds


