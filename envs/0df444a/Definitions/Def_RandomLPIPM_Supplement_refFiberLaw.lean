-- Prove2me | Definitions.Def_RandomLPIPM_Supplement_refFiberLaw
-- name    : RandomLPIPM_Supplement_refFiberLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:51:04.171652+00:00
-- url     : https://prove2.me/theorems/e8518d14-a095-4a8d-a4d8-ba4794391b13
-- title:
--   The reference law $\nu^0_x$ on the incidence fiber $F_x$
-- statement:
--   Fix $0<\mu<1$, $1\le k\le n-1$ and a point $x\in M_\mu^\circ$; put $s=\mu/x$ and
--   $$E_x=\{x-\mathbf 1,\,s-\mathbf 1\}^\perp,$$
--   a subspace of dimension $n-2$. The **incidence fiber** is $F_x=\{W\in\mathrm{Gr}(k,n): x-\mathbf 1\in W,\ s-\mathbf 1\in W^\perp\}$, and $W'\mapsto \mathrm{span}(x-\mathbf 1)\oplus W'$ identifies $\mathrm{Gr}(k-1,E_x)$ with $F_x$ isometrically. The **reference law** $\nu^0_x$ is the normalised Riemannian volume on $F_x$, that is, the law of
--   $$\mathrm{span}(x-\mathbf 1)\oplus W',\qquad W'\ \text{Haar distributed on } \mathrm{Gr}(k-1,E_x).$$
--
--   It is the law on the fiber against which the conditional law of the kernel is a tilt (Theorem 7.7), and it is the uniform-subspace law of Theorem 6.8 (Remark 7.8).
--
--   **Formalization Note** A subspace is represented by its orthogonal projector, so $\nu^0_x$ is a measure on $n\times n$ matrices. Haar measure on $\mathrm{Gr}(k-1,E_x)$ is realised by projecting $k-1$ independent standard Gaussian vectors of $\mathbb R^n$ onto $E_x$ and taking their span: the projected vectors are standard Gaussian in $E_x$, so the law of their span is invariant under the orthogonal group of $E_x$, and the span has dimension $k-1$ almost surely because $k-1\le n-2$. For $k=1$ the law is the point mass at $\mathrm{span}(x-\mathbf 1)$. The definition is applied only at points of $M_\mu^\circ$; the two excluded points form a null set for $\sigma_\mu$.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (100) and the incidence fiber, p.60; Proposition 7.1(ii) and the definition of ν⁰_x, p.61

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_RandomLPIPM_orthProj
import Definitions.Def_WainwrightHDS_NucNorm_projMat

open MeasureTheory

namespace RandomLPIPM.Supplement

/-- **The reference law `ν⁰_x` on the incidence fiber `F_x`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), §7.1 pp.60–61: for
`x ∈ M°_μ`, `s = μ/x`, `E_x = {x − 1, s − 1}^⊥` (100), and the incidence fiber is
`F_x = {W ∈ Gr(k, n) : x − 1 ∈ W, s − 1 ∈ W^⊥}`. By Proposition 7.1(ii), "`ν⁰_x` [the normalized
Riemannian volume on `F_x`] is the law of `span(x − 1) ⊕ W'` for `W'` Haar on `Gr(k − 1, E_x)`".

`refFiberLaw n k μ x` is that law, as a measure on orthogonal projector matrices `P_W` (functions
`Fin n → Fin n → ℝ`, with the Borel = product σ-algebra). Construction: let `Q` be the orthogonal
projector onto `E_x`, `g₁, …, g_{k−1}` the rows of `G` with independent `N(0,1)` entries, and
`W(G) = span({x − 1} ∪ {Q gᵢ : i < k − 1})`; `ν⁰_x` is the pushforward of the Gaussian law under
`G ↦ P_{W(G)}`.

**Formalization Note.** Mathlib has no Grassmannian; a subspace `W` is represented by its projector
`P_W` (`WainwrightHDS.NucNorm.projMat`), which identifies `Gr(k, n)` with a closed set of matrices
carrying its usual topology. Haar measure on `Gr(k − 1, E_x)` is realised as the span of `k − 1`
independent standard Gaussian vectors of `E_x` (the projections `Q gᵢ` are standard Gaussian in
`E_x`, and their law is invariant under the orthogonal group of `E_x`, hence so is the law of their
span; it has dimension `k − 1` almost surely since `k − 1 ≤ n − 2 = dim E_x` when `d ≥ 1`). This
is the device of the base mission's `RandomLPIPM.refProj`. `k` is the dimension `n − d` of
`ker A`; for `k = 1` no row is drawn and `ν⁰_x` is the point mass at `P_{span(x−1)}`. The
definition is used only for `x ∈ M°_μ` (the two excluded points are `σ_μ`-null). -/
noncomputable def refFiberLaw (n k : ℕ) (μ : ℝ) (x : Fin n → ℝ) : Measure (Fin n → Fin n → ℝ) :=
  let Q : (Fin n → ℝ) → (Fin n → ℝ) :=
    RandomLPIPM.orthProj
      (Submodule.span ℝ {WithLp.toLp 2 (x - 1), WithLp.toLp 2 ((fun i => μ / x i) - 1)})ᗮ
  let W : (Fin (k - 1) → Fin n → ℝ) → Submodule ℝ (EuclideanSpace ℝ (Fin n)) := fun G =>
    Submodule.span ℝ (insert (WithLp.toLp 2 (x - 1)) (Set.range fun i => WithLp.toLp 2 (Q (G i))))
  (GaussianMatrix.gaussianMatrix (k - 1) n).map
    (fun G => Matrix.of.symm (WainwrightHDS.NucNorm.projMat (W G)))

end RandomLPIPM.Supplement


