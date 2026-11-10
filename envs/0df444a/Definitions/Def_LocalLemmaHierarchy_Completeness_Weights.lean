-- Prove2me | Definitions.Def_LocalLemmaHierarchy_Completeness_Weights
-- name    : LocalLemmaHierarchy_Completeness_Weights
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:17:40.13065+00:00
-- url     : https://prove2.me/theorems/f70ce843-8000-43ce-b328-f4fab3d69c6b
-- title:
--   Weighted geometric means, the discrete Dirichlet energy $E_q$, $d_q$ and the sine weights
-- statement:
--   For a probability vector $\alpha$ on a finite index set, $\mathrm{GM}_\alpha(z)=\prod_i z_i^{\alpha_i}$, omitting factors whose exponent is zero and interpreting boundary values by continuity (App. F.1). For weights $w_1,\dots,w_q$ extended by $w_0=w_{q+1}=0$, the **discrete Dirichlet energy** is $E_q(w)=\sum_{i=0}^{q}(\sqrt{w_{i+1}}-\sqrt{w_i})^2$ (App. F.2). Further $d_q=2(1-\cos(\pi/(q+1)))$ and the **sine weights** are $w_j=\frac{2}{q+1}\sin^2(j\pi/(q+1))$ (F.6).
--
--   **Formalization Note.** $\mathrm{GM}$ uses `Real.rpow`, for which $0^0=1$ (so zero exponents are omitted) and $0^a=0$ for $a>0$ (the boundary value by continuity). Weights are functions `ℕ → ℝ`; `extWeights q w` is $w_i$ for $1\le i\le q$ and $0$ otherwise.
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), App. F.1 (GM, printed p. 36 / PDF 38) and F.2 ($E_q$, printed p. 37 / PDF 39; $d_q$, (F.6), printed p. 38 / PDF 40)

import Mathlib

namespace LocalLemmaHierarchy.Completeness

/-- The weighted geometric mean `GM_α(z) = ∏_i z_i^{α_i}` of App. F.1 (printed p. 36 / PDF 38), with
`Real.rpow`. Factors with exponent `0` equal `1` (`0^0 = 1`), so they are in effect omitted, and a
zero coordinate with a positive exponent gives `0`: this is the boundary value by continuity. -/
noncomputable def geomMean {ι : Type} [Fintype ι] (α z : ι → ℝ) : ℝ :=
  ∏ i, z i ^ α i

/-- The extension of weights `w_1, …, w_q` by `w_0 = w_{q+1} = 0` (and `0` beyond). -/
noncomputable def extWeights (q : ℕ) (w : ℕ → ℝ) (i : ℕ) : ℝ :=
  if 1 ≤ i ∧ i ≤ q then w i else 0

/-- The discrete Dirichlet energy of App. F.2 (printed p. 37 / PDF 39):
`E_q(w) = ∑_{i=0}^{q} (√w_{i+1} − √w_i)²` with `w_0 = w_{q+1} = 0`. -/
noncomputable def dirichletEnergy (q : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (q + 1),
    (Real.sqrt (extWeights q w (i + 1)) - Real.sqrt (extWeights q w i)) ^ 2

/-- `d_q = 2(1 − cos(π/(q+1)))` (Theorem 3.9, App. F). -/
noncomputable def dq (q : ℕ) : ℝ :=
  2 * (1 - Real.cos (Real.pi / ((q : ℝ) + 1)))

/-- The sine weights (F.6): `w_j = (2/(q+1)) sin²(jπ/(q+1))`. -/
noncomputable def sineWeight (q j : ℕ) : ℝ :=
  2 / ((q : ℝ) + 1) * Real.sin ((j : ℝ) * (Real.pi / ((q : ℝ) + 1))) ^ 2

end LocalLemmaHierarchy.Completeness


