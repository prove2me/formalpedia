-- Prove2me | Definitions.Def_QPSpinParisi_Xn
-- name    : QPSpinParisi_Xn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:42.290972+00:00
-- url     : https://prove2.me/theorems/f5677b0b-b79b-477c-91e9-69a9cc71aa4d
-- title:
--   The classical field $X_n$ on $(S^2)^n$
-- statement:
--   For $s=(s_1,\dots,s_n)\in(S^2)^n$,
--   $$X_{n,p}(s)=\sqrt{\frac n{\binom np}}\sum_{i_1<\dots<i_p}\sum_{\bar a\in[3]^p}\alpha[\bar i,\bar a]\prod_{j=1}^ps^{a_j}_{i_j},\qquad X_n(s)=\sum_{p=2}^nc_pX_{n,p}(s).$$
--   By Lemma 3.1 it equals $\sqrt n\langle\phi|H_n|\phi\rangle$ at the Bloch vectors of a product state.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.1, p.10 (PDF p.10)

import Mathlib
import Definitions.Def_QPSpinParisi_coef
import Definitions.Def_QPSpinParisi_E3
import Definitions.Def_RGGDetect_unifSphere

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The classical field `X_n(s) = ∑_{p=2}^n c_p X_{n,p}(s)`, with
`X_{n,p}(s) = √(n / binom(n,p)) ∑_{i₁<⋯<i_p} ∑_ā α[ī, ā] ∏_j s^{a_j}_{i_j}` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.1, p.10, PDF p.10).

**Formalization Note** `√(n / N) = √n · N^{-1/2}`, and the double sum is one sum over `Idx n`. `RGGDetect.Config n 3`
is `(S²)ⁿ`. -/
noncomputable def Xn (c : ℕ → ℝ) (n : ℕ) (α : Idx n → ℝ) (s : RGGDetect.Config n 3) : ℝ :=
  Real.sqrt n * ∑ i : Idx n, coef c i * α i * ∏ j : ↥i.1.1, (s j.1).1 (i.2 j)

end QPSpinParisi


