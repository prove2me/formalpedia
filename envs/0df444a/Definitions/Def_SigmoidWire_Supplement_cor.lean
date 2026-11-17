-- Prove2me | Definitions.Def_SigmoidWire_Supplement_cor
-- name    : SigmoidWire_Supplement_cor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:39:22.498205+00:00
-- url     : https://prove2.me/theorems/225eaa01-ec14-475f-9c4d-4b2461c913cc
-- title:
--   Correlation $\mathrm{Cor}(f,g)$ of two Boolean functions (Definition 3.5)
-- statement:
--   For Boolean functions $f,g:\{0,1\}^n\to\{0,1\}$, the **correlation** is the bias of their agreement probability under a uniformly random input:
--   $$\mathrm{Cor}(f,g)=\Big|\Pr_{x\leftarrow\{0,1\}^n}[f(x)=g(x)]-\tfrac12\Big|.$$
--
--   It measures how well $f$ approximates $g$ or its complement; the parity-correlation bound of Theorem 5.19 is stated with it.
--
--   **Formalization Note** The probability is the number of agreeing points divided by $2^n$.
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Definition 3.5, p.15

import Mathlib

namespace SigmoidWire.Supplement

open Classical in
/-- **Correlation of two Boolean functions** (Definition 3.5).

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Definition 3.5, p.15
(PDF p.17): "Cor(f, g) := |Pr_{x←{0,1}^n}[f(x) = g(x)] − 1/2|".

**Formalization Note.** The probability is over the uniform distribution on `{0,1}^n`, i.e. the
number of agreeing points divided by `2^n`. -/
noncomputable def cor {n : ℕ} (f g : (Fin n → Bool) → Bool) : ℝ :=
  |((Finset.univ.filter fun x : Fin n → Bool => f x = g x).card : ℝ) / 2 ^ n - 1 / 2|

end SigmoidWire.Supplement


