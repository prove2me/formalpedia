-- Prove2me | Definitions.Def_KSPolySign_coupling
-- name    : KSPolySign_coupling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:02.840537+00:00
-- url     : https://prove2.me/theorems/506406a4-4c74-4350-a98a-538d088eabe4
-- title:
--   The coupling $K_y(D)=\iota\sum_i\beta(y_i)C_iDC_i$
-- statement:
--   For $y\in[-1,1]^k$ and a Hermitian matrix $D$,
--   $$K_y(D) = \iota \sum_{i=1}^k \beta(y_i)\, C_i D C_i,$$
--   with $\iota=3.03$ and $\beta(t)=\sqrt{1-t^2}$. It couples the two barrier constraints of the potential; a signed coordinate ($|y_i|=1$) contributes nothing.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.2, p.18 (PDF p.18); Definition 3.5, p.19 (PDF p.19)

import Mathlib
import Definitions.Def_KSPolySign_iota
import Definitions.Def_KSPolySign_beta
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The coupling `K_y(D) = ι ∑_i β(y_i) C_i D C_i`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.2, p.18 (PDF p.18):
"K_y(D) := ι ∑_i β(y_i) Ā_i D Ā_i"; Definition 3.5, p.19: "with C_i in place of Ā_i". -/
noncomputable def coupling {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (y : Fin k → ℝ)
    (D : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((iota : ℝ) : ℂ) • ∑ i, ((beta (y i) : ℝ) : ℂ) • (C i * D * C i)

end KSPolySign


