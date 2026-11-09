-- Prove2me | Definitions.Def_KSPolySign_Msum
-- name    : KSPolySign_Msum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:30:19.729857+00:00
-- url     : https://prove2.me/theorems/ebb92a00-6354-4bcb-bb56-c200b0a5ea38
-- title:
--   The modeled matrix sum $M(y)=F+\sum_i y_iC_i$
-- statement:
--   For Hermitian matrices $C_1,\dots,C_k\in\mathbb C^{n\times n}$, a fixed Hermitian matrix $F$ and a fractional signing $y\in[-1,1]^k$, the **modeled sum** is
--   $$M(y) = F + \sum_{i=1}^k y_i C_i.$$
--   For the normalized inputs of Lemma 3.1 it is $M(y)=\sum_i y_i\bar A_i$ (Definition 3.2, $F=0$); on a retained face of the algorithm $F$ is the fixed contribution of the signed coordinates (Definition 3.5).
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.2, p.18 (PDF p.18); Definition 3.5, p.19 (PDF p.19)

import Mathlib
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The modeled matrix sum `M(y) = F + ∑_i y_i C_i`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.2, p.18 (PDF p.18):
"M(y) := ∑_i y_i Ā_i"; Definition 3.5, p.19 (PDF p.19): "M(y) := F + ∑_{i∈I} y_i C_i".

**Formalization Note** Stated for the maintained instance of Definition 3.5; the normalized
inputs of Definition 3.2 are the case `F = 0`, `C_i = Ā_i`. -/
noncomputable def Msum {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ)
    (y : Fin k → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  F + ∑ i, ((y i : ℝ) : ℂ) • C i

end KSPolySign


