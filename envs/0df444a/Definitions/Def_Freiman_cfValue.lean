-- Prove2me | Definitions.Def_Freiman_cfValue
-- name    : Freiman_cfValue
-- status  : Definition
-- author  : @tp
-- created : 2026-09-08T23:21:10.172918+00:00
-- url     : https://prove2.me/theorems/2fc23c02-52c4-475d-8bfe-b3eb7fa587c7
-- title:
--   Continued fractions and Perron values
-- statement:
--   For a finite word of positive integers, define its continued fraction recursively by
--   $$
--   F(\varnothing)=0,\qquad
--   F(bw)=\frac{1}{b+F(w)}.
--   $$
--   For a sequence $b=(b_n)_{n\ge0}$ of positive integers, let
--   $$
--   C_n(b)=F(b_0\cdots b_{n-1}),\qquad
--   C(b)=\sup_{n\ge0}C_{2n}(b).
--   $$
--   Thus $C_0(b)=0$. The convergence theorem identifies $C(b)$ with the infinite continued fraction $[0;b_0,b_1,\ldots]$.
--
--   The Perron values are
--   $$
--   P_n(b)=b_n+F(b_{n-1}\cdots b_0)
--             +C\bigl((b_{n+1+k})_{k\ge0}\bigr),\qquad n\ge0.
--   $$
--   The finite backward term is zero when $n=0$. These values relate continued fractions to rational approximation.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, p. 7, equations (1.1)–(1.2), and Theorem 1.2, p. 8. Digits are indexed from 0 in this declaration; the report indexes them from 1. The supremum of even convergents is the defining realization of the infinite value; its agreement with the limit is a separate theorem.

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.PNat.Defs

namespace Freiman

noncomputable def finiteCF : List ℕ+ → ℝ
  | [] => 0
  | b :: w => 1 / (((b : ℕ) : ℝ) + finiteCF w)

noncomputable def cfConvergent (b : ℕ → ℕ+) (n : ℕ) : ℝ :=
  finiteCF ((List.range n).map b)

noncomputable def cfValue (b : ℕ → ℕ+) : ℝ :=
  sSup (Set.range (fun n : ℕ => cfConvergent b (2 * n)))

noncomputable def perronValue (b : ℕ → ℕ+) (n : ℕ) : ℝ :=
  ((b n : ℕ) : ℝ) + finiteCF (((List.range n).map b).reverse) +
    cfValue (fun k : ℕ => b (n + 1 + k))

end Freiman


