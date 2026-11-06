-- Prove2me | Definitions.Def_SymNormLoad_pen
-- name    : SymNormLoad_pen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:46.805129+00:00
-- url     : https://prove2.me/theorems/05899b79-4e3c-4650-8e20-6f8cac7550e4
-- title:
--   Penalty $g(t)=\exp(h(t))$
-- statement:
--   For a load transform $h$, one machine's **penalty** at load $t$ is
--   $$
--   g(t)=\exp(h(t)).
--   $$
--   Since $h(0)=0$, $g(0)=1$.
--
--   **Formalization Note** Defined for any function $h:\mathbb R\to\mathbb R$; the theorems take $h$ to be a load transform.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Section 2.1.2, p.10

import Mathlib

namespace SymNormLoad

/-- **One machine's penalty `g(t) = exp(h(t))`.** Chen–Im–Sirri, *Online Load Balancing under
Symmetric Norms*, manuscript (STOC 2027 submission), §2.1.2, p.10: "Write `g(t) = exp(h(t))` for
one machine's penalty."

**Formalization Note** `h` is any function `ℝ → ℝ`; the theorems take `h` to be a load transform
(`IsLoadTransform`). -/
noncomputable def pen (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (h t)

end SymNormLoad


