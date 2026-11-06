-- Prove2me | Definitions.Def_SymNormLoad_countAbove
-- name    : SymNormLoad_countAbove
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:43.735207+00:00
-- url     : https://prove2.me/theorems/4b428c14-8819-456d-9e79-4211f02daaeb
-- title:
--   $N_x(t)=|\{i: x_i>t\}|$
-- statement:
--   For $x\in\mathbb R^M$ and $t\in\mathbb R$,
--   $$
--   N_x(t)=\bigl|\{i:\ x_i>t\}\bigr|,
--   $$
--   the number of coordinates of $x$ strictly above $t$. It is the integrand's argument in the upper bound of Lemma 2.2.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Lemma 2.2, p.9

import Mathlib

namespace SymNormLoad

/-- **`N_x(t) = |{i : x_i > t}|`.** Chen–Im–Sirri, *Online Load Balancing under Symmetric
Norms*, manuscript (STOC 2027 submission), Lemma 2.2, p.9: the number of coordinates of `x`
strictly above `t`. -/
noncomputable def countAbove {M : ℕ} (x : Fin M → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter (fun i => t < x i)).card

end SymNormLoad


