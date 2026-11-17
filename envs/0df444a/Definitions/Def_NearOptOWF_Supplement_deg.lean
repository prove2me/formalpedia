-- Prove2me | Definitions.Def_NearOptOWF_Supplement_deg
-- name    : NearOptOWF_Supplement_deg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:05:26.200198+00:00
-- url     : https://prove2.me/theorems/57d5128c-ece5-43e7-bbc0-b1268cfbb5b5
-- title:
--   The degree $\deg_f(y) = |f^{-1}(y)|$
-- statement:
--   For a circuit $f$ with $n$ inputs and a string $y$, the **degree** of $y$ is the number of its pre-images in $\{0,1\}^n$:
--   $$
--   \deg_f(y) = \bigl|\{x\in\{0,1\}^n : f(x) = y\}\bigr| .
--   $$
--   It appears in the degree bounds of Theorems 4.3 and 5.3.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §3 Notations, p.8 (PDF p.10); Theorems 4.3 and 5.3, pp.13, 24 (PDF pp.15, 26)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF.Supplement

open LaconicBarrier

/-- The **degree** `deg_f(y) = |f⁻¹(y)|` of a string `y` under a circuit `f` with `n` inputs: the number
of inputs `x ∈ {0,1}ⁿ` with `f(x) = y` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §3 Notations, p.8 (PDF p.10); Theorems 4.3 and 5.3, pp.13, 24). -/
def deg {n : ℕ} (f : MCircuit n) (y : List Bool) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Bool => f.eval (bits x) = y).card

end NearOptOWF.Supplement


