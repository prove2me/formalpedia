-- Prove2me | Definitions.Def_ErasureQTanner_uniformAvg
-- name    : ErasureQTanner_uniformAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:48.23626+00:00
-- url     : https://prove2.me/theorems/8559375e-24d9-4f82-aa71-90f7ea57bf6b
-- title:
--   Expectation over a uniform random linear code
-- statement:
--   A **uniform random linear code** of length $n$ and dimension $k$ is a uniformly chosen $k$-dimensional subspace of $\mathbb F_2^n$. This item defines the expectation of a real function and the probability of an event under it, as finite averages over all such subspaces.
--
--   **Formalization Note** The average is over subspaces and not over generator matrices, which would have a rank defect. When $k>n$ there is no subspace and the value is $0/0=0$: statements either bound $k$ by $n$ or take $n$ large enough that the rate does.
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), §9, p.19 (Lemma 9, and the proof of Corollary 10)

import Mathlib

set_option autoImplicit false

namespace ErasureQTanner

/-- A binary linear code of length `n`. -/
abbrev Code (n : ℕ) := Submodule (ZMod 2) (Fin n → ZMod 2)

/-- The linear codes of length `n` and dimension `k`. -/
abbrev RandCode (n k : ℕ) := {W : Code n // Module.finrank (ZMod 2) W = k}

noncomputable instance (n k : ℕ) : Fintype (RandCode n k) := Fintype.ofFinite _

/-- The expectation of `f` under a uniformly random linear code of length `n` and dimension `k`: Pfister, Sprumont,
Zémor, STOC 2027 submission (manuscript sha256 bf7a84a5…), §9, p.19 (Corollary 10's proof: "uniformly among
subspaces").

**Formalization Note.** Uniform over subspaces, not over generator matrices, which would have a rank defect. At
`k > n` no code exists and the value is `0/0 = 0`; every statement using this bounds `k` by `n`, or takes `n` large
enough that its rate bound does. -/
noncomputable def uniformAvg (n k : ℕ) (f : Code n → ℝ) : ℝ :=
  (∑ W : RandCode n k, f W.1) / Fintype.card (RandCode n k)

open Classical in
/-- The probability of an event under a uniformly random linear code of length `n` and dimension `k`. -/
noncomputable def uniformProb (n k : ℕ) (E : Code n → Prop) : ℝ :=
  uniformAvg n k fun C => if E C then 1 else 0

end ErasureQTanner


