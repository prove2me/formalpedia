-- Prove2me | Definitions.Def_NKtLB_Dense
-- name    : NKtLB_Dense
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:56:17.931798+00:00
-- url     : https://prove2.me/theorems/c30f06c1-89ab-4487-99c5-ff31d193e1e9
-- title:
--   Dense languages
-- statement:
--   A language $L$ is **dense** if there is a positive constant $b$ such that, for every large enough $n$,
--   $$
--   |L\cap\{0,1\}^n|\ \ge\ \frac{2^n}{n^b}.
--   $$
--
--
--   **Formalization Note** $b$ is a positive real and $n^b$ is the real power.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12

import Mathlib

namespace NKtLB

/-- **Dense languages** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12): "We say that a language `L` is dense if there is a
positive constant `b` such that, for every large enough `n`, we have `|L ∩ {0,1}^n| ≥ 2^n/n^b`."

**Formalization Note.** `b` is a positive real; `n^b` is the real power. -/
def Dense (L : Set (List Bool)) : Prop :=
  ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in Filter.atTop,
    (2 : ℝ) ^ n / (n : ℝ) ^ b ≤ (Set.ncard (L ∩ {x : List Bool | x.length = n}) : ℝ)

end NKtLB


