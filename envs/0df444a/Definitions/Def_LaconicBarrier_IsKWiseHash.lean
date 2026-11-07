-- Prove2me | Definitions.Def_LaconicBarrier_IsKWiseHash
-- name    : LaconicBarrier_IsKWiseHash
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:27.458847+00:00
-- url     : https://prove2.me/theorems/3f0a6a1b-cd35-4c6f-9b1c-19b6965a442b
-- title:
--   $k$-wise independent hash families
-- statement:
--   An indexed hash family $(h_s)_{s \in \{0,1\}^u}$ of functions $h_s : \{0,1\}^R \to \{0,1\}^b$ is **$k$-wise independent** if for every $1 \le q \le \min\{k, 2^R\}$, all distinct $x_1, \dots, x_q \in \{0,1\}^R$ and all $y_1, \dots, y_q \in \{0,1\}^b$,
--   $$
--   \Pr_{s \leftarrow \{0,1\}^u}\bigl[h_s(x_j) = y_j \text{ for all } j \in [q]\bigr] = 2^{-bq}.
--   $$
--   In particular the hash values are uniform as well as independent.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.35, p.29

import Mathlib

namespace LaconicBarrier

/-- A **`k`-wise independent hash family** (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript
sha256 1af78662…), Definition 4.35, p.29, after [Vad12, Definition 3.31]): the indexed family
`(h_s)_{s ∈ {0,1}^u}` of functions `{0,1}^R → {0,1}^b` satisfies, for every `1 ≤ q ≤ min{k, 2^R}`,
distinct `x₁, …, x_q ∈ {0,1}^R` and any `y₁, …, y_q ∈ {0,1}^b`,
`Pr_{s ← {0,1}^u}[h_s(x_j) = y_j for all j ∈ [q]] = 2^{−bq}`. -/
def IsKWiseHash {u R b : ℕ} (h : (Fin u → Bool) → (Fin R → Bool) → (Fin b → Bool)) (k : ℕ) :
    Prop :=
  ∀ q : ℕ, 1 ≤ q → q ≤ min k (2 ^ R) → ∀ xs : Fin q → (Fin R → Bool), Function.Injective xs →
    ∀ ys : Fin q → (Fin b → Bool),
      ((Finset.univ.filter fun s => ∀ j, h s (xs j) = ys j).card : ℝ) / 2 ^ u =
        ((2 : ℝ) ^ (b * q))⁻¹

end LaconicBarrier


