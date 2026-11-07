-- Prove2me | Definitions.Def_QMCBeyondHK_swapMap
-- name    : QMCBeyondHK_swapMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:28.858974+00:00
-- url     : https://prove2.me/theorems/e6860d25-7fd4-45d4-a467-1a83618425cb
-- title:
--   The half-swap map $T$ of the symmetry argument
-- statement:
--   Let $j \ge 1$, $0 \le k < 2^{j-1}$, $I = [k 2^{-(j-1)}, (k+1) 2^{-(j-1)})$ the support of $h_{j,k}$, and $I_+$, $I_-$ its left and right halves. The one-dimensional map $T_i$ sends $y \mapsto y + 2^{-j}$ on $I_+$, $y \mapsto y - 2^{-j}$ on $I_-$, and fixes every other point. For a coordinate $i \in [d]$, the map $T : [0,1)^d \to [0,1)^d$ is
--   $$
--   T(y)_r = y_r \ (r \ne i), \qquad T(y)_i = T_i(y_i),
--   $$
--   which swaps the two halves of $I$ in coordinate $i$.
--
--   It is the involution used to prove that distinct low-order Haar discrepancies are uncorrelated.
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), proof of Lemma 3.1.1, 'The Map T', p.10 (PDF p.12)

import Mathlib

set_option autoImplicit false

namespace QMCBeyondHK

/-- The one-dimensional map `T_i` of the proof of Lemma 3.1.1 (arXiv:2609.10921, sha256 bc273e88…,
p.10, PDF p.12): with `I = [k 2^{−(j−1)}, (k+1) 2^{−(j−1)})` and its left and right halves `I₊`,
`I₋`, it maps `y ↦ y + 2^{−j}` on `I₊`, `y ↦ y − 2^{−j}` on `I₋`, and fixes everything else. -/
noncomputable def swapHalves (j k : ℕ) (y : ℝ) : ℝ :=
  if (k : ℝ) / 2 ^ (j - 1) ≤ y ∧ y < (k : ℝ) / 2 ^ (j - 1) + 1 / 2 ^ j then y + 1 / 2 ^ j
  else if (k : ℝ) / 2 ^ (j - 1) + 1 / 2 ^ j ≤ y ∧ y < ((k : ℝ) + 1) / 2 ^ (j - 1) then y - 1 / 2 ^ j
  else y

/-- The map `T : [0,1)^d → [0,1)^d` of the proof of Lemma 3.1.1 (arXiv:2609.10921,
sha256 bc273e88…, p.10, PDF p.12): `T(y)_r = y_r` for `r ≠ i` and `T(y)_i = T_i(y_i)`, which swaps
the two halves of `I = supp h_{j,k}` in coordinate `i`. -/
noncomputable def swapMap {d : ℕ} (i : Fin d) (j k : ℕ) (y : Fin d → ℝ) : Fin d → ℝ :=
  Function.update y i (swapHalves j k (y i))

end QMCBeyondHK


