-- Prove2me | Definitions.Def_DerandSq_mGen
-- name    : DerandSq_mGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:56:54.209192+00:00
-- url     : https://prove2.me/theorems/24dd800d-73e7-4cd7-8f4d-de5b6bcdc489
-- title:
--   Generators $m_i$ of $\Gamma_d$
-- statement:
--   For $i \in [d]$, $m_i \in \Gamma_d$ is the nontrivial element of the $i$-th copy of $\mathbb Z_2$; these are the canonical involutive generators of $\Gamma_d$, $m_i^2 = e$.
--
--   **Formalization Note** Indices are `Fin d`. The module also records the structural fact $m_i m_i = e$.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Example 2.9, p.9 ($h_i$), §4.2, p.21 ($m_i$)

import Mathlib
import Definitions.Def_DerandSq_Gam

namespace DerandSq

/-- The canonical involutive generator `m_i ∈ Γ_d` (`h_i` in Example 2.9, p.9; `m_i` in §4.2,
p.21, of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0)): the nontrivial element of the `i`-th copy of `Z₂`. Indices are `Fin d`. -/
def mGen {d : ℕ} (i : Fin d) : Gam d :=
  Monoid.CoprodI.of (M := fun _ : Fin d => Multiplicative (ZMod 2)) (i := i)
    (Multiplicative.ofAdd (1 : ZMod 2))

/-- `m_i² = e`. -/
theorem mGen_mul_self {d : ℕ} (i : Fin d) : mGen i * mGen i = 1 := by
  unfold mGen
  rw [← map_mul, ← ofAdd_add]
  have : (1 + 1 : ZMod 2) = 0 := by decide
  rw [this, ofAdd_zero, map_one]

end DerandSq


