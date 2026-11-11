-- Prove2me | Definitions.Def_StabTestMem_conv
-- name    : StabTestMem_conv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:12.380397+00:00
-- url     : https://prove2.me/theorems/7cc2f761-9337-419e-b4cd-cb50f56c4c71
-- title:
--   Convolution $(f\star g)(x)=\sum_z f(z)g(x+z)$
-- statement:
--   For real functions $f,g$ on a finite additive group $V$ (in the paper $V=\mathbb F_2^{2n}$),
--
--   $$(f\star g)(x)=\sum_{z\in V} f(z)\,g(x+z).$$
--
--   The law of Bell difference sampling is $p_\psi\star p_\psi$.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §2.2, Eq. (16), p. 15

import Mathlib

namespace StabTestMem

/-- **Convolution of functions on a finite `F₂`-vector space.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §2.2, Eq. (16), p. 15:
"(f ⋆ g)(x) = Σ_{z∈F_2^n} [f(z) g(x + z)]".

Stated for any finite additive group `V`; the paper applies it on `F₂^{2n}` to `p_ψ ⋆ p_ψ`. -/
def conv {V : Type*} [Fintype V] [Add V] (f g : V → ℝ) (x : V) : ℝ :=
  ∑ z, f z * g (x + z)

end StabTestMem


