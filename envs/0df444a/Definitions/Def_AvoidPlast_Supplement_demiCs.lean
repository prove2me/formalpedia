-- Prove2me | Definitions.Def_AvoidPlast_Supplement_demiCs
-- name    : AvoidPlast_Supplement_demiCs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:04:32.45825+00:00
-- url     : https://prove2.me/theorems/898124cb-8a1e-4e54-afa4-1cf3739d557f
-- title:
--   The circuit $C_s(x,i)=g(x)\oplus s_i$
-- statement:
--   For a generator $g=\{g_n:\{0,1\}^{n-\lambda(n)}\to\{0,1\}^n\}$ and a tuple $s=(s_1,\dots,s_{t(n)})\in\{0,1\}^{t(n)\times n}$, the circuit
--   $$C_s(x,i)=g_n(x)\oplus s_i,$$
--   whose input is the seed $x$ followed by $i$ in $\lceil\log t(n)\rceil$ bits (least significant first); unused codes of $i$ are mapped to $s_1$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 6.5, 6.6, Corollary 6.7, pp.34–37

import Mathlib
import Definitions.Def_UniqueOptScores_decodeNat
import Definitions.Def_PPSLattice_xorStr
import Definitions.Def_AvoidPlast_Supplement_blockOf

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The circuit `C_s(x, i) = g(x) ⊕ s_i` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 6.5, p.34; Theorem 6.6, p.35;
Corollary 6.7, pp.36–37). For `s = (s_1, …, s_{t(n)}) ∈ {0,1}^{t(n)×n}`, the input `z` is the seed
`x` (its first `n - λ(n)` bits) followed by `i` in `⌈log t(n)⌉` bits (least significant first);
unused codes of `i` are mapped to `s_1` (block `0`). -/
def demiCs (g : ℕ → List Bool → List Bool) (lam t : ℕ → ℕ) (n : ℕ) (s z : List Bool) : List Bool :=
  let i := UniqueOptScores.decodeNat (z.drop (n - lam n))
  PPSLattice.xorStr (g n (z.take (n - lam n))) (blockOf s n (if i < t n then i else 0))

end AvoidPlast.Supplement


