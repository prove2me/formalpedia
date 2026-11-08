-- Prove2me | Definitions.Def_AvoidPlast_Lpad
-- name    : AvoidPlast_Lpad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:58.022063+00:00
-- url     : https://prove2.me/theorems/4d999f29-0363-44a1-bebd-c0124e7c4745
-- title:
--   The padded language $L_{pad}$
-- statement:
--   The padded language of the proof of Theorem 5.14: the strings $xy$ with $|y|=\lceil|x|^{k/\alpha}\rceil$. The page's $L$, "the language that simulates $F$ and accepts", contains every string since $F$ halts everywhere, so only the length condition remains.
--
--   **Formalization Note** The pair $(x,y)$ is plain concatenation, as in the page's "the string $xy$ belongs to $L_{pad}$". The map $n\mapsto n+\lceil n^{k/\alpha}\rceil$ is strictly increasing, so $|z|$ determines $|x|$, and $|x|\le|(x,y)|^{\alpha/k}$ follows.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Proof of Theorem 5.14, (2)⇒(1), p.30

import Mathlib
import Definitions.Def_AvoidPlast_padLen

namespace AvoidPlast

/-- The padded language `L_pad` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), proof of Theorem 5.14, (2)⇒(1), p.30): the strings `xy` with
`|y| = ⌈|x|^{k/α}⌉`. Here `L` is "the language that simulates `F` and accepts", which contains every
string since `F` halts everywhere.

**Formalization Note** The pair `(x, y)` is plain concatenation, as the page's "the string `xy` belongs
to `L_pad`" has it. `n ↦ n + ⌈n^{k/α}⌉` is strictly increasing, so `|z|` determines `|x|`; and
`|x| ≤ |(x, y)|^{α/k}` follows. -/
def Lpad (k : ℕ) (α : ℚ) : Set (List Bool) :=
  {z | ∃ x y : List Bool, z = x ++ y ∧ y.length = padLen k α x.length}

end AvoidPlast


