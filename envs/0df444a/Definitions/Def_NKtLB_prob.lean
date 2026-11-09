-- Prove2me | Definitions.Def_NKtLB_prob
-- name    : NKtLB_prob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:56:04.47746+00:00
-- url     : https://prove2.me/theorems/6e54ecd5-23bd-471c-8f6b-6ad896864aec
-- title:
--   Uniform probability over $\{0,1\}^r$
-- statement:
--   For a predicate $P$ on strings,
--   $$
--   \Pr_{w\sim U_r}[P(w)]=\frac{|\{w\in\{0,1\}^r : P(w)\}|}{2^r},
--   $$
--   where $U_r$ is the uniform distribution on $\{0,1\}^r$. A probability over independent uniform strings $(w,z)\sim U_r\times U_d$ is the uniform probability over $\{0,1\}^{r+d}$ of the split concatenation $w\circ z$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.1, p.21

import Mathlib

namespace NKtLB

/-- **Uniform probability over `{0,1}^r`** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §3.1, p.21: "We write `U_ℓ` for the uniform
distribution over `{0,1}^ℓ`"): `Pr_{w ∼ U_r}[P(w)] = |{w ∈ {0,1}^r : P(w)}| / 2^r`.
A probability over two independent uniform strings `(w, z) ∼ U_r × U_d` is `prob (r + d)` of the
split concatenation. -/
noncomputable def prob (r : ℕ) (P : List Bool → Prop) : ℝ :=
  (Set.ncard {w : List Bool | w.length = r ∧ P w} : ℝ) / 2 ^ r

end NKtLB


