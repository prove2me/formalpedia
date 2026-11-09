-- Prove2me | Definitions.Def_CutRankSched_signature
-- name    : CutRankSched_signature
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:33:01.122244+00:00
-- url     : https://prove2.me/theorems/8b5acaf5-7694-4b22-a0d4-8889139cca70
-- title:
--   Future-visible anticommutation signature $a^{(k)}_j$
-- statement:
--   For a processed event $j \le k$, its **future-visible anticommutation signature** at cut $k$ is the row vector
--   $$
--   a^{(k)}_j = (A_{j,k+1}, \dots, A_{j,n}) \in \mathbb F_2^{\,n-k} .
--   $$
--   The vector $b_i = (A_{i,i+1}, \dots, A_{i,n})$ used by the update (11) is the signature of event $i$ at cut $i$.
--
--   **Formalization Note** The signature is zero-padded into $\mathbb F_2^n$: coordinate $c$ holds $A_{jc}$ for the columns $c$ after the cut and $0$ before it. The embedding $\mathbb F_2^{n-k} \hookrightarrow \mathbb F_2^n$ is linear and injective, so spans, dimensions and kernels of coordinate functionals are unchanged.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.3, p.5; Section 5.3, p.9

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_A

set_option autoImplicit false

namespace CutRankSched

/-- The future-visible anticommutation signature `a^{(k)}_j = (A_{j,k+1}, …, A_{j,n}) ∈ 𝔽₂^{n−k}`
of an event `j` at cut `k` (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.3, p.5).

**Formalization Note** The vector is zero-padded into `𝔽₂^n`: coordinate `c` holds `A_jc` when
`k ≤ c.val` (the paper's columns `k+1, …, n`) and `0` otherwise. This embedding `𝔽₂^{n−k} ↪ 𝔽₂^n`
is linear and injective, so spans, dimensions and kernels of coordinate functionals are
unchanged. The vector `b_i = (A_{i,i+1}, …, A_{i,n})` of §5.3 (p.9) is `signature I (i.val+1) i`. -/
def signature (I : Instance) (k : ℕ) (j : Fin I.n) : Fin I.n → ZMod 2 :=
  fun c => if k ≤ c.val then A I j c else 0

end CutRankSched


