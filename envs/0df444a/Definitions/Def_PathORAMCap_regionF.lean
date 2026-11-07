-- Prove2me | Definitions.Def_PathORAMCap_regionF
-- name    : PathORAMCap_regionF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:32.825134+00:00
-- url     : https://prove2.me/theorems/57869f83-9bcb-4271-864e-6b6f282581ee
-- title:
--   Local region fields $A^{\mathrm{disc}}_v$ and capped overflows $F_v$ of the capacity-three scan
-- statement:
--   Let $N=2^L$ and consider the full scan $\pi=P_{3,N}(N,(1,\dots,N))$. Number its blocks in **reverse** access order: reverse block $i$ is address $N-i+1$, and $\delta_i$ is its final target. For integers $H\ge1$, $K\ge1$, $0\le d\le L-H$, $1\le n\le N$ and a node $v$ of depth $d$, retain the targets of the first $n$ reverse blocks only when their relative depths below $v$ are $0,\dots,H-1$:
--
--   $$A^{\mathrm{disc}}_v(w)=\bigl|\{i\le n:\delta_i=w\}\bigr|\quad(v\preceq w,\ |w|-d\le H-1),$$
--
--   and set
--
--   $$F_v=\min\{K,\,D^{(3)}(A^{\mathrm{disc}}_v)\},$$
--
--   with $D^{(3)}$ evaluated on the $H$-level local tree rooted at $v$.
--
--   $F_v$ is the local surplus of a region that the lower bound compares with a capacity-three geometric-load tree.
--
--   **Formalization Note** Reverse block $i$ is the Lean block with value $N-i$, so the first $n$ reverse blocks are those with value at least $N-n$. The final target is the general target $d_N(b)$ of the scan.
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), §5.2.2, p.38 (PDF p.41), eqs. (43)–(44); §5, p.36 (PDF p.39)

import Mathlib
import Definitions.Def_PathORAMCap_overflowAux
import Definitions.Def_PathORAMCap_targetLoads

set_option autoImplicit false

namespace PathORAMCap

/-- The retained local load field `A^disc_v` of a region of the full scan (Chang, Au, *The Minimum
Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), §5.2.2,
p.38 (PDF p.41), (44)). The full scan is `π = P_{3,N}(N, (1, …, N))` with `N = 2^L` (§5's standing
setting, p.36 (PDF p.39)). For the region rooted at `v` (of depth `d`), retain "the targets of the
first n blocks in reverse scan order only when their relative depths below v are 0, . . . , H − 1":
`A^disc_v(w)` counts the reverse blocks `i ≤ n` whose final target `δ_i` (41) equals `w`, where
`v ⪯ w` and `|w| < |v| + H`.

**Formalization Note.** Reverse block `i` (`1 ≤ i ≤ N`) is address `N − i + 1`, i.e. `Fin N` value
`N − i`, so the first `n` reverse blocks are the `b` with `N − n ≤ b`. The final target is the general
target `d_N(b)` of (19) (`target`), at time `N` of the scan `α = id`. -/
def regionLoad (L H n : ℕ) (ω : Labels (2 ^ L) (2 ^ L)) (v w : List Bool) : ℕ :=
  (Finset.univ.filter (fun b : Fin (2 ^ L) =>
    2 ^ L - n ≤ b.val ∧ target (fun i => i) ω (2 ^ L) b = w ∧ v <+: w ∧
      w.length < v.length + H)).card

/-- The capped local overflow `F_v = min{K, D^(3)(A^disc_v)}` of (44), p.38 (PDF p.41), with `D^(3)`
evaluated on the `H`-level local tree rooted at `v`. -/
noncomputable def regionF (L H K n : ℕ) (ω : Labels (2 ^ L) (2 ^ L)) (v : List Bool) : ℝ :=
  min (K : ℝ) (overflowAux 3 H (fun w => (regionLoad L H n ω v w : ℝ)) v)

end PathORAMCap


