-- Prove2me | Definitions.Def_DetANN_HPIMLayout
-- name    : DetANN_HPIMLayout
-- status  : Definition
-- author  : @milia
-- created : 2026-11-16T06:35:41.407528+00:00
-- url     : https://prove2.me/theorems/d907b077-bf1a-4e5b-abd3-053bdb58543b
-- title:
--   The memory layout of HPIM trees in a PNormReg state
-- statement:
--   Let $s$ be a PNormReg state (definition `PNormReg_Machine`) with integer memory $I$ and real memory $R$.
--
--   1. A box decision tree $T$ (definition `DetANN_HPIMFormat`) is **stored at** $u$ if:
--      - for a leaf: $I[u]=0$, and $I[u+1]$ is $0$ for a null answer or $i+1$ for the answer $i$;
--      - for a test $[lo,hi]$: $I[u]=1$, the real address $a=I[u+1]\ge0$ holds $lo$ in $R[a..a+m-1]$ and $hi$ in $R[a+m..a+2m-1]$, and the *yes* and *no* subtrees are stored at $I[u+2]$ and $I[u+3]$.
--   2. An HPIM tree is **stored at** $v$ if:
--      - for a single point $k$: $I[v]=0$ and $I[v+1]=k$;
--      - for an inner node: $I[v]=1$, $I[v+1]=M$ and $I[v+6]=t_0$, the table of powers $I[I[3]+t]=2^t$ holds for $t\le t_0$, and the lookups, the global indices and the children are stored through the arrays at $I[v+2]$, $I[v+3]$ and $I[v+4]$; the representatives' child is at $I[v+5]$.
--
--   Every real address is $\ge0$, so the query cells $-1,\dots,-m$ never collide with the data. The table of powers lets the ladder search run without pointer division.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_HPIMFormat

/-!
# The memory layout of HPIM trees in a PNormReg state

`BoxTreeAt m s u T` and `HTreeAt m s v T` say that the box decision tree `T` (resp. the HPIM tree `T`,
definition `DetANN_HPIMFormat`) is stored in the state `s` from integer address `u` (resp. `v`).

* A box decision tree node at `u`: `I[u] = 0` for a leaf, with `I[u+1] = 0` (null) or `i + 1` (answer
  `i`); `I[u] = 1` for a test, with the real address `I[u+1] ≥ 0` of `lo` (`m` cells) followed by `hi`
  (`m` cells), and the addresses `I[u+2]`, `I[u+3]` of the *yes* and *no* subtrees.
* An HPIM node at `v`: `I[v] = 0` for a single point with global index `I[v+1]`; `I[v] = 1` for an inner
  node with `I[v+1] = M`, `I[v+6] = t₀`, the table of powers `I[I[3] + t] = 2^t` (`t ≤ t₀`), and arrays
  at `I[v+2]` (lookups), `I[v+3]` (global indices), `I[v+4]` (children); `I[v+5]` is the
  representatives' child.

Every real address is `≥ 0`, so the query cells `−1, …, −m` never collide with the data.
-/

namespace DetANN.HPIM

/-- `T` is laid out in state `s` at integer address `u` (`hpim_spec.md` §6, BoxTree format). -/
inductive BoxTreeAt (m : ℕ) (s : PNormReg.State) : ℤ → BoxTree m → Prop
  | leaf (u : ℤ) (a : Option ℕ) :
      s.integerMemory u = 0 →
      s.integerMemory (u + 1) = (match a with | none => 0 | some i => (i : ℤ) + 1) →
      BoxTreeAt m s u (.leaf a)
  | test (u : ℤ) (lo hi : Fin m → ℝ) (y n : BoxTree m) :
      s.integerMemory u = 1 → 0 ≤ s.integerMemory (u + 1) →
      (∀ j : Fin m, s.core.mem (s.integerMemory (u + 1) + j) = lo j) →
      (∀ j : Fin m, s.core.mem (s.integerMemory (u + 1) + m + j) = hi j) →
      BoxTreeAt m s (s.integerMemory (u + 2)) y → BoxTreeAt m s (s.integerMemory (u + 3)) n →
      BoxTreeAt m s u (.test lo hi y n)

/-- `T` is laid out in state `s` at integer address `v` (`hpim_spec.md` §6, HTree format). -/
inductive HTreeAt (m : ℕ) (s : PNormReg.State) : ℤ → HTree m → Prop
  | single (v : ℤ) (k : ℕ) :
      s.integerMemory v = 0 → s.integerMemory (v + 1) = k → HTreeAt m s v (.single k)
  | node (v : ℤ) (n M t₀ : ℕ) (Z : Fin M → BoxTree m) (glob : Fin n → ℕ)
      (kidOf : Fin n → HTree m) (reps : HTree m) :
      s.integerMemory v = 1 → s.integerMemory (v + 1) = M → s.integerMemory (v + 6) = t₀ →
      (∀ t ≤ t₀, s.integerMemory (s.integerMemory 3 + t) = 2 ^ t) →
      (∀ i : Fin M, BoxTreeAt m s (s.integerMemory (s.integerMemory (v + 2) + i)) (Z i)) →
      (∀ i : Fin n, s.integerMemory (s.integerMemory (v + 3) + i) = glob i) →
      (∀ i : Fin n, HTreeAt m s (s.integerMemory (s.integerMemory (v + 4) + i)) (kidOf i)) →
      HTreeAt m s (s.integerMemory (v + 5)) reps →
      HTreeAt m s v (.node n M t₀ Z glob kidOf reps)

end DetANN.HPIM


