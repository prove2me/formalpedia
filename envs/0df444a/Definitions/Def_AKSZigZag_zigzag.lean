-- Prove2me | Definitions.Def_AKSZigZag_zigzag
-- name    : AKSZigZag_zigzag
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:09.946877+00:00
-- url     : https://prove2.me/theorems/c72416a0-12af-460b-8c22-9411a5747625
-- title:
--   The zig-zag sorting network
-- statement:
--   Fix $A$, a number $a$ of ZigZag repetitions, and a family of networks $\mathrm{ns}_m$ on $m$ registers ($\varepsilon$-nearsorts in the paper).
--
--   1. The **Zig step** of cycle $t$ runs $\mathrm{ns}_{|P|}$ simultaneously inside every part $P$ of $P_{t1}$.
--   2. The **Zag step** of cycle $t$ does the same for the parts of $P_{t2}$.
--   3. The **$t$-cycle** is Zig, Zag, Zig, Zag, …, $a$ times each.
--   4. The **algorithm** first applies $\mathrm{ns}_n$ to all registers, then performs the cycles $t=1,2,\dots,\log_2 n$.
--
--   The module defines the Zig and Zag steps of a cycle as networks, the algorithm up to the end of cycle $t$ (the configuration "after a completed cycle" in §8), and the whole **zig-zag network**.
--
--   Its depth is the depth of $\mathrm{ns}_n$ plus, for each of the $\log_2 n$ cycles, $a$ times the largest Zig depth plus the largest Zag depth.
--
--   **Formalization Note** Networks in different parts of a partition share parallel steps. $\log$ is `Nat.log 2`, which is exact on powers of $2$.
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §6, p.6 (ZigZag repeated a times), §7, p.7 (Zig step, Zag step, t-cycle, the whole algorithm)

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork
import Definitions.Def_AKSZigZag_NetworkOps
import Definitions.Def_AKSZigZag_RegisterAssignment

namespace AKSZigZag

open AKSSorting.Core

/-- The layers of the **Zig step** of cycle `t` (AKS, STOC 1983, §7, p.7): the ε-nearsort
`ns |P|` applied simultaneously within every part `P` of `P_t1`. -/
def zigLayers (A : ℕ) (ns : (m : ℕ) → ComparatorNetwork m) (n t : ℕ) :
    List (List (Fin n × Fin n)) :=
  parallelLayers ns (partition1 A n t)

/-- The layers of the **Zag step** of cycle `t`: the same within the parts of `P_t2`. -/
def zagLayers (A : ℕ) (ns : (m : ℕ) → ComparatorNetwork m) (n t : ℕ) :
    List (List (Fin n × Fin n)) :=
  parallelLayers ns (partition2 A n t)

/-- The layers of the **t-cycle** (AKS, STOC 1983, §7, p.7): "the application of ε-nearsort
simultaneously within the parts of Pt1 (Zig step), then the same for Pt2 (Zag step), then repeat
this alternately for Pt1 and Pt2, altogether a times each." -/
def cycleLayers (A a : ℕ) (ns : (m : ℕ) → ComparatorNetwork m) (n t : ℕ) :
    List (List (Fin n × Fin n)) :=
  (List.replicate a (zigLayers A ns n t ++ zagLayers A ns n t)).flatten

/-- The layers of the algorithm up to the end of cycle `t` (AKS, STOC 1983, §7, p.7): "The
whole algorithm starts with an ε-nearsort applied to the whole set of registers 1,2,...,n, then
the t-cycles are performed for t = 1,2,...,log n." `runLayers … 0` is the initial ε-nearsort. -/
def runLayers (A a : ℕ) (ns : (m : ℕ) → ComparatorNetwork m) (n t : ℕ) :
    List (List (Fin n × Fin n)) :=
  parallelLayers ns [Finset.univ] ++
    ((List.range t).map fun s => cycleLayers A a ns n (s + 1)).flatten

/-- One Zig step of cycle `t`, as a comparator network. -/
noncomputable def zigNet (A : ℕ) (ns : (m : ℕ) → ComparatorNetwork m) (n t : ℕ) :
    ComparatorNetwork n :=
  mkNet (zigLayers A ns n t)

/-- One Zag step of cycle `t`, as a comparator network. -/
noncomputable def zagNet (A : ℕ) (ns : (m : ℕ) → ComparatorNetwork m) (n t : ℕ) :
    ComparatorNetwork n :=
  mkNet (zagLayers A ns n t)

/-- The algorithm run up to the end of cycle `t` (`t = 0`: the initial ε-nearsort only), as a
comparator network. -/
noncomputable def runNet (A a : ℕ) (ns : (m : ℕ) → ComparatorNetwork m) (n t : ℕ) :
    ComparatorNetwork n :=
  mkNet (runLayers A a ns n t)

/-- **The zig-zag sorting network** of AKS, STOC 1983, §§5–7, with parameter `A`, `a` ZigZag
repetitions per cycle and the ε-nearsort family `ns` (`ns m` a network on `m` registers): the
initial ε-nearsort, then the cycles `t = 1, …, log₂ n`.

**Formalization Note.** A network on `m = |P|` registers is run inside a part `P` through the
registers of `P` in increasing order; networks in different parts of a partition run in the same
parallel steps. `log` is `Nat.log 2`, exact for the powers of 2 the paper assumes. -/
noncomputable def zigzag (A a : ℕ) (ns : (m : ℕ) → ComparatorNetwork m) (n : ℕ) :
    ComparatorNetwork n :=
  runNet A a ns n (Nat.log 2 n)

end AKSZigZag


