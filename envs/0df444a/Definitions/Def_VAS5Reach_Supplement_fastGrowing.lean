-- Prove2me | Definitions.Def_VAS5Reach_Supplement_fastGrowing
-- name    : VAS5Reach_Supplement_fastGrowing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:47:49.799875+00:00
-- url     : https://prove2.me/theorems/49337807-df21-4f6a-babb-2f67c1ec0462
-- title:
--   Fast-growing functions $F_k$ and the class $\mathbf F_d$
-- statement:
--   The **fast-growing functions** $F_k:\mathbb N\to\mathbb N$ are defined by
--   $$F_0(x)=x+1,\qquad F_{k+1}(x)=F_k^{\,x+1}(x),$$
--   the $(x+1)$-fold iterate of $F_k$ applied to $x$; so $F_1(x)=2x+1$ and $F_2(x)=2^{x+1}(x+1)-1$.
--
--   For $d\ge3$ the **fast-growing complexity class** $\mathbf F_d$ of Schmitz is
--   $$\mathbf F_d=\bigcup_{p\in\mathscr F_{<d}}\mathrm{DTIME}\big(F_d(p(n))\big),$$
--   the languages decided by a deterministic multitape Turing machine within $F_d(p(n))$ steps for some $p$ in the Löb–Wainer class $\mathscr F_{<d}=\mathscr F_{d-1}$. Equivalently, some deterministic machine decides the language within $F_d(F_{d-1}^{\,c}(n))$ steps on inputs of length $n$, for some $c\in\mathbb N$; this is how membership is stated. $\mathbf F_3$ is the class TOWER.
--
--   This is the class of Theorem 1.5.
--
--   **Formalization Note** Every $p\in\mathscr F_{d-1}$ is bounded by an iterate $F_{d-1}^{\,c}$ and every such iterate lies in $\mathscr F_{d-1}$, so the two unions coincide. Machines are deterministic machines of the published `SpaceMachine` model, and time is the number of steps until the machine halts. The class is only used for $d\ge3$.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), App. A.3, p.45 (PDF p.47), 'See [Sch16, Section 2]' (S. Schmitz, Complexity hierarchies beyond elementary, ACM TOCT 8(1), 2016); Theorem 1.5, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_ArrighiStarFree_HalfLevel_SpaceMachine

namespace VAS5Reach.Supplement

open ArrighiStarFree.HalfLevel

/-- The fast-growing functions `F_k : ℕ → ℕ`: `F_0(x) = x + 1` and
`F_{k+1}(x) = F_k^{x+1}(x)` (the `(x+1)`-fold iterate of `F_k`). So `F_1(x) = 2x + 1` and
`F_2(x) = 2^{x+1}(x+1) − 1`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), App. A.3, printed p. 45
(PDF p. 47): "We use F_d for the fast-growing functions and 𝐅_d for the associated complexity
classes. See [Sch16, Section 2] for more details" ([Sch16] = S. Schmitz, *Complexity hierarchies
beyond elementary*, ACM TOCT 8(1), 2016). -/
def fastGrowing : ℕ → ℕ → ℕ
  | 0, x => x + 1
  | k + 1, x => (fastGrowing k)^[x + 1] x

/-- The deterministic machine `M` (of the published multitape model, read-only input tape)
decides the language `L` in time `τ`: on every input `x` the unique run halts within `τ(|x|)`
steps, accepting iff `x ∈ L`. -/
def DecidesInTime (M : SpaceMachine) (L : Set (List Bool)) (τ : ℕ → ℕ) : Prop :=
  M.Deterministic ∧ ∀ x : List Bool, ∃ k ≤ τ x.length,
    (M.halt (M.run x (fun _ => false) k).state).isSome = true ∧
    (M.halt (M.run x (fun _ => false) k).state = some true ↔ x ∈ L)

/-- The fast-growing complexity class `𝐅_d` for finite `d ≥ 3` (Schmitz [Sch16, §2]):
`𝐅_d = ⋃_{p ∈ ℱ_{<d}} DTIME(F_d(p(n)))`, the languages decided by a deterministic multitape
Turing machine in time `F_d(p(n))` for some `p` in the Löb–Wainer class `ℱ_{<d} = ℱ_{d−1}`.
Here it is stated as: some deterministic machine decides `L` within `F_d(F_{d−1}^c(n))` steps,
for some `c`.

**Formalization Note** For `d ≥ 3` (so `d − 1 ≥ 2`), every `p ∈ ℱ_{d−1}` is bounded by some
iterate `F_{d−1}^c`, and each `F_{d−1}^c` lies in `ℱ_{d−1}` (Löb–Wainer); as DTIME is monotone in
its bound, the union over `p ∈ ℱ_{<d}` equals the union over the iterates `F_{d−1}^c`, which is
what is stated. Constant factors in the time bound are absorbed by `c`. The predicate is only used
for `d ≥ 3`; at `d = 0` the natural subtraction `d − 1` would give `0`. -/
def InFastGrowingClass (d : ℕ) (L : Set (List Bool)) : Prop :=
  ∃ (c : ℕ) (M : SpaceMachine),
    DecidesInTime M L (fun n => fastGrowing d ((fastGrowing (d - 1))^[c] n))

end VAS5Reach.Supplement


