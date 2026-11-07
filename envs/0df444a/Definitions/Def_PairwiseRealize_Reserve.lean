-- Prove2me | Definitions.Def_PairwiseRealize_Reserve
-- name    : PairwiseRealize_Reserve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:53.286604+00:00
-- url     : https://prove2.me/theorems/e7952de5-b00a-441e-af8b-55e6c44f0ad6
-- title:
--   §A.2, pp.11–12 — the coordinate tree, the rectangle trees, the budgets $T_R$, $k_R$, and the reserve size $L$
-- statement:
--   Set $t=40000\lceil\sqrt m\rceil$, $u_d=160000\lceil\sqrt{4d}\rceil$, $\ell=\lceil\log_2(n+1)\rceil$ and $C_0=2^{44}$. Recursively splitting $[n]$ into balanced halves gives **root rectangles** $A\times B$, one per split; each is refined by repeatedly bisecting its longer side down to single pairs. A node $R$ has dimension $d_R=|A||B|$, incoming bound $T_R=6t$ at a root and $T_R=u_{d_{\mathrm{parent}(R)}}$ otherwise, and at an internal node
--
--   $$k_R=C_0\bigl(T_R\lceil\sqrt{d_R}\rceil+d_R+\ell+\mathbf 1_{R=R_*}m\ell\bigr),$$
--
--   where $R_*$ is the top root. The **reserve size** is $L=6t+8nt+4\sum_{R\text{ internal}}k_R+8\sum_{R\text{ leaf}}T_R$.
--
--   **Formalization Note** All quantities depend only on the sizes of the rectangle, so a node records the sizes, $T_R$ and the two flags. A set of size $s$ splits into its first $\lfloor s/2\rfloor$ and last $\lceil s/2\rceil$ elements, and "the longer side" is $A$ on ties; the paper leaves both choices open. Everything is in $\mathbb N$, and `ceilSqrt` is the exact integer ceiling of the square root.
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §A.2, pp.11–12 (PDF pp.12–13); §3.2, p.7 (PDF p.8)

import Mathlib

namespace PairwiseRealize

/-!
# The reserve: coordinate tree, rectangle trees, budgets and the reserve size `L`

K. Shi, H. Sun, *Robust Exact Realization of Pairwise Boolean Statistics*, STOC 2027 submission
(manuscript sha256 62090516…), §A.2 "The complete reserve and its size", printed pp.11–12
(PDF pp.12–13), and §3.2, printed p.7 (PDF p.8).

"Set t = 40000⌈√m⌉, u_d = 160000⌈√(4d)⌉." "Recursively split [n] into balanced halves until
singletons. Each split S = A ⊔ B gives a root rectangle; these n − 1 rectangles partition all
unordered pairs. Within a rectangle, repeatedly bisect the longer side down to single pairs. At a
node R, let d_R be its dimension and set T_R = 6t for roots and T_R = u_{d_parent(R)} otherwise.
At every internal node use k_R = C0(T_R⌈√d_R⌉ + d_R + ℓ + 1_{R=R*} mℓ) accepted rectangles, where
R* is the top root." "At a leaf use 2T_R coordinate faces". (A.4):
L = 6t + 8nt + 4 Σ_{R internal} k_R + 8 Σ_{R leaf} T_R, with ℓ = ⌈log₂(n + 1)⌉ and C0 = 2⁴⁴ (p.7).

**Formalization Note** Every quantity attached to a node depends only on the sizes `|A|`, `|B|`
of its rectangle, its incoming bound `T_R`, and whether it is a root or the top root; so a node is
recorded by these data. "Balanced halves" splits a set of size `s` into its first `⌊s/2⌋` and last
`⌈s/2⌉` elements, and "bisect the longer side" splits `A` on ties; the paper leaves both choices
open. A rectangle with `|A||B| = 1` is a leaf. All ceilings of square roots are `ceilSqrt`, the
exact integer ceiling `⌈√d⌉`; `⌈log₂(n+1)⌉` is `Nat.clog 2 (n + 1)`. Everything is in `ℕ`.
The recursions carry a fuel argument equal to the sum of the sizes, which is never exhausted
before a leaf (each split lowers the sum by at least one).
-/

/-- The integer ceiling `⌈√d⌉` of the square root. -/
def ceilSqrt (d : ℕ) : ℕ := if Nat.sqrt d * Nat.sqrt d = d then Nat.sqrt d else Nat.sqrt d + 1

/-- `m = 1 + n + (n choose 2)`, the number of statistics. -/
def mDim (n : ℕ) : ℕ := 1 + n + n.choose 2

/-- `ℓ = ⌈log₂(n + 1)⌉`. -/
def ell (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

/-- `C0 = 2⁴⁴`. -/
def C0 : ℕ := 2 ^ 44

/-- The discrepancy radius `t = 40000⌈√m⌉`. -/
def tRad (n : ℕ) : ℕ := 40000 * ceilSqrt (mDim n)

/-- The rounding residual bound `u_d = 160000⌈√(4d)⌉`. -/
def uRad (d : ℕ) : ℕ := 160000 * ceilSqrt (4 * d)

/-- A node of a rectangle tree: the sizes `a = |A|`, `b = |B|` of its rectangle `A × B`, its
incoming bound `T_R`, and whether it is a root rectangle and whether it is the top root `R*`. -/
structure Node where
  a : ℕ
  b : ℕ
  T : ℕ
  root : Bool
  top : Bool
  deriving DecidableEq, Repr

/-- The dimension `d_R = |A||B|`. -/
def Node.d (R : Node) : ℕ := R.a * R.b

/-- A node is a leaf when it represents a single pair. -/
def Node.leaf (R : Node) : Bool := R.d ≤ 1

/-- The nodes of the rectangle tree below a rectangle of sizes `a × b` with incoming bound `T`
(preorder, the node first). A node with `ab > 1` bisects its longer side, `A` on ties, into halves
of sizes `⌊·/2⌋` and `⌈·/2⌉`; its children receive the bound `u_{ab}`. -/
def rectTree : ℕ → ℕ → ℕ → ℕ → Bool → Bool → List Node
  | 0, _, _, _, _, _ => []
  | fuel + 1, a, b, T, root, top =>
    if a * b ≤ 1 then [⟨a, b, T, root, top⟩]
    else if b ≤ a then
      ⟨a, b, T, root, top⟩ ::
        (rectTree fuel (a / 2) b (uRad (a * b)) false false ++
          rectTree fuel (a - a / 2) b (uRad (a * b)) false false)
    else
      ⟨a, b, T, root, top⟩ ::
        (rectTree fuel a (b / 2) (uRad (a * b)) false false ++
          rectTree fuel a (b - b / 2) (uRad (a * b)) false false)

/-- The root rectangles of the coordinate tree on a set of size `s`, as pairs of sizes
`(|A|, |B|)` with the flag "top root": a set of size `s ≥ 2` splits into its first `⌊s/2⌋` and
last `⌈s/2⌉` elements, giving the root rectangle `A × B`, and both halves are split recursively. -/
def coordRoots : ℕ → ℕ → Bool → List (ℕ × ℕ × Bool)
  | 0, _, _ => []
  | fuel + 1, s, top =>
    if s < 2 then []
    else (s / 2, s - s / 2, top) ::
      (coordRoots fuel (s / 2) false ++ coordRoots fuel (s - s / 2) false)

/-- The root rectangles of the coordinate tree on `[n]`; the first one is the top root `R*`. -/
def roots (n : ℕ) : List (ℕ × ℕ × Bool) := coordRoots n n true

/-- The whole forest: for each root rectangle, the nodes of its rectangle tree, the root carrying
`T_R = 6t`. -/
def forest (n : ℕ) : List Node :=
  (roots n).flatMap fun r => rectTree (r.1 + r.2.1) r.1 r.2.1 (6 * tRad n) true r.2.2

/-- `k_R = C0(T_R⌈√d_R⌉ + d_R + ℓ + 1_{R=R*} mℓ)`, the number of accepted rectangles reserved at
an internal node. -/
def kR (n : ℕ) (R : Node) : ℕ :=
  C0 * (R.T * ceilSqrt R.d + R.d + ell n + if R.top then mDim n * ell n else 0)

/-- The reserve size (A.4): `L = 6t + 8nt + 4 Σ_{R internal} k_R + 8 Σ_{R leaf} T_R`. -/
def reserveSize (n : ℕ) : ℕ :=
  6 * tRad n + 8 * n * tRad n + 4 * (((forest n).filter fun R => !R.leaf).map (kR n)).sum +
    8 * (((forest n).filter fun R => R.leaf).map Node.T).sum

end PairwiseRealize


