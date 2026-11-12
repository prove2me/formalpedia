-- Prove2me | Definitions.Def_LocalSweepFT_sizeT
-- name    : LocalSweepFT_sizeT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:39:43.036355+00:00
-- url     : https://prove2.me/theorems/d232c142-0c59-4ddf-a886-01fd6a38e629
-- title:
--   Potential walls and the size function $\mathrm{Size}$ on $\mathcal T^d_\infty$ and on the torus
-- statement:
--   The potential walls on $\mathbb Z^d$ are $L_i(v)=v_i$ for $i\le d$ and $L_{d+1}(v)=-\sum_i v_i$. For a finite set $A\subset\mathbb Z^d$,
--   $$\mathrm{Size}(A)=\sum_{i=1}^{d+1}\max_{v\in A}L_i(v),$$
--   and the size of a chain of $\mathcal T^d_\infty$ is the size of its vertex set. For a chain $x$ of the torus $\mathcal T^d_n$, a cover is a finite set $Y$ of cells of $\mathcal T^d_\infty$ that projects into the support of $x$ and onto it, and
--   $$\mathrm{Size}(x)=\min_{Y\text{ cover of }x}\mathrm{Size}(V(Y)).$$
--
--   Size measures the extent of an error cluster in the $d+1$ directions of the bounding hypertriangle; it is the quantity that the sweep rule decreases and that the barrier argument bounds.
--
--   **Formalization Note** $\mathrm{Size}(\emptyset)=0$. The minimum is an infimum in $\mathbb Z$ over a nonempty set of nonnegative values (lift each cell with root coordinates in $[0,n)$), so it is attained.
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Definition 4.17, p.23; Size, p.24; Definition 5.1, p.39

import Mathlib
import Definitions.Def_LocalSweepFT_Chain

namespace LocalSweepFT

/-! Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…): the potential walls (Def 4.17, p.23), the size function
(p.24) and its extension to the torus by minimizing covers (Def 5.1, p.39). -/

variable {d : ℕ}

/-- The potential walls `L_1, …, L_{d+1}` (Def 4.17, p.23) on `ℤ^d`: `L_i(v) = v_i` for `i ≤ d` and
`L_{d+1}(v) = −Σ_i v_i`. The index `i : Fin (d+1)` is `0`-based: `pot ⟨j, _⟩ = L_{j+1}` and
`pot (Fin.last d) = L_{d+1}`. -/
def pot (i : Fin (d + 1)) (v : Fin d → ℤ) : ℤ :=
  if h : (i : ℕ) < d then v ⟨i, h⟩ else -∑ j, v j

/-- `Size(A) := Σ_{i=1}^{d+1} max_{v∈A} L_i(v)` for a finite set `A ⊂ ℤ^d` (p.24).

**Formalization Note.** `Size(∅) := 0` (the paper applies `Size` only to nonempty sets). On a
nonempty set the value is `≥ 0`, because `Σ_i L_i(v) = 0` at every vertex; a single vertex has
size `0` and an `i`-cell has size `i`. -/
def sizeSet (A : Finset (Fin d → ℤ)) : ℤ :=
  if h : A.Nonempty then ∑ i : Fin (d + 1), A.sup' h (pot i) else 0

/-- The size of a chain on `ℤ^d`: the size of the set of vertices of its supporting cells (p.24). -/
def sizeZ {i : ℕ} (z : Chain ℤ d i) : ℤ := sizeSet (chainVerts z)

/-- The covering projection `ℤ^d → ℤ_n^d`, coordinatewise reduction mod `n`. -/
def projVtx (n : ℕ) (v : Fin d → ℤ) : Fin d → ZMod n := fun j => (v j : ZMod n)

/-- The projection of a cell of `T^d_∞` to `T^d_n` (root reduced mod `n`, same direction set). -/
def projCell (n : ℕ) {i : ℕ} (c : Cell ℤ d i) : Cell (ZMod n) d i := (projVtx n c.1, c.2)

/-- A finite set `Y` of cells of `T^d_∞` is a cover of the torus chain `x` (Def 5.1, p.39) if it
is a subchain of the `∞`-lift of `x` (every cell of `Y` projects into the support of `x`) and its
projection covers `x` (every cell of `x` is the projection of a cell of `Y`). -/
def IsCover (n : ℕ) {i : ℕ} (x : Chain (ZMod n) d i) (Y : Finset (Cell ℤ d i)) : Prop :=
  (∀ c ∈ Y, projCell n c ∈ x.support) ∧ ∀ c ∈ x.support, ∃ c' ∈ Y, projCell n c' = c

/-- The size of a chain on the torus `T^d_n` (Def 5.1, p.39): the minimum of `Size(y)` over the
finite covers `y` of `x` in the infinite cover.

**Formalization Note.** The minimum is taken as an `sInf` in `ℤ`. The set of values is nonempty
(lift each cell of `x` with its root's representatives in `[0, n)`) and bounded below by `0` (every
value is the size of a vertex set), so the infimum is attained and is the paper's minimum. The zero
chain has the empty cover and size `0`. -/
noncomputable def sizeT (n : ℕ) {i : ℕ} (x : Chain (ZMod n) d i) : ℤ :=
  sInf {s : ℤ | ∃ Y : Finset (Cell ℤ d i), IsCover n x Y ∧ sizeSet (Y.biUnion cellVerts) = s}

end LocalSweepFT


