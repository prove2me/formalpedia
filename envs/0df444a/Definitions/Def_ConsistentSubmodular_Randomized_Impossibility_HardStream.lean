-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardStream
-- name    : ConsistentSubmodular_Randomized_Impossibility_HardStream
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:31.785433+00:00
-- url     : https://prove2.me/theorems/0e003c97-4c2e-48e6-a18a-63fdd55451b8
-- title:
--   Hard coverage stream for the randomized impossibility: cells, weighted coverage, competitors
-- statement:
--   The hard instance has budget $k$ and stream length $3k+2$, with positions $0,\dots,3k+1$. The stream consists of $3k$ tiny sets, then $U_0$ at position $3k$ and $U_1$ at position $3k+1$. Cells are pairs $(g,b)$ with group $g\in\{0,1,2\}$ and block $b\in\{0,\dots,k-1\}$. $W_0$ is a number of copies and $w:\{0,1,2\}\to\mathbb{N}$ gives the copies kept per group.
--
--   - `elementCells k e` is the set of cells covered by the stream element at position $e$: the tiny set at position $gk+b<3k$ covers the single cell $(g,b)$; $U_0$ (position $3k$) covers all cells of group $0$; $U_1$ (position $3k+1$) covers all cells of group $1$.
--   - `cellSet k W₀ w B` is the set of universe elements $(g,b,r)$ with $(g,b)\in B$ and $r<w(g)$, $r\in\{0,\dots,W_0-1\}$: the first $w(g)$ copies of every cell of group $g$.
--   - `fiber C g` is the set of cells of $C$ of group $g$.
--   - `tinyCount k g T` $=c_g(T)$ is the number of tiny sets of group $g$ (positions $e<3k$ with $\lfloor e/k\rfloor=g$) in $T$.
--   - `tinyAt (g,b)` is the position $gk+b$ of the tiny set of cell $(g,b)$.
--   - `weightedValue k u T` $=f_u(T)=\sum_{g}u_g\,\bigl|\mathrm{fiber}(\textstyle\bigcup_{e\in T}\mathrm{elementCells}(e),\,g)\bigr|$: the total weight of the cells covered by $T$, each cell of group $g$ having weight $u_g$.
--   - `streamCover k W₀ w e` is the unweighted cover set of element $e$: `cellSet` of its cells, encoded in $\{0,\dots,u-1\}$ through a fixed bijection of the universe with $\{0,\dots,u-1\}$, $u=3kW_0$.
--   - `bigZero k` $=U_0$ (position $3k$) and `bigOne k` $=U_1$ (position $3k+1$).
--   - `positions k a m` is the set of positions $a,\dots,a+m-1$.
--   - The three competitors: `firstCompetitor` $=$ positions $0,\dots,k-1$ (the $k$ tiny sets of group $0$); `secondCompetitor` $=\{U_0\}\cup$ positions $k,\dots,2k-2$ ($U_0$ and $k-1$ tiny sets of group $1$); `thirdCompetitor` $=\{U_0,U_1\}\cup$ positions $2k,\dots,3k-3$ ($U_0$, $U_1$ and $k-2$ tiny sets of group $2$).
--
--   These definitions give the weighted coverage stream and its three competitors for the proof of Theorem 1, the impossibility for randomized algorithms (Appendix A.2); weights are later removed by rounding and replacing cells with unit-weight copies.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Impossibility/HardStream.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.HardInstance

/-- The cells `(g, b)` covered by a stream element: the tiny set at position
`g k + b < 3k` covers block `b` of group `g`, `U₀` (position `3k`) covers group
`0`, and `U₁` (position `3k + 1`) covers group `1`. -/
def elementCells (k : ℕ) (e : Fin (3 * k + 2)) : Finset (Fin 3 × Fin k) :=
  univ.filter fun c =>
    if e.val < 3 * k then c.1.val = e.val / k ∧ c.2.val = e.val % k
    else if e.val = 3 * k then c.1.val = 0 else c.1.val = 1

/-- The universe elements of a set of cells: the first `w g` of the `W₀`
copies of every cell of group `g`. -/
def cellSet (k W₀ : ℕ) (w : Fin 3 → ℕ) (B : Finset (Fin 3 × Fin k)) :
    Finset (Fin 3 × Fin k × Fin W₀) :=
  univ.filter fun x => (x.1, x.2.1) ∈ B ∧ x.2.2.val < w x.1

/-- The fibre of a set of cells over group `g`. -/
def fiber {k : ℕ} (C : Finset (Fin 3 × Fin k)) (g : Fin 3) : Finset (Fin 3 × Fin k) :=
  C.filter fun c => c.1 = g

/-- The number `c_g(T)` of tiny sets of group `g` in `T`. -/
def tinyCount (k : ℕ) (g : Fin 3) (T : Finset (Fin (3 * k + 2))) : ℕ :=
  (T.filter fun e => e.val < 3 * k ∧ e.val / k = g.val).card

/-- The tiny set of cell `(g, b)`, at position `g k + b`. -/
def tinyAt {k : ℕ} (c : Fin 3 × Fin k) : Fin (3 * k + 2) :=
  ⟨c.1.val * k + c.2.val, by
    have h1 := c.1.isLt
    have h2 := c.2.isLt
    have h3 : c.1.val * k ≤ 2 * k := Nat.mul_le_mul_right k (by omega)
    omega⟩

/-- The weighted coverage `f_u(T)` of a family `T`: the total weight of the cells
it covers, where every cell of group `g` has weight `u g`. -/
def weightedValue (k : ℕ) (u : Fin 3 → ℝ) (T : Finset (Fin (3 * k + 2))) : ℝ :=
  ∑ g, u g * (fiber (T.biUnion (elementCells k)) g).card

/-- The cover of the stream, with the universe `Fin 3 × Fin k × Fin W₀` encoded
as `Fin u`. -/
def streamCover (k W₀ : ℕ) (w : Fin 3 → ℕ) (e : Fin (3 * k + 2)) :
    Finset (Fin (Fintype.card (Fin 3 × Fin k × Fin W₀))) :=
  (cellSet k W₀ w (elementCells k e)).map (Fintype.equivFin _).toEmbedding

/-- `U₀`, the large set of group `0`, at position `3k`. -/
def bigZero (k : ℕ) : Fin (3 * k + 2) := ⟨3 * k, by omega⟩

/-- `U₁`, the large set of group `1`, at position `3k + 1`. -/
def bigOne (k : ℕ) : Fin (3 * k + 2) := ⟨3 * k + 1, by omega⟩

/-- The positions `a, ..., a + m - 1` of the stream. -/
def positions (k a m : ℕ) : Finset (Fin (3 * k + 2)) :=
  univ.filter fun e => a ≤ e.val ∧ e.val < a + m

/-- The competitor before `U₀` arrives: the `k` tiny sets of group `0`. -/
def firstCompetitor (k : ℕ) : Finset (Fin (3 * k + 2)) := positions k 0 k

/-- The competitor after `U₀` arrives: `U₀` and `k - 1` tiny sets of group `1`. -/
def secondCompetitor (k : ℕ) : Finset (Fin (3 * k + 2)) :=
  insert (bigZero k) (positions k k (k - 1))

/-- The competitor at the end: `U₀`, `U₁`, and `k - 2` tiny sets of group `2`. -/
def thirdCompetitor (k : ℕ) : Finset (Fin (3 * k + 2)) :=
  insert (bigZero k) (insert (bigOne k) (positions k (2 * k) (k - 2)))

end ConsistentSubmodular.HardInstance

end


