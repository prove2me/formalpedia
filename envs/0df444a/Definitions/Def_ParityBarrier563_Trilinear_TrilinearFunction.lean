-- Prove2me | Definitions.Def_ParityBarrier563_Trilinear_TrilinearFunction
-- name    : ParityBarrier563_Trilinear_TrilinearFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:11.273442+00:00
-- url     : https://prove2.me/theorems/7412b42e-79cc-4f7b-939c-1c3502646cf3
-- title:
--   Definition 5.2 — the trilinear function f_n, its slices and the live index sets T_x, T_y
-- statement:
--   For $n\ge1$, $x,y\in\{0,1\}^n$ and $a\in\{0,1\}^{2n-1}$, with coordinates numbered from zero, the **trilinear function** is
--
--   $$f_n(x,y,a)=\sum_{i=0}^{n-1}\sum_{j=0}^{n-1}a_{i+j}\,x_i\,y_j \bmod 2 .$$
--
--   It has $4n-1$ input bits, in three blocks $x$, $y$ and $a$. Fixing the seed $a$ gives the **slice** $f^a_n(x,y)=f_n(x,y,a)$, a function of the $2n$ data bits $x_0,\dots,x_{n-1},y_0,\dots,y_{n-1}$. For a restriction $\rho$ of these $2n$ variables, $T_x\subseteq\{0,\dots,n-1\}$ is the set of indices $i$ with $x_i$ live and $T_y$ the set of indices $j$ with $y_j$ live. Sumsets $A+B=\{\alpha+\beta:\alpha\in A,\beta\in B\}$ of such index sets are ordinary integer sumsets.
--
--   $f_n$ is the hard function of the goal theorem; the slices and the live index sets are the objects of Lemmas 5.4 and 5.5.
--
--   **Formalization Note** The three blocks are the disjoint union `(Fin n ⊕ Fin n) ⊕ Fin (2n − 1)`, so variables of different blocks are never identified. The output is `true` iff the number of pairs $(i,j)$ with $a_{i+j}=x_i=y_j=1$ is odd; the index $i+j\le 2n-2$ is always a valid coordinate of $a$. $T_x,T_y$ are sets of natural numbers, so their sumsets do not wrap around.
--
--   The total extension at $n=0$ is the constant false on an empty variable set; this is outside Definition 5.2's input-length convention and outside all applicable theorem instances.
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Definition 5.2, printed p.16 (PDF p.18); slices and T_x, T_y, printed p.17 (PDF p.19)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Restriction

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-! Definition 5.2, printed p.16 / PDF 18, and the slice bookkeeping of §5.1, printed p.17 /
PDF 19. Coordinates are numbered from zero: `x, y ∈ {0,1}^n` are indexed by `Fin n` and the seed
`a ∈ {0,1}^{2n−1}` by `Fin (2n − 1)`. The source uses `n ≥ 1`; at `n = 0`
the total extension has no variables and is constant false. -/

/-- The variables `x_0,…,x_{n−1}` (`Sum.inl i`) and `y_0,…,y_{n−1}` (`Sum.inr j`) of a slice. -/
abbrev SliceVar (n : ℕ) := Fin n ⊕ Fin n

/-- The `4n − 1` input variables of `f_n`: the data blocks `x`, `y` and the seed block `a`. -/
abbrev TriVar (n : ℕ) := SliceVar n ⊕ Fin (2 * n - 1)

/-- `f_n(x, y, a) = ∑_{i=0}^{n−1} ∑_{j=0}^{n−1} a_{i+j} x_i y_j mod 2`, as a Boolean value
(`true` iff the number of pairs `(i, j)` with `a_{i+j} = x_i = y_j = 1` is odd). The index
`i + j ≤ 2n − 2` is always a coordinate of `a`. -/
def trilinear (n : ℕ) (x y : Fin n → Bool) (a : Fin (2 * n - 1) → Bool) : Bool :=
  decide ((∑ i : Fin n, ∑ j : Fin n,
    (if a ⟨i.val + j.val, by omega⟩ && x i && y j then 1 else 0 : ℕ)) % 2 = 1)

/-- `f_n` as a Boolean function of its `4n − 1` input bits. -/
def trilinearFn (n : ℕ) : (TriVar n → Bool) → Bool := fun w =>
  trilinear n (fun i => w (Sum.inl (Sum.inl i))) (fun j => w (Sum.inl (Sum.inr j)))
    (fun l => w (Sum.inr l))

/-- The slice `f_n^a(x, y) = f_n(x, y, a)`, a Boolean function of the `2n` data bits. -/
def slice (n : ℕ) (a : Fin (2 * n - 1) → Bool) : (SliceVar n → Bool) → Bool := fun w =>
  trilinear n (fun i => w (Sum.inl i)) (fun j => w (Sum.inr j)) a

/-- `T_x ⊆ {0,…,n−1}`: the indices `i` such that `x_i` is live under `ρ` (as natural numbers,
so that sumsets are ordinary integer sumsets). -/
def liveX {n : ℕ} (ρ : Restriction (SliceVar n)) : Finset ℕ :=
  (Finset.univ.filter fun i : Fin n => ρ (Sum.inl i) = none).image Fin.val

/-- `T_y ⊆ {0,…,n−1}`: the indices `j` such that `y_j` is live under `ρ`. -/
def liveY {n : ℕ} (ρ : Restriction (SliceVar n)) : Finset ℕ :=
  (Finset.univ.filter fun j : Fin n => ρ (Sum.inr j) = none).image Fin.val

end ParityBarrier563.Trilinear


