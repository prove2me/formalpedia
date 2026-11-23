-- Prove2me | Definitions.Def_OptimalTraceDistance_Estimation_HoeffdingGen
-- name    : OptimalTraceDistance_Estimation_HoeffdingGen
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-23T06:31:19.023424+00:00
-- url     : https://prove2.me/theorems/f98c3a57-d3c4-4a35-803f-b2cdb7653d18
-- title:
--   Generic glue, contraction and effective kernel
-- statement:
--   Generic (alphabet-independent) versions of the gluing, contraction and effective-kernel constructions used in the quantum Hoeffding decomposition of Section 4.
--
--   Let $\iota$ be a finite set and $\tau$ an operator on $\mathbb C^{\iota}$. Registers of $k$ sites are indexed by tuples $x\in\iota^k$.
--
--   1. **Gluing.** For $j\le k$, $x\in\iota^j$ and $z\in\iota^{k-j}$, the tuple $\mathrm{glue}(x,z)\in\iota^k$ lists $x$ in the first $j$ positions and $z$ in the remaining $k-j$ positions.
--   2. **Contraction.** For a $k$-site kernel $H$, the $j$-site kernel $(H)_{\to j}$ is the partial trace of $(I^{\otimes j}\otimes\tau^{\otimes(k-j)})H$ over the last $k-j$ sites:
--   $$
--   (H)_{\to j}(x,y)=\sum_{z,w\in\iota^{k-j}}H\big(\mathrm{glue}(x,z),\mathrm{glue}(y,w)\big)\,\tau^{\otimes(k-j)}(w,z).
--   $$
--   3. **Effective kernel.** For kernels $h_k$ ($k\ge0$) and a degree bound $D$,
--   $$
--   B_j=\sum_{k=j}^{D}\binom kj\,(h_k)_{\to j}.
--   $$
--
--   These are the objects in the variance bound (37) of Lemma 4.1; they coincide with the platform's `glue`, `contraction` and `effectiveKernel` when $\iota=\{0,\dots,m-1\}$, but are stated for an arbitrary finite alphabet (for instance the labelled alphabet $\{0,1\}\times[d]$).
--
--   **Formalization Note.** Tuples are functions `Fin k → ι`; the kernel `h` is a dependent family indexed by the number of sites.
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875, Section 4.1, eq. (34) and Lemma 4.1, pp. 13-14

import Definitions.Def_OptimalTraceDistance_Estimation_Core

open scoped BigOperators Matrix
noncomputable section

namespace OptimalTraceDistance.Estimation

/-- Concatenate a `j`-tuple and a `(k-j)`-tuple into a `k`-tuple (generic alphabet). -/
def glueGen {α : Type*} {k j : ℕ} (x : Fin j → α) (z : Fin (k-j) → α) : Fin k → α :=
  fun i => if h : i.val < j then x ⟨i.val, h⟩ else z ⟨i.val - j, by omega⟩

/-- Partial trace of a `k`-site kernel against `τ` on the last `k-j` sites (generic alphabet). -/
def contractionGen {ι : Type*} [Fintype ι] (τ : Matrix ι ι ℂ) (k j : ℕ)
    (H : Matrix (Fin k → ι) (Fin k → ι) ℂ) : Matrix (Fin j → ι) (Fin j → ι) ℂ :=
  fun x y => ∑ z : Fin (k-j) → ι, ∑ w : Fin (k-j) → ι,
    H (glueGen x z) (glueGen y w) * powerState τ (k-j) w z

/-- Effective kernel `B_j = Σ_{k=j}^D C(k,j) (h_k)_{→j}` (generic alphabet). -/
def effectiveKernelGen {ι : Type*} [Fintype ι] (τ : Matrix ι ι ℂ) (D : ℕ)
    (h : (k : ℕ) → Matrix (Fin k → ι) (Fin k → ι) ℂ) (j : ℕ) : Matrix (Fin j → ι) (Fin j → ι) ℂ :=
  ∑ k ∈ Finset.Icc j D, (Nat.choose k j : ℂ) • contractionGen τ k j (h k)

end OptimalTraceDistance.Estimation


