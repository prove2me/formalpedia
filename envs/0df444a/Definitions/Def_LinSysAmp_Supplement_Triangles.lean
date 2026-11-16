-- Prove2me | Definitions.Def_LinSysAmp_Supplement_Triangles
-- name    : LinSysAmp_Supplement_Triangles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:48:26.813206+00:00
-- url     : https://prove2.me/theorems/b60fbc86-6a1a-40bb-9bd3-29f3e31b98f6
-- title:
--   Graphs, the parity of triangles, and the algorithm of Figure 6 (§5.4)
-- statement:
--   Identify a graph on the vertex set $[n]$ with its adjacency matrix $A\in\mathbb F_2^{n\times n}$, which is symmetric with zero diagonal; $S_n$ is the set of such matrices, and $A\leftarrow S_n$ is a uniform random graph. The **parity of triangles** is
--   $$\tau(A)=\sum_{1\le a<b<c\le n}A_{ab}A_{bc}A_{ac}\in\mathbb F_2 .$$
--
--   A **graph oracle** $O$ is a randomized map from $n\times n$ matrices over $\mathbb F_2$ to bits, with fresh coins per call; its success is $\Pr_{A\leftarrow S_n,O}[O(A)=\tau(A)]$.
--
--   **Figure 6** (algorithm $D^O(A_0)$ with parameter $t$):
--
--   1. set $s_0=0$;
--   2. for $j=0,\dots,t-1$: compute $b_j=O(A_j)+s_j$; sample $u,v\leftarrow\mathbb F_2^n$, set $A_{j+1}=A_j+uv^\top+vu^\top$ and $s_{j+1}=s_j+\tau(A_j)+\tau(A_{j+1})$;
--   3. output the most frequent value among $b_0,\dots,b_{t-1}$, or $0$ in case of a tie.
--
--   All operations on $s_j,b_j$ are in $\mathbb F_2$. The definition gives the output distribution of Figure 6 for every oracle, every $t$ and every start $A_0$, and the interface of the oracle machine for a graph oracle (a call reads an $n\times n$ matrix and writes one bit). It is the object of Theorem 5.8.
--
--   **Formalization Note** The state after $j$ iterations is $(A_j,s_j,\#\{i<j:b_i=1\})$, and the output is $1$ exactly when more than $t/2$ of the $b_i$ equal $1$. The paper computes $\tau(A_j)+\tau(A_{j+1})$ quickly with Lemma 5.7; the value is the same.
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), §5.4, p.29 (PDF p.31); Figure 6, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_LinSysAmp_Supplement_OracleMachine

set_option autoImplicit false

open Matrix

namespace LinSysAmp.Supplement

/-!
# Graphs, the parity of triangles, and the algorithm of Figure 6

G. Couteau, N. Melissaris, T. Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and
Fine-Grained Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…), §5.4, pp.29–31
(PDF pp.31–33): "We identify a graph on the vertex set [n] with the adjacency matrix A ∈ F₂^{n×n}
of this graph, which is symmetric with zero diagonal. We denote by S_n the set of such matrices. […]
τ(A) = ∑_{1≤a<b<c≤n} A_ab A_bc A_ac ∈ F₂."

Figure 6, p.31 (PDF p.33): "Algorithm D^O(A₀). Parameter: number of steps t. 1. Set s₀ = 0.
2. For j = 0, …, t − 1: (a) Compute b_j = O(A_j) + s_j. (b) Sample u, v ← F₂ⁿ. Set
A_{j+1} = A_j + uv⊤ + vu⊤, and compute s_{j+1} = s_j + τ(A_j) + τ(A_{j+1}) with Lemma 5.7.
3. Output the most frequent value among b₀, …, b_{t−1}, or 0 in case of a tie. […] All operations
on s_j and b_j are in F₂."

**Formalization Note.**
* `F₂` is `ZMod 2`; `S_n` is the subtype of symmetric `n × n` matrices over `ZMod 2` with zero
  diagonal; `A ← S_n` is the uniform (normalized counting) distribution on it.
* A graph oracle is a randomized map from `n × n` matrices over `F₂` to `PMF F₂` (fresh coins per
  call). It is defined on all matrices, but Figure 6 calls it only on matrices of `S_n`.
* `figure6 O t A₀` is the output distribution of Figure 6 at the level of probability mass
  functions. The state after `j` iterations is `(A_j, s_j, #{i < j : b_i = 1})`; the output is `1`
  if more than half of `b₀, …, b_{t−1}` equal `1`, and `0` otherwise (ties give `0`). Lemma 5.7
  only gives a fast way to compute `τ(A_j) + τ(A_{j+1})`; the value is the same.
* The machine interface `graphIface O` reads `n²` cells (the matrix row-major) and writes one
  cell, the oracle's bit.
-/

/-- `S_n`: the adjacency matrices of graphs on `[n]`, i.e. symmetric matrices over `F₂` with zero
diagonal. (arXiv:2611.04680, version held, sha256 af7a90ac…, §5.4, p.29 (PDF p.31).) -/
def GraphMat (n : ℕ) : Type := {A : Matrix (Fin n) (Fin n) (ZMod 2) // A.IsSymm ∧ ∀ i, A i i = 0}

noncomputable instance (n : ℕ) : Fintype (GraphMat n) := by
  unfold GraphMat; classical exact inferInstance

/-- `τ(A) = ∑_{1≤a<b<c≤n} A_ab A_bc A_ac ∈ F₂`, the parity of the number of triangles.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §5.4, p.29 (PDF p.31).) -/
def tau {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) : ZMod 2 :=
  ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
    if a < b ∧ b < c then A a b * A b c * A a c else 0

/-- `Pr_{A ← S_n, O}[O(A) = τ(A)]`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Theorem 5.8, p.31 (PDF p.33).) -/
noncomputable def triSuccess {n : ℕ} (O : Matrix (Fin n) (Fin n) (ZMod 2) → PMF (ZMod 2)) : ℝ :=
  (Fintype.card (GraphMat n) : ℝ)⁻¹ * ∑ A : GraphMat n, (O A.1 (tau A.1)).toReal

/-- One iteration of Figure 6 on the state `(A_j, s_j, #ones so far)`: query `b_j = O(A_j) + s_j`,
then move to `A_{j+1} = A_j + uv⊤ + vu⊤` with `s_{j+1} = s_j + τ(A_j) + τ(A_{j+1})`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Figure 6, p.31 (PDF p.33).) -/
noncomputable def figure6Step {n : ℕ} (O : Matrix (Fin n) (Fin n) (ZMod 2) → PMF (ZMod 2))
    (st : Matrix (Fin n) (Fin n) (ZMod 2) × ZMod 2 × ℕ) :
    PMF (Matrix (Fin n) (Fin n) (ZMod 2) × ZMod 2 × ℕ) :=
  (O st.1).bind fun o =>
    (PMF.uniformOfFintype ((Fin n → ZMod 2) × (Fin n → ZMod 2))).map fun uv =>
      let A' := st.1 + vecMulVec uv.1 uv.2 + vecMulVec uv.2 uv.1
      (A', st.2.1 + tau st.1 + tau A', st.2.2 + if o + st.2.1 = 1 then 1 else 0)

/-- The state of Figure 6 after `j` iterations from `A₀` (with `s₀ = 0` and no ones counted).
(arXiv:2611.04680, version held, sha256 af7a90ac…, Figure 6, p.31 (PDF p.33).) -/
noncomputable def figure6State {n : ℕ} (O : Matrix (Fin n) (Fin n) (ZMod 2) → PMF (ZMod 2))
    (A₀ : Matrix (Fin n) (Fin n) (ZMod 2)) : ℕ → PMF (Matrix (Fin n) (Fin n) (ZMod 2) × ZMod 2 × ℕ)
  | 0 => PMF.pure (A₀, 0, 0)
  | j + 1 => (figure6State O A₀ j).bind (figure6Step O)

/-- Figure 6: the output distribution of `D^O(A₀)` with `t` steps: the most frequent value among
`b₀, …, b_{t−1}`, or `0` in case of a tie.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Figure 6, p.31 (PDF p.33).) -/
noncomputable def figure6 {n : ℕ} (O : Matrix (Fin n) (Fin n) (ZMod 2) → PMF (ZMod 2)) (t : ℕ)
    (A₀ : Matrix (Fin n) (Fin n) (ZMod 2)) : PMF (ZMod 2) :=
  (figure6State O A₀ t).map fun st => if t < 2 * st.2.2 then 1 else 0

/-- The machine interface of a graph oracle: a call reads `n²` cells (row-major) and writes one
cell, the answer bit. (arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, §5.4.) -/
noncomputable def graphIface {n : ℕ} (O : Matrix (Fin n) (Fin n) (ZMod 2) → PMF (ZMod 2)) :
    Iface (ZMod 2) Unit where
  inLen _ := n * n
  call _ x _ := (O (unflatMat n x 0)).map fun b => ([b], none)

end LinSysAmp.Supplement


