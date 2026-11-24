-- Prove2me | Definitions.Def_SRAudit_TwoPhase_Supplement_LambdaMatrix
-- name    : SRAudit_TwoPhase_Supplement_LambdaMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:22:29.5758+00:00
-- url     : https://prove2.me/theorems/26524d4f-5860-427c-92aa-714cdd59d24f
-- title:
--   Appendix I, (I.3)–(I.4), OA-55 — the matrices J, D_n, Q_{2k,n}, R_{2k,m}, D̃_{2k} and the block matrices Λ(m,n,k), Λ̃(m,n,k)
-- statement:
--   For $m,n,k\in\mathbb N_0$ (I.3)–(I.4): $J_{m,n}$ is the $m\times n$ matrix of ones; $D_n=I_n+J_n$; $Q_{2k,n}$ is the $2k\times n$ matrix whose odd rows are all $1$ and even rows all $2$; $R_{2k,m}$ is the $2k\times m$ matrix whose odd rows are all $2$ and even rows all $1$; $\widetilde D_{2k}=D_k\otimes D_2$ (Kronecker product). The symmetric $(m+2k+n)\times(m+2k+n)$ matrix is
--   $$\Lambda(m,n,k)=\begin{bmatrix}2D_m & R_{2k,m}^{\mathsf T} & J_{m,n}\\ R_{2k,m} & \widetilde D_{2k} & Q_{2k,n}\\ J_{n,m} & Q_{2k,n}^{\mathsf T} & 2D_n\end{bmatrix}.$$
--   The second symmetric matrix of (I.4) is
--   $$\widetilde\Lambda(m,n,k)=\begin{bmatrix}2D_{m+k} & \begin{bmatrix}J_{m,k} & J_{m,n}\\ D_k & J_{k,n}\end{bmatrix}\\ \begin{bmatrix}J_{k,m} & D_k\\ J_{n,m} & J_{n,k}\end{bmatrix} & 2D_{k+n}\end{bmatrix}.$$
--   Up to the factor $-2\beta$, $\Lambda$ is the Jacobian of the pseudogradient of the tier-2 game with $m$ exclusive suppliers of firm $a$, $k$ shared suppliers and $n$ exclusive suppliers of firm $b$ (OA-6).
--
--   **Formalization Note** The middle block is indexed by pairs $(l,e)\in\{0,\dots,k-1\}\times\{0,1\}$ in lexicographic order; $(l,0)$ is row $2l+1$ (odd) and $(l,1)$ is row $2l+2$ (even) of the page.
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-55, Appendix I, (I.3)–(I.4)

import Mathlib

namespace SRAudit.TwoPhase.Supplement

open Matrix

/-- `J_{m,n}`, the `m × n` matrix of ones (I.3). -/
def Jmat (m n : Type) : Matrix m n ℝ := Matrix.of fun _ _ => 1

/-- `D_n = I_n + J_n` (I.3), on an index type `n`. -/
def Dmat (n : Type) [Fintype n] [DecidableEq n] : Matrix n n ℝ := 1 + Jmat n n

/-- `Q_{2k,n}` (I.3): `2k × n`, odd rows `1`, even rows `2`. Row `2l − 1` of the page is the index
`(l, 0)` and row `2l` is `(l, 1)`. -/
def Qmat (k n : ℕ) : Matrix (Fin k × Fin 2) (Fin n) ℝ :=
  Matrix.of fun p _ => if p.2 = 0 then 1 else 2

/-- `R_{2k,m}` (I.3): `2k × m`, odd rows `2`, even rows `1` (same row indexing as `Qmat`). -/
def Rmat (k m : ℕ) : Matrix (Fin k × Fin 2) (Fin m) ℝ :=
  Matrix.of fun p _ => if p.2 = 0 then 2 else 1

/-- `D̃_{2k} = D_k ⊗ D_2` (Kronecker product), indexed by `Fin k × Fin 2` in lexicographic order,
which is the row order `1, …, 2k` of the page. -/
def Dtilde (k : ℕ) : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℝ :=
  Matrix.kroneckerMap (· * ·) (Dmat (Fin k)) (Dmat (Fin 2))

/-- The `(m + 2k + n) × (m + 2k + n)` symmetric block matrix `Λ(m, n, k)` of (I.4):
```
Λ = [ 2D_m       R_{2k,m}ᵀ   J_{m,n}
      R_{2k,m}   D̃_{2k}      Q_{2k,n}
      J_{n,m}    Q_{2k,n}ᵀ   2D_n     ]
```
with the three diagonal blocks indexed by `Fin m`, `Fin k × Fin 2` and `Fin n`. -/
def Lambda (m n k : ℕ) :
    Matrix (Fin m ⊕ (Fin k × Fin 2) ⊕ Fin n) (Fin m ⊕ (Fin k × Fin 2) ⊕ Fin n) ℝ :=
  Matrix.of fun x y =>
    match x, y with
    | .inl i, .inl i' => 2 * Dmat (Fin m) i i'
    | .inl i, .inr (.inl p) => (Rmat k m)ᵀ i p
    | .inl i, .inr (.inr j) => Jmat (Fin m) (Fin n) i j
    | .inr (.inl p), .inl i => Rmat k m p i
    | .inr (.inl p), .inr (.inl p') => Dtilde k p p'
    | .inr (.inl p), .inr (.inr j) => Qmat k n p j
    | .inr (.inr j), .inl i => Jmat (Fin n) (Fin m) j i
    | .inr (.inr j), .inr (.inl p) => (Qmat k n)ᵀ j p
    | .inr (.inr j), .inr (.inr j') => 2 * Dmat (Fin n) j j'

/-- The `(m + 2k + n) × (m + 2k + n)` symmetric block matrix `Λ̃(m, n, k)` of (I.4):
```
Λ̃ = [ 2D_{m+k}                 [J_{m,k} J_{m,n}; D_k J_{k,n}]
      [J_{k,m} D_k; J_{n,m} J_{n,k}]   2D_{k+n}                 ]
```
with the row blocks indexed by `Fin m ⊕ Fin k` (top) and `Fin k ⊕ Fin n` (bottom). -/
def LambdaTilde (m n k : ℕ) :
    Matrix ((Fin m ⊕ Fin k) ⊕ (Fin k ⊕ Fin n)) ((Fin m ⊕ Fin k) ⊕ (Fin k ⊕ Fin n)) ℝ :=
  Matrix.of fun x y =>
    match x, y with
    | .inl p, .inl p' => 2 * Dmat (Fin m ⊕ Fin k) p p'
    | .inl (.inl i), .inr (.inl l) => Jmat (Fin m) (Fin k) i l
    | .inl (.inl i), .inr (.inr j) => Jmat (Fin m) (Fin n) i j
    | .inl (.inr l), .inr (.inl l') => Dmat (Fin k) l l'
    | .inl (.inr l), .inr (.inr j) => Jmat (Fin k) (Fin n) l j
    | .inr (.inl l), .inl (.inl i) => Jmat (Fin k) (Fin m) l i
    | .inr (.inl l), .inl (.inr l') => Dmat (Fin k) l l'
    | .inr (.inr j), .inl (.inl i) => Jmat (Fin n) (Fin m) j i
    | .inr (.inr j), .inl (.inr l) => Jmat (Fin n) (Fin k) j l
    | .inr q, .inr q' => 2 * Dmat (Fin k ⊕ Fin n) q q'

end SRAudit.TwoPhase.Supplement


