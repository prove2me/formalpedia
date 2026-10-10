-- Prove2me | Definitions.Def_QuadMatIneq_Stabilization_Data
-- name    : QuadMatIneq_Stabilization_Data
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:21.98312+00:00
-- url     : https://prove2.me/theorems/b907ddeb-e22a-42f2-9e68-08d9beb37d38
-- title:
--   §2 (2.1)–(2.4), Definition 2.1, §5.1 (5.1), (5.2), (5.5), (5.6) — data matrices, the set Σ, informativity for quadratic stabilization, M, N and the two LMIs
-- statement:
--   Consider the system $x(t+1)=A_sx(t)+B_su(t)+w(t)$ with $x,w\in\mathbb{R}^n$, $u\in\mathbb{R}^m$, and data collected over $T$ steps:
--   $$X=[x(0)\ \cdots\ x(T)],\quad U_-=[u(0)\ \cdots\ u(T-1)],\quad X_-=[x(0)\ \cdots\ x(T-1)],\quad X_+=[x(1)\ \cdots\ x(T)].$$
--   The unknown noise $W_-=[w(0)\ \cdots\ w(T-1)]$ is assumed to satisfy the quadratic matrix inequality (2.3), $[I;W_-^\top]^\top\Phi[I;W_-^\top]\geqslant 0$, for a given $\Phi\in\mathbb{S}^{n+T}$, i.e. $W_-^\top\in\mathcal Z_T(\Phi)$.
--
--   1. **Systems compatible with the data.** $\Sigma=\{(A,B)\in\mathbb{R}^{n\times n}\times\mathbb{R}^{n\times m}: X_+=AX_-+BU_-+W_- \text{ for some } W_- \text{ satisfying (2.3)}\}$.
--   2. **Informativity (Definition 2.1).** The data $(U_-,X)$ are *informative for quadratic stabilization* if there are $K\in\mathbb{R}^{m\times n}$ and $P>0$ with
--   $$P-(A+BK)P(A+BK)^\top>0\qquad\text{for all }(A,B)\in\Sigma. \tag{2.4}$$
--   3. **Stabilizing gain for all of $\Sigma$, certified by $P$.** For every $(A,B)\in\Sigma$, (2.4) holds and $(A+BK)^k\to 0$ as $k\to\infty$.
--   4. **The matrices of (5.1)–(5.2)**, partitioned $n\,|\,n+m$:
--   $$M=\begin{bmatrix}P&0&0\\0&-P&-PK^\top\\0&-KP&-KPK^\top\end{bmatrix},\qquad N=\begin{bmatrix}I&X_+\\0&-X_-\\0&-U_-\end{bmatrix}\Phi\begin{bmatrix}I&X_+\\0&-X_-\\0&-U_-\end{bmatrix}^{\!\top}.$$
--   5. **The LMIs (5.5) and (5.6)**, with block sizes $n\,|\,n\,|\,m\,|\,n$ and $L\in\mathbb{R}^{m\times n}$, $\beta\in\mathbb{R}$:
--   $$\begin{bmatrix}P-\beta I&0&0&0\\0&-P&-L^\top&0\\0&-L&0&L\\0&0&L^\top&P\end{bmatrix}-\begin{bmatrix}I&X_+\\0&-X_-\\0&-U_-\\0&0\end{bmatrix}\Phi\begin{bmatrix}I&X_+\\0&-X_-\\0&-U_-\\0&0\end{bmatrix}^{\!\top},$$
--   and the same matrix with $P$ in place of $P-\beta I$ in the top-left block.
--
--   These objects turn the question "does one controller stabilize every system consistent with noisy data?" into an inclusion between two QMI solution sets, and then into a linear matrix inequality.
--
--   **Formalization Note** $X$ is an $n\times(T+1)$ matrix; $X_-$ and $X_+$ are its first and last $T$ columns (`Fin.castSucc`, `Fin.succ`). $[X_-;U_-]$ is `Matrix.fromRows`, block matrices are `Matrix.fromBlocks`, and the rows of the four-block data factor are indexed by `(Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)`. Schur stability is stated as convergence of the powers $(A+BK)^k$ to $0$ in the entrywise topology. `lmi55` and `lmi56` are the left-hand sides of (5.5) and (5.6); the inequalities themselves are stated in the theorems.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §2 pp. 3–4, (2.1)–(2.4), Definition 2.1; §5.1 p. 18, (5.1), (5.2), (5.5); p. 19, (5.6)

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI

namespace QuadMatIneq.Stabilization

/-! §2 (pp. 3–5) and §5.1 (pp. 17–19) of van Waarde–Camlibel–Eising–Trentelman,
arXiv:2203.12959v3: the data matrices, the set `Σ` of systems compatible with the data,
informativity for quadratic stabilization (Definition 2.1), the matrices `M`, `N` of (5.1)–(5.2)
and the two linear matrix inequalities (5.5), (5.6). -/

open Matrix Filter Topology

variable {n m T : ℕ}

/-- `X₋ = [x(0) ⋯ x(T−1)]`: the first `T` columns of `X = [x(0) ⋯ x(T)]` (p. 3). -/
def Xminus (X : Matrix (Fin n) (Fin (T + 1)) ℝ) : Matrix (Fin n) (Fin T) ℝ :=
  X.submatrix id Fin.castSucc

/-- `X₊ = [x(1) ⋯ x(T)]`: the last `T` columns of `X = [x(0) ⋯ x(T)]` (p. 3). -/
def Xplus (X : Matrix (Fin n) (Fin (T + 1)) ℝ) : Matrix (Fin n) (Fin T) ℝ :=
  X.submatrix id Fin.succ

/-- The set `Σ` of systems `(A, B) ∈ ℝ^{n×n} × ℝ^{n×m}` compatible with the data (p. 4):
`X₊ = A X₋ + B U₋ + W₋` for some `W₋ ∈ ℝ^{n×T}` satisfying the noise model (2.3),
`[I; W₋ᵀ]ᵀ Φ [I; W₋ᵀ] ⩾ 0`, i.e. `W₋ᵀ ∈ 𝒵_T(Φ)`. -/
def Sigma (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ) (X : Matrix (Fin n) (Fin (T + 1)) ℝ)
    (Um : Matrix (Fin m) (Fin T) ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin m) ℝ) :=
  {AB | ∃ Wm : Matrix (Fin n) (Fin T) ℝ,
    Xplus X = AB.1 * Xminus X + AB.2 * Um + Wm ∧ Wmᵀ ∈ ZSet Φ}

/-- Definition 2.1 (p. 4): the data `(U₋, X)` are informative for quadratic stabilization if
there exist a feedback gain `K` and a matrix `P > 0` such that `P − (A + BK) P (A + BK)ᵀ > 0`
for all `(A, B) ∈ Σ` (inequality (2.4)). -/
def InformativeQS (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T + 1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ) : Prop :=
  ∃ K : Matrix (Fin m) (Fin n) ℝ, ∃ P : Matrix (Fin n) (Fin n) ℝ, P.PosDef ∧
    ∀ AB ∈ Sigma Φ X Um, (P - (AB.1 + AB.2 * K) * P * (AB.1 + AB.2 * K)ᵀ).PosDef

/-- `K` is a stabilizing feedback gain for all `(A, B) ∈ Σ`, certified by the Lyapunov matrix
`P`: for every `(A, B) ∈ Σ` the Lyapunov inequality (2.4) `P − (A + BK) P (A + BK)ᵀ > 0` holds,
and the closed-loop matrix `A + BK` is Schur stable (`(A + BK)^k → 0`). -/
def StabilizesAll (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T + 1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ AB ∈ Sigma Φ X Um,
    (P - (AB.1 + AB.2 * K) * P * (AB.1 + AB.2 * K)ᵀ).PosDef ∧
      Tendsto (fun k : ℕ => (AB.1 + AB.2 * K) ^ k) atTop (𝓝 0)

/-- The matrix `M` of (5.1) (p. 18), partitioned `n | n + m`:
`M = [P 0 0; 0 −P −PKᵀ; 0 −KP −KPKᵀ]`. -/
def Mmat (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin n ⊕ (Fin n ⊕ Fin m)) (Fin n ⊕ (Fin n ⊕ Fin m)) ℝ :=
  Matrix.fromBlocks P 0 0 (Matrix.fromBlocks (-P) (-(P * Kᵀ)) (-(K * P)) (-(K * P * Kᵀ)))

/-- The data factor `[I X₊; 0 −X₋; 0 −U₋]` of (2.5) and (5.2), of size `(n + n + m) × (n + T)`. -/
def dataFactor3 (X : Matrix (Fin n) (Fin (T + 1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ) :
    Matrix (Fin n ⊕ (Fin n ⊕ Fin m)) (Fin n ⊕ Fin T) ℝ :=
  Matrix.fromBlocks 1 (Xplus X) 0 (-Matrix.fromRows (Xminus X) Um)

/-- The matrix `N` of (5.2) (p. 18), partitioned `n | n + m`:
`N = [I X₊; 0 −X₋; 0 −U₋] Φ [I X₊; 0 −X₋; 0 −U₋]ᵀ`. -/
def Nmat (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ) (X : Matrix (Fin n) (Fin (T + 1)) ℝ)
    (Um : Matrix (Fin m) (Fin T) ℝ) :
    Matrix (Fin n ⊕ (Fin n ⊕ Fin m)) (Fin n ⊕ (Fin n ⊕ Fin m)) ℝ :=
  dataFactor3 X Um * Φ * (dataFactor3 X Um)ᵀ

/-- The data factor `[I X₊; 0 −X₋; 0 −U₋; 0 0]` of (5.5)–(5.6), of size
`(n + n + m + n) × (n + T)`, rows indexed by `(Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)`. -/
def dataFactor4 (X : Matrix (Fin n) (Fin (T + 1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ) :
    Matrix ((Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)) (Fin n ⊕ Fin T) ℝ :=
  Matrix.fromRows (Matrix.fromBlocks 1 (Xplus X) 0 (-Xminus X)) (Matrix.fromBlocks 0 (-Um) 0 0)

/-- The left-hand side of the LMI (5.5) (p. 18), block sizes `n | n | m | n`:
`[P − βI 0 0 0; 0 −P −Lᵀ 0; 0 −L 0 L; 0 0 Lᵀ P] − [I X₊; 0 −X₋; 0 −U₋; 0 0] Φ [⋯]ᵀ`. -/
def lmi55 (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ) (X : Matrix (Fin n) (Fin (T + 1)) ℝ)
    (Um : Matrix (Fin m) (Fin T) ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ)
    (β : ℝ) : Matrix ((Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)) ((Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)) ℝ :=
  Matrix.fromBlocks
      (Matrix.fromBlocks (P - β • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 0 (-P))
      (Matrix.fromBlocks 0 0 (-Lᵀ) 0)
      (Matrix.fromBlocks 0 (-L) 0 0)
      (Matrix.fromBlocks 0 L Lᵀ P)
    - dataFactor4 X Um * Φ * (dataFactor4 X Um)ᵀ

/-- The left-hand side of the LMI (5.6) (p. 19), block sizes `n | n | m | n`:
`[P 0 0 0; 0 −P −Lᵀ 0; 0 −L 0 L; 0 0 Lᵀ P] − [I X₊; 0 −X₋; 0 −U₋; 0 0] Φ [⋯]ᵀ`. -/
def lmi56 (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ) (X : Matrix (Fin n) (Fin (T + 1)) ℝ)
    (Um : Matrix (Fin m) (Fin T) ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ) :
    Matrix ((Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)) ((Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)) ℝ :=
  Matrix.fromBlocks
      (Matrix.fromBlocks P 0 0 (-P))
      (Matrix.fromBlocks 0 0 (-Lᵀ) 0)
      (Matrix.fromBlocks 0 (-L) 0 0)
      (Matrix.fromBlocks 0 L Lᵀ P)
    - dataFactor4 X Um * Φ * (dataFactor4 X Um)ᵀ

end QuadMatIneq.Stabilization


