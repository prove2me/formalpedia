-- Prove2me | Definitions.Def_QCQPTightness_Sharp_Examples
-- name    : QCQPTightness_Sharp_Examples
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:23:10.781972+00:00
-- url     : https://prove2.me/theorems/4e15bf25-c80b-43eb-95b5-3f05a2aa923f
-- title:
--   (13) and (14), pp. 22–23 — the two QCQPs of §4.3 showing that Theorems 1 and 2 are sharp
-- statement:
--   Two concrete QCQPs from §4.3.
--
--   **The QCQP (13).** For positive integers $n,k$ and $N=nk$, with $m=k+1$ constraints:
--   $$
--   \min_{x\in\mathbb R^N}\Big\{-x_1^2-x_{n+1}^2-\cdots-x_{(k-1)n+1}^2 : \|x\|^2-1\le 0;\ x_{(j-1)n+1}=0,\ \forall j\in[\![1,k]\!]\Big\}.
--   $$
--   Here $A_0=I_k\otimes(-e_1e_1^\top)$, $b_0=0$, $c_0=0$; the inequality $\|x\|^2-1\le0$ has $A_1=I$, $b_1=0$, $c_1=-1$; the equality $x_{(j-1)n+1}=0$ (constraint $j+1$) has $A_{j+1}=0$, $b_{j+1}=\tfrac12e_{(j-1)n+1}$, $c_{j+1}=0$; and $m_I=1$.
--
--   **The QCQP (14).** In $N=2$ variables with $m=2$ equality constraints:
--   $$
--   \min_{x\in\mathbb R^2}\Big\{\|x-e_1\|^2 : x_1^2-x_2^2+2x_1x_2=0;\ x_1^2-x_2^2-2x_1x_2=0\Big\},
--   $$
--   so $A_0=I$, $b_0=-e_1$, $c_0=1$, $A_1=\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $A_2=\begin{pmatrix}1&-1\\-1&-1\end{pmatrix}$, $b_1=b_2=0$, $c_1=c_2=0$, $m_I=0$.
--
--   The first shows that the multiplicity bound of Theorems 1 and 2 cannot be lowered by one; the second that polyhedrality of $\Gamma$ cannot be dropped.
--
--   **Formalization Note** The page gives only the matrices $A_i$ of (13); the linear terms above are the evident encoding of the constraints $x_{(j-1)n+1}=0$ (any nonzero scaling gives the same feasible set and the same $\Gamma$). The coordinate $x_{(j-1)n+1}$ is block $j-1$, entry $0$ under the block identification of Definition 3, and `hn : 0 < n` names that entry. The paper's constraint $j+1$ is index `j.succ` of `Fin (k+1)`.
-- source:
--   arXiv:1911.09195v3, §4.3, (13) (p. 22) and (14) (pp. 22–23)

import Mathlib
import Definitions.Def_QCQPTightness_Sharp_QCQP
import Definitions.Def_QCQPTightness_Sharp_Mult

noncomputable section

namespace QCQPTightness.Sharp

open Matrix

/-- The QCQP (13) of arXiv:1911.09195v3 (§4.3, proof of Proposition 2, p. 22), in `N = n k`
variables with `m = k + 1` constraints:
`min { −x_1² − x_{n+1}² − ⋯ − x_{(k−1)n+1}² : ‖x‖² − 1 ≤ 0; x_{(j−1)n+1} = 0, j ∈ ⟦1, k⟧ }`.
The coordinates are identified with blocks by `blockEquiv` (block `j`, entry `s` ↦ `s + n j`),
so the paper's coordinate `(j−1)n+1` is `blockEquiv _ (j − 1, 0)`; `hn : 0 < n` names entry `0`.
Data: `A₀ = I_k ⊗ (−e₁e₁ᵀ)`, `b₀ = 0`, `c₀ = 0`; constraint `0` (paper index 1) is the inequality
`‖x‖² − 1 ≤ 0`, i.e. `A = I`, `b = 0`, `c = −1`; constraint `j.succ` (paper index `j + 2`,
`j : Fin k`) is the equality `x_{blockEquiv (j, 0)} = 0`, i.e. `A = 0`, `b = ½ e_{blockEquiv (j, 0)}`,
`c = 0`; `m_I = 1`. -/
def qcqp13 (n k : ℕ) (hn : 0 < n) : QCQP (n * k) (k + 1) where
  A₀ := Matrix.reindex (blockEquiv (Nat.mul_comm k n)) (blockEquiv (Nat.mul_comm k n))
    (kronId k (-(Matrix.single (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n) (1 : ℝ))))
  b₀ := 0
  c₀ := 0
  A := Fin.cases 1 (fun _ => 0)
  b := Fin.cases 0 (fun j => Pi.single (blockEquiv (Nat.mul_comm k n) (j, ⟨0, hn⟩)) (1 / 2 : ℝ))
  c := Fin.cases (-1) (fun _ => 0)
  mI := 1
  mI_le := Nat.le_add_left 1 k
  A₀_symm := by
    unfold Matrix.IsSymm kronId
    rw [Matrix.transpose_reindex, ← Matrix.kroneckerMap_transpose, Matrix.transpose_one,
      Matrix.transpose_neg, Matrix.transpose_single]
  A_symm := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Matrix.isSymm_one
    · exact Matrix.isSymm_zero

/-- The QCQP (14) of arXiv:1911.09195v3 (§4.3, proof of Proposition 3, pp. 22–23), in `N = 2`
variables with `m = 2` equality constraints:
`min { ‖x − e₁‖² : x₁² − x₂² + 2x₁x₂ = 0; x₁² − x₂² − 2x₁x₂ = 0 }`.
Data: `A₀ = I`, `b₀ = −e₁`, `c₀ = 1`; `A₁ = [[1, 1], [1, −1]]`, `A₂ = [[1, −1], [−1, −1]]`,
`b₁ = b₂ = 0`, `c₁ = c₂ = 0`; `m_I = 0`. -/
def qcqp14 : QCQP 2 2 where
  A₀ := 1
  b₀ := -Pi.single 0 1
  c₀ := 1
  A := ![!![1, 1; 1, -1], !![1, -1; -1, -1]]
  b := fun _ => 0
  c := fun _ => 0
  mI := 0
  mI_le := Nat.zero_le 2
  A₀_symm := Matrix.isSymm_one
  A_symm := by
    intro i
    fin_cases i <;>
    · refine Matrix.IsSymm.ext fun a b => ?_
      fin_cases a <;> fin_cases b <;> simp

end QCQPTightness.Sharp


