-- Prove2me | Definitions.Def_VecBalPoly_q
-- name    : VecBalPoly_q
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:10:48.829692+00:00
-- url     : https://prove2.me/theorems/5840de6b-19d7-46ca-a3e1-89b5b59de416
-- title:
--   Row data $q_i$, $d_i$, $G_i$, $b_i$, $p_i$ and the row classes
-- statement:
--   For a state and a row $i$:
--   $$q_i=\sum_{j\in T_i}a_{ij}^2,\qquad d_i=c_i+\sum_{j\in T_i}a_{ij}x_j,\qquad G_i=\sum_{j\in T_i}a_{ij}^2(1-x_j^2).$$
--   The retained row vector $b_i$ has $(b_i)_j=a_{ij}$ for $j\in T_i$ and $0$ otherwise, and $p_i=b_i\circ b_i$, $(p_i)_j=(b_i)_j^2$. A row is **large** if $q_i>K^2$, **medium** if $0<q_i\le K^2$, and completed if $q_i=0$.
--
--   The tracked row sum $d_i$ replaces the true row sum $(Ax)_i$ in the algorithm; the classes decide which constraint a row imposes on an update.
--
--   **Formalization Note** Vectors of $\mathbb R^V$ are represented as vectors of $\mathbb R^n$; $b_i$ and $p_i$ vanish off $T_i\subseteq V$.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), §2.1, p.4 (PDF p.5); §2.2, p.4; §2.3, p.5

import Mathlib
import Definitions.Def_VecBalPoly_K
import Definitions.Def_VecBalPoly_St

namespace VecBalPoly

variable {m n : ℕ}

/-- **The retained squared mass `qᵢ = ∑_{j∈Tᵢ} a²ᵢⱼ`** of row `i`.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), §2.1, p.4 (PDF p.5). -/
noncomputable def q (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (i : Fin m) : ℝ :=
  ∑ j ∈ st.T i, A i j ^ 2

/-- **The tracked row sum `dᵢ = cᵢ + ∑_{j∈Tᵢ} aᵢⱼxⱼ`.** Source: ibid., §2.1, p.4 (PDF p.5). -/
noncomputable def d (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (i : Fin m) : ℝ :=
  st.c i + ∑ j ∈ st.T i, A i j * st.x j

/-- **`Gᵢ = ∑_{j∈Tᵢ} a²ᵢⱼ(1 − x²ⱼ)`.** Source: ibid., §2.2, p.4 (PDF p.5). -/
noncomputable def G (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (i : Fin m) : ℝ :=
  ∑ j ∈ st.T i, A i j ^ 2 * (1 - st.x j ^ 2)

/-- **The retained row vector `bᵢ`**: `(bᵢ)ⱼ = aᵢⱼ` for `j ∈ Tᵢ`, zero otherwise.
Source: ibid., §2.3, p.5 (PDF p.6).

**Formalization Note** Vectors of `ℝ^V` are vectors of `ℝⁿ` supported on `V`; `Tᵢ ⊆ V` at every
state of the algorithm. -/
def b (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (i : Fin m) : Fin n → ℝ :=
  fun j => if j ∈ st.T i then A i j else 0

/-- **`pᵢ = bᵢ ∘ bᵢ`**, `(pᵢ)ⱼ = (bᵢ)ⱼ²`. Source: ibid., §2.3, p.5 (PDF p.6). -/
def p (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (i : Fin m) : Fin n → ℝ :=
  fun j => b A st i j ^ 2

/-- **Large row**: `qᵢ > K²`. Source: ibid., §2.2, p.4 (PDF p.5). -/
def IsLarge (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (i : Fin m) : Prop :=
  K ^ 2 < q A st i

/-- **Medium row**: `0 < qᵢ ≤ K²` (a row with `qᵢ = 0` is completed).
Source: ibid., §2.2, p.4 (PDF p.5). -/
def IsMedium (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (i : Fin m) : Prop :=
  0 < q A st i ∧ q A st i ≤ K ^ 2

end VecBalPoly


