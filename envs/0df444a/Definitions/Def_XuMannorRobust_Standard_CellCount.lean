-- Prove2me | Definitions.Def_XuMannorRobust_Standard_CellCount
-- name    : XuMannorRobust_Standard_CellCount
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T15:29:02.22853+00:00
-- url     : https://prove2.me/theorems/3b6abd2b-d18f-4d5b-ba32-0bd937f5a881
-- title:
--   Cell counts $|N_i|$ of a training set in a partition
-- statement:
--   Let $C_1, \dots, C_K$ be subsets of a sample space $\mathcal Z$ and let $\mathbf s = (s_1, \dots, s_n) \in \mathcal Z^n$ be a training set. The set of indices of training points falling in the $i$-th cell is $N_i = \{ j \in \{1, \dots, n\} : s_j \in C_i \}$, and the **cell count** is its cardinality
--
--   $$|N_i| = \#\{ j : s_j \in C_i \}.$$
--
--   When the cells partition $\mathcal Z$ and $\mathbf s$ consists of $n$ i.i.d. draws from $\mu$, the vector $(|N_1|, \dots, |N_K|)$ is multinomial with parameters $n$ and $(\mu(C_1), \dots, \mu(C_K))$; its deviation $\sum_i \big| |N_i|/n - \mu(C_i) \big|$ is the quantity controlled in the proof of Theorem 1.
--
--   **Formalization Note** Indices run over `Fin n`, i.e. $0, \dots, n-1$. Membership is decided classically.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 396, proof of Theorem 1 (definition of N_i)

import Mathlib

namespace XuMannorRobust.Standard

open Classical in
/-- **Cell counts** (Xu & Mannor 2012, p. 396, proof of Theorem 1): for a family of cells
`C : Fin K → Set Z` and a training set `s : Fin n → Z`, `cellCount C s i = |N_i|` is the number of
indices `j` with `s_j ∈ C_i`. -/
noncomputable def cellCount {Z : Type*} {n K : ℕ} (C : Fin K → Set Z) (s : Fin n → Z)
    (i : Fin K) : ℕ :=
  (Finset.univ.filter fun j => s j ∈ C i).card

end XuMannorRobust.Standard


