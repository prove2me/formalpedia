-- Prove2me | Definitions.Def_RLCDiscrepancy_relDev
-- name    : RLCDiscrepancy_relDev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:19.551935+00:00
-- url     : https://prove2.me/theorems/c6fbf7b4-10f5-49d0-ab92-f12e3f06ba74
-- title:
--   Relative deviation $\delta_{C,f}$ of a linear code
-- statement:
--   For a linear code $C\subseteq\mathbb F_q^n$ (a subspace) and a function $f:\mathbb F_q^n\to\mathbb R$, write $f(C)=\sum_{x\in C}f(x)$. The **relative deviation** of $C$ with respect to $f$ is
--
--   $$
--   \delta_{C,f}=\frac{f(C)}{|C|}-1 .
--   $$
--
--   For normalized $f$ this is $\mathbb E_{x\sim C}[f(x)]-\mathbb E_{x\sim\mathbb F_q^n}[f(x)]$, the amount by which the code over- or under-samples $f$ relative to the whole space. It is the central quantity of the mission: Theorem 2.4 bounds it uniformly over the translates of $f$.
--
--   **Formalization Note** Defined by the last expression for every real $f$. $C$ is a `Submodule`, always nonempty since it contains $0$; the auxiliary `codeFinset C` lists its vectors.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 2.2, p.13

import Mathlib

namespace RLCDiscrepancy

/-- The vectors of a linear code `C ⊆ F^n`, as a `Finset` (membership decided classically). -/
noncomputable def codeFinset {F : Type*} [Field F] [Fintype F] {n : ℕ} (C : Submodule F (Fin n → F)) :
    Finset (Fin n → F) := by
  classical exact Finset.univ.filter (· ∈ C)

@[simp] theorem mem_codeFinset {F : Type*} [Field F] [Fintype F] {n : ℕ} (C : Submodule F (Fin n → F))
    (x : Fin n → F) : x ∈ codeFinset C ↔ x ∈ C := by
  classical simp [codeFinset]

/-- **Relative deviation δ_{C,f}** (Definition 2.2). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 2.2, p.13:
"Let f : F^n_q → R≥0 be normalized, and let C ⊆ F^n_q be nonempty. Write f(C) := ∑_{x∈C} f(x).
The relative deviation of C with respect to f is
δ_{C,f} := E_{x∼C}[f(x)] − E_{x∼F^n_q}[f(x)] = f(C)/|C| − 1."

**Formalization Note.** δ is defined by the last expression, f(C)/|C| − 1, for every real `f`
(it equals the difference of expectations when `f` is normalized). `C` is a linear code
(a `Submodule`), which is how every code of the paper's §4 and Theorem 2.4 arises; it is
nonempty since it contains `0`, and |C| is the number of its vectors. -/
noncomputable def relDev {F : Type*} [Field F] [Fintype F] {n : ℕ} (C : Submodule F (Fin n → F))
    (f : (Fin n → F) → ℝ) : ℝ :=
  (∑ x ∈ codeFinset C, f x) / (codeFinset C).card - 1

end RLCDiscrepancy


