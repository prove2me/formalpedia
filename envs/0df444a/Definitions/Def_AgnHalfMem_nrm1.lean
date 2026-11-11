-- Prove2me | Definitions.Def_AgnHalfMem_nrm1
-- name    : AgnHalfMem_nrm1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:44.049797+00:00
-- url     : https://prove2.me/theorems/b6d5ebc6-10c7-4865-b9bd-049b9f20fd41
-- title:
--   Uniform-normalized norms and inner product on functions $H\to\mathbb R$
-- statement:
--   Let $H$ be a finite nonempty set. For $f,g:H\to\mathbb R$ the norms and inner product are taken with respect to the uniform distribution on $H$:
--   $$
--   \|f\|_1=\mathbb E_{h\in_R H}|f(h)|,\qquad \|f\|_2=\big(\mathbb E_{h\in_R H}f(h)^2\big)^{1/2},\qquad \langle f,g\rangle=\mathbb E_{h\in_R H}[f(h)g(h)].
--   $$
--   For a matrix $M:X\times H\to\mathbb R$ and a row $x$, $\langle M_x,f\rangle=\frac1{|H|}\sum_h M(x,h)f(h)$. We also write $n=\log_2|H|$, so that a probability distribution $P$ on $H$ has $\|P\|_1=2^{-n}$.
--
--   **Formalization Note** These are the normalized norms of the paper, not counting norms; all constants of Appendix B depend on the normalization.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), §2, p.7; App. B, p.29

import Mathlib

namespace AgnHalfMem

/-- **Norms and inner products on `H → ℝ`.** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for
Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), §2, p.7: "For a function f : H → ℝ, denote by ‖f‖_p the ℓp norm of f, with
respect to the uniform distribution over H, that is: ‖f‖_p = (E_{h ∈_R H}[|f(h)|^p])^{1/p}. For two
functions f, g : H → ℝ, define their inner product with respect to the uniform distribution over H
as ⟨f, g⟩ = E_{h ∈_R H}[f(h) · g(h)]." App. B, p.29: "Let n = log₂ |H|."

`nrm1 f = (Σ_h |f h|)/|H|`, `nrm2 f = ((Σ_h f h²)/|H|)^{1/2}`, `ip f g = (Σ_h f h g h)/|H|`, and
`logCard H = log₂ |H|` (the paper's `n`, so that `2^{−n} = 1/|H|`).

**Formalization Note.** These are the uniform-normalized norms of p.7, not the counting norms;
`H` is a finite type (nonempty wherever the norms are used). -/
noncomputable def nrm1 {H : Type*} [Fintype H] (f : H → ℝ) : ℝ :=
  (∑ h, |f h|) / Fintype.card H

/-- `‖f‖₂ = (E_{h ∈_R H} f(h)²)^{1/2}` (p.7). -/
noncomputable def nrm2 {H : Type*} [Fintype H] (f : H → ℝ) : ℝ :=
  Real.sqrt ((∑ h, f h ^ 2) / Fintype.card H)

/-- `⟨f, g⟩ = E_{h ∈_R H}[f(h) g(h)]` (p.7). -/
noncomputable def ip {H : Type*} [Fintype H] (f g : H → ℝ) : ℝ :=
  (∑ h, f h * g h) / Fintype.card H

/-- `n = log₂ |H|` (App. B, p.29). -/
noncomputable def logCard (H : Type*) [Fintype H] : ℝ :=
  Real.logb 2 (Fintype.card H)

end AgnHalfMem


