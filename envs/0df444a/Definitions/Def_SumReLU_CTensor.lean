-- Prove2me | Definitions.Def_SumReLU_CTensor
-- name    : SumReLU_CTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:24.380841+00:00
-- url     : https://prove2.me/theorems/2728b321-bf89-4fe0-9b83-cade96ea6973
-- title:
--   Complex tensors, the conjugate-linear inner product and the Frobenius norm
-- statement:
--   A complex tensor of dimension $d$ and order $p$ is an array $(W)_{i_1,\dots,i_p}$ with complex entries, $i_1,\dots,i_p\in[d]$. The entrywise inner product and the Frobenius norm are
--   $$
--   \langle W,T\rangle=\sum_{i_1,\dots,i_p}\overline{(W)_{i_1\dots i_p}}\,(T)_{i_1\dots i_p},\qquad \|W\|_F^2=\sum_{i_1,\dots,i_p}|W_{i_1\dots i_p}|^2 .
--   $$
--   The inner product is conjugate-linear in its first argument. For a real vector $w$ and a complex vector $u$, $w\cdot u=\sum_j w_ju_j$ (no conjugation).
--
--   **Formalization Note** Index tuples are functions `Fin p → Fin d`.
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), §2, pp.9–10 (PDF pp.11–12); proof of Lemma 4.26, p.41 (PDF p.43)

import Mathlib

namespace SumReLU

/-- A complex tensor of dimension `d` and order `p`, `W ∈ (ℂᵈ)^{⊗p}`: a `p`-index array
`(W)_{i₁,…,i_p}` with complex entries, indexed by tuples `Fin p → Fin d`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), §2, p.9 (PDF p.11). -/
abbrev CTensor (d p : ℕ) := (Fin p → Fin d) → ℂ

/-- The entrywise inner product `⟨W, T⟩ = ∑_{i₁,…,i_p} \overline{(W)_{i₁…i_p}} (T)_{i₁…i_p}`,
conjugate-linear in its first argument (§2, p.10, PDF p.12, on the rendered page; p.41, PDF p.43:
"the inner product is conjugate-linear in its first argument"). -/
noncomputable def cinner {d p : ℕ} (A B : CTensor d p) : ℂ := ∑ J, star (A J) * B J

/-- The Frobenius norm `‖W‖_F = (∑ |W_{i₁…i_p}|²)^{1/2}` (§2, p.10, PDF p.12). -/
noncomputable def frob {d p : ℕ} (A : CTensor d p) : ℝ := Real.sqrt (∑ J, ‖A J‖ ^ 2)

/-- `w · u = ∑_j w_j u_j` for a real vector `w` and a complex vector `u`, without conjugation
(so `|w · u|^{2p} = (w · u)^p (w · ū)^p`, Claim 4.15, p.35, PDF p.37). -/
noncomputable def dotC {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (u : Fin d → ℂ) : ℂ :=
  ∑ j, (w j : ℂ) * u j

end SumReLU


