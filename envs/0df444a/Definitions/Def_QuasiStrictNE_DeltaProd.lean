-- Prove2me | Definitions.Def_QuasiStrictNE_DeltaProd
-- name    : QuasiStrictNE_DeltaProd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:01.980413+00:00
-- url     : https://prove2.me/theorems/c65bd059-683a-4b4a-a2ba-8b278d4f1195
-- title:
--   The polytope $\Delta_m\times\Delta_n\subseteq\mathbb R^{m+n}$
-- statement:
--   $\Delta_m\times\Delta_n$ is the set of $z\in\mathbb R^{m+n}$ whose first $m$ coordinates form a point of $\Delta_m$ and whose last $n$ coordinates form a point of $\Delta_n$.
--
--   **Formalization Note** $\mathbb R^{m+n}$ is `Fin (m + n) → ℝ`, split with `Fin.castAdd`/`Fin.natAdd`.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Lemma 5, p.16

import Mathlib

namespace QuasiStrictNE

/-- **The strategy-profile polytope `Δm × Δn ⊆ ℝ^{m+n}`** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Lemma 5, p.16: "for
z ∈ R^{m+n} that outputs No if z ∉ ∆m × ∆n").

`DeltaProd m n` is the set of `z ∈ ℝ^{m+n}` whose first `m` coordinates form a point of `Δm` and whose
last `n` coordinates form a point of `Δn`.

**Formalization Note** `ℝ^{m+n}` is `Fin (m + n) → ℝ`; the first block is `z ∘ Fin.castAdd n` and the
second `z ∘ Fin.natAdd m` (the inverse of `Fin.append`). -/
def DeltaProd (m n : ℕ) : Set (Fin (m + n) → ℝ) :=
  {z | (fun i => z (Fin.castAdd n i)) ∈ stdSimplex ℝ (Fin m) ∧
    (fun j => z (Fin.natAdd m j)) ∈ stdSimplex ℝ (Fin n)}

end QuasiStrictNE


