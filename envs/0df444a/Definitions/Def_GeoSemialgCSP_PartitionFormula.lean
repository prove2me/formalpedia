-- Prove2me | Definitions.Def_GeoSemialgCSP_PartitionFormula
-- name    : GeoSemialgCSP_PartitionFormula
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:59.173205+00:00
-- url     : https://prove2.me/theorems/7540321a-358a-4630-b3de-aa7bac0db20d
-- title:
--   The partition property of Theorem 7.1
-- statement:
--   A set $\Theta\subseteq\mathbb R^{d+p}$ (the solution set of a formula $\theta(x;y)$, $x\in\mathbb R^d$, $y\in\mathbb R^p$, with $C(y)=\{x:\theta(x;y)\}$) has the **partition property of Theorem 7.1** for the predicate $P$ (accepting set $S$) with constants $d_{\mathrm{fVC}}$ and $K_P$ if for every finitely supported probability measure $\mu_X$ on $\mathbb R^d$ and every $0<\varepsilon<1$ there is a partition $\mathbb R^d=C_0\sqcup\dots\sqcup C_{q-1}$ into $q\le K_P\varepsilon^{-K_P}$ nonempty cells $C_a=C(y_a)$ such that, with $\mu(a)=\mu_X(C_a)$ and $\Delta=\{(a_1,\dots,a_k): P\text{ is not constant on }C_{a_1}\times\dots\times C_{a_k}\}$ (14),
--
--   1. (a) $\mu_X^{\otimes k}\bigl(\bigcup_{a\in\Delta}C_{a_1}\times\dots\times C_{a_k}\bigr)=\mu^{\otimes k}(\Delta)\le\varepsilon$;
--   2. (b) $\mathrm{fVC}(\Delta)\le d_{\mathrm{fVC}}$.
--
--   **Formalization Note** $\mu_X$ is given by atoms $x:\mathrm{Fin}\,n\to\mathbb R^d$ with simplex masses $w$; the bound $q\le N_P(\varepsilon)\le K_P\varepsilon^{-K_P}$ is written $q\le K_P\varepsilon^{-K_P}$ (rpow).
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 7.1, Eq. (14), p.20 (PDF p.21)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_IsPartitionOf
import Definitions.Def_GeoSemialgCSP_multilin
import Definitions.Def_GeoSemialgCSP_fVC

namespace GeoSemialgCSP

/-- **The partition property of Theorem 7.1.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 7.1, Eq. (14), printed
p.20 (PDF p.21): the "following property" of the formula `θ(x; y)` (`x ∈ ℝ^d`, `y ∈ ℝ^p`) with the
constants `d_fVC(P)` and `K_P` (`N_P(ε) ≤ K_P ε^{−K_P}`). For every finitely supported probability
measure `μ_X` on `ℝ^d` and every `0 < ε < 1` there is a partition `ℝ^d = C₀ ⊔ ⋯ ⊔ C_{q−1}` into
`q ≤ K_P ε^{−K_P}` nonempty cells `C_a = C(y_a) = {x : θ(x; y_a)}` such that, with
`μ(a) = μ_X(C_a)` and `Δ` the label tuples on whose cell product `P` is not constant,
(a) `μ_X^{⊗k}(⋃_{a ∈ Δ} C_{a₁} × ⋯ × C_{a_k}) = μ^{⊗k}(Δ) ≤ ε` and (b) `fVC(Δ) ≤ d_fVC(P)`.

**Formalization Note.** `θ` is its solution set `Θ ⊆ ℝ^{d+p}` (point coordinates first, then the
parameter, via `Fin.append`). `μ_X` has atoms `x : Fin n → E d` and masses `w` in the simplex.
"`q ≤ N_P(ε) ≤ K_P ε^{−K_P}`" is written `q ≤ K_P ε^{−K_P}` (`Real.rpow`). -/
def PartitionFormula {k d p : ℕ} (S : Set (Fin k → E d)) (dfVC : ℕ) (KP : ℝ)
    (Θ : Set (Fin (d + p) → ℝ)) : Prop :=
  ∀ (n : ℕ) (x : Fin n → E d) (w : Fin n → ℝ), w ∈ stdSimplex ℝ (Fin n) →
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ (q : ℕ) (y : Fin q → (Fin p → ℝ)), (q : ℝ) ≤ KP * ε ^ (-KP) ∧
    let C : Fin q → Set (E d) := fun a => {z : E d | Fin.append (fun i => z i) (y a) ∈ Θ}
    let μ : Fin q → ℝ := fun a => ∑ i, (x ⁻¹' C a).indicator w i
    let Δ : Set (Fin k → Fin q) := {a | ∃ u v : Fin k → E d, (∀ j, u j ∈ C (a j)) ∧
      (∀ j, v j ∈ C (a j)) ∧ u ∈ S ∧ v ∉ S}
    IsPartitionOf C Set.univ ∧
    (∑ i : Fin k → Fin n, (∏ j, w (i j)) *
        (⋃ a ∈ Δ, {u : Fin k → E d | ∀ j, u j ∈ C (a j)}).indicator 1 (x ∘ i) =
      multilin (Δ.indicator 1) (fun _ => μ)) ∧
    multilin (Δ.indicator 1) (fun _ => μ) ≤ ε ∧
    fVC Δ ≤ (dfVC : ℕ∞)

end GeoSemialgCSP


