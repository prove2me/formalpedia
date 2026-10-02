-- Prove2me | Definitions.Def_TeschlQM_Shared_spectralMeasure
-- name    : TeschlQM_Shared_spectralMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T21:13:40.315495+00:00
-- url     : https://prove2.me/theorems/6777939a-2c8a-46b3-bd09-2e64a4c168e7
-- title:
--   Spectral measure μ_ψ(Ω) = ⟨ψ, P(Ω)ψ⟩ of a projection-valued measure
-- statement:
--   Let $P$ be a projection-valued measure on a complex Hilbert space $\mathfrak H$ and $\psi \in \mathfrak H$. The **spectral measure** of $\psi$ is the finite Borel measure on $\mathbb R$ given by
--   $$\mu_\psi(\Omega) = \langle \psi, P(\Omega)\psi \rangle = \|P(\Omega)\psi\|^2 .$$
--
--   This one definition is shared by every chunk of the series that uses it and is reviewed once for all of them. It serves:
--
--   - chunk `04-min-max`: p. 97, Section 3.1, Eqs. (3.50)–(3.51); p. 119, Theorem 4.12 (i); p. 119, Theorem 4.12 (ii)
--   - chunk `05-rage`: p. 105, Section 3.3, Eq. (3.83); p. 102, Eqs. (3.72)–(3.73); p. 127; pp. 123–124, Theorem 5.1; p. 128, Theorem 5.6, Eq. (5.13); p. 129, Theorem 5.7, Eq. (5.14); p. 130, Theorem 5.8, Eq. (5.18); p. 130, Corollary 5.9, Eqs. (5.19)–(5.20)
--   - chunk `14-scattering`: p. 247, Section 12.1, Eq. (12.3); p. 248, Lemma 12.1; p. 248, Theorem 12.2, Eq. (12.8); p. 249, Lemma 12.3, Eqs. (12.11)–(12.12); p. 249, Theorem 12.4
--
--   **Formalization Note.** Built with `Measure.ofMeasurable` from $\Omega \mapsto \|P(\Omega)\psi\|^2 \in [0, \infty]$ whenever that set function vanishes on $\emptyset$ and is countably additive on Borel sets, which holds for every projection-valued measure; for any other $P$ the zero measure is returned, a value that never enters a statement of this mission, since every statement using it assumes $P$ is a projection-valued measure.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 89, Section 3.1

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace TeschlQM.Shared

open Classical in
/-- Teschl, p. 89: the **spectral measure** `μ_ψ` of the vector `ψ` with respect to the
projection-valued measure `P`, the finite Borel measure with `μ_ψ(Ω) = ⟨ψ, P(Ω)ψ⟩ = ‖P(Ω)ψ‖²`.
It is built with `Measure.ofMeasurable` from `Ω ↦ ‖P(Ω)ψ‖²` whenever that set function vanishes
on `∅` and is countably additive on Borel sets (which holds for every projection-valued
measure); for any other `P` the value is the zero measure, a junk value that never occurs in
the statements of this mission, all of which assume `P` is a projection-valued measure. -/
noncomputable def spectralMeasure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : Set ℝ → (H →L[ℂ] H)) (ψ : H) : Measure ℝ :=
  if h : ((‖P ∅ ψ‖₊ : ℝ≥0∞) ^ 2 = 0 ∧
      ∀ ⦃Ω : ℕ → Set ℝ⦄, (∀ n, MeasurableSet (Ω n)) → Pairwise (Function.onFun Disjoint Ω) →
        (‖P (⋃ n, Ω n) ψ‖₊ : ℝ≥0∞) ^ 2 = ∑' n, (‖P (Ω n) ψ‖₊ : ℝ≥0∞) ^ 2) then
    Measure.ofMeasurable (fun Ω _ => (‖P Ω ψ‖₊ : ℝ≥0∞) ^ 2) h.1 (fun _ hΩ hd => h.2 hΩ hd)
  else 0

end TeschlQM.Shared


