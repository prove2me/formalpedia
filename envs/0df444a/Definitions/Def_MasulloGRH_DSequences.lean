-- Prove2me | Definitions.Def_MasulloGRH_DSequences
-- name    : MasulloGRH_DSequences
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:21:14.48691+00:00
-- url     : https://prove2.me/theorems/9b302a56-ac79-4856-9467-12b14d3a81f4
-- title:
--   D-sequences, averages and the maximal function on a locally compact abelian group
-- statement:
--   These are the differentiation bases used for the maximal theorem and the Lebesgue differentiation theorem on locally compact abelian groups.
--
--   Let $G$ be an abelian topological group with a measure $\mu$, and $(U_k)_{k\ge0}$ a sequence of subsets of $G$.
--
--   1. $(U_k)$ is a **D-sequence** with structural constant $C>0$ if every $U_k$ is $\mu$-measurable and contains the neutral element, and for every $k\ge0$:
--      - (integrability) $0<\mu(U_k)<\infty$;
--      - (monotonicity) $U_{k+1}\subset U_k$;
--      - (doubling) $0<\mu(U_kU_k^{-1})<C\,\mu(U_k)$.
--   2. $(U_k)$ is a **D′-sequence** if it is a D-sequence and every neighbourhood of the neutral element contains some $U_k$.
--   3. The **average** of a function $f$ over the translate $xU_k$ is
--   $$A_{U_k}(f)(x)=\frac{1}{\mu(U_k)}\int_{xU_k}f(y)\,d\mu(y).$$
--   4. The **maximal function** of $f$ is
--   $$(Mf)(x)=\limsup_{k\ge0}\frac{1}{\mu(U_k)}\int_{xU_k}|f(y)|\,d\mu(y)\in[0,\infty].$$
--
--   D′-sequences play the role of the intervals $(-r,r)$, $r\to0^+$, on the real line.
--
--   **Formalization Note** "$\mu$-measurable" is measurability with respect to the completion of $\mu$. The maximal function takes values in the extended non-negative reals.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix A, §A.5, Definition A.5.2.1 (p. 569); eq. (A.5.3.16) (p. 582); eq. (A.5.4.1) (p. 582)

import Mathlib

/-!
# D-sequences, averages and maximal functions on locally compact abelian groups

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix A, §A.5:
Definition A.5.2.1 (p. 569), eq. (A.5.3.16) (p. 582), eq. (A.5.4.1) (p. 582).
-/

namespace MasulloGRH

open MeasureTheory Pointwise

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]

/-- Definition A.5.2.1: `U` is a *D-sequence* in `G` for the measure `μ`, with structural constant
`C`: every `U k` is `μ`-measurable and contains the neutral element, `0 < μ (U k) < ∞`,
`U (k+1) ⊆ U k`, and `0 < μ (U k · (U k)⁻¹) < C · μ (U k)` for all `k`, with `C > 0`. -/
structure IsDSequence (μ : Measure G) (U : ℕ → Set G) (C : ℝ) : Prop where
  one_mem : ∀ k, (1 : G) ∈ U k
  nullMeasurable : ∀ k, NullMeasurableSet (U k) μ
  measure_pos : ∀ k, 0 < μ (U k)
  measure_lt_top : ∀ k, μ (U k) < ⊤
  antitone : ∀ k, U (k + 1) ⊆ U k
  const_pos : 0 < C
  doubling : ∀ k, 0 < μ (U k * (U k)⁻¹) ∧ μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k)

/-- Definition A.5.2.1: a *D′-sequence* is a D-sequence such that every neighbourhood of the
neutral element contains some `U k`. -/
def IsDPrimeSequence (μ : Measure G) (U : ℕ → Set G) (C : ℝ) : Prop :=
  IsDSequence μ U C ∧ ∀ V ∈ nhds (1 : G), ∃ k, U k ⊆ V

/-- The average `A_{U_k}(f)(x) = μ(U_k)⁻¹ ∫_{x U_k} f dμ` of `f` over the translate `x U_k`
(A.5.4.1). -/
def dAverage (μ : Measure G) (U : ℕ → Set G) (f : G → ℂ) (k : ℕ) (x : G) : ℂ :=
  ((μ (U k)).toReal)⁻¹ • ∫ y in x • U k, f y ∂μ

/-- The maximal function `(M f)(x) = limsup_k μ(U_k)⁻¹ ∫_{x U_k} |f| dμ` (A.5.3.16), with values
in `[0, ∞]`. -/
def dMaximal (μ : Measure G) (U : ℕ → Set G) (f : G → ℂ) (x : G) : ENNReal :=
  Filter.limsup (fun k : ℕ => (∫⁻ y in x • U k, ‖f y‖ₑ ∂μ) / μ (U k)) Filter.atTop

end

end MasulloGRH


