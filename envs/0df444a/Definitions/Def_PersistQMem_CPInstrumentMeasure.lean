-- Prove2me | Definitions.Def_PersistQMem_CPInstrumentMeasure
-- name    : PersistQMem_CPInstrumentMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:31:20.482184+00:00
-- url     : https://prove2.me/theorems/d76ffbc8-07ca-4bcb-b4b7-76fe596bdb6d
-- title:
--   Completely positive instrument-valued measures, Choi matrices and measurable adaptive instruments
-- statement:
--   For a linear map $\mathcal E$ from $d\times d$ to $K\times K$ matrices, the **Choi matrix** on $\mathbb C^d\otimes\mathbb C^K$ (input $\otimes$ output) is
--   $$\Gamma=\sum_{i,j}|i\rangle\langle j|\otimes\mathcal E(|i\rangle\langle j|),$$
--   so that $\mathcal E(Z)=\operatorname{Tr}_{\mathrm{in}}[(Z^{\mathsf T}\otimes I_K)\Gamma]$. A **complete completely positive instrument** on a measurable record space $\mathcal X$ assigns to every measurable event $S$ a linear map $\mathcal E(S)$ whose Choi matrix $\Gamma(S)$ is positive semidefinite, such that $S\mapsto\mathcal E(S)(Z)$ is countably additive for every $Z$ and $\mathcal E(\mathcal X)$ is trace preserving.
--
--   A **measurable adaptive instrument** (§6.6) is a family $h\mapsto\mathcal E_h$ of such instruments indexed by parent histories $h$, such that every entry of $\Gamma_h(S)$ is measurable in $h$ for every measurable next-record event $S$.
--
--   These are the instruments of the continuous-outcome extension of Theorem 2.2; §6.6 represents them by Kraus densities.
--
--   **Formalization Note** Values on non-measurable sets play no role. Countable additivity is convergence of the series in the entrywise topology of matrices.
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §6.6, pp.27–28 (PDF pp.30–31)

import Mathlib

open scoped Matrix ComplexOrder Kronecker
open MeasureTheory

namespace PersistQMem

/-- The Choi matrix `Γ = Σ_{i,j} |i⟩⟨j| ⊗ E(|i⟩⟨j|)` of a linear map `E` from `d × d` to `K × K`
matrices, on `C^d ⊗ C^K` (input ⊗ output) (Tao, Shen, *Structural Lower Bounds for Quantum Property
Estimation with Persistent Memory*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 6d48ad24…, §6.6, pp.27–28). With this order, `E(Z) = Tr_in[(Zᵀ ⊗ I_K) Γ]` and
`Tr_out Γ = I_d` for a trace-preserving `E` ((72)–(73), p.28). -/
def choi {d K : ℕ} (E : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin K) (Fin K) ℂ) :
    Matrix (Fin d × Fin K) (Fin d × Fin K) ℂ :=
  Matrix.of fun p q => E (Matrix.single p.1 q.1 1) p.2 q.2

/-- **A complete completely positive instrument on a measurable record space (§6.6, p.27).** For
every measurable event `S ⊆ X` of records, `E(S)` is a linear map from `d × d` to `K × K` matrices
that is completely positive (its Choi matrix `Γ(S)` is positive semidefinite); `S ↦ E(S)(Z)` is
countably additive for every `Z`; and the total map `E(X)` is trace preserving.

**Formalization Note.** Values on non-measurable sets are irrelevant. Countable additivity is
`HasSum` in the (entrywise) topology of matrices. -/
structure CPInstrumentMeasure (X : Type) [MeasurableSpace X] (d K : ℕ) where
  E : Set X → Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin K) (Fin K) ℂ
  cp : ∀ S, MeasurableSet S → (choi (E S)).PosSemidef
  countably_additive : ∀ S : ℕ → Set X, (∀ n, MeasurableSet (S n)) →
    Pairwise (Function.onFun Disjoint S) → ∀ Z, HasSum (fun n => E (S n) Z) (E (⋃ n, S n) Z)
  complete : ∀ Z, (E Set.univ Z).trace = Z.trace

/-- **A measurable adaptive instrument (§6.6, p.27).** For each parent history `h ∈ Y`,
`S ↦ E_h(S)` is a complete CP instrument, and every entry of its Choi matrix `Γ_h(S)` is measurable
in `h` for each measurable next-record event `S`. -/
def IsMeasurableAdaptive {Y X : Type} [MeasurableSpace Y] [MeasurableSpace X] {d K : ℕ}
    (E : Y → CPInstrumentMeasure X d K) : Prop :=
  ∀ S, MeasurableSet S → ∀ p q, Measurable fun h => choi ((E h).E S) p q

end PersistQMem


