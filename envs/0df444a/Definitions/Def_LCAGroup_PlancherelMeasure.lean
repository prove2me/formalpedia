-- Prove2me | Definitions.Def_LCAGroup_PlancherelMeasure
-- name    : LCAGroup_PlancherelMeasure
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T10:49:02.51301+00:00
-- url     : https://prove2.me/theorems/f5a98fc3-7db1-4b29-9194-b4d663c18333
-- title:
--   The Plancherel (dual Haar) measure $\mu_{\widehat G}$ on the Pontryagin dual of a locally compact abelian group
-- statement:
--   This is the **Plancherel measure** on the dual group: the Haar measure on $\widehat G$ that is dual to a given Haar measure on $G$.
--
--   Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\mu$, let $\widehat G$ be its Pontryagin dual (continuous characters $\chi\colon G\to U(1)$, compact-open topology), and for $f\in L^1(G,\mu)$ let
--   $$\widehat f(\chi)=\int_G f(x)\,\overline{\chi(x)}\,d\mu(x)\qquad(\chi\in\widehat G)$$
--   be its Fourier transform. A measure $\nu$ on $\widehat G$ is the **Plancherel measure of $\mu$** if
--
--   1. $\nu$ is a (regular) Haar measure on $\widehat G$, and
--   2. for every $f\in L^1(G,\mu)\cap L^2(G,\mu)$ the function $\widehat f$ belongs to $L^2(\widehat G,\nu)$ and
--   $$\|\widehat f\|_{L^2(\widehat G,\nu)}=\|f\|_{L^2(G,\mu)} .$$
--
--   By the Plancherel theorem such a $\nu$ exists and is unique (Lemma D.1.1.2(4) of the source); it is also the Haar measure on $\widehat G$ for which the Fourier inversion formula $f(x)=\int_{\widehat G}\widehat f(\chi)\chi(x)\,d\nu(\chi)$ holds. Replacing $\mu$ by $c\mu$ replaces $\nu$ by $c^{-1}\nu$. For example, the Plancherel measure of the counting measure on a discrete group is the Haar probability measure of its compact dual, and Lebesgue measure on $\mathbb R$ is its own Plancherel measure when $\widehat{\mathbb R}$ is identified with $\mathbb R$ through the characters $x\mapsto e^{2\pi i x\xi}$. The source uses the Plancherel measure to normalise the measures in the Poisson summation formula (Situation D.1.2.6) and for the Fourier transform on Schwartz–Bruhat spaces.
--
--   **Formalization Note.** `LCAGroup.IsPlancherelMeasure μ ν` is a predicate on a measure `μ` on `G` and a measure `ν` on `PontryaginDual G`: it is the conjunction of `ν.IsHaarMeasure`, `ν.Regular` and, for all `f : G → ℂ` with `Integrable f μ` and `MemLp f 2 μ`, of `MemLp f̂ 2 ν` and `eLpNorm f̂ 2 ν = eLpNorm f 2 μ`, where `f̂ = RiemannMasullo.lcaFourier μ f` is the Bochner integral $\chi\mapsto\int f(x)\overline{\chi(x)}\,d\mu$ of the platform definition `RiemannMasullo_LCAFourierConvolution`. Mathlib puts no $\sigma$-algebra on `PontryaginDual G`, so the definition takes an arbitrary `[MeasurableSpace (PontryaginDual G)]`; the theorems add `[BorelSpace (PontryaginDual G)]`. `Regular` is Mathlib's `Measure.Regular` (a Radon measure in the classical sense; automatic for Haar measures on second countable groups). No condition on `μ` is built in: the theorems assume that `μ` is a regular Haar measure.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 747, Lemma D.1.1.2(4), eq. (D.1.1.9); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Theorem 3.4.8 and p. 77

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution

/-!
# The Plancherel (dual Haar) measure on the Pontryagin dual of a locally compact abelian group

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix D,
Lemma D.1.1.2(4), eq. (D.1.1.9), p. 747.

Let `G` be a Hausdorff locally compact abelian group with a Haar measure `μ`, and let
`f̂(χ) = ∫ f(x) conj(χ(x)) dμ(x)` be the Fourier transform (D.1.1.4) of `f ∈ L¹(G, μ)`, a function on
the Pontryagin dual `Ĝ` (`RiemannMasullo.lcaFourier μ f`).  The *Plancherel measure* (dual measure)
of `μ` is the Haar measure `ν` on `Ĝ` for which `‖f̂‖_{L²(ν)} = ‖f‖_{L²(μ)}` for all
`f ∈ L¹(G, μ) ∩ L²(G, μ)`.
-/

namespace LCAGroup

open MeasureTheory

/-- `IsPlancherelMeasure μ ν`: the measure `ν` on the Pontryagin dual `Ĝ` is the Plancherel
measure of the measure `μ` on `G` (Lemma D.1.1.2(4)): `ν` is a regular Haar measure on `Ĝ`, and for
every `f ∈ L¹(G, μ) ∩ L²(G, μ)` the Fourier transform `f̂` lies in `L²(Ĝ, ν)` and
`‖f̂‖_{L²(ν)} = ‖f‖_{L²(μ)}` (D.1.1.9). -/
def IsPlancherelMeasure {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]
    [MeasurableSpace (PontryaginDual G)] (μ : Measure G) (ν : Measure (PontryaginDual G)) : Prop :=
  ν.IsHaarMeasure ∧ ν.Regular ∧
    ∀ f : G → ℂ, Integrable f μ → MemLp f 2 μ →
      MemLp (RiemannMasullo.lcaFourier μ f) 2 ν ∧
        eLpNorm (RiemannMasullo.lcaFourier μ f) 2 ν = eLpNorm f 2 μ

end LCAGroup


