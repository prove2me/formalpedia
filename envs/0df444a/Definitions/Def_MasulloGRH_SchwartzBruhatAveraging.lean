-- Prove2me | Definitions.Def_MasulloGRH_SchwartzBruhatAveraging
-- name    : MasulloGRH_SchwartzBruhatAveraging
-- status  : Definition
-- author  : @sflicht
-- created : 2026-11-21T14:37:43.902584+00:00
-- url     : https://prove2.me/theorems/b25cbdc1-280e-48ca-b14b-8e7d49b22bd7
-- title:
--   Normalized Haar measure of a compact subgroup and the averaging operators $A_{\Gamma,k}$ on functions on $G$
-- statement:
--   Let $G$ be a Hausdorff locally compact abelian group (written multiplicatively).
--
--   1. For a subgroup $k\subseteq G$, let $\mu_k$ denote the **normalized Haar measure** of $k$: when $k$ is compact, $\mu_k$ is the unique translation-invariant Borel probability measure on $k$ (with its subspace topology and Borel $\sigma$-algebra). When $k$ is not compact we set $\mu_k:=0$; this case never arises for good subgroups, which are compact.
--   2. For a pair of subgroups $(\Gamma,k)$ and a function $f\colon G\to\mathbb C$, the **averaging operator** is
--
--   $$
--   (A_{\Gamma,k}f)(x)\;=\;\mathbf 1_\Gamma(x)\int_k f(xy)\,d\mu_k(y)\qquad(x\in G).
--   $$
--
--   For a structural pair $(\Gamma,k)$ this is the operator that sends a Schwartz–Bruhat function on $G$ to a function that is supported on $\Gamma$ and $k$-invariant. Together with the inclusions $\mathcal S(\Gamma/k)\hookrightarrow\mathcal S(G)$, these operators give the compatible projections in the directed system of spaces $\mathcal S(\Gamma/k)$, as in the construction of $\mathcal S(G)$ in Bruhat's work and the averaging maps $\Phi_k$ of Masullo's Theorem D.1.7.1.
--
--   **Formalization Note** `subgroupHaar k` is Mathlib's `Measure.haarMeasure ⊤` on the compact space `↥k` with the Borel σ-algebra `borel ↥k`, so it gives total mass $1$ to $k$. `schwartzBruhatAverage Γ k f` is the indicator of `Γ` times the Bochner integral $\int_k f(x\,y)\,d\mu_k(y)$. It is defined for every function $f\colon G\to\mathbb C$; integrability holds for continuous $f$, in particular for Schwartz–Bruhat functions.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D: averaging map (D.1.7.2) in Theorem D.1.7.1 (p. 776) and Lemma D.1.6.18 (p. 772), used for the averaging operators in the proof of Theorem D.1.5.7 (pp. 760–764); F. Bruhat, Distributions sur un groupe localement compact, Bull. SMF 89 (1961), §9

import Definitions.Def_MasulloGRH_SchwartzBruhat

/-!
# The averaging operators on the Schwartz–Bruhat space

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix D, §D.1.5,
proof of Theorem D.1.5.7 (pp. 760–764); F. Bruhat, *Distributions sur un groupe localement
compact*, Bull. SMF 89 (1961).

For a subgroup `k` of `G` we write `subgroupHaar k` for the normalized Haar measure of `k`
(with its Borel σ-algebra) when `k` is compact, and `0` otherwise.  For a pair of subgroups
`(Γ, k)` the averaging operator is
`(A_{Γ,k} f)(x) = 1_Γ(x) ∫_k f(x y) dy`.
-/

namespace MasulloGRH

open MeasureTheory

noncomputable section

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

open Classical in
/-- The normalized Haar measure (a probability measure) of a compact subgroup `k`, on the Borel
σ-algebra of `k`; it is `0` when `k` is not compact. -/
def subgroupHaar (k : Subgroup G) : @Measure k (borel k) :=
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  if h : IsCompact (k : Set G) then
    haveI : CompactSpace k := isCompact_iff_compactSpace.mp h
    Measure.haarMeasure ⊤
  else 0

/-- The averaging operator `(A_{Γ,k} f)(x) = 1_Γ(x) ∫_k f(x y) dy` of a pair of subgroups
`(Γ, k)`, with `dy` the normalized Haar measure of `k`. -/
def schwartzBruhatAverage (Γ k : Subgroup G) (f : G → ℂ) : G → ℂ :=
  letI : MeasurableSpace k := borel k
  Set.indicator (Γ : Set G) (fun x => ∫ y : k, f (x * y) ∂ subgroupHaar k)

end

end MasulloGRH


