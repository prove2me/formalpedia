-- Prove2me | Definitions.Def_MHSpectralGap_GlobalLip_Wasserstein
-- name    : MHSpectralGap_GlobalLip_Wasserstein
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:02:54.973323+00:00
-- url     : https://prove2.me/theorems/8dbc85f3-f8fe-4e51-a74a-94b25fe64d48
-- title:
--   Definitions 2.1–2.3, 2.5 and (2.1): Wasserstein and Harris objects
-- statement:
--   For measures $\nu_1,\nu_2$ on a measurable space $E$, a coupling is a measure $\pi$ on $E\times E$ whose two marginals are $\nu_1$ and $\nu_2$. For a nonnegative cost $d$, its Wasserstein lift is
--
--   $$W_d(\nu_1,\nu_2)=\inf_{\pi\in\mathrm{Couplings}(\nu_1,\nu_2)}\int d(x,y)\,\pi(dx,dy).$$
--
--   The file also defines a distance-like cost (nonnegative, symmetric, lower semicontinuous, and zero exactly on the diagonal), $d$-contraction with constant $c\in(0,1)$, $d$-smallness with constant $s\in(0,1)$, a Lyapunov bound $P^nV(x)\le l^nV(x)+K$ for every $n$, and the weighted cost $\widetilde d(x,y)=\sqrt{d(x,y)(1+V(x)+V(y))}$. These are the objects in the weak Harris theorem.
--
--   **Formalization Note** Wasserstein costs and expectations are nonnegative extended reals, avoiding a spurious zero for a nonintegrable cost. The constants are explicit so that uniform bounds over the finite dimensional chains have the same meaning as in the paper.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, pp. 8–9, Definitions 2.1–2.3, 2.5 and displays (2.1)–(2.2)

import Mathlib

namespace MHSpectralGap.GlobalLip

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Couplings of two measures, Definition 2.1 and (2.1). -/
def couplings {X : Type} [MeasurableSpace X] (ν₁ ν₂ : Measure X) : Set (Measure (X × X)) :=
  {π | π.map Prod.fst = ν₁ ∧ π.map Prod.snd = ν₂}

/-- The Wasserstein lift of a nonnegative cost, (2.1). -/
noncomputable def wass {X : Type} [MeasurableSpace X]
    (d : X → X → ℝ) (ν₁ ν₂ : Measure X) : ℝ≥0∞ :=
  ⨅ π ∈ couplings ν₁ ν₂, ∫⁻ p, ENNReal.ofReal (d p.1 p.2) ∂π

/-- Distance-like functions of Definition 2.1. -/
def IsDistanceLike {X : Type} [TopologicalSpace X] (d : X → X → ℝ) : Prop :=
  (∀ x y, 0 ≤ d x y) ∧ (∀ x y, d x y = d y x) ∧
  LowerSemicontinuous (fun p : X × X => d p.1 p.2) ∧
  (∀ x y, d x y = 0 ↔ x = y)

/-- Definition 2.2 with its contraction constant exposed. -/
def IsDContracting {X : Type} [MeasurableSpace X] (P : Kernel X X)
    (d : X → X → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ c < 1 ∧
  ∀ x y, d x y < 1 → wass d (P x) (P y) ≤ ENNReal.ofReal (c * d x y)

/-- Definition 2.3 with its smallness constant exposed. -/
def IsDSmall {X : Type} [MeasurableSpace X] (P : Kernel X X)
    (d : X → X → ℝ) (S : Set X) (s : ℝ) : Prop :=
  0 < s ∧ s < 1 ∧
  ∀ x ∈ S, ∀ y ∈ S, wass d (P x) (P y) ≤ ENNReal.ofReal s

/-- Definition 2.5 and (2.2), including the bound for every n. -/
def IsLyapunov {X : Type} [MeasurableSpace X] (P : Kernel X X)
    (V : X → ℝ) (l K : ℝ) : Prop :=
  (∀ x, 0 ≤ V x) ∧ 0 < K ∧ 0 ≤ l ∧ l < 1 ∧
  ∀ (n : ℕ) x, (∫⁻ y, ENNReal.ofReal (V y) ∂((P ^ n) x)) ≤
    ENNReal.ofReal (l ^ n * V x + K)

/-- The weighted distance in Proposition 2.6. -/
noncomputable def dTilde {X : Type} (d : X → X → ℝ) (V : X → ℝ)
    (x y : X) : ℝ :=
  Real.sqrt (d x y * (1 + V x + V y))

end MHSpectralGap.GlobalLip


