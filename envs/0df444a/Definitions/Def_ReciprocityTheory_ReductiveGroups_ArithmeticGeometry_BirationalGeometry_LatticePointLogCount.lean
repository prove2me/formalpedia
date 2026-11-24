-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:58.180814+00:00
-- url     : https://prove2.me/theorems/462ecf3d-b27c-4ac0-8208-b16df5ce3386
-- title:
--   Lattice Point Log Count
-- statement:
--   Definitions and structural lemmas for Lattice Point Log Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/LatticePointLogCount.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial NumberField MeasureTheory
section Lattice
variable {r : ℕ}
def chiHat (nm : (Fin r → ℝ) → ℝ) : ℝ :=
  Real.log (volume {t | nm t ≤ 1}).toReal
def latticePointLogCount (nm : (Fin r → ℝ) → ℝ) : ℝ :=
  Real.log (Nat.card {k : Fin r → ℤ // nm (fun i => (k i : ℝ)) ≤ 1})
def IsSubexpDominated {r : ℕ → ℕ} (nm nm' : ∀ d, (Fin (r d) → ℝ) → ℝ) : Prop :=
  ∀ ε > 0, ∃ C : ℝ, ∀ d t, nm d t ≤ C * Real.exp (ε * d) * nm' d t
end Lattice
section Sections
variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] {r : ℕ}
def combPoly (b : Fin r → MvPolynomial ι K) (w : InfinitePlace K) (t : Fin r → ℝ) :
    MvPolynomial ι ℂ :=
  ∑ i, C (t i : ℂ) * map w.embedding (b i)
def arSupNorm (m : InfinitePlace K → ConeMetric ℂ ι) (I : Ideal (MvPolynomial ι K)) (d : ℕ)
    (b : Fin r → MvPolynomial ι K) (t : Fin r → ℝ) : ℝ :=
  ⨆ w : InfinitePlace K,
    supNorm (m w) (RingHom.id ℂ) (I.map (map w.embedding)) d (combPoly b w t)
def archimedeanL2Norm (m : InfinitePlace K → ConeMetric ℂ ι) (μ : InfinitePlace K → Measure (ι → ℂ))
    (d : ℕ) (b : Fin r → MvPolynomial ι K) (t : Fin r → ℝ) : ℝ :=
  Real.sqrt (∑ w : InfinitePlace K,
    (w.mult : ℝ) * l2Norm (m w) (RingHom.id ℂ) (μ w) d (combPoly b w t) ^ 2)
def BernsteinMarkov {r : ℕ → ℕ} (m : InfinitePlace K → ConeMetric ℂ ι)
    (I : Ideal (MvPolynomial ι K)) (μ : InfinitePlace K → Measure (ι → ℂ))
    (b : ∀ d, Fin (r d) → MvPolynomial ι K) : Prop :=
  IsSubexpDominated (fun d => arSupNorm m I d (b d)) (fun d => archimedeanL2Norm m μ d (b d))
end Sections
section ChowForm
variable {o : Type*} [CommRing o] {e n : ℕ}
def IsChowForm (σ : o →+* ℂ) (I : Ideal (MvPolynomial (Fin n) o)) (e δ : ℕ)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) : Prop :=
  IsMultihomog f δ ∧ Squarefree f ∧
    ∀ u : Fin (e + 1) → Fin n → ℂ,
      eval (fun p => u p.1 p.2) f = 0 ↔ ∃ z ∈ conePts σ I, ∀ j, ∑ i, u j i * z i = 0
end ChowForm
end ReciprocityTheory.ChartRestriction.G.Geo


