-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:21.871808+00:00
-- url     : https://prove2.me/theorems/3370a54d-8232-4b04-96de-24cc0a024c50
-- title:
--   Fibre St A
-- statement:
--   Definitions and structural lemmas for Fibre St A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
def deh {ι S : Type*} [Field S] (v : ι → S) (i₀ : ι) : MvPolynomial ι ℤ →+* S :=
  eval₂Hom (Int.castRingHom S) fun i => v i / v i₀
def homog {ι : Type*} [DecidableEq ι] (i₀ : ι) (N : ℕ) (G : MvPolynomial ι ℤ) :
    MvPolynomial ι ℤ :=
  ∑ m ∈ G.support, monomial (m + Finsupp.single i₀ (N - m.degree)) (G.coeff m)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ}
structure Gen (x : ι → Ω) (e : Fin (D + 1) → ι) where
  Θ : MvPolynomial ι ℤ
  P : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  monic : P.Monic
  root : P.eval₂ (deh (x ∘ e) 0) (deh x (e 0) Θ) = 0
  min : ∀ H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ), H.natDegree < P.natDegree →
    H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) Θ) = 0 → ∀ j, deh (x ∘ e) 0 (H.coeff j) = 0
  dd : MvPolynomial (Fin (D + 1)) ℤ
  dd_ne : deh (x ∘ e) 0 dd ≠ 0
  Q : ι → Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  hQ : ∀ i, deh (x ∘ e) 0 dd * deh x (e 0) (X i) = (Q i).eval₂ (deh (x ∘ e) 0) (deh x (e 0) Θ)
  cc : MvPolynomial (Fin (D + 1)) ℤ
  cc_ne : deh (x ∘ e) 0 cc ≠ 0
  U : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  V : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  hUV : (U * P + V * Polynomial.derivative P - Polynomial.C cc).map (deh (x ∘ e) 0) = 0
variable {x : ι → Ω} {e : Fin (D + 1) → ι}
def Gen.HG [DecidableEq ι] (G : Gen x e) (F : MvPolynomial ι ℤ) :
    Polynomial (MvPolynomial (Fin (D + 1)) ℤ) :=
  MvPolynomial.eval₂ (Int.castRingHom _) (fun o : Option ι => o.elim (Polynomial.C G.dd) G.Q)
    (homog none F.totalDegree (rename some F))
def Gen.evQ (G : Gen x e) {S : Type*} [Field S] (ψ : MvPolynomial (Fin (D + 1)) ℤ →+* S) (t : S) :
    ι → S :=
  fun i => (G.Q i).eval₂ ψ t / ψ G.dd
def Gen.zOf (G : Gen x e) (w : Fin (D + 1) → ℂ) (ρ : ℂ) : ι → ℂ :=
  fun i => w 0 * G.evQ (deh w 0) ρ i
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib


