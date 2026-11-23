-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LegendreSumSt
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_LegendreSumSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:56.770203+00:00
-- url     : https://prove2.me/theorems/b6f196e6-fc99-4789-bf1b-ee7ff9062d8c
-- title:
--   Legendre Sum St
-- statement:
--   Definitions and structural lemmas for Legendre Sum St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LegendreSumSt.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Formalism_PeriodIntegrals_DepthLegendre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPolynomial Formalism.L2.Pj
section Crude
variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ)
def crudeP (col : ∀ σ, Fin (r σ) → Fin n) (a : T → ℕ → ℕ) : MvPolynomial (Letter T r n) ℤ :=
  ∏ σ, ∏ s : Fin (r σ),
    Matrix.det ((letMat r n ℤ σ).submatrix (Fin.castLE s.isLt) (fun t : Fin (s + 1) => col σ (Fin.castLE s.isLt t))) ^
      (a σ s - a σ (s + 1))
def diagMono (col : ∀ σ, Fin (r σ) → Fin n) (a : T → ℕ → ℕ) : Letter T r n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ℓ => if ℓ.2.2 = col ℓ.1 ℓ.2.1 then a ℓ.1 ℓ.2.1 else 0
end Crude
def CrudeAlgSt : Prop :=
  ∀ (T : Type) [Fintype T] (r : T → ℕ) (n : ℕ) (cc : T → T) (isX : T → Prop)
    (col : ∀ σ, Fin (r σ) → Fin n) (a : T → ℕ → ℕ),
    (∀ σ, Function.Injective (col σ)) →
    (∀ σ τ (i : Fin (r σ)) (j : Fin (r τ)), isX σ → ¬ isX τ → col σ i ≠ col τ j) →
    (∀ τ, isX τ → ¬ isX (cc τ)) →
    (∀ σ i, a σ (i + 1) ≤ a σ i) → (∀ σ i, r σ ≤ i → a σ i = 0) →
    (∀ (k : Type) [Field k],
      MvPolynomial.map (Int.castRingHom k) (crudeP r n col a) ∈ HHa r n k cc isX a) ∧
    (crudeP r n col a).coeff (diagMono r n col a) = 1
def LegendreSumSt : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (ι : Type) [Fintype ι] (a : ι → ℕ),
    (p - 1) * ∑ i, padicValNat p (a i).factorial ≤ ∑ i, a i ∧
    ((∀ i, a i < p) → ∑ i, padicValNat p (a i).factorial = 0)
section Germ
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
def addF (k : Type) [CommRing k] (d : ℕ) : Fin d → PS k 2 d :=
  fun j => MvPowerSeries.X ((0 : Fin 2), j) + MvPowerSeries.X ((1 : Fin 2), j)
def PairingSt : Prop :=
  ∀ (k : Type) [CommRing k] (d : ℕ) (ι : Type) [Fintype ι] (j : ι → Fin d), Function.Injective j →
    ∀ (P : MvPolynomial ι k) (α : ι →₀ ℕ),
      constantCoeff (DpolyOf (addF k d) (fun l => Pi.single (j l) 1) P
          (∏ l, (MvPowerSeries.X ((0 : Fin 1), j l) : PS k 1 d) ^ α l)) =
        P.coeff α * ∏ l, ((α l).factorial : k)
def SymbolSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d),
    ev (n := 1) ![0, pt k (n := 1) d 0] h = 0 →
    ∀ (w0 : O) (mm : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin d → k) (P : MvPolynomial ι k) (N : ℕ),
      (∀ m ∈ P.support, m.degree = N) →
      ∀ f : PS k 1 d, (∀ e : Fin 1 × Fin d →₀ ℕ, e.degree < N → coeff e f = 0) →
        B.nabVal k h w0 mm f u P = constantCoeff (DpolyOf (addF k d) u P f)
end Germ
end Formalism.MainNotions.ModuliIntegralCharts.H1


