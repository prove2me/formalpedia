-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
-- name    : Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:28.589056+00:00
-- url     : https://prove2.me/theorems/1ac58327-d266-4b9c-963f-9c4cdd4f2d88
-- title:
--   Quot Realize
-- statement:
--   Definitions and structural lemmas for Quot Realize, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
namespace Formalism.HN
namespace QuotientRealization
section Covol
variable {E F M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [AddCommGroup M]
theorem eq_of_norm_eq (f : M →+ E) (g : M →+ F) (hn : ∀ m, ‖f m‖ = ‖g m‖) {m m' : M}
    (h : f m = f m') : g m = g m' := by
  have h0 : ‖g (m - m')‖ = 0 := by rw [← hn, map_sub, h, sub_self, norm_zero]
  rw [norm_eq_zero, map_sub, sub_eq_zero] at h0
  exact h0
def transport (f : M →+ E) (g : M →+ F) (L1 : Submodule ℤ E) (L2 : Submodule ℤ F)
    (h1 : ∀ y, y ∈ L1 ↔ ∃ m, f m = y) (h2 : ∀ y, y ∈ L2 ↔ ∃ m, g m = y)
    (hn : ∀ m, ‖f m‖ = ‖g m‖) : L1 →+ L2 where
  toFun y := ⟨g ((h1 y).1 y.2).choose, (h2 _).2 ⟨_, rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    have hs := ((h1 _).1 (0 : L1).2).choose_spec
    show g _ = 0
    rw [← map_zero g]
    exact eq_of_norm_eq f g hn (by rw [hs, map_zero]; rfl)
  map_add' y z := by
    apply Subtype.ext
    have hs := ((h1 _).1 (y + z).2).choose_spec
    have hy := ((h1 _).1 y.2).choose_spec
    have hz := ((h1 _).1 z.2).choose_spec
    show g _ = g _ + g _
    rw [← map_add]
    exact eq_of_norm_eq f g hn (by rw [hs, map_add, hy, hz]; rfl)
end Covol
section Psi
variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι]
end Psi
section Main
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
def pv (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (U : Submodule K V)
    (v : InfinitePlace K) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  Submodule.span ℂ ((fun y => (WithLp.equiv 2 (ι → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X v y)) '' (U : Set V))
section Lift
variable (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (U : Submodule K V)
  {κ : Type} [Fintype κ] [DecidableEq κ] (b'' : Basis κ K (V ⧸ U)) (c : κ → V)
def tv (v : InfinitePlace K) : (κ → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι :=
  Fintype.linearCombination ℂ
    (fun k => (pv b X U v)ᗮ.starProjection (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (c k))))
end Lift
end Main
end QuotientRealization
end Formalism.HN


