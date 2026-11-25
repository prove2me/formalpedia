-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PlugUP
-- name    : Formalism_LocalToGlobal_CharacterGerms_PlugUP
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:23.119801+00:00
-- url     : https://prove2.me/theorems/c357682e-3ac8-42bf-8cbd-b6ae25db4373
-- title:
--   Plug UP
-- statement:
--   Definitions and structural lemmas for Plug UP, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PlugUP.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_DualLattices_U10
import Definitions.Def_ReciprocityTheory_DualLattices_KilledGen
import Definitions.Def_ReciprocityTheory_DualLattices_IdemGen
import Definitions.Def_ReciprocityTheory_DualLattices_LenEx
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
namespace ValuationFitting
open ReciprocityTheory.PGsh.Up CharacteristicFromRanks
variable {C : Type} [Field C]
instance factL (V : VF C) : Fact V.l.Prime := ⟨V.l_prime⟩
def ValTie (V : VF C) (vm : Valuation C NNReal) : Prop :=
  ∀ x : C, x ≠ 0 → ∃ t : ℝ, V.v x = (t : WithTop ℝ) ∧ (vm x : ℝ) = (vm (V.l : C) : ℝ) ^ t
structure Comparison₂ {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    (G : ∀ g, Cart V d (I g) (J g)) (big : Fin 2 → ZMod d → Prop) (rh : ℕ) (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[V.l] R]
    (O : Type) [CommRing O] [Algebra ℤ_[V.l] O] (σ : O ≃ₐ[ℤ_[V.l]] O) (cp : R) (gB : ℕ)
    (H : HodgeTateDatum V.l gB vm R O σ cp) (U : UnramData V.l gB vm R O σ cp H) where
  val : ValTie V vm
  ix : Fin 2 → ZMod d → Fin U.m
  ix_frob : ∀ g a, U.φ (ix g a) = ix g (a + 1)
  ix_conj : ∀ g a, U.cj (ix g a) = ix (1 - g) a
  rank : ∀ g a, U.r (ix g a) + rh = pT G g a
  e : ∀ g a, Fin (pT G g a) ≃ {x : I g // (G g).ty (Sum.inl x) = a}
  αR : ∀ g a, Matrix (Fin (pT G g a)) (Fin (h g)) R
  αR_eq : ∀ g a c i, algebraMap R C (αR g a c i) = ht g i (e g a c)
  bad : ∀ g a, big g a → Nonempty (cokE H.Ht U.εT U.εL (ix g a) (U.cj (ix g a)) ≃ₗ[R]
    ((Fin (pT G g a) → R) ⧸ LinearMap.range (αR g a).mulVecLin))
def FittGe : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (m h : ℕ) (α : Matrix (Fin m) (Fin h) R) (x : NNReal),
    HasLen v R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x →
    ∃ y ∈ S4.fitt0 α, v (algebraMap R C y) = x
section Val
variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
def vA (V : VF C) (R : Type) [CommRing R] [Algebra R C] : AddValuation R (WithTop ℝ) :=
  V.v.comap (algebraMap R C)
end Val
section Val2
variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
end Val2
end ValuationFitting
end Formalism.L2.FormalSeriesBounds


