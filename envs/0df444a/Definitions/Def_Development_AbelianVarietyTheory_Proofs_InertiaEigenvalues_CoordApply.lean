-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CoordApply
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CoordApply
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:03:23.958111+00:00
-- url     : https://prove2.me/theorems/03b71fef-64ff-5401-8d18-4b5c9526fdff
-- title:
--   Coord Apply
-- statement:
--   Definitions and structural lemmas for Coord Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoordApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions GlobalTheory.NB
namespace GlobalTheory.WachTie
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}
def piNorm : O⟦X⟧ := ∏ δ ∈ W.DelF, W.γ₀ δ X
def FrTie (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) : Prop :=
  Function.Injective j ∧
  (∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a) ∧
  (∀ a, j (R.φ a) = W.φ₀ (j a)) ∧
  (∀ a, j (R.γ a) = W.γ₀ W.gam (j a)) ∧
  R.χ = W.χΓ W.gam ∧
  R.s = W.DelF.card ∧
  Associated (j X) (X ^ R.s) ∧
  Associated (j R.E) W.q₀
def EETie (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) : Prop :=
  (∀ a : ZMod n → O⟦X⟧, jE (fun i => R.ι (a i)) = algebraMap (LetA O n) W.EE (fun i => j (a i))) ∧
  Function.Injective jE ∧
  (∀ y, (∃ x, jE x = y) ↔ ∀ δ ∈ W.DelF, W.γE δ y = y) ∧
  (∀ x, jE (fun i => R.φE (x (i - 1))) = W.φE (jE x)) ∧
  (∀ x, jE (fun i => R.γE (x i)) = W.γE W.gam (jE x))
def coord (R : Fr l O) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ}
    (b : Fin r → W.DD T) : DD R n r →ₗ[O] W.DD T where
  toFun x := ∑ k, jE (fun i => x i k) • b k
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul, ← map_add]; rfl
  map_smul' c x := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_assoc, ← map_smul]; rfl
def DDinv (T : LocLat G Qp LL O) : Submodule O (W.DD T) where
  carrier := {x | ∀ δ ∈ W.DelF, W.γD T δ x = x}
  zero_mem' := fun δ _ => map_zero _
  add_mem' := fun ha hb δ hδ => by rw [map_add, ha δ hδ, hb δ hδ]
  smul_mem' := fun c a ha δ hδ => by rw [map_smul, ha δ hδ]
def wachDeltaInvariantCoboundaries (T : LocLat G Qp LL O) : Submodule O (W.DD T × W.DD T) :=
  (DDinv W T).map ((W.φD T - LinearMap.id).prod (W.γD T W.gamK - LinearMap.id))
def SysTie (R : Fr l O) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (S : Sys R n r) : Prop :=
  let Θ := coord W R jE T (fun k => (b k : W.DD T))
  (∀ k, (b k : W.DD T) ∈ W.NΔ T) ∧
  Function.Injective Θ ∧
  LinearMap.range Θ = DDinv W T ∧
  (∀ x, Θ x ∈ W.NΔ T ↔ ∀ i, x i ∈ R.N0 r) ∧
  (∀ x, Θ (S.φD x) = W.φD T (Θ x)) ∧
  (∀ x, Θ (S.γD x) = W.γD T W.gam (Θ x)) ∧
  S.Z1.map (Θ.prodMap Θ) = W.wachCocyclesDelta T ∧
  S.B1.map (Θ.prodMap Θ) = wachDeltaInvariantCoboundaries W T
end GlobalTheory.WachTie


