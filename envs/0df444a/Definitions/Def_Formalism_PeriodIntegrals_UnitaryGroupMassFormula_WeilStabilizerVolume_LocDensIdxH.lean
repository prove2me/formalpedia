-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxH
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:33.642451+00:00
-- url     : https://prove2.me/theorems/e3614263-bea2-4441-aa8f-917a01ed6bd5
-- title:
--   Loc Dens Idx H
-- statement:
--   Definitions and structural lemmas for Loc Dens Idx H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensIdxH.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHI
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing
namespace IdxHW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
def crdS (S : HermR (Fv F v) σ a) (i j : Fin a) (k : Fin d) : Fv F v :=
  (Algebra.TensorProduct.basis (Fv F v) b).repr ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k
theorem mem_hermO_iff (S : HermR (Fv F v) σ a) :
    S ∈ hermO b v σ a ↔ ∀ i j k, crdS b v σ a S i j k ∈ v.adicCompletionIntegers F := Iff.rfl
theorem crdS_add (S T : HermR (Fv F v) σ a) (i j : Fin a) (k : Fin d) :
    crdS b v σ a (S + T) i j k = crdS b v σ a S i j k + crdS b v σ a T i j k := by
  simp [crdS, Matrix.add_apply, map_add]
def redH : (hermO b v σ a) →+
    (Fin a → Fin a → Fin d → ResidueField (v.adicCompletionIntegers F)) where
  toFun S i j k := residue _ ⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩
  map_zero' := by
    funext i j k
    have : crdS b v σ a (0 : HermR (Fv F v) σ a) i j k = 0 := by simp [crdS]
    simp only [ZeroMemClass.coe_zero, this, Pi.zero_apply]
    rw [show (⟨0, _⟩ : v.adicCompletionIntegers F) = 0 from rfl, map_zero]
  map_add' S T := by
    funext i j k
    simp only [Pi.add_apply, ← map_add]
    congr 1
    ext
    simp [crdS_add]
end IdxHW
def IdxCount : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → SWc1W F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in cofinite,
      Nat.card (IdxHW.redH b v σ a).range = Nat.card (𝓞 F ⧸ v.asIdeal) ^ (a ^ 2)
end PI.VolStabW


