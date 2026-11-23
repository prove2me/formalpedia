-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensAAOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensAAOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:11.084082+00:00
-- url     : https://prove2.me/theorems/00739bb2-ad5f-4b20-b95b-e78707323ed7
-- title:
--   Dens AAOf
-- statement:
--   Definitions and structural lemmas for Dens AAOf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensAAOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Theorems.Thm_PI_VolStabW_sigma_invol

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
def ResAA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → SWc1W F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ ψ, IsCharAF F ψ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    ∀ᶠ v in cofinite,
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∃ (L : AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
      (Λ : ℕ → AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
      (H : ℕ → AddSubgroup (HermR (Fv F v) σ a)),
      (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) = latV b v ∧
      IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∧
      IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∧ Λ 0 ≤ L ∧
      (∀ n, IsOpen (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
      (∀ n, IsCompact (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧ Antitone Λ ∧
      (∀ n, IsOpen (H n : Set (HermR (Fv F v) σ a))) ∧
      (∀ n, IsCompact (H n : Set (HermR (Fv F v) σ a))) ∧
      (∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ n, (H n : Set (HermR (Fv F v) σ a)) ⊆ N') ∧
      (∀ y ∈ L, gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 y - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ H 0 →
        ∃ D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a,
          (∀ n, (Λ n).map D = H n) ∧ ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n,
            gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z + W) - gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z) - D W ∈
              H (n + 1)) ∧
      ∃ (k K : Type) (_ : Field k) (_ : Finite k) (_ : CommRing K) (_ : Algebra k K)
        (σ' : K ≃ₐ[k] K) (J' : Matrix (Fin M) (Fin M) K) (T' : Matrix (Fin a) (Fin a) K),
        IsQuadInv k K σ' ∧ (2 : k) ≠ 0 ∧ (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧
        (∀ i j, σ' (T' j i) = T' i j) ∧ IsUnit T'.det ∧ (Nat.card k : ℝ) = qV v ∧
        ((μv ((L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∩
            gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 ⁻¹' {z | z - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ H 0})) /
            νv (H 0)).toReal =
          (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ℝ) /
            (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2)
end PI.VolStabW


