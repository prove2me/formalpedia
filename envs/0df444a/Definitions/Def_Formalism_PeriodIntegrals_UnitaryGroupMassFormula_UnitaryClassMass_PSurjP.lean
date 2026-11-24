-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjP
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjP
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:08:56.388306+00:00
-- url     : https://prove2.me/theorems/027b5ba4-7951-40ed-b8e3-ce5f9954e3df
-- title:
--   PSurj P
-- statement:
--   Definitions and structural lemmas for PSurj P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjP.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
def IdemStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E), (∀ a, σ a = star a) →
    ∀ W : Finset (Ideal (𝓞 E)), (∀ p ∈ W, p.IsMaximal) →
      (∀ p ∈ W, ∀ q ∈ W, hcompl (K := E) p = hcompl (K := E) q → p = q) →
    ∃ e : Option W → AF F ⊗[F] E,
      (∀ i, e i * e i = e i) ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ (∑ i, e i = 1) ∧
      (∀ i, sigR (AF F) σ (e i) = e i) ∧
      (∀ i, finE F E (e i) ∈ PI.UnitaryGroupMassFormula.UJClassFin.Oh F E) ∧
      ∀ (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
        [FiniteDimensional E V] (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
        Submodule.IsLattice E L0 → ∀ v : V,
        (∀ p : W, finE F E (e (some p)) • PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (b.equivFun v) ∈
            latHat F E (crdOf b L0) ↔ v ∈ loc (K := E) (p : Ideal (𝓞 E)) L0) ∧
        (finE F E (e none) • PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (b.equivFun v) ∈ latHat F E (crdOf b L0) ↔
            ∀ q : Ideal (𝓞 E), q.IsMaximal → (∀ p ∈ W, hcompl (K := E) q ≠ hcompl (K := E) p) →
              v ∈ loc (K := E) q L0)
end PI.UnitaryGroupMassFormula.UJClassMass
end


