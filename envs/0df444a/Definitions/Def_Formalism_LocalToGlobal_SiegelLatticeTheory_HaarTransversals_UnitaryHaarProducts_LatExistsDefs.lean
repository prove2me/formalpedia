-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:58:26.735696+00:00
-- url     : https://prove2.me/theorems/6db76ccc-833c-4e5a-8537-f1dc535ffd5e
-- title:
--   Lat Exists Defs
-- statement:
--   Definitions and structural lemmas for Lat Exists Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
namespace Formalism.L2.SG.Pf.LatEx
def latSpanV {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] {r : ℕ} (c : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → V) :
    Submodule (𝓞 E) V :=
  Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ c a ∧ y = x • v a}
def SatBasisV : Prop :=
  ∀ (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (Λ : Submodule (𝓞 E) V), Submodule.IsLattice E Λ →
    ∀ (n : ℕ) (w : Fin (n + 1) → V), LinearIndependent E w →
    ∀ a : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 E)) E, (∀ i, a i ≠ 0) →
    ∃ (e : Fin (n + 1) → V) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      LinearIndependent E e ∧ Submodule.span E (Set.range e) = Submodule.span E (Set.range w) ∧ c ≠ 0 ∧
      Λ ⊓ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E) =
        latSpanV (Fin.snoc (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 E)) E) a c) e
def SplitDiff : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (p : ℕ) (P : Ideal (𝓞 E)),
    p.Prime → P.IsMaximal → ((p : ℕ) : 𝓞 E) ∈ P → ((p : ℕ) : 𝓞 E) ∉ P ^ 2 →
      ¬ (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) ≤ P)
end Formalism.L2.SG.Pf.LatEx


