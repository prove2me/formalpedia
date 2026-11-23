-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:40:23.918186+00:00
-- url     : https://prove2.me/theorems/4af42a72-0bd8-4994-8cbf-a2659f5a6df7
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/Development.lean

import Definitions.Def_Formalism_PeriodIntegrals_UJClassFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
namespace PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def vinc {M : ℕ} (x : Fin M → E) : Fin M → Af F ⊗[F] E := fun i => inclR (Af F) (x i)
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
def abelian₂ (L : Set (Fin M → E)) (h : HA (AF F) σ J) : Set (Fin M → E) :=
  {x | (finMat σ J h⁻¹).mulVec (vinc (F := F) x) ∈ latHat F E L}
theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]
theorem bc_mem (g : GL (Fin M) E) (hg : g ∈ UJ (σ : E →+* E) J) :
    bc (inclR (AF F)) g ∈ HR (AF F) σ J := by
  have hg' : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  have hc : cT (sigR (AF F) σ) ((g : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) =
      (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)).map (inclR (AF F)) := by
    ext i j
    simp [cT, sigR_inclR]
  show cT (sigR (AF F) σ) ((g : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) * J.map (inclR (AF F)) *
    (g : Matrix (Fin M) (Fin M) E).map (inclR (AF F)) = J.map (inclR (AF F))
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg']
def emb : UJ (σ : E →+* E) J →* HA (AF F) σ J where
  toFun g := (⟨bc (inclR (AF F)) g.1, bc_mem σ J g.1 g.2⟩ : HR (AF F) σ J)
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)
def RatDense : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)),
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) →
    ∀ (h : HA (AF F) σ J) (y : Fin M → Af F ⊗[F] E),
      (finMat σ J h⁻¹).mulVec y ∈ latHat F E L ↔ y ∈ latHat F E (abelian₂ σ J L h)
def ClassFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)),
    (∀ a, σ a = star a) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, HasSignature (J.map τ) M 0) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) →
    ∃ S : Set (Set (Fin M → E)), S.Finite ∧ ∀ h : HA (AF F) σ J, ∃ s ∈ S, ∃ g : UJ (σ : E →+* E) J,
      abelian₂ σ J L h = (fun x => ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec x) '' s
end PI.UnitaryGroupMassFormula.UJClassFin


