-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
-- name    : Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:32:18.634144+00:00
-- url     : https://prove2.me/theorems/c6079fbf-7ce9-4902-aeda-9155fadad334
-- title:
--   SCharts
-- statement:
--   Definitions and structural lemmas for SCharts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/RegularCharts/SCharts.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Reg
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
def ChV {A V : Type} [CommRing A] [IsDomain A] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (φ : A →+* V) (e : ℕ) (q : FractionRing A) (r : EReal) : Prop :=
  ∃ x s : A, φ s ≠ 0 ∧ q * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) x ∧
    r = nval V e (algebraMap V (FractionRing V) (φ x)) - nval V e (algebraMap V (FractionRing V) (φ s))
structure SCharts (la : HeightOneSpectrum (𝓞 c.F)) where
  O : Type
  [cr : CommRing O]
  [dom : IsDomain O]
  [dvr : IsDiscreteValuationRing O]
  [cpl : IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [ch0 : CharZero O]
  ioO : c.F →+* FractionRing O
  eO : ℕ
  overO : OverLa la O ioO eO
  J : Type
  [fin : Finite J]
  A : J → Type
  [acr : ∀ j, CommRing (A j)]
  [adom : ∀ j, IsDomain (A j)]
  [alg : ∀ j, Algebra O (A j)]
  [ft : ∀ j, Algebra.FiniteType O (A j)]
  [flat : ∀ j, Module.Flat O (A j)]
  [ic : ∀ j, IsIntegrallyClosed (A j)]
  ch : ∀ j, Rul Xo c → FractionRing (A j)
  Eb : ∀ j, Ideal (A j)
  Eb_ne : ∀ j, Eb j ≠ ⊥

  reg : ∀ j (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ e ∈ Eb j, ∀ ϖ : O,
    Irreducible ϖ → ∃ (x : A j) (t : ℕ), ch j f * algebraMap (A j) _ ((algebraMap O (A j) ϖ * e) ^ t) =
      algebraMap (A j) _ x

  pts : ∀ j (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V] [Module.Finite O V]
    (φ : A j →ₐ[O] V), (∃ e ∈ Eb j, φ e ≠ 0) → ∃ (ioV : c.F →+* FractionRing V) (e : ℕ), OverLa la V ioV e ∧
      (∀ ϖ : O, Irreducible ϖ → vV (K' := FractionRing V) V (algebraMap V (FractionRing V) (algebraMap O V ϖ)) * (eO : ℤ) = e) ∧
      ∃ v ∈ valSet Xo c (algCls Xo c) la, ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n,
        ChV φ.toRingHom e (ch j f) (v f)

  cover : ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, ∃ (j : J) (V : Type) (_ : CommRing V) (_ : IsDomain V)
    (_ : IsDiscreteValuationRing V) (_ : Algebra O V) (φ : A j →ₐ[O] V) (ioV : c.F →+* FractionRing V) (e : ℕ),
      OverLa la V ioV e ∧ (∃ x ∈ Eb j, φ x ≠ 0) ∧
      (∀ ϖ : O, Irreducible ϖ → vV (K' := FractionRing V) V (algebraMap V (FractionRing V) (algebraMap O V ϖ)) * (eO : ℤ) = e) ∧
      Ideal.map (algebraMap O (A j)) (IsLocalRing.maximalIdeal O) ≤ (IsLocalRing.maximalIdeal V).comap φ.toRingHom ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ChV φ.toRingHom e (ch j f) (v f)
attribute [instance] SCharts.cr SCharts.dom SCharts.dvr SCharts.cpl SCharts.ch0 SCharts.fin SCharts.acr SCharts.adom
  SCharts.alg SCharts.ft SCharts.flat SCharts.ic
variable {Xo c}
def SCharts.FamW {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {m : ℕ} (ws : Fin m → Rul Xo c) : Prop :=
  ∃ kj : S.J → Fin m, ∀ j, S.ch j (ws (kj j)) ≠ 0 ∧
    (∀ k, ∃ x : S.A j, S.ch j (ws k) = algebraMap (S.A j) _ x * S.ch j (ws (kj j))) ∧
    (∀ e ∈ S.Eb j, ∀ ϖ : S.O, Irreducible ϖ → ∃ (x : S.A j) (t : ℕ),
      (S.ch j (ws (kj j)))⁻¹ * algebraMap (S.A j) _ ((algebraMap S.O (S.A j) ϖ * e) ^ t) =
        algebraMap (S.A j) _ x)
def SCharts.CovQ {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) : Prop :=
  ∀ q ∈ trivSet Xo c, ∃ (j : S.J) (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
    (_ : Algebra S.O V) (φ : S.A j →ₐ[S.O] V),
      (∀ ϖ : S.O, Irreducible ϖ → Ideal.span {algebraMap S.O (S.A j) ϖ} ⊔
        (IsLocalRing.maximalIdeal V).comap φ.toRingHom ≠ ⊤) ∧
      (∀ ϖ : S.O, Irreducible ϖ → IsUnit (algebraMap S.O V ϖ)) ∧
      (∃ x ∈ S.Eb j, φ x ≠ 0) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ChV φ.toRingHom 1 (S.ch j f) (q f)
end GlobalTheory.Reg


