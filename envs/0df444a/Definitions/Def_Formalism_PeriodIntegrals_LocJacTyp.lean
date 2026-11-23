-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
-- name    : Formalism_PeriodIntegrals_LocJacTyp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:10:44.491795+00:00
-- url     : https://prove2.me/theorems/c5dbdd58-b9c1-4905-a5f8-ccb289cd6307
-- title:
--   Loc Jac Typ
-- statement:
--   Definitions and structural lemmas for Loc Jac Typ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LocJacTyp.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical
section Meas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))
def sdE (ι : Type) [Fintype ι] : Measure (ι → Fv F v ⊗[F] E) :=
  if h : ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ
      (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)))
  then h.choose else 0
end Meas
section Frames
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
def OEv : Set (Fv F v ⊗[F] E) :=
  SetLike.coe (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ))
def sc (x : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ[F] (1 : E)
def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d
def dV : Fv F v := if h : ∃ d, IsDiffVal v d then h.choose else 1
def alp (r : ℕ) (a : Fin (r + 1)) : Fv F v := if (a : ℕ) < r then (dV v)⁻¹ ^ (r - (a : ℕ)) else 1
def locZ {r : ℕ} (z : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) (i j : Fin (r + 1)) : Fv F v ⊗[F] E :=
  sc (E := E) v (alp v r i * alp v r j) * z (i, j)
end Frames
section Sets
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))
def ZZOrd (r : ℕ) : Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  {z | ∀ i j, locZ v z i j ∈ OEv (E := E) v}
def ZZTyp (g r : ℕ) (TF TF' : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :
    Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  {z | ∀ i j, (locZ v z i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v ∧
    ((locZ v z i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ +
        sigR (Fv F v) σ ((locZ v z j i - TF j i) * sc (E := E) v (g : Fv F v)⁻¹) -
        (TF' i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}
def PPOrd (r : ℕ) (l : Fin (r + 1)) : Set (Fv F v ⊗[F] E) :=
  {c | sc (E := E) v (alp v r l ^ 2) * c ∈ OEv (E := E) v}
def PPTyp (g r T T' : ℕ) (l : Fin (r + 1)) : Set (Fv F v ⊗[F] E) :=
  if (l : ℕ) < r then
    {c | sc (E := E) v (alp v r l ^ 2 * (g : Fv F v)⁻¹) * c ∈ OEv (E := E) v ∧
      sc (E := E) v (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) * (c + sigR (Fv F v) σ c) ∈ OEv (E := E) v}
  else
    {c | sc (E := E) v (g : Fv F v)⁻¹ * (c + (T : Fv F v ⊗[F] E)) ∈ OEv (E := E) v ∧
      sc (E := E) v (((g : Fv F v)⁻¹) ^ 2) * (c + sigR (Fv F v) σ c + (T : Fv F v ⊗[F] E) + (T' : Fv F v ⊗[F] E))
        ∈ OEv (E := E) v}
abbrev UIdx (r : ℕ) : Type := {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}
def UO (r : ℕ) : Set (UIdx r → Fv F v ⊗[F] E) :=
  {x | ∀ p, sc (E := E) v ((alp v r p.1.1)⁻¹ * alp v r p.1.2) * x p ∈ OEv (E := E) v}
def localVolumeOrdinary (r : ℕ) : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E)) :=
  UO v r ×ˢ UO v r
def deepCongruenceVolume (g r : ℕ) : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E)) :=
  {p | p.1 ∈ UO v r ∧ p.2 ∈ UO v r ∧ ∀ q,
    sc (E := E) v ((alp v r q.1.1)⁻¹ * alp v r q.1.2 * (g : Fv F v)⁻¹) * (p.1 q - p.2 q) ∈ OEv (E := E) v}
def volS {r : ℕ} (S : Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E)) : ℝ :=
  (sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) S).toReal
def volC (S : Set (Fv F v ⊗[F] E)) : ℝ :=
  (sdE (E := E) ψ v Unit ((fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' S)).toReal
def volU {r : ℕ} (S : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E))) : ℝ :=
  (((sdE (E := E) ψ v (UIdx r)).prod (sdE (E := E) ψ v (UIdx r))) S).toReal
def absV (x : Fv F v) : ℝ :=
  if h : Valued.v x = 0 then 0
  else ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (Multiplicative.toAdd (WithZero.unzero h))
def jacS (typed : Prop) (g r : ℕ) : ℝ :=
  ∏ l : Fin r, ((absV v ((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), alp v r i ^ 2) *
    (if typed then ((g : Fv F v)⁻¹) ^ ((l : ℕ) + 1) else 1))) ^ 2) ^ 2
end Sets
section Stmt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
def LocJacTyp : Prop :=
  ∀ (typed : Prop) (g r T T' : ℕ) (TF TF' : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)),
    Module.finrank F E = 2 → σ ≠ AlgHom.id F E → typed → 0 < g →
    (∃ x : Fv F v ⊗[F] E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1) →
    TF ∈ HermR (Fv F v) σ (r + 1) → TF' ∈ HermR (Fv F v) σ (r + 1) →
    (∀ i j, (TF' i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v) →
    (g : ℤ) ∣ ((T : ℤ) - T') →
    volS (E := E) ψ v (ZZTyp σ v g r TF TF') * jacS v typed g r =
      volU (E := E) ψ v (deepCongruenceVolume v g r) * ∏ l : Fin (r + 1), volC (E := E) ψ v (PPTyp σ v g r T T' l)
end Stmt
end PI.LocJacTyp


