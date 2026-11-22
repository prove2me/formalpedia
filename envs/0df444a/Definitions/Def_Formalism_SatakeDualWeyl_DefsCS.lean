-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
-- name    : Formalism_SatakeDualWeyl_DefsCS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:37.068814+00:00
-- url     : https://prove2.me/theorems/7e41e443-e8eb-45b3-b5bc-27d0d1ce1973
-- title:
--   Defs CS
-- statement:
--   Definitions and structural lemmas for Defs CS, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/DefsCS.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_StatementB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Theorems.Thm_Formalism_UG_P_levelaf_tmul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.UG.CS
open Formalism.UG
def starOfInv {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ e, σ (σ e) = e) : StarRing E where
  star := σ
  star_involutive := hσ
  star_mul a b := by simp only [map_mul, mul_comm]
  star_add a b := map_add σ a b
def formJ {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ e, σ (σ e) = e) {n : Type} [Fintype n]
    [DecidableEq n] (J : Matrix n n E) (c : E) :
    letI := starOfInv σ hσ; (n → E) →ₗ⋆[E] (n → E) →ₗ[E] E :=
  letI := starOfInv σ hσ
  Matrix.toLinearMapₛₗ₂' E (starRingEnd E) (RingHom.id E) (c • J)
section Glob
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
theorem incl_int (b : 𝓞 E) : ιA (algebraMap (𝓞 E) E b) ∈ 𝒮 := by
  have := Formalism.UG.P.levelaf_tmul_mem (F := F) (E := E) b (one_mem (intAd F))
  exact this
def globLat (g : GL n 𝒜) (Λ : Submodule (𝓞 E) (n → E)) : Submodule (𝓞 E) (n → E) where
  carrier := {x | ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈
    latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Pi.add_apply, map_add] at *
    rw [show (fun i => ιA (x i) + ιA (y i)) = (fun i => ιA (x i)) + (fun i => ιA (y i)) from rfl,
      mulVec_add]
    exact add_mem hx hy
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
    rw [show (fun _ : n => (0 : 𝒜)) = 0 from rfl, mulVec_zero]
    exact zero_mem _
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq, Pi.smul_apply] at *
    have : (fun i => ιA (a • x i)) = (ιA (algebraMap (𝓞 E) E a)) • (fun i => ιA (x i)) := by
      ext i; simp [Algebra.smul_def]
    rw [this, mulVec_smul]
    exact Submodule.smul_mem _ (⟨_, incl_int a⟩ : 𝒮) hx
end Glob
def SigmaInvol : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    ∀ e : E, σ (σ e) = e
def TracePos : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    IsTotDef σ J → ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x : n → E, x ≠ 0 →
      0 < Algebra.trace ℚ E (algebraMap F E (c : F) * hform (σ : E →+* E) J x x)
def FormSymm : Prop :=
  ∀ (E : Type) [Field E] (σ : E →+* E) (hσ : ∀ e, σ (σ e) = e) (n : Type) [Fintype n]
    [DecidableEq n] (J : Matrix n n E) (c : E), σ c = c → IsHerm σ J →
    letI := starOfInv σ hσ
    (formJ σ hσ J c).IsSymm ∧ ∀ x y, formJ σ hσ J c x y = c * hform σ J x y
def IsomUJ : Prop :=
  ∀ (E : Type) [Field E] (σ : E →+* E) (hσ : ∀ e, σ (σ e) = e) (n : Type) [Fintype n]
    [DecidableEq n] (J : Matrix n n E) (c : E), c ≠ 0 → σ c = c → ∀ g : GL n E,
    letI := starOfInv σ hσ
    (g ∈ UJ σ J ↔ glEquiv g ∈ Formalism.HermitianLatticesTheory.isom (formJ σ hσ J c))
def GlobLatLattice : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (Λ : Submodule (𝓞 E) (n → E)),
    Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (n → E)) = ⊤ →
    ∀ g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F), Submodule.IsLattice E (globLat g Λ)
def GlobLatOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (Λ : Submodule (𝓞 E) (n → E)),
    Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (n → E)) = ⊤ →
    globLat (F := F) 1 Λ = Λ
def GlobLatEquiv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (Λ : Submodule (𝓞 E) (n → E))
    (γ : GL n E) (g k : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    k ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ) →
    globLat (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g * k) Λ =
      Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat g Λ)
def IntAdApprox : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (D : 𝓞 F), D ≠ 0 →
    ∀ a ∈ intAd F, ∃ r : 𝓞 F, ∃ y ∈ intAd F,
      a = algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r +
        algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) D * y
def SpanRecover : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (Λ : Submodule (𝓞 E) (n → E)),
    Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (n → E)) = ⊤ →
    ∀ (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (u : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
      u ∈ Submodule.span (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))
          ((fun x : n → E => fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ''
            (globLat g Λ : Set (n → E))) ↔
        ((g⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n _) *ᵥ u ∈
          latS (F := F) (FiniteAdeleRing (𝓞 F) F)
            (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
def ClassInj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (Λ : Submodule (𝓞 E) (n → E)),
    Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (n → E)) = ⊤ →
    ∀ (g g' : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (γ : GL n E), γ ∈ UJ (σ : E →+* E) J →
      globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ =
        Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat (g' : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ) →
      DoubleCoset.mk ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
        ((levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) g =
      DoubleCoset.mk ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
        ((levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) g'
def ScaleBound : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (Λ : Submodule (𝓞 E) (n → E)),
    Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (n → E)) = ⊤ →
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), ∀ x ∈ globLat g Λ,
      ∀ y ∈ globLat g Λ, algebraMap (𝓞 E) E d * hform (σ : E →+* E) J x y ∈ (algebraMap (𝓞 E) E).range
def DualBound : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (Λ : Submodule (𝓞 E) (n → E)), IsUnit J.det →
    Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (n → E)) = ⊤ →
    ∃ e : 𝓞 E, e ≠ 0 ∧ ∀ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), ∀ x : n → E,
      (∀ y ∈ globLat g Λ, hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range) →
      algebraMap (𝓞 E) E e • x ∈ globLat g Λ
def CovolOfDual : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) →
    ∀ e : 𝓞 K, e ≠ 0 → ∃ C : ℝ, ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M →
      (∀ x ∈ Formalism.HermitianLatticesTheory.dual h M, (e : K) • x ∈ M) →
      ∀ [DiscreteTopology (Formalism.HermitianLatticesTheory.zmap ι M)] [IsZLattice ℝ (Formalism.HermitianLatticesTheory.zmap ι M)],
        ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M) ≤ C
def ClassSetFiniteBdd : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ d e : 𝓞 K, d ≠ 0 → e ≠ 0 →
    ∃ s : Finset (Submodule (𝓞 K) V), ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M →
      (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ (1 : Submodule (𝓞 K) K)) →
      (∀ x ∈ Formalism.HermitianLatticesTheory.dual h M, (e : K) • x ∈ M) →
      ∃ N ∈ s, ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g N = M
def StdLatFull : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : Type) [Fintype n] [DecidableEq n],
    Module.Finite (𝓞 E) (stdLat (n := n) (A := E) (𝓞 E)) ∧
    Submodule.span E ((stdLat (n := n) (A := E) (𝓞 E) : Submodule (𝓞 E) (n → E)) : Set (n → E)) = ⊤
def WeakApproxV : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    IsHerm (σ : E →+* E) J → IsUnit J.det → IsTotDef σ J →
    ∀ (Λ : Submodule (𝓞 E) (n → E)), Module.Finite (𝓞 E) Λ →
    Submodule.span E (Λ : Set (n → E)) = ⊤ → ∀ (v : HeightOneSpectrum (𝓞 F)),
    ∀ g ∈ UPts σ J (v.adicCompletion F), ∃ γ ∈ UJ (σ : E →+* E) J,
      (bc (inclE (F := F) (v.adicCompletion F)) γ)⁻¹ * g ∈ levelVL σ J v Λ
end Formalism.UG.CS


