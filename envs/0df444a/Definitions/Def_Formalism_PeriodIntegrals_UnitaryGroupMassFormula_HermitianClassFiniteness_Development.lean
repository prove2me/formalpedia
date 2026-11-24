-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:35:18.848062+00:00
-- url     : https://prove2.me/theorems/62b8f08b-f21d-4ac5-ae12-4f554458dd6e
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/Development.lean

import Definitions.Def_Formalism_PeriodIntegrals_InHHClassFin
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEasy
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_Final_SigConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain Formalism.UG PI.InHHClassFin
open scoped TensorProduct
namespace PI.UnitaryGroupMassFormula.InHHClassFin
def ClassSetMono : Prop :=
  ∀ (G : Type) [Group G] (Γ K K' : Subgroup G), K ≤ K' →
    Finite (ClassSet Γ K) → Finite (ClassSet Γ K')
def ClassSetFinIdx : Prop :=
  ∀ (G : Type) [Group G] (Γ K K' : Subgroup G), K' ≤ K → K'.relIndex K ≠ 0 →
    Finite (ClassSet Γ K) → Finite (ClassSet Γ K')
def ClassSetMap : Prop :=
  ∀ (G G' : Type) [Group G] [Group G'] (Φ : G ≃* G') (Γ K : Subgroup G),
    Finite (ClassSet (Γ.map Φ.toMonoidHom) (K.map Φ.toMonoidHom)) → Finite (ClassSet Γ K)
def KgNhd : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (x : I.Gf), 1 ≤ g →
    ∃ g' : ℕ, 1 ≤ g' ∧ ∀ h : I.Gf, h ∈ I.Kg g' → x⁻¹ * h * x ∈ I.Kg g
def SigConj : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (τ : I.E →+* ℂ),
    τ.comp (I.cm.sig : I.E →+* I.E) = (starRingEnd ℂ).comp τ
abbrev stdLevel (I : Formalism.MainNotions.S.AutInst) {k : ℕ} (J' : Matrix (Fin k) (Fin k) I.E) :
    Subgroup (UPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F)) :=
  (levelAfL I.cm.sig J' (stdLat (n := Fin k) (A := I.E) (𝓞 I.E))).subgroupOf
    (UPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F))
abbrev congS (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) (g : ℕ) : Subgroup (HfinS I S) :=
  Subgroup.closure {h : HfinS I S | (h : I.Gf) ∈ I.Kg g}
def Restrict (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) : Prop :=
  ∃ (k : ℕ) (J' : Matrix (Fin k) (Fin k) I.E)
    (Φ : HfinS I S ≃* UPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F)),
    IsHerm (I.cm.sig : I.E →+* I.E) J' ∧ IsUnit J'.det ∧ IsTotDef I.cm.sig J' ∧
    (iotaFS I S).range.map Φ.toMonoidHom =
      (ratPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F)).subgroupOf
        (UPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F)) ∧
    ∀ g : ℕ, 1 ≤ g →
      (stdLevel I J' ⊓ (congS I S g).map Φ.toMonoidHom).relIndex (stdLevel I J') ≠ 0
structure Frame (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) where
  m : ℕ
  k : ℕ
  B : Matrix (Fin I.n) (Fin m ⊕ Fin k) I.E
  Bi : Matrix (Fin m ⊕ Fin k) (Fin I.n) I.E
  mul_inv : B * Bi = 1
  inv_mul : Bi * B = 1
  col_span : ∀ j, (fun i => B i (Sum.inl j)) ∈ Submodule.span I.E S
  S_coord : ∀ s ∈ S, ∀ j, (Bi *ᵥ s) (Sum.inr j) = 0
  orth : ∀ s ∈ S, ∀ j, hform (starRingEnd I.E) I.J s (fun i => B i (Sum.inr j)) = 0
def Frame.J' {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)} (fr : Frame I S) :
    Matrix (Fin fr.k) (Fin fr.k) I.E :=
  (cT (starRingEnd I.E) fr.B * I.J * fr.B).toBlocks₂₂
def psiMat {E F : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {n m k : ℕ} (B : Matrix (Fin n) (Fin m ⊕ Fin k) E) (Bi : Matrix (Fin m ⊕ Fin k) (Fin n) E)
    (y : Matrix (Fin k) (Fin k) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R) :=
  (Matrix.map B (inclE (F := F) R) : Matrix (Fin n) (Fin m ⊕ Fin k) (E ⊗[F] R)) *
    Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (E ⊗[F] R)) 0 0 y *
    (Matrix.map Bi (inclE (F := F) R) : Matrix (Fin m ⊕ Fin k) (Fin n) (E ⊗[F] R))
def FrameExists : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)), DefiniteCompl I S → Nonempty (Frame I S)
def FrameIso : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) (fr : Frame I S),
    ∃ Φ : HfinS I S ≃* UPts I.cm.sig fr.J' (FiniteAdeleRing (𝓞 I.F) I.F),
      ∀ y, I.fmat ((Φ.symm y : HfinS I S) : I.Gf) =
        psiMat (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) fr.B fr.Bi
          ((y : GL (Fin fr.k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
            Matrix (Fin fr.k) (Fin fr.k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F))
def FrameGram : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) (fr : Frame I S), DefiniteCompl I S →
    IsHerm (I.cm.sig : I.E →+* I.E) fr.J' ∧ IsUnit fr.J'.det ∧ IsTotDef I.cm.sig fr.J'
def FrameRat : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) (fr : Frame I S)
    (Φ : HfinS I S ≃* UPts I.cm.sig fr.J' (FiniteAdeleRing (𝓞 I.F) I.F)),
    (∀ y, I.fmat ((Φ.symm y : HfinS I S) : I.Gf) =
        psiMat (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) fr.B fr.Bi
          ((y : GL (Fin fr.k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
            Matrix (Fin fr.k) (Fin fr.k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F))) →
    (iotaFS I S).range.map Φ.toMonoidHom =
      (ratPts I.cm.sig fr.J' (FiniteAdeleRing (𝓞 I.F) I.F)).subgroupOf
        (UPts I.cm.sig fr.J' (FiniteAdeleRing (𝓞 I.F) I.F))
def LevelStep : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (m k : ℕ) (B : Matrix (Fin I.n) (Fin m ⊕ Fin k) I.E)
    (Bi : Matrix (Fin m ⊕ Fin k) (Fin I.n) I.E), B * Bi = 1 → Bi * B = 1 →
    ∀ (J' : Matrix (Fin k) (Fin k) I.E) (g : ℕ), 1 ≤ g →
    ∃ N : Subgroup (UPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F)),
      N ≤ stdLevel I J' ∧ N.relIndex (stdLevel I J') ≠ 0 ∧
      ∀ y ∈ N, ∀ h : I.Gf,
        I.fmat h = psiMat (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) B Bi
          ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
            Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) → h ∈ I.Kg g
end PI.UnitaryGroupMassFormula.InHHClassFin


