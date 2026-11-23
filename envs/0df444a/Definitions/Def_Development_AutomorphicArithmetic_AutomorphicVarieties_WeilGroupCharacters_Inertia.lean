-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_Inertia
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_Inertia
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:18.556865+00:00
-- url     : https://prove2.me/theorems/34ce8970-a687-41fb-a2f1-d767d1bdc661
-- title:
--   Inertia
-- statement:
--   Definitions and structural lemmas for Inertia, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/WeilGroupCharacters/Inertia.lean

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_UniversalOrdinaryDeterminantRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing UpperTheory.V.Alg
namespace UpperTheory.V.W
def muG (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Subgroup G :=
  (CommGroup.primaryComponent (TopologicalAbelianization G) l).comap (QuotientGroup.mk' _)
structure LocAb (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (I : Subgroup G)
    (d : ℕ) where
  a : G →* Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l])
  cont : Continuous a
  surj : Function.Surjective a
  inertia : ∀ x : (Fin d → ℤ_[l]) × ℤ_[l], (∃ g ∈ I, a g = Multiplicative.ofAdd x) ↔ x.2 = 0
  univ : ∀ (C : Type) [CommGroup C] [Finite C], IsPGroup l C → ∀ χ : G →* C, IsOpen (χ.ker : Set G) →
    muG l G ≤ χ.ker → a.ker ≤ χ.ker
  b : G →* CommGroup.primaryComponent (TopologicalAbelianization G) l
  b_open : IsOpen (b.ker : Set G)
  b_mu : ∀ g ∈ muG l G, (b g : TopologicalAbelianization G) = QuotientGroup.mk' _ g
structure DetObj (O : Type) [CommRing O] [IsLocalRing O] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (Dbar : GDet n (ResidueField O) G) : Type 1 where
  R : Type
  [ring : CommRing R]
  [alg : Algebra O R]
  [co : IsCO O R]
  D : GDet n R G
  cont : D.IsCont (maximalIdeal R)
  red : D.map (res O R : R →+* ResidueField O) = Dbar
  univ : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (D' : GDet n R' G), D'.IsCont (maximalIdeal R') →
    D'.map (res O R' : R' →+* ResidueField O) = Dbar → ∃! f : R →ₐ[O] R', D.map (f : R →+* R') = D'
attribute [instance] DetObj.ring DetObj.alg DetObj.co
variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  (r : Resid F O n)
structure LamTObj : Type 1 where
  Λ : Type
  [ring : CommRing Λ]
  [alg : Algebra O Λ]
  [co : IsCO O Λ]
  ψ : ∀ v, Fin n → F.Gv v →* Λˣ
  psi : ∀ v i, r.IsPsi v i (ψ v i)
  univ : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ψ' : ∀ v, Fin n → F.Gv v →* Rˣ),
    (∀ v i, r.IsPsi v i (ψ' v i)) → ∃! f : Λ →ₐ[O] R, ∀ v i, pushCh (f : Λ →+* R) (ψ v i) = ψ' v i
attribute [instance] LamTObj.ring LamTObj.alg LamTObj.co
def Resid.Ok : Prop :=
  (∀ v (g : Fin n → F.Gv v) (h : F.G₀), r.Dbar.tr (MonoidAlgebra.single h 1 * F.oEl v (r.psib v) g) = 0) ∧
    ∀ v i (g : F.mu v), r.psib v i g = Units.map (residue O : O →* ResidueField O) (r.th v i g)
structure IsGPair {A : Type} [CommRing A] [Algebra O A] [IsLocalRing A] [IsLocalHom (algebraMap O A)]
    (D : GDet n A F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* Aˣ) : Prop where
  cont : D.IsCont (maximalIdeal A)
  red : D.map (residue A) = r.Dbar.map (ResidueField.map (algebraMap O A))
  ψ_cont : ∀ v i, AdicCont (maximalIdeal A) fun g => ((ψ v i g : Aˣ) : A)
  ψ_red : ∀ v i g, residue A (ψ v i g) = ResidueField.map (algebraMap O A) (r.psib v i g)
  ψ_mu : ∀ v i (g : F.mu v), ((ψ v i g : Aˣ) : A) = algebraMap O A (r.th v i g)
  P : ∀ i g, D.lam i (F.star O A n (MonoidAlgebra.single g 1)) = D.lam i (MonoidAlgebra.single g 1)
  Ord : ∀ v (g : Fin n → F.Gv v) (h : F.G₀), D.tr (MonoidAlgebra.single h 1 * F.oEl v (ψ v) g) = 0
  I : ∀ u, ∀ g ∈ r.Ip u, ∀ h : F.G₀, D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) = 0
structure FHom (F' F : GFrame l) where
  π : F'.Γ →* F.Γ
  π_cont : Continuous π
  hη : ∀ g, F.η (π g) = F'.η g
  hc : π F'.c = F.c
  hε : ∀ g, F.ε (π g) = F'.ε g
  vl : F'.Vl → F.Vl
  gv : ∀ v, F'.Gv v →* F.Gv (vl v)
  gv_cont : ∀ v, Continuous (gv v)
  hφ : ∀ v g, (F.φ (vl v) (gv v g) : F.Γ) = π (F'.φ v g)
  hI : ∀ v, ∀ g ∈ F'.Iv v, gv v g ∈ F.Iv (vl v)
namespace FHom
variable {F' : GFrame l} (h : FHom F' F)
def π₀ : F'.G₀ →* F.G₀ :=
  (h.π.comp F'.η.ker.subtype).codRestrict _ fun g => (h.hη g).trans g.2
structure Compat (r' : Resid F' O n) (r : Resid F O n) : Prop where
  chib : ∀ i, r'.chib i = (r.chib i).comp h.π₀
  psib : ∀ v i, r'.psib v i = (r.psib (h.vl v) i).comp (h.gv v)
  th : ∀ v i (g : F'.mu v) (hg : h.gv v g ∈ F.mu (h.vl v)), r'.th v i g = r.th (h.vl v) i ⟨_, hg⟩
  ip : ∀ u, ∀ g ∈ r'.Ip u, h.π₀ g = 1 ∨ ∃ u', h.π₀ g ∈ r.Ip u'
end FHom
end UpperTheory.V.W


