-- Prove2me | Definitions.Def_RPLib_S4_SwanGlobP
-- name    : RPLib_S4_SwanGlobP
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:39:00.47226+00:00
-- url     : https://prove2.me/theorems/ade4ebba-9b76-4fbd-861e-ce014e59e23a
-- title:
--   Swan conductors and breaks at infinity do not depend on the level of the cover
-- statement:
--   Let $C' \to C$ be a map of Galois covers of $\mathbb{F}_q(x)$ (a surjection of groups $G' \to G$ compatible with an embedding of fields $L \to L'$), and let $P'$ be a place of $L'$ over infinity lying over $P$. The file constructs the induced map of integral closures at infinity, proves that $I_{P'}$ maps onto $I_P$ and that the upper ramification groups correspond (Herbrand), so that for a representation $\rho$ of $G$ $$\mathrm{Sw}_{P'}(\rho \circ (G' \to G)) = \mathrm{Sw}_P(\rho),$$ and the breaks of $\rho$ at $P$ and of its inflation at $P'$ agree.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter IV, Section 3; N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), Chapter 1

import Mathlib
import Definitions.Def_RPLib_S4_SwanGlobS
import Definitions.Def_RPLib_S4_SwanGlobC
import Definitions.Def_RPLib_S4_SwanBrk

/-!
# S4-Swan (K2), part 19: Swan conductors and breaks at `∞` do not depend on the level

For a morphism of Galois covers `f : CoverHom C C'` with function fields `L ⊆ L'` (compatible with `f`), the
infinity charts form a tower `O_∞ → infChart L → infChart L'` (`infChartAlg`), every place `Q'` of `L'` over `∞`
lies over the place `underInf Q'` of `L`, and the inertia local data at the two places form a `LocData.Tower`
along `f.grpHom` (`infTower`, from `GlobS.inertiaTower`). Hence (`swanInf_comp`, `allBrkInf_comp`):

* `Sw_{Q'}(ρ ∘ f) = Sw_{Q' ∩ L}(ρ)` for every representation `ρ` of the cover group of `C`;
* `ρ ∘ f` has all breaks `x` at `Q'` iff `ρ` has all breaks `x` at `Q' ∩ L` (Herbrand's theorem).
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain

namespace RamanujanPetersson

namespace Swan.LocData

variable {G L G' L' : Type*} [Group G] [Field L] [MulSemiringAction G L]
  [Group G'] [Field L'] [MulSemiringAction G' L']
  {D : LocData G L} {D' : LocData G' L'} {ι : L →+* L'} {r : G' →* G} [Fintype r.ker]
  [Fintype G] [Fintype G'] [DecidableEq G]
  {k W : Type*} [Field k] [AddCommGroup W] [Module k W] (ρ : Representation k G W)

/-- Upper-numbering invariants do not depend on the level. -/
theorem Tower.fixd_upper (hT : Tower D D' ι r) (v : ℚ) :
    fixd (ρ.comp r) (D'.ramFn.upper v) = fixd ρ (D.ramFn.upper v) := by
  rw [fixd_comp, hT.map_upper]

/-- Breaks do not depend on the level. -/
theorem Tower.allBrk_iff (hT : Tower D D' ι r) (x : ℚ) :
    D'.ramFn.AllBrk (ρ.comp r) x ↔ D.ramFn.AllBrk ρ x := by
  simp only [RamFn.AllBrk, RamFn.BrkLE, hT.fixd_upper]

end Swan.LocData

namespace GalCover

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

section ChartMap

variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] (L L' : Type) [Field L] [Field L']
  [Algebra (RatFunc Fq) L] [Algebra (RatFunc Fq) L'] [Algebra L L'] [IsScalarTower (RatFunc Fq) L L']

theorem isScalarTower_Oinf : IsScalarTower (Places.Oinf Fq) L L' :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (Places.Oinf Fq) (RatFunc Fq) L,
      IsScalarTower.algebraMap_apply (Places.Oinf Fq) (RatFunc Fq) L',
      IsScalarTower.algebraMap_apply (RatFunc Fq) L L']

/-- The map of infinity charts induced by `L → L'`. -/
def infChartMap : infChart Fq L →ₐ[Places.Oinf Fq] infChart Fq L' :=
  haveI := isScalarTower_Oinf Fq L L'
  ((IsScalarTower.toAlgHom (Places.Oinf Fq) L L').comp (infChart Fq L).val).codRestrict
    (infChart Fq L') fun x =>
      (show IsIntegral (Places.Oinf Fq) (x : L) from x.2).map (IsScalarTower.toAlgHom (Places.Oinf Fq) L L')

theorem infChartMap_coe (x : infChart Fq L) : (infChartMap Fq L L' x : L') = algebraMap L L' x := rfl

/-- `infChart L'` as an algebra over `infChart L`. -/
abbrev infChartAlg : Algebra (infChart Fq L) (infChart Fq L') := (infChartMap Fq L L').toRingHom.toAlgebra

theorem infChart_faithfulSMul : FaithfulSMul (Places.Oinf Fq) (infChart Fq L) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro a b h
  have h2 := congrArg Subtype.val h
  change algebraMap (Places.Oinf Fq) L a = algebraMap (Places.Oinf Fq) L b at h2
  rw [IsScalarTower.algebraMap_apply (Places.Oinf Fq) (RatFunc Fq) L,
    IsScalarTower.algebraMap_apply (Places.Oinf Fq) (RatFunc Fq) L b] at h2
  exact IsFractionRing.injective (Places.Oinf Fq) (RatFunc Fq) ((algebraMap (RatFunc Fq) L).injective h2)

attribute [local instance] infChartAlg

theorem infChart_isScalarTower : IsScalarTower (Places.Oinf Fq) (infChart Fq L) (infChart Fq L') :=
  IsScalarTower.of_algHom (infChartMap Fq L L')

theorem infChart_faithfulSMul' : FaithfulSMul (infChart Fq L) (infChart Fq L') := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro a b h
  exact Subtype.ext ((algebraMap L L').injective (congrArg Subtype.val h))

theorem infChart_isScalarTower' : IsScalarTower (infChart Fq L) (infChart Fq L') L' :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem infChart_isIntegral : Algebra.IsIntegral (infChart Fq L) (infChart Fq L') := by
  haveI := infChart_isScalarTower Fq L L'
  exact Algebra.IsIntegral.tower_top (Places.Oinf Fq)

/-- The place of `L` under a place `Q'` of `L'` over `∞`. -/
def underInf (Q' : HeightOneSpectrum (infChart Fq L')) : HeightOneSpectrum (infChart Fq L) :=
  haveI := infChart_isIntegral Fq L L'
  Q'.under (infChart Fq L)

theorem underInf_asIdeal (Q' : HeightOneSpectrum (infChart Fq L')) :
    (underInf Fq L L' Q').asIdeal = Q'.asIdeal.comap (infChartMap Fq L L') := rfl

end ChartMap

section Action

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable (L : Type) [Field L] [Algebra C.B L] [IsFractionRing C.B L] [Algebra (RatFunc Fq) L]
  [Algebra A L] [IsScalarTower A (RatFunc Fq) L] [IsScalarTower A C.B L] [MulSemiringAction C.G L]
  [SMulDistribClass C.G C.B L]

/-- The cover group acting on the infinity chart. -/
abbrev infChartAction : MulSemiringAction C.G (infChart Fq L) := C.chartAction (RatFunc Fq) L (Places.Oinf Fq)

attribute [local instance] infChartAction in
theorem infChart_isGaloisGroup : IsGaloisGroup C.G (Places.Oinf Fq) (infChart Fq L) :=
  C.isGaloisGroup_chart (RatFunc Fq) L (Places.Oinf Fq)

end Action

section Level

variable {A : Type} [CommRing A] [IsDomain A] {C C' : GalCover A} (f : CoverHom C C')
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable {L : Type} [Field L] [Algebra C.B L] [IsFractionRing C.B L] [Algebra (RatFunc Fq) L]
  [Algebra A L] [IsScalarTower A (RatFunc Fq) L] [IsScalarTower A C.B L] [MulSemiringAction C.G L]
  [SMulDistribClass C.G C.B L]
variable {L' : Type} [Field L'] [Algebra C'.B L'] [IsFractionRing C'.B L'] [Algebra (RatFunc Fq) L']
  [Algebra A L'] [IsScalarTower A (RatFunc Fq) L'] [IsScalarTower A C'.B L'] [MulSemiringAction C'.G L']
  [SMulDistribClass C'.G C'.B L'] [Algebra L L'] [IsScalarTower (RatFunc Fq) L L']
variable (hf : ∀ b : C.B, algebraMap L L' (algebraMap C.B L b) = algebraMap C'.B L' (f.ringHom b))

include hf in
/-- The function fields are compatible with `f`. -/
theorem smul_algebraMap_frac (σ : C'.G) (x : L) :
    σ • algebraMap L L' x = algebraMap L L' (f.grpHom σ • x) := by
  have key : ∀ (τ : C'.G) (b : C.B), τ • algebraMap L L' (algebraMap C.B L b) =
      algebraMap L L' (f.grpHom τ • algebraMap C.B L b) := by
    intro τ b
    rw [hf, ← algebraMap.smul', ← f.equivariant, ← hf, algebraMap.smul']
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := C.B) x
  rw [map_div₀, smul_div₀', key, key, smul_div₀', map_div₀]

attribute [local instance] infChartAlg infChartAction infChart_isGaloisGroup infChart_faithfulSMul
  infChart_faithfulSMul' infChart_isScalarTower infChart_isScalarTower' infChart_isIntegral

include hf in
theorem chart_compat (σ : C'.G) (s : infChart Fq L) :
    σ • algebraMap (infChart Fq L) (infChart Fq L') s =
      algebraMap (infChart Fq L) (infChart Fq L') (f.grpHom σ • s) :=
  Subtype.ext (smul_algebraMap_frac f hf σ (s : L))

variable [FiniteDimensional (RatFunc Fq) L] [Algebra.IsSeparable (RatFunc Fq) L]
  [FiniteDimensional (RatFunc Fq) L'] [Algebra.IsSeparable (RatFunc Fq) L'] [Fintype Fq]

theorem infChart_finite' : Module.Finite (infChart Fq L) (infChart Fq L') :=
  Module.Finite.of_restrictScalars_finite (Places.Oinf Fq) _ _

attribute [local instance] infChart_finite'

/-- Restriction of inertia groups along `f`: `I(Q') → I(Q' ∩ L)` at places over `∞`. -/
def infInertiaRes (Q' : HeightOneSpectrum (infChart Fq L')) :
    C'.infInertia Fq L' Q'.asIdeal →* C.infInertia Fq L (underInf Fq L L' Q').asIdeal :=
  Swan.inertiaRes (S := infChart Fq L) (S' := infChart Fq L') (G := C.G) (G' := C'.G) (r := f.grpHom)
    (chart_compat f Fq hf) Q'

theorem infInertiaRes_coe (Q' : HeightOneSpectrum (infChart Fq L')) (σ : C'.infInertia Fq L' Q'.asIdeal) :
    (infInertiaRes f Fq hf Q' σ : C.G) = f.grpHom σ := rfl

/-- The local data at `Q'` and at `Q' ∩ L` form a tower along `f`. -/
theorem infTower (Q' : HeightOneSpectrum (infChart Fq L')) [Fintype (infInertiaRes f Fq hf Q').ker] :
    Swan.LocData.Tower (C.infLocData Fq L (underInf Fq L L' Q')) (C'.infLocData Fq L' Q')
      (algebraMap L L') (infInertiaRes f Fq hf Q') := by
  letI : Fintype (Swan.inertiaRes (S := infChart Fq L) (S' := infChart Fq L') (G := C.G) (G' := C'.G)
      (r := f.grpHom) (chart_compat f Fq hf) Q').ker := ‹Fintype (infInertiaRes f Fq hf Q').ker›
  have h := Swan.inertiaTower (R := Places.Oinf Fq) (S := infChart Fq L) (S' := infChart Fq L') (G := C.G)
    (G' := C'.G) (r := f.grpHom) (L := L) (L' := L') (chart_compat f Fq hf) Q' (hc := fun _ _ => rfl)
    (hc' := fun _ _ => rfl)
  convert h using 1 <;> first | rfl | exact HEq.rfl | exact Subsingleton.elim _ _

include hf in
/-- **Level independence of the Swan conductor at `∞`.** -/
theorem swanInf_comp {k V : Type} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k C.G V) (Q' : HeightOneSpectrum (infChart Fq L')) :
    C'.swanInf Fq L' (ρ.comp f.grpHom) Q' = C.swanInf Fq L ρ (underInf Fq L L' Q') := by
  classical
  have : Fintype (infInertiaRes f Fq hf Q').ker := Fintype.ofFinite _
  exact (infTower f Fq hf Q').swan_comp (ρ.comp (C.infInertia Fq L (underInf Fq L L' Q').asIdeal).subtype)

include hf in
/-- **Level independence of the breaks at `∞`.** -/
theorem allBrkInf_comp {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k C.G V) (Q' : HeightOneSpectrum (infChart Fq L')) (x : ℚ) :
    (C'.infRamFn Fq L' Q').AllBrk ((ρ.comp f.grpHom).comp (C'.infInertia Fq L' Q'.asIdeal).subtype) x ↔
      (C.infRamFn Fq L (underInf Fq L L' Q')).AllBrk
        (ρ.comp (C.infInertia Fq L (underInf Fq L L' Q').asIdeal).subtype) x := by
  classical
  have : Fintype (infInertiaRes f Fq hf Q').ker := Fintype.ofFinite _
  exact (infTower f Fq hf Q').allBrk_iff (ρ.comp (C.infInertia Fq L (underInf Fq L L' Q').asIdeal).subtype) x

end Level

end GalCover

end RamanujanPetersson


