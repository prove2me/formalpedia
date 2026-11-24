-- Prove2me | Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
-- name    : Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:34:53.848202+00:00
-- url     : https://prove2.me/theorems/20143451-5821-4b16-b8a0-4a0d4f1c8401
-- title:
--   Quotient Hom Nonvanishing Bound
-- statement:
--   Definitions and structural lemmas for Quotient Hom Nonvanishing Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_ReciprocityTheory_Gal_LocalEulerCharAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalEulerChar_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalFinitenessAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalFiniteness_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalTateDualityAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalTateDuality_restrict
import Theorems.Thm_ReciprocityTheory_Gal_UnramifiedOrthogonalityAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_UnramifiedOrthogonality_restrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
def glRep {O G : Type} [CommRing O] [Monoid G] {n : Type} [Fintype n] [DecidableEq n]
    (ρ : G →* GL n O) : Representation O G (n → O) where
  toFun g := Matrix.toLin' ((ρ g : GL n O) : Matrix n n O)
  map_one' := by
    simp only [map_one, Units.val_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl
def twistRep {O G V : Type} [CommRing O] [Monoid G] [AddCommGroup V] [Module O V]
    (ρ : Representation O G V) (χ : G →* Oˣ) : Representation O G V where
  toFun g := ((χ g : Oˣ) : O) • ρ g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul]
    rw [smul_mul_smul_comm]
def coefRep {O G V : Type} [CommRing O] [Monoid G] [AddCommGroup V] [Module O V]
    (ρ : Representation O G V) (M : Type) [AddCommGroup M] [Module O M] :
    Representation O G (TensorProduct O V M) :=
  ρ.tprod (Representation.trivial O G M)
def locDeg (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) : ℕ :=
  v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ
namespace Glob
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
def epsO (i : N.Loc) : G H.E N.Om →* (N.O i)ˣ :=
  (Units.map (algebraMap ℤ_[N.l i] (N.O i)).toMonoidHom).comp (cycZ (F := H.E) (Ω := N.Om) (N.l i))
def Wp (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) :
    Representation (N.O i) (G H.E N.Om) (Fin R.r → N.O i) :=
  twistRep (glRep ρ) (N.chi i 1)⁻¹
def T2 (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) :
    Representation (N.O i) (G H.E N.Om) (Module.Dual (N.O i) (Fin R.r → N.O i)) :=
  twistRep (Representation.dual (Wp N i ρ)) (epsO N i)
def WpK (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) := coefRep (Wp N i ρ) (FractionRing (N.O i))
def WpKO (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) := coefRep (Wp N i ρ) (KmodO (N.O i))
def KOtw (i : N.Loc) (e : ℤ) : Representation (N.O i) (G H.E N.Om) (KmodO (N.O i)) :=
  Formalism.GaloisCohomology.scalRep (KmodO (N.O i)) ((epsO N i) ^ (-e))
def rChiInv (i : N.Loc) (r : G H.E N.Om →* GL (Fin R.nV) (N.O i)) :
    Representation (N.O i) (G H.E N.Om) (Fin R.nV → N.O i) :=
  twistRep (glRep r) (N.chi i 1)⁻¹
def rDualChi (i : N.Loc) (r : G H.E N.Om →* GL (Fin R.nV) (N.O i)) :
    Representation (N.O i) (G H.E N.Om) (Module.Dual (N.O i) (Fin R.nV → N.O i)) :=
  twistRep (Representation.dual (glRep r)) (N.chi i 1 * epsO N i)
end Glob
def liftSpanFinrank {R : Ranks} (what₂ : Rows.Data R) (μ : what₂.Tup) (j : ℕ) : ℕ :=
  Module.finrank ℂ (what₂.Zj μ j)
def hE {R : Ranks} (H : Host R) : ℕ := NumberField.classNumber H.E
end Formalism.MainNotions.N
end
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.WeaklyAdmissibleFiltrations Module
namespace Formalism.MainNotions.N
open Formalism.BasicNotions
section Mat
variable {Kf : Type} [CommRing Kf] {Γ : Type} [Group Γ] {k : ℕ}
def matRep (M : Γ →* Matrix (Fin k) (Fin k) Kf) : Representation Kf Γ (Fin k → Kf) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) Kf ≃ₐ[Kf] Module.End Kf (Fin k → Kf)).toAlgHom.toMonoidHom.comp M
def twistM (M : Γ →* Matrix (Fin k) (Fin k) Kf) (χ : Γ →* Kfˣ) : Γ →* Matrix (Fin k) (Fin k) Kf where
  toFun g := ((χ g : Kfˣ) : Kf) • M g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul]
    rw [smul_mul_smul_comm]
def mapM {S : Type} [CommRing S] (f : Kf →+* S) (M : Γ →* Matrix (Fin k) (Fin k) Kf) :
    Γ →* Matrix (Fin k) (Fin k) S :=
  f.mapMatrix.toMonoidHom.comp M
def dualM (M : Γ →* Matrix (Fin k) (Fin k) Kf) : Γ →* Matrix (Fin k) (Fin k) Kf where
  toFun g := (M g⁻¹).transpose
  map_one' := by simp
  map_mul' g h := by
    simp only [mul_inv_rev, map_mul, Matrix.transpose_mul]
end Mat
section Local
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]
def IsMatLat {V : Type} [AddCommGroup V] [Module LL V] [Module O V] {ρ : Representation LL G V}
    (L : Submodule O V) {k : ℕ} (M : G → Matrix (Fin k) (Fin k) LL) : Prop :=
  ∃ e : V ≃ₗ[LL] (Fin k → LL), (∀ g v, e (ρ g v) = (M g).mulVec (e v)) ∧
    ∀ v, v ∈ L ↔ ∀ j, e v j ∈ Set.range (algebraMap O LL)
def IsSubOfSums {V : Type} [AddCommGroup V] [Module LL V] (ρ : Representation LL G V)
    {ι : Type} {k : ℕ} (Ms : ι → G → Matrix (Fin k) (Fin k) LL) : Prop :=
  ∃ (m : ℕ) (xs : Fin m → ι) (j : V →ₗ[LL] (Fin m → Fin k → LL)), Function.Injective j ∧
    ∀ g v, j (ρ g v) = fun a => (Ms (xs a) g).mulVec (j v a)
def IsSubquotOfSums {V : Type} [AddCommGroup V] [Module LL V] (ρ : Representation LL G V)
    {ι : Type} {k : ℕ} (Ms : ι → G → Matrix (Fin k) (Fin k) LL) : Prop :=
  ∃ (m : ℕ) (xs : Fin m → ι) (U : Submodule LL (Fin m → Fin k → LL))
      (q : (Fin m → Fin k → LL) →ₗ[LL] V),
    (∀ g, ∀ u ∈ U, (fun a => (Ms (xs a) g).mulVec (u a)) ∈ U) ∧
    (∀ v, ∃ u ∈ U, q u = v) ∧
    (∀ g, ∀ u ∈ U, q (fun a => (Ms (xs a) g).mulVec (u a)) = ρ g (q u))
def RowAt {ι : Type} {k k2 : ℕ} (Ms : ι → G → Matrix (Fin k) (Fin k) LL)
    (TorusMatching : G → Matrix (Fin k2) (Fin k2) LL) (lenw : ℚ) : Prop :=
  ∀ (V2 : Type) [AddCommGroup V2] [Module LL V2] [Module Qp V2] [IsScalarTower Qp LL V2] [Module O V2] [IsScalarTower O LL V2] [TopologicalSpace V2] [ContinuousAdd V2] [ContinuousConstSMul LL V2] [IsModuleTopology LL V2] [FiniteDimensional LL V2] (ρ2 : Representation LL G V2) (T2 : Lattice (O := O) ρ2), (∀ x, Continuous fun g => ρ2 g x) → IsMatLat (ρ := ρ2) T2.T TorusMatching →
  ∀ (V1 : Type) [AddCommGroup V1] [Module LL V1] [Module Qp V1] [IsScalarTower Qp LL V1] [Module O V1] [IsScalarTower O LL V1] [TopologicalSpace V1] [ContinuousAdd V1] [ContinuousConstSMul LL V1] [IsModuleTopology LL V1] [FiniteDimensional LL V1] (ρ1 : Representation LL G V1) (T1 : Lattice (O := O) ρ1), (∀ x, Continuous fun g => ρ1 g x) → IsSubOfSums ρ1 Ms →
    ∀ F : LatHom T1 T2, F.Onto → F.ColLe PD lenw
def LiftAt {ι : Type} {k : ℕ} (Ms : ι → G → Matrix (Fin k) (Fin k) LL) (e' : ℕ) : Prop :=
  ∀ (V1 : Type) [AddCommGroup V1] [Module LL V1] [Module Qp V1] [IsScalarTower Qp LL V1] [Module O V1] [IsScalarTower O LL V1] [TopologicalSpace V1] [ContinuousAdd V1] [ContinuousConstSMul LL V1] [IsModuleTopology LL V1] [FiniteDimensional LL V1] (ρ1 : Representation LL G V1) (L1 : Lattice (O := O) ρ1), (∀ x, Continuous fun g => ρ1 g x) → IsSubquotOfSums ρ1 Ms →
  ∀ (V2 : Type) [AddCommGroup V2] [Module LL V2] [Module Qp V2] [IsScalarTower Qp LL V2] [Module O V2] [IsScalarTower O LL V2] [TopologicalSpace V2] [ContinuousAdd V2] [ContinuousConstSMul LL V2] [IsModuleTopology LL V2] [FiniteDimensional LL V2] (ρ2 : Representation LL G V2) (L2 : Lattice (O := O) ρ2), (∀ x, Continuous fun g => ρ2 g x) → IsSubquotOfSums ρ2 Ms →
    ∀ F : LatHom L1 L2, F.Onto → F.LiftF PD e'
def Z1urD {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (I : Subgroup G) :
    Submodule O (G → V ⧸ L.T) where
  carrier := {c | ∃ x : V ⧸ L.T, ∀ g ∈ I, c g = actD L g x - x}
  zero_mem' := ⟨0, fun g _ => by simp⟩
  add_mem' := by
    rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x + y, fun g hg => ?_⟩
    simp only [Pi.add_apply, hx g hg, hy g hg, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨x, hx⟩
    refine ⟨c • x, fun g hg => ?_⟩
    simp only [Pi.smul_apply, hx g hg, map_smul, smul_sub]
def epsTw (e : ℕ) (g : G) : Matrix (Fin 1) (Fin 1) LL :=
  fun _ _ => algebraMap Qp LL (((PD.χ g)⁻¹ : Qpˣ) : Qp) ^ e
def TBAt (I : Subgroup G) (J : (K →ₐ[Qp] LL) → Set ℤ) (t cB : ℕ) : Prop :=
  (∀ (Vy : Type) [AddCommGroup Vy] [Module LL Vy] [Module Qp Vy] [IsScalarTower Qp LL Vy] [Module O Vy] [IsScalarTower O LL Vy] [TopologicalSpace Vy] [ContinuousAdd Vy] [ContinuousConstSMul LL Vy] [IsModuleTopology LL Vy] [FiniteDimensional LL Vy] (ρy : Representation LL G Vy) (Ly : Lattice (O := O) ρy), (∀ x, Continuous fun g => ρy g x) → IsCrys PD ρy → (∀ τ, JumpsInV PD ρy τ (J τ)) →
    ∀ p : Vy →ₗ[LL] LL, (∀ g v, p (ρy g v) = p v) →
      (∀ v ∈ Ly.T, p v ∈ Set.range (algebraMap O LL)) →
    ∀ e₀ ∈ Ly.T, p e₀ = 1 →
    ∀ e : ℕ, e < t →
    ∀ (Ve : Type) [AddCommGroup Ve] [Module LL Ve] [Module Qp Ve] [IsScalarTower Qp LL Ve] [Module O Ve] [IsScalarTower O LL Ve] [TopologicalSpace Ve] [ContinuousAdd Ve] [ContinuousConstSMul LL Ve] [IsModuleTopology LL Ve] [FiniteDimensional LL Ve] (ρe : Representation LL G Ve) (Le : Lattice (O := O) ρe), (∀ x, Continuous fun g => ρe g x) → IsMatLat (ρ := ρe) Le.T (epsTw PD e) →
    ∀ φ : Vy →ₗ[O] (Ve ⧸ Le.T),
      (∀ g, ∀ y ∈ Ly.T, p y = 0 → φ (ρy g y) = actD Le g (φ y)) →
      ((PD.p : O) ^ cB) • (fun g => φ (ρy g e₀ - e₀)) ∈ HfD PD Le) ∧
  (∀ e : ℕ, e < t →
    ∀ (Ve : Type) [AddCommGroup Ve] [Module LL Ve] [Module Qp Ve] [IsScalarTower Qp LL Ve] [Module O Ve] [IsScalarTower O LL Ve] [TopologicalSpace Ve] [ContinuousAdd Ve] [ContinuousConstSMul LL Ve] [IsModuleTopology LL Ve] [FiniteDimensional LL Ve] (ρe : Representation LL G Ve) (Le : Lattice (O := O) ρe), (∀ x, Continuous fun g => ρe g x) → IsMatLat (ρ := ρe) Le.T (epsTw PD e) →
    (0 < e → divisibleCocycles Le ⊓ HfD PD Le ≤ BD Le) ∧
    (e = 0 → divisibleCocycles Le ⊓ HfD PD Le = divisibleCocycles Le ⊓ (Z1urD Le I ⊔ BD Le)) ∧
    Module.length O (↥(divisibleCocycles Le ⊓ (HfD PD Le).comap (((PD.p : O) ^ cB) • LinearMap.id)) ⧸
        (divisibleCocycles Le ⊓ HfD PD Le).comap (divisibleCocycles Le ⊓ (HfD PD Le).comap (((PD.p : O) ^ cB) • LinearMap.id)).subtype) ≤
      ((finrank Qp K : ℕ∞) + 1) * (cB : ℕ∞) * lenOl PD (O := O))
def GainBoundAt {X : Type} {n r : ℕ} (Mr : X → G →* Matrix (Fin n) (Fin n) LL) (χ1 : G →* LLˣ)
    (t : ℕ) (Mc : ℕ → G →* Matrix (Fin 1) (Fin 1) LL)
    (MW TorusMatching : G →* Matrix (Fin r) (Fin r) LL) : Prop :=
  (∀ x, IsCrys PD (matRep (Mr x))) ∧
  (∀ (τ : K →ₐ[Qp] LL) (x y : X) (a : ℤ),
    multV PD (matRep (twistM (Mr x) χ1⁻¹)) τ a = multV PD (matRep (twistM (Mr y) χ1⁻¹)) τ a) ∧
  (∀ (τ : K →ₐ[Qp] LL) (x : X) (a : ℤ), multV PD (matRep (twistM (Mr x) χ1⁻¹)) τ a ≤ 1) ∧
  (∀ c, 1 ≤ c → c ≤ t → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
    IsJumpV PD (matRep (Mc c)) τ a ↔ a = (c : ℤ) - 1) ∧
  (∀ (τ : K →ₐ[Qp] LL) (x : X), ¬ IsJumpV PD (matRep (twistM (Mr x) χ1⁻¹)) τ (-1)) ∧
  H0V (matRep MW) = ⊥ ∧ H0V (matRep TorusMatching) = ⊥
end Local
section Glob
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
abbrev GE : Type := G H.E N.Om
abbrev KK (i : N.Loc) : Type := FractionRing (N.O i)
abbrev kk (i : N.Loc) : Type := IsLocalRing.ResidueField (N.O i)
abbrev Gw (w : HeightOneSpectrum (𝓞 H.E)) : Type := ↥(Dec (F := H.E) (N.plOm.1 w))
abbrev decS (w : HeightOneSpectrum (𝓞 H.E)) : Gw N w →* GE N :=
  (Dec (F := H.E) (N.plOm.1 w)).subtype
def evT (i : N.Loc) (x : N.X i) : N.T i →+* N.O i :=
  (Pi.evalRingHom (fun _ : N.X i => N.O i) x).comp (N.T i).val.toRingHom
section RepTh
variable {Kf : Type} [Field Kf] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module Kf V]
def Stable (ρ : Representation Kf Γ V) (W : Submodule Kf V) : Prop := ∀ g, ∀ v ∈ W, ρ g v ∈ W
def IsSS (ρ : Representation Kf Γ V) : Prop :=
  ∀ W : Submodule Kf V, Stable ρ W → ∃ W' : Submodule Kf V, Stable ρ W' ∧ IsCompl W W'
def AbsIrrDistinct (ρ : Representation Kf Γ V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Vs : ι → Submodule Kf V)
    (hs : ∀ j, Stable ρ (Vs j)),
    DirectSum.IsInternal Vs ∧ (∀ j, Vs j ≠ ⊥) ∧
    (∀ j, Submodule.span Kf (Set.range fun g => (ρ g).restrict (hs j g)) = ⊤) ∧
    (∀ j j', j ≠ j' → ∀ e : Vs j ≃ₗ[Kf] Vs j',
      ¬ ∀ g v, e ((ρ g).restrict (hs j g) v) = (ρ g).restrict (hs j' g) (e v))
end RepTh
def wildSet (A : ValuationSubring N.Om) : Set (GE N) :=
  {σ | ∀ y : N.Om, y ≠ 0 → A.valuation (σ y / y - 1) < 1}
def TameGen (A : ValuationSubring N.Om) (γ₀ : GE N) : Prop :=
  ((Ine (F := H.E) A : Subgroup (GE N)) : Set (GE N)) ⊆
    closure ((Subgroup.closure (insert γ₀ (wildSet N A)) : Subgroup (GE N)) : Set (GE N))
def stdO (i : N.Loc) (k : ℕ) : Submodule (N.O i) (Fin k → KK N i) :=
  LinearMap.range (LinearMap.compLeft (Algebra.linearMap (N.O i) (KK N i)) (Fin k))
section Char
variable (i : N.Loc)
abbrev chiU (c : ℕ) : GE N →* (N.O i)ˣ := N.chi i c
abbrev epsU : GE N →* (N.O i)ˣ := Formalism.MainNotions.N.Glob.epsO N i
abbrev toK : N.O i →+* KK N i := algebraMap (N.O i) (KK N i)
end Char
section Loc1
variable (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
def rO (x : N.X i) : GE N →* Matrix (Fin R.nV) (Fin R.nV) (N.O i) := (Units.coeHom _).comp (r x)
def rhoO (π : N.X i) : GE N →* Matrix (Fin R.r) (Fin R.r) (N.O i) := (Units.coeHom _).comp (ρ π)
def WpO (π : N.X i) : GE N →* Matrix (Fin R.r) (Fin R.r) (N.O i) :=
  twistM (rhoO N i ρ π) (chiU N i 1)⁻¹
def T2O (π : N.X i) : GE N →* Matrix (Fin R.r) (Fin R.r) (N.O i) :=
  twistM (dualM (WpO N i ρ π)) (epsU N i)
def rTwO (x : N.X i) : GE N →* Matrix (Fin R.nV) (Fin R.nV) (N.O i) :=
  twistM (rO N i r x) (chiU N i 1)⁻¹
def rDuO (x : N.X i) : GE N →* Matrix (Fin R.nV) (Fin R.nV) (N.O i) :=
  twistM (dualM (rO N i r x)) (chiU N i 1 * epsU N i)
def chiRatO (c : ℕ) : GE N →* Matrix (Fin 1) (Fin 1) (N.O i) :=
  twistM (1 : GE N →* Matrix (Fin 1) (Fin 1) (N.O i)) (chiU N i c * (chiU N i 1)⁻¹)
def repK (x : N.X i) : Representation (KK N i) (GE N) (Fin R.nV → KK N i) :=
  matRep (mapM (toK N i) (rO N i r x))
end Loc1
def VS (i : N.Loc) (Y : Set (N.X i)) :
    Submodule (KK N i) (TensorProduct (N.O i) (KK N i) (N.Mt i)) :=
  ⨆ x ∈ Y, heckeEig (N.T i) (N.act i) x
def MtIn (i : N.Loc) : Submodule (N.O i) (TensorProduct (N.O i) (KK N i) (N.Mt i)) :=
  LinearMap.range (TensorProduct.mk (N.O i) (KK N i) (N.Mt i) 1)
def MtUp (i : N.Loc) (Z' : Finset (N.X i)) :
    Submodule (N.O i) (TensorProduct (N.O i) (KK N i) (N.Mt i)) :=
  (MtIn N i ⊔ (VS N i ((Z' : Set (N.X i))ᶜ)).restrictScalars (N.O i)) ⊓
    (VS N i (Z' : Set (N.X i))).restrictScalars (N.O i)
def MtLow (i : N.Loc) (Z' : Finset (N.X i)) :
    Submodule (N.O i) (TensorProduct (N.O i) (KK N i) (N.Mt i)) :=
  MtIn N i ⊓ (VS N i (Z' : Set (N.X i))).restrictScalars (N.O i)
theorem stdO_inj (i : N.Loc) (k : ℕ) :
    Function.Injective (LinearMap.compLeft (Algebra.linearMap (N.O i) (KK N i)) (Fin k)) := by
  intro u v h
  funext j
  exact IsFractionRing.injective (N.O i) (KK N i) (congrFun h j)
def stdLat (i : N.Loc) {Γ : Type} [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) (N.O i)) :
    Lattice (O := N.O i) (matRep (mapM (toK N i) M)) where
  T := stdO N i k
  stable g x hx := by
    obtain ⟨u, rfl⟩ := hx
    refine ⟨(M g).mulVec u, ?_⟩
    funext j
    simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply]
    show _ = ((M g).map (algebraMap (N.O i) (KK N i))).mulVec _ j
    exact RingHom.map_mulVec (algebraMap (N.O i) (KK N i)) (M g) u j
  fg := by
    rw [stdO, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  free := Module.Free.of_equiv (LinearEquiv.ofInjective _ (stdO_inj N i k))
  span := by
    rw [eq_top_iff, ← (Pi.basisFun (KK N i) (Fin k)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    funext j'
    simp [Pi.single_apply]
def actRep {O LL G V : Type} [CommRing O] [Field LL] [Algebra O LL] [Group G] [AddCommGroup V]
    [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    (L : Lattice (O := O) ρ) : Representation O G (V ⧸ L.T) where
  toFun g := actD L g
  map_one' := by
    ext x
    simp [actD]
  map_mul' g h := by
    ext x
    simp only [actD, map_mul]
    rfl
abbrev KOr (i : N.Loc) : Type := (Fin R.r → KK N i) ⧸ stdO N i R.r
instance (i : N.Loc) : TopologicalSpace (KOr N i) := ⊥
instance (i : N.Loc) : DiscreteTopology (KOr N i) := ⟨rfl⟩
instance (i : N.Loc) : IsTopologicalAddGroup (KOr N i) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology
instance (i : N.Loc) : ContinuousConstSMul (N.O i) (KOr N i) :=
  ⟨fun _ => continuous_of_discreteTopology⟩
section Sel
variable [∀ i, Algebra ℚ_[N.l i] (KK N i)] [∀ i, TopologicalSpace (KK N i)]
  [∀ i, IsTopologicalRing (KK N i)]
open Classical
variable (i : N.Loc) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
def WKO (π : N.X i) : Representation (N.O i) (GE N) (KOr N i) := actRep (stdLat N i (WpO N i ρ π))
def bkW (π : N.X i) (w : HeightOneSpectrum (𝓞 H.E))
    {G : Type} [Group G] [TopologicalSpace G] {K₀ Kw B BdR : Type} [Field K₀] [Field Kw]
    [Algebra ℚ_[N.l i] K₀] [Algebra ℚ_[N.l i] Kw] [Algebra K₀ Kw] [IsScalarTower ℚ_[N.l i] K₀ Kw]
    [CommRing B] [CommRing BdR] [Algebra ℚ_[N.l i] B] [Algebra K₀ B] [IsScalarTower ℚ_[N.l i] K₀ B]
    [Algebra ℚ_[N.l i] BdR] [Algebra K₀ BdR] [Algebra Kw BdR] [IsScalarTower ℚ_[N.l i] Kw BdR]
    [IsScalarTower K₀ Kw BdR] [IsScalarTower ℚ_[N.l i] K₀ BdR]
    (PD : PeriodData G ℚ_[N.l i] K₀ Kw B BdR) (ι : G →* Gw N w) :
    Submodule (N.O i) (H1 ((WKO N i ρ π).comp (decS N w))) :=
  ((Z1 ((WKO N i ρ π).comp (decS N w))).comap (Submodule.subtype _) ⊓
    (HfD PD (stdLat N i (((WpO N i ρ π).comp (decS N w)).comp ι))).comap
      ((LinearMap.funLeft (N.O i) (KOr N i) ι).comp (Submodule.subtype _))).map (Submodule.mkQ _)
def selPi (π : N.X i)
    (Ll : ∀ v, Submodule (N.O i) (H1 ((WKO N i ρ π).comp (Dec (F := H.E) (N.plOm.1 v)).subtype))) :
    Submodule (N.O i) (H1 (WKO N i ρ π)) :=
  Formalism.GaloisCohomology.SelAll (WKO N i ρ π) N.plOm
    (Formalism.GaloisCohomology.bkCond (WKO N i ρ π) N.plOm (N.l i) (↑(N.S i ∪ N.Q i)) Ll)
def jW (π : N.X i) (w : HeightOneSpectrum (𝓞 H.E))
    {G : Type} [Group G] [TopologicalSpace G] {K₀ Kw B BdR : Type} [Field K₀] [Field Kw]
    [Algebra ℚ_[N.l i] K₀] [Algebra ℚ_[N.l i] Kw] [Algebra K₀ Kw] [IsScalarTower ℚ_[N.l i] K₀ Kw]
    [CommRing B] [CommRing BdR] [Algebra ℚ_[N.l i] B] [Algebra K₀ B] [IsScalarTower ℚ_[N.l i] K₀ B]
    [Algebra ℚ_[N.l i] BdR] [Algebra K₀ BdR] [Algebra Kw BdR] [IsScalarTower ℚ_[N.l i] Kw BdR]
    [IsScalarTower K₀ Kw BdR] [IsScalarTower ℚ_[N.l i] K₀ BdR]
    (PD : PeriodData G ℚ_[N.l i] K₀ Kw B BdR) (ι : G →* Gw N w) : ℕ :=
  finrank (KK N i) (FiniteCohomology PD (matRep (mapM (toK N i) (((WpO N i ρ π).comp (decS N w)).comp ι))))
def h0W (π : N.X i) (w : HeightOneSpectrum (𝓞 H.E)) : ℚ :=
  lenUnit (O := N.O i) (N.l i) ↥(Representation.invariants ((WKO N i ρ π).comp (decS N w)))
def lenCol (e' : ℕ) (j : ℕ) (π : N.X i) (w : HeightOneSpectrum (𝓞 H.E)) : ℚ :=
  (e' : ℚ) + (j : ℚ) * ((e' : ℚ) + N.vdel i) + 2 * N.vdel i + h0W N i ρ π w
end Sel
def h0 (i : N.Loc) (col : Finset (HeightOneSpectrum (𝓞 H.E))) : ℚ :=
  WithBot.unbotD 0 ((col ×ˢ (Finset.Ioo 0 R.t)).image (fun p =>
    lenUnit (O := N.O i) (N.l i)
      ↥(Representation.invariants ((Formalism.MainNotions.N.Glob.KOtw N i (p.2 : ℤ)).comp (decS N p.1))))).max
end Glob
end Formalism.MainNotions.N
noncomputable section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
section Rings
variable (i : N.Loc)
abbrev MatN : Type := Matrix (Fin R.nV) (Fin R.nV) (N.O i)
def InSpan {X' : Type} (T' : Subalgebra (N.O i) (X' → N.O i)) (rep : X' → (GE N →* MatN N i))
    (a : X' → MatN N i) : Prop :=
  ∃ (m : ℕ) (f : Fin m → X' → N.O i) (g : Fin m → GE N), (∀ k, f k ∈ T') ∧
    a = ∑ k, fun x' => f k x' • rep x' (g k)
def CharpolyCoeffsInSubalgebra {X' : Type} (T' : Subalgebra (N.O i) (X' → N.O i)) (rep : X' → (GE N →* MatN N i)) :
    Prop :=
  (∀ (m : ℕ) (a : Fin m → X' → MatN N i), (∀ k, InSpan N i T' rep (a k)) →
    ∀ d : Fin m →₀ ℕ,
      (fun x' => MvPolynomial.coeff d (Matrix.det (∑ k,
        (MvPolynomial.X k : MvPolynomial (Fin m) (N.O i)) • (a k x').map MvPolynomial.C))) ∈ T') ∧
  (∀ (g : ℕ) (Θ : Fin g → Fin g → X' → MatN N i), (∀ p q, InSpan N i T' rep (Θ p q)) →
    (fun x' => Matrix.det (Matrix.of fun (pa qb : Fin g × Fin R.nV) =>
      Θ pa.1 qb.1 x' pa.2 qb.2)) ∈ T')
def InR (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (a : N.X i → MatN N i) : Prop :=
  InSpan N i (N.T i) (rO N i r) a
structure IdempotentChoiceData where
  eB : N.X i → MatN N i
  e1 : N.X i → MatN N i
  g0 : GE N
  X0 : N.X i → MatN N i
  X' : Type
  [finX' : Fintype X']
  [decX' : DecidableEq X']
  p : X' → N.X i
  T' : Subalgebra (N.O i) (X' → N.O i)
  rr : ℕ → X' → N.O i
  π' : X'
  e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i))
  ψρ : (X' → MatN N i) → Matrix (Fin R.r) (Fin R.r) (N.O i)
  ψχ : Fin R.t → (X' → MatN N i) → N.O i
attribute [instance] IdempotentChoiceData.finX' IdempotentChoiceData.decX'
variable {i} (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
def InR' (S : IdempotentChoiceData N i) (a : S.X' → MatN N i) : Prop :=
  InSpan N i S.T' (fun x' => rO N i r (S.p x')) a
def Eel (S : IdempotentChoiceData N i) (x' : S.X') : MatN N i :=
  ((List.range' 2 (R.t - 1)).map fun c => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')).prod
def del51 (S : IdempotentChoiceData N i) (x' : S.X') : N.O i :=
  ∏ c ∈ Finset.Ioc 1 R.t, (S.rr 1 x' - S.rr c x')
def GoodCongruenceObjects (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) (S : IdempotentChoiceData N i) : Prop :=

  (InR N i r S.eB ∧ InR N i r S.e1 ∧ S.eB * S.eB = S.eB ∧ S.e1 * S.e1 = S.e1 ∧
    S.eB * S.e1 = 0 ∧ S.e1 * S.eB = 0 ∧
    (∀ x, ((S.eB x).map (toK N i)).rank = R.t) ∧ (∀ x, ((S.e1 x).map (toK N i)).rank = 1)) ∧

  (∀ g u, S.e ((mapM (toK N i) (rO N i r π) g).mulVec u) =
      ((mapM (toK N i) (rhoO N i ρ π) g).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧
  (∀ a, InR' N r S a → ∀ u, S.e (((a S.π').map (toK N i)).mulVec u) =
      (((S.ψρ a).map (toK N i)).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i (S.ψχ c a) * (S.e u).2 c)) ∧
  (∀ A : Matrix (Fin R.r) (Fin R.r) (N.O i), ∃ a, InR' N r S a ∧ S.ψρ a = A) ∧

  (∃ w ∈ placesOver H.E (N.l i), S.g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
  (∃ u : ℤ_[N.l i]ˣ, ((cycZ (F := H.E) (Ω := N.Om) (N.l i) S.g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
    1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * (u : ℤ_[N.l i])) ∧

  (InR N i r S.X0 ∧ S.eB * S.X0 = S.X0 ∧ S.X0 * S.eB = S.X0 ∧
    ∀ u, S.e (((S.X0 π).map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) S.g0 : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧

  ((∀ f ∈ N.T i, (fun x' => f (S.p x')) ∈ S.T') ∧ (∀ c ∈ Finset.Icc 1 R.t, S.rr c ∈ S.T') ∧
    S.T' = Algebra.adjoin (N.O i) ((fun f : N.X i → N.O i => fun x' => f (S.p x')) '' (N.T i : Set _) ∪
      (fun c => S.rr c) '' (Finset.Icc 1 R.t : Set ℕ)) ∧
    (∃ b : Fin R.t.factorial → S.X' → N.O i, (∀ k, b k ∈ S.T') ∧
      ∀ f ∈ S.T', ∃! cf : Fin R.t.factorial → N.T i,
        f = ∑ k, ((fun x' => (cf k : N.X i → N.O i) (S.p x')) : S.X' → N.O i) * b k) ∧
    (∀ x, Nat.card {x' // S.p x' = x} = R.t.factorial)) ∧

  (∀ x', ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x')) =
    Matrix.det ((Polynomial.X : Polynomial (N.O i)) • (S.eB (S.p x')).map (Polynomial.C (R := N.O i)) -
      (S.X0 (S.p x')).map (Polynomial.C (R := N.O i)) + 1 -
      (S.eB (S.p x')).map (Polynomial.C (R := N.O i)))) ∧

  (S.p S.π' = π ∧ ∀ c ∈ Finset.Icc 1 R.t,
    S.rr c S.π' = ((chiU N i c S.g0 : (N.O i)ˣ) : N.O i)) ∧

  ((∀ x', ((Eel N S x').map (toK N i)).rank = 1) ∧
    (∀ x', Eel N S x' * Eel N S x' = del51 N S x' • Eel N S x') ∧
    (∀ u, S.e (((Eel N S S.π').map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => if (c : ℕ) = 0 then toK N i (del51 N S S.π') * (S.e u).2 c else 0)) ∧
    lenUnit (O := N.O i) (N.l i) (N.O i ⧸ Ideal.span {del51 N S S.π'}) = N.vdel i) ∧

  CharpolyCoeffsInSubalgebra N i S.T' (fun x' => rO N i r (S.p x'))
def VanishingLemma (π : N.X i) (S : IdempotentChoiceData N i) : Prop :=
  ∀ f ∈ S.T', (∀ x', S.p x' ∉ N.Z i → f x' = 0) → f S.π' ∈ ccAt (N.T i) (N.Z i) π
def matQ (A : Matrix (Fin R.r) (Fin R.r) (N.O i)) : KOr N i →ₗ[N.O i] KOr N i :=
  (stdO N i R.r).mapQ (stdO N i R.r)
    (((A.map (toK N i)).mulVecLin).restrictScalars (N.O i)) (by
      rintro _ ⟨u, rfl⟩
      refine ⟨A.mulVec u, ?_⟩
      funext j
      exact RingHom.map_mulVec (toK N i) A u j)
def homRho (S : IdempotentChoiceData N i) {g : ℕ} (Rel : Set (Fin g → S.X' → MatN N i)) :
    Submodule (N.O i) (Fin g → KOr N i) :=
  ⨅ θ ∈ Rel, LinearMap.ker (∑ j, (matQ N (S.ψρ (θ j))).comp (LinearMap.proj j))
def homChi (S : IdempotentChoiceData N i) {g : ℕ} (Rel : Set (Fin g → S.X' → MatN N i)) (c : Fin R.t) :
    Submodule (N.O i) (Fin g → KmodO (N.O i)) :=
  ⨅ θ ∈ Rel, LinearMap.ker (∑ j, S.ψχ c (θ j) •
    (LinearMap.proj j : (Fin g → KmodO (N.O i)) →ₗ[N.O i] KmodO (N.O i)))
def QuotientHomNonvanishingBound (π : N.X i) (S : IdempotentChoiceData N i) : Prop :=
  ∀ (g : ℕ), ((g * R.nV : ℕ) : Cardinal) < Cardinal.mk (kk N i) →
  ∀ (Rel : Set (Fin g → S.X' → MatN N i)),
    (∀ θ ∈ Rel, ∀ j, InR' N r S (θ j)) → 0 ∈ Rel → (∀ θ ∈ Rel, ∀ θ' ∈ Rel, θ + θ' ∈ Rel) →
    (∀ a, InR' N r S a → ∀ θ ∈ Rel, (fun j => a * θ j) ∈ Rel) →
    (∀ x', S.p x' ∉ N.Z i → ∃ v : Fin g → Fin R.nV → KK N i, v ≠ 0 ∧
      ∀ θ ∈ Rel, ∑ j, ((θ j x').map (toK N i)).mulVec (v j) = 0) →
    Module.length (N.O i) ↥(homRho N S Rel) < ⊤ →
    (∀ c, Module.length (N.O i) ↥(homChi N S Rel c) < ⊤) →
    N.vcc i π ≤ lenUnit (O := N.O i) (N.l i) ↥(homRho N S Rel) +
      ∑ c, lenUnit (O := N.O i) (N.l i) ↥(homChi N S Rel c)
def yg (S : IdempotentChoiceData N i) (γ : GE N) (x' : S.X') : MatN N i :=
  (((chiU N i 1 γ)⁻¹ : (N.O i)ˣ) : N.O i) • (rO N i r (S.p x') γ * Eel N S x') - Eel N S x'
def InY (S : IdempotentChoiceData N i) (y : S.X' → MatN N i) : Prop :=
  ∃ (m : ℕ) (a : Fin m → S.X' → MatN N i) (γ : Fin m → GE N), (∀ k, InR' N r S (a k)) ∧
    y = ∑ k, a k * yg N r S (γ k)
end Rings
section G5
variable {i : N.Loc} (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
abbrev kr (i : N.Loc) : Type := Fin R.r → kk N i
instance (i : N.Loc) : TopologicalSpace (kr N i) := ⊥
instance (i : N.Loc) : DiscreteTopology (kr N i) := ⟨rfl⟩
instance (i : N.Loc) : IsTopologicalAddGroup (kr N i) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology
instance (i : N.Loc) : ContinuousConstSMul (kk N i) (kr N i) :=
  ⟨fun _ => continuous_of_discreteTopology⟩
def rhoBarTw (π : N.X i) (a : ℤ) : Representation (kk N i) (GE N) (kr N i) :=
  matRep (mapM (IsLocalRing.residue (N.O i))
    (twistM (rhoO N i ρ π) ((chiU N i 1)⁻¹ * (epsU N i) ^ a)))
def TameInertiaCondition (π : N.X i) (S : IdempotentChoiceData N i) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 H.E), (v ∈ N.S i ∨ v ∈ N.Q i) →
    TameGen N (N.plOm.1 v) (N.gam0 i v) ∧
    ((v ∈ N.Q i ∨ v ∈ placesOver H.E H.pde) →
      (∀ x, ∀ γ ∈ Ine (F := H.E) (N.plOm.1 v),
        (rO N i r x γ - 1) *
          (rO N i r x γ - ((chiU N i 1 γ : (N.O i)ˣ) : N.O i) • (1 : MatN N i)) = 0) ∧
      ∃ γ ∈ Ine (F := H.E) (N.plOm.1 v), chiU N i 1 γ ≠ 1) ∧
    ((∃ k, v ∈ placesOver H.E (H.g k)) →
      ∃ P : Polynomial (N.T i),
        (∀ x, ∀ γ ∈ Ine (F := H.E) (N.plOm.1 v),
          Polynomial.aeval (rO N i r x (N.gam0 i v)) (P.map (evT N i x)) *
            (rO N i r x γ - ((chiU N i 1 γ : (N.O i)ˣ) : N.O i) • (1 : MatN N i)) = 0) ∧
        IsUnit (P.eval (algebraMap (N.O i) (N.T i) (N.zeta i v)))) ∧
    (v ∈ N.S i →
      (∀ c : Fin R.t, ∀ φ : (S.X' → MatN N i) →ₗ[N.O i] KmodO (N.O i),
        (∀ a, InR' N r S a → ∀ y, InY N r S y → φ (a * y) = S.ψχ c a • φ y) →
        ∀ γ ∈ Ine (F := H.E) (N.plOm.1 v), φ (yg N r S γ) = 0) ∧
      ∀ a : ℤ,
        Subsingleton ↥(H0 ((rhoBarTw N ρ π a).comp (decS N v))) ∧
        Subsingleton (H1 ((rhoBarTw N ρ π a).comp (decS N v))) ∧
        Subsingleton (H2 ((rhoBarTw N ρ π a).comp (decS N v))))
end G5
end Formalism.MainNotions.N
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations Module
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc
section Std
def stdG (O LL : Type) [CommRing O] [Field LL] [Algebra O LL] (k : ℕ) : Submodule O (Fin k → LL) :=
  LinearMap.range (LinearMap.compLeft (Algebra.linearMap O LL) (Fin k))
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]
theorem stdG_inj (hinj : Function.Injective (algebraMap O LL)) (k : ℕ) :
    Function.Injective (LinearMap.compLeft (Algebra.linearMap O LL) (Fin k)) := by
  intro u v h
  funext j
  exact hinj (congrFun h j)
def stdLatG (hinj : Function.Injective (algebraMap O LL)) {Γ : Type} [Group Γ] {k : ℕ}
    (M : Γ →* Matrix (Fin k) (Fin k) O) : Lattice (O := O) (matRep (mapM (algebraMap O LL) M)) where
  T := stdG O LL k
  stable g x hx := by
    obtain ⟨u, rfl⟩ := hx
    refine ⟨(M g).mulVec u, ?_⟩
    funext j
    simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply]
    show _ = ((M g).map (algebraMap O LL)).mulVec _ j
    exact RingHom.map_mulVec (algebraMap O LL) (M g) u j
  fg := by
    rw [stdG, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  free := Module.Free.of_equiv (LinearEquiv.ofInjective _ (stdG_inj hinj k))
  span := by
    rw [eq_top_iff, ← (Pi.basisFun LL (Fin k)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    funext j'
    simp [Pi.single_apply]
end Std
abbrev KOG (O : Type) [CommRing O] [IsDomain O] (k : ℕ) : Type :=
  (Fin k → FractionRing O) ⧸ stdG O (FractionRing O) k
section KOGtop
variable (O : Type) [CommRing O] [IsDomain O] (k : ℕ)
instance : TopologicalSpace (KOG O k) := ⊥
instance : DiscreteTopology (KOG O k) := ⟨rfl⟩
instance : IsTopologicalAddGroup (KOG O k) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology
instance : ContinuousConstSMul O (KOG O k) := ⟨fun _ => continuous_of_discreteTopology⟩
end KOGtop
def WKG {O : Type} [CommRing O] [IsDomain O] {Γ : Type} [Group Γ] {k : ℕ}
    (M : Γ →* Matrix (Fin k) (Fin k) O) : Representation O Γ (KOG O k) :=
  actRep (stdLatG (IsFractionRing.injective O (FractionRing O)) M)
namespace Br
section Gen
variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)
abbrev LLw : Type := ↥Bw.LL.1
abbrev Ow : Type := ↥(OL Bw.LL)
theorem toLL_inj : Function.Injective Bw.toLL := fun _ _ h => Bw.eO.injective (Subtype.ext h)
def ι : ↥(GK Bw.Kw) →* ↥Gw := Bw.e.symm.toMonoidHom
def locO {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O) :
    ↥(GK Bw.Kw) →* Matrix (Fin k) (Fin k) (Ow Bw) :=
  (mapM Bw.eO.toRingHom M).comp (ι Bw)
def locM {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O) :
    ↥(GK Bw.Kw) →* Matrix (Fin k) (Fin k) (LLw Bw) :=
  mapM (algebraMap (Ow Bw) (LLw Bw)) (locO Bw M)
def lat {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O) :
    Lattice (O := Ow Bw) (matRep (locM Bw M)) :=
  stdLatG Subtype.val_injective (locO Bw M)
variable [IsDomain O]
def toLLK : FractionRing O →+* LLw Bw := IsFractionRing.lift (toLL_inj Bw)
theorem toLLK_alg (c : O) :
    toLLK Bw (algebraMap O (FractionRing O) c) = algebraMap (Ow Bw) (LLw Bw) (Bw.eO c) :=
  IsFractionRing.lift_algebraMap _ _
def vecS (k : ℕ) : (Fin k → FractionRing O) →ₛₗ[Bw.eO.toRingHom] (Fin k → LLw Bw) where
  toFun v j := toLLK Bw (v j)
  map_add' u v := by
    funext j
    simp
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, toLLK_alg]
    rfl
set_option synthInstance.maxHeartbeats 400000 in

def phi (k : ℕ) : KOG O k →ₛₗ[Bw.eO.toRingHom] ((Fin k → LLw Bw) ⧸ stdG (Ow Bw) (LLw Bw) k) :=
  Submodule.mapQ _ _ (vecS Bw k) (by
    rintro _ ⟨u, rfl⟩
    refine ⟨fun j => Bw.eO (u j), ?_⟩
    funext j
    exact (toLLK_alg Bw (u j)).symm)
set_option synthInstance.maxHeartbeats 400000 in

def Phi {k : ℕ} (rho : Representation O ↥Gw (KOG O k)) :
    ↥(Z1 rho) →ₛₗ[Bw.eO.toRingHom] (↥(GK Bw.Kw) → (Fin k → LLw Bw) ⧸ stdG (Ow Bw) (LLw Bw) k) where
  toFun c g := phi Bw k ((c : ↥Gw → KOG O k) (ι Bw g))
  map_add' a b := by
    funext g
    exact (phi Bw k).map_add _ _
  map_smul' c a := by
    funext g
    exact (phi Bw k).map_smulₛₗ c _
set_option synthInstance.maxHeartbeats 400000 in

def bkG (P : LocPrime l) {k : ℕ} (rho : Representation O ↥Gw (KOG O k))
    (M : ↥Gw →* Matrix (Fin k) (Fin k) O) : Submodule O (H1 rho) :=
  ((HfD (P.PD Bw.Kw) (lat Bw M)).comap (Phi Bw rho)).map (Submodule.mkQ _)
def ιHomeo : ↥(GK Bw.Kw) ≃ₜ ↥Gw where
  toEquiv := Bw.e.symm.toEquiv
  continuous_toFun := Bw.e_symm_cont
  continuous_invFun := Bw.e_cont
instance finKw : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
instance finLL : FiniteDimensional ℚ_[l] (LLw Bw) := Bw.LL.2
def cE : E →+* ↥Bw.Kw.1 := (Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 Bw.j_E
def SplitsW : Prop := Nat.card (↥Bw.Kw.1 →ₐ[ℚ_[l]] LLw Bw) = finrank ℚ_[l] ↥Bw.Kw.1
def EOAlg : Prop :=
  ∀ z : ℤ_[l], Bw.eO (algebraMap ℤ_[l] O z) = algebraMap ℤ_[l] (Ow Bw) z
def EOTop : Prop := Continuous Bw.eO ∧ Continuous Bw.eO.symm
def chiG (χ : ↥Gw →* Oˣ) : ↥(GK Bw.Kw) →* (LLw Bw)ˣ :=
  (Units.map Bw.toLL.toMonoidHom).comp (χ.comp (ι Bw))
def jG (P : LocPrime l) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O) : ℕ :=
  finrank (LLw Bw) (FiniteCohomology (P.PD Bw.Kw) (matRep (locM Bw M)))
end Gen
section GenSel
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω)
  (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (P : LocPrime l)
  (nb : ∀ w, w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (A.1 w)) O)
open Classical in

def LlG {k : ℕ} (M : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O) :
    ∀ v, Submodule O (H1 ((WKG M).comp (Dec (F := E) (A.1 v)).subtype)) :=
  fun v => if h : v ∈ placesOver E l then
    bkG (nb v h) P ((WKG M).comp (Dec (F := E) (A.1 v)).subtype) (M.comp (Dec (F := E) (A.1 v)).subtype)
  else ⊤
def selG (Sig : Set (HeightOneSpectrum (𝓞 E))) {k : ℕ} (M : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O) :
    Submodule O (H1 (WKG M)) :=
  Formalism.GaloisCohomology.SelAll (WKG M) A (Formalism.GaloisCohomology.bkCond (WKG M) A l Sig (LlG A l P nb M))
end GenSel
section Loc
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
abbrev NBr : Type :=
  ∀ (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)), w ∈ placesOver H.E (N.l i) →
    LocBridge (N.l i) H.E N.Om (Dec (F := H.E) (N.plOm.1 w)) (N.O i)
variable {N} (L : LocTheory) (nbr : NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E))
  (hw : w ∈ placesOver H.E (N.l i))
abbrev G : Type := ↥(GK (nbr i w hw).Kw)
abbrev K0 : Type := ↥(Loc.K0 (nbr i w hw).Kw)
abbrev Kw : Type := ↥(nbr i w hw).Kw.1
abbrev LL : Type := ↥(nbr i w hw).LL.1
abbrev OLL : Type := ↥(OL (nbr i w hw).LL)
def PD : PeriodData (G nbr i w hw) ℚ_[N.l i] (K0 nbr i w hw) (Kw nbr i w hw) (L (N.l i)).R.B
    (L (N.l i)).R.BdR :=
  (L (N.l i)).PD (nbr i w hw).Kw
def iota : G nbr i w hw →* Gw N w := ι (nbr i w hw)
def loc {k : ℕ} (M : GE N →* Matrix (Fin k) (Fin k) (N.O i)) :
    G nbr i w hw →* Matrix (Fin k) (Fin k) (LL nbr i w hw) :=
  locM (nbr i w hw) (M.comp (decS N w))
def locChi (χ : GE N →* (N.O i)ˣ) : G nbr i w hw →* (LL nbr i w hw)ˣ :=
  chiG (nbr i w hw) (χ.comp (decS N w))
def inert : Subgroup (G nbr i w hw) :=
  ((Ine (F := H.E) (N.plOm.1 w)).subgroupOf (Dec (F := H.E) (N.plOm.1 w))).comap (iota nbr i w hw)
def locLat {k : ℕ} (M : GE N →* Matrix (Fin k) (Fin k) (N.O i)) :
    Lattice (O := OLL nbr i w hw) (matRep (loc nbr i w hw M)) :=
  lat (nbr i w hw) (M.comp (decS N w))
def bk {k : ℕ} (M : GE N →* Matrix (Fin k) (Fin k) (N.O i)) :
    Submodule (N.O i) (H1 ((WKG M).comp (decS N w))) :=
  bkG (nbr i w hw) (L (N.l i)) ((WKG M).comp (decS N w)) (M.comp (decS N w))
def cEw : H.E →+* Kw nbr i w hw := cE (nbr i w hw)
section Pt
variable (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)
def jW : ℕ := jG (nbr i w hw) (L (N.l i)) ((WpO N i ρ π).comp (decS N w))
def WKO : Representation (N.O i) (GE N) (KOG (N.O i) R.r) := WKG (WpO N i ρ π)
def h0W : ℚ :=
  lenUnit (O := N.O i) (N.l i) ↥(Representation.invariants ((WKO i ρ π).comp (decS N w)))
def lenCol (e' : ℕ) : ℚ :=
  (e' : ℚ) + (jW L nbr i w hw ρ π : ℚ) * ((e' : ℚ) + N.vdel i) + 2 * N.vdel i + h0W i w ρ π
def selPi : Submodule (N.O i) (H1 (WKO i ρ π)) :=
  selG N.plOm (N.l i) (L (N.l i)) (nbr i) (↑(N.S i) ∪ ↑(N.Q i)) (WpO N i ρ π)
def sPi : ℚ := lenUnit (O := N.O i) (N.l i) ↥(selPi L nbr i ρ π)
def sFin : Prop := Module.length (N.O i) ↥(selPi L nbr i ρ π) < ⊤
end Pt
section Cr
variable {m : ℕ} (r : GE N →* GL (Fin m) (N.O i))
def IsCrysW : Prop := (nbr i w hw).IsCrysW (L (N.l i)) (r.comp (decS N w))
def IsdRW : Prop := (nbr i w hw).IsdRW (L (N.l i)) (r.comp (decS N w))
def IsPotCrysW : Prop := (nbr i w hw).IsPotCrysW (L (N.l i)) (r.comp (decS N w))
def IsJumpW (τ : Kw nbr i w hw →ₐ[ℚ_[N.l i]] LL nbr i w hw) (a : ℤ) : Prop :=
  (nbr i w hw).IsJumpW (L (N.l i)) (r.comp (decS N w)) τ a
def jumpMult (τ : Kw nbr i w hw →ₐ[ℚ_[N.l i]] LL nbr i w hw) (a : ℤ) : ℤ :=
  multV (PD L nbr i w hw) ((nbr i w hw).rep (r.comp (decS N w))) τ a
end Cr
def DegW : Prop := finrank ℚ_[N.l i] (Kw nbr i w hw) = locDeg H.E w
def EmbTypeU (τ : Kw nbr i w hw →ₐ[ℚ_[N.l i]] LL nbr i w hw) : Prop :=
  (∀ x : H.E, ∃ y : what₂.LL, toLLK (nbr i w hw) (N.embK i y) = τ (cEw nbr i w hw x)) ∧
  ∃ φ ∈ H.cmType,
    ∀ (x : H.E) (y : what₂.LL), toLLK (nbr i w hw) (N.embK i y) = τ (cEw nbr i w hw x) →
      what₂.embLL y = φ x
def PlTypeU : Prop := ∀ τ, EmbTypeU nbr i w hw τ
end Loc
section Tw
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} (tw : NTw R H what₂ LL0 N)
abbrev NBrTw : Type :=
  ∀ (i : tw.Tw) (w : HeightOneSpectrum (𝓞 H.E)), w ∈ placesOver H.E (tw.l i) →
    LocBridge (tw.l i) H.E N.Om (Dec (F := H.E) (N.plOm.1 w)) (tw.O0 i)
variable {tw} (L : LocTheory) (nbt : NBrTw tw) (i : tw.Tw)
def bkTw (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (tw.l i)) {k : ℕ}
    (M : GE N →* Matrix (Fin k) (Fin k) (tw.O0 i)) :
    Submodule (tw.O0 i) (H1 ((WKG M).comp (decS N w))) :=
  bkG (nbt i w hw) (L (tw.l i)) ((WKG M).comp (decS N w)) (M.comp (decS N w))
def selTw (Sig : Set (HeightOneSpectrum (𝓞 H.E))) {k : ℕ}
    (M : GE N →* Matrix (Fin k) (Fin k) (tw.O0 i)) : Submodule (tw.O0 i) (H1 (WKG M)) :=
  selG N.plOm (tw.l i) (L (tw.l i)) (nbt i) Sig M
end Tw
end Br
end Formalism.MainNotions.N


