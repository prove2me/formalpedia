-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:26.539972+00:00
-- url     : https://prove2.me/theorems/83a04506-a276-4197-ac06-483301ff7ff6
-- title:
--   Coord Ideal Is Multi Proj Prime
-- statement:
--   Definitions and structural lemmas for Coord Ideal Is Multi Proj Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CoordIdealIsMultiProjPrime.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
open MvPolynomial
noncomputable section
section Cech
structure CechSystem (ι : Type) (k : Type) [CommRing k] where

  V : Finset ι → Type
  [grp : ∀ I, AddCommGroup (V I)]
  [mod : ∀ I, Module k (V I)]

  res : ∀ {I J : Finset ι}, I ⊆ J → V I →ₗ[k] V J

  piece : ∀ I, Submodule k (V I)

  good : Finset ι → Prop
attribute [instance] CechSystem.grp CechSystem.mod
variable {ι : Type} {k : Type} [CommRing k]
def cechSign [LinearOrder ι] (J : Finset ι) (j : ι) : ℤ := (-1) ^ (J.filter (· < j)).card
open Classical in

def cechD [LinearOrder ι] (C : CechSystem ι k) : (∀ I, C.V I) →ₗ[k] (∀ I, C.V I) :=
  LinearMap.pi fun J => if C.good J then
    ∑ j ∈ J, cechSign J j • ((C.res (Finset.erase_subset j J)).comp (LinearMap.proj (J.erase j)))
  else 0
open Classical in

def cechC (C : CechSystem ι k) (i : ℕ) : Submodule k (∀ I, C.V I) :=
  Submodule.pi Set.univ fun I => if C.good I ∧ I.card = i + 1 then C.piece I else ⊥
def cechZ [LinearOrder ι] (C : CechSystem ι k) (i : ℕ) : Submodule k (∀ I, C.V I) :=
  cechC C i ⊓ LinearMap.ker (cechD C)
def cechB [LinearOrder ι] (C : CechSystem ι k) : ℕ → Submodule k (∀ I, C.V I)
  | 0 => ⊥
  | i + 1 => (cechC C i).map (cechD C)
abbrev cechH [LinearOrder ι] (C : CechSystem ι k) (i : ℕ) : Type :=
  ↥(cechZ C i) ⧸ (cechB C i).comap (cechZ C i).subtype
structure CechHom (C C' : CechSystem ι k) where

  app : ∀ I, C.V I →ₗ[k] C'.V I
  comm : ∀ {I J : Finset ι} (h : I ⊆ J), (C'.res h).comp (app I) = (app J).comp (C.res h)
  piece_le : ∀ I, (C.piece I).map (app I) ≤ C'.piece I
  good_iff : ∀ I, C'.good I ↔ C.good I
variable {C C' : CechSystem ι k}
def CechHom.amb (φ : CechHom C C') : (∀ I, C.V I) →ₗ[k] (∀ I, C'.V I) :=
  LinearMap.pi fun I => (φ.app I).comp (LinearMap.proj I)
theorem CechHom.amb_cechD [LinearOrder ι] (φ : CechHom C C') (v : ∀ I, C.V I) :
    φ.amb (cechD C v) = cechD C' (φ.amb v) := by
  classical
  funext J
  simp only [CechHom.amb, cechD, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  by_cases h : C.good J
  · have h' : C'.good J := (φ.good_iff J).2 h
    simp only [h, h', if_true, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_zsmul,
      LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.pi_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [← LinearMap.comp_apply, ← φ.comm]
    rfl
  · have h' : ¬ C'.good J := fun h' => h ((φ.good_iff J).1 h')
    simp [h, h']
theorem CechHom.amb_mem_cechC (φ : CechHom C C') {i : ℕ} {v : ∀ I, C.V I} (hv : v ∈ cechC C i) :
    φ.amb v ∈ cechC C' i := by
  classical
  simp only [cechC, Submodule.mem_pi, Set.mem_univ, true_implies] at hv ⊢
  intro I
  have hI := hv I
  by_cases h : C.good I ∧ I.card = i + 1
  · have h' : C'.good I ∧ I.card = i + 1 := ⟨(φ.good_iff I).2 h.1, h.2⟩
    simp only [h, h'] at hI ⊢
    exact φ.piece_le I ⟨_, hI, rfl⟩
  · have h' : ¬ (C'.good I ∧ I.card = i + 1) := fun h' => h ⟨(φ.good_iff I).1 h'.1, h'.2⟩
    simp only [h, h', if_false, Submodule.mem_bot] at hI ⊢
    simp [CechHom.amb, hI]
theorem CechHom.amb_mem_cechB [LinearOrder ι] (φ : CechHom C C') {i : ℕ} {v : ∀ I, C.V I} (hv : v ∈ cechB C i) :
    φ.amb v ∈ cechB C' i := by
  cases i with
  | zero =>
    simp only [cechB, Submodule.mem_bot] at hv ⊢
    simp [hv]
  | succ i =>
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨φ.amb w, φ.amb_mem_cechC hw, (φ.amb_cechD w).symm⟩
def CechHom.Zmap [LinearOrder ι] (φ : CechHom C C') (i : ℕ) : cechZ C i →ₗ[k] cechZ C' i :=
  φ.amb.restrict fun v hv => ⟨φ.amb_mem_cechC hv.1, by
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hv ⊢
    rw [← φ.amb_cechD, hv.2, map_zero]⟩
def CechHom.Hmap [LinearOrder ι] (φ : CechHom C C') (i : ℕ) : cechH C i →ₗ[k] cechH C' i :=
  Submodule.mapQ _ _ (φ.Zmap i) fun _ hz => φ.amb_mem_cechB hz
end Cech
section Graded
variable (S : Type) [CommRing S] (N : ℕ)
abbrev Poly : Type := MvPolynomial (Fin (N + 1)) S
def polyPiece (d : ℤ) : Submodule S (Poly S N) :=
  weightedHomogeneousSubmodule S (fun _ => (1 : ℤ)) d
structure GradedMod (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M]
    [IsScalarTower S (Poly S N) M] where

  piece : ℤ → Submodule S M
  internal : DirectSum.IsInternal piece
  smul_mem : ∀ (d c : ℤ) (f : Poly S N), f ∈ polyPiece S N d → ∀ m ∈ piece c, f • m ∈ piece (d + c)
def denoms (I : Finset (Fin (N + 1))) : Submonoid (Poly S N) :=
  Submonoid.closure ((fun i => (X i : Poly S N)) '' (I : Set (Fin (N + 1))))
theorem denoms_mono {I J : Finset (Fin (N + 1))} (h : I ⊆ J) : denoms S N I ≤ denoms S N J :=
  Submonoid.closure_mono (Set.image_mono (by exact_mod_cast h))
def Xprod (I : Finset (Fin (N + 1))) : Poly S N := ∏ i ∈ I, X i
theorem Xprod_mem_denoms (I : Finset (Fin (N + 1))) : Xprod S N I ∈ denoms S N I :=
  Submonoid.prod_mem _ fun i hi => Submonoid.subset_closure ⟨i, hi, rfl⟩
variable (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
abbrev LocM (I : Finset (Fin (N + 1))) : Type := LocalizedModule (denoms S N I) M
example (I : Finset (Fin (N + 1))) : IsScalarTower S (Poly S N) (LocM S N M I) := inferInstance
def locFrac (I : Finset (Fin (N + 1))) (m : M) (n : ℕ) : LocM S N M I :=
  LocalizedModule.mk m ⟨Xprod S N I ^ n, pow_mem (Xprod_mem_denoms S N I) n⟩
def locPiece (G : GradedMod S N M) (I : Finset (Fin (N + 1))) (c : ℤ) : Submodule S (LocM S N M I) :=
  Submodule.span S {y | ∃ (n : ℕ) (m : M), m ∈ G.piece (c + n * I.card) ∧ y = locFrac S N M I m n}
def locRes {I J : Finset (Fin (N + 1))} (h : I ⊆ J) : LocM S N M I →ₗ[S] LocM S N M J :=
  ((LocalizedModule.liftOfLE (denoms S N I) (denoms S N J) (denoms_mono S N h) :
    LocM S N M I →ₗ[Poly S N] LocM S N M J)).restrictScalars S
def gradedSys (G : GradedMod S N M) (c : ℤ) : CechSystem (Fin (N + 1)) S where
  V I := LocM S N M I
  res h := locRes S N M h
  piece I := locPiece S N M G I c
  good I := I.Nonempty
abbrev gradedH (G : GradedMod S N M) (i : ℕ) (c : ℤ) : Type := cechH (gradedSys S N M G c) i
abbrev gradedZ (G : GradedMod S N M) (i : ℕ) (c : ℤ) := cechZ (gradedSys S N M G c) i
open Classical in

def unitCochain (m : M) : ∀ I : Finset (Fin (N + 1)), LocM S N M I :=
  fun I => if I.card = 1 then locFrac S N M I m 0 else 0
variable {M} {M' : Type} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
def IsGradedHom (G : GradedMod S N M) (G' : GradedMod S N M') (f : M →ₗ[Poly S N] M') : Prop :=
  ∀ c, ∀ m ∈ G.piece c, f m ∈ G'.piece c
def locMap (f : M →ₗ[Poly S N] M') (I : Finset (Fin (N + 1))) : LocM S N M I →ₗ[S] LocM S N M' I :=
  ((IsLocalizedModule.map (denoms S N I) (LocalizedModule.mkLinearMap (denoms S N I) M)
    (LocalizedModule.mkLinearMap (denoms S N I) M') f : LocM S N M I →ₗ[Poly S N] LocM S N M' I)).restrictScalars S
theorem locMap_mk (f : M →ₗ[Poly S N] M') (I : Finset (Fin (N + 1))) (m : M) (s : denoms S N I) :
    locMap S N f I (LocalizedModule.mk m s) = LocalizedModule.mk (f m) s := by
  simp only [locMap, LinearMap.restrictScalars_apply]
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']
theorem locMap_locFrac (f : M →ₗ[Poly S N] M') (I : Finset (Fin (N + 1))) (m : M) (n : ℕ) :
    locMap S N f I (locFrac S N M I m n) = locFrac S N M' I (f m) n :=
  locMap_mk S N f I m _
omit [Module S M] [IsScalarTower S (Poly S N) M] in
theorem locRes_mk {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (m : M) (s : denoms S N I) :
    (LocalizedModule.liftOfLE (denoms S N I) (denoms S N J) (denoms_mono S N h)
      (LocalizedModule.mk m s : LocM S N M I)) = LocalizedModule.mk m ⟨(s : Poly S N), denoms_mono S N h s.2⟩ := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk']
  exact IsLocalizedModule.liftOfLE_mk' _ _ _ _ _ m s
theorem locRes_comp_locMap (f : M →ₗ[Poly S N] M') {I J : Finset (Fin (N + 1))} (h : I ⊆ J) :
    (locRes S N M' h).comp (locMap S N f I) = (locMap S N f J).comp (locRes S N M h) := by
  refine LinearMap.ext fun y => ?_
  refine LocalizedModule.induction_on (fun m s => ?_) y
  simp only [LinearMap.comp_apply, locRes, LinearMap.restrictScalars_apply]
  rw [locMap_mk, locRes_mk _ _ h, locRes_mk _ _ h, locMap_mk]
theorem locPiece_map_le {G : GradedMod S N M} {G' : GradedMod S N M'} {f : M →ₗ[Poly S N] M'}
    (hf : IsGradedHom S N G G' f) (I : Finset (Fin (N + 1))) (c : ℤ) :
    (locPiece S N M G I c).map (locMap S N f I) ≤ locPiece S N M' G' I c := by
  rw [locPiece, Submodule.map_span_le]
  rintro _ ⟨n, m, hm, rfl⟩
  rw [locMap_locFrac]
  exact Submodule.subset_span ⟨n, f m, hf _ m hm, rfl⟩
def gradedHom {G : GradedMod S N M} {G' : GradedMod S N M'} {f : M →ₗ[Poly S N] M'}
    (hf : IsGradedHom S N G G' f) (c : ℤ) : CechHom (gradedSys S N M G c) (gradedSys S N M' G' c) where
  app I := locMap S N f I
  comm h := locRes_comp_locMap S N f h
  piece_le I := locPiece_map_le S N hf I c
  good_iff _ := Iff.rfl
def gradedHmap {G : GradedMod S N M} {G' : GradedMod S N M'} {f : M →ₗ[Poly S N] M'}
    (hf : IsGradedHom S N G G' f) (i : ℕ) (c : ℤ) : gradedH S N M G i c →ₗ[S] gradedH S N M' G' i c :=
  (gradedHom S N hf c).Hmap i
def gradedCmap {G : GradedMod S N M} {G' : GradedMod S N M'} {f : M →ₗ[Poly S N] M'}
    (hf : IsGradedHom S N G G' f) (c : ℤ) :
    (∀ I, (gradedSys S N M G c).V I) →ₗ[S] (∀ I, (gradedSys S N M' G' c).V I) :=
  (gradedHom S N hf c).amb
end Graded
section Cl
open ReciprocityTheory.ChartRestriction.G.Geo
variable (S : Type) [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]
abbrev coordRing (x : Fin (N + 1) → Ω) : Subalgebra S (Polynomial Ω) := coneRing S x
def chartRingI (x : Fin (N + 1) → Ω) (I : Finset (Fin (N + 1))) : Subalgebra S Ω :=
  Algebra.adjoin S {y | ∃ i ∈ I, ∃ j, y = x j / x i}
def IsChart (x : Fin (N + 1) → Ω) (I : Finset (Fin (N + 1))) : Prop :=
  I.Nonempty ∧ ∀ i ∈ I, x i ≠ 0
variable (E : Type) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
structure SubFamily (x : Fin (N + 1) → Ω) where

  lat : Fin (N + 1) → AddSubgroup E
  stable : ∀ i, ∀ a ∈ chartRing S x i, ∀ e ∈ lat i, a • e ∈ lat i
  overlap : ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ lat i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ lat j
variable {S E}
def SubFamily.ofBundle {x : Fin (N + 1) → Ω} {r : ℕ} (B : ChartBundle S x r E) : SubFamily S E x :=
  ⟨B.lat, B.stable, B.overlap⟩
def SubFamily.mods {x : Fin (N + 1) → Ω} (F : SubFamily S E x) (i : Fin (N + 1)) : Submodule S E :=
  Submodule.span S (F.lat i : Set E)
variable (S)
def famI (x : Fin (N + 1) → Ω) (F : Fin (N + 1) → Submodule S E) (I : Finset (Fin (N + 1))) :
    Submodule S E :=
  ⨅ i ∈ I, Submodule.span S (Set.image2 (· • ·) (chartRingI S x I : Set Ω) (F i : Set E))
def famSys (x : Fin (N + 1) → Ω) (F : Fin (N + 1) → Submodule S E) : CechSystem (Fin (N + 1)) S where
  V _ := E
  res _ := LinearMap.id
  piece I := famI S x F I
  good I := IsChart x I
abbrev famH (x : Fin (N + 1) → Ω) (F : Fin (N + 1) → Submodule S E) (i : ℕ) : Type :=
  cechH (famSys S x F) i
def secs (x : Fin (N + 1) → Ω) (F : Fin (N + 1) → Submodule S E) : Submodule S E :=
  ⨅ i, ⨅ (_ : x i ≠ 0), F i
def IsGenerated (x : Fin (N + 1) → Ω) (F : Fin (N + 1) → Submodule S E) : Prop :=
  ∀ i, x i ≠ 0 → F i = Submodule.span S (Set.image2 (· • ·) (chartRing S x i : Set Ω) (secs S x F : Set E))
def IsGeneratedBy (x : Fin (N + 1) → Ω) (F : Fin (N + 1) → Submodule S E) {r : ℕ} (η : Fin (r + 1) → E) :
    Prop :=
  (∀ k, η k ∈ secs S x F) ∧
    ∀ i, x i ≠ 0 → F i = Submodule.span S (Set.image2 (· • ·) (chartRing S x i : Set Ω) (Set.range η))
def twistA (x : Fin (N + 1) → Ω) (F : Fin (N + 1) → Submodule S E) (c : ℤ) (i : Fin (N + 1)) :
    Submodule S E :=
  Submodule.span S ((fun e => (x i ^ c) • e) '' (F i : Set E))
def twistQ (F : Fin (N + 1) → Submodule S E) (Q : Fin (N + 1) → Submodule S Ω) (i : Fin (N + 1)) :
    Submodule S E :=
  Submodule.span S (Set.image2 (· • ·) (Q i : Set Ω) (F i : Set E))
variable {S}
abbrev LineBundle (x : Fin (N + 1) → Ω) : Type := ChartBundle S x 1 Ω
def LineBundle.mods {x : Fin (N + 1) → Ω} (Q : LineBundle (S := S) x) (i : Fin (N + 1)) : Submodule S Ω :=
  Submodule.span S (Q.lat i : Set Ω)
variable (S)
abbrev bundleA (x : Fin (N + 1) → Ω) : LineBundle (S := S) x := lineBundle S x 1
def lmul (Q Q' : Fin (N + 1) → Submodule S Ω) (i : Fin (N + 1)) : Submodule S Ω := Q i * Q' i
def lpow (Q : Fin (N + 1) → Submodule S Ω) (b : ℕ) (i : Fin (N + 1)) : Submodule S Ω := Q i ^ b
def sumGBA (x : Fin (N + 1) → Ω) (G B : LineBundle (S := S) x) (b : ℕ) (c : ℤ) :
    Fin (N + 1) → Submodule S Ω :=
  twistA S x (lmul S G.mods (lpow S B.mods b)) c
def secZ (x : Fin (N + 1) → Ω) (d : ℤ) : Submodule S Ω :=
  if 0 ≤ d then sec S x d.toNat else ⊥
def gradedGen {n : ℕ} (x : Fin (N + 1) → Ω) (c : Fin n → ℤ) (e : Fin n → E) (d : ℤ) : Submodule S E :=
  ⨆ k, Submodule.span S (Set.image2 (· • ·) (secZ S x (d - c k) : Set Ω) {e k})
def tildeZero {n : ℕ} (x : Fin (N + 1) → Ω) (c : Fin n → ℤ) (e : Fin n → E) (i : Fin (N + 1)) :
    Submodule S E :=
  Submodule.span S {y | ∃ (m : ℕ) (v : E), v ∈ gradedGen S x c e m ∧ y = (x i ^ m)⁻¹ • v}
def IsExtensionOf {n : ℕ} (x : Fin (N + 1) → Ω) (F : Fin (N + 1) → Submodule S E) (c : Fin n → ℤ)
    (e : Fin n → E) : Prop :=
  (∀ k, e k ∈ secs S x (twistA S x F (c k))) ∧ ∀ i, x i ≠ 0 → F i = tildeZero S x c e i
def SubFamily.IsFinite {x : Fin (N + 1) → Ω} (F : SubFamily S E x) : Prop :=
  ∀ i, x i ≠ 0 → ∃ g : Finset E, F.mods i = Submodule.span S (Set.image2 (· • ·) (chartRing S x i : Set Ω) (g : Set E))
def regOn (x : Fin (N + 1) → Ω) (H : Fin (N + 1) → Submodule S Ω) (m : ℕ) {M : ℕ} (h : Fin (M + 1) → Ω)
    (j : Fin (M + 1)) : Subalgebra S Ω :=
  Algebra.adjoin S {f | ∀ i, x i ≠ 0 → ∃ n : ℕ, f * h j ^ n ∈ (lpow S H m i) ^ n}
structure AmpleData (x : Fin (N + 1) → Ω) (H : Fin (N + 1) → Submodule S Ω) where
  m : ℕ
  m_pos : 0 < m
  M : ℕ
  h : Fin (M + 1) → Ω
  gen : IsGeneratedBy S x (lpow S H m) h
  finite : ∀ j, h j ≠ 0 → ∃ g : Finset Ω,
    (regOn S x H m h j : Set Ω) ⊆ Submodule.span (chartRing S h j) (g : Set Ω)
def dimCl (k : Type) [Field k] [Algebra k Ω] (x : Fin (N + 1) → Ω) : Cardinal :=
  Algebra.trdeg k (IntermediateField.adjoin k {y | ∃ i j, x i ≠ 0 ∧ y = x j / x i})
end Cl
section Filtration
open ReciprocityTheory.ChartRestriction.G.Geo
variable (S : Type) [CommRing S] (N : ℕ)
variable {M : Type} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
def IsGradedSub (G : GradedMod S N M) (L : Submodule (Poly S N) M) : Prop :=
  L.restrictScalars S = ⨆ c, L.restrictScalars S ⊓ G.piece c
structure PrimeFiltration (G : GradedMod S N M) where
  n : ℕ
  step : Fin (n + 1) → Submodule (Poly S N) M
  mono : Monotone step
  step_zero : step 0 = ⊥
  step_last : step (Fin.last n) = ⊤
  graded : ∀ k, IsGradedSub S N G (step k)
  prime : Fin n → Ideal (Poly S N)
  isPrime : ∀ k, (prime k).IsPrime
  homog : ∀ k, IsHomogIdeal S (prime k)
  ann_le : ∀ k, Module.annihilator (Poly S N) M ≤ prime k
  deg : Fin n → ℤ
  gen : Fin n → M
  gen_mem : ∀ k, gen k ∈ G.piece (deg k)
  step_succ : ∀ k : Fin n, step k.succ = step k.castSucc ⊔ Submodule.span (Poly S N) {gen k}
  ann_gen : ∀ (k : Fin n) (f : Poly S N), f • gen k ∈ step k.castSucc ↔ f ∈ prime k
open Classical in

def PrimeFiltration.count {G : GradedMod S N M} (F : PrimeFiltration S N G) (pp : Ideal (Poly S N)) : ℕ :=
  (Finset.univ.filter fun k => F.prime k = pp).card
variable {S N}
variable {Ω : Type} [Field Ω] [Algebra S Ω]
def ptCoord (pp : Ideal (Poly S N)) [pp.IsPrime] : Fin (N + 1) → FractionRing (Poly S N ⧸ pp) :=
  fun k => algebraMap (Poly S N ⧸ pp) _ (Ideal.Quotient.mk pp (X k))
def ResAt (x : Fin (N + 1) → Ω) (pp : Ideal (Poly S N)) [pp.IsPrime] (f : Ω)
    (y : FractionRing (Poly S N ⧸ pp)) : Prop :=
  ∃ (d : ℕ) (a b : Poly S N), a.IsHomogeneous d ∧ b.IsHomogeneous d ∧ b ∉ pp ∧
    f * aeval x b = aeval x a ∧
    y = algebraMap _ _ (Ideal.Quotient.mk pp a) / algebraMap _ _ (Ideal.Quotient.mk pp b)
def IsRestrictionOf (x : Fin (N + 1) → Ω) (pp : Ideal (Poly S N)) [pp.IsPrime] (Q : LineBundle (S := S) x)
    (QW : Fin (N + 1) → Submodule S (FractionRing (Poly S N ⧸ pp))) : Prop :=
  ∃ g : Ω, g ≠ 0 ∧ ∀ i, (X i : Poly S N) ∉ pp →
    (∀ q ∈ Q.lat i, ∃ y, ResAt x pp (q / g) y) ∧ (∃ q ∈ Q.lat i, ∃ y, ResAt x pp (g / q) y) ∧
    QW i = Submodule.span S {y | ∃ q ∈ Q.lat i, ResAt x pp (q / g) y}
variable (S)
def LSp (_S : Type) (_x : Fin (N + 1) → Ω) : Type := LaurentPolynomial Ω
instance (x : Fin (N + 1) → Ω) : CommRing (LSp S x) := inferInstanceAs (CommRing (LaurentPolynomial Ω))
instance (x : Fin (N + 1) → Ω) : Algebra S (LSp S x) := inferInstanceAs (Algebra S (LaurentPolynomial Ω))
def laurentMap (x : Fin (N + 1) → Ω) : Poly S N →ₐ[S] LSp S x :=
  aeval fun k => (LaurentPolynomial.C (x k) * LaurentPolynomial.T 1 : LaurentPolynomial Ω)
instance (x : Fin (N + 1) → Ω) : Algebra (Poly S N) (LSp S x) := (laurentMap S x).toRingHom.toAlgebra
instance (x : Fin (N + 1) → Ω) : IsScalarTower S (Poly S N) (LSp S x) :=
  IsScalarTower.of_algebraMap_eq fun s => ((laurentMap S x).commutes s).symm
def twLaurent (x : Fin (N + 1) → Ω) (Q : Fin (N + 1) → Submodule S Ω) (I : Finset (Fin (N + 1))) :
    Submodule (Poly S N) (LSp S x) :=
  Submodule.span (Poly S N) {y | ∃ I' ⊆ I, I'.Nonempty ∧ ∃ (d : ℤ) (q : Ω),
    q ∈ famI S x (twistA S x Q d) I' ∧ y = (LaurentPolynomial.C q * LaurentPolynomial.T d : LaurentPolynomial Ω)}
theorem twLaurent_mono (x : Fin (N + 1) → Ω) (Q : Fin (N + 1) → Submodule S Ω) {I J : Finset (Fin (N + 1))}
    (h : I ⊆ J) : twLaurent S x Q I ≤ twLaurent S x Q J :=
  Submodule.span_mono fun _ ⟨I', hI', hne, d, q, hq, e⟩ => ⟨I', hI'.trans h, hne, d, q, hq, e⟩
def quotTwistSys (x : Fin (N + 1) → Ω) (pp : Ideal (Poly S N)) (Q : Fin (N + 1) → Submodule S Ω) (c : ℤ) :
    CechSystem (Fin (N + 1)) S where
  V I := LSp S x ⧸ (pp • twLaurent S x Q I)
  res h := (Submodule.mapQ _ _ LinearMap.id (by
    rw [Submodule.comap_id]
    exact Submodule.smul_mono le_rfl (twLaurent_mono S x Q h))).restrictScalars S
  piece I := Submodule.span S {y | ∃ q ∈ famI S x (twistA S x Q c) I,
    y = Submodule.Quotient.mk (show LSp S x from LaurentPolynomial.C q * LaurentPolynomial.T c)}
  good I := IsChart x I
end Filtration
section Comparison₂
open ReciprocityTheory.ChartRestriction.G.Geo
variable {S : Type} [CommRing S] {σ : Type} {Ω : Type} [Field Ω] [Algebra S Ω]
end Comparison₂
section Inhabitants
open ReciprocityTheory.ChartRestriction.G.Geo
variable (S : Type) [CommRing S] (N : ℕ)
def polyGraded : GradedMod S N (Poly S N) where
  piece := polyPiece S N
  internal := by
    let _ := MvPolynomial.weightedDecomposition S (fun _ : Fin (N + 1) => (1 : ℤ))
    exact DirectSum.Decomposition.isInternal (fun d => weightedHomogeneousSubmodule S (fun _ : Fin (N + 1) => (1 : ℤ)) d)
  smul_mem d c f hf m hm := by
    simp only [polyPiece, mem_weightedHomogeneousSubmodule, smul_eq_mul] at hf hm ⊢
    exact hf.mul hm
def punitGraded : GradedMod S N PUnit where
  piece _ := ⊥
  internal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    exact ⟨fun _ => disjoint_bot_left, Subsingleton.elim _ _⟩
  smul_mem _ _ _ _ m _ := by simp [Subsingleton.elim m 0]
theorem isGradedHom_id {M : Type} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
    [IsScalarTower S (Poly S N) M] (G : GradedMod S N M) : IsGradedHom S N G G LinearMap.id :=
  fun _ _ hm => hm
def polySys : CechSystem (Fin (N + 1)) S := gradedSys S N (Poly S N) (polyGraded S N) 0
def polySysId : CechHom (polySys S N) (polySys S N) := gradedHom S N (isGradedHom_id S N (polyGraded S N)) 0
variable {S} {Ω : Type} [Field Ω] [Algebra S Ω]
theorem bundleA_isGeneratedBy (x : Fin (N + 1) → Ω) :
    IsGeneratedBy S x (bundleA S x).mods x := by
  refine ⟨fun k => ?_, fun i hi => ?_⟩
  · simp only [secs, Submodule.mem_iInf]
    intro i hi
    refine Submodule.subset_span ?_
    refine (mem_lineLat x 1 i _).2 ⟨x k / x i, div_mem_chartRing x i k, ?_⟩
    field_simp
  · apply le_antisymm
    · rw [LineBundle.mods, Submodule.span_le]
      intro e he
      obtain ⟨a, ha, rfl⟩ := (mem_lineLat x 1 i e).1 he
      exact Submodule.subset_span ⟨a, ha, x i, ⟨i, rfl⟩, by simp⟩
    · rw [Submodule.span_le]
      rintro _ ⟨a, ha, _, ⟨j, rfl⟩, rfl⟩
      refine Submodule.subset_span ((mem_lineLat x 1 i _).2 ⟨a * (x j / x i), mul_mem ha (div_mem_chartRing x i j), ?_⟩)
      simp only [smul_eq_mul]
      field_simp
end Inhabitants
section Inhabitants2
open ReciprocityTheory.ChartRestriction.G.Geo
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]
theorem bundleA_pow_le (x : Fin (N + 1) → Ω) (j : Fin (N + 1)) (n : ℕ) :
    (bundleA S x).mods j ^ n ≤
      (Subalgebra.toSubmodule (chartRing S x j)).map (LinearMap.mulRight S (x j ^ n)) := by
  induction n with
  | zero =>
    rw [pow_zero, Submodule.one_le]
    exact ⟨1, (Subalgebra.mem_toSubmodule _).2 (one_mem _), by simp⟩
  | succ n ih =>
    rw [pow_succ, Submodule.mul_le]
    intro m hm e he
    obtain ⟨a, ha, rfl⟩ := ih hm
    have hle : (bundleA S x).mods j ≤
        ((Subalgebra.toSubmodule (chartRing S x j)).map (LinearMap.mulRight S (x j ^ (n + 1)))).comap
          (LinearMap.mulLeft S (x j ^ n * a)) := by
      rw [LineBundle.mods, Submodule.span_le]
      intro e he
      obtain ⟨b, hb, rfl⟩ := (mem_lineLat x 1 j e).1 he
      refine ⟨a * b, (Subalgebra.mem_toSubmodule _).2 (mul_mem ((Subalgebra.mem_toSubmodule _).1 ha) hb), ?_⟩
      simp only [LinearMap.mulRight_apply, LinearMap.mulLeft_apply]
      ring
    obtain ⟨y, hy, hye⟩ := hle he
    refine ⟨y, hy, ?_⟩
    simp only [LinearMap.mulRight_apply, LinearMap.mulLeft_apply] at hye ⊢
    rw [hye]
    ring
def ampleA (x : Fin (N + 1) → Ω) : AmpleData S x (bundleA S x).mods where
  m := 1
  m_pos := one_pos
  M := N
  h := x
  gen := by
    have h1 : lpow S (bundleA S x).mods 1 = (bundleA S x).mods := funext fun i => pow_one _
    rw [h1]
    exact bundleA_isGeneratedBy N x
  finite j hj := by
    classical
    refine ⟨{1}, ?_⟩
    have hle : regOn S x (bundleA S x).mods 1 x j ≤ chartRing S x j := by
      rw [regOn, Algebra.adjoin_le_iff]
      intro f hf
      obtain ⟨n, hn⟩ := hf j hj
      have h1 : lpow S (bundleA S x).mods 1 j = (bundleA S x).mods j := pow_one _
      rw [h1] at hn
      obtain ⟨a, ha, hfa⟩ := bundleA_pow_le x j n hn
      simp only [LinearMap.mulRight_apply] at hfa
      have : a = f := mul_right_cancel₀ (pow_ne_zero n hj) hfa
      exact this ▸ ((Subalgebra.mem_toSubmodule _).1 ha)
    intro f hf
    have hf' : f ∈ chartRing S x j := hle hf
    rw [Finset.coe_singleton]
    exact Submodule.mem_span_singleton.2 ⟨⟨f, hf'⟩, by simp [Subalgebra.smul_def]⟩
variable (S N)
def polyFiltration [IsDomain S] : PrimeFiltration S N (polyGraded S N) where
  n := 1
  step := ![⊥, ⊤]
  mono := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  step_zero := rfl
  step_last := rfl
  graded k := by
    fin_cases k
    · simp [IsGradedSub]
    · simp only [IsGradedSub]
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Submodule.restrictScalars_top,
        top_inf_eq]
      exact ((polyGraded S N).internal.submodule_iSup_eq_top).symm
  prime _ := ⊥
  isPrime _ := Ideal.isPrime_bot
  homog _ := by
    intro f hf d
    rw [Ideal.mem_bot] at hf ⊢
    simp [hf]
  ann_le _ := by
    intro f hf
    rw [Module.mem_annihilator] at hf
    have := hf 1
    rw [smul_eq_mul, mul_one] at this
    exact (Ideal.mem_bot).2 this
  deg _ := 0
  gen _ := 1
  gen_mem _ := by
    simp only [polyGraded, polyPiece, mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_one S _
  step_succ k := by
    fin_cases k
    simp only [Fin.zero_eta, Fin.succ_zero_eq_one, Fin.castSucc_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, bot_sup_eq]
    exact (Ideal.span_singleton_one).symm
  ann_gen k f := by
    fin_cases k
    simp [smul_eq_mul]
def lineX (k : Type) [Field k] : Fin (1 + 1) → RatFunc k := ![1, RatFunc.X]
def lineFam (k : Type) [Field k] : SubFamily k (RatFunc k) (lineX k) :=
  SubFamily.ofBundle (bundleA k (lineX k))
end Inhabitants2
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman


