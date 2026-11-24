-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:56.275139+00:00
-- url     : https://prove2.me/theorems/611bc3b0-a7bb-425d-adc9-8fca1be78154
-- title:
--   Objects
-- statement:
--   Definitions and structural lemmas for Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
section Poly
variable (S : Type u) [CommRing S] (N : ℕ)
abbrev Poly : Type u := MvPolynomial (Fin (N + 1)) S
variable {S N}
def monos (I : Finset (Fin (N + 1))) : Submonoid (Poly S N) :=
  Submonoid.closure ((fun i => (X i : Poly S N)) '' (I : Set (Fin (N + 1))))
theorem monos_mono {I J : Finset (Fin (N + 1))} (h : I ⊆ J) : monos (S := S) I ≤ monos J :=
  Submonoid.closure_mono (Set.image_mono (by exact_mod_cast h))
theorem X_mem_monos {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) :
    (X i : Poly S N) ∈ monos I :=
  Submonoid.subset_closure ⟨i, by exact_mod_cast hi, rfl⟩
end Poly
section Graded
variable (S : Type u) [CommRing S] (N : ℕ)
variable (M : Type v) [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
structure GradedPMod where

  piece : ℤ → Submodule S M

  isInternal : DirectSum.IsInternal piece

  smul_mem : ∀ (d : ℕ) (c : ℤ) (p : Poly S N) (m : M), p.IsHomogeneous d → m ∈ piece c →
    p • m ∈ piece (c + d)
def LocMod (I : Finset (Fin (N + 1))) : Type (max u v) := LocalizedModule (monos (S := S) I) M
variable {S N M}
instance (I : Finset (Fin (N + 1))) : AddCommGroup (LocMod S N M I) :=
  inferInstanceAs (AddCommGroup (LocalizedModule _ M))
instance (I : Finset (Fin (N + 1))) : Module (Poly S N) (LocMod S N M I) :=
  inferInstanceAs (Module (Poly S N) (LocalizedModule _ M))
instance (I : Finset (Fin (N + 1))) : Module S (LocMod S N M I) :=
  Module.compHom _ (algebraMap S (Poly S N))
instance (I : Finset (Fin (N + 1))) : IsScalarTower S (Poly S N) (LocMod S N M I) where
  smul_assoc s p m := by
    change (s • p) • m = algebraMap S (Poly S N) s • (p • m)
    rw [Algebra.smul_def, mul_smul]
def locRes {I J : Finset (Fin (N + 1))} (h : I ⊆ J) : LocMod S N M I →ₗ[Poly S N] LocMod S N M J :=
  LocalizedModule.liftOfLE (monos I) (monos J) (monos_mono h)
theorem locRes_mk {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (m : M) (s : monos (S := S) I) :
    locRes (M := M) h (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M) =
      (LocalizedModule.mk m ⟨(s : Poly S N), monos_mono h s.2⟩ : LocalizedModule (monos J) M) := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk']
  exact IsLocalizedModule.liftOfLE_mk' (monos (S := S) I) (monos J) (monos_mono h)
    (LocalizedModule.mkLinearMap (monos (S := S) I) M) (LocalizedModule.mkLinearMap (monos J) M) m s
end Graded
abbrev Cell {n : ℕ} (U : Finset (Fin n)) : Type := {I : Finset (Fin n) // I.Nonempty ∧ I ⊆ U}
namespace Cech
variable {n : ℕ} {U : Finset (Fin n)}
abbrev Idx (U : Finset (Fin n)) (i : ℕ) : Type := {I : Cell U // I.1.card = i + 1}
def face {i : ℕ} (J : Idx U (i + 1)) (j : J.1.1) : Idx U i :=
  ⟨⟨J.1.1.erase j, by
      rw [← Finset.card_pos, Finset.card_erase_of_mem j.2, J.2]; omega,
    (Finset.erase_subset _ _).trans J.1.2.2⟩, by
    change (J.1.1.erase j).card = i + 1
    rw [Finset.card_erase_of_mem j.2, J.2]; rfl⟩
theorem face_subset {i : ℕ} (J : Idx U (i + 1)) (j : J.1.1) : (face J j).1.1 ⊆ J.1.1 :=
  Finset.erase_subset _ _
def sgn (J : Finset (Fin n)) (j : Fin n) : ℤ := (-1) ^ (J.filter (· < j)).card
variable {R : Type u} [CommRing R] (G : Cell U → Type v) [∀ I, AddCommGroup (G I)]
  [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)
abbrev Cochain (i : ℕ) : Type v := ∀ I : Idx U i, G I.1
instance (i : ℕ) : AddCommGroup (Cochain G i) := inferInstanceAs (AddCommGroup (∀ I : Idx U i, G I.1))
instance (i : ℕ) : Module R (Cochain G i) := inferInstanceAs (Module R (∀ I : Idx U i, G I.1))
def d (i : ℕ) : Cochain G i →ₗ[R] Cochain G (i + 1) :=
  LinearMap.pi fun J : Idx U (i + 1) => ∑ j : J.1.1, sgn J.1.1 j •
    ((ρ (face J j).1 J.1 (face_subset J j)).comp
      (LinearMap.proj (R := R) (φ := fun I : Idx U i => G I.1) (face J j)))
def bdry : (i : ℕ) → Submodule R (Cochain G i)
  | 0 => ⊥
  | i + 1 => LinearMap.range (d G ρ i)
def H (i : ℕ) : Type v :=
  LinearMap.ker (d G ρ i) ⧸ (bdry G ρ i).comap (LinearMap.ker (d G ρ i)).subtype
instance (i : ℕ) : AddCommGroup (H G ρ i) := Submodule.Quotient.addCommGroup _
instance (i : ℕ) : Module R (H G ρ i) := Submodule.Quotient.module _
section Deg
variable {R' : Type*} [CommRing R'] [∀ I, Module R' (G I)] (deg : ∀ I, Submodule R' (G I))
  (ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R'] G J)
def Cdeg (i : ℕ) : Submodule R' (Cochain G i) := Submodule.pi Set.univ fun I : Idx U i => deg I.1
def cocyDeg (i : ℕ) : Submodule R' (Cochain G i) := LinearMap.ker (d G ρ' i) ⊓ Cdeg G deg i
def bdryDeg : (i : ℕ) → Submodule R' (Cochain G i)
  | 0 => ⊥
  | i + 1 => (Cdeg G deg i).map (d G ρ' i)
def Hdeg (i : ℕ) : Type v :=
  cocyDeg G deg ρ' i ⧸ (bdryDeg G deg ρ' i).comap (cocyDeg G deg ρ' i).subtype
instance (i : ℕ) : AddCommGroup (Hdeg G deg ρ' i) := Submodule.Quotient.addCommGroup _
instance (i : ℕ) : Module R' (Hdeg G deg ρ' i) := Submodule.Quotient.module _
end Deg
end Cech
namespace Cech
variable {n : ℕ} {U : Finset (Fin n)}
theorem sum_sgn_of_card_two {J : Finset (Fin n)} (hJ : J.card = 2) : ∑ j ∈ J, sgn J j = 0 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hJ
  rw [Finset.sum_pair hab]
  rcases hab.lt_or_gt with h | h
  · have h1 : ({a, b} : Finset (Fin n)).filter (· < a) = ∅ := by
      ext z; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl) <;> omega
    have h2 : ({a, b} : Finset (Fin n)).filter (· < b) = {a} := by
      ext z; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩ <;> [rfl; omega]
      · rintro rfl; exact ⟨Or.inl rfl, h⟩
    simp [sgn, h1, h2]
  · have h1 : ({a, b} : Finset (Fin n)).filter (· < b) = ∅ := by
      ext z; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl) <;> omega
    have h2 : ({a, b} : Finset (Fin n)).filter (· < a) = {b} := by
      ext z; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩ <;> [omega; rfl]
      · rintro rfl; exact ⟨Or.inr rfl, h⟩
    simp [sgn, h1, h2]
variable {R : Type u} [CommRing R] {G : Cell U → Type v} [∀ I, AddCommGroup (G I)]
  [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
theorem d_apply (i : ℕ) (s : Cochain G i) (J : Idx U (i + 1)) :
    d G ρ i s J = ∑ j : J.1.1, sgn J.1.1 j • ρ (face J j).1 J.1 (face_subset J j) (s (face J j)) := by
  change (∑ j : J.1.1, sgn J.1.1 j • ((ρ (face J j).1 J.1 (face_subset J j)).comp
      (LinearMap.proj (R := R) (φ := fun I : Idx U i => G I.1) (face J j)))) s = _
  rw [LinearMap.sum_apply]
  rfl
theorem d_zero_of_compat (v : ∀ I, G I) (hv : ∀ I J h, ρ I J h (v I) = v J) :
    d G ρ 0 (fun I => v I.1) = 0 := by
  funext J
  have key : ∀ j : J.1.1, ρ (face J j).1 J.1 (face_subset J j) (v (face J j).1) = v J.1 :=
    fun j => hv _ _ _
  rw [d_apply]
  simp only [key]
  rw [← Finset.sum_smul, Finset.sum_coe_sort J.1.1 (fun j => sgn J.1.1 j), sum_sgn_of_card_two J.2,
    zero_smul]
  rfl
section Map
variable {G' : Cell U → Type w} [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}
def mapC (φ : ∀ I, G I →ₗ[R] G' I) (i : ℕ) : Cochain G i →ₗ[R] Cochain G' i :=
  LinearMap.pi fun I : Idx U i => (φ I.1).comp (LinearMap.proj (R := R) (φ := fun I : Idx U i => G I.1) I)
theorem mapC_d (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m))
    (i : ℕ) (s : Cochain G i) : mapC φ (i + 1) (d G ρ i s) = d G' ρ' i (mapC φ i s) := by
  funext J
  rw [d_apply]
  change φ J.1 (d G ρ i s J) = _
  rw [d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, hφ]
  rfl
variable (deg : ∀ I, Submodule R (G I)) (deg' : ∀ I, Submodule R (G' I))
def mapHdeg (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m))
    (hdeg : ∀ I m, m ∈ deg I → φ I m ∈ deg' I) (i : ℕ) :
    Hdeg G deg ρ i →ₗ[R] Hdeg G' deg' ρ' i :=
  Submodule.mapQ _ _ ((mapC φ i).restrict (p := cocyDeg G deg ρ i) (q := cocyDeg G' deg' ρ' i)
      (fun s hs => by
        refine ⟨?_, fun I _ => hdeg I.1 _ (hs.2 I (Set.mem_univ _))⟩
        change d G' ρ' i (mapC φ i s) = 0
        rw [← mapC_d φ hφ, show d G ρ i s = 0 from hs.1, map_zero]))
    (by
      intro s hs
      cases i with
      | zero =>
        change (s : Cochain G 0) ∈ (⊥ : Submodule R _) at hs
        rw [Submodule.mem_bot] at hs
        change (mapC φ 0 s : Cochain G' 0) ∈ (⊥ : Submodule R _)
        rw [hs, map_zero]; exact Submodule.zero_mem _
      | succ i =>
        obtain ⟨t, ht, hts⟩ := hs
        refine ⟨mapC φ i t, fun I _ => hdeg I.1 _ (ht I (Set.mem_univ _)), ?_⟩
        change d G' ρ' i (mapC φ i t) = mapC φ (i + 1) s
        rw [← mapC_d φ hφ, hts]
        rfl)
end Map
end Cech
section GradedCech
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
abbrev StdCell (N : ℕ) : Type := Cell (Finset.univ : Finset (Fin (N + 1)))
variable (S N M) in

abbrev locSys : StdCell N → Type (max u v) := fun I => LocMod S N M I.1
def locResS (I J : StdCell N) (h : I.1 ⊆ J.1) : LocMod S N M I.1 →ₗ[S] LocMod S N M J.1 :=
  (locRes (M := M) h).restrictScalars S
def degLoc (𝓜 : GradedPMod S N M) (c : ℤ) (I : StdCell N) : Submodule S (LocMod S N M I.1) :=
  Submodule.span S {z | ∃ (m : M) (s : monos (S := S) I.1) (a : ℤ) (e : ℕ), m ∈ 𝓜.piece a ∧
    (s : Poly S N).IsHomogeneous e ∧ a - e = c ∧
    z = (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) M)}
def cohom (𝓜 : GradedPMod S N M) (i : ℕ) (c : ℤ) : Type (max u v) :=
  Cech.Hdeg (locSys S N M) (degLoc 𝓜 c) locResS i
instance (𝓜 : GradedPMod S N M) (i : ℕ) (c : ℤ) : AddCommGroup (cohom 𝓜 i c) :=
  inferInstanceAs (AddCommGroup (Cech.Hdeg _ _ _ _))
instance (𝓜 : GradedPMod S N M) (i : ℕ) (c : ℤ) : Module S (cohom 𝓜 i c) :=
  inferInstanceAs (Module S (Cech.Hdeg _ _ _ _))
variable (M) in

def locMk (I : Finset (Fin (N + 1))) : M →ₗ[Poly S N] LocMod S N M I :=
  LocalizedModule.mkLinearMap (monos (S := S) I) M
def constCochain : M →ₗ[S] Cech.Cochain (locSys S N M) 0 :=
  LinearMap.pi fun I => (locMk M I.1.1).restrictScalars S
theorem constCochain_mem (𝓜 : GradedPMod S N M) (c : ℤ) (m : M) (hm : m ∈ 𝓜.piece c) :
    constCochain m ∈ Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0 := by
  refine ⟨?_, fun I _ => Submodule.subset_span ⟨m, 1, c, 0, hm, isHomogeneous_one _ _, by simp, by rfl⟩⟩
  change Cech.d _ locResS 0 (fun I => (LocalizedModule.mk m 1 : LocalizedModule _ M)) = 0
  refine Cech.d_zero_of_compat (G := locSys S N M)
    (v := fun I => (LocalizedModule.mk m 1 : LocalizedModule (monos (S := S) I.1) M)) ?_
  intro I J h
  change locRes h _ = _
  rw [locRes_mk]; rfl
def toH0 (𝓜 : GradedPMod S N M) (c : ℤ) : 𝓜.piece c →ₗ[S] cohom 𝓜 0 c :=
  (Submodule.mkQ _).comp
    ((constCochain.comp (𝓜.piece c).subtype).codRestrict _ fun m => constCochain_mem 𝓜 c m m.2)
def dP : Cech.Cochain (locSys S N M) 0 →ₗ[Poly S N] Cech.Cochain (locSys S N M) 1 :=
  Cech.d (locSys S N M) (fun _ _ h => locRes h) 0
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
structure GradedHom (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S N M') where

  toLin : M →ₗ[Poly S N] M'

  map_piece : ∀ (c : ℤ) (m : M), m ∈ 𝓜.piece c → toLin m ∈ 𝓜'.piece c
def locMap (f : M →ₗ[Poly S N] M') (I : Finset (Fin (N + 1))) :
    LocMod S N M I →ₗ[Poly S N] LocMod S N M' I :=
  IsLocalizedModule.map (monos I) (LocalizedModule.mkLinearMap (monos (S := S) I) M)
    (LocalizedModule.mkLinearMap (monos (S := S) I) M') f
theorem locMap_mk (f : M →ₗ[Poly S N] M') (I : Finset (Fin (N + 1))) (m : M) (s : monos (S := S) I) :
    locMap f I (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M) =
      (LocalizedModule.mk (f m) s : LocalizedModule (monos (S := S) I) M') :=
  IsLocalizedModule.map_LocalizedModules _ _ _ _
def cohomMap {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : GradedHom 𝓜 𝓜') (i : ℕ)
    (c : ℤ) : cohom 𝓜 i c →ₗ[S] cohom 𝓜' i c :=
  Cech.mapHdeg (degLoc 𝓜 c) (degLoc 𝓜' c) (fun I => (locMap f.toLin I.1).restrictScalars S)
    (fun I J h x => by
      induction x using LocalizedModule.induction_on with
      | h m s =>
        change locMap f.toLin J.1 (locRes h _) = locRes h (locMap f.toLin I.1 _)
        rw [locRes_mk, locMap_mk, locMap_mk, locRes_mk])
    (fun I x hx => by
      refine Submodule.span_induction (p := fun x _ => (locMap f.toLin I.1).restrictScalars S x ∈
        degLoc 𝓜' c I) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨m, s, a, e, hm, hs, hae, rfl⟩
        refine Submodule.subset_span ⟨f.toLin m, s, a, e, f.map_piece a m hm, hs, hae, ?_⟩
        exact locMap_mk f.toLin I.1 m s
      · simp
      · intro x y _ _ hx hy; simpa using add_mem hx hy
      · intro r x _ hx; simpa using Submodule.smul_mem _ r hx) i
end GradedCech
section Cone
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω]
def coneGen {σ : Type*} (y : σ → Ω) : MvPolynomial σ S →ₐ[S] Polynomial Ω :=
  aeval fun v => Polynomial.C (y v) * Polynomial.X
variable {N : ℕ} (x : Fin (N + 1) → Ω)
def cone : Poly S N →ₐ[S] Polynomial Ω := ReciprocityTheory.ChartRestriction.G.Geo.coneMap S x
def coordRing : Subalgebra S (Polynomial Ω) := ReciprocityTheory.ChartRestriction.G.Geo.coneRing S x
def primeOf : Ideal (Poly S N) := ReciprocityTheory.ChartRestriction.G.Geo.coordIdeal S x
theorem primeOf_eq : primeOf (S := S) x = RingHom.ker (cone (S := S) x) := rfl
instance : (primeOf (S := S) x).IsPrime := by rw [primeOf_eq]; exact RingHom.ker_isPrime _
open NumbersDVR in

def oneBlock : MRing (fun _ : Unit => Fin (N + 1)) S →ₐ[S] Poly S N := rename fun v => v.2
def primeOfOne : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) S) :=
  (primeOf (S := S) x).comap (oneBlock (S := S) (N := N))
end Cone
section Charts
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω)
def support : Finset (Fin (N + 1)) := by
  classical exact Finset.univ.filter fun i => x i ≠ 0
theorem mem_support {i : Fin (N + 1)} : i ∈ support x ↔ x i ≠ 0 := by
  classical
  simp [support]
abbrev Chart : Type := Cell (support x)
variable {x}
theorem eval_ne_zero_of_mem_monos (I : Chart x) {s : Poly S N} (hs : s ∈ monos I.1) :
    aeval x s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [aeval_X]
    exact (mem_support x).mp (I.2.2 hi)
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_ne_zero ha hb
variable (S x) in

def chartRing (I : Chart x) : Subalgebra S Ω where
  carrier := {a | ∃ (f s : Poly S N) (e : ℕ), s ∈ monos I.1 ∧ f.IsHomogeneous e ∧
    s.IsHomogeneous e ∧ a = aeval x f / aeval x s}
  mul_mem' := by
    rintro a b ⟨f, s, e, hs, hf, hse, rfl⟩ ⟨f', s', e', hs', hf', hse', rfl⟩
    exact ⟨f * f', s * s', e + e', mul_mem hs hs', hf.mul hf', hse.mul hse', by
      rw [map_mul, map_mul, div_mul_div_comm]⟩
  one_mem' := ⟨1, 1, 0, one_mem _, isHomogeneous_one _ _, isHomogeneous_one _ _, by simp⟩
  add_mem' := by
    rintro a b ⟨f, s, e, hs, hf, hse, rfl⟩ ⟨f', s', e', hs', hf', hse', rfl⟩
    refine ⟨f * s' + s * f', s * s', e + e', mul_mem hs hs', (hf.mul hse').add (hse.mul hf'),
      hse.mul hse', ?_⟩
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I hs) (eval_ne_zero_of_mem_monos I hs')]
    simp only [map_add, map_mul]
  zero_mem' := ⟨0, 1, 0, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩
  algebraMap_mem' r := ⟨C r, 1, 0, one_mem _, isHomogeneous_C _ _, isHomogeneous_one _ _, by
    simp [aeval_C]⟩
variable (S x) in

def twistMod (c : ℤ) (I : Chart x) : Submodule (chartRing S x I) Ω :=
  Submodule.span _ {a | ∃ (f s : Poly S N) (e e' : ℕ), s ∈ monos I.1 ∧ f.IsHomogeneous e' ∧
    s.IsHomogeneous e ∧ (e' : ℤ) = e + c ∧ a = aeval x f / aeval x s}
end Charts
section Dim
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
def funField (x : Fin (N + 1) → Ω) : IntermediateField k Ω :=
  IntermediateField.adjoin k {a | ∃ i j, x i ≠ 0 ∧ a = x j / x i}
variable (k) in

def dimCl (x : Fin (N + 1) → Ω) : Cardinal := Algebra.trdeg k (funField (k := k) x)
end Dim
section Families
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
theorem chartRing_mono {I J : Chart x} (h : I.1 ⊆ J.1) : chartRing S x I ≤ chartRing S x J :=
  fun _ ⟨f, s, e, hs, hf, hse, ha⟩ => ⟨f, s, e, monos_mono h hs, hf, hse, ha⟩
def chartIncl {I J : Chart x} (h : I.1 ⊆ J.1) : chartRing S x I →ₐ[S] chartRing S x J :=
  Subalgebra.inclusion (chartRing_mono h)
variable (S x) in

structure Family where

  F : Chart x → Type v
  [grp : ∀ I, AddCommGroup (F I)]
  [modA : ∀ I, Module (chartRing S x I) (F I)]
  [modS : ∀ I, Module S (F I)]
  [tower : ∀ I, IsScalarTower S (chartRing S x I) (F I)]

  res : ∀ I J : Chart x, I.1 ⊆ J.1 → F I →ₗ[S] F J
  res_smul : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (a : chartRing S x I) (m : F I),
    res I J h (a • m) = chartIncl h a • res I J h m
  res_self : ∀ (I : Chart x) (m : F I), res I I subset_rfl m = m
  res_comp : ∀ (I J K : Chart x) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : F I),
    res J K h' (res I J h m) = res I K (h.trans h') m

  exists_smul_eq_res : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (y : F J), ∃ (a : chartRing S x I)
    (m : F I), IsUnit (chartIncl h a) ∧ chartIncl h a • y = res I J h m

  exists_smul_eq_zero : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (m : F I), res I J h m = 0 →
    ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ a • m = 0
attribute [instance] Family.grp Family.modA Family.modS Family.tower
def Family.H (F : Family.{u, v, w} S x) (i : ℕ) : Type v := Cech.H F.F F.res i
instance (F : Family.{u, v, w} S x) (i : ℕ) : AddCommGroup (F.H i) :=
  inferInstanceAs (AddCommGroup (Cech.H _ _ _))
instance (F : Family.{u, v, w} S x) (i : ℕ) : Module S (F.H i) :=
  inferInstanceAs (Module S (Cech.H _ _ _))
variable (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
variable (S x) in

structure SubSystem where

  sub : ∀ I : Chart x, Submodule (chartRing S x I) E
  mono : ∀ (I J : Chart x), I.1 ⊆ J.1 → ∀ y, y ∈ sub I → y ∈ sub J
namespace SubSystem
variable {E}
def res (F : SubSystem S x E) (I J : Chart x) (h : I.1 ⊆ J.1) : F.sub I →ₗ[S] F.sub J where
  toFun y := ⟨y, F.mono I J h y y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def H (F : SubSystem S x E) (i : ℕ) : Type v := Cech.H (fun I => F.sub I) F.res i
instance (F : SubSystem S x E) (i : ℕ) : AddCommGroup (F.H i) :=
  inferInstanceAs (AddCommGroup (Cech.H _ _ _))
instance (F : SubSystem S x E) (i : ℕ) : Module S (F.H i) :=
  inferInstanceAs (Module S (Cech.H _ _ _))
def secs (F : SubSystem S x E) : Submodule S E := ⨅ I, (F.sub I).restrictScalars S
def Generated (F : SubSystem S x E) : Prop :=
  ∀ I, Submodule.span (chartRing S x I) (F.secs : Set E) = F.sub I
def twist (F : SubSystem S x E) (Q : SubSystem S x Ω) : SubSystem S x E where
  sub I := Submodule.span _ {z | ∃ q ∈ Q.sub I, ∃ y ∈ F.sub I, z = q • y}
  mono I J h z hz := by
    refine Submodule.span_induction (p := fun z _ => z ∈ Submodule.span (chartRing S x J)
      {z | ∃ q ∈ Q.sub J, ∃ y ∈ F.sub J, z = q • y}) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, y, hy, rfl⟩
      exact Submodule.subset_span ⟨q, Q.mono I J h q hq, y, F.mono I J h y hy, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz
      exact Submodule.smul_mem _ (chartIncl h a) hz
end SubSystem
variable (S x) in

def twistSys (c : ℤ) : SubSystem S x Ω where
  sub I := twistMod S x c I
  mono I J h z hz := by
    refine Submodule.span_induction (p := fun z _ => z ∈ twistMod S x c J) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
      exact Submodule.subset_span ⟨f, s, e, e', monos_mono h hs, hf, hse, hc, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz
      exact Submodule.smul_mem _ (chartIncl h a) hz
def SubSystem.pow (Q : SubSystem S x Ω) : ℕ → SubSystem S x Ω
  | 0 => twistSys S x 0
  | n + 1 => (Q.pow n).twist Q
variable (S x) in

structure SubFamily extends SubSystem S x E where
  mem_iff : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (y : E), y ∈ sub J ↔
    ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) • y ∈ sub I
variable (S x) in

structure LineBundle extends SubFamily S x Ω where
  fg : ∀ I, (sub I).FG
  invertible : ∀ I, ∃ Q' : Submodule (chartRing S x I) Ω, sub I * Q' = 1
def SubFamily.toFamily (F : SubFamily S x E) : Family.{u, v, w} S x where
  F I := F.sub I
  res := F.res
  res_smul _ _ _ _ _ := rfl
  res_self _ _ := rfl
  res_comp _ _ _ _ _ _ := rfl
  exists_smul_eq_res I J h y := by
    obtain ⟨a, ha, hay⟩ := (F.mem_iff I J h y).mp y.2
    exact ⟨a, ⟨(a : Ω) • (y : E), hay⟩, ha, rfl⟩
  exists_smul_eq_zero I J h m hm := by
    refine ⟨1, by simp, ?_⟩
    have : (m : E) = 0 := congrArg Subtype.val hm
    rw [one_smul]; exact Subtype.ext this
structure FinGradedSub where

  piece : ℤ → Submodule S E
  smul_mem : ∀ (d : ℕ) (c : ℤ) (f : Poly S N) (m : E), f.IsHomogeneous d → m ∈ piece c →
    aeval x f • m ∈ piece (c + d)

  fg : ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → E), (∀ j, gen j ∈ piece (deg j)) ∧
    ∀ c, piece c ≤ Submodule.span S {z | ∃ (j : Fin n) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f • gen j}
variable {E} in

def FinGradedSub.tilde (M : FinGradedSub (S := S) (x := x) E) (c : ℤ) (I : Chart x) :
    Submodule (chartRing S x I) E :=
  Submodule.span _ {y | ∃ (m : E) (s : Poly S N) (a : ℤ) (e : ℕ), s ∈ monos I.1 ∧
    s.IsHomogeneous e ∧ m ∈ M.piece a ∧ a - e = c ∧ y = (aeval x s)⁻¹ • m}
variable {E} in

def SubSystem.gam (F : SubSystem S x E) (c : ℤ) : Submodule S E := (F.twist (twistSys S x c)).secs
end Families
section Examples
variable {S : Type u} [CommRing S] {N : ℕ}
theorem isWeightedHomogeneous_int_of_isHomogeneous {p : Poly S N} {d : ℕ} (hp : p.IsHomogeneous d) :
    IsWeightedHomogeneous (fun _ => (1 : ℤ)) p (d : ℤ) := by
  intro s hs
  have := hp hs
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] at this ⊢
  rw [← this]
  push_cast
  exact Finset.sum_congr rfl fun _ _ => nsmul_one _
variable (S N) in

def polyGraded : GradedPMod S N (Poly S N) where
  piece c := weightedHomogeneousSubmodule S (fun _ => (1 : ℤ)) c
  isInternal := by
    classical
    exact (weightedDecomposition S (fun _ : Fin (N + 1) => (1 : ℤ))).isInternal
  smul_mem d c p m hp hm := by
    rw [mem_weightedHomogeneousSubmodule] at hm ⊢
    rw [smul_eq_mul, add_comm c (d : ℤ)]
    exact (isWeightedHomogeneous_int_of_isHomogeneous hp).mul hm
end Examples
section ChartFacts
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
theorem chartRing_smul_def {I : Chart x} (a : chartRing S x I) (z : Ω) : a • z = (a : Ω) * z := rfl
theorem twistMod_eq_span (c : ℤ) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    twistMod S x c I = Submodule.span _ {x i ^ c} := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  apply le_antisymm
  · rw [twistMod, Submodule.span_le]
    rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · have he : e' = e + n := by omega
      refine ⟨⟨aeval x f / aeval x (s * X i ^ n), f, s * X i ^ n, e',
        mul_mem hs (pow_mem (X_mem_monos hi) n), hf, he ▸ hse.mul (isHomogeneous_X_pow i n), rfl⟩, ?_⟩
      rw [chartRing_smul_def]
      simp only [map_mul, map_pow, aeval_X, zpow_natCast]
      field_simp
    · have he : e = e' + n := by omega
      refine ⟨⟨aeval x (f * X i ^ n) / aeval x s, f * X i ^ n, s, e, hs,
        he ▸ hf.mul (isHomogeneous_X_pow i n), hse, rfl⟩, ?_⟩
      rw [chartRing_smul_def]
      simp only [map_mul, map_pow, aeval_X, zpow_neg, zpow_natCast]
      field_simp
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · exact Submodule.subset_span ⟨X i ^ n, 1, 0, n, one_mem _, isHomogeneous_X_pow i n,
        isHomogeneous_one _ _, by simp, by simp⟩
    · exact Submodule.subset_span ⟨1, X i ^ n, n, 0, pow_mem (X_mem_monos hi) n,
        isHomogeneous_one _ _, isHomogeneous_X_pow i n, by simp, by simp [zpow_neg]⟩
theorem exists_isUnit_mul_mem {I J : Chart x} (h : I.1 ⊆ J.1) (b : chartRing S x J) :
    ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) * b ∈ chartRing S x I := by
  obtain ⟨f, s, e, hs, hf, hse, hb⟩ := b.2
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have hs0 := eval_ne_zero_of_mem_monos J hs
  have hX0 : aeval x (X i ^ e : Poly S N) ≠ 0 := by
    rw [map_pow, aeval_X]; exact pow_ne_zero _ hxi
  refine ⟨⟨aeval x s / aeval x (X i ^ e), s, X i ^ e, e, pow_mem (X_mem_monos hi) e, hse,
    isHomogeneous_X_pow i e, rfl⟩, ?_, ?_⟩
  · rw [isUnit_iff_exists_inv]
    refine ⟨⟨aeval x (X i ^ e) / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse, rfl⟩, ?_⟩
    apply Subtype.ext
    change aeval x s / aeval x (X i ^ e) * (aeval x (X i ^ e) / aeval x s) = 1
    field_simp
  · change aeval x s / aeval x (X i ^ e) * (b : Ω) ∈ chartRing S x I
    rw [hb]
    refine ⟨f, X i ^ e, e, pow_mem (X_mem_monos hi) e, hf, isHomogeneous_X_pow i e, ?_⟩
    field_simp
variable (S x) in

def twistBundle (c : ℤ) : LineBundle S x :=
  { twistSys S x c with
    mem_iff := fun I J h y => by
      obtain ⟨i, hi⟩ := I.2.1
      constructor
      · intro hy
        change y ∈ twistMod S x c J at hy
        rw [twistMod_eq_span c J (h hi), Submodule.mem_span_singleton] at hy
        obtain ⟨b, rfl⟩ := hy
        obtain ⟨a, ha, hab⟩ := exists_isUnit_mul_mem h b
        refine ⟨a, ha, ?_⟩
        change _ ∈ twistMod S x c I
        rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton]
        refine ⟨⟨_, hab⟩, ?_⟩
        rw [chartRing_smul_def, chartRing_smul_def, smul_eq_mul, mul_assoc]
      · rintro ⟨a, ⟨u, hu⟩, hay⟩
        have hJ := (twistSys S x c).mono I J h _ hay
        have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
          have := congrArg Subtype.val (Units.inv_mul u)
          rw [hu] at this
          exact this
        have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
          rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
        rw [hy]
        exact Submodule.smul_mem _ _ hJ
    fg := fun I => by
      obtain ⟨i, hi⟩ := I.2.1
      change (twistMod S x c I).FG
      rw [twistMod_eq_span c I hi]
      exact Submodule.fg_span_singleton _
    invertible := fun I => by
      obtain ⟨i, hi⟩ := I.2.1
      have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
      refine ⟨twistMod S x (-c) I, ?_⟩
      change twistMod S x c I * twistMod S x (-c) I = 1
      rw [twistMod_eq_span c I hi, twistMod_eq_span (-c) I hi, Submodule.span_mul_span,
        Set.singleton_mul_singleton, ← zpow_add₀ hxi, add_neg_cancel, zpow_zero,
        Submodule.one_eq_span] }
end ChartFacts
section MoreObjects
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
def H0tail (𝓜 : GradedPMod S N M) (c₁ : ℤ) : Submodule S (Cech.Cochain (locSys S N M) 0) :=
  ⨆ (c : ℤ) (_ : c₁ ≤ c), Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0
structure PrimeFilt (𝓜 : GradedPMod S N M) where

  n : ℕ

  step : Fin (n + 1) → Submodule (Poly S N) M

  gen : Fin n → M

  deg : Fin n → ℤ

  prime : Fin n → Ideal (Poly S N)
  step_zero : step 0 = ⊥
  step_last : step (Fin.last n) = ⊤
  step_succ : ∀ k : Fin n, step k.succ = step k.castSucc ⊔ Submodule.span (Poly S N) {gen k}
  gen_mem : ∀ k, gen k ∈ 𝓜.piece (deg k)
  mem_prime : ∀ k p, p ∈ prime k ↔ p • gen k ∈ step k.castSucc
  isPrime : ∀ k, (prime k).IsPrime
  isHomogeneous : ∀ k, ∀ p ∈ prime k, ∀ d : ℕ, homogeneousComponent d p ∈ prime k
  ann_le : ∀ k, Module.annihilator (Poly S N) M ≤ prime k
variable {Ω : Type w} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
def singleChart {j : Fin (N + 1)} (hj : x j ≠ 0) : Chart x :=
  ⟨{j}, Finset.singleton_nonempty j, Finset.singleton_subset_iff.mpr ((mem_support x).mpr hj)⟩
def ratio {j : Fin (N + 1)} (hj : x j ≠ 0) (i : Fin (N + 1)) : chartRing S x (singleChart hj) :=
  ⟨x i / x j, X i, X j, 1, X_mem_monos (Finset.mem_singleton_self j), isHomogeneous_X S i,
    isHomogeneous_X S j, by simp⟩
def chartPrime (pp : Ideal (Poly S N)) {j : Fin (N + 1)} (hj : x j ≠ 0) :
    Ideal (chartRing S x (singleChart hj)) :=
  Ideal.span {a | ∃ (f s : Poly S N) (e : ℕ), f ∈ pp ∧ s ∈ monos {j} ∧ f.IsHomogeneous e ∧
    s.IsHomogeneous e ∧ (a : Ω) = aeval x f / aeval x s}
def liftChart {K' : Type w} [Field K'] {y : Fin (N + 1) → K'} (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (I : Chart y) : Chart x :=
  ⟨I.1, I.2.1, fun i hi => (mem_support x).mpr (hxy i ((mem_support y).mp (I.2.2 hi)))⟩
def xProd (I : Chart x) : Ω := ∏ i ∈ I.1, x i
def ampleChart (H : SubSystem S x Ω) (m : ℕ) (h : Ω) (I : Chart x) : Set Ω :=
  {a | ∃ n : ℕ, a * h ^ n ∈ (H.pow (m * n)).sub I}
def ampleRing (H : SubSystem S x Ω) (m : ℕ) (h : Ω) : Set Ω := ⋂ I, ampleChart H m h I
def ampleBase {r : ℕ} (h : Fin (r + 1) → Ω) (j : Fin (r + 1)) : Subalgebra S Ω :=
  Algebra.adjoin S (Set.range fun l => h l / h j)
variable (S x) in

structure AmpleData (H : LineBundle S x) where

  m : ℕ
  m_pos : 0 < m

  r : ℕ

  h : Fin (r + 1) → Ω
  mem_secs : ∀ j, h j ∈ (H.pow m).secs
  generates : ∀ I, Submodule.span (chartRing S x I) (Set.range h) = (H.pow m).sub I
  finite : ∀ j, h j ≠ 0 → ∃ t : Finset Ω,
    ampleRing H.toSubSystem m (h j) ⊆ Submodule.span (ampleBase (S := S) h j) (t : Set Ω)
  affine : ∀ j, h j ≠ 0 → ∃ (n : ℕ) (a b : Fin n → Ω) (J : Fin n → Chart x),
    (∀ k, a k ∈ ampleRing H.toSubSystem m (h j)) ∧ (∀ k, b k ∈ ampleRing H.toSubSystem m (h j)) ∧
    ∑ k, a k * b k = 1 ∧ ∀ (k : Fin n) (I : Chart x), ∃ e : ℕ,
      b k ^ e * (xProd I ^ (J k).1.card / xProd (J k) ^ I.1.card) ∈ ampleChart H.toSubSystem m (h j) I
end MoreObjects
section Inhabitants
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
theorem mem_twistMod_one (I : Chart x) (j : Fin (N + 1)) : x j ∈ twistMod S x 1 I :=
  Submodule.subset_span ⟨X j, 1, 0, 1, one_mem _, isHomogeneous_X S j, isHomogeneous_one _ _,
    by simp, by simp⟩
end Inhabitants
section Line
variable (k : Type u) [Field k]
def lineX : Fin (1 + 1) → RatFunc k := ![1, RatFunc.X]
theorem lineX_ne_zero (i : Fin (1 + 1)) : lineX k i ≠ 0 := by
  fin_cases i
  · simp [lineX]
  · simp [lineX, RatFunc.X_ne_zero]
def tautologicalLineBundle : LineBundle k (lineX k) := twistBundle k (lineX k) 1
def lineChart0 : Chart (lineX k) := singleChart (lineX_ne_zero k 0)
end Line
section Generic
variable (k : Type u) [Field k] (N : ℕ)
def genericPt : Fin (N + 1) → FractionRing (Poly k N) :=
  fun i => algebraMap (Poly k N) (FractionRing (Poly k N)) (X i)
def polyPrimeFilt : PrimeFilt (polyGraded k N) where
  n := 1
  step := fun i => if i = 0 then ⊥ else ⊤
  gen := fun _ => 1
  deg := fun _ => 0
  prime := fun _ => ⊥
  step_zero := by simp
  step_last := by simp [Fin.last]
  step_succ i := by
    fin_cases i
    simp [Ideal.span_singleton_one]
  gen_mem _ := by
    change (1 : Poly k N) ∈ weightedHomogeneousSubmodule k _ _
    rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_one _ _
  mem_prime i p := by
    fin_cases i
    simp
  isPrime _ := Ideal.isPrime_bot
  isHomogeneous _ p hp d := by
    rw [Submodule.mem_bot] at hp ⊢
    rw [hp, map_zero]
  ann_le _ p hp := by
    rw [Module.mem_annihilator] at hp
    have := hp 1
    rw [smul_eq_mul, mul_one] at this
    rw [this]; exact Submodule.zero_mem _
end Generic
section AmpleExample
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
theorem one_mem_twistMod_zero (I : Chart x) : (1 : Ω) ∈ twistMod S x 0 I :=
  Submodule.subset_span ⟨1, 1, 0, 0, one_mem _, isHomogeneous_one _ _, isHomogeneous_one _ _,
    by simp, by simp⟩
theorem pow_twistSys_one_le (n : ℕ) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    ((twistSys S x 1).pow n).sub I ≤ Submodule.span _ {x i ^ n} := by
  induction n with
  | zero =>
    change twistMod S x 0 I ≤ _
    rw [twistMod_eq_span 0 I hi, zpow_zero, pow_zero]
  | succ n ih =>
    change Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x 1 I at hq
    rw [twistMod_eq_span 1 I hi, zpow_one, Submodule.mem_span_singleton] at hq
    obtain ⟨a, rfl⟩ := hq
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp (ih hy)
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨a * b, ?_⟩
    simp only [chartRing_smul_def, smul_eq_mul, Subalgebra.coe_mul, pow_succ]
    ring
theorem prod_mem_pow_twistSys_one (I : Chart x) (T : Finset (Fin (N + 1))) :
    ∏ i ∈ T, x i ∈ ((twistSys S x 1).pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => exact one_mem_twistMod_zero I
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    exact Submodule.subset_span ⟨x a, mem_twistMod_one I a, _, ih, rfl⟩
theorem mem_pow_one_twistSys_one (I : Chart x) (j : Fin (N + 1)) :
    x j ∈ ((twistSys S x 1).pow 1).sub I :=
  Submodule.subset_span ⟨x j, mem_twistMod_one I j, 1, one_mem_twistMod_zero I, by
    rw [smul_eq_mul, mul_one]⟩
theorem aeval_div_of_isHomogeneous {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (j : Fin (N + 1)) :
    aeval (fun l => x l / x j) f = aeval x f / x j ^ e := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hdeg : ∑ i ∈ s.support, s i = e := by
    have := hf (mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [aeval_monomial, aeval_monomial]
  simp only [Finsupp.prod, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
theorem mem_ampleBase_of_mem_chartRing {j : Fin (N + 1)} (hj : x j ≠ 0) {a : Ω}
    (ha : a ∈ chartRing S x (singleChart hj)) : a ∈ ampleBase (S := S) x j := by
  have := (algebraMap S Ω).domain_nontrivial
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  have hs' : s ∈ Submonoid.closure {(X j : Poly S N)} := by
    have : ((fun i => (X i : Poly S N)) '' ((({j} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
        {X j} := by simp
    rw [← this]; exact hs
  obtain ⟨m, rfl⟩ := Submonoid.mem_closure_singleton.mp hs'
  have hme : e = m := hse.inj_right (isHomogeneous_X_pow j m) (by
    rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
  subst hme
  rw [map_pow, aeval_X, ← aeval_div_of_isHomogeneous hf j, ampleBase,
    Algebra.adjoin_range_eq_range_aeval]
  exact ⟨f, rfl⟩
variable (S x) in

def twistAmple : AmpleData S x (twistBundle S x 1) where
  m := 1
  m_pos := one_pos
  r := N
  h := x
  mem_secs j := by
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    exact mem_pow_one_twistSys_one I j
  generates I := by
    obtain ⟨i, hi⟩ := I.2.1
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact mem_pow_one_twistSys_one I j
    · refine (pow_twistSys_one_le 1 I hi).trans (Submodule.span_mono ?_)
      rw [pow_one, Set.singleton_subset_iff]
      exact ⟨i, rfl⟩
  finite j hj := by
    refine ⟨{1}, fun a ha => ?_⟩
    have ha' := Set.mem_iInter.mp ha (singleChart hj)
    obtain ⟨n, hn⟩ := ha'
    rw [one_mul] at hn
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
      (pow_twistSys_one_le n (singleChart hj) (Finset.mem_singleton_self j) hn)
    rw [chartRing_smul_def] at hb
    have hab : a = b := by
      have hxn : x j ^ n ≠ 0 := pow_ne_zero _ hj
      exact (mul_right_cancel₀ hxn hb).symm
    have haB : a ∈ ampleBase (S := S) x j := hab ▸ mem_ampleBase_of_mem_chartRing hj b.2
    rw [Finset.coe_singleton, SetLike.mem_coe, Submodule.mem_span_singleton]
    exact ⟨⟨a, haB⟩, by rw [Subalgebra.smul_def, smul_eq_mul, mul_one]⟩
  affine j hj := by
    have h1 : (1 : Ω) ∈ ampleRing (twistBundle S x 1).toSubSystem 1 (x j) := by
      refine Set.mem_iInter.mpr fun I => ⟨0, ?_⟩
      rw [pow_zero, mul_one, mul_zero]
      exact one_mem_twistMod_zero I
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => singleChart hj, fun _ => h1, fun _ => h1,
      by simp, fun _ I => ⟨0, I.1.card, ?_⟩⟩
    have hxp : xProd (singleChart hj) = x j := by simp [xProd, singleChart]
    have hc : (singleChart hj).1.card = 1 := by simp [singleChart]
    rw [hxp, hc, pow_zero, one_mul, pow_one, one_mul, div_mul_cancel₀ _ (pow_ne_zero _ hj)]
    exact prod_mem_pow_twistSys_one I I.1
end AmpleExample
section MoreInhabitants
variable {S : Type u} [CommRing S] {N : ℕ}
variable (S N) in

def zeroGraded : GradedPMod S N PUnit where
  piece _ := ⊥
  isInternal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    exact ⟨fun _ => by simp, Subsingleton.elim _ _⟩
  smul_mem _ _ _ _ _ _ := (Submodule.mem_bot S).mpr (Subsingleton.elim _ _)
variable (S N) in

def polyGradedId : GradedHom (polyGraded S N) (polyGraded S N) where
  toLin := LinearMap.id
  map_piece _ _ h := h
variable (S N) in

def polyGradedToZero : GradedHom (polyGraded S N) (zeroGraded S N) where
  toLin := 0
  map_piece _ _ _ := by
    change _ ∈ (⊥ : Submodule S PUnit)
    exact (Submodule.mem_bot S).mpr (Subsingleton.elim _ _)
variable {Ω : Type w} [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
variable (S) in

def coordGraded : FinGradedSub (S := S) (x := x) Ω where
  piece c := Submodule.span S {z | ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ (e : ℤ) = c ∧
    z = aeval x f}
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span S
      {z | ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ (e : ℤ) = c + d ∧ z = aeval x f}) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨g, e, hg, he, rfl⟩
      exact Submodule.subset_span ⟨f * g, d + e, hf.mul hg, by push_cast; omega, by
        rw [map_mul, smul_eq_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha
      rw [smul_comm]; exact Submodule.smul_mem _ r ha
  fg := ⟨1, fun _ => 0, fun _ => 1, fun _ => Submodule.subset_span ⟨1, 0, isHomogeneous_one _ _,
      by simp, by simp⟩, fun c => Submodule.span_mono fun z ⟨f, e, hf, he, hz⟩ =>
      ⟨0, f, e, hf, by simp [he], by rw [hz, smul_eq_mul, mul_one]⟩⟩
end MoreInhabitants
end
end GroundTheory.Heights₂.Heights.Kleiman


