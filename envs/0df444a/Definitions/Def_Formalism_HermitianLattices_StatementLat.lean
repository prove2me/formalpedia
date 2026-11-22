-- Prove2me | Definitions.Def_Formalism_HermitianLattices_StatementLat
-- name    : Formalism_HermitianLattices_StatementLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:51:38.716369+00:00
-- url     : https://prove2.me/theorems/2ad3c7ac-be65-4ca8-a2b5-07941fed51a8
-- title:
--   Statement Lat
-- statement:
--   Definitions and structural lemmas for Statement Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/StatementLat.lean

import Mathlib
import Definitions.Def_Formalism_FockGram_StatementHerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
namespace Formalism.HermitianLatticesTheory
section Defs
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
def isom (h : V →ₗ⋆[K] V →ₗ[K] K) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x y
    change h (a (b x)) (a (b y)) = h x y
    rw [ha, hb]
  inv_mem' := by
    intro a ha x y
    have := ha (a.symm x) (a.symm y)
    change h (a.symm x) (a.symm y) = h x y
    simpa using this.symm
def gmap (g : V ≃ₗ[K] V) (L : Submodule R V) : Submodule R V :=
  L.map ((g : V →ₗ[K] V).restrictScalars R)
def dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Submodule R V :=
  Formalism.E.hdual h L
def IsIntegralLat (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, h x y ∈ (1 : Submodule R K)
def IsUnimodular (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Prop :=
  dual h L = L
def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx
def hcompl (p : Ideal R) : Submonoid R :=
  Submonoid.closure {s | s ∉ p ∧ ∀ t : R, algebraMap R K t = star (algebraMap R K s) → t ∉ p}
def loc {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) (L : Submodule R W) :
    Submodule R W :=
  locS (hcompl (K := K) p) L
def localization₂ {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime] (L : Submodule R W) :
    Submodule R W :=
  locS p.primeCompl L
def locR (p : Ideal R) : Submodule R K := loc (K := K) p (1 : Submodule R K)
def dualAt (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) :
    Submodule R V :=
  ⨅ y ∈ L, (locR (K := K) p).comap ((h y).restrictScalars R)
def IsUnimodularAt (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) : Prop :=
  dualAt h p (loc (K := K) p L) = loc (K := K) p L
def SameGenus (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) : Prop :=
  ∀ p : Ideal R, p.IsMaximal → ∃ g ∈ isom h, gmap g (loc (K := K) p L) = loc (K := K) p M
def genus (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Set (Submodule R V) :=
  {M | Submodule.IsLattice K M ∧ SameGenus h L M}
def conjIdeal (P : Ideal R) : Ideal R :=
  Ideal.span {r | ∃ s ∈ P, algebraMap R K r = star (algebraMap R K s)}
def IsNeighbour (P : Ideal R) (L M : Submodule R V) : Prop :=
  (∀ q : Ideal R, q.IsMaximal → q ≠ P → q ≠ conjIdeal (K := K) P →
    loc (K := K) q L = loc (K := K) q M) ∧
  Nonempty ((L ⧸ (L ⊓ M).comap L.subtype) ≃ₗ[R] (R ⧸ conjIdeal (K := K) P)) ∧
  Nonempty ((M ⧸ (L ⊓ M).comap M.subtype) ≃ₗ[R] (R ⧸ P))
def locLen (p : Ideal R) [p.IsPrime] (A B : Submodule R V) : ℕ :=
  (Module.length R ((localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype)).toNat
def lidx (p : Ideal R) [p.IsPrime] (A B : Submodule R V) : ℤ :=
  (locLen p A (A ⊓ B) : ℤ) - locLen p B (A ⊓ B)
def jIdx (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) [p.IsPrime] (A : Submodule R V) : ℤ :=
  lidx p A (dual h A)
end Defs
def DualBasic : Prop :=
  ∀ (R K V : Type) [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) →
    (∀ L M : Submodule R V, L ≤ M → dual h M ≤ dual h L) ∧
    (∀ L : Submodule R V, L ≤ dual h (dual h L)) ∧
    (∀ L M : Submodule R V, dual h (L ⊔ M) = dual h L ⊓ dual h M) ∧
    (∀ L : Submodule R V, IsIntegralLat h L ↔ L ≤ dual h L) ∧
    (∀ L : Submodule R V, IsUnimodular h L ↔ IsIntegralLat h L ∧ dual h L ≤ L)
def DualLattice : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
    [IsScalarTower R K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → h.Nondegenerate →
    (∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) →
    ∀ L : Submodule R V, Submodule.IsLattice K L →
      Submodule.IsLattice K (dual h L) ∧ dual h (dual h L) = L ∧
      ∀ a : K, a ≠ 0 → dual h (L.map ((LinearMap.lsmul K V a).restrictScalars R)) =
        (dual h L).map ((LinearMap.lsmul K V (star a)⁻¹).restrictScalars R)
def LocBasic : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDomain R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V],
    Function.Injective (algebraMap R K) →
    (∀ (p : Ideal R), p.IsPrime → ∀ L M : Submodule R V,
      L ≤ loc (K := K) p L ∧ (L ≤ M → loc (K := K) p L ≤ loc (K := K) p M) ∧
      loc (K := K) p (loc (K := K) p L) = loc (K := K) p L ∧
      loc (K := K) p (L ⊓ M) = loc (K := K) p L ⊓ loc (K := K) p M ∧
      loc (K := K) p (L ⊔ M) = loc (K := K) p L ⊔ loc (K := K) p M) ∧
    (∀ L : Submodule R V, (⨅ (p : Ideal R) (_ : p.IsMaximal), loc (K := K) p L) = L) ∧
    (∀ L M : Submodule R V, (∀ p : Ideal R, p.IsMaximal → loc (K := K) p L ≤ loc (K := K) p M) →
      L ≤ M) ∧
    (∀ (p : Ideal R) [p.IsPrime] (L : Submodule R V), loc (K := K) p L ≤ localization₂ p L) ∧
    ((∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) →
      ∀ (p : Ideal R) [p.IsPrime],
        ∃ _ : (conjIdeal (K := K) p).IsPrime, ∀ L : Submodule R V,
          loc (K := K) p L = localization₂ p L ⊓ localization₂ (conjIdeal (K := K) p) L)
def LocDual : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDomain R] [Field K] [StarRing K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) →
    ∀ L : Submodule R V, L.FG →
      (∀ p : Ideal R, p.IsPrime → loc (K := K) p (dual h L) = dualAt h p L ∧
        dualAt h p (loc (K := K) p L) = dualAt h p L) ∧
      (IsUnimodular h L ↔ ∀ p : Ideal R, p.IsMaximal → IsUnimodularAt h p L)
def IsomAct : Prop :=
  ∀ (R K V : Type) [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (g : V ≃ₗ[K] V), g ∈ isom h → ∀ L : Submodule R V,
      dual h (gmap g L) = gmap g (dual h L) ∧
      (∀ p : Ideal R, loc (K := K) p (gmap g L) = gmap g (loc (K := K) p L)) ∧
      (IsIntegralLat h (gmap g L) ↔ IsIntegralLat h L) ∧
      (IsUnimodular h (gmap g L) ↔ IsUnimodular h L) ∧
      (Submodule.IsLattice K (gmap g L) ↔ Submodule.IsLattice K L)
def GenusBasic : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDomain R] [Field K] [StarRing K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) →
    Equivalence (SameGenus (R := R) h) ∧
    (∀ (L : Submodule R V) (g : V ≃ₗ[K] V), g ∈ isom h → SameGenus h L (gmap g L)) ∧
    (∀ L M : Submodule R V, L.FG → M.FG → SameGenus h L M →
      (IsUnimodular h L ↔ IsUnimodular h M) ∧ (IsIntegralLat h L ↔ IsIntegralLat h M))
def ClassSetFinite : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
      ∃ s : Finset (Submodule (NumberField.RingOfIntegers K) V), (∀ M ∈ s, M ∈ genus h L) ∧
        ∀ M ∈ genus h L, ∃ N ∈ s, ∃ g ∈ isom h, gmap g N = M
def NeighbourBasic : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
    [IsScalarTower R K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → h.Nondegenerate →
    (∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) →
    ∀ (P : Ideal R), P.IsMaximal → ∀ L M : Submodule R V,
      Submodule.IsLattice K L → Submodule.IsLattice K M → IsNeighbour (K := K) P L M →
      IsNeighbour (K := K) (conjIdeal (K := K) P) M L ∧
      (Finite (R ⧸ P) → IsUnimodular h L → IsIntegralLat h M → IsUnimodular h M)
def IndexBasic : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
    [IsScalarTower R K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → h.Nondegenerate →
    (∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) →
    ∀ (p : Ideal R) [p.IsMaximal] (A B C : Submodule R V),
      Submodule.IsLattice K A → Submodule.IsLattice K B → Submodule.IsLattice K C →
      lidx p A A = 0 ∧ lidx p A B = - lidx p B A ∧
      lidx p A C = lidx p A B + lidx p B C ∧
      (B ≤ A → lidx p A B = locLen p A B) ∧
      (IsUnimodular h A → jIdx h p A = 0) ∧
      (IsIntegralLat h A → (jIdx h p A ≤ 0 ∧ (jIdx h p A = 0 ↔ localization₂ p (dual h A) = localization₂ p A)))
def ExampleZ : Prop :=
  ∀ h : ℚ →ₗ⋆[ℚ] ℚ →ₗ[ℚ] ℚ, (∀ x y, h x y = x * y) →
    Submodule.IsLattice ℚ (1 : Submodule ℤ ℚ) ∧ IsUnimodular h (1 : Submodule ℤ ℚ) ∧
    IsIntegralLat h (Submodule.span ℤ {(2 : ℚ)}) ∧
    dual h (Submodule.span ℤ {(2 : ℚ)}) = Submodule.span ℤ {(1 / 2 : ℚ)} ∧
    ¬ IsUnimodular h (Submodule.span ℤ {(2 : ℚ)}) ∧
    (∀ (p : Ideal ℤ) [p.IsPrime], p = Ideal.span {2} →
      lidx p (1 : Submodule ℤ ℚ) (Submodule.span ℤ {(2 : ℚ)}) = 1) ∧
    (∀ (p : Ideal ℤ) [p.IsPrime], p = Ideal.span {3} →
      lidx p (1 : Submodule ℤ ℚ) (Submodule.span ℤ {(2 : ℚ)}) = 0)
end Formalism.HermitianLatticesTheory


