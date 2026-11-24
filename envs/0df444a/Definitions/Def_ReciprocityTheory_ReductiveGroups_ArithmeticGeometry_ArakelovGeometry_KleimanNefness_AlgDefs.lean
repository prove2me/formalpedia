-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDefs
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:16.406154+00:00
-- url     : https://prove2.me/theorems/55617c80-7531-4205-befa-26c9b03624ba
-- title:
--   Alg Defs
-- statement:
--   Definitions and structural lemmas for Alg Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/KleimanNefness/AlgDefs.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def Cell (K : Type*) [Fintype K] (ι : K → Type*) (n : ℕ) : Type _ :=
  {I : ∀ k, Finset (ι k) // (∀ k, (I k).Nonempty) ∧ ∑ k, ((I k).card - 1) = n}
def cellMon (S : Type*) [CommRing S] {K : Type*} {ι : K → Type*} (I : ∀ k, Finset (ι k)) :
    Submonoid (MRingOver S ι) :=
  Submonoid.closure {f | ∃ k, ∃ i ∈ I k, f = X ⟨k, i⟩}
abbrev CechC (S : Type*) [CommRing S] {K : Type*} [Fintype K] (ι : K → Type*) (M : Type*)
    [AddCommGroup M] [Module (MRingOver S ι) M] (n : ℕ) : Type _ :=
  ∀ I : Cell K ι n, LocalizedModule (cellMon S I.1) M
open Classical in

def cellRes (S : Type*) [CommRing S] {K : Type*} {ι : K → Type*} (M : Type*) [AddCommGroup M]
    [Module (MRingOver S ι) M] (J I : ∀ k, Finset (ι k)) :
    LocalizedModule (cellMon S J) M →ₗ[MRingOver S ι] LocalizedModule (cellMon S I) M :=
  if h : cellMon S J ≤ cellMon S I then LocalizedModule.liftOfLE _ _ h else 0
def faceSign {K : Type*} [Fintype K] [LinearOrder K] {ι : K → Type*} [∀ k, LinearOrder (ι k)]
    (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) : ℤ :=
  (-1) ^ (((I k).filter (· < i)).card + ∑ l ∈ Finset.univ.filter (· < k), ((I l).card - 1))
open Classical in

def cechD (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, LinearOrder (ι k)] (M : Type*) [AddCommGroup M] [Module (MRingOver S ι) M] (n : ℕ) :
    CechC S ι M n →ₗ[MRingOver S ι] CechC S ι M (n + 1) :=
  LinearMap.pi fun I => ∑ k, ∑ i ∈ I.1 k,
    if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
      faceSign I.1 k i • (cellRes S M _ I.1).comp
        (LinearMap.proj (R := MRingOver S ι) (φ := fun J : Cell K ι n => LocalizedModule (cellMon S J.1) M)
          ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
    else 0
def IsMGraded (S : Type*) [CommRing S] {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) : Prop :=
  DirectSum.IsInternal 𝓜 ∧
    ∀ (a : K → ℕ) (c : K → ℤ) (p : MRingOver S ι) (m : M), IsMultiHomog p a → m ∈ 𝓜 c →
      p • m ∈ 𝓜 (c + fun k => (a k : ℤ))
def locPart {S : Type*} [CommRing S] {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (T : Submonoid (MRingOver S ι))
    (c : K → ℤ) : Submodule S (LocalizedModule T M) :=
  Submodule.span S {x | ∃ (m : M) (t : T) (a : K → ℕ), IsMultiHomog (t : MRingOver S ι) a ∧
    m ∈ 𝓜 (c + fun k => (a k : ℤ)) ∧ x = LocalizedModule.mk m t}
def cechCc {S : Type*} [CommRing S] {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) :
    Submodule S (CechC S ι M n) :=
  Submodule.pi Set.univ fun I => locPart ι 𝓜 (cellMon S I.1) c
def cechZc {S : Type*} [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) :
    Submodule S (CechC S ι M n) :=
  cechCc ι 𝓜 c n ⊓ (LinearMap.ker (cechD S ι M n)).restrictScalars S
def cechBc {S : Type*} [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) :
    (n : ℕ) → Submodule S (CechC S ι M n)
  | 0 => ⊥
  | n + 1 => (cechCc ι 𝓜 c n).map ((cechD S ι M n).restrictScalars S)
abbrev cechHc {S : Type*} [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) : Type _ :=
  ↥(cechZc ι 𝓜 c n) ⧸ (cechBc ι 𝓜 c n).comap (cechZc ι 𝓜 c n).subtype
def cechMap (S : Type*) [CommRing S] {K : Type*} [Fintype K] (ι : K → Type*) {M N : Type*}
    [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N] [Module (MRingOver S ι) N]
    (g : M →ₗ[MRingOver S ι] N) (n : ℕ) : CechC S ι M n →ₗ[MRingOver S ι] CechC S ι N n :=
  LinearMap.pi fun I => (IsLocalizedModule.map (cellMon S I.1) (LocalizedModule.mkLinearMap _ M)
    (LocalizedModule.mkLinearMap _ N) g).comp
      (LinearMap.proj (R := MRingOver S ι) (φ := fun J : Cell K ι n => LocalizedModule (cellMon S J.1) M) I)
def IsMGradedMap (S : Type*) [CommRing S] {K : Type*} (ι : K → Type*) {M N : Type*}
    [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [AddCommGroup N] [Module (MRingOver S ι) N]
    [Module S N] (𝓜 : (K → ℤ) → Submodule S M) (𝓝 : (K → ℤ) → Submodule S N)
    (g : M →ₗ[MRingOver S ι] N) : Prop :=
  ∀ c, ∀ m ∈ 𝓜 c, g m ∈ 𝓝 c
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH


