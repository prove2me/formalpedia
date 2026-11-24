-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:31:35.198529+00:00
-- url     : https://prove2.me/theorems/cfc1aba8-7008-42b9-b7cd-c49aaaf27c59
-- title:
--   Flag Pair Definite Part Lattice
-- statement:
--   Definitions and structural lemmas for Flag Pair Definite Part Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/FlagPairDefinitePartLattice.lean

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_AutFinite
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_final_autFinite
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_gmap_inv
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_gmap_mul
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_gmap_one
import Theorems.Thm_Formalism_HermitianLatticesTheory_massBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
noncomputable section
open Formalism.HermitianLatticeCounting.S6
namespace GlobalTheory.HermLat
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]
abbrev rs (R : Type) [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V] (S : Submodule K V) :
    Submodule R V := S.restrictScalars R
def perp (H : HermSpace K V) (S : Submodule K V) : Submodule K V :=
  ⨅ x ∈ S, LinearMap.ker (H.B.flip x)
def dual (H : HermSpace K V) (M : Submodule R V) : Submodule R V :=
  rs R (Submodule.span K (M : Set V)) ⊓ Formalism.HermitianLatticesTheory.dual H.B.flip M
def IsIntegralLat (H : HermSpace K V) (M : Submodule R V) : Prop :=
  Formalism.HermitianLatticesTheory.IsIntegralLat H.B.flip M
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] in

theorem _root_.GlobalTheory.HermLat.flip_isSymm (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) : H.B.flip.IsSymm := by
  rw [LinearMap.isSymm_def]
  intro x y
  simp only [LinearMap.flip_apply, starRingEnd_apply]
  exact H.herm y x
def IsLatMod (M : Submodule R V) (S I : Submodule K V) : Prop :=
  (∃ N : Submodule R V, N.FG ∧ M = N ⊔ rs R I) ∧ Submodule.span K (M : Set V) = S
def IsUnimodMod (H : HermSpace K V) (M : Submodule R V) (S I : Submodule K V) : Prop :=
  IsLatMod M S I ∧ dual H M = M
def IsUnimod (H : HermSpace K V) (M : Submodule R V) : Prop := IsUnimodMod H M ⊤ ⊥
def idx (M M' : Submodule R V) : ℕ := M'.toAddSubgroup.relIndex M.toAddSubgroup
def gidx (M M' : Submodule R V) : ℝ := (idx M M' : ℝ) / (idx M' M : ℝ)
def del (H : HermSpace K V) (M : Submodule R V) : ℝ := Real.sqrt (gidx (dual H M) M)
def smulLat (g : R) (M : Submodule R V) : Submodule R V := M.map (g • (LinearMap.id : V →ₗ[R] V))
def LocGen (M M' : Submodule R V) (e : ℕ) : Prop :=
  ∀ P : Ideal R, P.IsMaximal → ∃ v : Fin e → V, (∀ i, v i ∈ M) ∧
    M ≤ M' ⊔ P • M ⊔ Submodule.span R (Set.range v)
def IsPrim (L M : Submodule R V) : Prop := M = L ⊓ rs R (Submodule.span K (M : Set V))
def IsModIso (H : HermSpace K V) (g : R) (L' L : Submodule R V) (Γ : Submodule R (V × V)) : Prop :=
  Γ ≤ L'.prod L ∧ (smulLat g L').prod (smulLat g L) ≤ Γ ∧
  (∀ y' ∈ L', ∃ y, (y', y) ∈ Γ) ∧ (∀ y ∈ L, ∃ y', (y', y) ∈ Γ) ∧
  (∀ y, ((0 : V), y) ∈ Γ → y ∈ smulLat g L) ∧ (∀ y', (y', (0 : V)) ∈ Γ → y' ∈ smulLat g L') ∧
  ∀ p ∈ Γ, ∀ q ∈ Γ, ∃ t : R, H.B p.1 q.1 - H.B p.2 q.2 = algebraMap R K (g * t)
def fixLat (Γ : Submodule R (V × V)) : Submodule R V :=
  Γ.comap ((LinearMap.id : V →ₗ[R] V).prod LinearMap.id)
section Term
variable {H : HermSpace K V} {r : ℕ}
def lead (F : FlagD H r) (Λ : Submodule R V) (a : Fin (r + 1)) : Submodule R K :=
  (Λ ⊔ rs R (F.Xa a.val)).comap ((LinearMap.toSpanSingleton K V (F.e a)).restrictScalars R)
def IsFrame (F : FlagD H r) (Λ : Submodule R V) (aa : Fin r → Submodule R K) : Prop :=
  (∀ a : Fin r, lead F Λ a.castSucc = aa a) ∧ lead F Λ (Fin.last r) = 1
def IsAdm (F F' : FlagD H r) (Λ : Submodule R V) (g : R) : Prop :=
  ∀ (a : Fin (r + 1)) (t : K) (x' : V), x' ∈ Λ → x' - t • F'.e a ∈ F'.Xa a.val →
    ∃ x ∈ Λ, x - t • F.e a ∈ F.Xa a.val ∧ x - x' ∈ smulLat g Λ
def IsFramed (F F' : FlagD H r) (Λ : Submodule R V) (aa : Fin r → Submodule R K) : Prop :=
  IsUnimod H Λ ∧ IsFrame F Λ aa ∧ IsFrame F' Λ aa
def lamI (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V :=
  (Λ ⊓ rs R (perp H (II F F'))) ⊔ rs R (II F F')
def uPerp (F F' : FlagD H r) : Submodule K V := perp H (F.X ⊔ F'.X)
def wSp (F F' : FlagD H r) : Submodule K V := perp H (V0 F F')
def latL (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V :=
  rs R (uPerp F F') ⊓ (Λ ⊔ rs R F.X)
def flagPairDefinitePartLattice (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V := latL F F' Λ ⊓ rs R (wSp F F')
def latA0 (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V := (Λ ⊓ rs R F.X) ⊔ rs R (II F F')
def latF (F : FlagD H r) (Λ : Submodule R V) (j : ℕ) : Submodule R V := Λ ⊓ rs R (F.Xa j)
def bOne (F F' : FlagD H r) (Λ : Submodule R V) (j : ℕ) : ℕ :=
  idx (Λ ⊓ rs R F.X) (latF F Λ j ⊔ (Λ ⊓ rs R (II F F')))
def normD (F F' : FlagD H r) (Λ : Submodule R V) (l : ℕ) : ℝ := del H (latF F Λ l ⊔ latF F' Λ l)
def delBar (F F' : FlagD H r) (Λ : Submodule R V) : ℝ := del H (latA0 F F' Λ ⊔ latA0 F' F Λ)
def lamOne (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V := lamI F F' Λ ⊓ rs R (uPerp F F')
def cardB (F F' : FlagD H r) (Λ : Submodule R V) : ℕ :=
  idx (lamI F F' Λ ⊓ rs R (F.X ⊔ F'.X)) (latA0 F F' Λ ⊔ latA0 F' F Λ)
def latTh (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V := lamOne F F' Λ ⊓ rs R (wSp F F')
def iotaGraph (F F' : FlagD H r) (Λ : Submodule R V) (g : R) : Submodule R (V × V) :=
  (flagPairDefinitePartLattice F' F Λ).prod (flagPairDefinitePartLattice F F' Λ) ⊓
    ((Λ.prod Λ ⊓ (smulLat g Λ ⊔ (Λ ⊓ rs R F.X)).comap (LinearMap.snd R V V - LinearMap.fst R V V)) ⊔
      (rs R F'.X).prod (rs R F.X))
def latLa (F F' : FlagD H r) (Λ : Submodule R V) (g : R) : Submodule R V := fixLat (iotaGraph F F' Λ g)
end Term
section Genus
def isomGrp (H : HermSpace K V) : Subgroup (V ≃ₗ[K] V) := Formalism.HermitianLatticesTheory.isom H.B.flip
def imLat (s : V ≃ₗ[K] V) (M : Submodule R V) : Submodule R V := Formalism.HermitianLatticesTheory.gmap s M
def Isometric (H : HermSpace K V) (M M' : Submodule R V) : Prop := ∃ s ∈ isomGrp H, imLat s M = M'
def autCard (H : HermSpace K V) (M : Submodule R V) : ENNReal :=
  (Set.encard {s : V ≃ₗ[K] V | s ∈ isomGrp H ∧ imLat s M = M} : ENat)
def InGenus (H : HermSpace K V) (L M : Submodule R V) : Prop := M ∈ Formalism.HermitianLatticesTheory.genus H.B.flip L
def genusSum (H : HermSpace K V) (L : Submodule R V) (φ : Submodule R V → ENNReal) : ENNReal :=
  ∑' c : Quot (fun M M' : {M : Submodule R V // InGenus H L M} => Isometric H M.1 M'.1),
    φ (Quot.out c).1 / autCard H (Quot.out c).1
def genusMass (H : HermSpace K V) (L : Submodule R V) : ENNReal := genusSum H L fun _ => 1
def genusMean (H : HermSpace K V) (L : Submodule R V) (φ : Submodule R V → ENNReal) : ENNReal :=
  genusSum H L φ / genusMass H L
theorem isometric_equivalence (H : HermSpace K V) : Equivalence (Isometric (R := R) H) where
  refl M := ⟨1, (isomGrp H).one_mem, Formalism.HermitianLatticesTheory.genusBasic_gmap_one M⟩
  symm := by
    rintro M _ ⟨s, hs, rfl⟩
    exact ⟨s⁻¹, (isomGrp H).inv_mem hs, Formalism.HermitianLatticesTheory.genusBasic_gmap_inv s M⟩
  trans := by
    rintro M _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨t * s, (isomGrp H).mul_mem ht hs, Formalism.HermitianLatticesTheory.genusBasic_gmap_mul s t M⟩
theorem autCard_eq_of_isometric (H : HermSpace K V) {M M' : Submodule R V} (h : Isometric H M M') :
    autCard H M = autCard H M' := by
  have key : ∀ {N N' : Submodule R V}, Isometric H N N' → autCard H N ≤ autCard H N' := by
    rintro N _ ⟨g, hg, rfl⟩
    unfold autCard
    refine ENat.toENNReal_le.2 (Set.encard_le_encard_of_injOn (f := fun a => g * a * g⁻¹) ?_ ?_)
    · rintro a ⟨ha, haN⟩
      refine ⟨mul_mem (mul_mem hg ha) (inv_mem hg), ?_⟩
      unfold imLat at haN ⊢
      rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, Formalism.HermitianLatticesTheory.genusBasic_gmap_inv, Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, haN]
    · intro a _ b _ hab
      simpa using hab
  exact le_antisymm (key h) (key ((isometric_equivalence H).symm h))
end Genus
section Mass
open NumberField
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def IsTraceDef (H : HermSpace K V) : Prop := ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (H.B x x)
theorem genusSum_eq_sum (H : HermSpace K V) {L : Submodule (𝓞 K) V} {s : Finset (Submodule (𝓞 K) V)}
    (hs : Formalism.ThetaLiftIndependence.IsClassReps H.B.flip L s) {φ : Submodule (𝓞 K) V → ENNReal}
    (hφ : ∀ M M', InGenus H L M → Isometric H M M' → φ M = φ M') :
    genusSum H L φ = ∑ M ∈ s, φ M / autCard H M := by
  set r := fun M M' : {M : Submodule (𝓞 K) V // InGenus H L M} => Isometric H M.1 M'.1 with hr
  have hre : Equivalence r := (isometric_equivalence H).comap _
  have hq : ∀ a b, Quot.mk r a = Quot.mk r b ↔ r a b := fun a b => by
    rw [Quot.eq, hre.eqvGen_iff]
  let f : s → Quot r := fun N => Quot.mk r ⟨N.1, hs.1 N.1 N.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro N N' h
      have h1 : Isometric H N.1 N'.1 := (hq _ _).1 h
      obtain ⟨P, -, hP⟩ := hs.2 N'.1 (hs.1 _ N'.2)
      exact Subtype.ext ((hP N.1 ⟨N.2, h1⟩).trans
        (hP N'.1 ⟨N'.2, (isometric_equivalence H).refl _⟩).symm)
    · rintro ⟨M⟩
      obtain ⟨N, ⟨hN, h⟩, -⟩ := hs.2 M.1 M.2
      exact ⟨⟨N, hN⟩, (hq _ _).2 h⟩
  unfold genusSum
  rw [← (Equiv.ofBijective f hf).tsum_eq, ← Finset.tsum_subtype s (fun M => φ M / autCard H M)]
  refine tsum_congr fun N => ?_
  have h : Isometric H (Quot.out (f N)).1 N.1 := (hq _ ⟨N.1, hs.1 N.1 N.2⟩).1 (Quot.out_eq _)
  show φ (Quot.out (f N)).1 / autCard H (Quot.out (f N)).1 = _
  rw [hφ _ _ (Quot.out (f N)).2 h, autCard_eq_of_isometric H h]
variable [FiniteDimensional K V]
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] in
open NumberField in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
variable [FiniteDimensional K V] in

theorem _root_.GlobalTheory.HermLat.autCard_eq_natCard {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} (hH : _root_.GlobalTheory.HermLat.IsTraceDef H)
    {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) :
    (_root_.Formalism.ThetaLiftIndependence.autL H.B.flip M).Finite ∧ 0 < Nat.card (_root_.Formalism.ThetaLiftIndependence.autL H.B.flip M) ∧
      _root_.GlobalTheory.HermLat.autCard H M = (Nat.card (_root_.Formalism.ThetaLiftIndependence.autL H.B.flip M) : ENNReal) := by
  have hA := _root_.Formalism.HermitianLatticesTheory.final_autFinite
  unfold _root_.Formalism.HermitianLatticesTheory.AutFinite at hA
  have hfin : (_root_.Formalism.ThetaLiftIndependence.autL H.B.flip M).Finite := by
    unfold _root_.Formalism.ThetaLiftIndependence.autL
    exact hA K V H.B.flip (_root_.GlobalTheory.HermLat.flip_isSymm H) (fun x hx => by simpa using hH x hx) M hM
  have hone : (1 : V ≃ₗ[K] V) ∈ _root_.Formalism.ThetaLiftIndependence.autL H.B.flip M := by
    unfold _root_.Formalism.ThetaLiftIndependence.autL
    exact ⟨one_mem _, _root_.Formalism.ThetaLiftIndependence.LatticeLiftIndependence.gmap_one (K := K) M⟩
  refine ⟨hfin, ?_, ?_⟩
  · have : Finite (_root_.Formalism.ThetaLiftIndependence.autL H.B.flip M) := hfin.to_subtype
    exact Nat.card_pos_iff.2 ⟨⟨⟨1, hone⟩⟩, this⟩
  · have hset : {s : V ≃ₗ[K] V | s ∈ _root_.GlobalTheory.HermLat.isomGrp H ∧
        _root_.GlobalTheory.HermLat.imLat s M = M} = _root_.Formalism.ThetaLiftIndependence.autL H.B.flip M := by
      unfold _root_.Formalism.ThetaLiftIndependence.autL
      rfl
    unfold _root_.GlobalTheory.HermLat.autCard
    rw [hset, ← hfin.cast_ncard_eq, Nat.card_coe_set_eq]
    simp
theorem genusMass_eq {H : HermSpace K V} (hH : IsTraceDef H) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) :
    genusMass H L = ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass H.B.flip L) := by
  obtain ⟨⟨s, hs⟩, hm, -⟩ := Formalism.HermitianLatticesTheory.massBasic K V H.B.flip (flip_isSymm H) hH L hL
  rw [genusMass, genusSum_eq_sum H hs (fun _ _ _ _ => rfl), hm s hs,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  refine Finset.sum_congr rfl fun M hM => ?_
  obtain ⟨-, hpos, he⟩ := autCard_eq_natCard hH (hs.1 M hM).1
  rw [he, ENNReal.ofReal_inv_of_pos (by exact_mod_cast hpos), ENNReal.ofReal_natCast, one_div]
theorem genusMass_ne_zero {H : HermSpace K V} (hH : IsTraceDef H) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) : genusMass H L ≠ 0 := by
  rw [genusMass_eq hH hL]
  exact (ENNReal.ofReal_pos.2 (Formalism.HermitianLatticesTheory.massBasic K V H.B.flip (flip_isSymm H) hH L hL).2.2).ne'
theorem genusMass_ne_top {H : HermSpace K V} (hH : IsTraceDef H) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) : genusMass H L ≠ ⊤ := by
  rw [genusMass_eq hH hL]
  exact ENNReal.ofReal_ne_top
theorem genusMean_one {H : HermSpace K V} (hH : IsTraceDef H) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) : genusMean H L (fun _ => 1) = 1 :=
  ENNReal.div_self (genusMass_ne_zero hH hL) (genusMass_ne_top hH hL)
end Mass
section Examples
omit [IsScalarTower R K V] [Algebra R K] [StarRing K] [Field K] [Module K V] in
example (M : Submodule R V) : idx M M = 1 := by simp [idx]
example {H : HermSpace K V} {M : Submodule R V} (h : IsUnimod H M) : del H M = 1 := by
  simp [del, gidx, idx, h.2]
example : idx (⊤ : Submodule ℤ ℤ) (Ideal.span {2}) = 2 := by
  have : (Ideal.span {(2 : ℤ)}).toAddSubgroup = AddSubgroup.zmultiples 2 := by
    ext x; simp [Ideal.mem_span_singleton', AddSubgroup.mem_zmultiples_iff]
  rw [idx, this]
  simp [Int.index_zmultiples]
def ratLine : HermSpace ℚ ℚ where
  B := LinearMap.mk₂'ₛₗ (RingHom.id ℚ) (starRingEnd ℚ) (fun x y => x * y)
    (by intros; ring) (by intros; simp; ring) (by intros; ring) (by intros; simp; ring)
  herm := by intro x y; simp; ring
  nondeg := by intro x h; simpa using h 1
theorem ratLine_isTraceDef : IsTraceDef ratLine := by
  intro x hx
  have : ratLine.B x x = x * x := rfl
  rw [this]
  have h : Algebra.trace ℚ ℚ (x * x) = x * x := by
    have := Algebra.trace_algebraMap (R := ℚ) (S := ℚ) (x * x)
    simpa using this
  have h2 := mul_self_pos.2 hx
  rw [← h] at h2
  exact h2
theorem ratLine_isLattice :
    Submodule.IsLattice ℚ (1 : Submodule (NumberField.RingOfIntegers ℚ) ℚ) := by
  refine ⟨by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _, ?_⟩
  rw [eq_top_iff]
  intro x _
  have h1 : (1 : ℚ) ∈ Submodule.span ℚ ((1 : Submodule (NumberField.RingOfIntegers ℚ) ℚ) : Set ℚ) :=
    Submodule.subset_span (Submodule.mem_one.2 ⟨1, map_one _⟩)
  simpa using Submodule.smul_mem _ x h1
example : genusMean ratLine (1 : Submodule (NumberField.RingOfIntegers ℚ) ℚ) (fun _ => 1) = 1 :=
  genusMean_one ratLine_isTraceDef ratLine_isLattice
end Examples
end GlobalTheory.HermLat


