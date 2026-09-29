-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ff96eb08-3c07-5b42-9f60-4485cf5981ec

import Mathlib
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits"

namespace GrassH2

universe u

variable (R : Type) [CommRing R]

noncomputable abbrev strMap (A : Type) [CommRing A] [Algebra R A] :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

variable {R}

lemma spec_comp_strMap {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ strMap R A = strMap R B := by
  rw [strMap, strMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact φ.comp_algebraMap

@[reducible] noncomputable def algOf {A : Type} [CommRing A] (t : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) :
    Algebra R A :=
  (Spec.preimage t).hom.toAlgebra

lemma strMap_algOf {A : Type} [CommRing A] (t : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) :
    @strMap R _ A _ (algOf t) = t := by
  letI := algOf t
  show Spec.map (CommRingCat.ofHom (Spec.preimage t).hom) = t
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

lemma algebra_ext_of_strMap_eq {A : Type} [CommRing A] (i₁ i₂ : Algebra R A)
    (h : @strMap R _ A _ i₁ = @strMap R _ A _ i₂) : i₁ = i₂ := by
  apply Algebra.algebra_ext
  intro r
  have h' := congrArg (fun f => (CommRingCat.Hom.hom f) r) (Spec.map_injective h)
  simpa using h'

noncomputable def algHomOfSpec {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (a : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (ha : a ≫ strMap R A = strMap R B) :
    A →ₐ[R] B :=
  { (Spec.preimage a).hom with
    commutes' := fun r => by
      have h1 : Spec.map (CommRingCat.ofHom (algebraMap R A) ≫ Spec.preimage a) =
          Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
        rw [Spec.map_comp, Spec.map_preimage]; exact ha
      have h2 := congrArg (fun f => (CommRingCat.Hom.hom f) r) (Spec.map_injective h1)
      simpa using h2 }

lemma algHomOfSpec_toRingHom {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (a : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (ha : a ≫ strMap R A = strMap R B) :
    (algHomOfSpec a ha).toRingHom = (Spec.preimage a).hom := rfl

lemma spec_algHomOfSpec {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (a : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (ha : a ≫ strMap R A = strMap R B) :
    Spec.map (CommRingCat.ofHom (algHomOfSpec a ha).toRingHom) = a := by
  rw [algHomOfSpec_toRingHom, CommRingCat.ofHom_hom, Spec.map_preimage]

lemma range_comap_eq {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    Set.range (PrimeSpectrum.comap φ) = Set.range (Spec.map (CommRingCat.ofHom φ)) := by
  rfl

structure Ctx (R : Type) [CommRing R] (ι : Type) (S : ι → Type) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] : Type 1 where
  F : ∀ (A : Type) [CommRing A] [Algebra R A], Type
  Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B
  Fmap_id : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), Fmap A A (AlgHom.id R A) s = s
  Fmap_comp : ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B]
      [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (s : F A),
      Fmap A C (ψ.comp φ) s = Fmap B C ψ (Fmap A B φ s)
  G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type
  ev : ∀ (A : Type) [CommRing A] [Algebra R A],
      F A ≃ G.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))))
  hG : Presheaf.IsSheaf Scheme.zariskiTopology G.overTotal
  hev : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (s : F A)
      (h : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
        Spec.map (CommRingCat.ofHom (algebraMap R B))),
      ev B (Fmap A B φ s) =
        G.map (Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) h :
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))).op (ev A s)
  P : ι → ∀ (A : Type) [CommRing A] [Algebra R A], F A → Prop
  isOpen : ∀ (i : ι) (A : Type) [CommRing A] [Algebra R A] (s : F A),
      ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
        ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
          P i B (Fmap A B φ s) ↔ Set.range (PrimeSpectrum.comap φ.toRingHom) ⊆ U
  chart : ∀ (i : ι) (A : Type) [CommRing A] [Algebra R A], {s : F A // P i A s} ≃ (S i →ₐ[R] A)
  chart_natural : ∀ (i : ι) (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (φ : A →ₐ[R] B) (s : {s : F A // P i A s}) (h : P i B (Fmap A B φ s.1)),
      chart i B ⟨Fmap A B φ s.1, h⟩ = φ.comp (chart i A s)
  cover : ∀ (K : Type) [Field K] [Algebra R K] (s : F K), ∃ i, P i K s

variable {ι : Type} {S : ι → Type} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] (X : Ctx R ι S)

namespace Ctx

abbrev Sec (A : Type) [CommRing A] : Type := X.G.overTotal.obj (op (Spec (CommRingCat.of A)))

lemma map_comp_apply' {T T' T'' : Scheme.{0}} (a : T ⟶ T') (b : T' ⟶ T'') (ξ : X.G.overTotal.obj (op T'')) :
    X.G.overTotal.map (a ≫ b).op ξ = X.G.overTotal.map a.op (X.G.overTotal.map b.op ξ) := by
  rw [op_comp, Functor.map_comp_apply]

@[scoped simp] lemma map_fst {T T' : Scheme.{0}} (a : T ⟶ T') (ξ : X.G.overTotal.obj (op T')) :
    (X.G.overTotal.map a.op ξ).1 = a ≫ ξ.1 := rfl

noncomputable def secOf {A : Type} [CommRing A] [Algebra R A] (s : X.F A) : X.Sec A :=
  ⟨strMap R A, X.ev A s⟩

@[scoped simp] lemma secOf_fst {A : Type} [CommRing A] [Algebra R A] (s : X.F A) : (X.secOf s).1 = strMap R A := rfl

noncomputable def rd {A : Type} [CommRing A] [Algebra R A] (b : X.Sec A) (hb : b.1 = strMap R A) : X.F A :=
  (X.ev A).symm (Functor.OverTotal.toFibre (Over.mk (strMap R A)) b hb)

lemma rd_secOf {A : Type} [CommRing A] [Algebra R A] (s : X.F A) : X.rd (X.secOf s) rfl = s := by
  change (X.ev A).symm _ = s
  rw [Equiv.symm_apply_eq]
  exact Functor.map_op_apply_eq_self _ (by simp) _

lemma secOf_rd {A : Type} [CommRing A] [Algebra R A] (b : X.Sec A) (hb : b.1 = strMap R A) :
    X.secOf (X.rd b hb) = b := by
  change (⟨strMap R A, X.ev A ((X.ev A).symm _)⟩ : X.Sec A) = b
  rw [Equiv.apply_symm_apply]
  refine Eq.trans ?_ (Functor.OverTotal.ofFibre_toFibre (Over.mk (strMap R A)) b hb)
  exact Functor.OverTotal.ext' rfl rfl

lemma secOf_injective {A : Type} [CommRing A] [Algebra R A] : Function.Injective (X.secOf (A := A)) := by
  intro s s' h
  exact (X.ev A).injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

lemma exists_eq_secOf {A : Type} [CommRing A] (b : X.Sec A) :
    ∃ inst : Algebra R A, letI := inst; ∃ s : X.F A, X.secOf s = b := by
  letI := algOf b.1
  exact ⟨algOf b.1, X.rd b (strMap_algOf b.1).symm, X.secOf_rd b _⟩

lemma map_secOf {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) (s : X.F A) :
    X.G.overTotal.map (Spec.map (CommRingCat.ofHom φ.toRingHom)).op (X.secOf s) =
      X.secOf (X.Fmap A B φ s) := by
  have h := spec_comp_strMap (R := R) φ
  refine Functor.OverTotal.ext' ?_ ?_
  · exact h
  · simp only [secOf]
    rw [X.hev A B φ s h]
    change X.G.map _ (X.G.map _ (X.ev A s)) = X.G.map _ (X.ev A s)
    exact (Functor.map_op_map_op_apply _ _ _).trans (Functor.map_op_apply_eq_of_left_eq _ _ (by simp) _)

lemma map_secOf' {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (a : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (ha : a ≫ strMap R A = strMap R B) (s : X.F A) :
    X.G.overTotal.map a.op (X.secOf s) = X.secOf (X.Fmap A B (algHomOfSpec a ha) s) := by
  rw [← X.map_secOf (algHomOfSpec a ha) s, spec_algHomOfSpec]

def Q (i : ι) {A : Type} [CommRing A] (b : X.Sec A) : Prop :=
  ∃ inst : Algebra R A, letI := inst; ∃ s : X.F A, X.P i A s ∧ X.secOf s = b

lemma Q_secOf (i : ι) {A : Type} [CommRing A] [inst : Algebra R A] (s : X.F A) :
    X.Q i (X.secOf s) ↔ X.P i A s := by
  constructor
  · rintro ⟨inst', s', hP, hs⟩
    obtain rfl : inst' = inst := algebra_ext_of_strMap_eq _ _ (congrArg Sigma.fst hs)
    obtain rfl := X.secOf_injective hs
    exact hP
  · intro h
    exact ⟨inst, s, h, rfl⟩

lemma Q_iff (i : ι) {A : Type} [CommRing A] [Algebra R A] (b : X.Sec A) (hb : b.1 = strMap R A) :
    X.Q i b ↔ X.P i A (X.rd b hb) := by
  rw [← X.Q_secOf, X.secOf_rd]

lemma P_map (i : ι) {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
    {s : X.F A} (hs : X.P i A s) : X.P i B (X.Fmap A B φ s) := by
  obtain ⟨U, -, hU⟩ := X.isOpen i A s
  have huniv : Set.univ ⊆ U := by
    have h := (hU A (AlgHom.id R A)).mp (by rw [X.Fmap_id]; exact hs)
    intro x _
    apply h
    exact ⟨x, PrimeSpectrum.ext (Ideal.comap_id x.asIdeal)⟩
  exact (hU B φ).mpr fun _ _ => huniv trivial

lemma P_of_field (i : ι) {K L : Type} [Field K] [CommRing L] [Nontrivial L] [Algebra R K] [Algebra R L]
    (φ : K →ₐ[R] L) {s : X.F K} (hs : X.P i L (X.Fmap K L φ s)) : X.P i K s := by
  obtain ⟨U, -, hU⟩ := X.isOpen i K s
  have h1 : Set.range (PrimeSpectrum.comap φ.toRingHom) ⊆ U := (hU L φ).mp hs
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum L) := inferInstance
  have hpt : (default : PrimeSpectrum K) ∈ U := by
    have := h1 ⟨q, rfl⟩
    rwa [Subsingleton.elim (PrimeSpectrum.comap φ.toRingHom q) default] at this
  have huniv : Set.univ ⊆ U := fun x _ => by rwa [Subsingleton.elim x default]
  have := (hU K (AlgHom.id R K)).mpr (fun _ _ => huniv trivial)
  rwa [X.Fmap_id] at this

lemma Q_map (i : ι) {A B : Type} [CommRing A] [CommRing B]
    (a : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) {b : X.Sec A} (hb : X.Q i b) :
    X.Q i (X.G.overTotal.map a.op b) := by
  obtain ⟨inst, s, hP, rfl⟩ := hb
  letI : Algebra R B := algOf (a ≫ strMap R A)
  have ha : a ≫ strMap R A = strMap R B := (strMap_algOf _).symm
  rw [X.map_secOf' a ha]
  exact (X.Q_secOf i _).mpr (X.P_map i _ hP)

lemma Q_iff_of_field (i : ι) {K L : Type} [Field K] [Field L]
    (c : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) (b : X.Sec K) :
    X.Q i (X.G.overTotal.map c.op b) ↔ X.Q i b := by
  refine ⟨fun h => ?_, X.Q_map i c⟩
  obtain ⟨instK, s, rfl⟩ := X.exists_eq_secOf b
  letI : Algebra R L := algOf (c ≫ strMap R K)
  have hc : c ≫ strMap R K = strMap R L := (strMap_algOf _).symm
  rw [X.map_secOf' c hc, X.Q_secOf] at h
  exact (X.Q_secOf i s).mpr (X.P_of_field i _ h)

noncomputable def ptSec {T : Scheme.{0}} (ξ : X.G.overTotal.obj (op T)) (x : T) : X.Sec (T.residueField x) :=
  X.G.overTotal.map (T.fromSpecResidueField x).op ξ

def mem (i : ι) {T : Scheme.{0}} (ξ : X.G.overTotal.obj (op T)) (x : T) : Prop :=
  X.Q i (X.ptSec ξ x)

lemma mem_map (i : ι) {Y T : Scheme.{0}} (a : Y ⟶ T) (ξ : X.G.overTotal.obj (op T)) (y : Y) :
    X.mem i (X.G.overTotal.map a.op ξ) y ↔ X.mem i ξ (a y) := by
  unfold mem ptSec
  rw [← X.map_comp_apply', ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    X.map_comp_apply']
  exact X.Q_iff_of_field i _ _

noncomputable def U (i : ι) {A : Type} [CommRing A] [Algebra R A] (s : X.F A) : Set (PrimeSpectrum A) :=
  (X.isOpen i A s).choose

lemma isOpen_U (i : ι) {A : Type} [CommRing A] [Algebra R A] (s : X.F A) : IsOpen (X.U i s) :=
  (X.isOpen i A s).choose_spec.1

lemma U_spec (i : ι) {A : Type} [CommRing A] [Algebra R A] (s : X.F A) (B : Type) [CommRing B]
    [Algebra R B] (φ : A →ₐ[R] B) :
    X.P i B (X.Fmap A B φ s) ↔ Set.range (PrimeSpectrum.comap φ.toRingHom) ⊆ X.U i s :=
  (X.isOpen i A s).choose_spec.2 B φ

lemma Q_map_secOf_iff (i : ι) {A K : Type} [CommRing A] [Algebra R A] [Field K]
    (c : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A)) (s : X.F A) :
    X.Q i (X.G.overTotal.map c.op (X.secOf s)) ↔ Set.range c ⊆ X.U i s := by
  letI : Algebra R K := algOf (c ≫ strMap R A)
  have hc : c ≫ strMap R A = strMap R K := (strMap_algOf _).symm
  rw [X.map_secOf' c hc, X.Q_secOf, X.U_spec, range_comap_eq, spec_algHomOfSpec]
  exact Iff.rfl

lemma mem_secOf_iff (i : ι) {A : Type} [CommRing A] [Algebra R A] (s : X.F A)
    (p : Spec (CommRingCat.of A)) : X.mem i (X.secOf s) p ↔ p ∈ X.U i s := by
  unfold mem ptSec
  rw [X.Q_map_secOf_iff (K := (Spec (CommRingCat.of A)).residueField p),
    Scheme.range_fromSpecResidueField, Set.singleton_subset_iff]
  exact Iff.rfl

lemma forall_mem_secOf_iff (i : ι) {A : Type} [CommRing A] [Algebra R A] (s : X.F A) :
    (∀ p : Spec (CommRingCat.of A), X.mem i (X.secOf s) p) ↔ X.P i A s := by
  simp_rw [X.mem_secOf_iff]
  constructor
  · intro h
    have := (X.U_spec i s A (AlgHom.id R A)).mpr (fun p _ => h p)
    rwa [X.Fmap_id] at this
  · intro h p
    have h' := (X.U_spec i s A (AlgHom.id R A)).mp (by rwa [X.Fmap_id])
    exact h' ⟨p, PrimeSpectrum.ext (Ideal.comap_id p.asIdeal)⟩

lemma isOpen_setOf_mem_sec (i : ι) {A : CommRingCat.{0}} (b : X.G.overTotal.obj (op (Spec A))) :
    IsOpen {p : Spec A | X.mem i b p} := by
  obtain ⟨inst, s, rfl⟩ := X.exists_eq_secOf (A := A) b
  simp_rw [X.mem_secOf_iff]
  exact X.isOpen_U i s

lemma isOpen_setOf_mem (i : ι) {T : Scheme.{0}} (ξ : X.G.overTotal.obj (op T)) :
    IsOpen {x : T | X.mem i ξ x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  let 𝒰 := T.affineOpenCover
  obtain ⟨y, hy⟩ := 𝒰.covers x
  refine ⟨(𝒰.f (𝒰.idx x)) '' {p | X.mem i (X.G.overTotal.map (𝒰.f (𝒰.idx x)).op ξ) p}, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (X.mem_map i _ ξ p).mp hp
  · exact (𝒰.f (𝒰.idx x)).isOpenEmbedding.isOpenMap _ (X.isOpen_setOf_mem_sec i _)
  · exact ⟨y, (X.mem_map i _ ξ y).mpr (by rw [hy]; exact hx), hy⟩

def W (i : ι) {T : Scheme.{0}} (ξ : X.G.overTotal.obj (op T)) : T.Opens :=
  ⟨{x | X.mem i ξ x}, X.isOpen_setOf_mem i ξ⟩

lemma mem_W_iff (i : ι) {T : Scheme.{0}} (ξ : X.G.overTotal.obj (op T)) (x : T) :
    x ∈ X.W i ξ ↔ X.mem i ξ x := Iff.rfl

noncomputable def u (i : ι) : {s : X.F (S i) // X.P i (S i) s} := (X.chart i (S i)).symm (AlgHom.id R (S i))

noncomputable def univSec (i : ι) : X.Sec (S i) := X.secOf (X.u i).1

lemma chart_Fmap_u (i : ι) {A : Type} [CommRing A] [Algebra R A] (φ : S i →ₐ[R] A)
    (h : X.P i A (X.Fmap (S i) A φ (X.u i).1)) : X.chart i A ⟨X.Fmap (S i) A φ (X.u i).1, h⟩ = φ := by
  rw [X.chart_natural i (S i) A φ (X.u i) h]
  unfold u
  rw [Equiv.apply_symm_apply, AlgHom.comp_id]

lemma Fmap_chart (i : ι) {A : Type} [CommRing A] [Algebra R A] (s : {s : X.F A // X.P i A s}) :
    X.Fmap (S i) A (X.chart i A s) (X.u i).1 = s.1 := by
  have h : X.P i A (X.Fmap (S i) A (X.chart i A s) (X.u i).1) := X.P_map i _ (X.u i).2
  have h1 := X.chart_Fmap_u i (X.chart i A s) h
  exact congrArg Subtype.val ((X.chart i A).injective h1)

lemma mem_univSec (i : ι) (p : Spec (CommRingCat.of (S i))) : X.mem i (X.univSec i) p :=
  (X.forall_mem_secOf_iff i (X.u i).1).mpr (X.u i).2 p

lemma eq_of_map_univSec_eq_affine (i : ι) {A : CommRingCat.{0}}
    (b b' : Spec A ⟶ Spec (CommRingCat.of (S i)))
    (h : X.G.overTotal.map b.op (X.univSec i) = X.G.overTotal.map b'.op (X.univSec i)) : b = b' := by
  letI : Algebra R A := algOf (A := A) (b ≫ strMap R (S i))
  have hb : b ≫ strMap R (S i) = strMap R A := (strMap_algOf (A := A) _).symm
  have hb' : b' ≫ strMap R (S i) = strMap R A := by
    have h1 := congrArg Sigma.fst h
    change b ≫ strMap R (S i) = b' ≫ strMap R (S i) at h1
    rw [← h1]; exact hb
  have h2 := X.secOf_injective
    ((X.map_secOf' (B := A) b hb (X.u i).1).symm.trans (h.trans (X.map_secOf' (B := A) b' hb' (X.u i).1)))
  have e1 := X.chart_Fmap_u i (algHomOfSpec b hb) (X.P_map i (algHomOfSpec b hb) (X.u i).2)
  have e2 := X.chart_Fmap_u i (algHomOfSpec b' hb') (X.P_map i (algHomOfSpec b' hb') (X.u i).2)
  have e : algHomOfSpec b hb = algHomOfSpec b' hb' := by
    rw [← e1, ← e2]
    congr 1
    exact Subtype.ext h2
  exact (spec_algHomOfSpec (B := A) b hb).symm.trans (e ▸ spec_algHomOfSpec (B := A) b' hb')

lemma eq_of_map_univSec_eq (i : ι) {Y : Scheme.{0}} (b b' : Y ⟶ Spec (CommRingCat.of (S i)))
    (h : X.G.overTotal.map b.op (X.univSec i) = X.G.overTotal.map b'.op (X.univSec i)) : b = b' := by
  refine Y.affineOpenCover.openCover.hom_ext _ _ fun j => ?_
  show Y.affineOpenCover.f j ≫ b = Y.affineOpenCover.f j ≫ b'
  apply X.eq_of_map_univSec_eq_affine i
  rw [X.map_comp_apply', X.map_comp_apply', h]

lemma exists_map_univSec_eq_affine (i : ι) {A : CommRingCat.{0}} (b : X.G.overTotal.obj (op (Spec A)))
    (h : ∀ p, X.mem i b p) :
    ∃ c : Spec A ⟶ Spec (CommRingCat.of (S i)), X.G.overTotal.map c.op (X.univSec i) = b := by
  obtain ⟨inst, s, rfl⟩ := X.exists_eq_secOf (A := A) b
  have hP : X.P i A s := (X.forall_mem_secOf_iff i s).mp h
  refine ⟨Spec.map (CommRingCat.ofHom (X.chart i A ⟨s, hP⟩).toRingHom), ?_⟩
  exact (X.map_secOf (X.chart i A ⟨s, hP⟩) (X.u i).1).trans (congrArg X.secOf (X.Fmap_chart i ⟨s, hP⟩))

lemma exists_map_univSec_eq (i : ι) {Y : Scheme.{0}} (ζ : X.G.overTotal.obj (op Y))
    (h : ∀ y, X.mem i ζ y) :
    ∃ φ : Y ⟶ Spec (CommRingCat.of (S i)), X.G.overTotal.map φ.op (X.univSec i) = ζ := by
  let 𝒰 := Y.affineOpenCover
  have hj : ∀ j, ∃ c : Spec (𝒰.X j) ⟶ Spec (CommRingCat.of (S i)),
      X.G.overTotal.map c.op (X.univSec i) = X.G.overTotal.map (𝒰.f j).op ζ := fun j =>
    X.exists_map_univSec_eq_affine i _ (fun p => (X.mem_map i (𝒰.f j) ζ p).mpr (h _))
  choose c hc using hj
  have hcompat : ∀ j k, pullback.fst (𝒰.f j) (𝒰.f k) ≫ c j = pullback.snd (𝒰.f j) (𝒰.f k) ≫ c k := by
    intro j k
    apply X.eq_of_map_univSec_eq i
    rw [X.map_comp_apply', X.map_comp_apply', hc, hc, ← X.map_comp_apply', ← X.map_comp_apply',
      pullback.condition]
  refine ⟨𝒰.openCover.glueMorphisms c hcompat, ?_⟩
  have hsep := (((isSheaf_iff_isSheaf_of_type _ _).mp X.hG).isSheafFor _
    𝒰.openCover.mem_grothendieckTopology).isSeparatedFor
  apply hsep.ext
  rintro Z g ⟨j⟩
  rw [← X.map_comp_apply', Scheme.Cover.ι_glueMorphisms]
  exact hc j

noncomputable def f (i : ι) : yoneda.obj (Spec (CommRingCat.of (S i))) ⟶ X.G.overTotal :=
  yonedaEquiv.symm (X.univSec i)

lemma f_app (i : ι) {T : Scheme.{0}} (b : T ⟶ Spec (CommRingCat.of (S i))) :
    (X.f i).app (op T) b = X.G.overTotal.map b.op (X.univSec i) := rfl

theorem isOpenImmersion_presheaf (i : ι) : IsOpenImmersion.presheaf (X.f i) := by
  apply MorphismProperty.relative.of_exists
  intro T g
  have hg : ∀ {T' : Scheme.{0}} (a : T' ⟶ T), g.app (op T') a = X.G.overTotal.map a.op (yonedaEquiv g) :=
    fun a => (map_yonedaEquiv g a).symm
  obtain ⟨φ, hφ⟩ := X.exists_map_univSec_eq i (X.G.overTotal.map (X.W i (yonedaEquiv g)).ι.op (yonedaEquiv g))
    (fun w => (X.mem_map i _ _ w).mpr w.2)
  refine ⟨X.W i (yonedaEquiv g), yoneda.map φ, (X.W i (yonedaEquiv g)).ι, ?_, inferInstance⟩
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨T'⟩
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext c
    change (X.f i).app (op T') (c ≫ φ) = g.app (op T') (c ≫ (X.W i (yonedaEquiv g)).ι)
    rw [f_app, hg, X.map_comp_apply', X.map_comp_apply', hφ]
  · rintro c c' ⟨-, h2⟩
    exact (cancel_mono (X.W i (yonedaEquiv g)).ι).mp h2
  · intro x₂ x₃ hx
    change T' ⟶ Spec (CommRingCat.of (S i)) at x₂
    change T' ⟶ T at x₃
    change (X.f i).app (op T') x₂ = g.app (op T') x₃ at hx
    rw [f_app, hg] at hx
    have hrange : Set.range x₃ ⊆ Set.range (X.W i (yonedaEquiv g)).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      change X.mem i (yonedaEquiv g) (x₃ y)
      rw [← X.mem_map i x₃ _ y, ← hx, X.mem_map i x₂]
      exact X.mem_univSec i _
    refine ⟨IsOpenImmersion.lift _ x₃ hrange, ?_, IsOpenImmersion.lift_fac _ _ _⟩
    change IsOpenImmersion.lift _ x₃ hrange ≫ φ = x₂
    apply X.eq_of_map_univSec_eq i
    rw [X.map_comp_apply', hφ, ← X.map_comp_apply', IsOpenImmersion.lift_fac, ← hx]

theorem isLocallySurjective :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc X.f) := by
  constructor
  intro T ξ
  have hcov : ∀ x : T, ∃ i, x ∈ X.W i ξ := fun x => by
    obtain ⟨inst, s, hs⟩ := X.exists_eq_secOf (X.ptSec ξ x)
    obtain ⟨i, hi⟩ := X.cover _ s
    exact ⟨i, inst, s, hi, hs⟩
  let 𝒲 : T.OpenCover := Scheme.Cover.mkOfCovers ι (fun i => ((X.W i ξ : T.Opens) : Scheme.{0}))
    (fun i => (X.W i ξ).ι) (fun x => by
      obtain ⟨i, hi⟩ := hcov x
      exact ⟨i, ⟨x, hi⟩, rfl⟩)
  refine GrothendieckTopology.superset_covering _ ?_ 𝒲.mem_grothendieckTopology
  intro Y g hg
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  let a' : Y ⟶ (X.W i ξ : Scheme.{0}) := a
  obtain ⟨φ, hφ⟩ := X.exists_map_univSec_eq i (X.G.overTotal.map (X.W i ξ).ι.op ξ)
    (fun w => (X.mem_map i _ _ w).mpr w.2)
  refine ⟨(Sigma.ι (fun i => yoneda.obj (Spec (CommRingCat.of (S i)))) i).app (op Y) (a' ≫ φ), ?_⟩
  show (Sigma.ι (fun i => yoneda.obj (Spec (CommRingCat.of (S i)))) i ≫ Sigma.desc X.f).app (op Y)
    (a' ≫ φ) = X.G.overTotal.map (a' ≫ (X.W i ξ).ι).op ξ
  rw [Sigma.ι_desc, f_app, X.map_comp_apply', hφ, ← X.map_comp_apply']

lemma f_app_id (i : ι) :
    (X.f i).app (op (Spec (CommRingCat.of (S i)))) (𝟙 (Spec (CommRingCat.of (S i)))) =
      ⟨strMap R (S i), X.ev (S i) ((X.chart i (S i)).symm (AlgHom.id R (S i))).1⟩ := by
  rw [f_app, op_id, Functor.map_id_apply]
  rfl

theorem main : ∃ f : ∀ i, yoneda.obj (Spec (CommRingCat.of (S i))) ⟶ X.G.overTotal,
    (∀ i, IsOpenImmersion.presheaf (f i)) ∧
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) ∧
    ∀ i, (f i).app (op (Spec (CommRingCat.of (S i)))) (𝟙 (Spec (CommRingCat.of (S i)))) =
      ⟨strMap R (S i), X.ev (S i) ((X.chart i (S i)).symm (AlgHom.id R (S i))).1⟩ :=
  ⟨X.f, X.isOpenImmersion_presheaf, X.isLocallySurjective, X.f_app_id⟩

end Ctx
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart.GrassH2.Ctx"

end GrassH2
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart.GrassH2.Ctx P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart.GrassH2"

theorem solution
    (R : Type) [CommRing R]
    (F : ∀ (A : Type) [CommRing A] [Algebra R A], Type)
    (Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B)
    (Fmap_id : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), Fmap A A (AlgHom.id R A) s = s)
    (Fmap_comp : ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B]
      [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (s : F A),
      Fmap A C (ψ.comp φ) s = Fmap B C ψ (Fmap A B φ s))
    (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type)
    (ev : ∀ (A : Type) [CommRing A] [Algebra R A],
      F A ≃ G.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))))))
    (hG : Presheaf.IsSheaf Scheme.zariskiTopology G.overTotal)
    (hev : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (s : F A)
      (h : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
        Spec.map (CommRingCat.ofHom (algebraMap R B))),
      ev B (Fmap A B φ s) =
        G.map (Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) h :
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))).op (ev A s))
    (ι : Type) (P : ι → ∀ (A : Type) [CommRing A] [Algebra R A], F A → Prop)
    (isOpen : ∀ (i : ι) (A : Type) [CommRing A] [Algebra R A] (s : F A),
      ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
        ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
          P i B (Fmap A B φ s) ↔ Set.range (PrimeSpectrum.comap φ.toRingHom) ⊆ U)
    (S : ι → Type) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (chart : ∀ (i : ι) (A : Type) [CommRing A] [Algebra R A], {s : F A // P i A s} ≃ (S i →ₐ[R] A))
    (chart_natural : ∀ (i : ι) (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (φ : A →ₐ[R] B) (s : {s : F A // P i A s}) (h : P i B (Fmap A B φ s.1)),
      chart i B ⟨Fmap A B φ s.1, h⟩ = φ.comp (chart i A s))
    (cover : ∀ (K : Type) [Field K] [Algebra R K] (s : F K), ∃ i, P i K s) :
    ∃ f : ∀ i, yoneda.obj (Spec (CommRingCat.of (S i))) ⟶ G.overTotal,
      (∀ i, IsOpenImmersion.presheaf (f i)) ∧
      Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) ∧
      ∀ i, (f i).app (op (Spec (CommRingCat.of (S i)))) (𝟙 (Spec (CommRingCat.of (S i)))) =
        ⟨Spec.map (CommRingCat.ofHom (algebraMap R (S i))),
          ev (S i) ((chart i (S i)).symm (AlgHom.id R (S i))).1⟩ :=
  GrassH2.Ctx.main (R := R) (ι := ι) (S := S)
    ⟨F, Fmap, Fmap_id, Fmap_comp, G, ev, hG, hev, P, isOpen, chart, chart_natural, cover⟩

end S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart (solution)
