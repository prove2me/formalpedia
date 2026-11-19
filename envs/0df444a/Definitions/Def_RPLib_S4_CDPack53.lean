-- Prove2me | Definitions.Def_RPLib_S4_CDPack53
-- name    : RPLib_S4_CDPack53
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:08:23.720317+00:00
-- url     : https://prove2.me/theorems/24c12d60-0069-435a-95d0-1726efe6186e
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 53 of 71
-- statement:
--   Part 53 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_IntersectC_Flat`: S4-IntersectC, file Flat: dominant endomorphisms are flat (L35, O3)
--   * `Def_RP_IntersectC_Deg`: S4-IntersectC, file Deg: the rank of a dominant endomorphism is its degree (L35, O4)
--   * `Def_RP_IntersectC_Proj`: S4-IntersectC, file Proj: pulling divisors back along a dominant endomorphism (L35, O5)
--   * `Def_RP_IntersectC_NonDom`: S4-IntersectC, file NonDom: the projection formula (L35, O6)
--   * `Def_RP_IntersectC_Pit`: S4-IntersectC, file Pit: Krull's height theorem on a scheme (L36, O8)
--   * `Def_RP_IntersectC_Pit2`: S4-IntersectC, file Pit2: Krull at translated intersections; many `k`-points (L36, O8)
--   * `Def_RP_IntersectC_Dense`: S4-IntersectC, file Dense: translates of a separating divisor are dense (L36, O7)
--   * `Def_RP_IntersectC_Pos`: S4-IntersectC, file Pos: positivity of the self-intersection (L36, O9)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack51
import Definitions.Def_RPLib_S4_CDPack49
import Definitions.Def_RPLib_S4_CDPack52
import Definitions.Def_RPLib_S4_CDPack47
import Definitions.Def_RPLib_S4_CDPack45
import Definitions.Def_RPLib_S4_CDPack50

/-!
# Curve-duality library package, part 53 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_IntersectC_Flat`: S4-IntersectC, file Flat: dominant endomorphisms are flat (L35, O3)
* `Def_RP_IntersectC_Deg`: S4-IntersectC, file Deg: the rank of a dominant endomorphism is its degree (L35, O4)
* `Def_RP_IntersectC_Proj`: S4-IntersectC, file Proj: pulling divisors back along a dominant endomorphism (L35, O5)
* `Def_RP_IntersectC_NonDom`: S4-IntersectC, file NonDom: the projection formula (L35, O6)
* `Def_RP_IntersectC_Pit`: S4-IntersectC, file Pit: Krull's height theorem on a scheme (L36, O8)
* `Def_RP_IntersectC_Pit2`: S4-IntersectC, file Pit2: Krull at translated intersections; many `k`-points (L36, O8)
* `Def_RP_IntersectC_Dense`: S4-IntersectC, file Dense: translates of a separating divisor are dense (L36, O7)
* `Def_RP_IntersectC_Pos`: S4-IntersectC, file Pos: positivity of the self-intersection (L36, O9)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_IntersectC_Flat =====
section

/-!
# S4-IntersectC, file Flat: dominant endomorphisms are flat (L35, O3)

* `flat_of_isField`: a ring map out of a field is flat.
* `stalkMap_flat_of_conj`: flatness at a point is invariant under conjugation by automorphisms.
* `flat_left`: a dominant endomorphism `φ` of a group variety is flat (homogeneity: flat over the
  generic point, hence over an open set, and the translates of that open set cover `A`).
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA RamanujanPetersson.IntersectB

/-- A ring map out of a field is flat. -/
theorem flat_of_isField {R S : CommRingCat.{u}} (f : R ⟶ S) (hR : IsField R) : f.hom.Flat := by
  letI := hR.toField
  letI := f.hom.toAlgebra
  show Module.Flat R S
  infer_instance

/-- Flatness of a stalk map is invariant under conjugation by automorphisms. -/
theorem stalkMap_flat_of_conj {X Y : Scheme.{u}} (t : X ⟶ X) (s : Y ⟶ Y) [IsIso t] [IsIso s]
    (φ : X ⟶ Y) (h : t ≫ φ = φ ≫ s) (z : X) (H : (φ.stalkMap (t z)).hom.Flat) :
    (φ.stalkMap z).hom.Flat := by
  have H2 : ((t ≫ φ).stalkMap z).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.Flat.respectsIso.cancel_right_isIso _ _).mpr H
  rw [h, Scheme.Hom.stalkMap_comp] at H2
  exact (RingHom.Flat.respectsIso.cancel_left_isIso _ _).mp H2

section Variety

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- (O3) A dominant endomorphism of a group variety is flat. -/
theorem flat_left (φ : A ⟶ A) [IsMonHom φ] [IsDominant φ.left] : Flat φ.left := by
  obtain ⟨-, hfin, hsurj⟩ := isogDeg_L24 A φ
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have hinv : ∀ (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) (z : A.left),
      (φ.left.stalkMap ((transl A a).left z)).hom.Flat → (φ.left.stalkMap z).hom.Flat := by
    intro a z H
    have := isIso_transl_left A a
    have := isIso_transl_left A (a ≫ φ)
    refine stalkMap_flat_of_conj (transl A a).left (transl A (a ≫ φ)).left φ.left ?_ z H
    rw [← Over.comp_left, transl_comp_hom, Over.comp_left]
  have hη : ∀ z, φ.left z = genericPoint A.left → (φ.left.stalkMap z).hom.Flat := by
    intro z hz
    apply flat_of_isField
    apply isField_stalk_of_closure_mem_irreducibleComponents
    rw [hz]
    simp [irreducibleComponents_eq_singleton]
  obtain ⟨V, hηV, -, hV⟩ := exists_flat_nbhd φ.left (genericPoint A.left)
    (φ.left.finite_preimage_singleton _) hη
  let U : Set A.left := ⋃ a, (transl A a).left ⁻¹' (φ.left ⁻¹' V)
  have hUo : IsOpen U := isOpen_iUnion fun a =>
    (V.isOpen.preimage φ.left.continuous).preimage (transl A a).left.continuous
  have hU : ∀ z, z ∈ U := by
    by_contra hne
    push_neg at hne
    obtain ⟨c, hc⟩ := exists_pt_mem A Uᶜ hUo.isClosed_compl.isLocallyClosed hne
    obtain ⟨y, hy⟩ := hsurj (genericPoint A.left)
    obtain ⟨c0, hc0⟩ := exists_pt_mem A (φ.left ⁻¹' V)
      (V.isOpen.preimage φ.left.continuous).isLocallyClosed ⟨y, by simp [hy, hηV]⟩
    apply hc
    refine Set.mem_iUnion.mpr ⟨c⁻¹ * c0, ?_⟩
    show φ.left ((transl A (c⁻¹ * c0)).left (pt A c)) ∈ V
    rw [transl_pt, mul_inv_cancel_left]
    exact hc0
  refine Flat.of_stalkMap _ fun z => ?_
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hU z)
  exact hinv a z (hV _ ha)

end Variety

end RamanujanPetersson.IntersectC

end

-- ===== S4.Def_RP_IntersectC_Deg =====
section

/-!
# S4-IntersectC, file Deg: the rank of a dominant endomorphism is its degree (L35, O4)

* `finrank_eq_of_square`: along a commutative square of fraction fields, the degree of the
  fraction field extension equals the rank of the ring extension.
* `finrank_eq_degree`: for a dominant endomorphism `φ` of a group variety, `φ` (finite and flat)
  has rank `degree φ` at every point.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA RamanujanPetersson.IntersectB

/-- Along a commutative square `A → B`, `K → L` of fraction fields, `[L : K] = rank_A B`. -/
theorem finrank_eq_of_square {A B K L : Type u} [CommRing A] [CommRing B] [CommRing K]
    [CommRing L] (r : A →+* B) (gA : A →+* K) (gB : B →+* L) (m : K →+* L)
    (hc : m.comp gA = gB.comp r) (hA : @IsFractionRing A _ K _ gA.toAlgebra)
    (hB : @IsFractionRing B _ L _ gB.toAlgebra) :
    @Module.finrank K L _ _ m.toAlgebra.toModule = @Module.finrank A B _ _ r.toAlgebra.toModule := by
  letI := r.toAlgebra
  letI := gA.toAlgebra
  letI := gB.toAlgebra
  letI := m.toAlgebra
  letI : Algebra A L := (gB.comp r).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hc x).symm
  haveI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact IsFractionRing.finrank_eq A K B L

/-- The rank of a finite flat ring map out of a domain is its `finrank`. -/
theorem ringHom_finrank_eq {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] (r : R →+* S)
    (hf : r.Finite) (hfl : r.Flat) (p : PrimeSpectrum R) :
    r.finrank p = @Module.finrank R S _ _ r.toAlgebra.toModule := by
  letI := r.toAlgebra
  haveI : Module.Finite R S := hf
  haveI : Module.Flat R S := hfl
  rw [RingHom.finrank, ← Ideal.finrank_fiber_eq_rankAtStalk, Ideal.finrank_fiber_eq_finrank]

section Variety

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- (O4) A dominant endomorphism of a group variety has rank `degree φ` at every point. -/
theorem finrank_eq_degree (φ : A ⟶ A) [IsMonHom φ] [IsDominant φ.left] (x : A.left) :
    φ.left.finrank x = degree φ.left := by
  obtain ⟨hdeg, hfin, -⟩ := isogDeg_L24 A φ
  have hflat := flat_left A φ
  obtain ⟨V, hV, hηV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens
    (show genericPoint A.left ∈ (⊤ : A.left.Opens) from trivial)
  have hV' : IsAffineOpen V := hV
  have hW : IsAffineOpen (φ.left ⁻¹ᵁ V) := hV'.preimage φ.left
  have hηW : genericPoint A.left ∈ φ.left ⁻¹ᵁ V := by
    show φ.left (genericPoint A.left) ∈ V
    rw [map_genericPoint]
    exact hηV
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩
  haveI : Nonempty (φ.left ⁻¹ᵁ V) := ⟨⟨_, hηW⟩⟩
  have H : hW.fromSpec ≫ φ.left = Spec.map (φ.left.app V) ≫ hV'.fromSpec := by
    rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ.left hV' hW le_rfl]
  have hsq : IsPullback (Spec.map (φ.left.app V)) hW.fromSpec hV'.fromSpec φ.left :=
    IsOpenImmersion.isPullback _ _ _ _ H (by rw [hV'.opensRange_fromSpec, hW.opensRange_fromSpec])
  have hf1 : IsFinite (Spec.map (φ.left.app V)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip hfin
  have hf2 : Flat (Spec.map (φ.left.app V)) :=
    MorphismProperty.of_isPullback (P := @Flat) hsq.flip hflat
  have hrf : (φ.left.app V).hom.Finite := (IsFinite.SpecMap_iff _).mp hf1
  have hrfl : (φ.left.app V).hom.Flat := Flat.SpecMap_iff.mp hf2
  let p : PrimeSpectrum Γ(A.left, V) := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 : φ.left.finrank x = (φ.left.app V).hom.finrank p := by
    rw [finrank_const A φ.left x (hV'.fromSpec p),
      ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq.flip p,
      Scheme.Hom.finrank_SpecMap_eq_finrank hrf hrfl]
  rw [h1, ringHom_finrank_eq _ hrf hrfl p, hdeg]
  have hc := congrArg CommRingCat.Hom.hom (germ_ffMap_of_mem φ.left V hηV hηW)
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at hc
  exact (finrank_eq_of_square (φ.left.app V).hom (A.left.germToFunctionField V).hom
    (A.left.germToFunctionField (φ.left ⁻¹ᵁ V)).hom (ffMap φ.left).hom hc
    (functionField_isFractionRing_of_isAffineOpen A.left V hV')
    (functionField_isFractionRing_of_isAffineOpen A.left _ hW)).symm

end Variety

end RamanujanPetersson.IntersectC

end

-- ===== S4.Def_RP_IntersectC_Proj =====
section

/-!
# S4-IntersectC, file Proj: pulling divisors back along a dominant endomorphism (L35, O5)

* `Zid_comap`: translating the pullbacks `φ^* D_i` by `a_i` is pulling back the translates of
  `D_i` by `a_i φ`.
* `Pmap`: the endomorphism `φ × ⋯ × φ` of `A^n`; `Pmap_proj`, `ptOf_Pmap`.
* `exists_lift`: a dominant endomorphism is surjective on `k`-points.
* `inum_comap_dom`: `((φ^* D_1) ⋯ (φ^* D_g)) = deg φ · (D_1 ⋯ D_g)` for dominant `φ`.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj CartesianMonoidalCategory

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA RamanujanPetersson.IntersectB

section Pmap

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) (φ : A ⟶ A)

/-- The endomorphism `φ × ⋯ × φ` of `A^n`. -/
noncomputable def Pmap : (n : ℕ) → (Pw A n ⟶ Pw A n)
  | 0 => 𝟙 _
  | n + 1 => lift (fst (Pw A n) A ≫ Pmap n) (snd (Pw A n) A ≫ φ)

theorem Pmap_succ_fst (n : ℕ) :
    Pmap A φ (n + 1) ≫ fst (Pw A n) A = fst (Pw A n) A ≫ Pmap A φ n :=
  lift_fst _ _

theorem Pmap_succ_snd (n : ℕ) : Pmap A φ (n + 1) ≫ snd (Pw A n) A = snd (Pw A n) A ≫ φ :=
  lift_snd _ _

theorem Pmap_proj (n : ℕ) (i : Fin n) : Pmap A φ n ≫ proj A n i = proj A n i ≫ φ := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.lastCases with
    | last => rw [proj_last]; exact Pmap_succ_snd A φ n
    | cast j =>
      rw [proj_castSucc]
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ proj A n j) (Pmap_succ_fst A φ n))).trans
        ((Category.assoc _ _ _).trans ((congrArg (fst (Pw A n) A ≫ ·) (ih j)).trans
          (Category.assoc _ _ _).symm))

theorem ptOf_Pmap (n : ℕ) (b : Fin n → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ptOf A n b ≫ Pmap A φ n = ptOf A n (fun i => b i ≫ φ) := by
  rw [← ptOf_comp_proj A n (ptOf A n b ≫ Pmap A φ n)]
  congr 1
  funext i
  rw [Category.assoc, Pmap_proj, ← Category.assoc, ptOf_proj]

end Pmap

section Variety

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Translating the pullbacks `φ^* D_i` by `a_i` is pulling back the translates by `a_i φ`. -/
theorem Zid_comap {g : ℕ} (φ : A ⟶ A) [IsMonHom φ] (D : Fin g → A.left.IdealSheafData)
    (a : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    Zid A (fun i => (D i).comap φ.left) a = (Zid A D (fun i => a i ≫ φ)).comap φ.left := by
  simp only [Zid]
  rw [(Scheme.IdealSheafData.map_gc φ.left).l_iSup]
  congr 1
  funext i
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, ← Over.comp_left,
    transl_comp_hom, Over.comp_left]

variable [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left]

/-- A dominant endomorphism is surjective on `k`-points. -/
theorem exists_lift (φ : A ⟶ A) [IsMonHom φ] [IsDominant φ.left]
    (c : 𝟙_ (Over (Spec (.of k))) ⟶ A) : ∃ b, b ≫ φ = c := by
  have := isFinite_left A φ
  obtain ⟨x, hx⟩ := (surjective_of_isDominant A φ).surj (pt A c)
  obtain ⟨b, rfl⟩ := exists_pt_eq A x (isClosed_of_mem_fiber φ.left _ (isClosed_pt A c) x hx)
  exact ⟨b, pt_injective A (by rw [pt_comp]; exact hx)⟩

/-- **L35** (dominant case): `((φ^* D_1) ⋯ (φ^* D_g)) = deg φ · (D_1 ⋯ D_g)`. -/
theorem inum_comap_dom (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) (φ : A ⟶ A) [IsMonHom φ]
    [IsDominant φ.left] (hD' : ∀ i, ((D i).comap φ.left).support ≠ ⊤) :
    inum A g hdim (fun i => (D i).comap φ.left) hD' = degree φ.left * inum A g hdim D hD := by
  obtain ⟨U, hU, hne, hUs⟩ := inum_spec A g hdim D hD
  have := flat_left A φ
  have := isFinite_left A φ
  refine (inum_unique A g hdim _ hD' _ ((Pmap A φ g).left ⁻¹' U)
    (hU.preimage (Pmap A φ g).left.continuous) ?_ ?_).symm
  · have := isProper_Pw A g
    obtain ⟨c', hc'⟩ := exists_pt_mem (Pw A g) U hU.isLocallyClosed hne
    choose b hb using fun i => exists_lift A φ (c' ≫ proj A g i)
    refine ⟨pt (Pw A g) (ptOf A g b), ?_⟩
    show (Pmap A φ g).left (pt (Pw A g) (ptOf A g b)) ∈ U
    rw [← pt_comp, ptOf_Pmap, funext hb, ptOf_comp_proj]
    exact hc'
  · intro c hc
    have hc' : pt (Pw A g) (c ≫ Pmap A φ g) ∈ U := by rw [pt_comp]; exact hc
    obtain ⟨hfin, hlen⟩ := hUs _ hc'
    have hZ : Zid A (fun i => (D i).comap φ.left) (fun i => c ≫ proj A g i) =
        (Zid A D (fun i => (c ≫ Pmap A φ g) ≫ proj A g i)).comap φ.left := by
      rw [Zid_comap]
      congr 2
      funext i
      rw [Category.assoc, Category.assoc, Pmap_proj]
    obtain ⟨V, hV⟩ := exists_affine_mem A hfin.toFinset
    rw [hZ, len_comap_flat A _ V (fun x hx => hV x (hfin.mem_toFinset.2 hx)) hfin φ.left
      (Over.w φ) _ (finrank_eq_degree A φ), hlen]

end Variety

end RamanujanPetersson.IntersectC

end

-- ===== S4.Def_RP_IntersectC_NonDom =====
section

/-!
# S4-IntersectC, file NonDom: the projection formula (L35, O6)

* `inum_comap_nondom`: for non-dominant `φ`, `((φ^* D_1) ⋯ (φ^* D_g)) = 0`: a generic translated
  intersection of the pullbacks is stable under the (infinite) kernel, hence empty.
* `inum_comap`: **L35**, `((φ^* D_1) ⋯ (φ^* D_g)) = deg φ · (D_1 ⋯ D_g)`.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj CartesianMonoidalCategory

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA RamanujanPetersson.IntersectB

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- **L35** (non-dominant case): the pullbacks along a non-dominant `φ` have intersection `0`. -/
theorem inum_comap_nondom (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (φ : A ⟶ A) [IsMonHom φ] (h : ¬ IsDominant φ.left)
    (hD' : ∀ i, ((D i).comap φ.left).support ≠ ⊤) :
    inum A g hdim (fun i => (D i).comap φ.left) hD' = 0 := by
  have hinf : Infinite (kerPts A φ) :=
    (IsogDegB.degree_eq_zero_iff φ).mp (isogDeg_L24_zero A φ h)
  obtain ⟨U, hU, hne, hUs⟩ := inum_spec A g hdim _ hD'
  have := isProper_Pw A g
  obtain ⟨c, hc⟩ := exists_pt_mem (Pw A g) U hU.isLocallyClosed hne
  obtain ⟨hfin, hlen⟩ := hUs c hc
  rw [← hlen]
  set J := Zid A (fun i => (D i).comap φ.left) (fun i => c ≫ proj A g i) with hJ
  have hS : ∀ x, x ∈ (J.support : Set A.left) ↔
      φ.left x ∈ ((Zid A D (fun i => (c ≫ proj A g i) ≫ φ)).support : Set A.left) := by
    intro x
    rw [hJ, Zid_comap, Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Set.mem_preimage]
  have hempty : (J.support : Set A.left) = ∅ := by
    by_contra hne'
    obtain ⟨b, hb⟩ := exists_pt_mem A _ J.support.isClosed.isLocallyClosed
      (Set.nonempty_iff_ne_empty.2 hne')
    have hmaps : ∀ κ : kerPts A φ, pt A (b * κ.1) ∈ (J.support : Set A.left) := by
      intro κ
      rw [hS, ← pt_comp, mul_comp, κ.2, _root_.mul_one, pt_comp, ← hS]
      exact hb
    have hinj : Function.Injective
        (fun κ : kerPts A φ => (⟨pt A (b * κ.1), hmaps κ⟩ : (J.support : Set A.left))) := by
      intro κ κ' hk
      have h1 : pt A (b * κ.1) = pt A (b * κ'.1) := congrArg Subtype.val hk
      exact Subtype.ext (_root_.mul_left_cancel (pt_injective A h1))
    have : Infinite (J.support : Set A.left) := Infinite.of_injective _ hinj
    exact (Set.infinite_coe_iff.mp this) hfin
  have hJtop : J = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    ext1
    exact hempty
  rw [hJtop, len_top]

/-- **L35** (projection formula): `((φ^* D_1) ⋯ (φ^* D_g)) = deg φ · (D_1 ⋯ D_g)`, where
`deg φ = 0` for non-dominant `φ`. -/
theorem inum_comap (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) (φ : A ⟶ A) [IsMonHom φ]
    (hD' : ∀ i, ((D i).comap φ.left).support ≠ ⊤) :
    inum A g hdim (fun i => (D i).comap φ.left) hD' = degree φ.left * inum A g hdim D hD := by
  by_cases h : IsDominant φ.left
  · exact inum_comap_dom A g hdim D hD φ hD'
  · rw [isogDeg_L24_zero A φ h, zero_mul]
    exact inum_comap_nondom A g hdim D φ h hD'

end RamanujanPetersson.IntersectC

end

-- ===== S4.Def_RP_IntersectC_Pit =====
section

/-!
# S4-IntersectC, file Pit: Krull's height theorem on a scheme (L36, O8)

* `exists_gen_of_span`: if `J` is generated on an affine chart by `i` sections and `y` lies in
  its support with `i < coheight y`, some other point of the support generalizes `y`.
* `exists_span_of_iSup`: a finite sup of locally principal ideal sheaves is generated, near any
  point, by one section per term.
* `locPrin_comap_iso`: pulling back along an isomorphism keeps an ideal sheaf locally principal.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.IntersectB

/-- **Krull** on a chart: a support point `y` of codimension `> i` of an ideal sheaf generated by `i`
sections has a proper generalization in the support. -/
theorem exists_gen_of_span {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (W : X.affineOpens) {y : X} (hyW : y ∈ (W : X.Opens)) {i : ℕ} (v : Fin i → Γ(X, W))
    (hv : J.ideal W = Ideal.span (Set.range v)) (hy : y ∈ (J.support : Set X))
    (hi : (i : ℕ∞) < Order.coheight y) :
    ∃ z ∈ (J.support : Set X), z ≠ y ∧ z ⤳ y := by
  classical
  have hW := W.2
  have := hW.isOpenImmersion_fromSpec
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian W
  set m := hW.primeIdealOf ⟨y, hyW⟩ with hm
  have hmy : hW.fromSpec m = y := hW.fromSpec_primeIdealOf ⟨y, hyW⟩
  have hmem : ∀ q, hW.fromSpec q ∈ (W : X.Opens) := fun q => by
    have h := Set.mem_range_self (f := hW.fromSpec) q
    rw [hW.range_fromSpec] at h
    exact h
  have hsupp : ∀ q : PrimeSpectrum Γ(X, W),
      hW.fromSpec q ∈ (J.support : Set X) ↔ J.ideal W ≤ q.asIdeal := by
    intro q
    change hW.fromSpec q ∈ J.support ↔ _
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (hmem q)]
    exact (Set.ext_iff.mp (hW.fromSpec_preimage_zeroLocus (J.ideal W : Set Γ(X, W))) q).trans
      ((PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe)
  have hIm : J.ideal W ≤ m.asIdeal := (hsupp m).1 (hmy ▸ hy)
  obtain ⟨p, hpmin, hpm⟩ := Ideal.exists_minimalPrimes_le hIm
  have hpprime : p.IsPrime := hpmin.1.1
  have hpi : p.height ≤ i := by
    have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset (s := Finset.univ.image v)
      (p := p) (by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← hv]; exact hpmin)
    have hc : (Finset.univ.image v).card ≤ i :=
      Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
    exact h1.trans (by exact_mod_cast hc)
  letI := X.presheaf.algebra_section_stalk (⟨y, hyW⟩ : (W : X.Opens))
  have hloc := hW.isLocalization_stalk ⟨y, hyW⟩
  have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal
    (X.presheaf.stalk ((⟨y, hyW⟩ : (W : X.Opens)) : X))
  have h2 := ringKrullDim_stalk_eq_coheight ((⟨y, hyW⟩ : (W : X.Opens)) : X)
  have hmh : m.asIdeal.height = Order.coheight y := WithBot.coe_inj.mp (h1.symm.trans h2)
  have hpm' : p ≠ m.asIdeal := by
    rintro rfl
    rw [hmh] at hpi
    exact absurd hi (not_lt.2 hpi)
  refine ⟨hW.fromSpec ⟨p, hpprime⟩, (hsupp _).2 hpmin.1.2, fun h => ?_, ?_⟩
  · rw [← hmy] at h
    exact hpm' (congrArg PrimeSpectrum.asIdeal (hW.fromSpec.isOpenEmbedding.injective h))
  · rw [← hmy]
    exact ((PrimeSpectrum.le_iff_specializes ⟨p, hpprime⟩ m).1 hpm).map hW.fromSpec.continuous

/-- A finite sup of locally principal ideal sheaves is locally generated by one section per term. -/
theorem exists_span_of_iSup {X : Scheme.{u}} {n : ℕ} (I : Fin n → X.IdealSheafData)
    (hI : ∀ j (x : X), ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧
      ∃ u, (I j).ideal W = Ideal.span {u}) (x : X) :
    ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧
      ∃ v : Fin n → Γ(X, W), (⨆ j, I j).ideal W = Ideal.span (Set.range v) := by
  choose W hxW u hu using fun j => hI j x
  let O : X.Opens := ⟨⋂ j, ((W j : X.Opens) : Set X), isOpen_iInter_of_finite fun j => (W j).1.2⟩
  have hxO : x ∈ O := Set.mem_iInter.mpr hxW
  obtain ⟨W0, hW0, hxW0, hle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxO
  have hle' : ∀ j, (⟨W0, hW0⟩ : X.affineOpens) ≤ W j := fun j z hz => Set.mem_iInter.mp (hle hz) j
  refine ⟨⟨W0, hW0⟩, hxW0, fun j => X.presheaf.map (homOfLE (hle' j)).op (u j), ?_⟩
  rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply, ← Set.iUnion_singleton_eq_range,
    Ideal.span_iUnion]
  exact iSup_congr fun j => ideal_res_span (I j) (hle' j) (hu j)

/-- Pulling back along an isomorphism keeps an ideal sheaf locally principal. -/
theorem locPrin_comap_iso {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) [IsIso f]
    (hI : ∀ y : Y, ∃ W : Y.affineOpens, y ∈ (W : Y.Opens) ∧ ∃ u, I.ideal W = Ideal.span {u})
    (x : X) : ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧ ∃ u, (I.comap f).ideal W = Ideal.span {u} := by
  obtain ⟨W, hxW, u, hu⟩ := hI (f x)
  let W' : X.affineOpens := ⟨f ⁻¹ᵁ W, W.2.preimage f⟩
  let W'' : Y.affineOpens := ⟨f ''ᵁ (W' : X.Opens), W'.2.image_of_isOpenImmersion f⟩
  have hle : W'' ≤ W := f.image_preimage_le W
  let σ : Γ(Y, (W'' : Y.Opens)) ≃+* Γ(X, (W' : X.Opens)) :=
    (f.appIso (W' : X.Opens)).commRingCatIsoToRingEquiv
  refine ⟨W', hxW, σ (Y.presheaf.map (homOfLE hle).op u), ?_⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, ideal_res_span I hle hu]
  change Ideal.comap (σ.symm : Γ(X, (W' : X.Opens)) →+* Γ(Y, (W'' : Y.Opens))) _ = _
  rw [Ideal.comap_coe, Ideal.comap_symm, Ideal.map_span, Set.image_singleton]

end RamanujanPetersson.IntersectC

end

-- ===== S4.Def_RP_IntersectC_Pit2 =====
section

/-!
# S4-IntersectC, file Pit2: Krull at translated intersections; many `k`-points (L36, O8)

* `infinite_pts`: a closed set containing a proper specialization `z ⤳ y` has infinitely many
  `k`-points (Jacobson).
* `locPrin_effI`: the ideal sheaf of an effective Weil divisor is locally principal.
* `pit_transl`: a point of codimension `> i` in the intersection of `i` translates of `effI D` has a
  proper generalization in that intersection.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj CartesianMonoidalCategory
  TopologicalSpace

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA
  RamanujanPetersson.IntersectB

/-- The ideal sheaf of an effective Weil divisor is locally principal. -/
theorem locPrin_effI {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {D : AlgebraicCycle X ℤ} (hD : D ∈ weilDivisors X) (hfin : (Function.support D).Finite)
    (x : X) : ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧ ∃ u, (effI D).ideal W = Ideal.span {u} := by
  obtain ⟨W, hxW, u, -, hu, -⟩ := effGen hufd hD hfin x
  exact ⟨W, hxW, u, hu⟩

section Pts

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k)))
  [LocallyOfFiniteType A.hom]

/-- A closed set containing a proper specialization has infinitely many `k`-points. -/
theorem infinite_pts (S : Set A.left) (hS : IsClosed S) {y z : A.left} (hzS : z ∈ S)
    (hzy : z ⤳ y) (hne : z ≠ y) :
    {b : 𝟙_ (Over (Spec (.of k))) ⟶ A | pt A b ∈ S}.Infinite := by
  intro hfin
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hsub : closure {z} ∩ closedPoints A.left ⊆ pt A '' {b | pt A b ∈ S} := by
    rintro x ⟨hx, hxc⟩
    obtain ⟨b, rfl⟩ := exists_pt_eq A x hxc
    exact ⟨b, closure_minimal (Set.singleton_subset_iff.2 hzS) hS hx, rfl⟩
  have hT : (closure {z} ∩ closedPoints A.left).Finite := (hfin.image (pt A)).subset hsub
  have hTc : IsClosed (closure {z} ∩ closedPoints A.left) := by
    rw [← Set.biUnion_of_singleton (closure {z} ∩ closedPoints A.left)]
    exact hT.isClosed_biUnion fun x hx => hx.2
  have h1 := closure_inter_closedPoints (X := A.left) (isClosed_closure (s := {z}))
  rw [hTc.closure_eq] at h1
  have hz : z ∈ closure {z} ∩ closedPoints A.left := by
    rw [h1]; exact subset_closure (Set.mem_singleton z)
  have hzc : IsClosed ({z} : Set A.left) := hz.2
  have hy : y ∈ closure ({z} : Set A.left) := specializes_iff_mem_closure.mp hzy
  rw [hzc.closure_eq] at hy
  exact hne (Set.mem_singleton_iff.mp hy).symm

end Pts

section Transl

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- **Krull at translates**: a point of codimension `> i` in the intersection of `i` translates of
`effI D` has a proper generalization in that intersection. -/
theorem pit_transl [IsIntegral A.left] [IsLocallyNoetherian A.left]
    (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    {D : AlgebraicCycle A.left ℤ} (hD : D ∈ weilDivisors A.left)
    (hfin : (Function.support D).Finite) {i : ℕ}
    (a : Fin i → (𝟙_ (Over (Spec (.of k))) ⟶ A)) {y : A.left}
    (hy : y ∈ ((Zid A (fun _ => effI D) a).support : Set A.left))
    (hi : (i : ℕ∞) < Order.coheight y) :
    ∃ z ∈ ((Zid A (fun _ => effI D) a).support : Set A.left), z ≠ y ∧ z ⤳ y := by
  have hI : ∀ (j : Fin i) (x : A.left), ∃ W : A.left.affineOpens, x ∈ (W : A.left.Opens) ∧
      ∃ u, ((effI D).comap (transl A (a j)).left).ideal W = Ideal.span {u} := fun j x => by
    have := isIso_translL A (a j)
    exact locPrin_comap_iso _ _ (locPrin_effI hufd hD hfin) x
  obtain ⟨W, hyW, v, hv⟩ := exists_span_of_iSup _ hI y
  exact exists_gen_of_span (Zid A (fun _ => effI D) a) W hyW v hv hy hi

end Transl

end RamanujanPetersson.IntersectC

end

-- ===== S4.Def_RP_IntersectC_Dense =====
section

/-!
# S4-IntersectC, file Dense: translates of a separating divisor are dense (L36, O7)

* `mem_support_effI_of_pos`: a point with positive coefficient lies in `supp (effI D)`.
* `coheight_iso`: isomorphisms of schemes keep the codimension of points.
* `finite_coheight_one`: a proper closed subset of an irreducible Noetherian scheme has finitely many
  points of codimension one.
* `transl_dense`: if the right translates of `supp D` separate `k`-points, the left translates of
  `supp D` by any infinite set of `k`-points are dense.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj CartesianMonoidalCategory
  TopologicalSpace

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA
  RamanujanPetersson.IntersectB

section Top

variable {X : Scheme.{u}}

/-- A point with positive coefficient lies in the support of `effI D`. -/
lemma mem_support_effI_of_pos (D : AlgebraicCycle X ℤ) (hfin : (Function.support D).Finite)
    {z : X} (hz : 0 < D z) : z ∈ ((effI D).support : Set X) := by
  classical
  have hmem : z ∈ hfin.toFinset := hfin.mem_toFinset.mpr hz.ne'
  rw [effI_eq_prod D hfin.toFinset fun w hw => hfin.mem_toFinset.mpr hw,
    ← Finset.prod_erase_mul _ _ hmem]
  simp only [Scheme.IdealSheafData.support_mul, Closeds.coe_sup, Set.mem_union]
  right
  rw [(primeI z).support_pow _ (by omega), coe_support_primeI]
  exact subset_closure (Set.mem_singleton z)

/-- Isomorphisms of schemes keep the codimension of points. -/
lemma coheight_iso {Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (x : X) :
    Order.coheight (f x) = Order.coheight x :=
  Topology.IsOpenEmbedding.coheight_eq (x := x) f f.isOpenEmbedding

/-- A codimension-one point of a proper closed subset is maximal in it. -/
lemma eq_of_coheight_one [IrreducibleSpace X] {S : Set X} (hS : IsClosed S) (hne : S ≠ Set.univ)
    {p q : X} (hp : Order.coheight p = 1) (hq : q ∈ S) (hqp : q ⤳ p) : q = p := by
  by_contra hne'
  have hη : genericPoint X ∉ S := fun h => hne (Set.eq_univ_of_forall fun x =>
    (genericPoint_specializes x).mem_closed hS h)
  have h1 : p < q := lt_of_le_not_ge hqp fun h => hne' (Specializes.antisymm (show p ⤳ q from h) hqp).eq.symm
  have h2 : q < genericPoint X := lt_of_le_not_ge (genericPoint_specializes q) fun h =>
    hη ((show q ⤳ genericPoint X from h).mem_closed hS hq)
  have hq1 : 1 ≤ Order.coheight q := le_trans le_add_self (Order.coheight_add_one_le h2)
  have h4 : (1 : ℕ∞) + 1 ≤ Order.coheight q + 1 := by gcongr
  have h3 : (1 : ℕ∞) + 1 ≤ 1 := h4.trans ((Order.coheight_add_one_le h1).trans hp.le)
  exact absurd h3 (by norm_num)

/-- A proper closed subset of an irreducible Noetherian scheme has finitely many codimension-one
points. -/
lemma finite_coheight_one [IrreducibleSpace X] [NoetherianSpace X] {S : Set X} (hS : IsClosed S)
    (hne : S ≠ Set.univ) : {p | p ∈ S ∧ Order.coheight p = 1}.Finite := by
  obtain ⟨T, hT, hST⟩ := NoetherianSpace.exists_finset_irreducible (⟨S, hS⟩ : Closeds X)
  refine (T.finite_toSet.biUnion fun C _ =>
    Set.Subsingleton.finite (s := {p | IsGenericPoint p (C : Set X)})
      fun x hx y hy => IsGenericPoint.eq hx hy).subset ?_
  rintro p ⟨hpS, hp⟩
  have hpT : p ∈ ((T.sup id : Closeds X) : Set X) := by rw [← hST]; exact hpS
  rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂] at hpT
  obtain ⟨C, hCT, hpC⟩ := hpT
  have hgen := (hT ⟨C, hCT⟩).isGenericPoint_genericPoint C.isClosed
  have hCS : (C : Set X) ⊆ S := fun x hx => by
    have h : C ≤ T.sup id := Finset.le_sup (f := id) hCT
    rw [← hST] at h
    exact SetLike.coe_subset_coe.mpr h hx
  refine Set.mem_biUnion hCT ?_
  rw [← eq_of_coheight_one hS hne hp (hCS hgen.mem) (hgen.specializes hpC)]
  exact hgen

end Top

section Dense

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

omit [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left] in
theorem ltransl_inv_apply (w : 𝟙_ (Over (Spec (.of k))) ⟶ A) (x : A.left) :
    (ltransl A w).left ((ltransl A w⁻¹).left x) = x := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ltransl_comp_ltransl, _root_.mul_inv_cancel,
    ltransl_one, Over.id_left]
  try rfl

/-- **TranslDense** (L36 a): if the right translates of `supp D` separate `k`-points, the left
translates of `supp D` by an infinite set of `k`-points are dense. -/
theorem transl_dense {D : AlgebraicCycle A.left ℤ} (hW : D ∈ weilDivisors A.left)
    (hsep : ∀ b b' : 𝟙_ (Over (Spec (.of k))) ⟶ A, b ≠ b' → ∃ a,
      pt A (b * a) ∈ ((effI D).support : Set A.left) ∧
        pt A (b' * a) ∉ ((effI D).support : Set A.left))
    (Z : Set (𝟙_ (Over (Spec (.of k))) ⟶ A)) (hZ : Z.Infinite) :
    closure (⋃ w ∈ Z, (ltransl A w).left ⁻¹' ((effI D).support : Set A.left)) = Set.univ := by
  classical
  have := noetherianSpace_left A
  have hfin : (Function.support D).Finite := support_finite_of_compact D
  by_contra hne
  have hS := isClosed_closure (s := ⋃ w ∈ Z, (ltransl A w).left ⁻¹' ((effI D).support : Set A.left))
  have hPfin : {z : A.left | 0 < D z}.Finite := hfin.subset fun z (hz : 0 < D z) => hz.ne'
  have : Finite {z : A.left | 0 < D z} := hPfin.to_subtype
  have hmaps : Set.MapsTo (fun w (z : {z : A.left | 0 < D z}) => (ltransl A w⁻¹).left z) Z
      (Set.pi Set.univ fun _ => {p | p ∈ closure (⋃ w ∈ Z, (ltransl A w).left ⁻¹'
        ((effI D).support : Set A.left)) ∧ Order.coheight p = 1}) := by
    intro w hw z _
    refine ⟨subset_closure (Set.mem_biUnion hw ?_), ?_⟩
    · show (ltransl A w).left ((ltransl A w⁻¹).left z) ∈ ((effI D).support : Set A.left)
      rw [ltransl_inv_apply]
      exact mem_support_effI_of_pos D hfin z.2
    · have := isIso_ltransl_left A w⁻¹
      show Order.coheight ((ltransl A w⁻¹).left z) = 1
      rw [coheight_iso]
      exact hW z.1 (show 0 < D z.1 from z.2).ne'
  obtain ⟨w, -, w', -, hww, heq⟩ := hZ.exists_ne_map_eq_of_mapsTo hmaps
    (Set.Finite.pi fun _ => finite_coheight_one hS hne)
  have hc : ∀ z, 0 < D z → (ltransl A (w * w'⁻¹)).left z = z := fun z hz => by
    have h : (ltransl A w⁻¹).left z = (ltransl A w'⁻¹).left z := congrFun heq ⟨z, hz⟩
    rw [← ltransl_comp_ltransl, Over.comp_left, Scheme.Hom.comp_apply, ← h, ltransl_inv_apply]
  obtain ⟨a, ha, hca⟩ := hsep 1 (w * w'⁻¹) fun h => hww (_root_.mul_inv_eq_one.mp h.symm)
  rw [_root_.one_mul] at ha
  apply hca
  rw [← ltransl_pt]
  obtain ⟨z, hz, hza⟩ := mem_support_effI D hfin ha
  have h := (specializes_iff_mem_closure.mpr hza).map (ltransl A (w * w'⁻¹)).left.continuous
  rw [hc z hz] at h
  exact h.mem_closed (effI D).support.isClosed (mem_support_effI_of_pos D hfin hz)

end Dense

end RamanujanPetersson.IntersectC

end

-- ===== S4.Def_RP_IntersectC_Pos =====
section

/-!
# S4-IntersectC, file Pos: positivity of the self-intersection (L36, O9)

* `le_coheight_closed`: closed points have codimension `≥ g` (homogeneity).
* `len_pos`: a closed subscheme with finite nonempty support has positive length.
* `zid_nonempty`: `i ≤ g` translates of `supp D` always meet, when translates separate points.
* **L36** `inum_pos`: `0 < (D^g)` for an effective Weil divisor whose translates separate points.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj CartesianMonoidalCategory
  TopologicalSpace

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA
  RamanujanPetersson.IntersectB

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- Homogeneity: closed points have codimension `≥ g` when some point has height `≥ g`. -/
theorem le_coheight_closed {g : ℕ} (hg : ∃ x : A.left, (g : ℕ∞) ≤ Order.height x) (y : A.left)
    (hy : IsClosed ({y} : Set A.left)) : (g : ℕ∞) ≤ Order.coheight y := by
  obtain ⟨x, hx⟩ := hg
  obtain ⟨p, -, hp⟩ := Order.exists_series_of_le_height x hx
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨y0, hy0, hy0c⟩ := (isClosed_closure (s := {p.head})).exists_closed_singleton
    ⟨p.head, subset_closure (Set.mem_singleton _)⟩
  obtain ⟨a, ha⟩ := exists_transl_eq A y0 y hy0c hy
  have := isIso_translL A a
  rw [← ha, coheight_iso, ← hp]
  exact Order.length_le_coheight (x := y0) (p := p)
    (show p.head ⤳ y0 from specializes_iff_mem_closure.mpr hy0)

/-- A closed subscheme with finite nonempty support has positive length. -/
theorem len_pos (J : A.left.IdealSheafData) (hfin : (J.support : Set A.left).Finite)
    (hne : (J.support : Set A.left).Nonempty) : 0 < len A J := by
  obtain ⟨V, hV⟩ := exists_affine_mem A hfin.toFinset
  have hV' : (J.support : Set A.left) ⊆ V := fun x hx => hV x (hfin.mem_toFinset.mpr hx)
  obtain ⟨hfinite, hlen⟩ := len_eq_finrank A J V hV' hfin
  let _ := (algV A V).hom.toAlgebra
  rw [hlen]
  obtain ⟨x, hx⟩ := hne
  have hxV : x ∈ (V : A.left.Opens) := hV' hx
  have hne_top : J.ideal V ≠ ⊤ := fun htop => by
    have h := (Scheme.IdealSheafData.mem_support_iff_of_mem hxV).mp hx
    rw [Scheme.mem_zeroLocus_iff] at h
    exact h 1 (by rw [htop]; exact Submodule.mem_top)
      (by rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; exact hxV)
  have : Nontrivial (Γ(A.left, V) ⧸ J.ideal V) := Ideal.Quotient.nontrivial_iff.mpr hne_top
  exact Module.finrank_pos

/-- The slice `b ↦ (a', b)` of `A^(i+1) = A^i × A` over the point with coordinates `a'`. -/
noncomputable def slice {i : ℕ} (a' : Fin i → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    A ⟶ Pw A (i + 1) :=
  lift (toUnit A ≫ ptOf A i a') (𝟙 A)

theorem comp_slice {i : ℕ} (a' : Fin i → (𝟙_ (Over (Spec (.of k))) ⟶ A))
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ A) : b ≫ slice A a' = ptOf A (i + 1) (Fin.snoc a' b) := by
  change b ≫ lift (toUnit A ≫ ptOf A i a') (𝟙 A) =
    lift (ptOf A i (Fin.init (Fin.snoc a' b : Fin (i + 1) → _)))
      ((Fin.snoc a' b : Fin (i + 1) → _) (Fin.last i))
  rw [Fin.init_snoc, Fin.snoc_last, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit,
    toUnit_unit, Category.id_comp]

theorem mem_supp_snoc {i : ℕ} (E : A.left.IdealSheafData)
    (a' : Fin i → (𝟙_ (Over (Spec (.of k))) ⟶ A)) (b : 𝟙_ (Over (Spec (.of k))) ⟶ A) (x : A.left) :
    x ∈ ((Zid A (fun _ => E) (Fin.snoc a' b)).support : Set A.left) ↔
      x ∈ ((Zid A (fun _ => E) a').support : Set A.left) ∧
        (transl A b).left x ∈ (E.support : Set A.left) := by
  simp only [coe_support_Zid, Set.mem_iInter, Set.mem_preimage, Fin.forall_fin_succ',
    Fin.snoc_castSucc, Fin.snoc_last]

/-- One more translate still meets the intersection (induction step of L36). -/
theorem step (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x)) {g : ℕ}
    (hg : ∃ x : A.left, (g : ℕ∞) ≤ Order.height x) {D : AlgebraicCycle A.left ℤ}
    (hW : D ∈ weilDivisors A.left)
    (hsep : ∀ b b' : 𝟙_ (Over (Spec (.of k))) ⟶ A, b ≠ b' → ∃ a,
      pt A (b * a) ∈ ((effI D).support : Set A.left) ∧
        pt A (b' * a) ∉ ((effI D).support : Set A.left))
    {i : ℕ} (hi : i < g) (a' : Fin i → (𝟙_ (Over (Spec (.of k))) ⟶ A))
    (hne : ((Zid A (fun _ => effI D) a').support : Set A.left).Nonempty)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    ((Zid A (fun _ => effI D) (Fin.snoc a' b)).support : Set A.left).Nonempty := by
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hfin : (Function.support D).Finite := support_finite_of_compact D
  have hSc := (Zid A (fun _ => effI D) a').support.isClosed
  obtain ⟨w0, hw0⟩ := exists_pt_mem A _ hSc.isLocallyClosed hne
  obtain ⟨z, hzS, hz0, hzy⟩ := pit_transl A hufd hW hfin a' hw0
    (lt_of_lt_of_le (by exact_mod_cast hi) (le_coheight_closed A hg _ (isClosed_pt A w0)))
  have hZ := infinite_pts A _ hSc hzS hzy hz0
  have := isProper_famP A (fun _ : Fin (i + 1) => effI D)
  have hT : IsClosed ((slice A a').left ⁻¹' Set.range (famP A (fun _ : Fin (i + 1) => effI D))) :=
    (famP A _).isClosedMap.isClosed_range.preimage (slice A a').left.continuous
  have hmemT : ∀ b', pt A b' ∈ (slice A a').left ⁻¹' Set.range (famP A (fun _ : Fin (i + 1) => effI D))
      ↔ ((Zid A (fun _ => effI D) (Fin.snoc a' b')).support : Set A.left).Nonempty := fun b' => by
    show (slice A a').left (pt A b') ∈ Set.range (famP A (fun _ : Fin (i + 1) => effI D)) ↔ _
    rw [← pt_comp, comp_slice, mem_range_famP_iff]
    simp only [ptOf_proj]
  have hsub : (⋃ w ∈ {w | pt A w ∈ ((Zid A (fun _ => effI D) a').support : Set A.left)},
      (ltransl A w).left ⁻¹' ((effI D).support : Set A.left)) ⊆
        (slice A a').left ⁻¹' Set.range (famP A (fun _ : Fin (i + 1) => effI D)) := by
    refine Set.iUnion₂_subset fun w hw => ?_
    have hc : IsClosed ((ltransl A w).left ⁻¹' ((effI D).support : Set A.left)) :=
      (effI D).support.isClosed.preimage (ltransl A w).left.continuous
    rw [← closure_inter_closedPoints hc]
    refine closure_minimal ?_ hT
    rintro x ⟨hx, hxc⟩
    obtain ⟨b', rfl⟩ := exists_pt_eq A x hxc
    refine (hmemT b').2 ⟨pt A w, (mem_supp_snoc A _ a' b' _).2 ⟨hw, ?_⟩⟩
    rw [transl_pt, ← ltransl_pt]
    exact hx
  have hTu := closure_minimal hsub hT
  rw [transl_dense A hW hsep _ hZ] at hTu
  exact (hmemT b).1 (hTu (Set.mem_univ _))

/-- Up to `g` translates of `supp D` always meet. -/
theorem zid_nonempty (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    {g : ℕ} (hg : ∃ x : A.left, (g : ℕ∞) ≤ Order.height x) {D : AlgebraicCycle A.left ℤ}
    (hW : D ∈ weilDivisors A.left)
    (hsep : ∀ b b' : 𝟙_ (Over (Spec (.of k))) ⟶ A, b ≠ b' → ∃ a,
      pt A (b * a) ∈ ((effI D).support : Set A.left) ∧
        pt A (b' * a) ∉ ((effI D).support : Set A.left))
    (i : ℕ) (hi : i ≤ g) (a : Fin i → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ((Zid A (fun _ => effI D) a).support : Set A.left).Nonempty := by
  induction i with
  | zero =>
    exact ⟨genericPoint A.left, by
      rw [coe_support_Zid]; exact Set.mem_iInter.mpr fun j => j.elim0⟩
  | succ i ih =>
    rw [← Fin.snoc_init_self a]
    exact step A hufd hg hW hsep (by omega) _ (ih (by omega) _) _

/-- **L36**: `0 < (D^g)` for an effective Weil divisor `D` whose translates separate points. -/
theorem inum_pos (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    {g : ℕ} (hdim : ∀ x : A.left, Order.height x ≤ g)
    (hg : ∃ x : A.left, (g : ℕ∞) ≤ Order.height x) {D : AlgebraicCycle A.left ℤ}
    (hW : D ∈ weilDivisors A.left) (hE : (effI D).support ≠ ⊤)
    (hsep : ∀ b b' : 𝟙_ (Over (Spec (.of k))) ⟶ A, b ≠ b' → ∃ a,
      pt A (b * a) ∈ ((effI D).support : Set A.left) ∧
        pt A (b' * a) ∉ ((effI D).support : Set A.left)) :
    0 < inum A g hdim (fun _ => effI D) (fun _ => hE) := by
  have := isProper_Pw A g
  obtain ⟨U, hU, hUne, hspec⟩ := inum_spec A g hdim (fun _ => effI D) (fun _ => hE)
  obtain ⟨c, hc⟩ := exists_pt_mem (Pw A g) U hU.isLocallyClosed hUne
  obtain ⟨hfin, hlen⟩ := hspec c hc
  rw [← hlen]
  exact len_pos A _ hfin (zid_nonempty A hufd hg hW hsep g le_rfl _)

end RamanujanPetersson.IntersectC

end


