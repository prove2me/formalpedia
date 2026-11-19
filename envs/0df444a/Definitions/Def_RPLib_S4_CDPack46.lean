-- Prove2me | Definitions.Def_RPLib_S4_CDPack46
-- name    : RPLib_S4_CDPack46
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:35:12.273298+00:00
-- url     : https://prove2.me/theorems/480c5e8e-a18e-44f0-aea6-141ba42c7202
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 46 of 71
-- statement:
--   Part 46 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_IntersectA_PwInst`: S4-IntersectA, file PwInst: the parameter space `A^n` and the family over it
--   * `Def_RP_IntersectA`: S4-IntersectA: intersection numbers at generic translates (L31-L32)
--   * `Def_RP_IntersectB_Sym`: S4-IntersectB, file Sym: symmetry and translation invariance of `inum` (L33, part 1)
--   * `Def_RP_IntersectB_Aff`: S4-IntersectB, file Aff: affine charts for finite subschemes (L33, part 2)
--   * `Def_RP_IntersectB_Add_Ring`: S4-IntersectB, file Add_Ring: the chart step of additivity (L33, B3 core)
--   * `Def_RP_IntersectB_Add`: S4-IntersectB, file Add: additivity of `inum` in the first slot (L33, B3)
--   * `Def_RP_JacDivisors_Q`: S4-JacDivisors Q (O14, steps E9-E10: Weil's extension theorem, Milne I.3.1-3.2)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack45
import Definitions.Def_RPLib_S4_CDPack25
import Definitions.Def_RPLib_S4_CDPack38

/-!
# Curve-duality library package, part 46 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_IntersectA_PwInst`: S4-IntersectA, file PwInst: the parameter space `A^n` and the family over it
* `Def_RP_IntersectA`: S4-IntersectA: intersection numbers at generic translates (L31-L32)
* `Def_RP_IntersectB_Sym`: S4-IntersectB, file Sym: symmetry and translation invariance of `inum` (L33, part 1)
* `Def_RP_IntersectB_Aff`: S4-IntersectB, file Aff: affine charts for finite subschemes (L33, part 2)
* `Def_RP_IntersectB_Add_Ring`: S4-IntersectB, file Add_Ring: the chart step of additivity (L33, B3 core)
* `Def_RP_IntersectB_Add`: S4-IntersectB, file Add: additivity of `inum` in the first slot (L33, B3)
* `Def_RP_JacDivisors_Q`: S4-JacDivisors Q (O14, steps E9-E10: Weil's extension theorem, Milne I.3.1-3.2)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_IntersectA_PwInst =====
section

/-!
# S4-IntersectA, file PwInst: the parameter space `A^n` and the family over it

`A^n` is proper over `k`, integral (`isIntegral_pullback`) and locally Noetherian; `A` is a
Noetherian space. The family `famP A D` is proper, and its fibre over the point with coordinates
`a0` is finite once the intersection `Zid A D a0` has finite support (`finite_fibre`).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits
  TopologicalSpace

namespace RamanujanPetersson.IntersectA

open RamanujanPetersson.IsogDegA

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

theorem isProper_Pw [IsProper A.hom] (n : ℕ) : IsProper (Pw A n).hom := by
  induction n with
  | zero => exact (inferInstance : IsProper (𝟙 (Spec (.of k))))
  | succ n ih =>
    have := ih
    exact (inferInstance : IsProper (pullback.fst (Pw A n).hom A.hom ≫ (Pw A n).hom))

theorem isIntegral_Pw [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left] (n : ℕ) :
    IsIntegral (Pw A n).left := by
  induction n with
  | zero => exact (inferInstance : IsIntegral (Spec (.of k)))
  | succ n ih =>
    have := ih
    have := isProper_Pw A n
    exact isIntegral_pullback (Pw A n).hom A.hom

theorem isLocallyNoetherian_Pw [IsProper A.hom] (n : ℕ) : IsLocallyNoetherian (Pw A n).left := by
  have := isProper_Pw A n
  exact LocallyOfFiniteType.isLocallyNoetherian (Pw A n).hom

theorem noetherianSpace_left [IsProper A.hom] : NoetherianSpace A.left := by
  have := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := by constructor
  infer_instance

variable [GrpObj A]

theorem isProper_famP [IsProper A.hom] {g : ℕ} (D : Fin g → A.left.IdealSheafData) :
    IsProper (famP A D) := by
  change IsProper ((famI A D).subschemeι ≫ pullback.snd A.hom (Pw A g).hom)
  infer_instance

/-- The fibre of the family over the point with coordinates `a0` is finite when `Zid A D a0` is. -/
theorem finite_fibre {g : ℕ} (D : Fin g → A.left.IdealSheafData)
    (a0 : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) (ha0 : ((Zid A D a0).support : Set A.left).Finite) :
    (famP A D ⁻¹' {pt (Pw A g) (ptOf A g a0)}).Finite := by
  have hJ : (famI A D).comap (sec A (ptOf A g a0)).left = Zid A D a0 := by
    rw [comap_famI]
    congr 1
    funext i
    exact ptOf_proj A g a0 i
  have h := isPullback_fibre A D (ptOf A g a0)
  have : Finite ((famI A D).comap (sec A (ptOf A g a0)).left).subscheme := by
    refine Set.finite_univ_iff.mp (Set.Finite.of_finite_image ?_
      ((famI A D).comap (sec A (ptOf A g a0)).left).subschemeι.isClosedEmbedding.injective.injOn)
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι, hJ]
    exact ha0
  refine (Set.finite_range
    (((famI A D).comapIso (sec A (ptOf A g a0)).left).hom ≫ pullback.snd _ _)).subset ?_
  intro z hz
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := famP A D)
    (g := (ptOf A g a0).left) z (pt0 k) hz
  refine ⟨h.isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hw]

end RamanujanPetersson.IntersectA

end

-- ===== S4.Def_RP_IntersectA =====
section

/-!
# S4-IntersectA: intersection numbers at generic translates (L31-L32)

`A` is an integral group scheme, proper over an algebraically closed field `k`, all of whose points
have height `≤ g`; `D : Fin g → A.left.IdealSheafData` are proper closed subschemes. For a `k`-point
`c` of `A^g`, `Zid A D (c ≫ proj A g ·)` is the intersection of the translates `D i · cᵢ`.

* `exists_inum` (L31-L32): there are `n` and a nonempty open `U ⊆ A^g` such that for every `k`-point
  `c ∈ U` the intersection is finite and has length `n` (generic flatness of the family `famP`).
* `inum A g hdim D hD` is this `n`, the intersection number `(D_1 ⋯ D_g)`; `inum_spec` and
  `inum_unique` (any nonempty open with a constant length gives `inum`).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits
  TopologicalSpace

namespace RamanujanPetersson.IntersectA

open RamanujanPetersson.IsogDegA

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Over the open image of a good neighbourhood, every fibre is finite of length `n`. -/
theorem fibre_of_goodNbhd {g : ℕ} (D : Fin g → A.left.IdealSheafData) {T W : Scheme.{u}}
    (j : T ⟶ (Pw A g).left) [IsOpenImmersion j] (i0 : W ⟶ (famI A D).subscheme) (q : W ⟶ T)
    (hsq : IsPullback i0 q (famP A D) j) [Flat q] [IsFinite q] (n : ℕ)
    (hn : ∀ t, q.finrank t = n) (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g)
    (hc : pt (Pw A g) c ∈ Set.range j) :
    ((Zid A D (fun i => c ≫ proj A g i)).support : Set A.left).Finite ∧
      len A (Zid A D (fun i => c ≫ proj A g i)) = n := by
  have H : Set.range c.left ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim (α := Spec (.of k)) x (pt0 k)]
    exact hc
  have s : IsPullback (((famI A D).comapIso (sec A c).left).hom ≫ pullback.snd _ _)
      (((famI A D).comap (sec A c).left).subschemeι ≫ A.hom) (famP A D)
      (IsOpenImmersion.lift j c.left H ≫ j) := by
    rw [IsOpenImmersion.lift_fac]
    exact isPullback_fibre A D c
  have S := IsPullback.of_right' s hsq
  have : IsFinite (((famI A D).comap (sec A c).left).subschemeι ≫ A.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite) S inferInstance
  rw [← comap_famI]
  refine ⟨?_, ?_⟩
  · have hf := (((famI A D).comap (sec A c).left).subschemeι ≫ A.hom).finite_preimage_singleton
      (pt0 k)
    have hu : (((famI A D).comap (sec A c).left).subschemeι ≫ A.hom) ⁻¹' {pt0 k} = Set.univ :=
      Set.eq_univ_of_forall fun x => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact Subsingleton.elim _ _
    rw [hu] at hf
    have := Set.finite_univ_iff.mp hf
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.finite_range _
  · show Scheme.Hom.finrank _ (pt0 k) = n
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ S (pt0 k)]
    exact hn _

variable [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left]

/-- L31-L32: on a nonempty open of `A^g`, the translated intersections are finite of constant
length. -/
theorem exists_inum (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) :
    ∃ n : ℕ, ∃ U : Set (Pw A g).left, IsOpen U ∧ U.Nonempty ∧
      ∀ c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g, pt (Pw A g) c ∈ U →
        ((Zid A D (fun i => c ≫ proj A g i)).support : Set A.left).Finite ∧
          len A (Zid A D (fun i => c ≫ proj A g i)) = n := by
  have := noetherianSpace_left A
  have := isIntegral_Pw A g
  have := isLocallyNoetherian_Pw A g
  have := isProper_famP A D
  obtain ⟨a0, ha0, -⟩ := exists_finite_support A g hdim D hD
  obtain ⟨T, W, j, i0, q, hj, hT, hsq, hflat, hfin, n, hn⟩ :=
    goodNbhd_of_isProper (famP A D) _ (finite_fibre A D a0 ha0)
  have := hj
  have := hT
  have := hflat
  have := hfin
  exact ⟨n, Set.range j, j.isOpenEmbedding.isOpen_range, Set.range_nonempty j,
    fun c hc => fibre_of_goodNbhd A D j i0 q hsq n hn c hc⟩

/-- The intersection number `(D_1 ⋯ D_g)`: the length of the intersection of generic translates. -/
noncomputable def inum (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) : ℕ :=
  Classical.choose (exists_inum A g hdim D hD)

theorem inum_spec (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) :
    ∃ U : Set (Pw A g).left, IsOpen U ∧ U.Nonempty ∧
      ∀ c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g, pt (Pw A g) c ∈ U →
        ((Zid A D (fun i => c ≫ proj A g i)).support : Set A.left).Finite ∧
          len A (Zid A D (fun i => c ≫ proj A g i)) = inum A g hdim D hD :=
  Classical.choose_spec (exists_inum A g hdim D hD)

/-- Any nonempty open of `A^g` on which the length is constant computes `inum`. -/
theorem inum_unique (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) (n : ℕ)
    (U : Set (Pw A g).left) (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g, pt (Pw A g) c ∈ U →
      len A (Zid A D (fun i => c ≫ proj A g i)) = n) :
    n = inum A g hdim D hD := by
  obtain ⟨U', hU', hne', h'⟩ := inum_spec A g hdim D hD
  have := isIntegral_Pw A g
  have := isProper_Pw A g
  obtain ⟨c, hc⟩ := exists_pt_mem (Pw A g) (U ∩ U') (hU.inter hU').isLocallyClosed
    (nonempty_preirreducible_inter hU hU' hne hne')
  rw [← h c hc.1, (h' c hc.2).2]

end RamanujanPetersson.IntersectA

end

-- ===== S4.Def_RP_IntersectB_Sym =====
section

/-!
# S4-IntersectB, file Sym: symmetry and translation invariance of `inum` (L33, part 1)

`liftPw` builds maps into `A^n` from their coordinates (`liftPw_proj`, `Pw_hom_ext`).
`inum_eq_of_reparam`: an automorphism `ψ` of the parameter space `A^g` that carries the translated
intersections of `D'` to those of `D` gives `inum D' = inum D`. Applied to coordinate permutations
(`inum_perm`) and coordinatewise translations (`inum_shift`).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section Lift

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- A map into `A^n` with the given coordinates. -/
noncomputable def liftPw : (n : ℕ) → {X : Over (Spec (.of k))} → (Fin n → (X ⟶ A)) → (X ⟶ Pw A n)
  | 0, X, _ => toUnit X
  | n + 1, _, f => lift (liftPw n (Fin.init f)) (f (Fin.last n))

theorem liftPw_proj (n : ℕ) {X : Over (Spec (.of k))} (f : Fin n → (X ⟶ A)) (i : Fin n) :
    liftPw A n f ≫ proj A n i = f i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.lastCases with
    | last => rw [proj_last]; exact lift_snd _ _
    | cast j =>
      rw [proj_castSucc]
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ proj A n j) (lift_fst _ _))).trans (ih _ j)

theorem Pw_hom_ext (n : ℕ) {X : Over (Spec (.of k))} (f f' : X ⟶ Pw A n)
    (h : ∀ i, f ≫ proj A n i = f' ≫ proj A n i) : f = f' := by
  induction n with
  | zero => exact toUnit_unique _ _
  | succ n ih =>
    refine CartesianMonoidalCategory.hom_ext (X := Pw A n) (Y := A) _ _ ?_ ?_
    · refine ih _ _ fun j => ?_
      have hj := h j.castSucc
      rw [proj_castSucc] at hj
      exact (Category.assoc _ _ _).trans (hj.trans (Category.assoc _ _ _).symm)
    · have hl := h (Fin.last n)
      rw [proj_last] at hl
      exact hl

theorem surjective_left_of_comp_eq_id {X Y : Over (Spec (.of k))} (ψ : X ⟶ Y) (ψ' : Y ⟶ X)
    (h : ψ' ≫ ψ = 𝟙 Y) : Function.Surjective ψ.left := by
  intro y
  refine ⟨ψ'.left y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
  rfl

/-- Permutation of the coordinates of `A^g`. -/
noncomputable def permPw (g : ℕ) (σ : Equiv.Perm (Fin g)) : Pw A g ⟶ Pw A g :=
  liftPw A g (fun j => proj A g (σ.symm j))

theorem permPw_proj (g : ℕ) (σ : Equiv.Perm (Fin g)) (j : Fin g) :
    permPw A g σ ≫ proj A g j = proj A g (σ.symm j) :=
  liftPw_proj A g _ j

theorem permPw_inv (g : ℕ) (σ : Equiv.Perm (Fin g)) :
    permPw A g σ.symm ≫ permPw A g σ = 𝟙 _ :=
  Pw_hom_ext A g _ _ fun j => by
    rw [Category.assoc, permPw_proj, permPw_proj, Equiv.symm_symm, Equiv.apply_symm_apply,
      Category.id_comp]

/-- Coordinatewise right translation of `A^g`. -/
noncomputable def shiftPw (g : ℕ) (b : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) [GrpObj A] :
    Pw A g ⟶ Pw A g :=
  liftPw A g (fun j => proj A g j ≫ transl A (b j))

theorem shiftPw_proj (g : ℕ) (b : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) [GrpObj A] (j : Fin g) :
    shiftPw A g b ≫ proj A g j = proj A g j ≫ transl A (b j) :=
  liftPw_proj A g _ j

theorem shiftPw_inv (g : ℕ) (b : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) [GrpObj A] :
    shiftPw A g (fun j => (b j)⁻¹) ≫ shiftPw A g b = 𝟙 _ :=
  Pw_hom_ext A g _ _ fun j => by
    rw [Category.assoc, shiftPw_proj, ← Category.assoc, shiftPw_proj, Category.assoc,
      transl_comp_transl, _root_.inv_mul_cancel, transl_one, Category.comp_id, Category.id_comp]

end Lift

section Reparam

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- Reparametrising the translations by a surjective endomorphism of `A^g` does not change `inum`. -/
theorem inum_eq_of_reparam (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D D' : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤)
    (hD' : ∀ i, (D' i).support ≠ ⊤) (ψ : Pw A g ⟶ Pw A g) (hψ : Function.Surjective ψ.left)
    (h : ∀ c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g,
      Zid A D' (fun i => c ≫ proj A g i) = Zid A D (fun i => (c ≫ ψ) ≫ proj A g i)) :
    inum A g hdim D' hD' = inum A g hdim D hD := by
  obtain ⟨U, hU, hne, hc⟩ := inum_spec A g hdim D hD
  refine (inum_unique A g hdim D' hD' _ (ψ.left ⁻¹' U) (hU.preimage ψ.left.continuous) ?_ ?_).symm
  · obtain ⟨y, hy⟩ := hne
    obtain ⟨x, rfl⟩ := hψ y
    exact ⟨x, hy⟩
  · intro c hcU
    rw [h c]
    exact (hc (c ≫ ψ) (by rw [pt_comp]; exact hcU)).2

/-- B1 (symmetry): `inum` is invariant under permuting the divisors. -/
theorem inum_perm (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) (σ : Equiv.Perm (Fin g)) :
    inum A g hdim (fun i => D (σ i)) (fun i => hD (σ i)) = inum A g hdim D hD := by
  refine inum_eq_of_reparam A g hdim D _ hD _ (permPw A g σ)
    (surjective_left_of_comp_eq_id _ _ (permPw_inv A g σ)) fun c => ?_
  simp only [Zid]
  refine (iSup_congr fun i => ?_).trans (Equiv.iSup_comp (g := fun j =>
    (D j).comap (transl A ((c ≫ permPw A g σ) ≫ proj A g j)).left) σ)
  rw [Category.assoc, permPw_proj, Equiv.symm_apply_apply]

theorem support_comap_transl_ne_top (I : A.left.IdealSheafData) (hI : I.support ≠ ⊤)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ A) : (I.comap (transl A b).left).support ≠ ⊤ := by
  intro h
  apply hI
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : (transl A b).left ((transl A b⁻¹).left x) = x := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, transl_comp_transl, _root_.inv_mul_cancel,
      transl_one]
    rfl
  have hy : (transl A b⁻¹).left x ∈ (I.comap (transl A b).left).support := by
    rw [h]; exact Set.mem_univ _
  rw [Scheme.IdealSheafData.support_comap] at hy
  rw [← hx]
  exact hy

/-- B2 (translation invariance): translating the divisors does not change `inum`. -/
theorem inum_shift (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤)
    (b : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    inum A g hdim (fun i => (D i).comap (transl A (b i)).left)
      (fun i => support_comap_transl_ne_top A (D i) (hD i) (b i)) = inum A g hdim D hD := by
  refine inum_eq_of_reparam A g hdim D _ hD _ (shiftPw A g b)
    (surjective_left_of_comp_eq_id _ _ (shiftPw_inv A g b)) fun c => ?_
  simp only [Zid]
  refine iSup_congr fun i => ?_
  rw [← Scheme.IdealSheafData.comap_comp, ← Over.comp_left, transl_comp_transl, Category.assoc,
    shiftPw_proj, ← Category.assoc, point_comp_transl]

end Reparam

end RamanujanPetersson.IntersectB

end

-- ===== S4.Def_RP_IntersectB_Aff =====
section

/-!
# S4-IntersectB, file Aff: affine charts for finite subschemes (L33, part 2)

* `exists_affine_mem`: on a group scheme, any finite set of points lies in one affine open.
* `algV`, `algV_spec`: the `k`-algebra structure on sections over an affine open.
* `len_eq_finrank`: a closed subscheme with finite support inside an affine open `V` has
  `len = finrank_k (Γ(V) ⧸ J(V))`, and this quotient is finite over `k`.
* `comap_mul_of_isIso`: pulling back ideal sheaves along an isomorphism preserves products.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits
  TopologicalSpace

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section Aff

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- Translations are isomorphisms (as in `IsogDegA_QF`, which this file does not import). -/
theorem isIso_translL [GrpObj A] (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : IsIso (transl A a).left :=
  ⟨⟨(transl A a⁻¹).left, by
    rw [← Over.comp_left, transl_comp_transl, _root_.mul_inv_cancel, transl_one, Over.id_left], by
    rw [← Over.comp_left, transl_comp_transl, _root_.inv_mul_cancel, transl_one, Over.id_left]⟩⟩

/-- (a) Finitely many points of a group scheme lie in one affine open. -/
theorem exists_affine_mem [GrpObj A] [IsAlgClosed k] [LocallyOfFiniteType A.hom]
    [IrreducibleSpace A.left] (S : Finset A.left) :
    ∃ V : A.left.affineOpens, ∀ x ∈ S, x ∈ (V : A.left.Opens) := by
  obtain ⟨x0⟩ : Nonempty A.left := inferInstance
  obtain ⟨_, ⟨V0, hV0, rfl⟩, hx0, -⟩ :=
    A.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x0) isOpen_univ
  have hD : IsClosed (V0 : Set A.left)ᶜ := V0.isOpen.isClosed_compl
  have hne : (V0 : Set A.left)ᶜ ≠ Set.univ := by
    intro h
    have h1 : x0 ∈ (V0 : Set A.left)ᶜ := h ▸ Set.mem_univ x0
    exact h1 hx0
  obtain ⟨a, ha⟩ := exists_good A S _ hD hne
  have := isIso_translL A a
  refine ⟨⟨(transl A a).left ⁻¹ᵁ V0, hV0.preimage_of_isIso _⟩, fun x hx => ?_⟩
  have := ha x hx
  simpa using this

/-- The `k`-algebra structure on the sections of `A` over an affine open. -/
noncomputable def algV (V : A.left.affineOpens) : CommRingCat.of k ⟶ Γ(A.left, V) :=
  Spec.preimage (V.2.fromSpec ≫ A.hom)

theorem algV_spec (V : A.left.affineOpens) : Spec.map (algV A V) = V.2.fromSpec ≫ A.hom :=
  Spec.map_preimage _

/-- (b) The length of a closed subscheme with finite support inside an affine open `V`. -/
theorem len_eq_finrank [LocallyOfFiniteType A.hom] (J : A.left.IdealSheafData)
    (V : A.left.affineOpens) (hV : (J.support : Set A.left) ⊆ V)
    (hfin : (J.support : Set A.left).Finite) :
    letI := (algV A V).hom.toAlgebra
    Module.Finite k (Γ(A.left, V) ⧸ J.ideal V) ∧
      len A J = Module.finrank k (Γ(A.left, V) ⧸ J.ideal V) := by
  letI := (algV A V).hom.toAlgebra
  let f : Spec (.of (Γ(A.left, V) ⧸ J.ideal V)) ⟶ J.subscheme := J.subschemeCover.f V
  have hfo : IsOpenImmersion f := J.subschemeCover.map_prop V
  have hf : IsIso f := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨hfo, ⟨fun z => ?_⟩⟩
    have h2 := J.opensRange_subschemeCover_map V
    have hz : z ∈ J.subschemeι ⁻¹ᵁ (V : A.left.Opens) :=
      hV (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩)
    rw [← h2] at hz
    exact hz
  have hcomp : f ≫ J.subschemeι ≫ A.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V))) := by
    have h1 : f ≫ J.subschemeι = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal V))) ≫
        V.2.fromSpec :=
      (J.subschemeCover_map_subschemeι V).trans (J.glueDataObjι_ι V)
    rw [← Category.assoc, h1, Category.assoc, ← algV_spec, ← Spec.map_comp]
    rfl
  -- finiteness over `k`
  have hft : Algebra.FiniteType k Γ(A.left, V) := by
    have : LocallyOfFiniteType (Spec.map (algV A V)) := by
      rw [algV_spec]
      have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  have hJac : IsJacobsonRing (Γ(A.left, V) ⧸ J.ideal V) := isJacobsonRing_of_finiteType (A := k)
  have hfinsub : Finite J.subscheme := by
    have hi : Function.Injective J.subschemeι := J.subschemeι.isEmbedding.injective
    refine Set.finite_univ_iff.mp (Set.Finite.of_finite_image (hfin.subset ?_) hi.injOn)
    rintro _ ⟨z, -, rfl⟩
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have hfinR : Finite (PrimeSpectrum (Γ(A.left, V) ⧸ J.ideal V)) :=
    Finite.of_injective (β := J.subscheme) (fun x => f x) f.isOpenEmbedding.injective
  have hdisc : DiscreteTopology (PrimeSpectrum (Γ(A.left, V) ⧸ J.ideal V)) :=
    JacobsonSpace.discreteTopology (Set.toFinite _)
  have hdim := (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hdisc).2
  have hmf : Module.Finite k (Γ(A.left, V) ⧸ J.ideal V) :=
    (Module.finite_iff_krullDimLE_zero k _).mpr hdim
  refine ⟨hmf, ?_⟩
  have hg : J.subschemeι ≫ A.hom = inv f ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V))) := by
    rw [← hcomp, IsIso.inv_hom_id_assoc]
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V)))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]; infer_instance
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V)))) := by
    rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]; exact hmf
  show Scheme.Hom.finrank _ (pt0 k) = _
  rw [hg, Scheme.Hom.finrank_comp_left_of_isIso]
  refine (Scheme.Hom.finrank_SpecMap_algebraMap k (Γ(A.left, V) ⧸ J.ideal V) (pt0 k)).trans ?_
  rw [Module.rankAtStalk_eq_finrank_of_free]
  rfl

/-- (c) Pulling back along an isomorphism preserves products of ideal sheaves. -/
theorem comap_mul_of_isIso {X Y : Scheme.{u}} (I I' : Y.IdealSheafData) (f : X ⟶ Y) [IsIso f] :
    (I * I').comap f = I.comap f * I'.comap f := by
  ext U : 2
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  let e := (f.appIso U).commRingCatIsoToRingEquiv
  have h (K : Ideal Γ(Y, f ''ᵁ U)) : K.comap (f.appIso U).inv.hom = K.map e := by
    rw [← Ideal.comap_symm]; rfl
  rw [h, h, h, Ideal.map_mul]

end Aff

end RamanujanPetersson.IntersectB

end

-- ===== S4.Def_RP_IntersectB_Add_Ring =====
section

/-!
# S4-IntersectB, file Add_Ring: the chart step of additivity (L33, B3 core)

* `IsLocPrin I`: `I` is principal near every maximal ideal of every affine chart; stable under
  pullback along isomorphisms (`isLocPrin_comap`).
* `finrank_chart`: for ideals `I, I', J` of a Noetherian domain over an infinite field, with `I'`
  locally principal and contained in no associated prime of `R ⧸ J`,
  `dim R/(II'+J) = dim R/(I+J) + dim R/(I'+J)`.
* `len_mul`: the same for lengths of closed subschemes of `A` with finite support, when the
  support of `L'` avoids the associated points of `C`.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section Ring

/-- Local principality transported along a ring isomorphism. -/
theorem locPrinAt_comap {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (ψ : R' →+* R)
    (h1 : ∀ x, φ (ψ x) = x) (h2 : ∀ x, ψ (φ x) = x) {K : Ideal R'} {m : Ideal R}
    (h : LocPrinAt K (m.comap ψ)) : LocPrinAt (K.comap φ) m := by
  obtain ⟨v, hv, t, ht, htv⟩ := h
  refine ⟨ψ v, ?_, ψ t, ht, fun y hy => ?_⟩
  · show φ (ψ v) ∈ K
    rw [h1]; exact hv
  · obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (htv (φ y) hy)
    refine Ideal.mem_span_singleton'.2 ⟨ψ a, ?_⟩
    rw [← map_mul, ha, map_mul, h2]

/-- Ring step of B3. -/
theorem finrank_chart (k : Type*) [Field k] [Infinite k] {R : Type*} [CommRing R] [Algebra k R]
    [IsDomain R] [IsNoetherianRing R] (I I' J : Ideal R) [Module.Finite k (R ⧸ (I * I' ⊔ J))]
    (hloc : ∀ m : Ideal R, m.IsMaximal → LocPrinAt I' m)
    (hass : ∀ p ∈ associatedPrimes R (R ⧸ J), ¬ I' ≤ p) :
    Module.finrank k (R ⧸ (I * I' ⊔ J)) =
      Module.finrank k (R ⧸ (I ⊔ J)) + Module.finrank k (R ⧸ (I' ⊔ J)) := by
  obtain ⟨u, hu, s, hs, hsu⟩ := exists_gen_quot k I' (I * I' ⊔ J) (fun m hm _ => hloc m hm)
  refine finrank_quot_mul I I' J u s hu hsu hs (weak_nzd J u s fun p hp hup => ?_)
  by_contra hsp
  refine hass p hp fun y hy => ?_
  have hp' : p.IsPrime := IsAssociatedPrime.isPrime hp
  have h1 : s * y ∈ p := (Ideal.span_singleton_le_iff_mem p).2 hup (hsu y hy)
  exact (hp'.mem_or_mem h1).resolve_left hsp

end Ring

section Sch

/-- `I` is principal near every maximal ideal of every affine chart. -/
def IsLocPrin {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ (V : X.affineOpens) (m : Ideal Γ(X, V)), m.IsMaximal → LocPrinAt (I.ideal V) m

theorem isLocPrin_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) [IsIso f]
    (h : IsLocPrin I) : IsLocPrin (I.comap f) := by
  intro V m hm
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  refine locPrinAt_comap _ (f.appIso V).hom.hom (fun x => ?_) (fun x => ?_) (h _ _ ?_)
  · rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  · rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  · exact Ideal.comap_isMaximal_of_surjective _ fun y => ⟨(f.appIso V).inv.hom y, by
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl⟩

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [LocallyOfFiniteType A.hom] [IsIntegral A.left]

/-- B3 at the level of lengths: `len (L L' + C) = len (L + C) + len (L' + C)`. -/
theorem len_mul (L L' C : A.left.IdealSheafData)
    (hfin : ((L * L' ⊔ C).support : Set A.left).Finite)
    (hloc : IsLocPrin L') (hass : ∀ x ∈ assSet C, x ∉ L'.support) :
    len A (L * L' ⊔ C) = len A (L ⊔ C) + len A (L' ⊔ C) := by
  classical
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨x0⟩ : Nonempty A.left := inferInstance
  obtain ⟨V, hV⟩ := exists_affine_mem A (insert x0 hfin.toFinset)
  have hS : ((L * L' ⊔ C).support : Set A.left) ⊆ (V : A.left.Opens) := fun x hx =>
    hV x (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 hx))
  have h2 : ((L ⊔ C).support : Set A.left) ⊆ (L * L' ⊔ C).support :=
    Scheme.IdealSheafData.support_antitone (sup_le_sup_right
      (Scheme.IdealSheafData.le_def.2 fun U => Ideal.mul_le_left) C)
  have h3 : ((L' ⊔ C).support : Set A.left) ⊆ (L * L' ⊔ C).support :=
    Scheme.IdealSheafData.support_antitone (sup_le_sup_right
      (Scheme.IdealSheafData.le_def.2 fun U => Ideal.mul_le_right) C)
  have : Nonempty (V : A.left.Opens) := ⟨⟨x0, hV x0 (Finset.mem_insert_self _ _)⟩⟩
  have : IsDomain Γ(A.left, V) := inferInstance
  have : IsNoetherianRing Γ(A.left, V) := IsLocallyNoetherian.component_noetherian V
  letI := (algV A V).hom.toAlgebra
  obtain ⟨hf1, e1⟩ := len_eq_finrank A (L * L' ⊔ C) V hS hfin
  obtain ⟨-, e2⟩ := len_eq_finrank A (L ⊔ C) V (h2.trans hS) (hfin.subset h2)
  obtain ⟨-, e3⟩ := len_eq_finrank A (L' ⊔ C) V (h3.trans hS) (hfin.subset h3)
  rw [e1, e2, e3]
  have : Module.Finite k (Γ(A.left, V) ⧸ (L.ideal V * L'.ideal V ⊔ C.ideal V)) := hf1
  exact finrank_chart k (L.ideal V) (L'.ideal V) (C.ideal V) (fun m hm => hloc V m hm)
    (fun p hp => not_le_of_ass C L' hass V p hp)

end Sch

end RamanujanPetersson.IntersectB

end

-- ===== S4.Def_RP_IntersectB_Add =====
section

/-!
# S4-IntersectB, file Add: additivity of `inum` in the first slot (L33, B3)

For a locally principal `I'` (`IsLocPrin`), `(I I' · E) = (I · E) + (I' · E)`.
Proof (slice trick): pick a `k`-point `c*` of `A^(n+1)` where all three intersections are generic,
freeze its last `n` coordinates (intersection `C`), and move the first coordinate inside the slice
so that the translate of `supp I'` avoids the finitely many associated points of `C`; then
`len_mul` applies.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section Slice

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

theorem Zid_cons [GrpObj A] {n : ℕ} (X : A.left.IdealSheafData) (E : Fin n → A.left.IdealSheafData)
    (a : Fin (n + 1) → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    Zid A (Fin.cons X E : Fin (n + 1) → A.left.IdealSheafData) a =
      X.comap (transl A (a 0)).left ⊔ ⨆ j, (E j).comap (transl A (a j.succ)).left := by
  unfold Zid
  apply le_antisymm
  · refine iSup_le fun i => ?_
    induction i using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact le_sup_left
    | succ j =>
      rw [Fin.cons_succ]
      exact le_sup_of_le_right (le_iSup (fun j => (E j).comap (transl A (a j.succ)).left) j)
  · refine sup_le ?_ (iSup_le fun j => ?_)
    · refine le_trans ?_ (le_iSup _ (0 : Fin (n + 1)))
      rw [Fin.cons_zero]
    · refine le_trans ?_ (le_iSup _ j.succ)
      rw [Fin.cons_succ]

/-- The slice of `A^(n+1)` through `c` along the first coordinate. -/
noncomputable def slice {n : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A (n + 1)) : A ⟶ Pw A (n + 1) :=
  liftPw A (n + 1) (X := A) (Fin.cons (𝟙 A) fun j => toUnit A ≫ c ≫ proj A (n + 1) j.succ)

theorem slice_proj_zero {n : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A (n + 1)) :
    slice A c ≫ proj A (n + 1) 0 = 𝟙 A := by
  rw [slice, liftPw_proj, Fin.cons_zero]

theorem slice_proj_succ {n : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A (n + 1)) (j : Fin n) :
    slice A c ≫ proj A (n + 1) j.succ = toUnit A ≫ c ≫ proj A (n + 1) j.succ := by
  rw [slice, liftPw_proj, Fin.cons_succ]

theorem pt_slice_zero {n : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A (n + 1))
    (w : 𝟙_ (Over (Spec (.of k))) ⟶ A) : (w ≫ slice A c) ≫ proj A (n + 1) 0 = w := by
  rw [Category.assoc, slice_proj_zero, Category.comp_id]

theorem pt_slice_succ {n : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A (n + 1))
    (w : 𝟙_ (Over (Spec (.of k))) ⟶ A) (j : Fin n) :
    (w ≫ slice A c) ≫ proj A (n + 1) j.succ = c ≫ proj A (n + 1) j.succ := by
  rw [Category.assoc, slice_proj_succ, ← Category.assoc, comp_toUnit, toUnit_unit,
    Category.id_comp]

theorem slice_self {n : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A (n + 1)) :
    (c ≫ proj A (n + 1) 0) ≫ slice A c = c :=
  Pw_hom_ext A (n + 1) _ _ fun i => by
    induction i using Fin.cases with
    | zero => exact pt_slice_zero A c _
    | succ j => exact pt_slice_succ A c _ j

end Slice

section B3

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- B3: additivity of the intersection number in a locally principal factor. -/
theorem inum_mul (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    (I I' : A.left.IdealSheafData) (E : Fin n → A.left.IdealSheafData)
    (h1 : ∀ i, ((Fin.cons (I * I') E : Fin (n + 1) → A.left.IdealSheafData) i).support ≠ ⊤)
    (h2 : ∀ i, ((Fin.cons I E : Fin (n + 1) → A.left.IdealSheafData) i).support ≠ ⊤)
    (h3 : ∀ i, ((Fin.cons I' E : Fin (n + 1) → A.left.IdealSheafData) i).support ≠ ⊤)
    (hloc : IsLocPrin I') :
    inum A (n + 1) hdim (Fin.cons (I * I') E) h1 =
      inum A (n + 1) hdim (Fin.cons I E) h2 + inum A (n + 1) hdim (Fin.cons I' E) h3 := by
  have := isIntegral_Pw A (n + 1)
  have := isProper_Pw A (n + 1)
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨U1, hU1o, hU1n, hU1⟩ := inum_spec A (n + 1) hdim _ h1
  obtain ⟨U2, hU2o, hU2n, hU2⟩ := inum_spec A (n + 1) hdim _ h2
  obtain ⟨U3, hU3o, hU3n, hU3⟩ := inum_spec A (n + 1) hdim _ h3
  have hUo : IsOpen (U1 ∩ U2 ∩ U3) := (hU1o.inter hU2o).inter hU3o
  obtain ⟨cs, hcs⟩ := exists_pt_mem (Pw A (n + 1)) (U1 ∩ U2 ∩ U3) hUo.isLocallyClosed
    (nonempty_preirreducible_inter (hU1o.inter hU2o) hU3o
      (nonempty_preirreducible_inter hU1o hU2o hU1n hU2n) hU3n)
  obtain ⟨C, hC⟩ : ∃ C : A.left.IdealSheafData,
      C = ⨆ j, (E j).comap (transl A (cs ≫ proj A (n + 1) j.succ)).left := ⟨_, rfl⟩
  have hEf := assSet_finite C
  have hI' : (I'.support : Set A.left) ≠ Set.univ := fun h => h3 0 (by
    rw [Fin.cons_zero]; exact SetLike.coe_injective (h.trans TopologicalSpace.Closeds.coe_top.symm))
  choose G hGo hGn hG using fun ξ => exists_open_good A ξ _ I'.support.isClosed hI'
  have hO : IsOpen ((slice A cs).left ⁻¹' (U1 ∩ U2 ∩ U3)) := hUo.preimage (slice A cs).left.continuous
  have hOn : pt A (cs ≫ proj A (n + 1) 0) ∈ (slice A cs).left ⁻¹' (U1 ∩ U2 ∩ U3) := by
    show (slice A cs).left (pt A _) ∈ U1 ∩ U2 ∩ U3
    rw [← pt_comp, slice_self]; exact hcs
  obtain ⟨c0, hc0O, hc0G⟩ := exists_pt_mem A _ (hO.inter (isOpen_biInter_finset fun ξ _ => hGo ξ)).isLocallyClosed
    (nonempty_preirreducible_inter hO (isOpen_biInter_finset fun ξ _ => hGo ξ) ⟨_, hOn⟩
      (nonempty_biInter_finset hEf.toFinset G (fun ξ _ => hGo ξ) fun ξ _ => hGn ξ))
  have hc : pt (Pw A (n + 1)) (c0 ≫ slice A cs) ∈ U1 ∩ U2 ∩ U3 := by rw [pt_comp]; exact hc0O
  have hZ (X : A.left.IdealSheafData) :
      Zid A (Fin.cons X E : Fin (n + 1) → A.left.IdealSheafData)
        (fun i => (c0 ≫ slice A cs) ≫ proj A (n + 1) i) = X.comap (transl A c0).left ⊔ C := by
    rw [Zid_cons, hC, pt_slice_zero]
    simp only [pt_slice_succ]
  have := isIso_translL A c0
  obtain ⟨hfin1, hl1⟩ := hU1 _ hc.1.1
  obtain ⟨-, hl2⟩ := hU2 _ hc.1.2
  obtain ⟨-, hl3⟩ := hU3 _ hc.2
  rw [hZ, comap_mul_of_isIso] at hfin1 hl1
  rw [hZ] at hl2 hl3
  rw [← hl1, ← hl2, ← hl3]
  refine len_mul A _ _ C hfin1 (isLocPrin_comap I' _ hloc) fun x hx => ?_
  rw [Scheme.IdealSheafData.support_comap]
  exact hG x c0 (Set.mem_iInter₂.1 hc0G x (hEf.mem_toFinset.2 hx))

end B3

end RamanujanPetersson.IntersectB

end

-- ===== S4.Def_RP_JacDivisors_Q =====
section

/-!
# S4-JacDivisors Q (O14, steps E9-E10: Weil's extension theorem, Milne I.3.1-3.2)
For `V G : Over (Spec k)` (`k` algebraically closed), `G` a group object and `f : V ⇀ G` a partial map over `k`:
* `mem_domain_of_slice`: if `a ∈ dom f` is a `k`-point and the difference map `Φ(v, w) = f(v) f(w)⁻¹` is defined at
  `(x, a)`, then `f` extends to `x` (`v ↦ Φ(v, a) · f(a)` near `x`).
* `mem_domain_of_isClosed`: if `Φ` is defined at `Δ x` and `x` is closed, then `f` extends to `x`.
* `domain_eq_top` (E10): if `V` and `V ×_k V` are integral, locally Noetherian with factorial stalks, `V` is of finite type
  and `G` is separated, locally of finite type and satisfies the existence part of the valuative criterion (e.g. proper),
  then every rational map `V ⤏ G` over `k` is defined everywhere.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Limits Order Topology MonoidalCategory MonObj CartesianMonoidalCategory

universe u

/-- The maximal representative of a rational map between `S`-schemes is again an `S`-map. -/
lemma toPartialMap_comp {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) [IsReduced X] [Y.IsSeparated]
    [S.IsSeparated] (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX) :
    f.toRationalMap.toPartialMap.hom ≫ sY = f.toRationalMap.toPartialMap.domain.ι ≫ sX := by
  letI : X.Over S := ⟨sX⟩
  letI : Y.Over S := ⟨sY⟩
  haveI : f.IsOver S := Scheme.PartialMap.isOver_iff.mpr hf
  exact Scheme.PartialMap.isOver_iff.mp inferInstance

section
variable {k : Type u} [Field k] {V G : Over (Spec (.of k))}

/-- The slice `v ↦ (v, a)` through a `k`-point `a`. -/
noncomputable abbrev slice (a : 𝟙_ (Over (Spec (.of k))) ⟶ V) : V ⟶ V ⊗ V := lift (𝟙 V) (toUnit V ≫ a)

lemma slice_fst_apply (a : 𝟙_ (Over (Spec (.of k))) ⟶ V) (v : V.left) :
    (fst V V).left ((slice a).left v) = v := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
  rfl

lemma slice_snd_apply (a : 𝟙_ (Over (Spec (.of k))) ⟶ V) (v : V.left) :
    (snd V V).left ((slice a).left v) = IsogDegA.pt V a := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd, Over.comp_left, Scheme.Hom.comp_apply]
  change a.left _ = a.left (IsogDegA.pt0 k)
  congr 1
  exact @Subsingleton.elim (Spec (.of k)) _ _ _

lemma slice_le (a : 𝟙_ (Over (Spec (.of k))) ⟶ V) (D : V.left.Opens) (ha : IsogDegA.pt V a ∈ D) :
    D ≤ (slice a).left ⁻¹ᵁ sqOpen D := fun v hv =>
  ⟨show (fst V V).left ((slice a).left v) ∈ D by rw [slice_fst_apply]; exact hv,
   show (snd V V).left ((slice a).left v) ∈ D by rw [slice_snd_apply]; exact ha⟩

lemma resLE_comp_resLE (D : V.left.Opens) (s : V ⟶ V ⊗ V) (p : V ⊗ V ⟶ V) (hp : s ≫ p = 𝟙 V)
    (h₁ : D ≤ s.left ⁻¹ᵁ sqOpen D) (h₂ : sqOpen D ≤ p.left ⁻¹ᵁ D) :
    s.left.resLE (sqOpen D) D h₁ ≫ p.left.resLE D (sqOpen D) h₂ = 𝟙 _ := by
  rw [← cancel_mono D.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι, Category.assoc, ← Over.comp_left, hp, Over.id_left,
    Category.comp_id, Category.id_comp]

variable [GrpObj G]

/-- E9 (slice step): if `a` is a `k`-point in the domain of `f` and the difference map `Φ` is defined at `(x, a)`,
then `f` extends to `x`. -/
theorem mem_domain_of_slice [IrreducibleSpace V.left] [IsReduced (V ⊗ V).left]
    [IrreducibleSpace (V ⊗ V).left] [G.left.IsSeparated]
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom)
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ V) (ha : IsogDegA.pt V a ∈ f.domain) {x : V.left}
    (hx : (slice a).left x ∈ (quotPM f hf).toRationalMap.domain) : x ∈ f.toRationalMap.domain := by
  let Φ' := (quotPM f hf).toRationalMap.toPartialMap
  have hΦ' : Φ'.hom ≫ G.hom = Φ'.domain.ι ≫ (V ⊗ V).hom :=
    toPartialMap_comp (V ⊗ V).hom G.hom (quotPM f hf) (quotPM_comp f hf)
  have hsq : sqOpen f.domain ≤ Φ'.domain := (quotPM f hf).le_domain_toRationalMap
  have hsD : f.domain ≤ (slice a).left ⁻¹ᵁ sqOpen f.domain := slice_le a f.domain ha
  let N : V.left.Opens := (slice a).left ⁻¹ᵁ Φ'.domain
  have hDN : f.domain ≤ N := fun v hv => hsq (hsD hv)
  let D' : Over (Spec (.of k)) := Over.mk (f.domain.ι ≫ V.hom)
  let N' : Over (Spec (.of k)) := Over.mk (N.ι ≫ V.hom)
  let P' : Over (Spec (.of k)) := Over.mk (Φ'.domain.ι ≫ (V ⊗ V).hom)
  let fD : D' ⟶ G := Over.homMk f.hom hf
  let ΦO : P' ⟶ G := Over.homMk Φ'.hom hΦ'
  let sN : N' ⟶ P' := Over.homMk ((slice a).left.resLE Φ'.domain N le_rfl) (by
    change _ ≫ Φ'.domain.ι ≫ (V ⊗ V).hom = N.ι ≫ V.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w (slice a)])
  have hrange : Set.range a.left ⊆ Set.range f.domain.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    have hp : p = IsogDegA.pt0 k := @Subsingleton.elim (Spec (.of k)) _ _ _
    subst hp
    exact ha
  let aD : 𝟙_ (Over (Spec (.of k))) ⟶ D' := Over.homMk (IsOpenImmersion.lift f.domain.ι a.left hrange) (by
    change _ ≫ f.domain.ι ≫ V.hom = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w a])
  let c : 𝟙_ (Over (Spec (.of k))) ⟶ G := aD ≫ fD
  let Ψ : N' ⟶ G := sN ≫ ΦO * (toUnit N' ≫ c)
  let iD : D' ⟶ N' := Over.homMk (V.left.homOfLE hDN) (by
    change _ ≫ N.ι ≫ V.hom = f.domain.ι ≫ V.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])
  let δ : D' ⟶ sqOver f.domain := Over.homMk ((slice a).left.resLE (sqOpen f.domain) f.domain hsD) (by
    change _ ≫ (sqOpen f.domain).ι ≫ (V ⊗ V).hom = f.domain.ι ≫ V.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w (slice a)])
  have h1 : δ ≫ prRes f hf (fst V V) (sqOpen_le_fst _) = fD := by
    apply Over.OverMorphism.ext
    change (slice a).left.resLE _ _ _ ≫ (fst V V).left.resLE _ _ _ ≫ f.hom = f.hom
    rw [← Category.assoc, resLE_comp_resLE _ _ _ (lift_fst _ _), Category.id_comp]
  have h2 : δ ≫ prRes f hf (snd V V) (sqOpen_le_snd _) = toUnit D' ≫ c := by
    apply Over.OverMorphism.ext
    change (slice a).left.resLE _ _ _ ≫ (snd V V).left.resLE _ _ _ ≫ f.hom =
      (toUnit D').left ≫ IsOpenImmersion.lift f.domain.ι a.left hrange ≫ f.hom
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono f.domain.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc, IsOpenImmersion.lift_fac,
      ← Over.comp_left, lift_snd, Over.comp_left, ← Category.assoc]
    congr 1
  have hres : (V ⊗ V).left.homOfLE hsq ≫ Φ'.hom = (quotPM f hf).hom :=
    (quotPM f hf).toPartialMap_toRationalMap_restrict
  have hfΦ : iD ≫ sN ≫ ΦO = δ ≫ quotHom f hf := by
    apply Over.OverMorphism.ext
    change V.left.homOfLE hDN ≫ (slice a).left.resLE Φ'.domain N le_rfl ≫ Φ'.hom =
      (slice a).left.resLE (sqOpen f.domain) f.domain hsD ≫ (quotPM f hf).hom
    rw [← hres, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono Φ'.domain.ι]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc]
  have hΨ : iD ≫ Ψ = fD := by
    change iD ≫ (sN ≫ ΦO * (toUnit N' ≫ c)) = fD
    rw [comp_mul, hfΦ, ← Category.assoc, comp_toUnit, quotHom, comp_mul, GrpObj.comp_inv, h1, h2,
      inv_mul_cancel_right]
  let g : V.left.PartialMap G.left :=
    ⟨N, N.isOpen.dense ⟨_, hDN f.dense_domain.nonempty.choose_spec⟩, Ψ.left⟩
  have heq : g.equiv f := by
    refine ⟨f.domain, f.dense_domain, hDN, le_rfl, ?_⟩
    simp only [Scheme.PartialMap.restrict_hom, Scheme.homOfLE_rfl, Category.id_comp]
    exact congrArg (fun φ => φ.left) hΨ
  exact Scheme.RationalMap.mem_domain.mpr ⟨g, hx, Scheme.PartialMap.toRationalMap_eq_iff.mpr heq⟩

/-- E9: if the difference map is defined at `Δ x` for a closed point `x`, then `f` extends to `x`. -/
theorem mem_domain_of_isClosed [IsAlgClosed k] [LocallyOfFiniteType V.hom] [IrreducibleSpace V.left]
    [IsReduced (V ⊗ V).left] [IrreducibleSpace (V ⊗ V).left] [G.left.IsSeparated]
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) {x : V.left}
    (hx : IsClosed ({x} : Set V.left)) (hΔ : (diag V).left x ∈ (quotPM f hf).toRationalMap.domain) :
    x ∈ f.toRationalMap.domain := by
  haveI : JacobsonSpace V.left := LocallyOfFiniteType.jacobsonSpace V.hom
  obtain ⟨b, rfl⟩ := IsogDegA.exists_pt_eq V x hx
  let t : V ⟶ V ⊗ V := lift (toUnit V ≫ b) (𝟙 V)
  have e1 : b ≫ toUnit V = 𝟙 _ := toUnit_unique _ _
  have hbt : b ≫ t = b ≫ diag V := by
    simp only [t, comp_lift, Category.comp_id, reassoc_of% e1]
  have htx : t.left (IsogDegA.pt V b) = (diag V).left (IsogDegA.pt V b) := by
    rw [← IsogDegA.pt_comp, ← IsogDegA.pt_comp, hbt]
  let O : V.left.Opens := t.left ⁻¹ᵁ (quotPM f hf).toRationalMap.domain
  have hO : ((O : Set V.left) ∩ (f.domain : Set V.left)).Nonempty :=
    nonempty_preirreducible_inter O.isOpen f.domain.isOpen
      ⟨IsogDegA.pt V b, show t.left _ ∈ _ by rw [htx]; exact hΔ⟩ f.dense_domain.nonempty
  obtain ⟨a, haO, hacl⟩ := nonempty_inter_closedPoints hO (O.isOpen.inter f.domain.isOpen).isLocallyClosed
  obtain ⟨c, rfl⟩ := IsogDegA.exists_pt_eq V a hacl
  have e2 : c ≫ toUnit V = 𝟙 _ := toUnit_unique _ _
  refine mem_domain_of_slice f hf c haO.2 ?_
  have hbc : b ≫ slice c = c ≫ t := by
    simp only [slice, t, comp_lift, Category.comp_id, reassoc_of% e1, reassoc_of% e2]
  rw [← IsogDegA.pt_comp, hbc, IsogDegA.pt_comp]
  exact haO.1

/-- E10, **Weil's extension theorem** (factorial-stalk form): a rational map over `k` from `V` (with `V` and `V ×_k V`
integral, locally Noetherian, with factorial local rings) to a separated group `G` satisfying the existence part of the
valuative criterion is defined everywhere. -/
theorem domain_eq_top [IsAlgClosed k] [LocallyOfFiniteType V.hom] [LocallyOfFiniteType G.hom] [IsSeparated G.hom]
    [IsIntegral V.left] [IsLocallyNoetherian V.left] [IsIntegral (V ⊗ V).left] [IsLocallyNoetherian (V ⊗ V).left]
    [∀ v : V.left, UniqueFactorizationMonoid (V.left.presheaf.stalk v)]
    [∀ p : (V ⊗ V).left, UniqueFactorizationMonoid ((V ⊗ V).left.presheaf.stalk p)]
    (hY : ValuativeCriterion.Existence G.hom)
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) :
    f.toRationalMap.domain = ⊤ := by
  haveI : G.left.IsSeparated := ⟨by rw [← terminal.comp_from G.hom]; infer_instance⟩
  haveI : JacobsonSpace V.left := LocallyOfFiniteType.jacobsonSpace V.hom
  let f' := f.toRationalMap.toPartialMap
  have hf' : f'.hom ≫ G.hom = f'.domain.ι ≫ V.hom := toPartialMap_comp V.hom G.hom f hf
  have hcod : ∀ v : V.left, coheight v ≤ 1 → v ∈ f'.domain := fun v hv =>
    mem_domain_of_coheight_le_one V.hom G.hom hY f hf hv
  have hcl : ∀ x : V.left, IsClosed ({x} : Set V.left) → x ∈ f.toRationalMap.domain := by
    intro x hx
    have h := mem_domain_of_isClosed f' hf' hx (diag_mem_domain f' hf' hcod x)
    rwa [Scheme.RationalMap.toRationalMap_toPartialMap] at h
  refine top_unique fun x _ => ?_
  by_contra hx
  obtain ⟨y, hy, hycl⟩ := nonempty_inter_closedPoints (Z := ((f.toRationalMap.domain : Set V.left))ᶜ)
    ⟨x, hx⟩ f.toRationalMap.domain.isOpen.isClosed_compl.isLocallyClosed
  exact hy (hcl y hycl)

/-- **Weil's extension theorem** for a proper group `G`. -/
theorem domain_eq_top_of_isProper [IsAlgClosed k] [LocallyOfFiniteType V.hom] [IsProper G.hom]
    [IsIntegral V.left] [IsLocallyNoetherian V.left] [IsIntegral (V ⊗ V).left] [IsLocallyNoetherian (V ⊗ V).left]
    [∀ v : V.left, UniqueFactorizationMonoid (V.left.presheaf.stalk v)]
    [∀ p : (V ⊗ V).left, UniqueFactorizationMonoid ((V ⊗ V).left.presheaf.stalk p)]
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) :
    f.toRationalMap.domain = ⊤ := by
  have h : UniversallyClosed G.hom := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  exact domain_eq_top h.1 f hf

end

end RamanujanPetersson.JacDivisors

end


