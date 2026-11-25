-- Prove2me | Definitions.Def_RPLib_FX_EtP1_45
-- name    : RPLib_FX_EtP1_45
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T13:34:19.877643+00:00
-- url     : https://prove2.me/theorems/6ed32c27-882a-5fce-a41f-be4bb96327dc
-- title:
--   Étale cohomology of the projective line, library file 45 (an extra file from a re-cut)
-- statement:
--   File 45 (an extra file from a re-cut) of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_ExtInj`: S4-EtCompact, E1a (O7b): extending sections of point-supported sheaves along injective étale arrows
--   * `S4.Def_RP_EtCompact_CurveAll`: S4-EtCompact, D2 (O7, curve part): `H^(n+3) = 0` on `A¹`, `G_m` for every sheaf; `H^(n+4)(P¹, -) = 0`
--   * `S4.Def_RP_EtCompact_P1Cl`: S4-EtCompact, E0 (O7b): closed points of `P¹`
--   * `S4.Def_RP_EtCompact_P1Sky`: S4-EtCompact, E1b (O7b): `H¹` of point-supported sheaves on a union of two affines; `P¹`
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_29

/-!
# Étale cohomology of the projective line, library file 45 (extra file from a re-cut)

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_ExtInj`: S4-EtCompact, E1a (O7b): extending sections of point-supported sheaves along injective étale arrows
* `S4.Def_RP_EtCompact_CurveAll`: S4-EtCompact, D2 (O7, curve part): `H^(n+3) = 0` on `A¹`, `G_m` for every sheaf; `H^(n+4)(P¹, -) = 0`
* `S4.Def_RP_EtCompact_P1Cl`: S4-EtCompact, E0 (O7b): closed points of `P¹`
* `S4.Def_RP_EtCompact_P1Sky`: S4-EtCompact, E1b (O7b): `H¹` of point-supported sheaves on a union of two affines; `P¹`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_ExtInj =====
section

/-!
# S4-EtCompact, E1a (O7b): extending sections of point-supported sheaves along injective étale arrows

Hypotheses as in `Cech.exists_delta`: `Y` locally noetherian, the stalks of `F` vanish at non-closed points (`hF`),
`Gal y` is trivial at closed points (`hG`).

* **`ext_of_inj`**: for `h : W ⟶ T` with `h.left` injective and `W` affine, every section of `F` over `W` is the
  restriction of a section over `T`;
* `opnLE`, `opnLE_comp`: inclusions of open étale sub-objects; **`exists_factor`**: arrows into `opn T U` and `opn T V`
  agreeing over `T` factor through `opn T (U ⊓ V)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}} (F : EtSh Λ Y)

/-- **Extension along an injective étale arrow** for sheaves supported on closed points. -/
theorem ext_of_inj [IsLocallyNoetherian Y] (hF : ∀ y : Y, ¬ IsClosed ({y} : Set Y) → IsZero (Mx F y))
    (hG : ∀ y : Y, IsClosed ({y} : Set Y) → Subsingleton (Gal y))
    {W T : Y.Etale} (h : W ⟶ T) (hinj : Function.Injective h.left) [IsAffine W.left]
    (z : F.obj.obj (op W)) : ∃ t : F.obj.obj (op T), (F.obj.map h.op).hom t = z := by
  have hfin := finite_supp F hF z
  have : Fintype (supp F z) := hfin.fintype
  choose p hp1 hp2 using fun w : supp F z =>
    (show ∃ q : Σ y : Y, (geomPtAt y).point.fiber.obj W, fpt q.1 q.2 = w.1 ∧
        ((geomPtAt q.1).point.toPresheafFiber W q.2 F.obj).hom z ≠ 0 from
      by obtain ⟨y, a, ha, hne⟩ := w.2; exact ⟨⟨y, a⟩, ha, hne⟩)
  have hcl : ∀ w : supp F z, IsClosed ({(p w).1} : Set Y) := fun w => by
    have := isClosed_of_mem_supp F hF z w.2
    rwa [← hp1 w, fib_over] at this
  choose s hs1 hs2 using fun w : supp F z =>
    exists_delta F hF hG (p w).1 (hcl w) ((geomPtAt (p w).1).point.fiber.map h (p w).2)
      (((geomPtAt (p w).1).point.toPresheafFiber W (p w).2 F.obj).hom z)
  refine ⟨∑ w, s w, eq_of_germs F _ _ fun x c => ?_⟩
  rw [germ_map, map_sum]
  by_cases hc : fpt x c ∈ supp F z
  · let w0 : supp F z := ⟨fpt x c, hc⟩
    rw [Finset.sum_eq_single w0]
    · exact germ_restrict_eq F h hF hG z x c hc (p w0).1 (p w0).2 (s w0) (hs1 w0) (hp1 w0)
    · intro w _ hw
      refine hs2 w x _ fun he => hw (Subtype.ext ?_)
      rw [fib_left_map, fib_left_map] at he
      exact ((hp1 w).symm.trans (hinj he).symm)
    · exact fun h' => absurd (Finset.mem_univ w0) h'
  · rw [germ_eq_zero_of_not_mem_supp F z x c hc]
    refine Finset.sum_eq_zero fun w _ => hs2 w x _ fun he => hc ?_
    rw [fib_left_map, fib_left_map] at he
    rw [hinj he, hp1 w]
    exact w.2

section Opn

variable {X : Scheme.{u}}

/-- **Factorisation through the intersection.** -/
theorem exists_factor (T : X.Etale) (U V : T.left.Opens) {Z : X.Etale} (u : Z ⟶ opn T U) (v : Z ⟶ opn T V)
    (huv : u ≫ opnι T U = v ≫ opnι T V) :
    ∃ w : Z ⟶ opn T (U ⊓ V), w ≫ opnLE T inf_le_left = u ∧ w ≫ opnLE T inf_le_right = v := by
  have hl : u.left ≫ U.ι = v.left ≫ V.ι := congrArg (fun f => f.left) huv
  have hr : Set.range (u.left ≫ U.ι) ⊆ Set.range (U ⊓ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · have hm : U.ι (u.left z) ∈ Set.range U.ι := ⟨_, rfl⟩
      rw [Scheme.Opens.range_ι] at hm
      exact hm
    · rw [hl]
      have hm : V.ι (v.left z) ∈ Set.range V.ι := ⟨_, rfl⟩
      rw [Scheme.Opens.range_ι] at hm
      exact hm
  let l : Z.left ⟶ (U ⊓ V).toScheme := IsOpenImmersion.lift (U ⊓ V).ι (u.left ≫ U.ι) hr
  have hlf : l ≫ (U ⊓ V).ι = u.left ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  let w : Z ⟶ opn T (U ⊓ V) := MorphismProperty.Over.homMk l (by
    change l ≫ (U ⊓ V).ι ≫ T.hom = Z.hom
    rw [← Category.assoc, hlf]
    exact (Category.assoc u.left U.ι T.hom).trans (MorphismProperty.Over.w u))
  refine ⟨w, MorphismProperty.Over.Hom.ext ((cancel_mono U.ι).1 ?_),
    MorphismProperty.Over.Hom.ext ((cancel_mono V.ι).1 ?_)⟩
  · change (l ≫ T.left.homOfLE (inf_le_left : U ⊓ V ≤ U)) ≫ U.ι = u.left ≫ U.ι
    rw [Category.assoc, Scheme.homOfLE_ι, hlf]
  · change (l ≫ T.left.homOfLE (inf_le_right : U ⊓ V ≤ V)) ≫ V.ι = v.left ≫ V.ι
    rw [Category.assoc, Scheme.homOfLE_ι, hlf, hl]

end Opn

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_CurveAll =====
section

/-!
# S4-EtCompact, D2 (O7, curve part): `H^(n+3) = 0` on `A¹`, `G_m` for every sheaf; `H^(n+4)(P¹, -) = 0`

* `s1`, `s2`, **`ext_eq_zero_of_map`**: for `φ : F ⟶ G` with `Ext^(n+2)(A, ker φ) = Ext^(n+1)(A, coker φ) =
  Ext^(n+2)(A, G) = 0`, `Ext^(n+2)(A, F) = 0` (`0 → ker φ → F → im φ → 0`, `0 → im φ → G → coker φ → 0`);
* **`affine_H_add_three_eq_zero_all`**: `H^(n+3)(Spec A, F) = 0` for EVERY `F` (`A` noetherian integrally closed of
  dimension `≤ 1`, `H²(η, -) = 0`, `R²g_* = 0`, Galois-trivial closed points): `u = η_F : F ⟶ g_* g^* F` has kernel
  and cokernel supported on closed points (`GenUnit`), which are acyclic (`Cech.H_eq_zero_of_closed`);
* **`A1.H_add_three_eq_zero_all`**, **`Gm.H_add_three_eq_zero_all`** (`k = k̄`, `ℓ ≠ char k`, `ℓ^m Λ = 0`);
* **`P1.H_add_four_eq_zero_all`**: `H^(n+4)(P¹, G) = 0` for every `G` (Mayer-Vietoris).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact.CurveHn

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne RamanujanPetersson.EtCompact RamanujanPetersson.Tsen
  RamanujanPetersson.EtCompact.GenFrac

universe u

section Devissage

universe w v

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {F G : C} (φ : F ⟶ G)

theorem s1_shortExact : (s1 φ).ShortExact where
  exact := by
    let ψ : s1 φ ⟶ ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ) :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := Abelian.image.ι φ
        comm₁₂ := by simp
        comm₂₃ := by
          show 𝟙 _ ≫ φ = Abelian.factorThruImage φ ≫ Abelian.image.ι φ
          rw [Abelian.image.fac, Category.id_comp] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ))

/-- **Dévissage along `φ : F ⟶ G`.** -/
theorem ext_eq_zero_of_map (A : C) (n : ℕ) (hK : ∀ e : Abelian.Ext A (kernel φ) (n + 2), e = 0)
    (hC : ∀ e : Abelian.Ext A (cokernel φ) (n + 1), e = 0) (hG : ∀ e : Abelian.Ext A G (n + 2), e = 0)
    (e : Abelian.Ext A F (n + 2)) : e = 0 := by
  have e1 : (s1 φ).g ≫ (s2 φ).f = φ := Abelian.image.fac φ
  have h0 : (e.comp (Abelian.Ext.mk₀ (s1 φ).g) (add_zero _)).comp (Abelian.Ext.mk₀ (s2 φ).f) (add_zero _) = 0 := by
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, e1]
    exact hG _
  have hy : e.comp (Abelian.Ext.mk₀ (s1 φ).g) (add_zero _) = 0 := by
    obtain ⟨z, hz⟩ := Abelian.Ext.covariant_sequence_exact₁ _ (s2_shortExact φ)
      (e.comp (Abelian.Ext.mk₀ (s1 φ).g) (add_zero _)) h0 (show n + 1 + 1 = n + 2 from rfl)
    rw [← hz, hC z, Abelian.Ext.zero_comp]
  obtain ⟨x, hx⟩ := Abelian.Ext.covariant_sequence_exact₂ _ (s1_shortExact φ) e hy
  rw [← hx, hK x, Abelian.Ext.zero_comp]

end Devissage

/-- **`H^(n+3)(Spec A, F) = 0` for every sheaf `F`.** -/
theorem affine_H_add_three_eq_zero_all (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Ring.KrullDimLE 1 A] {Λ : Type} [CommRing Λ]
    (hG : ∀ y : Spec (CommRingCat.of A), IsClosed ({y} : Set (Spec (CommRingCat.of A))) → Subsingleton (Gal y))
    (hη : ∀ (M : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))) (e : H Λ M 2), e = 0)
    (hR : ∀ M : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))),
      IsZero (R1 (gen A) Λ (Qt Λ M)))
    (F : EtSh Λ (Spec (CommRingCat.of A))) (n : ℕ) (e : H Λ F (n + 3)) : e = 0 := by
  refine ext_eq_zero_of_map ((pullAdj (gen A) Λ).unit.app F) (unitSh Λ _) (n + 1) (fun e' => ?_) (fun e' => ?_)
    (fun e' => R1Gen.H_push_gen_eq_zero hG hη hR _ n e') e
  · refine Cech.H_eq_zero_of_closed _ (fun y hy => ?_) hG (n + 2) e'
    obtain rfl := R1Gen.eq_genPt y hy
    exact GenUnit.isZero_stalk_kernel_unit F
  · refine Cech.H_eq_zero_of_closed _ (fun y hy => ?_) hG (n + 1) e'
    obtain rfl := R1Gen.eq_genPt y hy
    exact GenUnit.isZero_stalk_cokernel_unit F

section Curves

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0)
  (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)

include hl hΛ

/-- **`H^(n+3)(A¹, F) = 0`** for every sheaf `F`. -/
theorem A1.H_add_three_eq_zero_all (F : EtSh Λ (A1 k)) (n : ℕ) (e : H Λ F (n + 3)) : e = 0 :=
  affine_H_add_three_eq_zero_all k[X] (fun y hy => gal_closed k k[X] y hy)
    (fun M e => H_genPt_eq_zero k l hl m hΛ 0 M e) (A1.isZero_R1_qt k l hl m hΛ) F n e

/-- **`H^(n+3)(G_m, F) = 0`** for every sheaf `F`. -/
theorem Gm.H_add_three_eq_zero_all (F : EtSh Λ (Gm k)) (n : ℕ) (e : H Λ F (n + 3)) : e = 0 :=
  affine_H_add_three_eq_zero_all (LX k) (fun y hy => gal_closed k (LX k) y hy)
    (fun M e => LX.H_genPt_eq_zero k l hl m hΛ 0 M e) (Gm.isZero_R1_qt k l hl m hΛ) F n e

end Curves

end RamanujanPetersson.EtCompact.CurveHn

end

end

-- ===== S4.Def_RP_EtCompact_P1Cl =====
section

/-!
# S4-EtCompact, E0 (O7b): closed points of `P¹`

* `isGenericPoint_bot`, **`map_genPt`**: an open immersion `Spec A ⟶ P¹` (`A` a domain) sends the generic point of
  `Spec A` to the generic point of `P¹`;
* **`P1.isClosed_of_ne_genPt`**: every point of `P¹` other than the generic point is closed;
* **`P1.gal_closed`**: closed points of `P¹` (over `k = k̄`) have trivial Galois groups.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact.CurveHn

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

theorem isGenericPoint_bot (A : Type) [CommRing A] [IsDomain A] :
    IsGenericPoint (GenBr.genPt A) (Set.univ : Set (Spec (CommRingCat.of A))) :=
  isGenericPoint_iff_specializes.2 fun _ =>
    ⟨fun _ => Set.mem_univ _, fun _ => (PrimeSpectrum.le_iff_specializes _ _).1 bot_le⟩

variable (k : Type) [Field k]

/-- An open immersion `Spec A ⟶ P¹` sends the generic point to the generic point. -/
theorem map_genPt (A : Type) [CommRing A] [IsDomain A] (f : Spec (CommRingCat.of A) ⟶ P1 k) [IsOpenImmersion f] :
    f (GenBr.genPt A) = P1.genPt k := by
  have h := (isGenericPoint_bot A).image f.continuous
  rw [Set.image_univ, ((f.isOpenEmbedding.isOpen_range).dense ⟨_, GenBr.genPt A, rfl⟩).closure_eq] at h
  exact h.eq (P1.isGenericPoint_genPt k)

/-- A non-generic point in the range of a chart has an open complement inside the chart. -/
theorem exists_open_of_chart (A : Type) [CommRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    (f : Spec (CommRingCat.of A) ⟶ P1 k) [IsOpenImmersion f] (y : P1 k) (hy : y ≠ P1.genPt k) (z : P1 k)
    (hz : z ∈ Set.range f) (hzy : z ≠ y) : ∃ O : Set (P1 k), IsOpen O ∧ z ∈ O ∧ y ∉ O := by
  by_cases hyf : y ∈ Set.range f
  · obtain ⟨t, rfl⟩ := hyf
    have ht : IsClosed ({t} : Set (Spec (CommRingCat.of A))) := by
      by_contra h
      exact hy ((congrArg f (R1Gen.eq_genPt t h)).trans (map_genPt k A f))
    obtain ⟨s, rfl⟩ := hz
    refine ⟨f '' ({t}ᶜ), f.isOpenEmbedding.isOpenMap _ ht.isOpen_compl, ⟨s, fun h => hzy (by rw [h]), rfl⟩, ?_⟩
    rintro ⟨s', hs', he⟩
    exact hs' (f.isOpenEmbedding.injective he)
  · exact ⟨Set.range f, f.isOpenEmbedding.isOpen_range, hz, hyf⟩

/-- **Every point of `P¹` other than the generic point is closed.** -/
theorem P1.isClosed_of_ne_genPt (y : P1 k) (hy : y ≠ P1.genPt k) : IsClosed ({y} : Set (P1 k)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  have hzy : z ≠ y := hz
  have key : ∃ O : Set (P1 k), IsOpen O ∧ z ∈ O ∧ y ∉ O := by
    rcases P1.cover k z with h | h
    · exact exists_open_of_chart k k[X] (chartA1 k) y hy z h hzy
    · exact exists_open_of_chart k k[X] (chartA1' k) y hy z h hzy
  obtain ⟨O, hO, hzO, hyO⟩ := key
  exact ⟨O, fun w hw (hw' : w = y) => hyO (hw' ▸ hw), hO, hzO⟩

/-- A closed point of `P¹` in the range of a chart from `A¹` has an algebraically closed residue field. -/
theorem isAlgClosed_of_chart [IsAlgClosed k] (f : A1 k ⟶ P1 k) [IsOpenImmersion f] (t : A1 k)
    (ht : f t ≠ P1.genPt k) : IsAlgClosed ((P1 k).residueField (f t)) := by
  have htc : IsClosed ({t} : Set (A1 k)) := by
    by_contra h
    exact ht ((congrArg f (R1Gen.eq_genPt t h)).trans (map_genPt k k[X] f))
  have := isAlgClosed_residue k k[X] t htc
  exact IsAlgClosed.of_ringEquiv _ _ (asIso (f.residueFieldMap t)).symm.commRingCatIsoToRingEquiv

/-- **Closed points of `P¹` have trivial Galois groups.** -/
theorem P1.gal_closed [IsAlgClosed k] (y : P1 k) (hy : IsClosed ({y} : Set (P1 k))) : Subsingleton (Gal y) := by
  have hy' : y ≠ P1.genPt k := by
    rintro rfl
    have h := (P1.isGenericPoint_genPt k).def
    rw [hy.closure_eq] at h
    have h2 : P1.infPt k ∈ ({P1.genPt k} : Set (P1 k)) := h ▸ Set.mem_univ _
    rw [Set.mem_singleton_iff] at h2
    exact P1.infPt_not_mem_range k (by rw [h2]; exact P1.genPt_mem_range k)
  rcases P1.cover k y with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have := isAlgClosed_of_chart k (chartA1 k) t hy'
    exact gal_subsingleton _
  · have := isAlgClosed_of_chart k (chartA1' k) t hy'
    exact gal_subsingleton _

end RamanujanPetersson.EtCompact.CurveHn

end

end

-- ===== S4.Def_RP_EtCompact_P1Sky =====
section

/-!
# S4-EtCompact, E1b (O7b): `H¹` of point-supported sheaves on a union of two affines; `P¹`

* **`sections_surj_cover`**: for a short exact `0 → X₁ → X₂ → X₃ → 0` with `X₁` supported on closed points (Galois-trivial
  there), global sections of `X₂ → X₃` are surjective on `Y = U ∪ V` with `U`, `V`, `U ∩ V` affine;
* **`H1_eq_zero_of_cover`**: then `H¹(Y, X₁) = 0` (Cartan's argument with `0 → F → god F → Q → 0`);
* `P1.isLocallyNoetherian`; **`P1.H1_closed`**: `H¹(P¹, Z) = 0` when `Z` has zero stalk at the generic point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry Opposite Abelian TopologicalSpace
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}}

/-- **Global sections are surjective** on a union of two affines with affine intersection. -/
theorem sections_surj_cover {S : ShortComplex (EtSh Λ Y)} (hS : S.ShortExact) [IsLocallyNoetherian Y]
    (hF : ∀ y : Y, ¬ IsClosed ({y} : Set Y) → IsZero (Mx S.X₁ y))
    (hG : ∀ y : Y, IsClosed ({y} : Set Y) → Subsingleton (Gal y))
    (U V : Y.Opens) (hUV : ∀ x : Y, x ∈ U ∨ x ∈ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUVa : IsAffineOpen (U ⊓ V)) :
    Function.Surjective (S.g.hom.app (op (etId Y))).hom := by
  intro q
  let T : Y.Etale := etId Y
  have h1 : CechExact Λ S.X₁ := cechExact_of_closed S.X₁ hF hG
  have : IsAffine (opn T U).left := hU
  have : IsAffine (opn T V).left := hV
  have : IsAffine (opn T (U ⊓ V)).left := hUVa
  obtain ⟨a1, ha1⟩ := sections_surj hS h1 (opn T U) ((S.X₃.obj.map (opnι T U).op).hom q)
  obtain ⟨a2, ha2⟩ := sections_surj hS h1 (opn T V) ((S.X₃.obj.map (opnι T V).op).hom q)
  let i1 : opn T (U ⊓ V) ⟶ opn T U := opnLE T inf_le_left
  let i2 : opn T (U ⊓ V) ⟶ opn T V := opnLE T inf_le_right
  -- naturality of `S.g` and `S.f` along restrictions
  have ng : ∀ {A B : Y.Etale} (r : A ⟶ B) (x : S.X₂.obj.obj (op B)),
      (S.g.hom.app (op A)).hom ((S.X₂.obj.map r.op).hom x) = (S.X₃.obj.map r.op).hom ((S.g.hom.app (op B)).hom x) :=
    fun r x => by rw [← ModuleCat.comp_apply, NatTrans.naturality, ModuleCat.comp_apply]
  have nf : ∀ {A B : Y.Etale} (r : A ⟶ B) (x : S.X₁.obj.obj (op B)),
      (S.f.hom.app (op A)).hom ((S.X₁.obj.map r.op).hom x) = (S.X₂.obj.map r.op).hom ((S.f.hom.app (op B)).hom x) :=
    fun r x => by rw [← ModuleCat.comp_apply, NatTrans.naturality, ModuleCat.comp_apply]
  have mc : ∀ {A B C : Y.Etale} (r : A ⟶ B) (r' : B ⟶ C) (x : S.X₃.obj.obj (op C)),
      (S.X₃.obj.map r.op).hom ((S.X₃.obj.map r'.op).hom x) = (S.X₃.obj.map (r ≫ r').op).hom x :=
    fun r r' x => by rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← op_comp]
  have hi1 : i1 ≫ opnι T U = opnι T (U ⊓ V) := opnLE_comp T _
  have hi2 : i2 ≫ opnι T V = opnι T (U ⊓ V) := opnLE_comp T _
  let d := (S.X₂.obj.map i1.op).hom a1 - (S.X₂.obj.map i2.op).hom a2
  have hd : (S.g.hom.app (op (opn T (U ⊓ V)))).hom d = 0 := by
    rw [map_sub, ng, ng, ha1, ha2, mc, mc, hi1, hi2, sub_self]
  obtain ⟨z, hz⟩ := sec_exact hS (opn T (U ⊓ V)) d hd
  obtain ⟨z1, hz1⟩ := ext_of_inj S.X₁ hF hG i1 (opnLE_injective T _) z
  let a1' := a1 - (S.f.hom.app (op (opn T U))).hom z1
  have hga1' : (S.g.hom.app (op (opn T U))).hom a1' = (S.X₃.obj.map (opnι T U).op).hom q := by
    rw [map_sub, sec_fg, sub_zero, ha1]
  have hres : (S.X₂.obj.map i1.op).hom a1' = (S.X₂.obj.map i2.op).hom a2 := by
    rw [map_sub, ← nf, hz1, hz]
    exact sub_sub_cancel _ _
  have mc2 : ∀ {A B C : Y.Etale} (r : A ⟶ B) (r' : B ⟶ C) (x : S.X₂.obj.obj (op C)),
      (S.X₂.obj.map (r ≫ r').op).hom x = (S.X₂.obj.map r.op).hom ((S.X₂.obj.map r'.op).hom x) :=
    fun r r' x => by rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← op_comp]
  have hcov : ∀ p : T.left, (∃ w, (opnι T U).left w = p) ∨ ∃ v, (opnι T V).left v = p := fun p => by
    rcases hUV p with hp | hp
    · left
      have hm : p ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hp
      exact hm
    · right
      have hm : p ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hp
      exact hm
  obtain ⟨p, hp1, hp2⟩ := glue2 S.X₂ (opnι T U) (opnι T V) hcov a1' a2
    (fun _ u v huv => by rw [opnι_cancel T U u v huv])
    (fun _ u v huv => by
      obtain ⟨w, hw1, hw2⟩ := exists_factor T U V u v huv
      rw [← hw1, ← hw2, mc2, mc2, hres])
    (fun _ u v huv => by rw [opnι_cancel T V u v huv])
  refine ⟨p, eq_of_germs S.X₃ _ _ fun x a => ?_⟩
  rcases hUV (fpt x a) with hp | hp
  · obtain ⟨w, hw⟩ : fpt x a ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hp
    obtain ⟨b, hb, -⟩ := exists_lift_fib (opnι T U) x a w hw
    rw [← hb, ← germ_map, ← germ_map, ← ng, hp1, hga1']
  · obtain ⟨w, hw⟩ : fpt x a ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hp
    obtain ⟨b, hb, -⟩ := exists_lift_fib (opnι T V) x a w hw
    rw [← hb, ← germ_map, ← germ_map, ← ng, hp2, ha2]

end RamanujanPetersson.EtCompact.Cech

namespace RamanujanPetersson.EtCompact.CurveHn

open RamanujanPetersson.EtCompact Polynomial

variable (k : Type) [Field k]

end RamanujanPetersson.EtCompact.CurveHn

end

end


