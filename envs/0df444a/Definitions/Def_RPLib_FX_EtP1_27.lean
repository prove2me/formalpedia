-- Prove2me | Definitions.Def_RPLib_FX_EtP1_27
-- name    : RPLib_FX_EtP1_27
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T11:30:28.169506+00:00
-- url     : https://prove2.me/theorems/5df1030a-ab7d-562d-bb67-ba63a915d2cd
-- title:
--   Étale cohomology of the projective line, library file 27 of 34
-- statement:
--   File 27 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_CoInd`: S4-EtCompact, A1: co-induction from an open subgroup (group layer for `R²g_* = 0`)
--   * `S4.Def_RP_EtCompact_FibMk`: S4-EtCompact, B1b: fibre points from embeddings, and finite fixing sets
--   * `S4.Def_RP_EtCompact_StdSub`: S4-EtCompact, B1a: standard étale subalgebras of a separable closure
--   * `S4.Def_RP_EtCompact_GenStalk`: S4-EtCompact, B1c: `g_*` of an epimorphism is epi at the generic geometric point
--   * `S4.Def_RP_EtCompact_GPtIso`: S4-EtCompact, B1d: isomorphic geometric points, and the generic point through `g`
--   * `S4.Def_RP_EtCompact_Shrink`: S4-EtCompact: shrinking a neighbourhood of a germ (O8c (B), file C6c1)
--   * `S4.Def_RP_EtCompact_Delta`: S4-EtCompact: sections with prescribed germs over a closed point (O8c (B), file C6c2)
--   * `S4.Def_RP_EtCompact_CechFin`: S4-EtCompact: sheaves supported on closed points are Cech-exact (O8c (B), file C6d)
--   * `S4.Def_RP_EtCompact_PtSub`: S4-EtCompact, A2: Galois cohomology of an open subgroup over a field point
--   * `S4.Def_RP_EtCompact_ExtInj`: S4-EtCompact, E1a (O7b): extending sections of point-supported sheaves along injective étale arrows
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_42

/-!
# Étale cohomology of the projective line, library file 27 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_CoInd`: S4-EtCompact, A1: co-induction from an open subgroup (group layer for `R²g_* = 0`)
* `S4.Def_RP_EtCompact_FibMk`: S4-EtCompact, B1b: fibre points from embeddings, and finite fixing sets
* `S4.Def_RP_EtCompact_StdSub`: S4-EtCompact, B1a: standard étale subalgebras of a separable closure
* `S4.Def_RP_EtCompact_GenStalk`: S4-EtCompact, B1c: `g_*` of an epimorphism is epi at the generic geometric point
* `S4.Def_RP_EtCompact_GPtIso`: S4-EtCompact, B1d: isomorphic geometric points, and the generic point through `g`
* `S4.Def_RP_EtCompact_Shrink`: S4-EtCompact: shrinking a neighbourhood of a germ (O8c (B), file C6c1)
* `S4.Def_RP_EtCompact_Delta`: S4-EtCompact: sections with prescribed germs over a closed point (O8c (B), file C6c2)
* `S4.Def_RP_EtCompact_CechFin`: S4-EtCompact: sheaves supported on closed points are Cech-exact (O8c (B), file C6d)
* `S4.Def_RP_EtCompact_PtSub`: S4-EtCompact, A2: Galois cohomology of an open subgroup over a field point
* `S4.Def_RP_EtCompact_ExtInj`: S4-EtCompact, E1a (O7b): extending sections of point-supported sheaves along injective étale arrows
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_CoInd =====
section

/-!
# S4-EtCompact, A1: co-induction from an open subgroup (group layer for `R²g_* = 0`)

`H ≤ G` a subgroup, `σ` a representation of `H` on `X`.

* `CoInd.sub H σ = {f : G → X | f (h g) = σ h (f g)}` with `G` acting by right translation (`CoInd.rep`);
* `CoInd.unit : X → CoInd` (`H`-equivariant, `unit_equivariant`); `CoInd.map` (functorial, `map_injective`,
  `map_unit`);
* `CoInd.counit : CoInd(Res ρ) → M` for a `G`-representation `ρ` and finitely many cosets (`counit_rep`:
  `G`-equivariant; `counit_unit`: `counit ∘ unit = id`);
* `CoInd.rep_isDiscrete`: co-induction from an open subgroup of finite index preserves discreteness;
  `IsDiscreteRep.comp_subtype`: restriction to a subgroup preserves it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtCompact.CoInd

attribute [local instance] Classical.propDecidable

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] (H : Subgroup G)

section Def

variable {X : Type*} [AddCommGroup X] [Module Λ X] (σ : Representation Λ H X)

variable {Y : Type*} [AddCommGroup Y] [Module Λ Y] {σ} {σY : Representation Λ H Y}

variable (φ : X →ₗ[Λ] Y) (hφ : ∀ h : H, φ ∘ₗ σ h = σY h ∘ₗ φ)

end Def

section Counit

variable {M : Type*} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ G M)

theorem term_eq (f : sub H (ρ.comp H.subtype)) (c : RC H) (g : G)
    (hc : Quotient.mk (QuotientGroup.rightRel H) g = c) :
    ρ (c.out)⁻¹ ((f : G → M) c.out) = ρ g⁻¹ ((f : G → M) g) := by
  subst hc
  obtain ⟨h, hh⟩ := exists_out_eq H g
  rw [hh, inv_apply_mul]

variable [Fintype (RC H)]

/-- **The counit** `CoInd_H^G (Res ρ) → M`, `f ↦ ∑_{Hg} g⁻¹ f(g)`. -/
def counit : sub H (ρ.comp H.subtype) →ₗ[Λ] M :=
  ∑ c : RC H, ρ (c.out)⁻¹ ∘ₗ LinearMap.proj (R := Λ) (φ := fun _ : G => M) c.out ∘ₗ
    (sub H (ρ.comp H.subtype)).subtype

theorem counit_apply (f : sub H (ρ.comp H.subtype)) :
    counit H ρ f = ∑ c : RC H, ρ (c.out)⁻¹ ((f : G → M) c.out) := by
  rw [counit, LinearMap.sum_apply]
  rfl

theorem counit_rep (τ : G) (f : sub H (ρ.comp H.subtype)) :
    counit H ρ (rep H (ρ.comp H.subtype) τ f) = ρ τ (counit H ρ f) := by
  let e : RC H ≃ RC H := Quotient.congr (Equiv.mulRight τ) fun a b => by
    refine QuotientGroup.rightRel_apply.trans (Iff.trans ?_ QuotientGroup.rightRel_apply.symm)
    show b * a⁻¹ ∈ H ↔ b * τ * (a * τ)⁻¹ ∈ H
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel_right]
  have he : ∀ c : RC H, e c = Quotient.mk (QuotientGroup.rightRel H) (c.out * τ) := fun c => by
    have h := Quotient.congr_mk (ra := QuotientGroup.rightRel H) (rb := QuotientGroup.rightRel H)
      (Equiv.mulRight τ) (fun a b => by
        refine QuotientGroup.rightRel_apply.trans (Iff.trans ?_ QuotientGroup.rightRel_apply.symm)
        show b * a⁻¹ ∈ H ↔ b * τ * (a * τ)⁻¹ ∈ H
        rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel_right]) c.out
    rw [Quotient.out_eq] at h
    exact h
  rw [counit_apply, counit_apply, map_sum,
    ← Equiv.sum_comp e (fun c => ρ τ (ρ (c.out)⁻¹ ((f : G → M) c.out)))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [rep_apply, term_eq H ρ f (e c) (c.out * τ) (he c).symm, ← Module.End.mul_apply, ← map_mul, mul_inv_rev,
    mul_inv_cancel_left]

theorem counit_unit (x : M) : counit H ρ (unit H (ρ.comp H.subtype) x) = x := by
  rw [counit_apply, Finset.sum_eq_single (Quotient.mk (QuotientGroup.rightRel H) 1)]
  · rw [term_eq H ρ _ _ 1 rfl]
    show ρ 1⁻¹ (unitFun H (ρ.comp H.subtype) x 1) = x
    rw [unitFun, dif_pos H.one_mem, inv_one]
    show ρ 1 (ρ 1 x) = x
    rw [map_one, Module.End.one_apply, Module.End.one_apply]
  · intro c _ hc
    have hnot : c.out ∉ H := fun hm => hc ((Quotient.out_eq c).symm.trans
      (Quotient.sound (QuotientGroup.rightRel_apply.2 (by simpa using hm))))
    rw [unit_apply_not_mem H _ x hnot, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Counit

section Disc

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : Type*} [AddCommGroup X] [Module Λ X]

/-- **Co-induction from an open subgroup of finite index preserves discreteness.** -/
theorem rep_isDiscrete [Finite (RC H)] (hH : IsOpen (H : Set G)) {σ : Representation Λ H X}
    (hσ : IsDiscreteRep σ) : IsDiscreteRep (rep H σ) := by
  intro f
  choose K hKo hK using fun c : RC H => hσ ((f : G → X) c.out)
  let U : RC H → Subgroup G := fun c => ((K c).map H.subtype).comap (MulAut.conj c.out).toMonoidHom
  have hU : ∀ c, IsOpen (U c : Set G) := fun c => by
    have h1 : IsOpen (((K c).map H.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.coe_map]
      exact hH.isOpenEmbedding_subtypeVal.isOpenMap _ (hKo c)
    have h2 : Continuous fun τ : G => c.out * τ * (c.out)⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact h2.isOpen_preimage _ h1
  refine ⟨⨅ c, U c, ?_, fun τ hτ => ?_⟩
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hU
  · refine Subtype.ext (funext fun g => ?_)
    show (f : G → X) (g * τ) = (f : G → X) g
    obtain ⟨h, hh⟩ := exists_out_eq H g
    have hτc : τ ∈ ((K (Quotient.mk (QuotientGroup.rightRel H) g)).map H.subtype).comap
        (MulAut.conj (Quotient.mk (QuotientGroup.rightRel H) g).out).toMonoidHom := Subgroup.mem_iInf.1 hτ _
    obtain ⟨k, hk, hk'⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hτc)
    have hk2 : (k : G) = (Quotient.mk (QuotientGroup.rightRel H) g).out * τ *
        ((Quotient.mk (QuotientGroup.rightRel H) g).out)⁻¹ := hk'
    have hg : g = ((h⁻¹ : H) : G) * (Quotient.mk (QuotientGroup.rightRel H) g).out := by
      rw [hh, Subgroup.coe_inv, inv_mul_cancel_left]
    have hgτ : g * τ = ((h⁻¹ * k : H) : G) * (Quotient.mk (QuotientGroup.rightRel H) g).out := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hk2, hh]
      group
    rw [hgτ, sub_apply, map_mul, Module.End.mul_apply, hK _ k hk, ← sub_apply, ← hg]

end Disc

end RamanujanPetersson.EtCompact.CoInd

end

end

-- ===== S4.Def_RP_EtCompact_FibMk =====
section

/-!
# S4-EtCompact, B1b: fibre points from embeddings, and finite fixing sets

`A` a domain, `g = gen A`, `x0`, `Ω = κ(x0)^sep` (an `A`-algebra), `B` étale over `A`.

* **`fibOf ψ : Fib A B`** for an `A`-algebra map `ψ : B →ₐ[A] Ω` (the lift `Spec Ω → Spec B ×_U Y`),
  `phi_fibOf`, **`phiB_fibOf`**: `φ_(fibOf ψ) = ψ`;
* **`fib_ext`**: fibre points with the same `φ` are equal;
* **`exists_fin_fix`**: every stalk element is fixed by all `σ` fixing some finite `T ⊆ κ(x)^sep` pointwise.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.FibMk

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.EtCompact.LT

section Fin

variable (Λ : Type) [CommRing Λ] {X : Scheme.{0}}

/-- **Finite fixing sets**: a stalk element is fixed by every `σ` fixing a finite set `T` pointwise. -/
theorem exists_fin_fix (F : EtSh Λ X) (x : X) (m : stalk Λ F x) :
    ∃ T : Finset (SeparableClosure (X.residueField x)),
      ∀ σ : Gal x, (∀ t ∈ T, σ t = t) → galRep Λ F x σ m = m := by
  classical
  obtain ⟨H, hH, hfix⟩ := exists_open_fix Λ F x m
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff (X.residueField x)
    (SeparableClosure (X.residueField x)) (H : Set (Gal x))).1 (hH.mem_nhds H.one_mem)
  let b := Module.finBasis (X.residueField x) E
  refine ⟨Finset.univ.image (fun i => (b i : SeparableClosure (X.residueField x))), fun σ hσ => hfix σ (hsub ?_)⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have key : σ.toLinearMap ∘ₗ E.val.toLinearMap = E.val.toLinearMap :=
    b.ext fun i => hσ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact LinearMap.congr_fun key ⟨y, hy⟩

end Fin

variable {A : Type} [CommRing A] [IsDomain A] {B : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B]

theorem cond (ψ : B →ₐ[A] SeparableClosure (κ0 A)) :
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (specEt A B).hom = (geomPtAt (x0 A)).pt ≫ gen A := by
  refine Eq.trans ?_ (Spec.map_preimage ((geomPtAt (x0 A)).pt ≫ gen A))
  rw [preimage_pt]
  refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
  exact CommRingCat.hom_ext ψ.comp_algebraMap

/-- The fibre point of an `A`-algebra embedding `ψ : B →ₐ[A] Ω`. -/
def fibOf (ψ : B →ₐ[A] SeparableClosure (κ0 A)) : Fib A B :=
  (Over.homMk (pullback.lift (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (geomPtAt (x0 A)).pt (cond ψ))
    (pullback.lift_snd _ _ _) : CategoryTheory.Over.mk (geomPtAt (x0 A)).pt ⟶
      (Scheme.Etale.forget _).obj ((etPull (gen A)).obj (specEt A B)))

theorem liftOf_fibOf (ψ : B →ₐ[A] SeparableClosure (κ0 A)) :
    ((geomPtAt (x0 A)).liftOf (fibOf ψ)).left =
      pullback.lift (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (geomPtAt (x0 A)).pt (cond ψ) := rfl

theorem phi_fibOf (ψ : B →ₐ[A] SeparableClosure (κ0 A)) :
    FibPt.phi (x0 A) (gen A) (specEt A B) (𝟙 _) (fibOf ψ) = CommRingCat.ofHom ψ.toRingHom := by
  apply Spec.map_injective
  refine (FibPt.map_phi _ _ _ _ _).trans ?_
  refine (congrArg (((geomPtAt (x0 A)).liftOf (fibOf ψ)).left ≫ ·)
    (Category.comp_id (pullback.fst (specEt A B).hom (gen A)))).trans ?_
  exact pullback.lift_fst _ _ _

theorem phiB_fibOf (ψ : B →ₐ[A] SeparableClosure (κ0 A)) : phiB A (fibOf ψ) = ψ := by
  refine AlgHom.ext fun c => ?_
  exact congrArg (fun f => f.hom c) (phi_fibOf ψ)

/-- **Fibre points are determined by `φ`.** -/
theorem fib_ext {a a' : Fib A B} (h : ∀ c, phiB A a c = phiB A a' c) : a = a' := by
  have hφ : FibPt.phi (x0 A) (gen A) (specEt A B) (𝟙 _) a = FibPt.phi (x0 A) (gen A) (specEt A B) (𝟙 _) a' := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact h
  have e1 := FibPt.map_phi (x0 A) (gen A) (specEt A B) (𝟙 _) a
  have e2 := FibPt.map_phi (x0 A) (gen A) (specEt A B) (𝟙 _) a'
  rw [hφ, e2] at e1
  have e3 : ((geomPtAt (x0 A)).liftOf a).left ≫ pullback.fst (specEt A B).hom (gen A) =
      ((geomPtAt (x0 A)).liftOf a').left ≫ pullback.fst (specEt A B).hom (gen A) :=
    (congrArg (((geomPtAt (x0 A)).liftOf a).left ≫ ·)
      (Category.comp_id (pullback.fst (specEt A B).hom (gen A)))).symm.trans (e1.symm.trans
      (congrArg (((geomPtAt (x0 A)).liftOf a').left ≫ ·)
        (Category.comp_id (pullback.fst (specEt A B).hom (gen A)))))
  refine fiber_ext _ (pullback.hom_ext e3 ?_)
  exact (Over.w ((geomPtAt (x0 A)).liftOf a)).trans (Over.w ((geomPtAt (x0 A)).liftOf a')).symm

end RamanujanPetersson.EtCompact.FibMk

end

end

-- ===== S4.Def_RP_EtCompact_StdSub =====
section

/-!
# S4-EtCompact, B1a: standard étale subalgebras of a separable closure

`A` an integrally closed domain with fraction field `K`, `Ω/K` separable (an `A`-algebra through `K`).
* `pair θ hθ s`: the standard étale pair `(minpoly A θ, s · (minpoly A θ)')`, `hasMap`, **`lift_injective`**:
  its algebra `A[X][1/g]/(f)` embeds into `Ω` by `X ↦ θ`; `sub` its image, `etale_sub`;
* `eq_bot_of_comap`: in an `A`-subalgebra of `Ω` the only ideal over `(0) ⊆ A` is `⊥`;
* **`exists_sub`**: every finite `T ⊆ Ω` lies in an étale `A`-subalgebra `S ⊆ Ω` whose only prime over `(0)` is `⊥`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact.StdSub

variable {A K Ω : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field Ω] [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω]

variable (K) in
include K in
theorem algebraMap_injective : Function.Injective (algebraMap A Ω) := by
  rw [IsScalarTower.algebraMap_eq A K Ω]
  exact (algebraMap K Ω).injective.comp (IsFractionRing.injective A K)

variable (K) in
theorem isAlgebraic_A [Algebra.IsAlgebraic K Ω] (x : Ω) : IsAlgebraic A x :=
  (IsFractionRing.isAlgebraic_iff A K Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)

variable (K) in
/-- In an `A`-subalgebra of `Ω` (algebraic over `K`), the only ideal over `(0)` is `⊥`. -/
theorem eq_bot_of_comap [Algebra.IsAlgebraic K Ω] (S : Subalgebra A Ω) (P : Ideal S)
    (hP : P.comap (algebraMap A S) = ⊥) : P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  by_contra hx0
  exact Ideal.comap_ne_bot_of_algebraic_mem hx0 hx
    (Subalgebra.isAlgebraic_iff_isAlgebraic_val.2 (isAlgebraic_A K (x : Ω))) hP

/-- The standard étale pair `(minpoly A θ, C s * (minpoly A θ)')`. -/
def pair (θ : Ω) (hθ : IsIntegral A θ) (s : A) : StandardEtalePair A where
  f := minpoly A θ
  monic_f := minpoly.monic hθ
  g := C s * derivative (minpoly A θ)
  cond := ⟨C s, 0, 1, by ring⟩

theorem hasMap (θ : Ω) (hθ : IsIntegral A θ) (hsep : aeval θ (derivative (minpoly A θ)) ≠ 0) {s : A}
    (hs : algebraMap A Ω s ≠ 0) : (pair θ hθ s).HasMap θ := by
  refine ⟨minpoly.aeval A θ, ?_⟩
  show IsUnit (aeval θ (C s * derivative (minpoly A θ)))
  rw [map_mul, aeval_C]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero hs hsep)

variable [IsIntegrallyClosed A]

variable (K) in
include K in
/-- **The standard étale algebra embeds into `Ω`**. -/
theorem lift_injective (θ : Ω) (hθ : IsIntegral A θ) (s : A) (h : (pair θ hθ s).HasMap θ) :
    Function.Injective ((pair θ hθ s).lift θ h) := by
  haveI : Module.IsTorsionFree A Ω := Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_injective K)
  let Pr := pair θ hθ s
  let Q : StandardEtalePresentation A Pr.Ring :=
    { P := Pr, x := Pr.X, hasMap := Pr.hasMap_X,
      lift_bijective := by rw [Pr.lift_X_left, AlgHom.coe_id]; exact Function.bijective_id }
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨p, n, hpn⟩ := Q.exists_mul_aeval_x_g_pow_eq_aeval_x y
  change y * aeval Pr.X Pr.g ^ n = aeval Pr.X p at hpn
  have h1 : aeval θ p = 0 := by
    have e := congrArg (Pr.lift θ h) hpn
    rw [map_mul, hy, zero_mul, ← aeval_algHom_apply, Pr.lift_X] at e
    exact e.symm
  obtain ⟨r, hr⟩ := minpoly.isIntegrallyClosed_dvd hθ h1
  have h2 : aeval Pr.X p = 0 := by
    rw [hr, map_mul]
    have : aeval Pr.X (minpoly A θ) = 0 := Pr.hasMap_X.1
    rw [this, zero_mul]
  have hu : IsUnit (aeval Pr.X Pr.g ^ n) := Pr.hasMap_X.2.pow n
  exact hu.mul_left_eq_zero.1 (hpn.trans h2)

/-- The image of the standard étale algebra in `Ω`. -/
def sub (θ : Ω) (hθ : IsIntegral A θ) (s : A) (h : (pair θ hθ s).HasMap θ) : Subalgebra A Ω :=
  ((pair θ hθ s).lift θ h).range

variable (K) in
include K in
theorem etale_sub (θ : Ω) (hθ : IsIntegral A θ) (s : A) (h : (pair θ hθ s).HasMap θ) :
    Algebra.Etale A (sub θ hθ s h) := by
  let e : (pair θ hθ s).Ring ≃ₐ[A] sub θ hθ s h := AlgEquiv.ofInjective _ (lift_injective K θ hθ s h)
  haveI := Algebra.IsStandardEtale.of_equiv e
  infer_instance

theorem aeval_mem_sub (θ : Ω) (hθ : IsIntegral A θ) (s : A) (h : (pair θ hθ s).HasMap θ) (Q : A[X]) :
    aeval θ Q ∈ sub θ hθ s h :=
  (AlgHom.mem_range _).2 ⟨aeval (pair θ hθ s).X Q, by rw [← aeval_algHom_apply, StandardEtalePair.lift_X]⟩

theorem inv_mem_sub (θ : Ω) (hθ : IsIntegral A θ) (s : A) (h : (pair θ hθ s).HasMap θ)
    (hsep : aeval θ (derivative (minpoly A θ)) ≠ 0) (hs : algebraMap A Ω s ≠ 0) :
    (algebraMap A Ω s)⁻¹ ∈ sub θ hθ s h := by
  set P := pair θ hθ s
  let u := P.hasMap_X.2.unit
  have hgu : P.lift θ h (u : P.Ring) = aeval θ P.g := by
    show P.lift θ h (aeval P.X P.g) = _
    rw [← aeval_algHom_apply, P.lift_X]
  have hg : aeval θ P.g = algebraMap A Ω s * aeval θ (derivative (minpoly A θ)) := by
    show aeval θ (C s * derivative (minpoly A θ)) = _
    rw [map_mul, aeval_C]
  have hinv : P.lift θ h (↑u⁻¹ : P.Ring) = (aeval θ P.g)⁻¹ := by
    rw [← hgu]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  have hm : (aeval θ P.g)⁻¹ ∈ sub θ hθ s h := (AlgHom.mem_range _).2 ⟨_, hinv⟩
  have e : (algebraMap A Ω s)⁻¹ = aeval θ (derivative (minpoly A θ)) * (aeval θ P.g)⁻¹ := by
    rw [hg, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hsep, one_mul]
  rw [e]
  exact Subalgebra.mul_mem _ (aeval_mem_sub θ hθ s h _) hm

variable (A) in
/-- Clearing denominators: `b • aeval θ P = aeval θ Q` with `Q ∈ A[X]`. -/
theorem exists_clear (θ : Ω) (P : K[X]) : ∃ b : A, b ≠ 0 ∧ ∃ Q : A[X], algebraMap A Ω b * aeval θ P = aeval θ Q := by
  obtain ⟨b, hb, hbP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) P
  refine ⟨b, nonZeroDivisors.ne_zero hb, IsLocalization.integerNormalization (nonZeroDivisors A) P, ?_⟩
  rw [← aeval_map_algebraMap K θ (IsLocalization.integerNormalization (nonZeroDivisors A) P), hbP,
    Algebra.smul_def, map_mul, Polynomial.algebraMap_apply, aeval_C, IsScalarTower.algebraMap_apply A K Ω]

variable (K) in
/-- **Standard étale subalgebras**: every finite `T ⊆ Ω` lies in an étale `A`-subalgebra of `Ω` in which `⊥` is the
only ideal over `(0) ⊆ A`. -/
theorem exists_sub [Algebra.IsSeparable K Ω] (T : Finset Ω) :
    ∃ S : Subalgebra A Ω, Algebra.Etale A S ∧ (∀ t ∈ T, t ∈ S) ∧
      ∀ P : Ideal S, P.comap (algebraMap A S) = ⊥ → P = ⊥ := by
  classical
  -- a primitive element of `K⟮T⟯`
  let M : IntermediateField K Ω := IntermediateField.adjoin K (T : Set Ω)
  haveI : FiniteDimensional K M := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsSeparable.isSeparable K x).isIntegral)
  haveI : Algebra.IsSeparable K M := Algebra.isSeparable_tower_bot_of_isSeparable K M Ω
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K M
  have hT0 : ∀ t ∈ T, t ∈ IntermediateField.adjoin K {(α : Ω)} := by
    intro t ht
    have htM : t ∈ M := IntermediateField.subset_adjoin K _ ht
    have : t ∈ (IntermediateField.adjoin K {α}).map M.val :=
      (IntermediateField.mem_map _).2 ⟨⟨t, htM⟩, by rw [hα]; exact IntermediateField.mem_top, rfl⟩
    rwa [IntermediateField.adjoin_map, Set.image_singleton] at this
  -- an integral multiple
  obtain ⟨d, hd0, hdi⟩ := (isAlgebraic_A (A := A) K (α : Ω)).exists_integral_multiple
  set θ : Ω := d • (α : Ω) with hθdef
  have hd : algebraMap A Ω d ≠ 0 := fun h0 => hd0 (algebraMap_injective K (h0.trans (map_zero _).symm))
  have hle : IntermediateField.adjoin K {(α : Ω)} ≤ IntermediateField.adjoin K {θ} := by
    rw [IntermediateField.adjoin_simple_le_iff]
    have e : (α : Ω) = (algebraMap K Ω (algebraMap A K d))⁻¹ * θ := by
      rw [hθdef, Algebra.smul_def, ← IsScalarTower.algebraMap_apply A K Ω, inv_mul_cancel_left₀ hd]
    rw [e]
    exact mul_mem (inv_mem (IntermediateField.algebraMap_mem _ _)) (IntermediateField.mem_adjoin_simple_self K θ)
  have hθK : IsIntegral K θ := (Algebra.IsSeparable.isSeparable K θ).isIntegral
  have hT1 : ∀ t ∈ T, ∃ b : A, b ≠ 0 ∧ ∃ Q : A[X], algebraMap A Ω b * t = aeval θ Q := by
    intro t ht
    have h1 : t ∈ (IntermediateField.adjoin K {θ}).toSubalgebra := hle (hT0 t ht)
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθK.isAlgebraic, Algebra.adjoin_singleton_eq_range_aeval] at h1
    obtain ⟨P, rfl⟩ := (AlgHom.mem_range _).1 h1
    exact exists_clear A θ P
  choose! b hb0 Q hQ using hT1
  let s : A := ∏ t ∈ T, b t
  have hs0 : s ≠ 0 := Finset.prod_ne_zero_iff.2 hb0
  have hs : algebraMap A Ω s ≠ 0 := fun h0 => hs0 (algebraMap_injective K (h0.trans (map_zero _).symm))
  have hsep : aeval θ (derivative (minpoly A θ)) ≠ 0 := by
    have := Polynomial.Separable.aeval_derivative_ne_zero (Algebra.IsSeparable.isSeparable K θ)
      (minpoly.aeval K θ)
    rwa [minpoly.isIntegrallyClosed_eq_field_fractions' K hdi, derivative_map, aeval_map_algebraMap] at this
  let h := hasMap θ hdi hsep hs
  refine ⟨sub θ hdi s h, etale_sub K θ hdi s h, fun t ht => ?_, eq_bot_of_comap K _⟩
  have hbt : algebraMap A Ω (b t) ≠ 0 := fun h0 => hb0 t ht (algebraMap_injective K (h0.trans (map_zero _).symm))
  have hinv : (algebraMap A Ω (b t))⁻¹ ∈ sub θ hdi s h := by
    have hsplit : algebraMap A Ω s = algebraMap A Ω (b t) * algebraMap A Ω (∏ t' ∈ T.erase t, b t') := by
      rw [← map_mul, Finset.mul_prod_erase T b ht]
    have hp : algebraMap A Ω (∏ t' ∈ T.erase t, b t') ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hsplit
      exact hs hsplit
    have e : (algebraMap A Ω (b t))⁻¹ = algebraMap A Ω (∏ t' ∈ T.erase t, b t') * (algebraMap A Ω s)⁻¹ := by
      rw [hsplit, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]
    rw [e]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (inv_mem_sub θ hdi s h hsep hs)
  have e : t = (algebraMap A Ω (b t))⁻¹ * aeval θ (Q t) := by
    rw [← hQ t ht, inv_mul_cancel_left₀ hbt]
  rw [e]
  exact Subalgebra.mul_mem _ hinv (aeval_mem_sub θ hdi s h _)

end RamanujanPetersson.EtCompact.StdSub

end

end

-- ===== S4.Def_RP_EtCompact_GenStalk =====
section

/-!
# S4-EtCompact, B1c: `g_*` of an epimorphism is epi at the generic geometric point

`A` an integrally closed domain, `g = gen A : Y = Spec κ(η) ⟶ U = Spec A`, `x̄0 = geomPtAt x0`, `p : I ⟶ Q` on `Y`.

* **`exists_lift_std`**: a section `q` of `Q` over `g^* Spec B` whose germ at `a` is `p(m)` lifts to `I` over
  `g^* Spec S` for an étale `A`-subalgebra `S ⊆ Ω` with `fibOf S.val ↦ a` (`S ⊇ φ_a(B)` and a finite fixing set
  of `m`, `StdSub.exists_sub`; one Galois orbit on the fibre, `GalLift.exists_lift_of_fixed`);
* **`epi_push`**: for `p` epi, `(g_* p)` is epi on the stalks at the point `comapPt g x̄0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GenStalk

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.EtCompact.LT
  RamanujanPetersson.EtCompact.FibMk

variable {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]
  {I Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))} (p : I ⟶ Q)

theorem galRep_mul_apply (F : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))))
    (σ τ : Gal (x0 A)) (m : stalk Λ F (x0 A)) :
    galRep Λ F (x0 A) (σ * τ) m = galRep Λ F (x0 A) σ (galRep Λ F (x0 A) τ m) := by
  rw [map_mul]
  rfl

theorem germ_galAct (F : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))))
    (τ : Gal (x0 A)) {W : (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))).Etale}
    (a : (geomPtAt (x0 A)).point.fiber.obj W) (z : F.obj.obj (op W)) :
    galRep Λ F (x0 A) τ (((geomPtAt (x0 A)).point.toPresheafFiber W a F.obj).hom z) =
      ((geomPtAt (x0 A)).point.toPresheafFiber W ((galAct (x0 A) τ).app W a) F.obj).hom z := by
  rw [galRep_apply]
  exact GeomPt.stalkAut_toPresheafFiber (geomPtAt (x0 A)) Λ _ _ F W a z

/-- `σ` fixes the fibre point of `S ⊆ Ω` iff it fixes `S` pointwise (one direction). -/
theorem fix_of_galAct (S : Subalgebra A (SeparableClosure (κ0 A))) [Algebra.Etale A S] (ρ : Gal (x0 A))
    (hρ : (galAct (x0 A) ρ).app _ (fibOf S.val) = fibOf S.val) (s : SeparableClosure (κ0 A)) (hs : s ∈ S) :
    ρ s = s := by
  have h := FibPt.phi_galAct_apply (x0 A) (gen A) (specEt A S) (𝟙 _) ρ (fibOf S.val) ⟨s, hs⟩
  rw [hρ] at h
  have e : (FibPt.phi (x0 A) (gen A) (specEt A S) (𝟙 _) (fibOf S.val)).hom ⟨s, hs⟩ = s :=
    congrArg (fun f => f.hom ⟨s, hs⟩) (phi_fibOf S.val)
  rw [e] at h
  exact h.symm

/-- **Lifting through a standard étale subalgebra of `Ω`.** -/
theorem exists_lift_std (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] (a : Fib A B)
    (q : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B)))) (m : stalk Λ I (x0 A))
    (hm : (((geomPtAt (x0 A)).stalkF Λ).map p).hom m =
      ((geomPtAt (x0 A)).point.toPresheafFiber _ a Q.obj).hom q) :
    ∃ (S : Subalgebra A (SeparableClosure (κ0 A))) (_ : Algebra.Etale A S) (ψ : B →ₐ[A] S)
      (f : I.obj.obj (op ((etPull (gen A)).obj (specEt A S)))),
      fmap A ψ (fibOf S.val) = a ∧
        (p.hom.app _).hom f = (Q.obj.map ((etPull (gen A)).map (specEtMap ψ)).op).hom q := by
  classical
  obtain ⟨T, hT⟩ := exists_fin_fix Λ I (x0 A) m
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := A) (A := B)
  let φ := phiB A a
  obtain ⟨S, hSet, hTS, huniq⟩ := StdSub.exists_sub (A := A) (κ0 A) (T ∪ G.image φ)
  have hφS : ∀ c, φ c ∈ S := by
    have hle : Algebra.adjoin A (G : Set B) ≤ S.comap φ :=
      Algebra.adjoin_le fun g hg => hTS _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg))
    intro c
    have hc : c ∈ Algebra.adjoin A (G : Set B) := by
      rw [hG]
      exact Algebra.mem_top
    exact hle hc
  let ψ : B →ₐ[A] S := φ.codRestrict S hφS
  have hfb : fmap A ψ (fibOf S.val) = a := fib_ext fun c => by
    rw [← phiB_map, phiB_fibOf]
    rfl
  let qS := (Q.obj.map ((etPull (gen A)).map (specEtMap ψ)).op).hom q
  have hb : ((geomPtAt (x0 A)).point.toPresheafFiber _ (fibOf S.val) Q.obj).hom qS =
      ((geomPtAt (x0 A)).point.toPresheafFiber _ a Q.obj).hom q := by
    have hw := congrArg (fun φ => φ.hom q) (GrothendieckTopology.Point.toPresheafFiber_w
      (Φ := (geomPtAt (x0 A)).point) ((etPull (gen A)).map (specEtMap ψ)) (fibOf S.val) Q.obj)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hw
    refine hw.trans ?_
    rw [← hfb]
    rfl
  have : Subsingleton ((etPull (gen A)).obj (specEt A S)).left :=
    Chart.subsingleton_pull fun P₁ P₂ h₁ h₂ => PrimeSpectrum.ext ((huniq _ h₁).trans (huniq _ h₂).symm)
  obtain ⟨f, hf⟩ := GalLift.exists_lift_of_fixed (x0 A) p ((etPull (gen A)).obj (specEt A S)) qS (fun a' => by
    obtain ⟨τ, hτ⟩ := FibPt.exists_galAct_eq (x0 A) (fibOf S.val) a'
    refine ⟨galRep Λ I (x0 A) τ m, fun σ hσ => ?_, ?_⟩
    · have hρ : (galAct (x0 A) (τ⁻¹ * σ * τ)).app _ (fibOf S.val) = fibOf S.val := by
        rw [galAct_mul, galAct_mul, hτ, hσ, ← hτ, ← galAct_mul, inv_mul_cancel, galAct_one]
      have hm' : galRep Λ I (x0 A) (τ⁻¹ * σ * τ) m = m := hT _ fun t ht =>
        fix_of_galAct S (τ⁻¹ * σ * τ) hρ t (hTS t (Finset.mem_union_left _ ht))
      rw [← galRep_mul_apply, show σ * τ = τ * (τ⁻¹ * σ * τ) by group, galRep_mul_apply, hm']
    · have h1 := LinearMap.congr_fun (galRep_natural Λ p (x0 A) τ) m
      simp only [LinearMap.comp_apply] at h1
      rw [h1, hm, ← hb, germ_galAct, hτ])
  exact ⟨S, hSet, ψ, f, hfb, hf⟩

end RamanujanPetersson.EtCompact.GenStalk

end

end

-- ===== S4.Def_RP_EtCompact_GPtIso =====
section

/-!
# S4-EtCompact, B1d: isomorphic geometric points, and the generic point through `g`

* `ptIso e`: an isomorphism `Over.mk s.pt ≅ Over.mk t.pt` of geometric points gives an isomorphism of points of the
  small étale site; `epi_of_ptIso`: stalk maps are epi together;
* `overIsoGeomPtAt`: a geometric point `Spec Ω' → Spec κ(x) → X` with `Ω'` separable over `κ(x)` is isomorphic
  to `geomPtAt x` (`IsSepClosure.equiv`);
* **`genPtIso A`**: `geomPtAt η ≅ comapPt g (geomPtAt x0)` for `g = gen A : Spec κ(η) ⟶ Spec A`;
* **`isZero_stalk_cokernel`**: the stalk of `coker φ` at `η` vanishes when `φ` is epi on the `comapPt` stalks.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GPtIso

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac

universe u

section General

variable {X : Scheme.{u}}

/-- An isomorphism of geometric points gives an isomorphism of points of the small étale site. -/
def ptIso {s t : GeomPt X} (e : CategoryTheory.Over.mk s.pt ≅ CategoryTheory.Over.mk t.pt) : s.point ≅ t.point :=
  let F : t.point.fiber ≅ s.point.fiber := Functor.isoWhiskerLeft (Scheme.Etale.forget X) (coyoneda.mapIso e.op)
  { hom := ⟨F.hom⟩
    inv := ⟨F.inv⟩
    hom_inv_id := by ext : 1; exact F.inv_hom_id
    inv_hom_id := by ext : 1; exact F.hom_inv_id }

variable (Λ : Type u) [CommRing Λ]

theorem epi_of_ptIso {Φ₁ Φ₂ : (Scheme.smallEtaleTopology X).Point} (e : Φ₁ ≅ Φ₂) {F G : EtSh Λ X} (φ : F ⟶ G)
    (h : Epi (Φ₂.sheafFiber.map φ)) : Epi (Φ₁.sheafFiber.map φ) := by
  have w := (ptIsoSheafFiber Λ e).hom.naturality φ
  have : Epi ((ptIsoSheafFiber Λ e).hom.app F ≫ Φ₁.sheafFiber.map φ) := by
    rw [← w]
    infer_instance
  exact epi_of_epi ((ptIsoSheafFiber Λ e).hom.app F) _

theorem isZero_cokernel (s : GeomPt X) {F G : EtSh Λ X} (φ : F ⟶ G) (h : Epi ((s.stalkF Λ).map φ)) :
    IsZero ((s.stalkF Λ).obj (cokernel φ)) :=
  (isZero_cokernel_of_epi ((s.stalkF Λ).map φ)).of_iso (PreservesCokernel.iso (s.stalkF Λ) φ)

/-- A geometric point `Spec Ω' → Spec κ(x) → X` with `Ω'` separable over `κ(x)` is isomorphic to `geomPtAt x`. -/
def overIsoGeomPtAt (x : X) (s : GeomPt X) (φ : X.residueField x ⟶ CommRingCat.of s.Ω)
    (hs : s.pt = Spec.map φ ≫ X.fromSpecResidueField x)
    (hsep : @Algebra.IsSeparable (X.residueField x) s.Ω _ _ φ.hom.toAlgebra) :
    CategoryTheory.Over.mk s.pt ≅ CategoryTheory.Over.mk (geomPtAt x).pt :=
  letI : Algebra (X.residueField x) s.Ω := φ.hom.toAlgebra
  haveI : IsSepClosure (X.residueField x) s.Ω := ⟨inferInstance, hsep⟩
  let σ : SeparableClosure (X.residueField x) ≃ₐ[X.residueField x] s.Ω := IsSepClosure.equiv _ _ _
  Over.isoMk (Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op) (by
    refine Eq.trans ?_ hs.symm
    change Spec.map σ.toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (SeparableClosure (X.residueField x)))) ≫
        X.fromSpecResidueField x = _
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext r
    exact σ.commutes r)

end General

section Gen

variable (A : Type) [CommRing A] [IsDomain A]

theorem pt_map_gen : ((geomPtAt (x0 A)).map (gen A)).pt =
    Spec.map ((ptResidueIso (GenBr.genPt A)).hom ≫ CommRingCat.ofHom (algebraMap (κ0 A) (SeparableClosure (κ0 A)))) ≫
      (Spec (CommRingCat.of A)).fromSpecResidueField (GenBr.genPt A) := by
  change (Spec.map (CommRingCat.ofHom (algebraMap (κ0 A) (SeparableClosure (κ0 A)))) ≫
    (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))).fromSpecResidueField (x0 A)) ≫ gen A = _
  rw [← map_ptResidueIso_hom]
  exact congrArg (· ≫ gen A) (Spec.map_comp _ _).symm

theorem sep_gen : @Algebra.IsSeparable ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))
    (SeparableClosure (κ0 A)) _ _ ((ptResidueIso (GenBr.genPt A)).hom ≫
      CommRingCat.ofHom (algebraMap (κ0 A) (SeparableClosure (κ0 A)))).hom.toAlgebra := by
  let _ : Algebra ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)) (SeparableClosure (κ0 A)) :=
    ((ptResidueIso (GenBr.genPt A)).hom ≫
      CommRingCat.ofHom (algebraMap (κ0 A) (SeparableClosure (κ0 A)))).hom.toAlgebra
  refine Algebra.IsSeparable.of_equiv_equiv (A₁ := κ0 A) (B₁ := SeparableClosure (κ0 A))
    (ptResidueIso (GenBr.genPt A)).symm.commRingCatIsoToRingEquiv (RingEquiv.refl _) ?_
  refine RingHom.ext fun r => ?_
  have e : (ptResidueIso (GenBr.genPt A)).hom.hom ((ptResidueIso (GenBr.genPt A)).inv.hom r) = r :=
    congrArg (fun f => f.hom r) (ptResidueIso (GenBr.genPt A)).inv_hom_id
  exact congrArg (algebraMap (κ0 A) (SeparableClosure (κ0 A))) e

/-- **The two geometric points at `η`**: `geomPtAt η ≅ comapPt g (geomPtAt x0)`. -/
def genPtIso : (geomPtAt (GenBr.genPt A)).point ≅ comapPt (gen A) (geomPtAt (x0 A)) :=
  (ptIso (overIsoGeomPtAt (GenBr.genPt A) ((geomPtAt (x0 A)).map (gen A)) _ (pt_map_gen A) (sep_gen A))).symm ≪≫
    comapPtIso (gen A) (geomPtAt (x0 A))

variable {A} {Λ : Type} [CommRing Λ]

/-- **B1d**: the stalk of `coker φ` at `η` vanishes if `φ` is epi on the stalks at `comapPt g x̄0`. -/
theorem isZero_stalk_cokernel {F G : EtSh Λ (Spec (CommRingCat.of A))} (φ : F ⟶ G)
    (h : Epi ((comapPt (gen A) (geomPtAt (x0 A))).sheafFiber.map φ)) :
    IsZero (stalk Λ (cokernel φ) (GenBr.genPt A)) :=
  isZero_cokernel Λ (geomPtAt (GenBr.genPt A)) φ (epi_of_ptIso Λ (genPtIso A) φ h)

end Gen

end RamanujanPetersson.EtCompact.GPtIso

end

end

-- ===== S4.Def_RP_EtCompact_Shrink =====
section

/-!
# S4-EtCompact: shrinking a neighbourhood of a germ (O8c (B), file C6c1)

* `opn W U`, `opnι W U`: the open etale sub-object of `W` on an open `U ⊆ W`.
* **`exists_shrink`**: for `F` with stalks vanishing at non-closed points (`Y` locally noetherian), a closed point
  `x`, a fibre point `a` of `x̄` over `T` and a germ `m ∈ F_x̄`, there is an etale neighbourhood `g : W ⟶ T` of `a`
  (fibre point `b`) and `z ∈ F(W)` with germ `m` at `b`, all other germs of `z` zero, and `fpt b` the only point
  of `W` over `fpt a`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

section Opn

variable {X : Scheme.{u}}

/-- The open etale sub-object of `W` on an open `U`. -/
def opn (W : X.Etale) (U : W.left.Opens) : X.Etale := Scheme.Etale.mk (U.ι ≫ W.hom)

/-- Its inclusion. -/
def opnι (W : X.Etale) (U : W.left.Opens) : opn W U ⟶ W := MorphismProperty.Over.homMk U.ι rfl

theorem opnι_mem (W : X.Etale) (U : W.left.Opens) (v : (opn W U).left) : (opnι W U).left v ∈ U :=
  (Scheme.Opens.range_ι U).subset ⟨v, rfl⟩

theorem opnι_injective (W : X.Etale) (U : W.left.Opens) : Function.Injective (opnι W U).left :=
  U.ι.isOpenEmbedding.injective

end Opn

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}} (F : EtSh Λ Y)

/-- **Shrinking**: a neighbourhood of a germ on which the section is supported at one point only. -/
theorem exists_shrink [IsLocallyNoetherian Y] (hF : ∀ y : Y, ¬ IsClosed ({y} : Set Y) → IsZero (Mx F y))
    (x : Y) (hx : IsClosed ({x} : Set Y)) {T : Y.Etale} (a : (geomPtAt x).point.fiber.obj T) (m : Mx F x) :
    ∃ (W : Y.Etale) (g : W ⟶ T) (b : (geomPtAt x).point.fiber.obj W) (z : F.obj.obj (op W)),
      (geomPtAt x).point.fiber.map g b = a ∧ ((geomPtAt x).point.toPresheafFiber W b F.obj).hom z = m ∧
      (∀ (y : Y) (c : (geomPtAt y).point.fiber.obj W), fpt y c ≠ fpt x b →
        ((geomPtAt y).point.toPresheafFiber W c F.obj).hom z = 0) ∧
      ∀ v : W.left, g.left v = fpt x a → v = fpt x b := by
  -- a representative of `m` over `T`
  obtain ⟨W0, b0, z0, hz0⟩ := (geomPtAt x).point.toPresheafFiber_jointly_surjective m
  let e1 : (geomPtAt x).point.fiber.Elements := ⟨W0, b0⟩
  let e2 : (geomPtAt x).point.fiber.Elements := ⟨T, a⟩
  let h1 := IsCofiltered.minToLeft e1 e2
  let h2 := IsCofiltered.minToRight e1 e2
  let W1 : Y.Etale := (IsCofiltered.min e1 e2).1
  let b1 : (geomPtAt x).point.fiber.obj W1 := (IsCofiltered.min e1 e2).2
  have hb1 : (geomPtAt x).point.fiber.map h1.1 b1 = b0 := h1.2
  have hb1' : (geomPtAt x).point.fiber.map h2.1 b1 = a := h2.2
  let z1 : F.obj.obj (op W1) := (F.obj.map h1.1.op).hom z0
  have hz1 : ((geomPtAt x).point.toPresheafFiber W1 b1 F.obj).hom z1 = m := by
    rw [germ_map, hb1]
    exact hz0
  -- an affine neighbourhood
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, -⟩ :=
    W1.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (fpt x b1)) isOpen_univ
  obtain ⟨b2, hb2, -⟩ := exists_lift_fib (opnι W1 V) x b1 (⟨fpt x b1, hwV⟩ : V) rfl
  have : IsAffine (opn W1 V).left := hV
  let W2 : Y.Etale := opn W1 V
  let z2 : F.obj.obj (op W2) := (F.obj.map (opnι W1 V).op).hom z1
  let g2 : W2 ⟶ T := opnι W1 V ≫ h2.1
  have hg2 : (geomPtAt x).point.fiber.map g2 b2 = a := by
    rw [Functor.map_comp_apply, hb2, hb1']
  have hz2 : ((geomPtAt x).point.toPresheafFiber W2 b2 F.obj).hom z2 = m := by
    rw [germ_map, hb2, hz1]
  -- remove the other support points and the other points over `fpt a`
  let A : Set W2.left := supp F z2 ∪ g2.left ⁻¹' {fpt x a}
  have hAx : ∀ v ∈ g2.left ⁻¹' {fpt x a}, W2.hom v = x := by
    intro v hv
    rw [← MorphismProperty.Over.w g2, Scheme.Hom.comp_apply, Set.mem_preimage.1 hv, fib_over]
  have hAcl : ∀ v ∈ A, IsClosed ({v} : Set W2.left) := by
    rintro v (hv | hv)
    · exact isClosed_pt v (isClosed_of_mem_supp F hF z2 hv)
    · exact isClosed_pt v (by rw [hAx v hv]; exact hx)
  have hAfin : A.Finite :=
    (finite_supp F hF z2).union ((finite_preimage_closed W2 x hx).subset fun v hv => hAx v hv)
  let A' : Set W2.left := A \ {fpt x b2}
  have hA'cl : IsClosed A' := by
    have hA'fin : A'.Finite := hAfin.subset Set.sdiff_subset
    have := hA'fin.isClosed_biUnion (f := fun v => ({v} : Set W2.left)) fun v hv => hAcl v hv.1
    rwa [Set.biUnion_of_singleton] at this
  let O : W2.left.Opens := ⟨A'ᶜ, hA'cl.isOpen_compl⟩
  have hwO : fpt x b2 ∈ O := fun h => h.2 rfl
  obtain ⟨b3, hb3, hb3'⟩ := exists_lift_fib (opnι W2 O) x b2 (⟨fpt x b2, hwO⟩ : O) rfl
  have hw3 : (opnι W2 O).left (fpt x b3) = fpt x b2 := by rw [hb3']; rfl
  have key : ∀ v : (opn W2 O).left, (opnι W2 O).left v ∈ A → v = fpt x b3 := by
    intro v hv
    refine opnι_injective W2 O ?_
    rw [hw3]
    by_contra hne
    exact opnι_mem W2 O v ⟨hv, hne⟩
  refine ⟨opn W2 O, opnι W2 O ≫ g2, b3, (F.obj.map (opnι W2 O).op).hom z2, ?_, ?_, ?_, ?_⟩
  · rw [Functor.map_comp_apply, hb3, hg2]
  · rw [germ_map, hb3, hz2]
  · intro y c hc
    rw [germ_map]
    refine germ_eq_zero_of_not_mem_supp F z2 y _ fun hs => hc ?_
    exact key (fpt y c) (Or.inl hs)
  · intro v hv
    exact key v (Or.inr hv)

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_Delta =====
section

/-!
# S4-EtCompact: sections with prescribed germs over a closed point (O8c (B), file C6c2)

Hypotheses: `Y` locally noetherian, the stalks of `F` vanish at non-closed points (`hF`), `Gal y` is trivial at
closed points (`hG`).
* `glue2`: gluing along a two-element cover.
* **`exists_delta`**: for a closed `x`, a fibre point `a` of `x̄` over `T` and `m ∈ F_x̄` there is `s ∈ F(T)` with germ
  `m` at `a` and germ `0` at every fibre point over another point of `T`.
* **`exists_ux_eq`**: over a quasi-compact `T`, every section of `x̄_* F_x̄` is `ux x s` for some `s` with
  `ux y s = 0` for all `y ≠ x`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}} (F : EtSh Λ Y)

/-- Gluing along a cover by two etale arrows. -/
theorem glue2 {T W T' : Y.Etale} (g : W ⟶ T) (j : T' ⟶ T)
    (hcov : ∀ p : T.left, (∃ w, g.left w = p) ∨ ∃ v, j.left v = p) (z : F.obj.obj (op W))
    (z' : F.obj.obj (op T'))
    (h11 : ∀ (Z : Y.Etale) (u v : Z ⟶ W), u ≫ g = v ≫ g →
      (F.obj.map u.op).hom z = (F.obj.map v.op).hom z)
    (h12 : ∀ (Z : Y.Etale) (u : Z ⟶ W) (v : Z ⟶ T'), u ≫ g = v ≫ j →
      (F.obj.map u.op).hom z = (F.obj.map v.op).hom z')
    (h22 : ∀ (Z : Y.Etale) (u v : Z ⟶ T'), u ≫ j = v ≫ j →
      (F.obj.map u.op).hom z' = (F.obj.map v.op).hom z') :
    ∃ s : F.obj.obj (op T), (F.obj.map g.op).hom s = z ∧ (F.obj.map j.op).hom s = z' := by
  let V : Bool → Y.Etale := fun i => cond i W T'
  let f : ∀ i, V i ⟶ T := fun i => match i with
    | true => g
    | false => j
  let xs : ∀ i, F.obj.obj (op (V i)) := fun i => match i with
    | true => z
    | false => z'
  have hR : Sieve.ofArrows V f ∈ Y.smallEtaleTopology T := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 ?_
    rcases hcov p with ⟨w, hw⟩ | ⟨v, hv⟩
    · exact ⟨true, w, hw⟩
    · exact ⟨false, v, hv⟩
  have hc : ∀ i k (Z : Y.Etale) (gi : Z ⟶ V i) (gk : Z ⟶ V k), gi ≫ f i = gk ≫ f k →
      (F.obj.map gi.op).hom (xs i) = (F.obj.map gk.op).hom (xs k) := by
    intro i k Z gi gk e
    cases i <;> cases k
    · exact h22 Z gi gk e
    · exact (h12 Z gk gi e.symm).symm
    · exact h12 Z gi gk e
    · exact h11 Z gi gk e
  obtain ⟨s, hs, -⟩ := existsUnique_glue F f hR xs hc
  exact ⟨s, hs true, hs false⟩

/-- **A section with one prescribed germ over a closed point and no other germs.** -/
theorem exists_delta [IsLocallyNoetherian Y] (hF : ∀ y : Y, ¬ IsClosed ({y} : Set Y) → IsZero (Mx F y))
    (hG : ∀ y : Y, IsClosed ({y} : Set Y) → Subsingleton (Gal y))
    (x : Y) (hx : IsClosed ({x} : Set Y)) {T : Y.Etale} (a : (geomPtAt x).point.fiber.obj T) (m : Mx F x) :
    ∃ s : F.obj.obj (op T), ((geomPtAt x).point.toPresheafFiber T a F.obj).hom s = m ∧
      ∀ (y : Y) (a' : (geomPtAt y).point.fiber.obj T), fpt y a' ≠ fpt x a →
        ((geomPtAt y).point.toPresheafFiber T a' F.obj).hom s = 0 := by
  obtain ⟨W, g, b, z, hb, hz, hz0, hW⟩ := exists_shrink F hF x hx a m
  have hta : g.left (fpt x b) = fpt x a := by rw [← fib_left_map, hb]
  have ht : IsClosed ({fpt x a} : Set T.left) := isClosed_pt _ (by rw [fib_over]; exact hx)
  let U : T.left.Opens := ⟨{fpt x a}ᶜ, ht.isOpen_compl⟩
  have hz1 : ∀ (y : Y) (c : (geomPtAt y).point.fiber.obj W), g.left (fpt y c) ≠ fpt x a →
      ((geomPtAt y).point.toPresheafFiber W c F.obj).hom z = 0 :=
    fun y c hc => hz0 y c fun h => hc (h ▸ hta)
  have hcomp : ∀ {Z V' : Y.Etale} (u : Z ⟶ W) (v : Z ⟶ V') (k : V' ⟶ T), u ≫ g = v ≫ k →
      ∀ (y : Y) (c : (geomPtAt y).point.fiber.obj Z),
        g.left (fpt y ((geomPtAt y).point.fiber.map u c)) = k.left (fpt y ((geomPtAt y).point.fiber.map v c)) := by
    intro Z V' u v k e y c
    have e2 := congrArg (fun φ => fpt y ((geomPtAt y).point.fiber.map φ c)) e
    simp only [Functor.map_comp_apply, fib_left_map] at e2
    exact e2
  have hcov : ∀ p : T.left, (∃ w, g.left w = p) ∨ ∃ v, (opnι T U).left v = p := by
    intro p
    by_cases hp : p = fpt x a
    · exact Or.inl ⟨fpt x b, hta.trans hp.symm⟩
    · exact Or.inr ⟨(⟨p, hp⟩ : U), rfl⟩
  have h11 : ∀ (Z : Y.Etale) (u v : Z ⟶ W), u ≫ g = v ≫ g →
      (F.obj.map u.op).hom z = (F.obj.map v.op).hom z := by
    intro Z u v e
    refine eq_of_germs F _ _ fun y c => ?_
    rw [germ_map, germ_map]
    have e' := hcomp u v g e y c
    by_cases h : g.left (fpt y ((geomPtAt y).point.fiber.map u c)) = fpt x a
    · have hu := hW _ h
      have hv := hW _ (e'.symm.trans h)
      have hy : IsClosed ({y} : Set Y) := by
        rw [← fib_over y ((geomPtAt y).point.fiber.map u c), hu, fib_over]
        exact hx
      have := hG y hy
      rw [fiber_eq_of_pt y _ _ (hu.trans hv.symm)]
    · rw [hz1 y _ h, hz1 y _ fun h' => h (e'.trans h')]
  have h12 : ∀ (Z : Y.Etale) (u : Z ⟶ W) (v : Z ⟶ opn T U), u ≫ g = v ≫ opnι T U →
      (F.obj.map u.op).hom z = (F.obj.map v.op).hom 0 := by
    intro Z u v e
    rw [map_zero]
    refine eq_zero_of_germs F _ fun y c => ?_
    rw [germ_map]
    exact hz1 y _ fun h => opnι_mem T U _ ((hcomp u v (opnι T U) e y c).symm.trans h)
  have h22 : ∀ (Z : Y.Etale) (u v : Z ⟶ opn T U), u ≫ opnι T U = v ≫ opnι T U →
      (F.obj.map u.op).hom (0 : F.obj.obj (op (opn T U))) = (F.obj.map v.op).hom 0 := by
    intro Z u v _
    rw [map_zero, map_zero]
  obtain ⟨s, hs1, hs2⟩ := glue2 F g (opnι T U) hcov z 0 h11 h12 h22
  refine ⟨s, ?_, fun y a' ha' => ?_⟩
  · rw [← hb, ← germ_map, hs1, hz]
  · obtain ⟨c, hc, -⟩ := exists_lift_fib (opnι T U) y a' (⟨fpt y a', ha'⟩ : U) rfl
    rw [← hc, ← germ_map, hs2, map_zero]

/-- **Every section of `x̄_* F_x̄` over a quasi-compact `T` comes from a section of `F` supported over `x`.** -/
theorem exists_ux_eq [IsLocallyNoetherian Y] (hF : ∀ y : Y, ¬ IsClosed ({y} : Set Y) → IsZero (Mx F y))
    (hG : ∀ y : Y, IsClosed ({y} : Set Y) → Subsingleton (Gal y))
    (x : Y) (hx : IsClosed ({x} : Set Y)) {T : Y.Etale} [CompactSpace T.left]
    (w : ((geomPtAt x).point.skyscraperSheaf (Mx F x)).obj.obj (op T)) :
    ∃ s : F.obj.obj (op T), ((ux F x).hom.app (op T)).hom s = w ∧
      ∀ y : Y, y ≠ x → ((ux F y).hom.app (op T)).hom s = 0 := by
  have := hG x hx
  have := finite_fib x T hx
  haveI := Fintype.ofFinite ((geomPtAt x).point.fiber.obj T)
  choose d hd1 hd2 using fun a : (geomPtAt x).point.fiber.obj T =>
    exists_delta F hF hG x hx a ((Pi.π (fun _ => Mx F x) a).hom w)
  refine ⟨∑ a, d a, pi_ext (ι := (geomPtAt x).point.fiber.obj T) _ _
    fun a => (ux_π_apply F x a _).trans ?_, fun y hy => ?_⟩
  · rw [map_sum]
    refine (Finset.sum_eq_single a (fun a' _ ha' => ?_) fun h => absurd (Finset.mem_univ a) h).trans (hd1 a)
    exact hd2 a' x a fun h => ha' (fiber_eq_of_pt x _ _ h).symm
  · rw [ux_eq_zero_iff]
    intro a'
    rw [map_sum]
    refine Finset.sum_eq_zero fun a _ => hd2 a y a' fun h => hy ?_
    rw [← fib_over y a', h, fib_over]

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_CechFin =====
section

/-!
# S4-EtCompact: sheaves supported on closed points are Cech-exact (O8c (B), file C6d)

Hypotheses: `Y` locally noetherian, the stalks of `F` vanish at non-closed points (`hF`), `Gal y` is trivial at
closed points (`hG`).
* **`cechExact_of_closed`**: `F` is Cech-exact. A Cech cocycle `c` has finite support over a finite set `Z` of closed
  points; for `y ∈ Z`, `ux y c` is a cocycle of the (exact) Cech complex of the skyscraper `ȳ_* F_ȳ`, hence a
  coboundary `d b'_y`; `b'_y = ux y b_y` with `b_y` supported over `y` (`exists_ux_eq`), and `d (∑ b_y) = c` since
  both sides have the same image under every `ux y` (`eq_of_ux`).
* **`H_eq_zero_of_closed`**: on affine `Y` such sheaves have no higher cohomology (Cartan's lemma).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace AlgebraicTopology Simplicial
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}} (F : EtSh Λ Y)

/-- **Sheaves supported on closed points (with trivial Galois groups there) are Cech-exact.** -/
theorem cechExact_of_closed [IsLocallyNoetherian Y]
    (hF : ∀ y : Y, ¬ IsClosed ({y} : Set Y) → IsZero (Mx F y))
    (hG : ∀ y : Y, IsClosed ({y} : Set Y) → Subsingleton (Gal y)) : CechExact Λ F := by
  intro V W f hV hW hf n
  refine cech_exactAt_of_elt F f n fun c hc => ?_
  have hA1 : IsAffine (nv f (n + 1)).left := isAffine_cechNerve f (n + 1)
  have hA0 : IsAffine (nv f n).left := isAffine_cechNerve f n
  have hcov := cover_of_surjective f hf
  have hex : ∀ y : Y, ∃ b' : ((geomPtAt y).point.skyscraperSheaf (Mx F y)).obj.obj (op (nv f n)),
      (cd ((geomPtAt y).point.skyscraperSheaf (Mx F y)) f n (n + 1)).hom b' =
        ((ux F y).hom.app (op (nv f (n + 1)))).hom c := by
    intro y
    have h : (cechC Λ ((geomPtAt y).point.skyscraperSheaf (Mx F y)) f).ExactAt (n + 1) :=
      (skyCodeg (geomPtAt y).point (Mx F y) f (fun w => (fiber_map_surjective _ f hcov w).choose)
        fun w => (fiber_map_surjective _ f hcov w).choose_spec).exactAt_succ n
    exact cech_exact_elt _ f n (n + 1) (n + 2) rfl rfl h _ (by rw [cech_d_nat, hc, map_zero])
  choose b' hb' using hex
  let Z : Set Y := (nv f (n + 1)).hom '' supp F c
  have hZ : Z.Finite := (finite_supp F hF c).image _
  have hZc : ∀ y ∈ Z, IsClosed ({y} : Set Y) := by
    rintro _ ⟨t, ht, rfl⟩
    exact isClosed_of_mem_supp F hF c ht
  choose! bs hbs1 hbs2 using fun y (hy : y ∈ Z) => exists_ux_eq F hF hG y (hZc y hy) (b' y)
  refine ⟨∑ y ∈ hZ.toFinset, bs y, eq_of_ux F _ _ fun y => ?_⟩
  rw [← cech_d_nat, map_sum, map_sum]
  by_cases hy : y ∈ Z
  · refine (Finset.sum_eq_single y (fun y' hy' hne => ?_) fun h => absurd (hZ.mem_toFinset.2 hy) h).trans ?_
    · rw [hbs2 y' (hZ.mem_toFinset.1 hy') y hne.symm, map_zero]
    · rw [hbs1 y hy, hb']
  · refine (Finset.sum_eq_zero fun y' hy' => ?_).trans ?_
    · rw [hbs2 y' (hZ.mem_toFinset.1 hy') y (fun h => hy (by rw [h]; exact hZ.mem_toFinset.1 hy')), map_zero]
    · exact ((ux_eq_zero_iff F y c).2 fun a =>
        germ_eq_zero_of_not_mem_supp F c y a fun h => hy ⟨_, h, fib_over y a⟩).symm

/-- **On affine `Y`, sheaves supported on closed points (trivial Galois groups there) have no higher
cohomology.** -/
theorem H_eq_zero_of_closed [IsAffine Y] [IsLocallyNoetherian Y]
    (hF : ∀ y : Y, ¬ IsClosed ({y} : Set Y) → IsZero (Mx F y))
    (hG : ∀ y : Y, IsClosed ({y} : Set Y) → Subsingleton (Gal y)) (n : ℕ) (e : H Λ F (n + 1)) : e = 0 :=
  H_eq_zero_of_cechExact n F (cechExact_of_closed F hF hG) e

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_PtSub =====
section

/-!
# S4-EtCompact, A2: Galois cohomology of an open subgroup over a field point

`X ≅ Spec κ(x0)`, `H ≤ Gal x0` an open subgroup.

* `inj_extend`: for an injective sheaf `I`, the stalk `I_x̄` is injective among discrete Galois modules;
* **`coboundary_of_injective_sub`**: `H`-cocycles in `I_x̄` are coboundaries (co-induction `CoInd` + `inj_extend`);
* `PtH2Sub`, `ptH2Sub_of_hypL`: `H²(H, F_x̄) = 0` from `HypL ℓ (Gal x0)` (`hypL_subgroup`);
* **`coboundary_of_coker_sub`**: `H`-cocycles in `(I/F)_x̄` are coboundaries when `H²(H, F_x̄) = 0`;
* **`lift_fixed_sub`**: an `H`-fixed element of `(I/N)_x̄` lifts to an `H`-fixed element of `I_x̄` when
  `H¹(H, N_x̄) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Topology

noncomputable section

namespace RamanujanPetersson.EtCompact.PtSub

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne RamanujanPetersson.EtCompact

universe u

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] {Λ : Type u} [CommRing Λ]

/-- `Gal x0 ⧸ H` (right cosets) is finite for an open subgroup `H`. -/
theorem finite_rc (H : Subgroup (Gal x0)) (hH : IsOpen (H : Set (Gal x0))) : Finite (CoInd.RC H) :=
  have : Finite (Gal x0 ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm

/-- `H`-cocycle-level `H²(H, F_x̄) = 0`. -/
def PtH2Sub (H : Subgroup (Gal x0)) (F : EtSh Λ X) : Prop :=
  ∀ f : H × H → stalk Λ F x0, IsLocallyConstant f →
    (∀ g h j : H, f (g * h, j) + f (g, h) = galRep Λ F x0 g (f (h, j)) + f (g, h * j)) →
    ∃ a : H → stalk Λ F x0, IsLocallyConstant a ∧
      ∀ g h : H, f (g, h) = galRep Λ F x0 g (a h) - a (g * h) + a g

end RamanujanPetersson.EtCompact.PtSub

end

end

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

section Opn

variable {X : Scheme.{u}}

/-- The inclusion `opn T U' ⟶ opn T U` for `U' ≤ U`. -/
def opnLE (T : X.Etale) {U' U : T.left.Opens} (hle : U' ≤ U) : opn T U' ⟶ opn T U :=
  MorphismProperty.Over.homMk (T.left.homOfLE hle) (by
    change T.left.homOfLE hle ≫ U.ι ≫ T.hom = U'.ι ≫ T.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

theorem opnLE_left (T : X.Etale) {U' U : T.left.Opens} (hle : U' ≤ U) :
    (opnLE T hle).left = T.left.homOfLE hle := rfl

end Opn

end RamanujanPetersson.EtCompact.Cech

end

end


