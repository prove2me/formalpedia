-- Prove2me | Definitions.Def_RPLib_FX_EtP1_43
-- name    : RPLib_FX_EtP1_43
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T12:12:13.603404+00:00
-- url     : https://prove2.me/theorems/9cb4b785-6a80-56f3-a879-1871cb24c25a
-- title:
--   Étale cohomology of the projective line, library file 43 (an extra file from a re-cut)
-- statement:
--   File 43 (an extra file from a re-cut) of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_GenStalk`: S4-EtCompact, B1c: `g_*` of an epimorphism is epi at the generic geometric point
--   * `S4.Def_RP_EtCompact_R1Gen`: S4-EtCompact, B1: `R¹g_* N` has vanishing generic stalk, hence no higher cohomology on a curve
--   * `S4.Def_RP_EtCompact_PtSub`: S4-EtCompact, A2: Galois cohomology of an open subgroup over a field point
--   * `S4.Def_RP_EtCompact_ExtInj`: S4-EtCompact, E1a (O7b): extending sections of point-supported sheaves along injective étale arrows
--   * `S4.Def_RP_EtSheaves_PullTens`: S4-EtSheaves, part 27: pullback is monoidal along every morphism
--   * `S4.Def_RP_EtCompact_GenUnit`: S4-EtCompact, D1: the unit `F ⟶ g_* g^* F` is an isomorphism at the generic point
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_27

/-!
# Étale cohomology of the projective line, library file 43 (extra file from a re-cut)

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_GenStalk`: S4-EtCompact, B1c: `g_*` of an epimorphism is epi at the generic geometric point
* `S4.Def_RP_EtCompact_R1Gen`: S4-EtCompact, B1: `R¹g_* N` has vanishing generic stalk, hence no higher cohomology on a curve
* `S4.Def_RP_EtCompact_PtSub`: S4-EtCompact, A2: Galois cohomology of an open subgroup over a field point
* `S4.Def_RP_EtCompact_ExtInj`: S4-EtCompact, E1a (O7b): extending sections of point-supported sheaves along injective étale arrows
* `S4.Def_RP_EtSheaves_PullTens`: S4-EtSheaves, part 27: pullback is monoidal along every morphism
* `S4.Def_RP_EtCompact_GenUnit`: S4-EtCompact, D1: the unit `F ⟶ g_* g^* F` is an isomorphism at the generic point
-/

set_option autoImplicit false

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

/-- **B1c**: `g_* p` is epi on the stalks at `comapPt g x̄0` when `p` is epi. -/
theorem epi_push [Epi p] :
    Epi ((comapPt (gen A) (geomPtAt (x0 A))).sheafFiber.map ((push (gen A) Λ).map p)) := by
  rw [ModuleCat.epi_iff_surjective]
  intro y
  obtain ⟨W, a, q, rfl⟩ := GrothendieckTopology.Point.toPresheafFiber_jointly_surjective (A := ModuleCat.{0} Λ)
    (comapPt (gen A) (geomPtAt (x0 A))) (P := ((push (gen A) Λ).obj Q).obj) y
  let a₀ : (geomPtAt (x0 A)).point.fiber.obj ((etPull (gen A)).obj W) := a
  obtain ⟨R, _, _, _, F, r, hr⟩ := Supp.exists_affine A W (pullback.fst W.hom (gen A) (Cech.fpt (x0 A) a₀))
  obtain ⟨t, ht⟩ := etPull_exists_preimage (gen A) F r (Cech.fpt (x0 A) a₀) hr
  obtain ⟨aR, haR, -⟩ := Cech.exists_lift_fib ((etPull (gen A)).map F) (x0 A) a₀ t ht
  let qR : Q.obj.obj (op ((etPull (gen A)).obj (specEt A R))) := (Q.obj.map ((etPull (gen A)).map F).op).hom q
  have : Epi (((geomPtAt (x0 A)).stalkF Λ).map p) := inferInstance
  obtain ⟨m, hm⟩ := (ModuleCat.epi_iff_surjective _).1 this
    (((geomPtAt (x0 A)).point.toPresheafFiber _ aR Q.obj).hom qR)
  obtain ⟨S, hS, ψ, f, hfb, hf⟩ := exists_lift_std p R aR qR m hm
  refine ⟨((comapPt (gen A) (geomPtAt (x0 A))).toPresheafFiber (specEt A S) (fibOf S.val)
    ((push (gen A) Λ).obj I).obj).hom f, ?_⟩
  have h1 := congrArg (fun φ => φ.hom f) (GrothendieckTopology.Point.toPresheafFiber_naturality
    (comapPt (gen A) (geomPtAt (x0 A))) ((push (gen A) Λ).map p).hom (specEt A S) (fibOf S.val))
  have h2 := congrArg (fun φ => φ.hom qR) (GrothendieckTopology.Point.toPresheafFiber_w
    (Φ := comapPt (gen A) (geomPtAt (x0 A))) (specEtMap ψ) (fibOf S.val) ((push (gen A) Λ).obj Q).obj)
  have h3 := congrArg (fun φ => φ.hom q) (GrothendieckTopology.Point.toPresheafFiber_w
    (Φ := comapPt (gen A) (geomPtAt (x0 A))) F aR ((push (gen A) Λ).obj Q).obj)
  have hf' : (((push (gen A) Λ).map p).hom.app (op (specEt A S))).hom f =
      (((push (gen A) Λ).obj Q).obj.map (specEtMap ψ).op).hom qR := hf
  have hfb' : (comapPt (gen A) (geomPtAt (x0 A))).fiber.map (specEtMap ψ) (fibOf S.val) = aR := hfb
  have haR' : (comapPt (gen A) (geomPtAt (x0 A))).fiber.map F aR = a := haR
  have e1 : ((comapPt (gen A) (geomPtAt (x0 A))).sheafFiber.map ((push (gen A) Λ).map p)).hom
      (((comapPt (gen A) (geomPtAt (x0 A))).toPresheafFiber (specEt A S) (fibOf S.val)
        ((push (gen A) Λ).obj I).obj).hom f) =
      ((comapPt (gen A) (geomPtAt (x0 A))).toPresheafFiber (specEt A S) (fibOf S.val)
        ((push (gen A) Λ).obj Q).obj).hom ((((push (gen A) Λ).obj Q).obj.map (specEtMap ψ).op).hom qR) :=
    h1.trans (congrArg ((comapPt (gen A) (geomPtAt (x0 A))).toPresheafFiber (specEt A S) (fibOf S.val)
      ((push (gen A) Λ).obj Q).obj).hom hf')
  refine e1.trans (h2.trans ((congrArg (fun z => ((comapPt (gen A) (geomPtAt (x0 A))).toPresheafFiber
    (specEt A R) z ((push (gen A) Λ).obj Q).obj).hom qR) hfb').trans (h3.trans ?_)))
  exact congrArg (fun z => ((comapPt (gen A) (geomPtAt (x0 A))).toPresheafFiber W z
    ((push (gen A) Λ).obj Q).obj).hom q) haR'

end RamanujanPetersson.EtCompact.GenStalk

end

end

-- ===== S4.Def_RP_EtCompact_R1Gen =====
section

/-!
# S4-EtCompact, B1: `R¹g_* N` has vanishing generic stalk, hence no higher cohomology on a curve

`A` a noetherian integrally closed domain of dimension `≤ 1`, `g = gen A : Spec κ(η) ⟶ Spec A`.

* **`isZero_R1_gen`**: the stalk of `R¹g_* N` at `η` vanishes (`GenStalk.epi_push` + `GPtIso.isZero_stalk_cokernel`);
* `eq_genPt`: the only non-closed point of `Spec A` is `η`; `hF_R1`;
* **`H_R1_eq_zero`**: `H^(n+1)(Spec A, R¹g_* N) = 0` when the closed points have trivial Galois groups
  (`Cech.H_eq_zero_of_closed`);
* **`H_push_gen_eq_zero`**: `H^(n+3)(Spec A, g_* N) = 0` given `H²(η, -) = 0` and `R²g_* = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.R1Gen

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac

variable {A : Type} [CommRing A] [IsDomain A] {Λ : Type} [CommRing Λ]

/-- **B1**: the generic stalk of `R¹g_* N` vanishes. -/
theorem isZero_R1_gen [IsIntegrallyClosed A]
    (N : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))) :
    IsZero (stalk Λ (R1 (gen A) Λ N) (GenBr.genPt A)) :=
  GPtIso.isZero_stalk_cokernel _ (GenStalk.epi_push (cokernel.π (Injective.ι N)))

theorem hF_R1 [IsIntegrallyClosed A] [Ring.KrullDimLE 1 A]
    (N : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))) (y : Spec (CommRingCat.of A))
    (hy : ¬ IsClosed ({y} : Set (Spec (CommRingCat.of A)))) : IsZero (Cech.Mx (R1 (gen A) Λ N) y) := by
  obtain rfl := eq_genPt y hy
  exact isZero_R1_gen N

/-- **`H^(n+1)(Spec A, R¹g_* N) = 0`** (closed points with trivial Galois groups). -/
theorem H_R1_eq_zero [IsNoetherianRing A] [IsIntegrallyClosed A] [Ring.KrullDimLE 1 A]
    (hG : ∀ y : Spec (CommRingCat.of A), IsClosed ({y} : Set (Spec (CommRingCat.of A))) → Subsingleton (Gal y))
    (N : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))) (n : ℕ)
    (e : H Λ (R1 (gen A) Λ N) (n + 1)) : e = 0 :=
  Cech.H_eq_zero_of_closed (R1 (gen A) Λ N) (hF_R1 N) hG n e

end RamanujanPetersson.EtCompact.R1Gen

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

/-- **`I_x̄` is injective among discrete Galois modules** for an injective sheaf `I`. -/
theorem inj_extend (I : EtSh Λ X) [Injective I] {A B : Type u} [AddCommGroup A] [Module Λ A]
    [AddCommGroup B] [Module Λ B] {ρA : Representation Λ (Gal x0) A} {ρB : Representation Λ (Gal x0) B}
    (hA : IsDiscreteRep ρA) (hB : IsDiscreteRep ρB) (j : A →ₗ[Λ] B) (hj : Function.Injective j)
    (hjeq : ∀ σ, j ∘ₗ ρA σ = ρB σ ∘ₗ j) (f : A →ₗ[Λ] stalk Λ I x0)
    (hf : ∀ σ, f ∘ₗ ρA σ = galRep Λ I x0 σ ∘ₗ f) :
    ∃ g : B →ₗ[Λ] stalk Λ I x0, g ∘ₗ j = f ∧ ∀ σ, g ∘ₗ ρB σ = galRep Λ I x0 σ ∘ₗ g := by
  obtain ⟨EA, eA, heA⟩ := specField_essSurj x0 Λ ρA hA
  obtain ⟨EB, eB, heB⟩ := specField_essSurj x0 Λ ρB hB
  let jl : stalk Λ EA x0 →ₗ[Λ] stalk Λ EB x0 := eB.symm.toLinearMap ∘ₗ j ∘ₗ eA.toLinearMap
  have hjl : ∀ σ : Gal x0, jl ∘ₗ galRep Λ EA x0 σ = galRep Λ EB x0 σ ∘ₗ jl := fun σ =>
    LinearMap.ext fun v => by
      apply eB.injective
      show eB (eB.symm (j (eA (galRep Λ EA x0 σ v)))) = eB (galRep Λ EB x0 σ (eB.symm (j (eA v))))
      rw [heB, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, heA]
      exact LinearMap.congr_fun (hjeq σ) (eA v)
  let fl : stalk Λ EA x0 →ₗ[Λ] stalk Λ I x0 := f ∘ₗ eA.toLinearMap
  have hfl : ∀ σ : Gal x0, fl ∘ₗ galRep Λ EA x0 σ = galRep Λ I x0 σ ∘ₗ fl := fun σ =>
    LinearMap.ext fun v => by
      show f (eA (galRep Λ EA x0 σ v)) = galRep Λ I x0 σ (f (eA v))
      rw [heA]
      exact LinearMap.congr_fun (hf σ) (eA v)
  let J : EA ⟶ EB := (specField_homEquiv x0 Λ EA EB).symm ⟨jl, hjl⟩
  have hJ : (((geomPtAt x0).stalkF Λ).map J).hom = jl :=
    congrArg Subtype.val ((specField_homEquiv x0 Λ EA EB).apply_symm_apply ⟨jl, hjl⟩)
  let F : EA ⟶ I := (specField_homEquiv x0 Λ EA I).symm ⟨fl, hfl⟩
  have hF : (((geomPtAt x0).stalkF Λ).map F).hom = fl :=
    congrArg Subtype.val ((specField_homEquiv x0 Λ EA I).apply_symm_apply ⟨fl, hfl⟩)
  have hmono : Mono J := by
    rw [mono_iff_stalk Λ J]
    intro x
    have := subsingleton_of_isIso x0
    rw [Subsingleton.elim x x0, ModuleCat.mono_iff_injective]
    show Function.Injective (((geomPtAt x0).stalkF Λ).map J).hom
    rw [hJ]
    exact eB.symm.injective.comp (hj.comp eA.injective)
  let r : EB ⟶ I := Injective.factorThru F J
  have hjr : J ≫ r = F := Injective.comp_factorThru F J
  refine ⟨(((geomPtAt x0).stalkF Λ).map r).hom ∘ₗ eB.symm.toLinearMap, ?_, fun σ => ?_⟩
  · refine LinearMap.ext fun a => ?_
    obtain ⟨v, rfl⟩ := eA.surjective a
    have h1 : (((geomPtAt x0).stalkF Λ).map (J ≫ r)).hom v = (((geomPtAt x0).stalkF Λ).map F).hom v := by
      rw [hjr]
    rw [CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hJ, hF] at h1
    exact h1
  · refine LinearMap.ext fun b => ?_
    obtain ⟨w, rfl⟩ := eB.surjective b
    show (((geomPtAt x0).stalkF Λ).map r).hom (eB.symm (ρB σ (eB w))) =
      galRep Λ I x0 σ ((((geomPtAt x0).stalkF Λ).map r).hom (eB.symm (eB w)))
    rw [← heB, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun (galRep_natural Λ r x0 σ) w

/-- **`H`-cocycles in an injective sheaf are coboundaries** (`H` open in `Gal x0`). -/
theorem coboundary_of_injective_sub (I : EtSh Λ X) [Injective I] (H : Subgroup (Gal x0))
    (hH : IsOpen (H : Set (Gal x0))) {b : H → stalk Λ I x0}
    (hb : IsCocycle ((galRep Λ I x0).comp H.subtype) b) (hbl : IsLocallyConstant b) :
    ∃ m₀ : stalk Λ I x0, ∀ g : H, b g = galRep Λ I x0 g m₀ - m₀ := by
  set ρ := galRep Λ I x0 with hρdef
  set σI := ρ.comp H.subtype with hσI
  have : Finite (CoInd.RC H) := finite_rc x0 H hH
  have : Fintype (CoInd.RC H) := Fintype.ofFinite _
  have hσd : IsDiscreteRep σI := (galRep_isDiscrete x0 I).comp_subtype H
  set E := extRep σI b hb with hEdef
  have hEd : IsDiscreteRep E := by
    intro v
    obtain ⟨K, hK, hv⟩ := hσd v.1
    refine ⟨repStab E v, Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      (Filter.inter_mem (hK.mem_nhds K.one_mem)
        ((hbl.isOpen_fiber 0).mem_nhds (show b 1 ∈ ({0} : Set (stalk Λ I x0)) from hb.map_one))) ?_),
      fun σ hσ => hσ⟩
    rintro σ ⟨hσK, hσ0⟩
    show E σ v = v
    rw [hEdef, extRep_apply, hv σ hσK, show b σ = 0 from hσ0, smul_zero, add_zero]
  have hinl : ∀ h : H, LinearMap.inl Λ (stalk Λ I x0) Λ ∘ₗ σI h = E h ∘ₗ LinearMap.inl Λ (stalk Λ I x0) Λ :=
    fun h => LinearMap.ext fun m => (extRep_inl σI hb h m).symm
  obtain ⟨g, hg, hgeq⟩ := inj_extend x0 I (CoInd.rep_isDiscrete H hH hσd) (CoInd.rep_isDiscrete H hH hEd)
    (CoInd.map H (LinearMap.inl Λ (stalk Λ I x0) Λ) hinl)
    (CoInd.map_injective H _ hinl LinearMap.inl_injective) (fun τ => LinearMap.ext fun f => rfl)
    (CoInd.counit H ρ) (fun τ => LinearMap.ext fun f => CoInd.counit_rep H ρ τ f)
  refine (exists_retraction_iff σI hb).1 ⟨g ∘ₗ CoInd.unit H E, LinearMap.ext fun m => ?_,
    fun s => LinearMap.ext fun v => ?_⟩
  · show g (CoInd.unit H E (LinearMap.inl Λ (stalk Λ I x0) Λ m)) = m
    rw [← CoInd.map_unit H _ hinl m]
    exact (LinearMap.congr_fun hg (CoInd.unit H σI m)).trans (CoInd.counit_unit H ρ m)
  · show g (CoInd.unit H E (E s v)) = σI s (g (CoInd.unit H E v))
    rw [CoInd.unit_equivariant H E s v]
    exact LinearMap.congr_fun (hgeq s) (CoInd.unit H E v)

/-- `PtH2Sub` from `HypL ℓ (Gal x0)` when `ℓ^k = 0` in `Λ`. -/
theorem ptH2Sub_of_hypL (l : ℕ) [Fact l.Prime] (hL : HypL l (Gal x0)) (k : ℕ) (hΛ : ((l ^ k : ℕ) : Λ) = 0)
    (H : Subgroup (Gal x0)) (hH : IsOpen (H : Set (Gal x0))) (F : EtSh Λ X) : PtH2Sub x0 H F := by
  intro f hf hc
  have : CompactSpace H := isCompact_iff_compactSpace.1 (H.isClosed_of_isOpen hH).isCompact
  exact h2_lcCob (ρ := (galRep Λ F x0).comp H.subtype) l (hypL_subgroup l hL H hH) k
    ((galRep_isDiscrete x0 F).comp_subtype H)
    (fun m => by rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]) hf hc

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

/-- Germs over a fibre point match after restriction along the fibre map. -/
theorem germ_restrict_eq {W T : Y.Etale} (h : W ⟶ T)
    (hF : ∀ y : Y, ¬ IsClosed ({y} : Set Y) → IsZero (Mx F y))
    (hG : ∀ y : Y, IsClosed ({y} : Set Y) → Subsingleton (Gal y))
    (z : F.obj.obj (op W)) (x : Y) (c : (geomPtAt x).point.fiber.obj W) (hc : fpt x c ∈ supp F z)
    (y : Y) (b : (geomPtAt y).point.fiber.obj W) (sw : F.obj.obj (op T))
    (h1 : ((geomPtAt y).point.toPresheafFiber T ((geomPtAt y).point.fiber.map h b) F.obj).hom sw =
      ((geomPtAt y).point.toPresheafFiber W b F.obj).hom z)
    (h2 : fpt y b = fpt x c) :
    ((geomPtAt x).point.toPresheafFiber T ((geomPtAt x).point.fiber.map h c) F.obj).hom sw =
      ((geomPtAt x).point.toPresheafFiber W c F.obj).hom z := by
  have hy : y = x := (fib_over y b).symm.trans ((congrArg W.hom h2).trans (fib_over x c))
  subst hy
  have hcl : IsClosed ({y} : Set Y) := by
    have := isClosed_of_mem_supp F hF z hc
    rwa [fib_over] at this
  have := hG y hcl
  have hbc : b = c := fiber_eq_of_pt y b c h2
  subst hbc
  exact h1

section Opn

variable {X : Scheme.{u}}

theorem opnLE_comp (T : X.Etale) {U' U : T.left.Opens} (hle : U' ≤ U) : opnLE T hle ≫ opnι T U = opnι T U' :=
  MorphismProperty.Over.Hom.ext (Scheme.homOfLE_ι _ hle)

theorem opnLE_injective (T : X.Etale) {U' U : T.left.Opens} (hle : U' ≤ U) :
    Function.Injective (opnLE T hle).left :=
  (T.left.homOfLE hle).isOpenEmbedding.injective

theorem opnι_cancel (T : X.Etale) (U : T.left.Opens) {Z : X.Etale} (u v : Z ⟶ opn T U)
    (h : u ≫ opnι T U = v ≫ opnι T U) : u = v := by
  have h' : u.left ≫ U.ι = v.left ≫ U.ι := congrArg (fun f => f.left) h
  exact MorphismProperty.Over.Hom.ext ((cancel_mono U.ι).1 h')

end Opn

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtSheaves_PullTens =====
section

/-!
# S4-EtSheaves, part 27: pullback is monoidal along every morphism

For any `f : X ⟶ Y` and etale sheaves `F G` on `Y`: `f^*(F ⊗ G) ≅ f^*F ⊗ f^*G` (`pullTensIsoGen`),
and the `Core` form `IsEt.pullTensAny`.

Route: the comparison map `δ : f^*(F ⊗ G) ⟶ f^*F ⊗ f^*G` (`pullTensMap`) is the adjoint transpose of
`γ : F ⊗ G ⟶ f_*(f^*F ⊗ f^*G)` (`tensUnit`: sheafified `η_F ⊗ η_G`). It is an isomorphism on stalks:
the base-change map `ρ_A : (f_*A)_{s ≫ f} ⟶ A_s` (`pushFib`, on germs `A(V ×_Y X)` at `b`) satisfies
`β_F = ψ(η_F) ≫ ρ_{f^*F}` for Mathlib's stalk isomorphism `β = sheafFiberComapIso` (`comapIso_hom_app`),
and `ψ(γ) ≫ ρ` is computed on germs of `z₁ ⊗ z₂` (`fib_tensUnitPre`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

section Gen

variable (Λ : Type u) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeomPt X)

/-- The base-change map `ρ_A : (f_* A)_{s ≫ f} ⟶ A_s`: the germ of `a ∈ A(V ×_Y X)` at `b`. -/
def pushFib (A : EtSh Λ X) :
    (comapPt f s).sheafFiber.obj ((push f Λ).obj A) ⟶ s.point.sheafFiber.obj A :=
  (comapPt f s).presheafFiberDesc (P := ((push f Λ).obj A).obj)
    (fun V b => s.point.toPresheafFiber ((etPull f).obj V) b A.obj)
    (fun _ _ g b => s.point.toPresheafFiber_w ((etPull f).map g) b A.obj)

@[reassoc]
theorem germ_pushFib (A : EtSh Λ X) (V : Y.Etale) (b : (comapPt f s).fiber.obj V) :
    (comapPt f s).toPresheafFiber V b ((push f Λ).obj A).obj ≫ pushFib Λ f s A =
      s.point.toPresheafFiber ((etPull f).obj V) b A.obj :=
  Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _

theorem skyUnit_hom_π (A : EtSh Λ X) (U : X.Etale) (x : s.point.fiber.obj U) :
    (s.point.skyscraperSheafAdjunction.unit.app A).hom.app (op U) ≫
        Pi.π (fun _ : s.point.fiber.obj U => s.point.sheafFiber.obj A) x =
      s.point.toPresheafFiber U x A.obj := by
  erw [← Adjunction.homEquiv_id, Point.skyscraperSheafAdjunction_homEquiv_apply_hom,
    Point.skyscraperPresheafHomEquiv_app_π, Category.comp_id]
  rfl

/-- The transpose of `ρ_A` under the skyscraper adjunction is `f_*` of the skyscraper unit. -/
theorem homEquiv_pushFib (A : EtSh Λ X) :
    (comapPt f s).skyscraperSheafAdjunction.homEquiv _ _ (pushFib Λ f s A) =
      (push f Λ).map (s.point.skyscraperSheafAdjunction.unit.app A) := by
  erw [← Equiv.eq_symm_apply]
  refine Point.presheafFiber_hom_ext _ (fun V b => ?_)
  erw [germ_pushFib, Point.skyscraperSheafAdjunction_homEquiv_symm_apply,
    Point.toPresheafFiber_skyscraperPresheafHomEquiv_symm]
  exact (skyUnit_hom_π Λ s A ((etPull f).obj V) b).symm

/-- **Key lemma**: Mathlib's stalk isomorphism `(f^*F)_s ≅ F_{s ≫ f}` is `ψ(η_F) ≫ ρ_{f^*F}`. -/
theorem comapIso_hom_app (F : EtSh Λ Y) :
    (s.point.sheafFiberComapIso (etPull f) (etPull_coverPreserving f) (ModuleCat.{u} Λ)).hom.app F =
      (comapPt f s).sheafFiber.map ((pullAdj f Λ).unit.app F) ≫ pushFib Λ f s ((pull f Λ).obj F) := by
  have h := unit_conjugateEquiv_symm ((pullAdj f Λ).comp s.point.skyscraperSheafAdjunction)
    (comapPt f s).skyscraperSheafAdjunction
    (s.point.skyscraperSheafFunctorCompSheafPushforwardContinuous (etPull f)
      (etPull_coverPreserving f) (ModuleCat.{u} Λ)).hom F
  apply ((comapPt f s).skyscraperSheafAdjunction.homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine h.symm.trans ?_
  erw [Adjunction.comp_unit_app]
  simp only [Point.skyscraperSheafFunctorCompSheafPushforwardContinuous, Iso.refl_hom,
    NatTrans.id_app, Category.assoc]
  erw [Category.comp_id]
  erw [Functor.map_comp, Adjunction.unit_naturality_assoc,
    ← (comapPt f s).skyscraperSheafAdjunction.homEquiv_unit,
    homEquiv_pushFib]

end Gen

namespace IsEt

variable {k : Type} [Field k] {Λ : Type} [CommRing Λ]

end IsEt

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtCompact_GenUnit =====
section

/-!
# S4-EtCompact, D1: the unit `F ⟶ g_* g^* F` is an isomorphism at the generic point

`A` an integrally closed domain, `g = gen A : Y = Spec κ(η) ⟶ U = Spec A`, `x̄0 = geomPtAt x0`,
`Ψ = comapPt g x̄0`.

* `eq_zero_of_germ_std`: a section over `g^*(Spec S)` (`S ⊆ Ω` standard étale with one generic prime) whose germ at
  `fibOf S` vanishes is zero (one Galois orbit on the fibre);
* **`pushFib_injective`**: the base-change map `ρ_M : (g_* M)_Ψ ⟶ M_x̄0` is injective (spread a vanishing
  neighbourhood out over `A` with `StdSub.exists_sub`);
* **`isIso_stalk_unit`**: `(η_F)_Ψ` is an isomorphism (`comapIso_hom_app`: `β_F = (η_F)_Ψ ≫ ρ_{g^*F}`);
* `isZero_stalk_kernel_unit`, `isZero_stalk_cokernel_unit`: kernel and cokernel of `η_F` vanish at `η`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GenUnit

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.EtCompact.LT
  RamanujanPetersson.EtCompact.FibMk

variable {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

/-- A section over `g^*(Spec S)` with one generic prime whose germ at `fibOf S` vanishes is zero. -/
theorem eq_zero_of_germ_std (M : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))))
    (S : Subalgebra A (SeparableClosure (κ0 A))) [Algebra.Etale A S]
    (huniq : ∀ P : Ideal S, P.comap (algebraMap A S) = ⊥ → P = ⊥)
    (z : M.obj.obj (op ((etPull (gen A)).obj (specEt A S))))
    (hz : ((geomPtAt (x0 A)).point.toPresheafFiber _ (fibOf S.val) M.obj).hom z = 0) : z = 0 := by
  have : Subsingleton ((etPull (gen A)).obj (specEt A S)).left :=
    Chart.subsingleton_pull fun P₁ P₂ h₁ h₂ => PrimeSpectrum.ext ((huniq _ h₁).trans (huniq _ h₂).symm)
  refine Cech.eq_zero_of_germs M z fun x a' => ?_
  have hx : x = x0 A := Subsingleton.elim _ _
  subst hx
  obtain ⟨τ, hτ⟩ := FibPt.exists_galAct_eq (x0 A) (fibOf S.val) a'
  rw [← hτ, ← GenStalk.germ_galAct M τ (fibOf S.val) z, hz]
  exact (galRep Λ M (x0 A) τ).map_zero

/-- **The base-change map `(g_* M)_Ψ ⟶ M_x̄0` is injective.** -/
theorem pushFib_injective (M : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))) :
    Function.Injective (pushFib Λ (gen A) (geomPtAt (x0 A)) M).hom := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨W, a, q, rfl⟩ := GrothendieckTopology.Point.toPresheafFiber_jointly_surjective (A := ModuleCat.{0} Λ)
    (comapPt (gen A) (geomPtAt (x0 A))) (P := ((push (gen A) Λ).obj M).obj) y
  let a₀ : (geomPtAt (x0 A)).point.fiber.obj ((etPull (gen A)).obj W) := a
  have h0 : ((geomPtAt (x0 A)).point.toPresheafFiber ((etPull (gen A)).obj W) a₀ M.obj).hom q = 0 := by
    have e := congrArg (fun φ => φ.hom q) (germ_pushFib Λ (gen A) (geomPtAt (x0 A)) M W a)
    exact e.symm.trans hy
  obtain ⟨R, _, _, _, Fm, r, hr⟩ := Supp.exists_affine A W (pullback.fst W.hom (gen A) (Cech.fpt (x0 A) a₀))
  obtain ⟨t, ht⟩ := etPull_exists_preimage (gen A) Fm r (Cech.fpt (x0 A) a₀) hr
  obtain ⟨aR, haR, -⟩ := Cech.exists_lift_fib ((etPull (gen A)).map Fm) (x0 A) a₀ t ht
  let qR : M.obj.obj (op ((etPull (gen A)).obj (specEt A R))) :=
    (M.obj.map ((etPull (gen A)).map Fm).op).hom q
  have hR0 : ((geomPtAt (x0 A)).point.toPresheafFiber _ aR M.obj).hom qR = 0 := by
    rw [Cech.germ_map M ((etPull (gen A)).map Fm) (x0 A) aR q, haR]
    exact h0
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := A) (A := R)
  let φ := phiB A aR
  obtain ⟨S, hSet, hTS, huniq⟩ := StdSub.exists_sub (A := A) (κ0 A) (G.image φ)
  have hφS : ∀ c, φ c ∈ S := by
    have hle : Algebra.adjoin A (G : Set R) ≤ S.comap φ :=
      Algebra.adjoin_le fun g hg => hTS _ (Finset.mem_image_of_mem _ hg)
    intro c
    have hc : c ∈ Algebra.adjoin A (G : Set R) := by
      rw [hG]
      exact Algebra.mem_top
    exact hle hc
  let ψ : R →ₐ[A] S := φ.codRestrict S hφS
  have hfb : fmap A ψ (fibOf S.val) = aR := fib_ext fun c => by
    rw [← phiB_map, phiB_fibOf]
    rfl
  let qS := (M.obj.map ((etPull (gen A)).map (specEtMap ψ)).op).hom qR
  have hS0 : ((geomPtAt (x0 A)).point.toPresheafFiber _ (fibOf S.val) M.obj).hom qS = 0 := by
    have hw := congrArg (fun φ => φ.hom qR) (GrothendieckTopology.Point.toPresheafFiber_w
      (Φ := (geomPtAt (x0 A)).point) ((etPull (gen A)).map (specEtMap ψ)) (fibOf S.val) M.obj)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hw
    refine hw.trans (Eq.trans ?_ hR0)
    rw [← hfb]
    rfl
  have hqS : qS = 0 := eq_zero_of_germ_std M S huniq qS hS0
  have h2 := congrArg (fun φ => φ.hom qR) (GrothendieckTopology.Point.toPresheafFiber_w
    (Φ := comapPt (gen A) (geomPtAt (x0 A))) (specEtMap ψ) (fibOf S.val) ((push (gen A) Λ).obj M).obj)
  have h3 := congrArg (fun φ => φ.hom q) (GrothendieckTopology.Point.toPresheafFiber_w
    (Φ := comapPt (gen A) (geomPtAt (x0 A))) Fm aR ((push (gen A) Λ).obj M).obj)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2 h3
  have hfb' : (comapPt (gen A) (geomPtAt (x0 A))).fiber.map (specEtMap ψ) (fibOf S.val) = aR := hfb
  have haR' : (comapPt (gen A) (geomPtAt (x0 A))).fiber.map Fm aR = a := haR
  rw [hfb'] at h2
  rw [haR'] at h3
  rw [← h3]
  refine h2.symm.trans ?_
  exact (congrArg (fun z : M.obj.obj (op ((etPull (gen A)).obj (specEt A S))) =>
    ((comapPt (gen A) (geomPtAt (x0 A))).toPresheafFiber (specEt A S) (fibOf S.val)
      ((push (gen A) Λ).obj M).obj).hom z) hqS).trans (map_zero _)

/-- **`(η_F)_Ψ` is an isomorphism.** -/
theorem isIso_stalk_unit (F : EtSh Λ (Spec (CommRingCat.of A))) :
    IsIso ((comapPt (gen A) (geomPtAt (x0 A))).sheafFiber.map ((pullAdj (gen A) Λ).unit.app F)) := by
  have hβ := comapIso_hom_app Λ (gen A) (geomPtAt (x0 A)) F
  have hm : Mono (pushFib Λ (gen A) (geomPtAt (x0 A)) ((pull (gen A) Λ).obj F)) :=
    (ModuleCat.mono_iff_injective _).2 (pushFib_injective _)
  have hi : IsIso ((comapPt (gen A) (geomPtAt (x0 A))).sheafFiber.map ((pullAdj (gen A) Λ).unit.app F) ≫
      pushFib Λ (gen A) (geomPtAt (x0 A)) ((pull (gen A) Λ).obj F)) := by
    rw [← hβ]
    infer_instance
  have : Epi (pushFib Λ (gen A) (geomPtAt (x0 A)) ((pull (gen A) Λ).obj F)) :=
    epi_of_epi ((comapPt (gen A) (geomPtAt (x0 A))).sheafFiber.map ((pullAdj (gen A) Λ).unit.app F)) _
  have : IsIso (pushFib Λ (gen A) (geomPtAt (x0 A)) ((pull (gen A) Λ).obj F)) := isIso_of_mono_of_epi _
  exact IsIso.of_isIso_comp_right _ (pushFib Λ (gen A) (geomPtAt (x0 A)) ((pull (gen A) Λ).obj F))

end RamanujanPetersson.EtCompact.GenUnit

end

end


