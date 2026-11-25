-- Prove2me | Definitions.Def_RPLib_FX_EtP1_36
-- name    : RPLib_FX_EtP1_36
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T06:26:45.597098+00:00
-- url     : https://prove2.me/theorems/83e9574d-eacb-5c9c-b2d8-6c1bce5852ed
-- title:
--   Étale cohomology of the projective line, library file 36 (an extra file from a re-cut)
-- statement:
--   File 36 (an extra file from a re-cut) of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_KCe`: S4-EtCompact, part 53: the Kummer condition for elements (F7b of plan v5)
--   * `S4.Def_RP_EtSheaves_SpecEs`: S4-EtSheaves, part 32: every discrete Galois module is the stalk of a sheaf over a field
--   * `S4.Def_RP_EtCompact_Twist`: S4-EtCompact, part 45: every Galois character is an obstruction (P2 of curve core v4)
--   * `S4.Def_RP_EtCompact_SgUnit`: S4-EtCompact, part 42: `Λ_U ≅ g_*Λ_η` at the generic point (K5)
--   * `S4.Def_RP_EtCompact_GlobQ`: S4-EtCompact, part 54: the global Kummer section at a closed point (F7c of plan v5)
--   * `S4.Def_RP_EtCompact_GalCd`: S4-EtCompact, part 36: `H²` of a `C₁` field on discrete `ℓ`-power torsion modules (CC2a)
--   * `S4.Def_RP_EtCompact_PtInj`: S4-EtCompact, part 37: dimension shifting and cocycles in injective sheaves on a point (CC2b)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_14

/-!
# Étale cohomology of the projective line, library file 36 (extra file from a re-cut)

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_KCe`: S4-EtCompact, part 53: the Kummer condition for elements (F7b of plan v5)
* `S4.Def_RP_EtSheaves_SpecEs`: S4-EtSheaves, part 32: every discrete Galois module is the stalk of a sheaf over a field
* `S4.Def_RP_EtCompact_Twist`: S4-EtCompact, part 45: every Galois character is an obstruction (P2 of curve core v4)
* `S4.Def_RP_EtCompact_SgUnit`: S4-EtCompact, part 42: `Λ_U ≅ g_*Λ_η` at the generic point (K5)
* `S4.Def_RP_EtCompact_GlobQ`: S4-EtCompact, part 54: the global Kummer section at a closed point (F7c of plan v5)
* `S4.Def_RP_EtCompact_GalCd`: S4-EtCompact, part 36: `H²` of a `C₁` field on discrete `ℓ`-power torsion modules (CC2a)
* `S4.Def_RP_EtCompact_PtInj`: S4-EtCompact, part 37: dimension shifting and cocycles in injective sheaves on a point (CC2b)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_KCe =====
section

/-!
# S4-EtCompact, part 53: the Kummer condition for elements (F7b of plan v5)

* `KCAt hζ q u e a` (one fibre point `a`, elements `u i ∈ B`), `KCe` (every fibre point); `kc_iff`: the condition
  `LT.KC` for units is `KCe` for their values;
* **`kc_of_one`**: over `g^* Spec B` with a single point, the condition at one fibre point gives it everywhere
  (Galois transitivity, conjugation of obstructions, `τ ζ = ζ`);
* `kcat_map`, `kce_map` (restriction along `B →ₐ[A] B'`), `obs_sub`;
* `good_iff` (`y ∈ Good c` iff the stalk of `c` at `1` vanishes), `good_sub`, `good_comp`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.dupNamespace false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.KCe

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.LT

section ObsSub

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] {MN MI : Type*} [AddCommGroup MN] [Module Λ MN]
  [AddCommGroup MI] [Module Λ MI] {ρ : Representation Λ G MI} {ι : MN →ₗ[Λ] MI}

end ObsSub

variable (A : Type) [CommRing A] [IsDomain A]

section Sheaves

variable {Λ : Type} [CommRing Λ]
  {Ns I Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))} (ι : Ns ⟶ I) (p : I ⟶ Q)

/-- The Kummer condition at one fibre point `a`, for elements `u i ∈ B`. -/
def KCAt {d : ℕ} [NeZero d] {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    {B : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B)))) {k : ℕ} (u : Fin k → B)
    (e : Fin k → stalk Λ Ns (x0 A)) (a : Fib A B) : Prop :=
  ∃ m : stalk Λ I (x0 A),
    (((geomPtAt (x0 A)).stalkF Λ).map p).hom m =
      ((geomPtAt (x0 A)).point.toPresheafFiber _ a Q.obj).hom q ∧
    ∃ β : Fin k → SeparableClosure (κ0 A), (∀ i, β i ^ d = phiB A a (u i)) ∧
      ∀ σ : Gal (x0 A), (galAct (x0 A) σ).app _ a = a →
        Obs.obs (galRep Λ I (x0 A)) (((geomPtAt (x0 A)).stalkF Λ).map ι).hom m σ =
          ∑ i, (dlog hζ (σ (β i) / β i)).val • e i

/-- The Kummer condition for elements: at every fibre point. -/
def KCe {d : ℕ} [NeZero d] {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    {B : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B)))) {k : ℕ} (u : Fin k → B)
    (e : Fin k → stalk Λ Ns (x0 A)) : Prop :=
  ∀ a : Fib A B, KCAt A ι p hζ q u e a

theorem kc_iff {d : ℕ} [NeZero d] {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    {B : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B)))) {k : ℕ} (u : Fin k → Bˣ)
    (e : Fin k → stalk Λ Ns (x0 A)) : KC A ι p hζ B q u e ↔ KCe A ι p hζ q (fun i => (u i : B)) e :=
  Iff.rfl

variable {A ι p}

/-- **One point suffices** over a one-point `g^* Spec B`. -/
theorem kc_of_one (hex : ∀ y, (((geomPtAt (x0 A)).stalkF Λ).map p).hom y = 0 →
      ∃ x, (((geomPtAt (x0 A)).stalkF Λ).map ι).hom x = y)
    (hι : Function.Injective (((geomPtAt (x0 A)).stalkF Λ).map ι).hom)
    (hN : ∀ (σ : Gal (x0 A)) (n : stalk Λ Ns (x0 A)),
      galRep Λ I (x0 A) σ ((((geomPtAt (x0 A)).stalkF Λ).map ι).hom n) = (((geomPtAt (x0 A)).stalkF Λ).map ι).hom n)
    {d : ℕ} [NeZero d] {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    (hζG : ∀ σ : Gal (x0 A), σ ζ = ζ)
    {B : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B]
    [Subsingleton ((etPull (gen A)).obj (specEt A B)).left]
    (q : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B)))) {k : ℕ} (u : Fin k → B)
    (e : Fin k → stalk Λ Ns (x0 A)) (a₀ : Fib A B) (h₀ : KCAt A ι p hζ q u e a₀) : KCe A ι p hζ q u e := by
  intro a
  obtain ⟨τ, rfl⟩ := FibPt.exists_galAct_eq (x0 A) a₀ a
  obtain ⟨m, hm, β, hβ, hobs⟩ := h₀
  refine ⟨galRep Λ I (x0 A) τ m, ?_, fun i => τ (β i), fun i => ?_, fun σ hσ => ?_⟩
  · have h1 := LinearMap.congr_fun (galRep_natural Λ p (x0 A) τ) m
    simp only [LinearMap.comp_apply] at h1
    rw [h1, hm, ← galRep_germ]
  · show τ (β i) ^ d = phiB A _ (u i)
    rw [← map_pow, hβ i]
    exact (FibPt.phi_galAct_apply (x0 A) (gen A) (specEt A B) (𝟙 _) τ a₀ (u i)).symm
  · have hσ' : (galAct (x0 A) (τ⁻¹ * σ * τ)).app _ a₀ = a₀ := by
      rw [galAct_mul, galAct_mul, hσ, ← galAct_mul, inv_mul_cancel, galAct_one]
    have hconj := Obs.obs_conj hι hN τ (adm hex q a₀ m hm (τ⁻¹ * σ * τ) hσ')
    have he : τ * (τ⁻¹ * σ * τ) * τ⁻¹ = σ := by group
    rw [he] at hconj
    rw [hconj, hobs _ hσ']
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    have hx : τ ((τ⁻¹ * σ * τ) (β i) / β i) = (τ⁻¹ * σ * τ) (β i) / β i := by
      by_cases hb : β i = 0
      · rw [hb, div_zero, map_zero]
      · have h2 : (τ⁻¹ * σ * τ) (β i) ^ d = β i ^ d := by
          rw [← map_pow, hβ i]
          exact (FibPt.phi_galAct_apply (x0 A) (gen A) (specEt A B) (𝟙 _) (τ⁻¹ * σ * τ) a₀ (u i)).symm.trans
            (congrArg (fun a => phiB A a (u i)) hσ')
        have h1 : ((τ⁻¹ * σ * τ) (β i) / β i) ^ d = 1 := by
          rw [div_pow, h2, div_self (pow_ne_zero _ hb)]
        obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
        rw [← hj, map_pow, hζG]
    have hy : σ (τ (β i)) / τ (β i) = (τ⁻¹ * σ * τ) (β i) / β i := by
      rw [← hx, map_div₀]
      congr 1
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
      congr 1
      group
    rw [hy]

/-- Restriction of the pointwise condition along `B →ₐ[A] B'`. -/
theorem kcat_map {d : ℕ} [NeZero d] {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    {B B' : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B] [CommRing B'] [Algebra A B']
    [Algebra.Etale A B'] (h : B →ₐ[A] B')
    (q : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B)))) {k : ℕ} (u : Fin k → B)
    (e : Fin k → stalk Λ Ns (x0 A)) (a' : Fib A B') (hkc : KCAt A ι p hζ q u e (fmap A h a')) :
    KCAt A ι p hζ ((Q.obj.map ((etPull (gen A)).map (specEtMap h)).op).hom q) (fun i => h (u i)) e a' := by
  obtain ⟨m, hm, β, hβ, hobs⟩ := hkc
  refine ⟨m, ?_, β, fun i => ?_, fun σ hσ => ?_⟩
  · have hw := congrArg (fun φ => φ.hom q) (GrothendieckTopology.Point.toPresheafFiber_w
      (Φ := (geomPtAt (x0 A)).point) ((etPull (gen A)).map (specEtMap h)) a' Q.obj)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hw
    exact hm.trans hw.symm
  · rw [hβ i]
    exact (phiB_map A h a' (u i)).symm
  · have hσ' : (galAct (x0 A) σ).app _ (fmap A h a') = fmap A h a' := by
      rw [galAct_fmap, hσ]
    exact hobs σ hσ'

theorem kce_map {d : ℕ} [NeZero d] {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    {B B' : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B] [CommRing B'] [Algebra A B']
    [Algebra.Etale A B'] (h : B →ₐ[A] B')
    (q : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B)))) {k : ℕ} (u : Fin k → B)
    (e : Fin k → stalk Λ Ns (x0 A)) (hkc : KCe A ι p hζ q u e) :
    KCe A ι p hζ ((Q.obj.map ((etPull (gen A)).map (specEtMap h)).op).hom q) (fun i => h (u i)) e :=
  fun a' => kcat_map hζ h q u e a' (hkc (fmap A h a'))

end Sheaves

section Good

variable {A} {Λ : Type} [CommRing Λ] {F : EtSh Λ (Spec (CommRingCat.of A))}

/-- `y ∈ Good c` iff the stalk of `c` at `y` kills `1`. -/
theorem good_iff (c : unitSh Λ (Spec (CommRingCat.of A)) ⟶ F) (y : Spec (CommRingCat.of A)) :
    y ∈ Supp.Good A c ↔ (((geomPtAt y).stalkF Λ).map c).hom (oneStalk Λ y) = 0 := by
  constructor
  · rintro ⟨V, w, hw, h0⟩
    exact Supp.stalk_eq_zero_of c hw h0
  · intro h
    have h3 : ((geomPtAt y).point.toPresheafFiber _ (geomPtAt y).top F.obj).hom (Supp.sc c (etId _)) =
        ((geomPtAt y).point.toPresheafFiber _ (geomPtAt y).top F.obj).hom 0 :=
      (Supp.stalk_sc c y (etId _) (geomPtAt y).top).symm.trans (h.trans (LinearMap.map_zero _).symm)
    obtain ⟨W', f, b', -, hfz⟩ := ((geomPtAt y).point.toPresheafFiber_eq_iff' _ (geomPtAt y).top _ _).1 h3
    obtain ⟨w, hw⟩ := (geomPtAt y).center_mem_range b'
    exact ⟨W', w, hw.trans (center_geomPtAt y), (Supp.sc_map c f).symm.trans (hfz.trans (LinearMap.map_zero _))⟩

theorem good_sub (c c' : unitSh Λ (Spec (CommRingCat.of A)) ⟶ F) {y : Spec (CommRingCat.of A)}
    (h : y ∈ Supp.Good A c) (h' : y ∈ Supp.Good A c') : y ∈ Supp.Good A (c - c') := by
  rw [good_iff] at h h' ⊢
  rw [Functor.map_sub, ModuleCat.hom_sub, LinearMap.sub_apply, h, h', sub_self]

end Good

end RamanujanPetersson.EtCompact.KCe

end

end

-- ===== S4.Def_RP_EtSheaves_SpecEs =====
section

/-!
# S4-EtSheaves, part 32: every discrete Galois module is the stalk of a sheaf over a field

For `X` with `X.fromSpecResidueField x0` an isomorphism and a representation `ρ` of `Gal(Ω/κ(x0))` on `M` with open
stabilizers (a discrete Galois module), evaluation on the stalk of the sheaf `skyG(M)` of equivariant maps is
surjective (`evG_surjective`: `m` fixed by the fixing group of a finite subextension `E` gives the equivariant map
`σ·[E ⊆ Ω] ↦ σ m` on the fibre of `Spec E`), hence bijective, and it intertwines the Galois action on the stalk with
`ρ` (`evG_galRep`). Headline: `specField_essSurj`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] (Λ : Type u) [CommRing Λ]
  {M : Type u} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ (Gal x0) M)

/-- **Over a field, evaluation on the stalk of `skyG(M)` is surjective** when `M` is a discrete Galois module. -/
theorem evG_surjective (hρ : ∀ m : M, ∃ H : Subgroup (Gal x0), IsOpen (H : Set (Gal x0)) ∧ ∀ σ ∈ H, ρ σ m = m) :
    Function.Surjective (evG (geomPtAt x0).point (galAct x0) Λ (fun σ => ρ σ)).hom := by
  intro m
  obtain ⟨H, hHo, hH⟩ := hρ m
  obtain ⟨E, hE, hEH⟩ := (krullTopology_mem_nhds_one_iff (X.residueField x0)
    (SeparableClosure (X.residueField x0)) (H : Set (Gal x0))).1 (hHo.mem_nhds H.one_mem)
  have stab : ∀ g h : Gal x0, (galAct x0 g).app _ (specPt x0 E) = (galAct x0 h).app _ (specPt x0 E) →
      ρ g m = ρ h m := by
    intro g h e
    have h1 : (galAct x0 (h⁻¹ * g)).app _ (specPt x0 E) = specPt x0 E := by
      rw [galAct_mul, e, ← galAct_mul, inv_mul_cancel, galAct_one]
    have h2 : h⁻¹ * g ∈ H := hEH (mem_fixingSubgroup_of_galAct x0 E h1)
    calc ρ g m = ρ (h * (h⁻¹ * g)) m := by rw [mul_inv_cancel_left]
      _ = ρ h (ρ (h⁻¹ * g) m) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ h m := by rw [hH _ h2]
  choose τ hτ using specObj_transitive x0 E
  let β : (geomPtAt x0).point.fiber.obj (specObj x0 E) → M := fun b => ρ (τ b) m
  have hβ : β ∈ eqSub (geomPtAt x0).point (galAct x0) Λ (fun σ => ρ σ) (specObj x0 E) := by
    refine (mem_eqSub _ _ _ _ _).2 fun σ b => ?_
    change ρ (τ ((galAct x0 σ).app _ b)) m = ρ σ (ρ (τ b) m)
    rw [stab (τ ((galAct x0 σ).app _ b)) (σ * τ b) (by rw [hτ, galAct_mul, hτ]), map_mul,
      Module.End.mul_apply]
  refine ⟨((geomPtAt x0).point.toPresheafFiber (specObj x0 E) (specPt x0 E)
    (skyPre (geomPtAt x0).point (galAct x0) Λ (fun σ => ρ σ))).hom ⟨β, hβ⟩, ?_⟩
  refine (evG_germ _ _ Λ _ _ _ _).trans ?_
  change ρ (τ (specPt x0 E)) m = m
  rw [stab (τ (specPt x0 E)) 1 (by rw [hτ, galAct_one]), map_one, Module.End.one_apply]

omit [IsIso (X.fromSpecResidueField x0)] in
/-- Evaluation intertwines the Galois action on the stalk of `skyG(M)` with `ρ`. -/
theorem evG_galRep (σ : Gal x0)
    (v : stalk Λ (skyG (geomPtAt x0).point (galAct x0) Λ (fun σ => ρ σ)) x0) :
    (evG (geomPtAt x0).point (galAct x0) Λ (fun σ => ρ σ)).hom
      (galRep Λ (skyG (geomPtAt x0).point (galAct x0) Λ (fun σ => ρ σ)) x0 σ v) =
        ρ σ ((evG (geomPtAt x0).point (galAct x0) Λ (fun σ => ρ σ)).hom v) := by
  obtain ⟨U, a, γ, rfl⟩ := (geomPtAt x0).point.toPresheafFiber_jointly_surjective
    (P := (skyG (geomPtAt x0).point (galAct x0) Λ (fun σ => ρ σ)).obj) v
  refine (congrArg (evG (geomPtAt x0).point (galAct x0) Λ (fun σ => ρ σ)).hom
    (galRep_germ Λ (skyG (geomPtAt x0).point (galAct x0) Λ (fun σ => ρ σ)) x0 σ U a γ).symm).trans ?_
  refine (evG_germ _ _ Λ _ U _ γ).trans ?_
  refine ((mem_eqSub _ _ Λ _ _).1 γ.2 σ a).trans ?_
  exact congrArg (ρ σ) (evG_germ _ _ Λ _ U a γ).symm

/-- **Sheaves over a field, essential surjectivity**: every discrete `Gal(Ω/κ(x0))`-module is, Galois-equivariantly,
the stalk `F_x̄` of an etale sheaf `F` on `X ≅ Spec κ(x0)`. -/
theorem specField_essSurj
    (hρ : ∀ m : M, ∃ H : Subgroup (Gal x0), IsOpen (H : Set (Gal x0)) ∧ ∀ σ ∈ H, ρ σ m = m) :
    ∃ (F : EtSh Λ X) (e : stalk Λ F x0 ≃ₗ[Λ] M), ∀ (σ : Gal x0) (v : stalk Λ F x0),
      e (galRep Λ F x0 σ v) = ρ σ (e v) := by
  refine ⟨skyG (geomPtAt x0).point (galAct x0) Λ (fun σ => ρ σ),
    LinearEquiv.ofBijective (evG (geomPtAt x0).point (galAct x0) Λ (fun σ => ρ σ)).hom
      ⟨evG_injective x0 Λ (fun σ => ρ σ), evG_surjective x0 Λ ρ hρ⟩, fun σ v => ?_⟩
  exact evG_galRep x0 Λ ρ σ v

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtCompact_Twist =====
section

/-!
# S4-EtCompact, part 45: every Galois character is an obstruction (P2 of curve core v4)

`X` with `X.fromSpecResidueField x0` an isomorphism ("`X = Spec κ(x0)`"), `ι : N ⟶ I` a monomorphism into an
injective sheaf, `Gal(Ω/κ(x0))` acting trivially on `N_x̄`.

* `twAct x0 χ`: the twisted action `σ (n, c) = (n + c • χ σ, c)` on `N_x̄ × Λ`;
* **`exists_twist_lift`**: for every additive `χ : Gal x0 → N_x̄` vanishing on an open subgroup there is `m ∈ I_x̄`
  with `σ m - m = ι(χ σ)` for all `σ` (`H¹(G, I_x̄) = 0`): the twisted module is the stalk of a sheaf `E`
  (`specField_essSurj`), `N ⟶ E` is the equivariant inclusion (`specField_homEquiv`), extend `ι` along it
  (`I` injective) and take the image of `(0, 1)`.
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.Twist

open RamanujanPetersson.EtSheaves

variable {X : Scheme.{u}} (x0 : X) {Λ : Type u} [CommRing Λ]

section Mod

variable {M : Type u} [AddCommGroup M] [Module Λ M]

/-- The twisted representation (for additive `χ`). -/
def twRep (χ : Gal x0 → M) (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ) : Representation Λ (Gal x0) (M × Λ) where
  toFun := twAct x0 χ
  map_one' := LinearMap.ext fun v => by
    have h1 : χ 1 = 0 := by
      have h := hχ 1 1
      rw [mul_one] at h
      exact left_eq_add.mp h
    rw [Module.End.one_apply, twAct_apply, h1, smul_zero, add_zero]
  map_mul' σ τ := LinearMap.ext fun v => by
    rw [Module.End.mul_apply, twAct_apply, twAct_apply, twAct_apply, hχ, smul_add]
    ext
    · show v.1 + (v.2 • χ σ + v.2 • χ τ) = v.1 + v.2 • χ τ + v.2 • χ σ
      abel
    · rfl

theorem twRep_apply (χ : Gal x0 → M) (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ) (σ : Gal x0) (v : M × Λ) :
    twRep x0 χ hχ σ v = (v.1 + v.2 • χ σ, v.2) := rfl

end Mod

variable [IsIso (X.fromSpecResidueField x0)]

/-- **`H¹(Gal, I_x̄) = 0` in the form needed for P2**: every additive `χ : Gal x0 → N_x̄` with open kernel is
`σ ↦ σ m - m` for some `m ∈ I_x̄`. -/
theorem exists_twist_lift {N I : EtSh Λ X} (hN : ∀ (σ : Gal x0) (v : stalk Λ N x0), galRep Λ N x0 σ v = v)
    [Injective I] (ι : N ⟶ I) [Mono ι] (χ : Gal x0 → stalk Λ N x0)
    (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ)
    (hχc : ∃ H : Subgroup (Gal x0), IsOpen (H : Set (Gal x0)) ∧ ∀ σ ∈ H, χ σ = 0) :
    ∃ m : stalk Λ I x0, ∀ σ : Gal x0,
      galRep Λ I x0 σ m - m = (((geomPtAt x0).stalkF Λ).map ι).hom (χ σ) := by
  obtain ⟨H, hHo, hH⟩ := hχc
  obtain ⟨E, e, he⟩ := specField_essSurj x0 Λ (twRep x0 χ hχ) (fun v => ⟨H, hHo, fun σ hσ => by
    rw [twRep_apply, hH σ hσ, smul_zero, add_zero]⟩)
  have hE : ∀ σ w, galRep Λ E x0 σ (e.symm w) = e.symm (twRep x0 χ hχ σ w) := fun σ w => by
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let jl : stalk Λ N x0 →ₗ[Λ] stalk Λ E x0 := e.symm.toLinearMap ∘ₗ LinearMap.inl Λ (stalk Λ N x0) Λ
  have hjl : ∀ v, jl v = e.symm (v, 0) := fun v => rfl
  have hj : ∀ σ : Gal x0, jl ∘ₗ galRep Λ N x0 σ = galRep Λ E x0 σ ∘ₗ jl := fun σ => by
    refine LinearMap.ext fun v => ?_
    show e.symm (galRep Λ N x0 σ v, 0) = galRep Λ E x0 σ (e.symm (v, 0))
    rw [hN σ v, hE, twRep_apply, zero_smul, add_zero]
  let j : N ⟶ E := (specField_homEquiv x0 Λ N E).symm ⟨jl, hj⟩
  have hjs : (((geomPtAt x0).stalkF Λ).map j).hom = jl := by
    have := congrArg Subtype.val ((specField_homEquiv x0 Λ N E).apply_symm_apply ⟨jl, hj⟩)
    rwa [specField_homEquiv_apply] at this
  have : Mono j := by
    rw [mono_iff_stalk]
    intro x
    have := subsingleton_of_isIso x0
    rw [Subsingleton.elim x x0]
    refine (ModuleCat.mono_iff_injective _).2 ?_
    show Function.Injective (((geomPtAt x0).stalkF Λ).map j).hom
    rw [hjs]
    intro v w hvw
    rw [hjl, hjl] at hvw
    exact congrArg Prod.fst (e.symm.injective hvw)
  let φ : E ⟶ I := Injective.factorThru ι j
  have hφ : j ≫ φ = ι := Injective.comp_factorThru ι j
  refine ⟨(((geomPtAt x0).stalkF Λ).map φ).hom (e.symm (0, 1)), fun σ => ?_⟩
  have hnat := LinearMap.congr_fun (galRep_natural Λ φ x0 σ) (e.symm (0, 1))
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hnat
  have h2 : e.symm (twRep x0 χ hχ σ (0, 1)) - e.symm (0, 1) = jl (χ σ) := by
    rw [← map_sub, twRep_apply, hjl]
    congr 1
    ext <;> simp
  have h3 : (((geomPtAt x0).stalkF Λ).map φ).hom ((((geomPtAt x0).stalkF Λ).map j).hom (χ σ)) =
      (((geomPtAt x0).stalkF Λ).map ι).hom (χ σ) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp, hφ]
  rw [← hnat, hE, ← map_sub, h2, ← hjs, h3]

end RamanujanPetersson.EtCompact.Twist

end

end

-- ===== S4.Def_RP_EtCompact_SgUnit =====
section

/-!
# S4-EtCompact, part 42: `Λ_U ≅ g_*Λ_η` at the generic point (K5)

For `g : Y ⟶ X` and a `Λ`-module `M`, `uC g M : M_X ⟶ g_* M_Y` is the sheafified map sending a constant section `m`
over `V` to the constant section `m` over `V ×_X Y` (`uC_constUnit`).
* `mono_uC`: it is a monomorphism when every nonempty etale `V` has nonempty `V ×_X Y` (constant sections over a
  nonempty object are injective, `constUnit_injective`, and every section is locally constant);
* `epi_uC`: it is an epimorphism when every point of every etale `V` has an etale neighbourhood `V'` with
  `V' ×_X Y` having at most one point (every section of `M_Y` over such an object is constant, `eq_constUnit`);
* **`isIso_uC_genPt`**, **`unitIsoPush`**: for `A` a noetherian integrally closed domain, `U = Spec A`, `η` its
  generic point and `g = Spec κ(η) ⟶ U`: `Λ_U ≅ g_* Λ_η` (charts with one generic point, `ChartSch.hChart`, and
  `g` a preimmersion, so `V ×_U Spec κ(η) ↪ V`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

namespace SgUnit

universe u

section General

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (g : Y ⟶ X) (M : ModuleCat.{u} Λ)

/-- Constant sections are stable under restriction. -/
theorem cU_map {V W : Y.Etale} (f : V ⟶ W) (n : M) :
    ((constSh Λ Y M).obj.map f.op).hom ((constUnit M W).hom n) = (constUnit M V).hom n :=
  (congrArg (fun φ => φ.hom n)
    ((toSheafify Y.smallEtaleTopology (constPre M)).naturality f.op)).symm

/-- Constant sections over a nonempty object are injective. -/
theorem constUnit_injective {W : Y.Etale} (w : W.left) : Function.Injective (constUnit M W).hom := by
  obtain ⟨b⟩ := (geomPtAt (W.hom w)).exists_fiber W w (center_geomPtAt _).symm
  refine (injective_iff_map_eq_zero (constUnit M W).hom).2 fun n hn => ?_
  have h := congrArg (fun φ => φ.hom n) (constUnit_germ (geomPtAt (W.hom w)) M W b)
  change ((geomPtAt (W.hom w)).point.toPresheafFiber W b (constSh Λ Y M).obj).hom
    ((constUnit M W).hom n) = _ at h
  rw [hn, map_zero] at h
  exact (iso_inv_eq_zero (constStalkIso Λ (geomPtAt (W.hom w)) M) n).1 h.symm

/-- **Sections of a constant sheaf over an object with at most one point are constant.** -/
theorem eq_constUnit {W : Y.Etale} (hW : ∀ a b : W.left, a = b) (c : (constSh Λ Y M).obj.obj (op W)) :
    ∃ n : M, c = (constUnit M W).hom n := by
  have key : ∃ n : M, ∀ w : W.left, ∃ (V : Y.Etale) (f : V ⟶ W) (v : V.left),
      ((constSh Λ Y M).obj.map f.op).hom c = (constUnit M V).hom n ∧ f.left v = w := by
    by_cases h : Nonempty W.left
    · obtain ⟨w0⟩ := h
      obtain ⟨V, f, v, ⟨n, hn⟩, hv⟩ := (mem_smallEtale_iff W _).1
        (Presheaf.imageSieve_mem Y.smallEtaleTopology (toSheafify Y.smallEtaleTopology (constPre M)) c) w0
      exact ⟨n, fun w => ⟨V, f, v, hn.symm, hv.trans (hW w0 w)⟩⟩
    · exact ⟨0, fun w => (h ⟨w⟩).elim⟩
  obtain ⟨n, hn⟩ := key
  let R : Sieve W :=
    { arrows := fun _ f => ((constSh Λ Y M).obj.map f.op).hom c =
        ((constSh Λ Y M).obj.map f.op).hom ((constUnit M W).hom n)
      downward_closed := fun {_ _} {f} hf g => by
        show ((constSh Λ Y M).obj.map (g ≫ f).op).hom c =
          ((constSh Λ Y M).obj.map (g ≫ f).op).hom ((constUnit M W).hom n)
        rw [← map_map_apply, ← map_map_apply, hf] }
  have hR : R ∈ Y.smallEtaleTopology W := (mem_smallEtale_iff W R).2 fun w => by
    obtain ⟨V, f, v, h1, h2⟩ := hn w
    exact ⟨V, f, v, h1.trans (cU_map M f n).symm, h2⟩
  exact ⟨n, sep_eq (constSh Λ Y M) R hR c _ fun _ f hf => hf⟩

/-- `uC : M_X ⟶ g_* M_Y`, constant sections to constant sections. -/
def uC : constSh Λ X M ⟶ (push g Λ).obj (constSh Λ Y M) :=
  ObjectProperty.homMk (sheafifyLift X.smallEtaleTopology (cPre g M) ((push g Λ).obj (constSh Λ Y M)).property)

theorem uC_constUnit (V : X.Etale) (n : M) :
    ((uC g M).hom.app (op V)).hom ((constUnit M V).hom n) = (constUnit M ((etPull g).obj V)).hom n :=
  congrArg (fun φ => (φ.app (op V)).hom n)
    (toSheafify_sheafifyLift X.smallEtaleTopology (cPre g M) ((push g Λ).obj (constSh Λ Y M)).property)

/-- **`uC` is a monomorphism** when nonempty etale objects have nonempty base change along `g`. -/
theorem mono_uC (hne : ∀ V : X.Etale, V.left → Nonempty ((etPull g).obj V).left) : Mono (uC g M) := by
  have hinj : ∀ V : X.Etale, Function.Injective ((uC g M).hom.app (op V)).hom := fun V => by
    refine (injective_iff_map_eq_zero _).2 fun d hd => ?_
    let R : Sieve V :=
      { arrows := fun _ f => ((constSh Λ X M).obj.map f.op).hom d = 0
        downward_closed := fun {_ _} {f} (hf : ((constSh Λ X M).obj.map f.op).hom d = 0) g => by
          show ((constSh Λ X M).obj.map (g ≫ f).op).hom d = 0
          rw [← map_map_apply, hf, map_zero] }
    have hR : R ∈ X.smallEtaleTopology V := (mem_smallEtale_iff V R).2 fun w => by
      obtain ⟨V1, f, v, ⟨n, hn⟩, hv⟩ := (mem_smallEtale_iff V _).1
        (Presheaf.imageSieve_mem X.smallEtaleTopology (toSheafify X.smallEtaleTopology (constPre M)) d) w
      have hn' : ((constSh Λ X M).obj.map f.op).hom d = (constUnit M V1).hom n := hn.symm
      obtain ⟨p⟩ := hne V1 v
      have h0 : (constUnit M ((etPull g).obj V1)).hom n = 0 := by
        rw [← uC_constUnit, ← hn', app_map, hd, map_zero]
        rfl
      have hn0 : n = 0 :=
        constUnit_injective M p (h0.trans (map_zero (constUnit M ((etPull g).obj V1)).hom).symm)
      refine ⟨V1, f, v, ?_, hv⟩
      show ((constSh Λ X M).obj.map f.op).hom d = 0
      rw [hn', hn0, map_zero]
    exact sep_eq (constSh Λ X M) R hR d 0 fun _ f (hf : ((constSh Λ X M).obj.map f.op).hom d = 0) =>
      hf.trans (map_zero _).symm
  have : ∀ V : X.Etaleᵒᵖ, Mono ((uC g M).hom.app V) := fun V =>
    (ModuleCat.mono_iff_injective _).2 (hinj V.unop)
  have : Mono (uC g M).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono (f := uC g M)

/-- **`uC` is an epimorphism** when every point has an etale neighbourhood with at most one point over `Y`. -/
theorem epi_uC (hloc : ∀ (V : X.Etale) (v : V.left), ∃ (V' : X.Etale) (f : V' ⟶ V) (v' : V'.left),
    f.left v' = v ∧ ∀ a b : ((etPull g).obj V').left, a = b) : Epi (uC g M) := by
  have : Sheaf.IsLocallySurjective (uC g M) := ⟨fun {V} t => (mem_smallEtale_iff V _).2 fun v => by
    obtain ⟨V', f, v', hv', hsub⟩ := hloc V v
    obtain ⟨n, hn⟩ := eq_constUnit M hsub ((((push g Λ).obj (constSh Λ Y M)).obj.map f.op).hom t)
    exact ⟨V', f, v', ⟨(constUnit M V').hom n, (uC_constUnit g M V' n).trans hn.symm⟩, hv'⟩⟩
  exact (Sheaf.isLocallySurjective_iff_epi' (φ := uC g M)).1 this

theorem isIso_uC (hne : ∀ V : X.Etale, V.left → Nonempty ((etPull g).obj V).left)
    (hloc : ∀ (V : X.Etale) (v : V.left), ∃ (V' : X.Etale) (f : V' ⟶ V) (v' : V'.left),
      f.left v' = v ∧ ∀ a b : ((etPull g).obj V').left, a = b) : IsIso (uC g M) := by
  have := mono_uC g M hne
  have := epi_uC g M hloc
  exact isIso_of_mono_of_epi _

end General

section Spec

variable (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]

/-- `g : Spec κ(η) ⟶ Spec A` at the generic point `η`. -/
abbrev gη : Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)) ⟶ Spec (CommRingCat.of A) :=
  (Spec (CommRingCat.of A)).fromSpecResidueField (GenBr.genPt A)

theorem genPt_mem' (O : Set (Spec (CommRingCat.of A))) (hO : IsOpen O) (hne : O.Nonempty) :
    GenBr.genPt A ∈ O := by
  rw [GenBr.genPt_eq]
  exact ((genericPoint_spec (Spec (CommRingCat.of A))).mem_open_set_iff hO).2 (by simpa using hne)

theorem hne_gη (V : (Spec (CommRingCat.of A)).Etale) (v : V.left) : Nonempty ((etPull (gη A)).obj V).left := by
  have : Etale V.hom := V.prop
  obtain ⟨v', hv'⟩ := genPt_mem' A _ V.hom.isOpenMap.isOpen_range ⟨_, v, rfl⟩
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := V.hom) (g := gη A) v'
    (IsLocalRing.closedPoint _) (hv'.trans (Scheme.fromSpecResidueField_apply _ _).symm)
  exact ⟨p⟩

/-- Points of `T ×_X Spec κ(x)` are determined by their image in `T` (`Spec κ(x) ⟶ X` is a preimmersion). -/
theorem fst_injective {X T : Scheme.{0}} (x : X) (f : T ⟶ X) :
    Function.Injective (pullback.fst f (X.fromSpecResidueField x)) :=
  (pullback.fst f (X.fromSpecResidueField x)).isEmbedding.injective

theorem fst_over {X T : Scheme.{0}} (x : X) (f : T ⟶ X) (a : ↥(pullback f (X.fromSpecResidueField x))) :
    f (pullback.fst f (X.fromSpecResidueField x) a) = x := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem hloc_gη (V : (Spec (CommRingCat.of A)).Etale) (v : V.left) :
    ∃ (V' : (Spec (CommRingCat.of A)).Etale) (f : V' ⟶ V) (v' : V'.left),
      f.left v' = v ∧ ∀ a b : ((etPull (gη A)).obj V').left, a = b := by
  obtain ⟨T, h, hh, c, w, hw, -, huniq⟩ := ChartSch.hChart A (unitSh ℤ _) isLisse_unitSh V v
  have h1 : ∀ z : T, ((etComp h).obj (etId T)).hom z = h z := fun z => by
    show (𝟙 T ≫ h) z = h z
    rw [Category.id_comp]
  refine ⟨(etComp h).obj (etId T), c, w, hw, fun a b => fst_injective (GenBr.genPt A)
    ((etComp h).obj (etId T)).hom (huniq _ _ ((h1 _).symm.trans (fst_over _ _ a))
      ((h1 _).symm.trans (fst_over _ _ b)))⟩

variable {Λ : Type} [CommRing Λ]

/-- **`Λ_U ⟶ g_*Λ_η` is an isomorphism** on `U = Spec A`. -/
theorem isIso_uC_genPt : IsIso (uC (Λ := Λ) (gη A) (ModuleCat.of Λ Λ)) :=
  isIso_uC _ _ (hne_gη A) (hloc_gη A)

/-- **`Λ_U ≅ g_*Λ_η`** on `U = Spec A`, `g : Spec κ(η) ⟶ U`. -/
def unitIsoPush : unitSh Λ (Spec (CommRingCat.of A)) ≅ (push (gη A) Λ).obj (unitSh Λ _) :=
  have := isIso_uC_genPt A (Λ := Λ)
  asIso (uC (gη A) (ModuleCat.of Λ Λ))

theorem unitIsoPush_hom : (unitIsoPush A (Λ := Λ)).hom = uC (gη A) (ModuleCat.of Λ Λ) := rfl

end Spec

end SgUnit

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_GlobQ =====
section

/-!
# S4-EtCompact, part 54: the global Kummer section at a closed point (F7c of plan v5)

`A` a domain, `g = gen A`, `Ω = κ(η)^sep`, `ι : Ns ⟶ I`, `p : I ⟶ Q` on `Spec κ(η)` with `ι ≫ p = 0`, exact on
stalks, `I` injective, `Gal` trivial on `Ns_x̄`, `d • Ns_x̄ = 0`, `d` a unit of `A`, `ζ ∈ Ω` a primitive `d`-th root
fixed by `Gal`. For `π ≠ 0` in `A` and `r ∈ Ns_x̄`:

* `ϖ ^ d = π`, the character `σ ↦ (dlog(σϖ/ϖ)).val • r` (additive, open kernel), its twist lift `m ∈ I_x̄`;
* `alpha y₀ : Λ_Y ⟶ Q` (stalk `1 ↦ y₀` for a fixed `y₀`), `aMap y₀ := uC g ≫ g_* alpha : Λ_{Spec A} ⟶ g_* Q`;
* **`exists_globQ`**: a global `a : Λ ⟶ g_* Q` whose germs are all `p m`, and `a ≫ c` vanishes near every point of
  `D(π)` for every `c` killing `g_* p` (local triviality over `A[1/π]` with the unit `π`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GlobQ

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.LT

section Char

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {d : ℕ} [NeZero d] {ζ : Ω} (hζ : IsPrimitiveRoot ζ d)
  (hζG : ∀ σ : Ω ≃ₐ[K] Ω, σ ζ = ζ) {ϖ : Ω} (hϖ0 : ϖ ≠ 0) (hϖ : ∀ σ : Ω ≃ₐ[K] Ω, σ (ϖ ^ d) = ϖ ^ d)
include hζG hϖ0 hϖ

end Char

variable (A : Type) [CommRing A] [IsDomain A]

section Alpha

variable {Λ : Type} [CommRing Λ] {Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))}

/-- The map `Λ_Y ⟶ Q` with stalk `v ↦ v • y₀`, for a Galois-fixed `y₀ ∈ Q_x̄`. -/
def alpha (y₀ : stalk Λ Q (x0 A)) (hy : ∀ σ, galRep Λ Q (x0 A) σ y₀ = y₀) : unitSh Λ _ ⟶ Q :=
  (specField_homEquiv (x0 A) Λ (unitSh Λ _) Q).symm
    ⟨(LinearMap.toSpanSingleton Λ _ y₀) ∘ₗ (constStalkIso Λ (geomPtAt (x0 A)) (ModuleCat.of Λ Λ)).hom.hom,
      fun σ => by
        rw [galRep_unitSh, LinearMap.comp_id]
        refine LinearMap.ext fun v => ?_
        simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, LinearMap.map_smul, hy]⟩

theorem alpha_stalk (y₀ : stalk Λ Q (x0 A)) (hy : ∀ σ, galRep Λ Q (x0 A) σ y₀ = y₀) :
    (((geomPtAt (x0 A)).stalkF Λ).map (alpha A y₀ hy)).hom (oneStalk Λ (x0 A)) = y₀ := by
  have hs := congrArg Subtype.val ((specField_homEquiv (x0 A) Λ (unitSh Λ _) Q).apply_symm_apply
    ⟨(LinearMap.toSpanSingleton Λ _ y₀) ∘ₗ (constStalkIso Λ (geomPtAt (x0 A)) (ModuleCat.of Λ Λ)).hom.hom,
      fun σ => by
        rw [galRep_unitSh, LinearMap.comp_id]
        refine LinearMap.ext fun v => ?_
        simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, LinearMap.map_smul, hy]⟩)
  rw [specField_homEquiv_apply] at hs
  have h1 : (constStalkIso Λ (geomPtAt (x0 A)) (ModuleCat.of Λ Λ)).hom.hom (oneStalk Λ (x0 A)) = (1 : Λ) := by
    show ((constStalkIso Λ (geomPtAt (x0 A)) (ModuleCat.of Λ Λ)).inv ≫
      (constStalkIso Λ (geomPtAt (x0 A)) (ModuleCat.of Λ Λ)).hom).hom (1 : Λ) = (1 : Λ)
    rw [Iso.inv_hom_id]
    rfl
  rw [alpha, hs, LinearMap.comp_apply, h1, LinearMap.toSpanSingleton_apply, one_smul]

/-- The global section map `Λ_{Spec A} ⟶ g_* Λ_Y ⟶ g_* Q`. -/
def aMap (y₀ : stalk Λ Q (x0 A)) (hy : ∀ σ, galRep Λ Q (x0 A) σ y₀ = y₀) :
    unitSh Λ (Spec (CommRingCat.of A)) ⟶ (push (gen A) Λ).obj Q :=
  SgUnit.uC (gen A) (ModuleCat.of Λ Λ) ≫ (push (gen A) Λ).map (alpha A y₀ hy)

theorem sc_aMap (y₀ : stalk Λ Q (x0 A)) (hy : ∀ σ, galRep Λ Q (x0 A) σ y₀ = y₀) (V : (Spec (CommRingCat.of A)).Etale) :
    Supp.sc (aMap A y₀ hy) V = Supp.sc (alpha A y₀ hy) ((etPull (gen A)).obj V) := by
  rw [aMap, Supp.sc_comp, Supp.sc, Supp.sc, SgUnit.uC_constUnit]
  rfl

theorem germ_aMap (y₀ : stalk Λ Q (x0 A)) (hy : ∀ σ, galRep Λ Q (x0 A) σ y₀ = y₀) (V : (Spec (CommRingCat.of A)).Etale)
    (b : (geomPtAt (x0 A)).point.fiber.obj ((etPull (gen A)).obj V)) :
    ((geomPtAt (x0 A)).point.toPresheafFiber _ b Q.obj).hom (Supp.sc (aMap A y₀ hy) V) = y₀ := by
  rw [sc_aMap]
  exact (Supp.stalk_sc (alpha A y₀ hy) (x0 A) _ b).symm.trans (alpha_stalk A y₀ hy)

end Alpha

section Main

variable {A} {Λ : Type} [CommRing Λ]
  {Ns I Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))} (ι : Ns ⟶ I) (p : I ⟶ Q)

/-- **The global Kummer section at `π`**. -/
theorem exists_globQ (hex : ∀ y, (((geomPtAt (x0 A)).stalkF Λ).map p).hom y = 0 →
      ∃ x, (((geomPtAt (x0 A)).stalkF Λ).map ι).hom x = y)
    (hN : ∀ (σ : Gal (x0 A)) (v : stalk Λ Ns (x0 A)), galRep Λ Ns (x0 A) σ v = v)
    [Injective I] [Mono ι] (hιp : ι ≫ p = 0)
    {d : ℕ} [NeZero d] (hdA : IsUnit (d : A)) {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    (hζG : ∀ σ : Gal (x0 A), σ ζ = ζ) (hd : ∀ v : stalk Λ Ns (x0 A), d • v = 0)
    (π : A) (hπ : π ≠ 0) (r : stalk Λ Ns (x0 A)) :
    ∃ (ϖ : SeparableClosure (κ0 A)) (m : stalk Λ I (x0 A))
      (a : unitSh Λ (Spec (CommRingCat.of A)) ⟶ (push (gen A) Λ).obj Q),
      ϖ ^ d = algebraMap A (SeparableClosure (κ0 A)) π ∧
      (∀ σ : Gal (x0 A), galRep Λ I (x0 A) σ m - m =
        (((geomPtAt (x0 A)).stalkF Λ).map ι).hom ((dlog hζ (σ ϖ / ϖ)).val • r)) ∧
      (∀ (V : (Spec (CommRingCat.of A)).Etale) (b : (geomPtAt (x0 A)).point.fiber.obj ((etPull (gen A)).obj V)),
        ((geomPtAt (x0 A)).point.toPresheafFiber _ b Q.obj).hom (Supp.sc a V) =
          (((geomPtAt (x0 A)).stalkF Λ).map p).hom m) ∧
      ∀ {C : EtSh Λ (Spec (CommRingCat.of A))} (c : (push (gen A) Λ).obj Q ⟶ C), (push (gen A) Λ).map p ≫ c = 0 →
        ∀ y : Spec (CommRingCat.of A), π ∉ y.asIdeal → y ∈ Supp.Good A (a ≫ c) := by
  have hι : Function.Injective (((geomPtAt (x0 A)).stalkF Λ).map ι).hom :=
    (ModuleCat.mono_iff_injective _).1 ((mono_iff_stalk Λ ι).1 inferInstance (x0 A))
  -- the root `ϖ`
  have : NeZero ((d : ℕ) : SeparableClosure (κ0 A)) := ⟨by
    rw [← map_natCast (algebraMap A (SeparableClosure (κ0 A)))]
    exact (hdA.map _).ne_zero⟩
  obtain ⟨ϖ, hϖ⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap A (SeparableClosure (κ0 A)) π) d
  have hπ0 : algebraMap A (SeparableClosure (κ0 A)) π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A (κ0 A) (SeparableClosure (κ0 A))]
    exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective A (κ0 A))).2 hπ)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne d)] at hϖ
    exact hπ0 hϖ.symm
  have hϖG : ∀ σ : Gal (x0 A), σ (ϖ ^ d) = ϖ ^ d := by
    intro σ
    rw [hϖ, IsScalarTower.algebraMap_apply A (κ0 A) (SeparableClosure (κ0 A)), AlgEquiv.commutes]
  -- the character and its twist lift
  let χ : Gal (x0 A) → stalk Λ Ns (x0 A) := fun σ => (dlog hζ (σ ϖ / ϖ)).val • r
  have hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ := by
    intro σ τ
    show (dlog hζ ((σ * τ) ϖ / ϖ)).val • r = (dlog hζ (σ ϖ / ϖ)).val • r + (dlog hζ (τ ϖ / ϖ)).val • r
    rw [dlog_mul hζ hζG hϖ0 hϖG]
    exact val_add_nsmul (hd r) _ _
  have hχc : ∃ H : Subgroup (Gal (x0 A)), IsOpen (H : Set (Gal (x0 A))) ∧ ∀ σ ∈ H, χ σ = 0 := by
    refine ⟨MulAction.stabilizer (Gal (x0 A)) ϖ, stabilizer_isOpen_of_isIntegral ϖ, fun σ hσ => ?_⟩
    have hσ' : σ ϖ = ϖ := hσ
    show (dlog hζ (σ ϖ / ϖ)).val • r = 0
    rw [hσ', div_self hϖ0]
    have h0 := dlog_epow hζ (0 : ZMod d)
    rw [epow, ZMod.val_zero, pow_zero] at h0
    rw [h0, ZMod.val_zero, zero_smul]
  obtain ⟨m, hm⟩ := Twist.exists_twist_lift (x0 A) hN ι χ hχ hχc
  -- the fixed germ and the global section
  have hpι : ∀ v, (((geomPtAt (x0 A)).stalkF Λ).map p).hom ((((geomPtAt (x0 A)).stalkF Λ).map ι).hom v) = 0 := by
    intro v
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp, hιp, Functor.map_zero,
      ModuleCat.hom_zero, LinearMap.zero_apply]
  have hy : ∀ σ, galRep Λ Q (x0 A) σ ((((geomPtAt (x0 A)).stalkF Λ).map p).hom m) =
      (((geomPtAt (x0 A)).stalkF Λ).map p).hom m := by
    intro σ
    have h1 := LinearMap.congr_fun (galRep_natural Λ p (x0 A) σ) m
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, ← sub_eq_zero, ← map_sub, hm σ, hpι]
  refine ⟨ϖ, m, aMap A _ hy, hϖ, hm, fun V b => germ_aMap A _ hy V b, ?_⟩
  intro C c hc y hy'
  -- local triviality over `A[1/π]`
  let B := Localization.Away π
  let u : Fin 1 → Bˣ := fun _ => (IsLocalization.Away.algebraMap_isUnit (S := B) π).unit
  have hkc : KC A ι p hζ B (Supp.sc (alpha A _ hy) ((etPull (gen A)).obj (specEt A B))) u (fun _ => r) := by
    intro a'
    refine ⟨m, ?_, fun _ => ϖ, fun _ => ?_, fun σ _ => ?_⟩
    · exact ((Supp.stalk_sc (alpha A _ hy) (x0 A) _ a').symm.trans (alpha_stalk A _ hy)).symm
    · show ϖ ^ d = phiB A a' ((IsLocalization.Away.algebraMap_isUnit (S := B) π).unit : B)
      rw [IsUnit.unit_spec, AlgHom.commutes, hϖ]
    · rw [Fin.sum_univ_one]
      exact Obs.obs_eq_of hι (hm σ).symm
  obtain ⟨V', F, hF, f, hf⟩ := LT.exists_lift hex hdA hζ hζG 1 B _ u (fun _ => r) hkc
  have hr := PrimeSpectrum.localization_away_comap_range B π
  obtain ⟨c₀, hc₀⟩ : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) := by
    rw [hr]
    exact hy'
  obtain ⟨v', hv'⟩ := hF c₀
  refine ⟨V', v', (congrArg (fun φ => φ v') (MorphismProperty.Over.w F)).symm.trans
    ((congrArg (fun z => (specEt A B).hom z) hv').trans hc₀), ?_⟩
  have h1 : Supp.sc (aMap A _ hy) V' = (((push (gen A) Λ).map p).hom.app (op V')).hom f := by
    rw [← Supp.sc_map (aMap A _ hy) F, sc_aMap]
    exact hf.symm
  have h2 := congrArg (fun ψ => (ψ.hom.app (op V')).hom f) hc
  rw [Supp.sc_comp, h1]
  refine h2.trans ?_
  simp
  rfl

end Main

end RamanujanPetersson.EtCompact.GlobQ

end

end

-- ===== S4.Def_RP_EtCompact_GalCd =====
section

/-!
# S4-EtCompact, part 36: `H²` of a `C₁` field on discrete `ℓ`-power torsion modules (CC2a)

* `IsDiscreteRep ρ`: every vector has an open stabiliser;
* **`h2_lcCob`**: for a compact group `G` with `HypL ℓ G` (`cd_ℓ G ≤ 1`), every locally constant 2-cocycle with
  values in a discrete representation killed by `ℓⁿ` is the coboundary of a locally constant 1-cochain (the values of
  the cocycle and their orbits generate a finite `G`-stable subgroup; `CdOne.cd_le_one_of_nsmul` there);
* **`hypL_gal`**: `HypL ℓ Gal(L^sep/L)` for a `C₁` field `L` with a primitive `ℓ`-th root of unity
  (`CdOne.hypL_of_field`; the Kummer closure property is automatic in the separable closure).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Topology groupCohomology

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.CdOne RamanujanPetersson.Tsen

section Fin

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type*} [AddCommGroup M] [Module Λ M]

/-- A representation is **discrete** if every vector has an open stabiliser. -/
def IsDiscreteRep (ρ : Representation Λ G M) : Prop :=
  ∀ m : M, ∃ H : Subgroup G, IsOpen (H : Set G) ∧ ∀ σ ∈ H, ρ σ m = m

variable {ρ : Representation Λ G M}

theorem IsDiscreteRep.lc_orbit (hρ : IsDiscreteRep ρ) (m : M) : IsLocallyConstant fun σ : G => ρ σ m := by
  obtain ⟨H, hH, hm⟩ := hρ m
  exact lc_of_coset H hH _ fun g w hw => by rw [map_mul, Module.End.mul_apply, hm w hw]

variable (ρ) in
/-- The `G`-orbits of the values of `f`. -/
def orbVals (f : G × G → M) : Set M := ⋃ v ∈ Set.range f, Set.range fun σ : G => ρ σ v

theorem orbVals_finite [CompactSpace G] (hρ : IsDiscreteRep ρ) {f : G × G → M} (hf : IsLocallyConstant f) :
    (orbVals ρ f).Finite :=
  hf.range_finite.biUnion fun v _ => (hρ.lc_orbit v).range_finite

theorem mem_orbVals (f : G × G → M) (σ : G) (p : G × G) : ρ σ (f p) ∈ orbVals ρ f :=
  Set.mem_iUnion₂.2 ⟨f p, ⟨p, rfl⟩, σ, rfl⟩

theorem self_mem_orbVals (f : G × G → M) (p : G × G) : f p ∈ orbVals ρ f := by
  have h := mem_orbVals (ρ := ρ) f 1 p
  rwa [map_one, Module.End.one_apply] at h

variable (ρ) in
/-- The subgroup generated by `orbVals ρ f`. -/
abbrev orbSub (f : G × G → M) : AddSubgroup M := AddSubgroup.closure (orbVals ρ f)

theorem orbSub_stable (f : G × G → M) (σ : G) {m : M} (hm : m ∈ orbSub ρ f) : ρ σ m ∈ orbSub ρ f := by
  have h : orbSub ρ f ≤ (orbSub ρ f).comap (ρ σ).toAddMonoidHom := by
    rw [AddSubgroup.closure_le]
    intro t ht
    obtain ⟨v, ⟨p, rfl⟩, ht⟩ := Set.mem_iUnion₂.1 ht
    obtain ⟨τ, rfl⟩ := ht
    have h' := mem_orbVals (ρ := ρ) f (σ * τ) p
    rw [map_mul, Module.End.mul_apply] at h'
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    exact AddSubgroup.subset_closure h'
  exact AddSubgroup.mem_comap.1 (h hm)

variable (ρ) in
/-- The action of `G` on `orbSub ρ f`. -/
def orbAct (f : G × G → M) : DistribMulAction G (orbSub ρ f) where
  smul σ m := ⟨ρ σ m, orbSub_stable f σ m.2⟩
  one_smul m := Subtype.ext (show ρ 1 (m : M) = m by rw [map_one, Module.End.one_apply])
  mul_smul σ τ m := Subtype.ext (show ρ (σ * τ) (m : M) = ρ σ (ρ τ m) by rw [map_mul, Module.End.mul_apply])
  smul_zero σ := Subtype.ext (show ρ σ (0 : M) = 0 from map_zero _)
  smul_add σ m m' := Subtype.ext (show ρ σ ((m : M) + m') = ρ σ m + ρ σ m' from map_add _ _ _)

/-- **`H² = 0` on discrete `ℓ`-power torsion representations** of a compact group with `HypL ℓ`. -/
theorem h2_lcCob [CompactSpace G] (l : ℕ) [hl : Fact l.Prime] (hL : HypL l G) (n : ℕ) (hρ : IsDiscreteRep ρ)
    (hM : ∀ m : M, (l ^ n) • m = 0) {f : G × G → M} (hf : IsLocallyConstant f)
    (hc : ∀ g h j : G, f (g * h, j) + f (g, h) = ρ g (f (h, j)) + f (g, h * j)) :
    ∃ a : G → M, IsLocallyConstant a ∧ ∀ g h : G, f (g, h) = ρ g (a h) - a (g * h) + a g := by
  let _ := orbAct ρ f
  have : Finite (orbVals ρ f) := (orbVals_finite hρ hf).to_subtype
  have hM0 : ∀ m : orbSub ρ f, (l ^ n) • m = 0 := fun m => Subtype.ext (by simpa using hM (m : M))
  have : Finite (orbSub ρ f) := AddCommGroup.finite_of_fg_isAddTorsion (orbSub ρ f) fun m =>
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨l ^ n, pow_pos hl.out.pos n, hM0 m⟩
  have hact : LcAct G (orbSub ρ f) := fun m =>
    IsLocallyConstant.desc _ Subtype.val (hρ.lc_orbit (m : M)) Subtype.val_injective
  let f0 : G × G → orbSub ρ f := fun p => ⟨f p, AddSubgroup.subset_closure (self_mem_orbVals f p)⟩
  have hf0 : IsLocallyConstant f0 := IsLocallyConstant.desc _ Subtype.val hf Subtype.val_injective
  have hc0 : IsCocycle₂ f0 := fun g h j => Subtype.ext (hc g h j)
  obtain ⟨b, hb, hfb⟩ := cd_le_one_of_nsmul l hL n (orbSub ρ f) hM0 hact hf0 hc0
  exact ⟨fun g => (b g : M), hb.comp Subtype.val, fun g h => congrArg Subtype.val (hfb g h)⟩

end Fin

/-- **`HypL ℓ Gal(L^sep/L)`** for a `C₁` field `L` with a primitive `ℓ`-th root of unity. -/
theorem hypL_gal (L : Type*) [Field L] (hC1 : IsC1 L) (l : ℕ) [Fact l.Prime] (hl : (l : L) ≠ 0) {ζ : L}
    (hζ : IsPrimitiveRoot ζ l) : HypL l (SeparableClosure L ≃ₐ[L] SeparableClosure L) := by
  refine hypL_of_field l hζ (fun E hE => by have := hE; exact hC1.of_algebraic) ?_
  intro E L' _ _ _ b _
  refine ⟨1, one_ne_zero, ?_⟩
  have : NeZero ((l : SeparableClosure L)) := ⟨by
    rw [← map_natCast (algebraMap L (SeparableClosure L))]
    exact (_root_.map_ne_zero _).2 hl⟩
  obtain ⟨y, hy⟩ := IsSepClosed.exists_pow_nat_eq (((b : L') : SeparableClosure L)) l
  exact ⟨y, by rw [map_one, one_mul, hy]⟩

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_PtInj =====
section

/-!
# S4-EtCompact, part 37: dimension shifting and cocycles in injective sheaves on a point (CC2b)

* `ext_eq_zero_of_coker`: if `Ext¹(A, I/F) = 0` for every injective presentation `F ↪ I`, then
  `Ext^(n+2)(A, -) = 0` (dimension shifting);
* `IsDiscreteRep.lc_apply`: `y ↦ ρ (s y) (u y)` is locally constant (`s` continuous, `u` locally constant);
* `repStab ρ v`: the stabiliser of `v`, as a subgroup;
* `galRep_isDiscrete`: the Galois action on a stalk is discrete;
* **`coboundary_of_injective`**: on `X ≅ Spec κ(x0)`, every locally constant 1-cocycle of `Gal x0` with values in
  the stalk of an injective sheaf `I` is a coboundary (realize the extension `I_x̄ × Λ` as a sheaf `E`; the
  inclusion `I ⟶ E` has a retraction).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Topology

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne

section Gen

universe w v u'

variable {C : Type u'} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]

open Abelian

/-- **Dimension shifting**: if `Ext¹(A, I/F) = 0` for every injective presentation `F ↪ I`, then
`Ext^(n+2)(A, -) = 0`. -/
theorem ext_eq_zero_of_coker (A : C) (h : ∀ (F : C) (e : Ext.{w} A (cokernel (Injective.ι F)) 1), e = 0) :
    ∀ (n : ℕ) (F : C) (e : Ext.{w} A F (n + 2)), e = 0 := by
  intro n
  induction n with
  | zero =>
    intro F e
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ A (injPres_shortExact F) e
      (Ext.eq_zero_of_injective _) (show 1 + 1 = 0 + 2 from rfl)
    rw [h F x₃, Ext.zero_comp]
  | succ n ih =>
    intro F e
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ A (injPres_shortExact F) e
      (Ext.eq_zero_of_injective _) (show n + 2 + 1 = n + 1 + 2 by omega)
    rw [ih _ x₃, Ext.zero_comp]

end Gen

section Rep

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type*} [AddCommGroup M] [Module Λ M] {ρ : Representation Λ G M}

theorem IsDiscreteRep.lc_apply {Y : Type*} [TopologicalSpace Y] (hρ : IsDiscreteRep ρ) {s : Y → G} {u : Y → M}
    (hs : Continuous s) (hu : IsLocallyConstant u) : IsLocallyConstant fun y => ρ (s y) (u y) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y0
  obtain ⟨H, hH, hfix⟩ := hρ (u y0)
  have h1 := (IsLocallyConstant.iff_eventually_eq u).1 hu y0
  have h2 : (fun y => (s y0)⁻¹ * s y) ⁻¹' (H : Set G) ∈ 𝓝 y0 :=
    (continuous_const.mul hs).continuousAt.preimage_mem_nhds
      (hH.mem_nhds (show (s y0)⁻¹ * s y0 ∈ H by rw [inv_mul_cancel]; exact H.one_mem))
  filter_upwards [h1, h2] with y hy1 hy2
  rw [hy1, ← mul_inv_cancel_left (s y0) (s y), map_mul, Module.End.mul_apply, hfix ((s y0)⁻¹ * s y) hy2]

variable (ρ) in
/-- The stabiliser of `v`, as a subgroup. -/
def repStab (v : M) : Subgroup G where
  carrier := {σ | ρ σ v = v}
  mul_mem' {a b} ha hb := by
    show ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, show ρ b v = v from hb, show ρ a v = v from ha]
  one_mem' := by
    show ρ 1 v = v
    rw [map_one, Module.End.one_apply]
  inv_mem' {a} ha := by
    show ρ a⁻¹ v = v
    have ha' : ρ a v = v := ha
    conv_lhs => rw [← ha']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end Rep

section Point

universe u

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] {Λ : Type u} [CommRing Λ]

theorem galRep_isDiscrete (F : EtSh Λ X) : IsDiscreteRep (galRep Λ F x0) := fun v => exists_open_fix Λ F x0 v

/-- **Cocycles in an injective sheaf are coboundaries** (on a point). -/
theorem coboundary_of_injective (I : EtSh Λ X) [Injective I] {b : Gal x0 → stalk Λ I x0}
    (hb : IsCocycle (galRep Λ I x0) b) (hbl : IsLocallyConstant b) :
    ∃ m₀ : stalk Λ I x0, ∀ g, b g = galRep Λ I x0 g m₀ - m₀ := by
  set ρ := galRep Λ I x0 with hρdef
  have hρE : ∀ v : stalk Λ I x0 × Λ, ∃ H : Subgroup (Gal x0), IsOpen (H : Set (Gal x0)) ∧
      ∀ σ ∈ H, extRep ρ b hb σ v = v := by
    intro v
    obtain ⟨H, hH, hv⟩ := exists_open_fix Λ I x0 v.1
    refine ⟨repStab (extRep ρ b hb) v, Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      (Filter.inter_mem (hH.mem_nhds H.one_mem)
        ((hbl.isOpen_fiber 0).mem_nhds (show b 1 ∈ ({0} : Set (stalk Λ I x0)) from hb.map_one))) ?_),
      fun σ hσ => hσ⟩
    rintro σ ⟨hσH, hσ0⟩
    show extRep ρ b hb σ v = v
    rw [extRep_apply, hv σ hσH, show b σ = 0 from hσ0, smul_zero, add_zero]
  obtain ⟨E, e, he⟩ := specField_essSurj x0 Λ (extRep ρ b hb) hρE
  have heq : ∀ (σ : Gal x0) (w : stalk Λ I x0 × Λ),
      galRep Λ E x0 σ (e.symm w) = e.symm (extRep ρ b hb σ w) := by
    intro σ w
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let jl : stalk Λ I x0 →ₗ[Λ] stalk Λ E x0 := e.symm.toLinearMap ∘ₗ LinearMap.inl Λ _ Λ
  have hjl : ∀ σ : Gal x0, jl ∘ₗ galRep Λ I x0 σ = galRep Λ E x0 σ ∘ₗ jl := by
    intro σ
    refine LinearMap.ext fun m => ?_
    show e.symm (LinearMap.inl Λ _ Λ (ρ σ m)) = galRep Λ E x0 σ (e.symm (LinearMap.inl Λ _ Λ m))
    rw [heq, extRep_inl]
  let j : I ⟶ E := (specField_homEquiv x0 Λ I E).symm ⟨jl, hjl⟩
  have hj : (((geomPtAt x0).stalkF Λ).map j).hom = jl :=
    congrArg Subtype.val ((specField_homEquiv x0 Λ I E).apply_symm_apply ⟨jl, hjl⟩)
  have hmono : Mono j := by
    rw [mono_iff_stalk Λ j]
    intro x
    have := subsingleton_of_isIso x0
    rw [Subsingleton.elim x x0, ModuleCat.mono_iff_injective]
    show Function.Injective (((geomPtAt x0).stalkF Λ).map j).hom
    rw [hj, LinearMap.coe_comp]
    exact e.symm.injective.comp LinearMap.inl_injective
  let r : E ⟶ I := Injective.factorThru (𝟙 I) j
  have hjr : j ≫ r = 𝟙 I := Injective.comp_factorThru (𝟙 I) j
  let rl : stalk Λ I x0 × Λ →ₗ[Λ] stalk Λ I x0 := (((geomPtAt x0).stalkF Λ).map r).hom ∘ₗ e.symm.toLinearMap
  have h1 : rl ∘ₗ LinearMap.inl Λ _ Λ = LinearMap.id :=
    calc rl ∘ₗ LinearMap.inl Λ _ Λ = (((geomPtAt x0).stalkF Λ).map r).hom ∘ₗ jl := rfl
      _ = (((geomPtAt x0).stalkF Λ).map (j ≫ r)).hom := by
        rw [CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, hj]
      _ = LinearMap.id := by rw [hjr, CategoryTheory.Functor.map_id, ModuleCat.hom_id]
  have h2 : ∀ σ : Gal x0, rl ∘ₗ extRep ρ b hb σ = ρ σ ∘ₗ rl := by
    intro σ
    refine LinearMap.ext fun w => ?_
    show (((geomPtAt x0).stalkF Λ).map r).hom (e.symm (extRep ρ b hb σ w)) =
      ρ σ ((((geomPtAt x0).stalkF Λ).map r).hom (e.symm w))
    rw [← heq]
    exact LinearMap.congr_fun (galRep_natural Λ r x0 σ) (e.symm w)
  exact (exists_retraction_iff ρ hb).1 ⟨rl, h1, h2⟩

end Point

end RamanujanPetersson.EtCompact

end

end


