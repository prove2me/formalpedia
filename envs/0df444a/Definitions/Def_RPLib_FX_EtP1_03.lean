-- Prove2me | Definitions.Def_RPLib_FX_EtP1_03
-- name    : RPLib_FX_EtP1_03
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T01:11:49.742809+00:00
-- url     : https://prove2.me/theorems/95987233-5e33-4269-a175-9c96ef360e94
-- title:
--   Étale cohomology of the projective line, library file 03 of 34
-- statement:
--   File 03 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtSheaves_GalEt`: S4-EtSheaves, part O10d-1: Galois covers with trivial inertia are etale (Chase-Harrison-Rosenberg)
--   * `S4.Def_RP_EtSheaves_TorSec`: S4-EtSheaves, part O10d-2(i): sections over `T ×_X Y` for a Galois cover
--   * `S4.Def_RP_EtSheaves_GenBr`: S4-EtSheaves, part O10b: the generic Galois group maps onto `π₁(Spec A)`
--   * `S4.Def_RP_EtSheaves_FV`: S4-EtSheaves, part O10d-2(ii): the sheaf `F_V` of a representation of a Galois group
--   * `S4.Def_RP_EtSheaves_FVRes`: S4-EtSheaves, part O10d-2(iii): `F_V` becomes constant on the Galois cover, so it is lisse
--   * `S4.Def_RP_EtSheaves_StalkFV`: S4-EtSheaves, part O10d-2(iv-b): the stalk of `F_V` is `V`, with the Galois action through `ρ`
--   * `S4.Def_RP_EtSheaves_GalFV`: S4-EtSheaves, part O10d-2(iv-c): the Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`
--   * `S4.Def_RP_EtSheaves_GenUniq`: S4-EtSheaves, O10f part b: sections of a locally constant sheaf are determined by their generic germs
--   * `S4.Def_RP_EtSheaves_LocalEx`: S4-EtSheaves, O10f part c1: local existence of sections with prescribed generic germs
--   * `S4.Def_RP_EtSheaves_FullAbs`: S4-EtSheaves, O10f part c2: fullness of the generic fibre functor (abstract form)
--   * `S4.Def_RP_EtSheaves_Unibranch`: S4-EtSheaves, O10c part 1: standard etale algebras over normal domains are unibranch
--   * `S4.Def_RP_EtSheaves_GenChart`: S4-EtSheaves, O10f part d: standard etale charts with one generic point
--   * `S4.Def_RP_EtSheaves_ChartAlg`: S4-EtSheaves, O10f part e1: etale charts with one generic point (algebra)
--   * `S4.Def_RP_EtSheaves_ChartSch`: S4-EtSheaves, O10f part e2: charts for lisse sheaves on `Spec A`
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_02

/-!
# Étale cohomology of the projective line, library file 03 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtSheaves_GalEt`: S4-EtSheaves, part O10d-1: Galois covers with trivial inertia are etale (Chase-Harrison-Rosenberg)
* `S4.Def_RP_EtSheaves_TorSec`: S4-EtSheaves, part O10d-2(i): sections over `T ×_X Y` for a Galois cover
* `S4.Def_RP_EtSheaves_GenBr`: S4-EtSheaves, part O10b: the generic Galois group maps onto `π₁(Spec A)`
* `S4.Def_RP_EtSheaves_FV`: S4-EtSheaves, part O10d-2(ii): the sheaf `F_V` of a representation of a Galois group
* `S4.Def_RP_EtSheaves_FVRes`: S4-EtSheaves, part O10d-2(iii): `F_V` becomes constant on the Galois cover, so it is lisse
* `S4.Def_RP_EtSheaves_StalkFV`: S4-EtSheaves, part O10d-2(iv-b): the stalk of `F_V` is `V`, with the Galois action through `ρ`
* `S4.Def_RP_EtSheaves_GalFV`: S4-EtSheaves, part O10d-2(iv-c): the Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`
* `S4.Def_RP_EtSheaves_GenUniq`: S4-EtSheaves, O10f part b: sections of a locally constant sheaf are determined by their generic germs
* `S4.Def_RP_EtSheaves_LocalEx`: S4-EtSheaves, O10f part c1: local existence of sections with prescribed generic germs
* `S4.Def_RP_EtSheaves_FullAbs`: S4-EtSheaves, O10f part c2: fullness of the generic fibre functor (abstract form)
* `S4.Def_RP_EtSheaves_Unibranch`: S4-EtSheaves, O10c part 1: standard etale algebras over normal domains are unibranch
* `S4.Def_RP_EtSheaves_GenChart`: S4-EtSheaves, O10f part d: standard etale charts with one generic point
* `S4.Def_RP_EtSheaves_ChartAlg`: S4-EtSheaves, O10f part e1: etale charts with one generic point (algebra)
* `S4.Def_RP_EtSheaves_ChartSch`: S4-EtSheaves, O10f part e2: charts for lisse sheaves on `Spec A`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtSheaves_GalEt =====
section

/-!
# S4-EtSheaves, part O10d-1: Galois covers with trivial inertia are etale (Chase-Harrison-Rosenberg)

Let a finite group `G` act on `B` with `A = B^G` (`IsGaloisGroup G A B`), `A → B` injective and finite, and every
inertia group at a maximal ideal of `B` trivial. Then (Chase-Harrison-Rosenberg, Thm 1.3):

* `exists_chr`: there are `x y : Fin n → B` with `∑ x_i y_i = 1` and `∑ x_i σ(y_i) = 0` for `σ ≠ 1` (`CHR`);
* `projective`: `B` is a projective `A`-module (dual basis `b = ∑ tr(y_i b) x_i`, `sum_trL_smul`);
* `phi_injective`, `phi_surjective`, `torsorEquiv`: `B ⊗_A B ≅ Π_G B`, `b ⊗ b' ↦ (b σ(b'))_σ`;
* `formallyUnramified`, HEADLINE `etale`: `A → B` is etale.

For a `GalCover` `C` this gives `GalCover.etale C : Algebra.Etale A C.B`, the scheme form `GalCover.etale_spec`, and
the torsor isomorphism `GalCover.torsorEquiv C : C.B ⊗[A] C.B ≃ₐ[A] (C.G → C.B)`.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtSheaves

namespace GalEt

section Pair

variable {B G : Type*} [CommRing B] [Group G] [MulSemiringAction G B]

end Pair

section Trace

variable (A : Type*) {B : Type*} (G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G] [Fintype G]
  [MulSemiringAction G B] [IsGaloisGroup G A B]

variable [FaithfulSMul A B]

variable {A G} {n : ℕ} {x y : Fin n → B}

end Trace

section Torsor

variable (A : Type*) {B : Type*} (G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [SMulCommClass G A B]

variable {A G} [Fintype G] {n : ℕ} {x y : Fin n → B}

variable [IsGaloisGroup G A B] [FaithfulSMul A B]

theorem psi_phi (h : CHR G x y) (u : B ⊗[A] B) : psi x y (phi A G u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [psi, map_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero, TensorProduct.zero_tmul]
  | tmul b b' =>
    unfold psi
    conv_rhs => rw [← sum_trL_smul (A := A) h b', TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← TensorProduct.smul_tmul, Algebra.smul_def (trL A G (y j * b')), algebraMap_trL, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [phi_tmul, smul_mul']
    ring
  | add u v hu hv => rw [map_add, psi_add, hu, hv]

theorem phi_injective (h : CHR G x y) : Function.Injective (phi A G (B := B)) := fun u v huv =>
  (psi_phi h u).symm.trans ((congrArg (psi x y) huv).trans (psi_phi h v))

omit [IsGaloisGroup G A B] [FaithfulSMul A B] in
theorem phi_surjective (h : CHR G x y) : Function.Surjective (phi A G (B := B)) := by
  intro f
  refine ⟨∑ τ : G, (f τ ⊗ₜ[A] (1 : B)) * ∑ i, x i ⊗ₜ[A] (τ⁻¹ • y i), funext fun σ => ?_⟩
  simp only [map_sum, map_mul, Finset.sum_apply, Pi.mul_apply, phi_tmul, smul_one, mul_one, smul_smul]
  rw [Finset.sum_eq_single σ (fun τ _ hτ => by
      rw [h.ne _ (fun h' => hτ (mul_inv_eq_one.mp h').symm), mul_zero])
    (fun h1 => absurd (Finset.mem_univ _) h1)]
  rw [mul_inv_cancel]
  simp only [one_smul, h.one, mul_one]

/-- The torsor isomorphism `B ⊗_A B ≅ Π_G B`. -/
def torsorEquiv (h : CHR G x y) : B ⊗[A] B ≃ₐ[A] (G → B) :=
  AlgEquiv.ofBijective (phi A G) ⟨phi_injective h, phi_surjective h⟩

theorem torsorEquiv_tmul (h : CHR G x y) (b b' : B) (σ : G) : torsorEquiv h (b ⊗ₜ[A] b') σ = b * σ • b' := rfl

end Torsor

section Etale

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [IsGaloisGroup G A B] [FaithfulSMul A B] [Module.Finite A B]

/-- CHR (4): `A → B` is formally unramified. -/
theorem formallyUnramified [Fintype G] {n : ℕ} {x y : Fin n → B} (h : CHR G x y) :
    Algebra.FormallyUnramified A B := by
  have := projective (A := A) h
  have : Module.FinitePresentation A B := Module.finitePresentation_of_projective A B
  rw [Algebra.FormallyUnramified.iff_exists_tensorProduct]
  refine ⟨∑ i, x i ⊗ₜ[A] y i, fun s => phi_injective (A := A) h ?_, ?_⟩
  · rw [map_mul, map_zero]
    funext σ
    simp only [Pi.mul_apply, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, phi_tmul, one_mul, smul_one,
      mul_one, Pi.zero_apply]
    by_cases hσ : σ = 1
    · subst hσ; rw [one_smul, sub_self, zero_mul]
    · rw [h.ne σ hσ, mul_zero]
  · simp only [map_sum, Algebra.TensorProduct.lmul'_apply_tmul]
    exact h.one

/-- **HEADLINE (CHR 1.3).** A finite Galois extension `A = B^G ⊆ B` with trivial inertia at every maximal ideal is
etale. -/
theorem etale [Finite G] (hI : ∀ m : Ideal B, m.IsMaximal → m.inertia G = ⊥) : Algebra.Etale A B := by
  have := Fintype.ofFinite G
  obtain ⟨n, x, y, h⟩ := exists_chr hI
  have := projective (A := A) h
  have : Module.FinitePresentation A B := Module.finitePresentation_of_projective A B
  have := formallyUnramified (A := A) h
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Etale

end GalEt

end RamanujanPetersson.EtSheaves

namespace RamanujanPetersson.GalCover

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)

/-- **A Galois cover is etale.** -/
theorem etale : Algebra.Etale A C.B :=
  EtSheaves.GalEt.etale (G := C.G) fun m hm => C.unramified m hm.isPrime

/-- Scheme form: `Spec C.B → Spec A` is etale. -/
theorem etale_spec : AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A C.B))) :=
  (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).2
    (RingHom.etale_algebraMap.2 C.etale)

/-- The torsor isomorphism `B ⊗_A B ≅ Π_G B`, `b ⊗ b' ↦ (b σ(b'))_σ`. -/
noncomputable def torsorEquiv : C.B ⊗[A] C.B ≃ₐ[A] (C.G → C.B) :=
  have := Fintype.ofFinite C.G
  EtSheaves.GalEt.torsorEquiv C.exists_chr.choose_spec.choose_spec.choose_spec

theorem torsorEquiv_tmul (b b' : C.B) (σ : C.G) : C.torsorEquiv (b ⊗ₜ[A] b') σ = b * σ • b' := rfl

end RamanujanPetersson.GalCover

end

end

-- ===== S4.Def_RP_EtSheaves_TorSec =====
section

/-!
# S4-EtSheaves, part O10d-2(i): sections over `T ×_X Y` for a Galois cover

For a Galois cover `C : GalCover A`, `π : Y = Spec B → X = Spec A` and `T` etale over `Y`, the maps
`ι σ : T → T ×_X Y`, `t ↦ (t, σ_Y t)` (`σ ∈ G`, `σ_Y = Spec σ`) cover `T ×_X Y` by pairwise disjoint sections, so for
every etale sheaf `F` on `X`, restriction is a bijection `F(T ×_X Y) ≅ Π_G F(T)` (`secEquiv`).

* `existsUnique_glue`: gluing for sheaves of modules along a covering family of arrows.
* `exists_eq_comp`: two maps `B → K` to a field that agree on `A` differ by some `σ ∈ G` (from `B ⊗_A B ≅ Π_G B`).
* `eq_of_comp_eq`: `φ ∘ σ = φ ∘ τ` for `φ : B → K` forces `σ = τ` (trivial inertia).
* `sec_cover`, `isEmpty_of_sec`, `existsUnique_sec`, `secEquiv`, `sec_naturality`, `pr_surjective`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

section Glue

universe u

variable {Λ : Type u} [CommRing Λ] {Z : Scheme.{u}}

end Glue

namespace TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)

/-- **Points of `Y` over one point of `X` differ by `G`** (ring form, from `B ⊗_A B ≅ Π_G B`). -/
theorem exists_eq_comp {K : Type} [Field K] (γ β : C.B →+* K)
    (h : γ.comp (algebraMap A C.B) = β.comp (algebraMap A C.B)) : ∃ σ : C.G, β = γ.comp (rh C σ) := by
  classical
  have := Fintype.ofFinite C.G
  letI : Algebra A K := (γ.comp (algebraMap A C.B)).toAlgebra
  let γ' : C.B →ₐ[A] K := { γ with commutes' := fun _ => rfl }
  let β' : C.B →ₐ[A] K := { β with commutes' := fun a => (RingHom.congr_fun h a).symm }
  let ψ : (C.G → C.B) →ₐ[A] K :=
    (Algebra.TensorProduct.lift γ' β' fun _ _ => Commute.all _ _).comp C.torsorEquiv.symm.toAlgHom
  have hψ : ∀ b b' : C.B, ψ (fun σ => b * σ • b') = γ b * β b' := by
    intro b b'
    have e : (fun σ => b * σ • b') = C.torsorEquiv (b ⊗ₜ[A] b') :=
      funext fun σ => (C.torsorEquiv_tmul b b' σ).symm
    rw [e]
    show (Algebra.TensorProduct.lift γ' β' (fun _ _ => Commute.all _ _)) (C.torsorEquiv.symm (C.torsorEquiv (b ⊗ₜ[A] b'))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.lift_tmul]
    rfl
  have hone : ∑ σ : C.G, (Pi.single σ (1 : C.B) : C.G → C.B) = 1 := by
    simpa using Finset.univ_sum_single (1 : C.G → C.B)
  have hsum : ∑ σ : C.G, ψ (Pi.single σ 1) = 1 := by
    rw [← map_sum, hone, map_one]
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun σ => ψ (Pi.single σ 1)) (by rw [hsum]; exact one_ne_zero)
  have he : ψ (Pi.single σ 1) = 1 := by
    have h2 : ψ (Pi.single σ 1) * ψ (Pi.single σ 1) = ψ (Pi.single σ 1) * 1 := by
      rw [← map_mul, ← Pi.single_mul, mul_one, mul_one]
    exact mul_left_cancel₀ hσ h2
  have hloc : ∀ x x' : C.G → C.B, x σ = x' σ → ψ x = ψ x' := by
    intro x x' hxx
    have hx : ∀ y : C.G → C.B, ψ y = ψ (y * Pi.single σ 1) := fun y => by rw [map_mul, he, mul_one]
    rw [hx x, hx x']
    congr 1
    funext τ
    by_cases hτ : τ = σ
    · subst hτ
      simp [hxx]
    · simp [hτ]
  refine ⟨σ, RingHom.ext fun b' => ?_⟩
  have h1 := hψ 1 b'
  have h2 := hψ (σ • b') 1
  rw [map_one, one_mul] at h1
  rw [map_one, mul_one] at h2
  show β b' = γ (σ • b')
  rw [← h1, ← h2]
  exact hloc _ _ (by simp)

/-- **Disjointness** (trivial inertia): `φ ∘ σ = φ ∘ τ` for a map `φ : B → K` to a field forces `σ = τ`. -/
theorem eq_of_comp_eq {K : Type} [Field K] (φ : C.B →+* K) {σ τ : C.G}
    (h : φ.comp (rh C σ) = φ.comp (rh C τ)) : σ = τ := by
  have hQ : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmem : σ * τ⁻¹ ∈ (RingHom.ker φ).inertia C.G := fun x => by
    show (σ * τ⁻¹) • x - x ∈ RingHom.ker φ
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, mul_smul]
    have := RingHom.congr_fun h (τ⁻¹ • x)
    simpa [smul_inv_smul] using this
  rw [C.inertia_eq_bot (RingHom.ker φ), Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

instance : Etale (pr C) := C.etale_spec

@[reassoc (attr := simp)]
theorem act_pr (σ : C.G) : act C σ ≫ pr C = pr C := by
  rw [act, ← Spec.map_comp]
  congr 1
  ext a
  exact smul_algebraMap σ a

theorem act_mul (σ τ : C.G) : act C σ ≫ act C τ = act C (σ * τ) := by
  rw [act, act, act, ← Spec.map_comp]
  congr 1
  ext b
  simp [mul_smul]

variable {C}

/-- `T` as an etale `X`-scheme. -/
abbrev tx (T : (SY C).Etale) : (SX A).Etale := (etComp (pr C)).obj T

/-- `T ×_X Y` as an etale `X`-scheme. -/
abbrev tp (T : (SY C).Etale) : (SX A).Etale := (etComp (pr C)).obj ((etPull (pr C)).obj (tx T))

/-- The section `ι σ : T → T ×_X Y`, `t ↦ (t, σ_Y t)`, on schemes. -/
def secL (T : (SY C).Etale) (σ : C.G) : T.left ⟶ tpL T :=
  pullback.lift (𝟙 T.left) (T.hom ≫ act C σ) (by simp)

@[reassoc (attr := simp)]
theorem secL_fst (T : (SY C).Etale) (σ : C.G) :
    secL T σ ≫ pullback.fst (T.hom ≫ pr C) (pr C) = 𝟙 T.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem secL_snd (T : (SY C).Etale) (σ : C.G) :
    secL T σ ≫ pullback.snd (T.hom ≫ pr C) (pr C) = T.hom ≫ act C σ :=
  pullback.lift_snd _ _ _

/-- The section `ι σ` as a morphism of etale `X`-schemes. -/
def sec (T : (SY C).Etale) (σ : C.G) : tx T ⟶ tp T :=
  MorphismProperty.Over.homMk (secL T σ) (by
    show secL T σ ≫ pullback.snd (T.hom ≫ pr C) (pr C) ≫ pr C = T.hom ≫ pr C
    rw [secL_snd_assoc, act_pr]) trivial

theorem sec_left (T : (SY C).Etale) (σ : C.G) : (sec T σ).left = secL T σ := rfl

/-- Every point of `T ×_X Y` lies on some section `ι σ`. -/
theorem exists_secL_apply (T : (SY C).Etale) (p : tpL T) :
    ∃ (σ : C.G) (q : T.left), secL T σ q = p := by
  let P := tpL T
  let fp := P.fromSpecResidueField p
  let a : Spec (P.residueField p) ⟶ T.left := fp ≫ pullback.fst (T.hom ≫ pr C) (pr C)
  let b : Spec (P.residueField p) ⟶ SY C := fp ≫ pullback.snd (T.hom ≫ pr C) (pr C)
  have hab : (a ≫ T.hom) ≫ pr C = b ≫ pr C := by
    simp only [a, b, Category.assoc]
    rw [pullback.condition]
  obtain ⟨σ, hσ⟩ := exists_eq_comp C (Spec.preimage (a ≫ T.hom)).hom (Spec.preimage b).hom (by
    rw [← Spec.map_preimage (a ≫ T.hom), ← Spec.map_preimage b] at hab
    dsimp only [pr] at hab
    rw [← Spec.map_comp, ← Spec.map_comp] at hab
    simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective hab))
  have hb : b = (a ≫ T.hom) ≫ act C σ := by
    rw [← Spec.map_preimage b, ← Spec.map_preimage (a ≫ T.hom), act, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (by rw [hσ]; rfl)
  have hfp : fp = a ≫ secL T σ := by
    refine pullback.hom_ext (f := T.hom ≫ pr C) (g := pr C) ?_ ?_
    · rw [Category.assoc, secL_fst, Category.comp_id]
    · rw [Category.assoc, secL_snd, ← Category.assoc, ← hb]
  refine ⟨σ, a (IsLocalRing.closedPoint (P.residueField p)), ?_⟩
  have := P.fromSpecResidueField_apply p (IsLocalRing.closedPoint (P.residueField p))
  rw [show P.fromSpecResidueField p = fp from rfl, hfp] at this
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans this

/-- The sections `ι σ` cover `T ×_X Y`. -/
theorem sec_cover (T : (SY C).Etale) :
    Sieve.ofArrows (fun _ : C.G => tx T) (sec T) ∈ (SX A).smallEtaleTopology (tp T) := by
  rw [mem_smallEtale_iff]
  intro p
  obtain ⟨σ, q, hq⟩ := exists_secL_apply T p
  exact ⟨tx T, sec T σ, q, Sieve.ofArrows_mk _ _ σ, hq⟩

theorem sec_left_eq {T : (SY C).Etale} {W : (SX A).Etale} {σ τ : C.G} (gi gj : W ⟶ tx T)
    (h : gi ≫ sec T σ = gj ≫ sec T τ) : gi = gj := by
  let gl : W.left ⟶ T.left := gi.left
  let gl' : W.left ⟶ T.left := gj.left
  have h0 : gl ≫ secL T σ = gl' ≫ secL T τ := congrArg (fun φ : W ⟶ tp T => φ.left) h
  have h1 := congrArg (· ≫ pullback.fst (T.hom ≫ pr C) (pr C)) h0
  simp only [Category.assoc, secL_fst, Category.comp_id] at h1
  exact MorphismProperty.Over.Hom.ext h1

/-- **The sections are disjoint**: two of them agree only over the empty scheme. -/
theorem isEmpty_of_sec {T : (SY C).Etale} {W : (SX A).Etale} {σ τ : C.G} (hστ : σ ≠ τ) (g : W ⟶ tx T)
    (h : g ≫ sec T σ = g ≫ sec T τ) : IsEmpty W.left := by
  let gl : W.left ⟶ T.left := g.left
  have h0 : gl ≫ secL T σ = gl ≫ secL T τ := congrArg (fun φ : W ⟶ tp T => φ.left) h
  have h2 := congrArg (· ≫ pullback.snd (T.hom ≫ pr C) (pr C)) h0
  simp only [Category.assoc, secL_snd] at h2
  refine ⟨fun z => hστ ?_⟩
  let k := W.left.fromSpecResidueField z ≫ gl ≫ T.hom
  have hk : k ≫ act C σ = k ≫ act C τ := by
    simp only [k, Category.assoc, h2]
  apply eq_of_comp_eq C (Spec.preimage k).hom
  rw [← Spec.map_preimage k, act, act, ← Spec.map_comp, ← Spec.map_comp] at hk
  simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective hk)

variable (Λ : Type) [CommRing Λ]

/-- **Sections over `T ×_X Y`**: every family over the sections `ι σ` glues uniquely. -/
theorem existsUnique_sec (F : EtSh Λ (SX A)) (T : (SY C).Etale) (x : C.G → F.obj.obj (op (tx T))) :
    ∃! s, ∀ σ, (F.obj.map (sec T σ).op).hom s = x σ := by
  classical
  refine existsUnique_glue F (sec T) (sec_cover T) x fun i j W gi gj e => ?_
  have hg := sec_left_eq gi gj e
  subst hg
  by_cases hij : i = j
  · subst hij
    rfl
  · have hz := isZero_obj_of_isEmpty Λ F W (isEmpty_of_sec hij gi e)
    exact (ModuleCat.subsingleton_of_isZero hz).elim _ _

/-- Restriction to the sections `ι σ`. -/
def secMap (F : EtSh Λ (SX A)) (T : (SY C).Etale) :
    F.obj.obj (op (tp T)) →ₗ[Λ] (C.G → F.obj.obj (op (tx T))) :=
  LinearMap.pi fun σ => (F.obj.map (sec T σ).op).hom

theorem secMap_bijective (F : EtSh Λ (SX A)) (T : (SY C).Etale) : Function.Bijective (secMap Λ F T) := by
  refine ⟨fun s t hst => ?_, fun x => ?_⟩
  · obtain ⟨u, -, hu⟩ := existsUnique_sec Λ F T (secMap Λ F T s)
    exact (hu s fun σ => rfl).trans (hu t fun σ => (congrFun hst σ).symm).symm
  · obtain ⟨s, hs, -⟩ := existsUnique_sec Λ F T x
    exact ⟨s, funext hs⟩

/-- **`F(T ×_X Y) ≅ Π_G F(T)`** for every etale sheaf `F` on `X`. -/
def secEquiv (F : EtSh Λ (SX A)) (T : (SY C).Etale) :
    F.obj.obj (op (tp T)) ≃ₗ[Λ] (C.G → F.obj.obj (op (tx T))) :=
  LinearEquiv.ofBijective (secMap Λ F T) (secMap_bijective Λ F T)

@[simp] theorem secEquiv_apply (F : EtSh Λ (SX A)) (T : (SY C).Etale) (s : F.obj.obj (op (tp T))) (σ : C.G) :
    secEquiv Λ F T s σ = (F.obj.map (sec T σ).op).hom s := rfl

/-- The sections are natural in `T` (scheme form). -/
theorem secL_naturality {T' T : (SY C).Etale} (h : T' ⟶ T) (σ : C.G) :
    secL T' σ ≫ pullback.lift (pullback.fst (T'.hom ≫ pr C) (pr C) ≫ h.left) (pullback.snd _ _) (by
      rw [Category.assoc, ← Category.assoc h.left, MorphismProperty.Over.w h]
      exact pullback.condition) = h.left ≫ secL T σ := by
  refine pullback.hom_ext (f := T.hom ≫ pr C) (g := pr C) ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, secL_fst_assoc, Category.assoc, secL_fst,
      Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, secL_snd, Category.assoc, secL_snd, ← Category.assoc,
      MorphismProperty.Over.w h]

/-- The sections are natural in `T`. -/
theorem sec_naturality {T' T : (SY C).Etale} (h : T' ⟶ T) (σ : C.G) :
    sec T' σ ≫ (etComp (pr C)).map ((etPull (pr C)).map ((etComp (pr C)).map h)) =
      (etComp (pr C)).map h ≫ sec T σ :=
  MorphismProperty.Over.Hom.ext (secL_naturality h σ)

end TorSec

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_GenBr =====
section

/-!
# S4-EtSheaves, part O10b: the generic Galois group maps onto `π₁(Spec A)`

For a field `K` (a fraction field of `A`), a field `κ` with `K → κ`, and a separably closed `Ω/κ`, the maximal
unramified extension `K_U = maxUnram A K` embeds into `Ω` over `K` (`emb`), and restriction along this embedding is a
continuous group homomorphism `toPi1 : Gal(Ω/κ) →* Pi1 A K` (`emb_toPi1`), surjective when `K → κ` is onto
(`toPi1_surjective`), with kernel the automorphisms fixing `emb(K_U)` (`toPi1_eq_one_iff`).

Specialised to the generic point `η = ⊥` of `Spec A` (`κ(η) ≅ K`, `fracIso`), this is the bridge
`genToPi1 : Gal η →* Pi1 A K` from the Galois group acting on stalks at `η̄` (`galRep`) to `GalCover`'s `π₁`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves

namespace GenBr

section Abstract

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

attribute [local instance] embAlg

theorem embTower : IsScalarTower K (maxUnram A K) Ω :=
  IsScalarTower.of_algebraMap_eq (fun x => ((emb A K Ω).commutes x).symm)

attribute [local instance] embTower

variable (κ : Type) [Field κ] [Algebra K κ] [Algebra κ Ω] [IsScalarTower K κ Ω]

/-- Restriction `Gal(Ω/κ) → Gal(K_U/K) = π₁(Spec A)` along `emb`. -/
def toPi1 : (Ω ≃ₐ[κ] Ω) →* Pi1 A K :=
  (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (maxUnram A K)).comp (AlgEquiv.restrictScalarsHom K)

theorem emb_toPi1 (σ : Ω ≃ₐ[κ] Ω) (x : maxUnram A K) :
    emb A K Ω (toPi1 A K Ω κ σ x) = σ (emb A K Ω x) :=
  AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) (maxUnram A K) x

theorem toPi1_eq_one_iff (σ : Ω ≃ₐ[κ] Ω) :
    toPi1 A K Ω κ σ = 1 ↔ ∀ x : maxUnram A K, σ (emb A K Ω x) = emb A K Ω x := by
  constructor
  · intro h x
    have := emb_toPi1 A K Ω κ σ x
    rw [h] at this
    exact this.symm
  · intro h
    refine AlgEquiv.ext fun x => ?_
    apply (emb A K Ω).toRingHom.injective
    show emb A K Ω (toPi1 A K Ω κ σ x) = emb A K Ω x
    rw [emb_toPi1, h]

/-- If `K → κ` is onto and `Ω/κ` is Galois, every element of `π₁` comes from `Gal(Ω/κ)`. -/
theorem toPi1_surjective [IsGalois κ Ω] (h : Function.Surjective (algebraMap K κ)) :
    Function.Surjective (toPi1 A K Ω κ) := by
  have hb : Function.Bijective (algebraMap K κ) := ⟨(algebraMap K κ).injective, h⟩
  haveI : IsGalois K Ω := IsGalois.of_equiv_equiv (F := κ) (E := Ω)
    (f := (RingEquiv.ofBijective (algebraMap K κ) hb).symm) (g := RingEquiv.refl Ω) (by
      ext c
      show algebraMap K Ω ((RingEquiv.ofBijective (algebraMap K κ) hb).symm c) = algebraMap κ Ω c
      rw [IsScalarTower.algebraMap_apply K κ Ω]
      congr 1
      exact (RingEquiv.ofBijective (algebraMap K κ) hb).apply_symm_apply c)
  intro τ
  have hσ : ∀ c : κ, (τ.liftNormal Ω) (algebraMap κ Ω c) = algebraMap κ Ω c := by
    intro c
    obtain ⟨k, rfl⟩ := h c
    rw [← IsScalarTower.algebraMap_apply K κ Ω]
    exact (τ.liftNormal Ω).commutes k
  refine ⟨AlgEquiv.ofRingEquiv (f := (τ.liftNormal Ω).toRingEquiv) hσ, ?_⟩
  refine AlgEquiv.ext fun x => ?_
  apply (emb A K Ω).toRingHom.injective
  show emb A K Ω (toPi1 A K Ω κ _ x) = emb A K Ω (τ x)
  rw [emb_toPi1]
  exact τ.liftNormal_commutes Ω x

end Abstract

section Generic

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

attribute [local instance] genAlg

attribute [local instance] genAlgSep

attribute [local instance] genTower

/-- The bridge `Gal(κ(η)^sep/κ(η)) →* π₁(Spec A) = Gal(K_U/K)` at the generic point. -/
def genToPi1 : Gal (genPt A) →* Pi1 A K := toPi1 A K (SeparableClosure (genField A)) (genField A)

/-- The embedding `K_U → κ(η)^sep` underlying `genToPi1`. -/
def genEmb : maxUnram A K →+* SeparableClosure (genField A) :=
  (emb A K (SeparableClosure (genField A))).toRingHom

theorem genEmb_algebraMap (k : K) :
    genEmb A K (algebraMap K (maxUnram A K) k) =
      algebraMap (genField A) (SeparableClosure (genField A)) (fracIso A K k) :=
  (emb A K (SeparableClosure (genField A))).commutes k

theorem genEmb_genToPi1 (σ : Gal (genPt A)) (x : maxUnram A K) :
    genEmb A K (genToPi1 A K σ x) = σ (genEmb A K x) :=
  emb_toPi1 A K (SeparableClosure (genField A)) (genField A) σ x

theorem genToPi1_eq_one_iff (σ : Gal (genPt A)) :
    genToPi1 A K σ = 1 ↔ ∀ x : maxUnram A K, σ (genEmb A K x) = genEmb A K x :=
  toPi1_eq_one_iff A K (SeparableClosure (genField A)) (genField A) σ

theorem genToPi1_surjective : Function.Surjective (genToPi1 A K) :=
  toPi1_surjective A K (SeparableClosure (genField A)) (genField A) (fracIso A K).surjective

end Generic

end GenBr

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_FV =====
section

/-!
# S4-EtSheaves, part O10d-2(ii): the sheaf `F_V` of a representation of a Galois group

* `eqSh S a b`: for an etale sheaf `S` and families `a b : ι → (S ⟶ S)`, the subsheaf of sections `s` with
  `a i s = b i s` for all `i` (glued in `S`, membership by separatedness: `existsUnique_glueS`, `sep_eq`).
* For a Galois cover `C : GalCover A` (`π : Y = Spec B → X = Spec A`) and a representation `ρ` of `G` on `V`:
  `G` acts on `U ×_X Y` over `X` by `1 × σ_Y` (`tE`, natural in `U`), hence on `SV : U ↦ V_X(U ×_X Y)` (`aS`), and on
  values by `ρ(σ⁻¹)` (`th`, `bS`). `FV C Λ V ρ := eqSh (SV C Λ V) (aS C Λ V) (bS C Λ V ρ)`.
* `sec_tE`: `ι τ ≫ (1 × σ_Y) = ι (τ σ)`; `mem_FV_iff`: for `T` etale over `Y`, a section `s` of `V_X` over `T ×_X Y`
  lies in `F_V(T)` iff `s(τσ) = ρ(σ⁻¹) s(τ)` for all `σ τ`, where `s(τ)` is the restriction of `s` along `ι τ`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

section EqSh

universe u

variable {Λ : Type u} [CommRing Λ] {Z : Scheme.{u}}

/-- **Gluing along a covering sieve** for sheaves of modules on the small etale site. -/
theorem existsUnique_glueS (F : EtSh Λ Z) {U : Z.Etale} (R : Sieve U) (hR : R ∈ Z.smallEtaleTopology U)
    (x : ∀ ⦃V : Z.Etale⦄ (f : V ⟶ U), R f → F.obj.obj (op V))
    (hx : ∀ ⦃V₁ V₂ W : Z.Etale⦄ (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U) (h₁ : R f₁) (h₂ : R f₂) (g₁ : W ⟶ V₁)
      (g₂ : W ⟶ V₂), g₁ ≫ f₁ = g₂ ≫ f₂ → (F.obj.map g₁.op).hom (x f₁ h₁) = (F.obj.map g₂.op).hom (x f₂ h₂)) :
    ∃! s, ∀ ⦃V : Z.Etale⦄ (f : V ⟶ U) (h : R f), (F.obj.map f.op).hom s = x f h := by
  let y : Presieve.FamilyOfElements (F.obj ⋙ coyoneda.obj (op (ModuleCat.of Λ Λ))) R.arrows := by
    intro V f h
    exact elt (x f h)
  have hy : y.Compatible := by
    intro V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ e
    change elt (x f₁ h₁) ≫ F.obj.map g₁.op = elt (x f₂ h₂) ≫ F.obj.map g₂.op
    rw [elt_comp, elt_comp, hx f₁ f₂ h₁ h₂ g₁ g₂ e]
  obtain ⟨t, ht, hu⟩ := F.property (ModuleCat.of Λ Λ) R hR y hy
  let t' : ModuleCat.of Λ Λ ⟶ F.obj.obj (op U) := t
  refine ⟨t'.hom 1, fun V f h => ?_, fun s hs => ?_⟩
  · have h1 : t' ≫ F.obj.map f.op = elt (x f h) := ht f h
    have h2 := congrArg (fun φ : ModuleCat.of Λ Λ ⟶ F.obj.obj (op V) => φ.hom 1) h1
    simpa [elt] using h2
  · have e : elt s = t := hu _ (by
      intro V f h
      change elt s ≫ F.obj.map f.op = elt (x f h)
      rw [elt_comp, hs f h])
    change s = t'.hom 1
    rw [← elt_one s]
    exact congrArg (fun φ : ModuleCat.of Λ Λ ⟶ F.obj.obj (op U) => φ.hom 1) e

/-- **Separatedness** along a covering sieve. -/
theorem sep_eq (F : EtSh Λ Z) {U : Z.Etale} (R : Sieve U) (hR : R ∈ Z.smallEtaleTopology U)
    (s t : F.obj.obj (op U))
    (h : ∀ ⦃V : Z.Etale⦄ (f : V ⟶ U), R f → (F.obj.map f.op).hom s = (F.obj.map f.op).hom t) : s = t := by
  obtain ⟨u, -, hu⟩ := existsUnique_glueS F R hR (fun V f _ => (F.obj.map f.op).hom t) (by
    intro V₁ V₂ W f₁ f₂ _ _ g₁ g₂ e
    rw [map_map_apply, map_map_apply, e])
  exact (hu s h).trans (hu t fun _ _ _ => rfl).symm

variable (S : EtSh Λ Z) {ι : Type*} (a b : ι → (S ⟶ S))

/-- Sections on which `a i` and `b i` agree for every `i`. -/
def eqSecSub (U : Z.Etale) : Submodule Λ (S.obj.obj (op U)) where
  carrier := {s | ∀ i, ((a i).hom.app (op U)).hom s = ((b i).hom.app (op U)).hom s}
  add_mem' {s t} hs ht i := by
    simp only [Set.mem_ofPred_eq] at hs ht
    simp only [map_add, hs i, ht i]
  zero_mem' i := by simp
  smul_mem' c s hs i := by
    simp only [Set.mem_ofPred_eq] at hs
    simp only [map_smul, hs i]

theorem mem_eqSecSub {U : Z.Etale} (s : S.obj.obj (op U)) :
    s ∈ eqSecSub S a b U ↔ ∀ i, ((a i).hom.app (op U)).hom s = ((b i).hom.app (op U)).hom s := Iff.rfl

/-- Restriction of such sections. -/
def eqSecRes {U V : Z.Etale} (f : V ⟶ U) : eqSecSub S a b U →ₗ[Λ] eqSecSub S a b V where
  toFun s := ⟨(S.obj.map f.op).hom s.1, (mem_eqSecSub S a b _).2 fun i => by
    rw [app_map (a i) f, app_map (b i) f, (mem_eqSecSub S a b _).1 s.2 i]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The presheaf of such sections. -/
def eqPre : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ where
  obj U := ModuleCat.of Λ (eqSecSub S a b U.unop)
  map f := ModuleCat.ofHom (eqSecRes S a b f.unop)
  map_id U := ModuleCat.hom_ext (LinearMap.ext fun s => Subtype.ext (by
    change (S.obj.map (𝟙 U)).hom s.1 = s.1
    rw [CategoryTheory.Functor.map_id]
    rfl))
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun s => Subtype.ext (by
    change (S.obj.map (f ≫ g)).hom s.1 = (S.obj.map g).hom ((S.obj.map f).hom s.1)
    rw [CategoryTheory.Functor.map_comp]
    rfl))

theorem isSheaf_eqPre : Presheaf.IsSheaf (Scheme.smallEtaleTopology Z) (eqPre S a b) := by
  refine Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u})
    ((isSheaf_iff_isSheaf_of_type (J := Scheme.smallEtaleTopology Z)
      (P := eqPre S a b ⋙ forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u})).2 ?_)
  intro U R hR x hx
  obtain ⟨s, hs, hu⟩ := existsUnique_glueS S R hR (fun V f h => (x f h).down.1) (by
    intro V₁ V₂ W f₁ f₂ h₁ h₂ g₁ g₂ e
    exact congrArg (fun t => t.down.1) (hx g₁ g₂ h₁ h₂ e))
  have hmem : s ∈ eqSecSub S a b U := (mem_eqSecSub S a b s).2 fun i =>
    sep_eq S R hR _ _ fun V f h => by
      rw [← app_map (a i) f, ← app_map (b i) f, hs f h]
      exact (mem_eqSecSub S a b _).1 (x f h).down.2 i
  refine ⟨ULift.up ⟨s, hmem⟩, fun V f h => ?_, fun t ht => ?_⟩
  · apply ULift.ext
    apply Subtype.ext
    exact hs f h
  · apply ULift.ext
    apply Subtype.ext
    exact hu t.down.1 fun V f h => congrArg (fun t => t.down.1) (ht f h)

/-- **The equaliser subsheaf** `U ↦ {s ∈ S(U) | ∀ i, a i s = b i s}`. -/
def eqSh : EtSh Λ Z := ⟨eqPre S a b, isSheaf_eqPre S a b⟩

end EqSh

namespace TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)

/-- `1 × σ_Y` on `U ×_X Y`, as a scheme map. -/
def tL (σ : C.G) (U : (SX A).Etale) : pullback U.hom (pr C) ⟶ pullback U.hom (pr C) :=
  pullback.lift (pullback.fst U.hom (pr C)) (pullback.snd U.hom (pr C) ≫ act C σ)
    (by rw [Category.assoc, act_pr]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem tL_fst (σ : C.G) (U : (SX A).Etale) :
    tL C σ U ≫ pullback.fst U.hom (pr C) = pullback.fst U.hom (pr C) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem tL_snd (σ : C.G) (U : (SX A).Etale) :
    tL C σ U ≫ pullback.snd U.hom (pr C) = pullback.snd U.hom (pr C) ≫ act C σ :=
  pullback.lift_snd _ _ _

/-- The scheme map of `U ×_X Y ⟶ U' ×_X Y` induced by `f : U ⟶ U'`. -/
def mL {U U' : (SX A).Etale} (f : U ⟶ U') : pullback U.hom (pr C) ⟶ pullback U'.hom (pr C) :=
  pullback.lift (pullback.fst U.hom (pr C) ≫ f.left) (pullback.snd U.hom (pr C)) (by
    rw [Category.assoc, MorphismProperty.Over.w f]
    exact pullback.condition)

theorem tL_naturality {U U' : (SX A).Etale} (f : U ⟶ U') (σ : C.G) :
    mL C f ≫ tL C σ U' = tL C σ U ≫ mL C f := by
  refine pullback.hom_ext (f := U'.hom) (g := pr C) ?_ ?_
  · calc (mL C f ≫ tL C σ U') ≫ pullback.fst U'.hom (pr C) = mL C f ≫ pullback.fst U'.hom (pr C) := by
          rw [Category.assoc, tL_fst]
      _ = pullback.fst U.hom (pr C) ≫ f.left := pullback.lift_fst _ _ _
      _ = tL C σ U ≫ pullback.fst U.hom (pr C) ≫ f.left := by rw [tL_fst_assoc]
      _ = (tL C σ U ≫ mL C f) ≫ pullback.fst U'.hom (pr C) := by
          rw [Category.assoc]
          exact congrArg (tL C σ U ≫ ·) (pullback.lift_fst _ _ _).symm
  · calc (mL C f ≫ tL C σ U') ≫ pullback.snd U'.hom (pr C)
        = mL C f ≫ pullback.snd U'.hom (pr C) ≫ act C σ := by rw [Category.assoc, tL_snd]
      _ = pullback.snd U.hom (pr C) ≫ act C σ := by
          rw [← Category.assoc]
          exact congrArg (· ≫ act C σ) (pullback.lift_snd _ _ _)
      _ = tL C σ U ≫ pullback.snd U.hom (pr C) := (tL_snd C σ U).symm
      _ = (tL C σ U ≫ mL C f) ≫ pullback.snd U'.hom (pr C) := by
          rw [Category.assoc]
          exact congrArg (tL C σ U ≫ ·) (pullback.lift_snd _ _ _).symm

/-- `1 × σ_Y` as an endomorphism of the etale `X`-scheme `U ×_X Y`. -/
def tE (σ : C.G) (U : (SX A).Etale) :
    (etComp (pr C)).obj ((etPull (pr C)).obj U) ⟶ (etComp (pr C)).obj ((etPull (pr C)).obj U) :=
  MorphismProperty.Over.homMk (tL C σ U) (by
    show tL C σ U ≫ pullback.snd U.hom (pr C) ≫ pr C = pullback.snd U.hom (pr C) ≫ pr C
    rw [tL_snd_assoc, act_pr]) trivial

theorem tE_left (σ : C.G) (U : (SX A).Etale) : (tE C σ U).left = tL C σ U := rfl

theorem tE_naturality {U U' : (SX A).Etale} (f : U ⟶ U') (σ : C.G) :
    (etComp (pr C)).map ((etPull (pr C)).map f) ≫ tE C σ U' =
      tE C σ U ≫ (etComp (pr C)).map ((etPull (pr C)).map f) :=
  MorphismProperty.Over.Hom.ext (tL_naturality C f σ)

variable (Λ : Type) [CommRing Λ] (V : Type) [AddCommGroup V] [Module Λ V]

/-- The sheaf `SV : U ↦ V_X(U ×_X Y)` (`= π_* π^* V_X`). -/
def SV : EtSh Λ (SX A) :=
  ⟨(etPull (pr C)).op ⋙ (etComp (pr C)).op ⋙ (VX A Λ V).obj,
    (etPull (pr C)).op_comp_isSheaf_of_isSheaf (SX A).smallEtaleTopology (SY C).smallEtaleTopology _
      ((etComp (pr C)).op_comp_isSheaf (SY C).smallEtaleTopology (SX A).smallEtaleTopology (VX A Λ V))⟩

/-- `G` acting on `SV` through `1 × σ_Y`. -/
def aS (σ : C.G) : SV C Λ V ⟶ SV C Λ V :=
  ObjectProperty.homMk
    { app := fun U => (VX A Λ V).obj.map (tE C σ U.unop).op
      naturality := fun U U' f => by
        change (VX A Λ V).obj.map ((etComp (pr C)).map ((etPull (pr C)).map f.unop)).op ≫
            (VX A Λ V).obj.map (tE C σ U'.unop).op =
          (VX A Λ V).obj.map (tE C σ U.unop).op ≫
            (VX A Λ V).obj.map ((etComp (pr C)).map ((etPull (pr C)).map f.unop)).op
        rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, ← op_comp, ← op_comp,
          tE_naturality] }

variable {V} (ρ : Representation Λ C.G V)

theorem th_comp (σ τ : C.G) : th C Λ ρ τ ≫ th C Λ ρ σ = th C Λ ρ (τ * σ) := by
  have h : ModuleCat.ofHom (ρ τ⁻¹) ≫ ModuleCat.ofHom (ρ σ⁻¹) = ModuleCat.ofHom (ρ (τ * σ)⁻¹) := by
    ext v
    simp [mul_inv_rev]
  unfold th
  rw [← CategoryTheory.Functor.map_comp, h]

theorem th_one : th C Λ ρ 1 = 𝟙 _ := by
  have h : ModuleCat.ofHom (ρ (1 : C.G)⁻¹) = 𝟙 (ModuleCat.of Λ V) := by
    ext v
    simp
  unfold th
  rw [h, CategoryTheory.Functor.map_id]

theorem th_app_comp (σ τ : C.G) (U : ((SX A).Etale)ᵒᵖ) (v : (VX A Λ V).obj.obj U) :
    ((th C Λ ρ σ).hom.app U).hom (((th C Λ ρ τ).hom.app U).hom v) = ((th C Λ ρ (τ * σ)).hom.app U).hom v := by
  rw [← th_comp]
  rfl

theorem th_app_one (U : ((SX A).Etale)ᵒᵖ) (v : (VX A Λ V).obj.obj U) :
    ((th C Λ ρ 1).hom.app U).hom v = v := by
  rw [th_one]
  rfl

/-- `G` acting on the values of `SV` through `ρ(σ⁻¹)`. -/
def bS (σ : C.G) : SV C Λ V ⟶ SV C Λ V :=
  ObjectProperty.homMk
    { app := fun U => (th C Λ ρ σ).hom.app (op ((etComp (pr C)).obj ((etPull (pr C)).obj U.unop)))
      naturality := fun _ _ f =>
        (th C Λ ρ σ).hom.naturality ((etComp (pr C)).map ((etPull (pr C)).map f.unop)).op }

/-- **The sheaf `F_V`**: sections `s` of `V_X` over `U ×_X Y` with `(1 × σ_Y)^* s = ρ(σ⁻¹) s` for all `σ`. -/
def FV : EtSh Λ (SX A) := eqSh (SV C Λ V) (aS C Λ V) (bS C Λ ρ)

variable {C}

theorem secL_tL (T : (SY C).Etale) (σ τ : C.G) :
    secL T τ ≫ pullback.lift (pullback.fst (T.hom ≫ pr C) (pr C))
      (pullback.snd (T.hom ≫ pr C) (pr C) ≫ act C σ) (by rw [Category.assoc, act_pr]; exact pullback.condition) =
      secL T (τ * σ) := by
  refine pullback.hom_ext (f := T.hom ≫ pr C) (g := pr C) ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, secL_fst, secL_fst]
  · rw [Category.assoc, pullback.lift_snd, secL_snd_assoc, secL_snd, act_mul]

/-- **`ι τ ≫ (1 × σ_Y) = ι (τ σ)`.** -/
theorem sec_tE (T : (SY C).Etale) (σ τ : C.G) : sec T τ ≫ tE C σ (tx T) = sec T (τ * σ) :=
  MorphismProperty.Over.Hom.ext (secL_tL T σ τ)

/-- **Sections of `F_V` over `T` etale over `Y`**: `s(τσ) = ρ(σ⁻¹) s(τ)`. -/
theorem mem_FV_iff (T : (SY C).Etale) (s : (VX A Λ V).obj.obj (op (tp T))) :
    s ∈ eqSecSub (SV C Λ V) (aS C Λ V) (bS C Λ ρ) (tx T) ↔
      ∀ σ τ : C.G, ((VX A Λ V).obj.map (sec T (τ * σ)).op).hom s =
        ((th C Λ ρ σ).hom.app (op (tx T))).hom (((VX A Λ V).obj.map (sec T τ).op).hom s) := by
  constructor
  · intro hs σ τ
    have h := congrArg ((VX A Λ V).obj.map (sec T τ).op).hom
      ((mem_eqSecSub (U := tx T) (SV C Λ V) (aS C Λ V) (bS C Λ ρ) s).1 hs σ)
    calc ((VX A Λ V).obj.map (sec T (τ * σ)).op).hom s
        = ((VX A Λ V).obj.map (sec T τ).op).hom (((VX A Λ V).obj.map (tE C σ (tx T)).op).hom s) := by
          rw [map_map_apply (VX A Λ V) (tE C σ (tx T)) (sec T τ) s, sec_tE]
      _ = ((VX A Λ V).obj.map (sec T τ).op).hom (((th C Λ ρ σ).hom.app (op (tp T))).hom s) := h
      _ = _ := (app_map (th C Λ ρ σ) (sec T τ) s).symm
  · intro h
    refine (mem_eqSecSub (U := tx T) (SV C Λ V) (aS C Λ V) (bS C Λ ρ) s).2 fun σ => ?_
    change ((VX A Λ V).obj.map (tE C σ (tx T)).op).hom s = ((th C Λ ρ σ).hom.app (op (tp T))).hom s
    refine (secMap_bijective Λ (VX A Λ V) T).1 (funext fun τ => ?_)
    change ((VX A Λ V).obj.map (sec T τ).op).hom (((VX A Λ V).obj.map (tE C σ (tx T)).op).hom s) =
      ((VX A Λ V).obj.map (sec T τ).op).hom (((th C Λ ρ σ).hom.app (op (tp T))).hom s)
    rw [map_map_apply (VX A Λ V) (tE C σ (tx T)) (sec T τ) s, sec_tE, ← app_map (th C Λ ρ σ) (sec T τ) s]
    exact h σ τ

end TorSec

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_FVRes =====
section

/-!
# S4-EtSheaves, part O10d-2(iii): `F_V` becomes constant on the Galois cover, so it is lisse

For `T` etale over `Y`, restriction along the section `ι 1` is an isomorphism `F_V(T) ≅ V_X(T)` (`eT`: a section of
`F_V` is determined by `s(1)`, and `τ ↦ ρ(τ⁻¹) v` glues to a section of `F_V`, `glueV`). These are natural in `T`, so
`π^* F_V ≅ π^* V_X ≅ V_Y` (`resIso`, `pullIso`), and `F_V` is lisse for finite `V` since `π` is surjective
(`isLisse_FV`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A} (Λ : Type) [CommRing Λ] {V : Type}
  [AddCommGroup V] [Module Λ V] (ρ : Representation Λ C.G V)

/-- The family `τ ↦ ρ(τ⁻¹) v` glued over `T ×_X Y`. -/
def glueV (T : (SY C).Etale) (v : (VX A Λ V).obj.obj (op (tx T))) : (VX A Λ V).obj.obj (op (tp T)) :=
  (secEquiv Λ (VX A Λ V) T).symm (fun τ => ((th C Λ ρ τ).hom.app (op (tx T))).hom v)

theorem sec_glueV (T : (SY C).Etale) (v : (VX A Λ V).obj.obj (op (tx T))) (τ : C.G) :
    ((VX A Λ V).obj.map (sec T τ).op).hom (glueV Λ ρ T v) = ((th C Λ ρ τ).hom.app (op (tx T))).hom v :=
  congrFun ((secEquiv Λ (VX A Λ V) T).apply_symm_apply
    (fun τ => ((th C Λ ρ τ).hom.app (op (tx T))).hom v)) τ

theorem glueV_mem (T : (SY C).Etale) (v : (VX A Λ V).obj.obj (op (tx T))) :
    glueV Λ ρ T v ∈ eqSecSub (SV C Λ V) (aS C Λ V) (bS C Λ ρ) (tx T) :=
  (mem_FV_iff Λ ρ T _).2 fun σ τ => by
    rw [sec_glueV, sec_glueV, th_app_comp]

/-- **`F_V(T) ≅ V_X(T)`** for `T` etale over `Y`: restriction along `ι 1`. -/
def eT (T : (SY C).Etale) : (FV C Λ ρ).obj.obj (op (tx T)) ≃ₗ[Λ] (VX A Λ V).obj.obj (op (tx T)) where
  toFun s := ((VX A Λ V).obj.map (sec T 1).op).hom s.1
  map_add' s t := map_add _ s.1 t.1
  map_smul' c s := map_smul _ c s.1
  invFun v := ⟨glueV Λ ρ T v, glueV_mem Λ ρ T v⟩
  left_inv s := Subtype.ext ((secMap_bijective Λ (VX A Λ V) T).1 (funext fun τ => by
    change ((VX A Λ V).obj.map (sec T τ).op).hom (glueV Λ ρ T _) =
      ((VX A Λ V).obj.map (sec T τ).op).hom s.1
    rw [sec_glueV]
    have h := (mem_FV_iff Λ ρ T s.1).1 s.2 τ 1
    rw [one_mul] at h
    exact h.symm))
  right_inv v := by
    change ((VX A Λ V).obj.map (sec T 1).op).hom (glueV Λ ρ T v) = v
    rw [sec_glueV, th_app_one]

theorem eT_apply (T : (SY C).Etale) (s : (FV C Λ ρ).obj.obj (op (tx T))) :
    eT Λ ρ T s = ((VX A Λ V).obj.map (sec T 1).op).hom s.1 := rfl

end RamanujanPetersson.EtSheaves.TorSec

end

end

-- ===== S4.Def_RP_EtSheaves_StalkFV =====
section

/-!
# S4-EtSheaves, part O10d-2(iv-b): the stalk of `F_V` is `V`, with the Galois action through `ρ`

For a geometric point `t` of `Y = Spec B`, the stalk of `F_V` at `t ≫ π` is `V` (`stalkFV`: restriction to `Y`
(`resFibIso`), `F_V|_Y ≅ V_X|_Y` (`resIso`), constant stalks). Its inverse sends `v` to the germ of the section
`unitFV v` of `F_V` over `Y` (`stalkFV_inv`). The element `g ∈ G` acting on `Y` over `X` moves `unitFV v` to
`unitFV (ρ g v)` (`map_actE_unitFV`), so an automorphism `τ` of `Spec Ω` over `X` with `τ ≫ t = t ≫ g_Y` acts on the
stalk by `ρ g` (`stalkAut_stalkFV_inv`). Every such `τ` determines a unique `g` (`existsUnique_act`, trivial inertia),
`actOf`, multiplicative in `τ` (`actOf_comp`), and `τ` acts on the stalk by `ρ (actOf τ)` (`stalkAut_stalkFV`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A} (Λ : Type) [CommRing Λ] {V : Type}
  [AddCommGroup V] [Module Λ V] (ρ : Representation Λ C.G V)

/-- The section of `F_V` over `Y` corresponding to `v` (constant on `Y`). -/
def unitFV (v : V) : (FV C Λ ρ).obj.obj (op (tx (etId (SY C)))) :=
  (eT Λ ρ (etId (SY C))).symm ((constUnit (ModuleCat.of Λ V) (tx (etId (SY C)))).hom v)

end RamanujanPetersson.EtSheaves.TorSec

end

end

-- ===== S4.Def_RP_EtSheaves_GalFV =====
section

/-!
# S4-EtSheaves, part O10d-2(iv-c): the Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`

Every geometric point `s` of `X = Spec A` lifts to `Y = Spec B` (`exists_lift`); for a lift `l`, the stalk of `F_V`
at `s` is `V` (`stalkFVAt`), an automorphism `τ` of `Spec Ω` over `X` moves `l` by a unique `actOfL τ ∈ G`
(`actOfL_eq_iff`, multiplicative: `actOfL_comp`) and acts on the stalk by `ρ (actOfL τ)` (`stalkAut_stalkFVAt`).
At `x̄ = geomPtAt x` this gives a hom `galFV : Gal(κ(x)^sep/κ(x)) →* G` with open kernel (`isOpen_ker_galFV`, via
the regular representation and discreteness of stalks), and the Galois representation on `(F_V)_x̄` is
`ρ ∘ galFV` (`galRep_FV`, `stalkFVAt_galRep`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A}

/-- **Every geometric point of `X` lifts to `Y`.** -/
theorem exists_lift (s : GeomPt (SX A)) : ∃ l : Spec (CommRingCat.of s.Ω) ⟶ SY C, l ≫ pr C = s.pt := by
  obtain ⟨y, hy⟩ := pr_surjective C s.center
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (pr C) s.pt y hy
  exact ⟨l, hl⟩

section Act

variable (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C)

end Act

variable (Λ : Type) [CommRing Λ] {V : Type} [AddCommGroup V] [Module Λ V] (ρ : Representation Λ C.G V)

end RamanujanPetersson.EtSheaves.TorSec

end

end

-- ===== S4.Def_RP_EtSheaves_GenUniq =====
section

/-!
# S4-EtSheaves, O10f part b: sections of a locally constant sheaf are determined by their generic germs

Let `x0 : X` lie in every nonempty open subset of `X` (a generic point) and `G` be a locally constant etale sheaf on
`X`. A section `d ∈ G(W)` over an etale `W → X` whose germs at all lifts of the geometric point `geomPtAt x0` vanish is
zero (`eq_zero_of_germ`); hence two sections with the same generic germs are equal (`eq_of_germ`).

Proof: near any `w ∈ W` take a chart `U → X` trivialising `G`, `G|_U ≅ M_U`; on `W ×_X U` the section `d` becomes a
section of the constant sheaf `M`, which is locally (on some `V1 ∋` a point over `w`) a constant `n ∈ M`. The image of
`V1` in `X` is a nonempty open, so it meets `x0`; the germ of `d` at a lift of `geomPtAt x0` through `V1` is `n`, so
`n = 0`. Thus `d` vanishes on a covering of `W`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

namespace GenUniq

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} (x0 : X)

/-- **Local vanishing**: a section of a locally constant sheaf with zero germs at all lifts of the generic geometric
point vanishes on an etale neighbourhood of every point. -/
theorem exists_zero_nbhd (hgen : ∀ O : Set X, IsOpen O → O.Nonempty → x0 ∈ O) {G : EtSh Λ X}
    (hG : IsLocConst Λ G) (W : X.Etale) (d : G.obj.obj (op W))
    (h : ∀ a : (geomPtAt x0).point.fiber.obj W, ((geomPtAt x0).point.toPresheafFiber W a G.obj).hom d = 0)
    (w : W.left) :
    ∃ (V : X.Etale) (g : V ⟶ W) (v : V.left), (G.obj.map g.op).hom d = 0 ∧ g.left v = w := by
  obtain ⟨U, v, hv, M, ⟨e⟩⟩ := hG (W.hom w)
  obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback w v hv.symm
  let V0 : U.left.Etale := (etPull U.hom).obj W
  let g0 : (etComp U.hom).obj V0 ⟶ W :=
    MorphismProperty.Over.homMk (pullback.fst W.hom U.hom) pullback.condition trivial
  let E : (res U.hom Λ).obj G ≅ constSh Λ U.left M := ((pullIsoRes U.hom Λ).app G).symm ≪≫ e
  let d0 : ((res U.hom Λ).obj G).obj.obj (op V0) := (G.obj.map g0.op).hom d
  obtain ⟨V1, g1, v1, ⟨n, hn⟩, hv1⟩ := (mem_smallEtale_iff V0 _).1
    (Presheaf.imageSieve_mem U.left.smallEtaleTopology (toSheafify U.left.smallEtaleTopology (constPre M))
      ((E.hom.hom.app (op V0)).hom d0)) p
  let d1 : ((res U.hom Λ).obj G).obj.obj (op V1) := (((res U.hom Λ).obj G).obj.map g1.op).hom d0
  have hn' : (E.hom.hom.app (op V1)).hom d1 = (constUnit M V1).hom n := by
    rw [app_map]
    exact hn.symm
  -- a lift of the generic geometric point through `V1`
  have hne : (Set.range ((etComp U.hom).obj V1).hom).Nonempty := ⟨_, v1, rfl⟩
  obtain ⟨v', hv'⟩ := hgen _ ((etComp U.hom).obj V1).hom.isOpenMap.isOpen_range hne
  have hu' : U.hom (V1.hom v') = (geomPtAt x0).center := by
    rw [center_geomPtAt, ← hv']
    rfl
  obtain ⟨t, ht, htx⟩ := exists_geomPt_lift (Y := U.left) (X := X) U.hom (geomPtAt x0) (V1.hom v') hu'
  obtain ⟨b1⟩ := t.exists_fiber V1 v' ht.symm
  rw [← htx] at h
  -- the germ of `d1` at `b1` vanishes
  have h1 : (t.point.toPresheafFiber V1 b1 ((res U.hom Λ).obj G).obj).hom d1 = 0 := by
    apply resFib_injective U.hom t Λ G
    refine (resFib_germ U.hom t Λ G V1 b1 d1).trans (Eq.trans ?_ (map_zero _).symm)
    have h3 : ((t.map U.hom).point.toPresheafFiber ((etComp U.hom).obj V1) (liftX U.hom t b1) G.obj).hom
        ((G.obj.map ((etComp U.hom).map g1 ≫ g0).op).hom d) =
        ((t.map U.hom).point.toPresheafFiber W
          ((t.map U.hom).point.fiber.map ((etComp U.hom).map g1 ≫ g0) (liftX U.hom t b1)) G.obj).hom d :=
      congrArg (fun φ => φ.hom d) (GrothendieckTopology.Point.toPresheafFiber_w
        (Φ := (t.map U.hom).point) ((etComp U.hom).map g1 ≫ g0) (liftX U.hom t b1) G.obj)
    exact (congrArg ((t.map U.hom).point.toPresheafFiber ((etComp U.hom).obj V1) (liftX U.hom t b1) G.obj).hom
      (map_map_apply G g0 ((etComp U.hom).map g1) d)).trans (h3.trans (h _))
  -- hence the constant `n` is zero
  have h4 : (constStalkIso Λ t M).inv.hom n = 0 := by
    have h7 : (constStalkIso Λ t M).inv.hom n =
        (t.point.toPresheafFiber V1 b1 (constSh Λ U.left M).obj).hom ((constUnit M V1).hom n) :=
      (congrArg (fun φ => φ.hom n) (constUnit_germ t M V1 b1)).symm
    have h5 : (t.point.toPresheafFiber V1 b1 (constSh Λ U.left M).obj).hom ((E.hom.hom.app (op V1)).hom d1) =
        (t.point.presheafFiber.map E.hom.hom).hom
          ((t.point.toPresheafFiber V1 b1 ((res U.hom Λ).obj G).obj).hom d1) :=
      (congrArg (fun φ => φ.hom d1) (GrothendieckTopology.Point.toPresheafFiber_naturality
        (Φ := t.point) E.hom.hom V1 b1)).symm
    exact h7.trans ((congrArg (t.point.toPresheafFiber V1 b1 (constSh Λ U.left M).obj).hom hn'.symm).trans
      (h5.trans ((congrArg (t.point.presheafFiber.map E.hom.hom).hom h1).trans (map_zero _))))
  have hn0 : n = 0 := (iso_inv_eq_zero (constStalkIso Λ t M) n).1 h4
  have hd1 : d1 = 0 := by
    have h6 : (E.hom.hom.app (op V1)).hom d1 = 0 :=
      hn'.trans ((congrArg (constUnit M V1).hom hn0).trans (map_zero _))
    have key : (E.inv.hom.app (op V1)).hom ((E.hom.hom.app (op V1)).hom d1) = d1 :=
      congrArg (fun φ => (φ.hom.app (op V1)).hom d1) E.hom_inv_id
    exact key.symm.trans ((congrArg (E.inv.hom.app (op V1)).hom h6).trans (map_zero _))
  refine ⟨(etComp U.hom).obj V1, (etComp U.hom).map g1 ≫ g0, v1, ?_, ?_⟩
  · exact (map_map_apply G g0 ((etComp U.hom).map g1) d).symm.trans hd1
  · change pullback.fst W.hom U.hom (g1.left v1) = w
    exact (congrArg (fun z => pullback.fst W.hom U.hom z) hv1).trans hp1

/-- **Generic germs detect zero**: a section of a locally constant sheaf whose germs at all lifts of the generic
geometric point vanish is zero. -/
theorem eq_zero_of_germ (hgen : ∀ O : Set X, IsOpen O → O.Nonempty → x0 ∈ O) {G : EtSh Λ X}
    (hG : IsLocConst Λ G) (W : X.Etale) (d : G.obj.obj (op W))
    (h : ∀ a : (geomPtAt x0).point.fiber.obj W, ((geomPtAt x0).point.toPresheafFiber W a G.obj).hom d = 0) :
    d = 0 := by
  let R : Sieve W :=
    { arrows := fun _ f => (G.obj.map f.op).hom d = 0
      downward_closed := fun {_ _} {f} (hf : (G.obj.map f.op).hom d = 0) g => by
        show (G.obj.map (g ≫ f).op).hom d = 0
        exact (map_map_apply G f g d).symm.trans ((congrArg (G.obj.map g.op).hom hf).trans (map_zero _)) }
  have hR : R ∈ X.smallEtaleTopology W :=
    (mem_smallEtale_iff W R).2 fun w => exists_zero_nbhd x0 hgen hG W d h w
  exact sep_eq G R hR d 0 fun _ f (hf : (G.obj.map f.op).hom d = 0) => hf.trans (map_zero _).symm

/-- **Generic germs determine sections** of a locally constant sheaf. -/
theorem eq_of_germ (hgen : ∀ O : Set X, IsOpen O → O.Nonempty → x0 ∈ O) {G : EtSh Λ X}
    (hG : IsLocConst Λ G) (W : X.Etale) (y₁ y₂ : G.obj.obj (op W))
    (h : ∀ a : (geomPtAt x0).point.fiber.obj W, ((geomPtAt x0).point.toPresheafFiber W a G.obj).hom y₁ =
      ((geomPtAt x0).point.toPresheafFiber W a G.obj).hom y₂) :
    y₁ = y₂ :=
  sub_eq_zero.1 (eq_zero_of_germ x0 hgen hG W (y₁ - y₂) fun a => by rw [map_sub, h a, sub_self])

end GenUniq

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_LocalEx =====
section

/-!
# S4-EtSheaves, O10f part c1: local existence of sections with prescribed generic germs

Let `f : F_x̄₀ → G_x̄₀` be a `Gal(κ(x0)^sep/κ(x0))`-equivariant linear map between the stalks of two etale sheaves at
the geometric point `x̄₀ = geomPtAt x0`. Let `h : T → X` be etale with `h^* G ≅ M_T` constant and with at most one point
of `T` over `x0`. Then for every section `z ∈ F(T)` there is `y ∈ G(T)` whose germ at every lift `b` of `x̄₀` to `T` is
`f` of the germ of `z` at `b` (`exists_good`).

Proof: fix one lift `b'`; every element of `G_x̄₀` is the germ at `b'` of a section over `T` (`G` is constant there), so
choose `y` with germ `f(z_{b'})`. Any other lift `b` has the same centre (the unique point over `x0`), hence differs
from `b'` by a Galois element `σ`, which moves germs of `F` and `G` alike; equivariance of `f` finishes.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

namespace LocalEx

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} (x0 : X)

/-- Every lift of `geomPtAt x0` to an etale `W` has its centre over `x0`. -/
theorem centre_over (W : X.Etale) (b : (geomPtAt x0).point.fiber.obj W) :
    W.hom (((geomPtAt x0).liftOf b).left (IsLocalRing.closedPoint (SeparableClosure (X.residueField x0)))) =
      x0 := by
  have hw : ((geomPtAt x0).liftOf b).left ≫ W.hom = (geomPtAt x0).pt := Over.w ((geomPtAt x0).liftOf b)
  have h1 : (((geomPtAt x0).liftOf b).left ≫ W.hom)
      (IsLocalRing.closedPoint (SeparableClosure (X.residueField x0))) =
      (geomPtAt x0).pt (IsLocalRing.closedPoint (SeparableClosure (X.residueField x0))) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint (SeparableClosure (X.residueField x0)))) hw
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans
    (h1.trans ((congrArg (geomPtAt x0).pt (Subsingleton.elim _ _)).trans (center_geomPtAt x0)))

/-- The same for the chart `(etComp h).obj (etId T)`, read in `T`. -/
theorem centre_over_chart {T : Scheme.{u}} (h : T ⟶ X) [Etale h]
    (b : (geomPtAt x0).point.fiber.obj ((etComp h).obj (etId T))) :
    h (((geomPtAt x0).liftOf b).left (IsLocalRing.closedPoint (SeparableClosure (X.residueField x0)))) = x0 :=
  centre_over x0 ((etComp h).obj (etId T)) b

variable {F G : EtSh Λ X} (f : stalk Λ F x0 →ₗ[Λ] stalk Λ G x0)

/-- **Local existence**: on a chart trivialising `G` with at most one point over `x0`, every section of `F` has a
partner section of `G` whose generic germs are the images under the equivariant map `f`. -/
theorem exists_good (hf : ∀ (σ : Gal x0) (v : stalk Λ F x0), f (galRep Λ F x0 σ v) = galRep Λ G x0 σ (f v))
    {T : Scheme.{u}} (h : T ⟶ X) [Etale h] (M : ModuleCat.{u} Λ) (e : (pull h Λ).obj G ≅ constSh Λ T M)
    (huniq : ∀ w₁ w₂ : T, h w₁ = x0 → h w₂ = x0 → w₁ = w₂)
    (z : F.obj.obj (op ((etComp h).obj (etId T)))) :
    ∃ y : G.obj.obj (op ((etComp h).obj (etId T))),
      ∀ b : (geomPtAt x0).point.fiber.obj ((etComp h).obj (etId T)),
        ((geomPtAt x0).point.toPresheafFiber _ b G.obj).hom y =
          f (((geomPtAt x0).point.toPresheafFiber _ b F.obj).hom z) := by
  by_cases hne : Nonempty ((geomPtAt x0).point.fiber.obj ((etComp h).obj (etId T)))
  swap
  · exact ⟨0, fun b => (hne ⟨b⟩).elim⟩
  obtain ⟨b0⟩ := hne
  have hc0 : h (((geomPtAt x0).liftOf b0).left
      (IsLocalRing.closedPoint (SeparableClosure (X.residueField x0)))) = (geomPtAt x0).center :=
    (centre_over_chart x0 h b0).trans (center_geomPtAt x0).symm
  obtain ⟨t, -, htx⟩ := exists_geomPt_lift (Y := T) h (geomPtAt x0) _ hc0
  have key : ∀ P : GeomPt X, t.map h = P → ∃ b' : P.point.fiber.obj ((etComp h).obj (etId T)),
      ∀ v : (P.stalkF Λ).obj G, ∃ y : G.obj.obj (op ((etComp h).obj (etId T))),
        (P.point.toPresheafFiber _ b' G.obj).hom y = v := by
    rintro P rfl
    exact ⟨liftX h t t.top, fun v => exists_germ_of_triv h G M e t v⟩
  obtain ⟨b', hb'⟩ := key _ htx
  obtain ⟨y, hy⟩ := hb' (f (((geomPtAt x0).point.toPresheafFiber _ b' F.obj).hom z))
  refine ⟨y, fun b => ?_⟩
  have hab := huniq _ _ (centre_over_chart x0 h b') (centre_over_chart x0 h b)
  obtain ⟨σ, hσ⟩ := Trans.exists_germ_galRep x0 Λ ((etComp h).obj (etId T)) b' b hab
  exact (hσ G y).trans ((congrArg (galRep Λ G x0 σ) hy).trans ((hf σ _).symm.trans
    (congrArg f (hσ F z).symm)))

end LocalEx

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_FullAbs =====
section

/-!
# S4-EtSheaves, O10f part c2: fullness of the generic fibre functor (abstract form)

Let `x0 : X` lie in every nonempty open subset of `X`, `F, G` etale sheaves on `X` with `G` locally constant, and
suppose `G` has *charts*: every point of every etale `U → X` has an etale neighbourhood `T → X` mapping to `U` on which
`G` is constant and which has at most one point over `x0` (`HChart`). Then every Galois-equivariant linear map
`f : F_x̄₀ → G_x̄₀` of stalks at `x̄₀ = geomPtAt x0` is the stalk of a sheaf map `φ : F ⟶ G` (`full`).

Proof: a section `y ∈ G(U)` is *good* for `z ∈ F(U)` when its germ at every lift of `x̄₀` is `f` of the germ of `z`.
Good sections are unique (generic germs determine sections, `GenUniq.eq_of_germ`), exist on charts
(`LocalEx.exists_good`), hence glue to a good section on every `U`; `φ_U z` is that section.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

namespace FullAbs

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} (x0 : X)

/-- **Charts** for `G` at `x0`: every point of every etale `U → X` has an etale neighbourhood `T → X` over `U` on
which `G` is constant and which has at most one point over `x0`. -/
def HChart (G : EtSh Λ X) : Prop :=
  ∀ (U : X.Etale) (u : U.left), ∃ (T : Scheme.{u}) (h : T ⟶ X) (_ : Etale h)
    (g : (etComp h).obj (etId T) ⟶ U) (w : ((etComp h).obj (etId T)).left), g.left w = u ∧
    (∃ M : ModuleCat.{u} Λ, Nonempty ((pull h Λ).obj G ≅ constSh Λ T M)) ∧
    ∀ w₁ w₂ : T, h w₁ = x0 → h w₂ = x0 → w₁ = w₂

variable {F G : EtSh Λ X} (f : stalk Λ F x0 →ₗ[Λ] stalk Λ G x0)

/-- The hypotheses of the fullness theorem. -/
structure Hyp : Prop where
  gen : ∀ O : Set X, IsOpen O → O.Nonempty → x0 ∈ O
  locConst : IsLocConst Λ G
  chart : HChart x0 G
  equiv : ∀ (σ : Gal x0) (v : stalk Λ F x0), f (galRep Λ F x0 σ v) = galRep Λ G x0 σ (f v)

/-- `y ∈ G(U)` is good for `z ∈ F(U)`: its generic germs are the images under `f` of those of `z`. -/
def Good (U : X.Etale) (z : F.obj.obj (op U)) (y : G.obj.obj (op U)) : Prop :=
  ∀ a : (geomPtAt x0).point.fiber.obj U,
    ((geomPtAt x0).point.toPresheafFiber U a G.obj).hom y = f (((geomPtAt x0).point.toPresheafFiber U a F.obj).hom z)

/-- Germs of restrictions. -/
theorem germ_map (P : EtSh Λ X) {U V : X.Etale} (g : V ⟶ U) (a : (geomPtAt x0).point.fiber.obj V)
    (s : P.obj.obj (op U)) :
    ((geomPtAt x0).point.toPresheafFiber V a P.obj).hom ((P.obj.map g.op).hom s) =
      ((geomPtAt x0).point.toPresheafFiber U ((geomPtAt x0).point.fiber.map g a) P.obj).hom s :=
  congrArg (fun φ => φ.hom s) (GrothendieckTopology.Point.toPresheafFiber_w (Φ := (geomPtAt x0).point) g a P.obj)

theorem good_map {U V : X.Etale} (g : V ⟶ U) {z : F.obj.obj (op U)} {y : G.obj.obj (op U)}
    (hy : Good x0 f U z y) : Good x0 f V ((F.obj.map g.op).hom z) ((G.obj.map g.op).hom y) := fun a =>
  (germ_map x0 G g a y).trans ((hy _).trans (congrArg f (germ_map x0 F g a z).symm))

theorem good_unique (H : Hyp x0 f) (U : X.Etale) {z : F.obj.obj (op U)} {y₁ y₂ : G.obj.obj (op U)}
    (h₁ : Good x0 f U z y₁) (h₂ : Good x0 f U z y₂) : y₁ = y₂ :=
  GenUniq.eq_of_germ x0 H.gen H.locConst U y₁ y₂ fun a => (h₁ a).trans (h₂ a).symm

/-- **Good sections exist** on every etale `U`: glue the local ones from the charts. -/
theorem exists_good (H : Hyp x0 f) (U : X.Etale) (z : F.obj.obj (op U)) : ∃ y, Good x0 f U z y := by
  let R : Sieve U :=
    { arrows := fun _ g => ∃ y, Good x0 f _ ((F.obj.map g.op).hom z) y
      downward_closed := fun {V W} {g} (hg : ∃ y, Good x0 f V ((F.obj.map g.op).hom z) y) k => by
        obtain ⟨y, hy⟩ := hg
        refine ⟨(G.obj.map k.op).hom y, fun a => ((good_map x0 f k hy) a).trans ?_⟩
        exact congrArg (fun s => f (((geomPtAt x0).point.toPresheafFiber W a F.obj).hom s))
          (map_map_apply F g k z) }
  have hR : R ∈ X.smallEtaleTopology U := by
    refine (mem_smallEtale_iff U R).2 fun u => ?_
    obtain ⟨T, h, _, g, w, hw, ⟨M, ⟨e⟩⟩, huniq⟩ := H.chart U u
    exact ⟨_, g, w, LocalEx.exists_good x0 f H.equiv h M e huniq _, hw⟩
  obtain ⟨s, hs, -⟩ := existsUnique_glueS G R hR (fun _ _ hg => Classical.choose hg) (by
    intro V₁ V₂ W g₁ g₂ h₁ h₂ k₁ k₂ hk
    refine GenUniq.eq_of_germ x0 H.gen H.locConst W _ _ fun a => ?_
    refine ((germ_map x0 G k₁ a _).trans (Classical.choose_spec h₁ _)).trans
      (Eq.trans ?_ ((germ_map x0 G k₂ a _).trans (Classical.choose_spec h₂ _)).symm)
    refine congrArg f ((germ_map x0 F g₁ _ z).trans (Eq.trans ?_ (germ_map x0 F g₂ _ z).symm))
    have e : (geomPtAt x0).point.fiber.map g₁ ((geomPtAt x0).point.fiber.map k₁ a) =
        (geomPtAt x0).point.fiber.map g₂ ((geomPtAt x0).point.fiber.map k₂ a) :=
      (Functor.map_comp_apply (geomPtAt x0).point.fiber k₁ g₁ a).symm.trans
        ((congrArg (fun m => (geomPtAt x0).point.fiber.map m a) hk).trans (Functor.map_comp_apply (geomPtAt x0).point.fiber k₂ g₂ a))
    exact congrArg (fun b => ((geomPtAt x0).point.toPresheafFiber U b F.obj).hom z) e)
  refine ⟨s, fun a => ?_⟩
  obtain ⟨V, g, hg, b, rfl⟩ := (geomPtAt x0).point.jointly_surjective R hR a
  exact (germ_map x0 G g b s).symm.trans
    ((congrArg ((geomPtAt x0).point.toPresheafFiber V b G.obj).hom (hs g hg)).trans
      ((Classical.choose_spec hg b).trans (congrArg f (germ_map x0 F g b z))))

/-- The glued map on sections over `U`. -/
def phiFun (H : Hyp x0 f) (U : X.Etale) (z : F.obj.obj (op U)) : G.obj.obj (op U) :=
  Classical.choose (exists_good x0 f H U z)

theorem phiFun_good (H : Hyp x0 f) (U : X.Etale) (z : F.obj.obj (op U)) : Good x0 f U z (phiFun x0 f H U z) :=
  Classical.choose_spec (exists_good x0 f H U z)

theorem phiFun_map (H : Hyp x0 f) {U V : X.Etale} (g : V ⟶ U) (z : F.obj.obj (op U)) :
    phiFun x0 f H V ((F.obj.map g.op).hom z) = (G.obj.map g.op).hom (phiFun x0 f H U z) :=
  good_unique x0 f H V (phiFun_good x0 f H V _) (good_map x0 f g (phiFun_good x0 f H U z))

/-- `phiFun` is linear. -/
def phiLin (H : Hyp x0 f) (U : X.Etale) : F.obj.obj (op U) →ₗ[Λ] G.obj.obj (op U) where
  toFun := phiFun x0 f H U
  map_add' z₁ z₂ := good_unique x0 f H U (phiFun_good x0 f H U (z₁ + z₂)) fun a =>
    (map_add _ _ _).trans ((congrArg₂ (· + ·) (phiFun_good x0 f H U z₁ a) (phiFun_good x0 f H U z₂ a)).trans
      ((map_add f _ _).symm.trans (congrArg f (map_add _ _ _).symm)))
  map_smul' c z := good_unique x0 f H U (phiFun_good x0 f H U (c • z)) fun a =>
    (map_smul _ c _).trans ((congrArg (c • ·) (phiFun_good x0 f H U z a)).trans
      ((map_smul f c _).symm.trans (congrArg f (map_smul _ c z).symm)))

/-- The sheaf map glued from good sections. -/
def phi (H : Hyp x0 f) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom (phiLin x0 f H U.unop)
      naturality := fun _ _ g => ModuleCat.hom_ext (LinearMap.ext fun z => phiFun_map x0 f H g.unop z) }

/-- **The stalk of `φ` at the generic geometric point is `f`.** -/
theorem stalk_phi (H : Hyp x0 f) : (((geomPtAt x0).stalkF Λ).map (phi x0 f H)).hom = f := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨U, a, z, rfl⟩ := (geomPtAt x0).point.toPresheafFiber_jointly_surjective (P := F.obj) v
  have h1 : (((geomPtAt x0).stalkF Λ).map (phi x0 f H)).hom
      (((geomPtAt x0).point.toPresheafFiber U a F.obj).hom z) =
      ((geomPtAt x0).point.toPresheafFiber U a G.obj).hom (phiFun x0 f H U z) :=
    congrArg (fun φ => φ.hom z) (GrothendieckTopology.Point.toPresheafFiber_naturality
      (Φ := (geomPtAt x0).point) (phi x0 f H).hom U a)
  exact h1.trans (phiFun_good x0 f H U z a)

/-- **Fullness of the generic fibre functor** (abstract form): under `Hyp`, every Galois-equivariant map of generic
stalks `F_x̄₀ → G_x̄₀` is the stalk of a sheaf map `F ⟶ G`. -/
theorem full (H : Hyp x0 f) : ∃ φ : F ⟶ G, (((geomPtAt x0).stalkF Λ).map φ).hom = f :=
  ⟨phi x0 f H, stalk_phi x0 f H⟩

end FullAbs

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_Unibranch =====
section

/-!
# S4-EtSheaves, O10c part 1: standard etale algebras over normal domains are unibranch

Let `B` be an integrally closed domain and `x : S` with `f(x) = 0` for a monic `f : B[X]`,
`f'(x)` a unit, and every `s : S` satisfying `s * u = p(x)` for some unit `u` and `p : B[X]`
(the shape of a standard etale presentation). Then two primes of `S` lying over `(0)` that are
contained in a common prime `𝔮` coincide.

Proof: the minimal polynomials `μᵢ` over `B` of the images of `x` in `S ⧸ 𝔭ᵢ` both divide `f`;
if they differ, they are coprime over `Frac B` (Gauss), so `μ₁ μ₂ ∣ f` in `B[X]` and `f'(x) ∈ 𝔮`,
which is impossible. With `μ₁ = μ₂`, `s ∈ 𝔭ᵢ ↔ μ ∣ p` for the same `p`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtSheaves.Unibranch

variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]

theorem aeval_mk (𝔭 : Ideal S) (x : S) (p : B[X]) :
    aeval (Ideal.Quotient.mk 𝔭 x) p = Ideal.Quotient.mk 𝔭 (aeval x p) := by
  rw [← Ideal.Quotient.mkₐ_eq_mk B, aeval_algHom_apply]

theorem isIntegral_mk (𝔭 : Ideal S) (x : S) (f : B[X]) (hf : f.Monic) (hfx : aeval x f = 0) :
    IsIntegral B (Ideal.Quotient.mk 𝔭 x) :=
  ⟨f, hf, by rw [← aeval_def, aeval_mk, hfx, map_zero]⟩

theorem algebraMap_quot_injective (𝔭 : Ideal S) (h𝔭 : 𝔭.comap (algebraMap B S) = ⊥) :
    Function.Injective (algebraMap B (S ⧸ 𝔭)) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  have hb' : algebraMap B S b ∈ 𝔭 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap]
    exact hb
  have hb'' : b ∈ 𝔭.comap (algebraMap B S) := hb'
  rw [h𝔭] at hb''
  exact Ideal.mem_bot.1 hb''

variable [IsDomain B] [IsIntegrallyClosed B]

/-- Membership of `p(x)` in a prime over `(0)` is divisibility by the minimal polynomial. -/
theorem mem_iff_minpoly_dvd (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔭.comap (algebraMap B S) = ⊥)
    (x : S) (f : B[X]) (hf : f.Monic) (hfx : aeval x f = 0) (p : B[X]) :
    aeval x p ∈ 𝔭 ↔ minpoly B (Ideal.Quotient.mk 𝔭 x) ∣ p := by
  have : Module.IsTorsionFree B (S ⧸ 𝔭) := Module.isTorsionFree_iff_faithfulSMul.2
    ((faithfulSMul_iff_algebraMap_injective B (S ⧸ 𝔭)).2 (algebraMap_quot_injective 𝔭 h𝔭))
  have hint := isIntegral_mk 𝔭 x f hf hfx
  constructor
  · intro hp
    apply minpoly.isIntegrallyClosed_dvd hint
    rw [aeval_mk, Ideal.Quotient.eq_zero_iff_mem.2 hp]
  · rintro ⟨q, rfl⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← aeval_mk, aeval_mul, minpoly.aeval, zero_mul]

section Main

variable (x : S) (f : B[X]) (hf : f.Monic) (hfx : aeval x f = 0)
  (hd : IsUnit (aeval x (derivative f)))
  {𝔮 𝔭₁ 𝔭₂ : Ideal S} [𝔮.IsPrime] [𝔭₁.IsPrime] [𝔭₂.IsPrime]
  (h₁ : 𝔭₁ ≤ 𝔮) (h₂ : 𝔭₂ ≤ 𝔮)
  (h₁0 : 𝔭₁.comap (algebraMap B S) = ⊥) (h₂0 : 𝔭₂.comap (algebraMap B S) = ⊥)

include hf hfx hd h₁ h₂ h₁0 h₂0 in
/-- The two minimal polynomials agree: otherwise `f'(x) ∈ 𝔮`. -/
theorem minpoly_eq_of_le :
    minpoly B (Ideal.Quotient.mk 𝔭₁ x) = minpoly B (Ideal.Quotient.mk 𝔭₂ x) := by
  by_contra hne
  have hint1 := isIntegral_mk 𝔭₁ x f hf hfx
  have hint2 := isIntegral_mk 𝔭₂ x f hf hfx
  have hm1 := minpoly.monic hint1
  have hm2 := minpoly.monic hint2
  have hf1 : minpoly B (Ideal.Quotient.mk 𝔭₁ x) ∣ f :=
    (mem_iff_minpoly_dvd 𝔭₁ h₁0 x f hf hfx f).1 (by rw [hfx]; exact 𝔭₁.zero_mem)
  have hf2 : minpoly B (Ideal.Quotient.mk 𝔭₂ x) ∣ f :=
    (mem_iff_minpoly_dvd 𝔭₂ h₂0 x f hf hfx f).1 (by rw [hfx]; exact 𝔭₂.zero_mem)
  have hinjK : Function.Injective (algebraMap B (FractionRing B)) :=
    IsFractionRing.injective B (FractionRing B)
  have irr1 : Irreducible ((minpoly B (Ideal.Quotient.mk 𝔭₁ x)).map
      (algebraMap B (FractionRing B))) :=
    (hm1.irreducible_iff_irreducible_map_fraction_map (K := FractionRing B)).1
      (minpoly.irreducible hint1)
  have irr2 : Irreducible ((minpoly B (Ideal.Quotient.mk 𝔭₂ x)).map
      (algebraMap B (FractionRing B))) :=
    (hm2.irreducible_iff_irreducible_map_fraction_map (K := FractionRing B)).1
      (minpoly.irreducible hint2)
  have ndvd : ¬ (minpoly B (Ideal.Quotient.mk 𝔭₁ x)).map (algebraMap B (FractionRing B)) ∣
      (minpoly B (Ideal.Quotient.mk 𝔭₂ x)).map (algebraMap B (FractionRing B)) := by
    intro h
    exact hne (map_injective _ hinjK
      (eq_of_monic_of_associated (hm1.map _) (hm2.map _) (irr1.associated_of_dvd irr2 h)))
  have cop := (irr1.coprime_iff_not_dvd).2 ndvd
  have hK := cop.mul_dvd (Polynomial.map_dvd (algebraMap B (FractionRing B)) hf1)
    (Polynomial.map_dvd (algebraMap B (FractionRing B)) hf2)
  rw [← Polynomial.map_mul] at hK
  obtain ⟨h, hh⟩ := (map_dvd_map _ hinjK (hm1.mul hm2)).1 hK
  have ha1 : aeval x (minpoly B (Ideal.Quotient.mk 𝔭₁ x)) ∈ 𝔮 :=
    h₁ ((mem_iff_minpoly_dvd 𝔭₁ h₁0 x f hf hfx _).2 dvd_rfl)
  have ha2 : aeval x (minpoly B (Ideal.Quotient.mk 𝔭₂ x)) ∈ 𝔮 :=
    h₂ ((mem_iff_minpoly_dvd 𝔭₂ h₂0 x f hf hfx _).2 dvd_rfl)
  have hmem : aeval x (derivative f) ∈ 𝔮 := by
    rw [hh, derivative_mul, derivative_mul]
    simp only [map_add, map_mul]
    exact 𝔮.add_mem (𝔮.mul_mem_right _ (𝔮.add_mem (𝔮.mul_mem_left _ ha2)
      (𝔮.mul_mem_right _ ha1))) (𝔮.mul_mem_right _ (𝔮.mul_mem_right _ ha1))
  exact Ideal.IsPrime.ne_top ‹𝔮.IsPrime› (Ideal.eq_top_of_isUnit_mem _ hmem hd)

end Main

/-- Equal minimal polynomials give `𝔭₁ ≤ 𝔭₂`, using the generation property. -/
theorem le_of_minpoly_eq (x : S) (f : B[X]) (hf : f.Monic) (hfx : aeval x f = 0)
    (hgen : ∀ s : S, ∃ p : B[X], ∃ u : S, IsUnit u ∧ s * u = aeval x p)
    {𝔭₁ 𝔭₂ : Ideal S} [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (h₁0 : 𝔭₁.comap (algebraMap B S) = ⊥) (h₂0 : 𝔭₂.comap (algebraMap B S) = ⊥)
    (heq : minpoly B (Ideal.Quotient.mk 𝔭₁ x) = minpoly B (Ideal.Quotient.mk 𝔭₂ x)) :
    𝔭₁ ≤ 𝔭₂ := by
  intro s hs
  obtain ⟨p, u, hu, hsu⟩ := hgen s
  have h1 : aeval x p ∈ 𝔭₁ := hsu ▸ 𝔭₁.mul_mem_right u hs
  have hdv : minpoly B (Ideal.Quotient.mk 𝔭₂ x) ∣ p :=
    heq ▸ (mem_iff_minpoly_dvd 𝔭₁ h₁0 x f hf hfx p).1 h1
  have h2 : s * u ∈ 𝔭₂ := hsu ▸ (mem_iff_minpoly_dvd 𝔭₂ h₂0 x f hf hfx p).2 hdv
  exact (Ideal.mul_unit_mem_iff_mem 𝔭₂ hu).1 h2

/-- HEADLINE (generic form): two primes over `(0)` below a common prime coincide. -/
theorem eq_of_le_of_comap_eq_bot (x : S) (f : B[X]) (hf : f.Monic) (hfx : aeval x f = 0)
    (hd : IsUnit (aeval x (derivative f)))
    (hgen : ∀ s : S, ∃ p : B[X], ∃ u : S, IsUnit u ∧ s * u = aeval x p)
    {𝔮 𝔭₁ 𝔭₂ : Ideal S} [𝔮.IsPrime] [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (h₁ : 𝔭₁ ≤ 𝔮) (h₂ : 𝔭₂ ≤ 𝔮)
    (h₁0 : 𝔭₁.comap (algebraMap B S) = ⊥) (h₂0 : 𝔭₂.comap (algebraMap B S) = ⊥) :
    𝔭₁ = 𝔭₂ := by
  have heq := minpoly_eq_of_le x f hf hfx hd h₁ h₂ h₁0 h₂0
  exact le_antisymm (le_of_minpoly_eq x f hf hfx hgen h₁0 h₂0 heq)
    (le_of_minpoly_eq x f hf hfx hgen h₂0 h₁0 heq.symm)

/-- HEADLINE: a standard etale algebra over an integrally closed domain is unibranch: two primes
lying over `(0)` and contained in a common prime coincide. -/
theorem unibranch (P : StandardEtalePresentation B S)
    {𝔮 𝔭₁ 𝔭₂ : Ideal S} [𝔮.IsPrime] [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (h₁ : 𝔭₁ ≤ 𝔮) (h₂ : 𝔭₂ ≤ 𝔮)
    (h₁0 : 𝔭₁.comap (algebraMap B S) = ⊥) (h₂0 : 𝔭₂.comap (algebraMap B S) = ⊥) :
    𝔭₁ = 𝔭₂ :=
  eq_of_le_of_comap_eq_bot P.x P.f P.monic_f P.hasMap.1 P.hasMap.isUnit_derivative_f
    (fun s => by
      obtain ⟨p, n, e⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
      exact ⟨p, _, P.hasMap.2.pow n, e⟩) h₁ h₂ h₁0 h₂0

end RamanujanPetersson.EtSheaves.Unibranch

end

end

-- ===== S4.Def_RP_EtSheaves_GenChart =====
section

/-!
# S4-EtSheaves, O10f part d: standard etale charts with one generic point

Let `B` be an integrally closed domain and `S` a standard etale `B`-algebra which is noetherian. For every prime `q` of
`S` there is `f ∉ q` such that `D(f) ⊆ Spec S` contains at most one prime over `(0) ⊆ B` (`exists_away`), i.e.
`Spec S_f` has at most one point over the generic point of `Spec B` (`exists_away_uniq`).

Proof: `S` has finitely many minimal primes; let `f` be a product of elements `f_p ∈ p \ q`, one for each minimal
prime `p ⊄ q`. A prime `p₁` over `(0)` missing `f` contains a minimal prime `p`, which must lie in `q`; `p` is also over
`(0)`, so `p = p₁` by the unibranch property at `p₁`, hence `p₁ ⊆ q`. Two such primes lie in `q` and coincide by the
unibranch property at `q`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtSheaves.GenChart

variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S] [IsDomain B] [IsIntegrallyClosed B]

open Classical in
/-- A chosen element of `p \ q` when `p ⊄ q` (and `1` otherwise). -/
def sep (q p : Ideal S) : S :=
  if h : ¬ p ≤ q then Classical.choose (SetLike.not_le_iff_exists.1 h) else 1

theorem sep_mem {q p : Ideal S} (h : ¬ p ≤ q) : sep q p ∈ p ∧ sep q p ∉ q := by
  rw [sep, dif_pos h]
  exact Classical.choose_spec (SetLike.not_le_iff_exists.1 h)

theorem sep_notMem (q : Ideal S) [q.IsPrime] (p : Ideal S) : sep q p ∉ q := by
  by_cases h : ¬ p ≤ q
  · exact (sep_mem h).2
  · rw [sep, dif_neg h]
    exact fun h1 => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one q).2 h1)

/-- A prime over `(0)` missing the product of the `sep q p` over the minimal primes lies in `q`. -/
theorem le_of_notMem (P : StandardEtalePresentation B S) (q : Ideal S) [q.IsPrime] (s : Finset (Ideal S))
    (hs : ∀ p ∈ minimalPrimes S, p ∈ s) (p₁ : Ideal S) [p₁.IsPrime]
    (hf : ∏ p ∈ s, sep q p ∉ p₁) (h0 : p₁.comap (algebraMap B S) = ⊥) : p₁ ≤ q := by
  obtain ⟨p, hp, hle⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal S) ≤ p₁)
  have : p.IsPrime := hp.1.1
  have hpq : p ≤ q := by
    by_contra h
    exact hf (Ideal.IsPrime.prod_mem_iff.2 ⟨p, hs p hp, hle (sep_mem h).1⟩)
  have hp0 : p.comap (algebraMap B S) = ⊥ := eq_bot_iff.2 ((Ideal.comap_mono hle).trans h0.le)
  rw [← Unibranch.unibranch P hle le_rfl hp0 h0]
  exact hpq

/-- **One generic prime near `q`**: some `f ∉ q` is outside at most one prime over `(0)`. -/
theorem exists_away (P : StandardEtalePresentation B S) [IsNoetherianRing S] (q : Ideal S) [q.IsPrime] :
    ∃ f ∉ q, ∀ p₁ p₂ : Ideal S, p₁.IsPrime → p₂.IsPrime → f ∉ p₁ → f ∉ p₂ →
      p₁.comap (algebraMap B S) = ⊥ → p₂.comap (algebraMap B S) = ⊥ → p₁ = p₂ := by
  let s : Finset (Ideal S) := (minimalPrimes.finite_of_isNoetherianRing S).toFinset
  have hs : ∀ p ∈ minimalPrimes S, p ∈ s := fun p hp => (Set.Finite.mem_toFinset _).2 hp
  refine ⟨∏ p ∈ s, sep q p, fun h => ?_, fun p₁ p₂ h₁ h₂ hf₁ hf₂ h₁0 h₂0 => ?_⟩
  · obtain ⟨p, -, hp⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact sep_notMem q p hp
  · exact Unibranch.unibranch P (le_of_notMem P q s hs p₁ hf₁ h₁0) (le_of_notMem P q s hs p₂ hf₂ h₂0) h₁0 h₂0

/-- **The same on `Spec S_f`**: at most one point of `Spec S_f` lies over the generic point of `Spec B`. -/
theorem exists_away_uniq (P : StandardEtalePresentation B S) [IsNoetherianRing S] (q : Ideal S) [q.IsPrime] :
    ∃ f ∉ q, ∀ P₁ P₂ : PrimeSpectrum (Localization.Away f),
      P₁.asIdeal.comap (algebraMap B (Localization.Away f)) = ⊥ →
      P₂.asIdeal.comap (algebraMap B (Localization.Away f)) = ⊥ → P₁ = P₂ := by
  obtain ⟨f, hfq, hf⟩ := exists_away P q
  refine ⟨f, hfq, fun P₁ P₂ h₁ h₂ => ?_⟩
  have hnm : ∀ Q : PrimeSpectrum (Localization.Away f), f ∉ Q.asIdeal.comap (algebraMap S _) := fun Q h =>
    Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.1 h) (IsLocalization.Away.algebraMap_isUnit f))
  have hc : ∀ Q : PrimeSpectrum (Localization.Away f),
      Q.asIdeal.comap (algebraMap B (Localization.Away f)) = ⊥ →
      (Q.asIdeal.comap (algebraMap S (Localization.Away f))).comap (algebraMap B S) = ⊥ := fun Q h => by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact h
  apply PrimeSpectrum.localization_comap_injective (Localization.Away f) (Submonoid.powers f)
  apply PrimeSpectrum.ext
  exact hf _ _ (Ideal.comap_isPrime _ _) (Ideal.comap_isPrime _ _) (hnm P₁) (hnm P₂) (hc P₁ h₁) (hc P₂ h₂)

omit [IsDomain B] [IsIntegrallyClosed B] in
/-- The noetherian hypothesis holds when `B` is noetherian. -/
theorem isNoetherianRing (P : StandardEtalePresentation B S) [IsNoetherianRing B] : IsNoetherianRing S := by
  have : Algebra.IsStandardEtale B S := ⟨⟨P⟩⟩
  exact Algebra.FiniteType.isNoetherianRing B S

end RamanujanPetersson.EtSheaves.GenChart

end

end

-- ===== S4.Def_RP_EtSheaves_ChartAlg =====
section

/-!
# S4-EtSheaves, O10f part e1: etale charts with one generic point (algebra)

Let `A` be a noetherian integrally closed domain, `R` an etale `A`-algebra and `q` a prime of `R`. There are
`f₀ ∈ R` and `f₁ ∈ R_{f₀}` such that `Spec (R_{f₀})_{f₁}` contains a point over `q` and at most one point over the
generic point of `Spec A` (`exists_chartAlg`): `f₀` makes `R_{f₀}` standard etale (`IsEtaleAt.exists_isStandardEtale`)
and `f₁` comes from `GenChart.exists_away_uniq`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtSheaves.ChartAlg

variable {A R : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  [CommRing R] [Algebra A R] [Algebra.Etale A R]

/-- **Etale charts with one generic point**, algebraic form. -/
theorem exists_chartAlg (q : Ideal R) [q.IsPrime] :
    ∃ (f₀ : R) (f₁ : Localization.Away f₀) (P₀ : PrimeSpectrum (Localization.Away f₁)),
      (P₀.asIdeal.comap (algebraMap (Localization.Away f₀) (Localization.Away f₁))).comap
        (algebraMap R (Localization.Away f₀)) = q ∧
      ∀ P₁ P₂ : PrimeSpectrum (Localization.Away f₁),
        ((P₁.asIdeal.comap (algebraMap (Localization.Away f₀) (Localization.Away f₁))).comap
          (algebraMap R (Localization.Away f₀))).comap (algebraMap A R) = ⊥ →
        ((P₂.asIdeal.comap (algebraMap (Localization.Away f₀) (Localization.Away f₁))).comap
          (algebraMap R (Localization.Away f₀))).comap (algebraMap A R) = ⊥ → P₁ = P₂ := by
  have : Algebra.IsEtaleAt A q := Algebra.FormallyEtale.comp A R (Localization.AtPrime q)
  obtain ⟨f₀, hf₀, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) q
  have hdisj : Disjoint (Submonoid.powers f₀ : Set R) q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf₀
  have hq' : (q.map (algebraMap R (Localization.Away f₀))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₀) _ q ‹_› hdisj
  have h1 := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f₀) (Localization.Away f₀)
    ‹q.IsPrime› hdisj
  rw [Ideal.under] at h1
  let P := hstd.nonempty_standardEtalePresentation.some
  have : IsNoetherianRing (Localization.Away f₀) := GenChart.isNoetherianRing P
  obtain ⟨f₁, hf₁, huniq⟩ := GenChart.exists_away_uniq P (q.map (algebraMap R (Localization.Away f₀)))
  have hdisj' : Disjoint (Submonoid.powers f₁ : Set (Localization.Away f₀))
      (q.map (algebraMap R (Localization.Away f₀))) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf₁
  have h2 := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f₁) (Localization.Away f₁) hq' hdisj'
  rw [Ideal.under] at h2
  refine ⟨f₀, f₁, ⟨(q.map (algebraMap R (Localization.Away f₀))).map (algebraMap _ (Localization.Away f₁)),
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₁) _ _ hq' hdisj'⟩, ?_,
    fun P₁ P₂ e₁ e₂ => huniq P₁ P₂ ?_ ?_⟩
  · change (((q.map (algebraMap R (Localization.Away f₀))).map _).comap _).comap _ = q
    rw [h2, h1]
  · rw [IsScalarTower.algebraMap_eq A (Localization.Away f₀) (Localization.Away f₁), ← Ideal.comap_comap,
      IsScalarTower.algebraMap_eq A R (Localization.Away f₀), ← Ideal.comap_comap]
    exact e₁
  · rw [IsScalarTower.algebraMap_eq A (Localization.Away f₀) (Localization.Away f₁), ← Ideal.comap_comap,
      IsScalarTower.algebraMap_eq A R (Localization.Away f₀), ← Ideal.comap_comap]
    exact e₂

end RamanujanPetersson.EtSheaves.ChartAlg

end

end

-- ===== S4.Def_RP_EtSheaves_ChartSch =====
section

/-!
# S4-EtSheaves, O10f part e2: charts for lisse sheaves on `Spec A`

Let `A` be a noetherian integrally closed domain and `G` a lisse etale sheaf on `Spec A`. Then `G` has charts at the
generic point (`hChart`): every point `u` of every etale `U → Spec A` has an etale neighbourhood `T → Spec A` over `U`
on which `G` is constant and which has at most one point over the generic point.

Proof: take a trivialising `U₁ → Spec A` for `G` at the image of `u`, a point `p` of `U ×_{Spec A} U₁` over `u`, an
affine open `Spec R ⊆ U ×_{Spec A} U₁` around `p` (`R` is etale over `A`), and the localisation
`Spec (R_{f₀})_{f₁} ⊆ Spec R` of `ChartAlg.exists_chartAlg` (`chart_of` assembles the chart).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

namespace ChartSch

section Abstract

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} (x0 : X) {G : EtSh Λ X}

/-- **Assembling a chart**: an etale `ι : T ⟶ U ×_X U₁` with `G|_{U₁}` constant, a point of `T` over `u` and at most
one point of `T` over `x0` give a chart of `G` at `u`. -/
theorem chart_of {U U₁ : X.Etale} (u : U.left) {T : Scheme.{u}} (ι : T ⟶ pullback U.hom U₁.hom) [Etale ι]
    (M : ModuleCat.{u} Λ) (e : (pull U₁.hom Λ).obj G ≅ constSh Λ U₁.left M) (w : T)
    (hw : pullback.fst U.hom U₁.hom (ι w) = u)
    (huniq : ∀ w₁ w₂ : T, U₁.hom (pullback.snd U.hom U₁.hom (ι w₁)) = x0 →
      U₁.hom (pullback.snd U.hom U₁.hom (ι w₂)) = x0 → w₁ = w₂) :
    ∃ (T : Scheme.{u}) (h : T ⟶ X) (_ : Etale h)
      (g : (etComp h).obj (etId T) ⟶ U) (w : ((etComp h).obj (etId T)).left), g.left w = u ∧
      (∃ M : ModuleCat.{u} Λ, Nonempty ((pull h Λ).obj G ≅ constSh Λ T M)) ∧
      ∀ w₁ w₂ : T, h w₁ = x0 → h w₂ = x0 → w₁ = w₂ := by
  have : Etale U.hom := U.prop
  have : Etale U₁.hom := U₁.prop
  refine ⟨T, (ι ≫ pullback.snd U.hom U₁.hom) ≫ U₁.hom, inferInstance,
    MorphismProperty.Over.homMk (ι ≫ pullback.fst U.hom U₁.hom) ?_ trivial, w, ?_,
    ⟨M, ⟨(pullCompIso Λ (ι ≫ pullback.snd U.hom U₁.hom) U₁.hom).app G ≪≫
      (pull (ι ≫ pullback.snd U.hom U₁.hom) Λ).mapIso e ≪≫
      pullConst Λ (ι ≫ pullback.snd U.hom U₁.hom) M⟩⟩, ?_⟩
  · show (ι ≫ pullback.fst U.hom U₁.hom) ≫ U.hom = 𝟙 T ≫ ((ι ≫ pullback.snd U.hom U₁.hom) ≫ U₁.hom)
    simp only [Category.id_comp, Category.assoc, pullback.condition]
  · show (ι ≫ pullback.fst U.hom U₁.hom) w = u
    rw [Scheme.Hom.comp_apply]
    exact hw
  · intro w₁ w₂ h₁ h₂
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h₁ h₂
    exact huniq w₁ w₂ h₁ h₂

end Abstract

section Spec

variable (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  {Λ : Type} [CommRing Λ]

end Spec

end ChartSch

end RamanujanPetersson.EtSheaves

end

end


