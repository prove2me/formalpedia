-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_191
-- name    : RPLib_FX_EtPBC_191
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:49:49.909946+00:00
-- url     : https://prove2.me/theorems/e7f22556-0606-58e7-8c25-48f45bb1aa51
-- title:
--   Proper base change for the projective line, library file 191
-- statement:
--   File 191 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat10`: S4-EtPBC-A, R4-T2 (A2c-4c): the completed chart `Ê₁` is finite over `B₁`
--   * `S4.Def_RP_EtPBC_A_CovEt1`: S4-EtPBC-A, R4-T2 (A2c-5, E4a): the completed chart `Ê₁` is etale near `p`
--   * `S4.Def_RP_EtPBC_A_CovFix`: S4-EtPBC-A, R4-T2 (G'): the geometric half of T2 from the corrected statement `CoverLiftAt₂`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_185

/-!
# Proper base change for the projective line, library file 191

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat10`: S4-EtPBC-A, R4-T2 (A2c-4c): the completed chart `Ê₁` is finite over `B₁`
* `S4.Def_RP_EtPBC_A_CovEt1`: S4-EtPBC-A, R4-T2 (A2c-5, E4a): the completed chart `Ê₁` is etale near `p`
* `S4.Def_RP_EtPBC_A_CovFix`: S4-EtPBC-A, R4-T2 (G'): the geometric half of T2 from the corrected statement `CoverLiftAt₂`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovHat10 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-4c): the completed chart `Ê₁` is finite over `B₁`

* `span_key₁`: every fraction is a `B₁`-combination of the fractions of finitely many generators of degree `D + 1`;
* **`hE₁_span`**: finitely many fractions span `Ê₁` over `B₁` (via `β₁`); **`β₁_finite`**.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Fin₁

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))

include hts in
/-- **`B₁ → Ê₁` is finite.** -/
theorem β₁_finite [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hspl : ∀ e, D ≤ e → ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁),
      z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) : (β₁ C H hφ₀ hu₀).Finite := by
  classical
  obtain ⟨r, w, hw⟩ := hE₁_span C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hspl hs hfil
  letI := (β₁ C H hφ₀ hu₀).toAlgebra
  show Module.Finite B₁ (hE₁ C H)
  refine ⟨⟨Finset.univ.image w, ?_⟩⟩
  rw [eq_top_iff]
  intro z _
  obtain ⟨b, hb⟩ := hw z
  rw [hb]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem _ (b i)
    (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem w (Finset.mem_univ i))))

end Fin₁

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovEt1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E4a): the completed chart `Ê₁` is etale near `p`

* **`et_near₁`**: there is `s ∈ Ê₁` with `s ≡ 1 mod J₁ Ê₁` and `Ê₁[1/s]` etale over `B₁` (via `β₁`); mirror of
  `et_near₀` (CovEt). Flatness of `Ê₁ ⧸ J₁^(k+1)` over `B₁ ⧸ J₁^(k+1)` comes from `θ₁ k` (`fq_flat`), freeness near `V(J₁)` from the
  local criterion (`lf_mem_freeLocus`), the unit `r` killing `Ω` from `unr_elt`, and etaleness from `et_gen` (CovEt).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Et₁

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))

include hts in
/-- `Ê₁ ⧸ J₁^(k+1)` is flat over `B₁ ⧸ J₁^(k+1)`. -/
def hE₁_flat [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R)
    (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) (k : ℕ) :
    letI := (β₁ C H hφ₀ hu₀).toAlgebra
    Module.Flat (B₁ ⧸ J₁ ^ (k + 1)) (hE₁ C H ⧸ (J₁ ^ (k + 1) • ⊤ : Submodule B₁ (hE₁ C H))) := by
  letI := (β₁ C H hφ₀ hu₀).toAlgebra
  letI : Algebra (B₁ ⧸ J₁ ^ (k + 1)) (C k).E₁ := (C k).a₁.toAlgebra
  letI : Algebra B₁ (C k).E₁ := ((C k).a₁.comp (Ideal.Quotient.mk (J₁ ^ (k + 1)))).toAlgebra
  haveI : IsScalarTower B₁ (B₁ ⧸ J₁ ^ (k + 1)) (C k).E₁ :=
    IsScalarTower.of_algebraMap_eq (R := B₁) (S := B₁ ⧸ J₁ ^ (k + 1)) (A := (C k).E₁) (fun _ => rfl)
  haveI : Module.Flat (B₁ ⧸ J₁ ^ (k + 1)) (C k).E₁ :=
    RingHom.flat_algebraMap_iff.1 (RingHom.Etale.iff_flat_and_formallyUnramified.1 (C k).et₁).1
  let θA : hE₁ C H →ₐ[B₁] (C k).E₁ := { toRingHom := θ₁ C H k, commutes' := θ₁_β₁ C H hφ₀ hu₀ k }
  exact fq_flat (J₁ ^ (k + 1)) θA (θ₁_surj C H ιB₀ ιB₁ p hts α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil k)
    ((RingHom.ker_coe_toRingHom θA).symm.trans (θ₁_ker' C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil k))

include hts in
/-- `Ê₁ ⧸ J₁ Ê₁ ≅ E₁(0)` is formally unramified over `B₁`. -/
def hE₁_fu [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R)
    (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) :
    letI := (β₁ C H hφ₀ hu₀).toAlgebra
    Algebra.FormallyUnramified B₁ (hE₁ C H ⧸ (J₁ ^ (0 + 1)).map (β₁ C H hφ₀ hu₀)) := by
  letI := (β₁ C H hφ₀ hu₀).toAlgebra
  letI : Algebra (B₁ ⧸ J₁ ^ (0 + 1)) (C 0).E₁ := (C 0).a₁.toAlgebra
  letI : Algebra B₁ (C 0).E₁ := ((C 0).a₁.comp (Ideal.Quotient.mk (J₁ ^ (0 + 1)))).toAlgebra
  haveI : IsScalarTower B₁ (B₁ ⧸ J₁ ^ (0 + 1)) (C 0).E₁ :=
    IsScalarTower.of_algebraMap_eq (R := B₁) (S := B₁ ⧸ J₁ ^ (0 + 1)) (A := (C 0).E₁) (fun _ => rfl)
  haveI : Algebra.Etale (B₁ ⧸ J₁ ^ (0 + 1)) (C 0).E₁ := RingHom.etale_algebraMap.1 (C 0).et₁
  haveI : Algebra.FormallyUnramified B₁ (C 0).E₁ :=
    Algebra.FormallyUnramified.comp B₁ (B₁ ⧸ J₁ ^ (0 + 1)) (C 0).E₁
  let θA : hE₁ C H →ₐ[B₁] (C 0).E₁ := { toRingHom := θ₁ C H 0, commutes' := θ₁_β₁ C H hφ₀ hu₀ 0 }
  have hθA : Function.Surjective θA := θ₁_surj C H ιB₀ ιB₁ p hts α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil 0
  exact Algebra.FormallyUnramified.of_equiv ((Ideal.quotientEquivAlgOfEq B₁
    ((RingHom.ker_coe_toRingHom θA).symm.trans (θ₁_ker' C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil 0)).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hθA)).symm

end Et₁

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFix =====
section

/-!
# S4-EtPBC-A, R4-T2 (G'): the geometric half of T2 from the corrected statement `CoverLiftAt₂`

* `ker_χV`, `ker_beta`: the fibre charts `Γ(Y, U) ↠ Γ(Y_x, fx⁻¹ U)` have kernel `(ker χ) Γ(Y, U)` (`Z3.ker_fx_app`);
* **`nonempty_liftD₂`**: `CoverLiftAt₂` at `x` gives the lift data `LiftD` (as `nonempty_liftD` from `CoverLiftAt`);
* **`liftT_core₂`**, **`liftT_of_coverLiftAt₂`**: `CoverLiftAt₂` at `xV` gives `T2.LiftT (qV K gK) s π`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

universe u

section Ker

end Ker

section Cover

attribute [local instance] algKY

attribute [local instance] algT

end Cover

end RamanujanPetersson.EtPBC.Cov

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.Cov

universe u

section Main

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algKY algT CoverLift.cR CoverLift.aR CoverLift.eR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁ CoverLift.f₀ CoverLift.f₁ CoverLift.et₀ CoverLift.et₁

variable (K : Type u) [Field K] {S : Scheme.{u}} (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S) [IsIso (s.pt ≫ gK)]
  {Y : Scheme.{u}} (π : Y ⟶ PV K gK) [IsFinite π] {V : Scheme.{u}} [IsAffine V] (hj : V ⟶ S) [Etale hj]
  (v : Spec (CommRingCat.of s.Ω) ⟶ V) (hv : v ≫ hj = s.pt)

/-- **G2 core** (corrected statement): the `LiftT` conclusion for one finite etale surjective `tq : T ⟶ Y_s`. -/
theorem liftT_core₂
    (hL : @CoverLiftAt₂ K _ Γ(V, ⊤) _ (algKV K (hj ≫ gK)) (χV K (hj ≫ gK) (xV K gK s v) (xV_g K gK s hj v hv)))
    {Tl : Scheme.{u}} (tq : Tl ⟶ pullback π (fibι (qV K gK) s)) [IsFinite tq] [Etale tq] [Surjective tq] :
    ∃ (P' U : Scheme.{u}) (f : P' ⟶ PV K gK) (_ : Etale f) (ι' : fib (qV K gK) s ⟶ P')
      (hι : ι' ≫ f = fibι (qV K gK) s) (_ : IsClosedImmersion ι') (Φ : U ⟶ P') (_ : IsFinite Φ) (h : U ⟶ Y)
      (hh : h ≫ π = Φ ≫ f) (_ : Function.Surjective ⇑(pullback.lift Φ h hh.symm : U ⟶ pullback f π))
      (ψ : pullback Φ ι' ⟶ Tl), ψ ≫ tq = T3d.hsU π f Φ h hh ι' (fibι (qV K gK) s) hι := by
  obtain ⟨L⟩ := nonempty_liftD₂ K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v)
    (pullback.snd tq (eY'V K gK s π hj v hv)) (xV_g K gK s hj v hv) hL
  letI := algKV K (hj ≫ gK)
  obtain ⟨U', ρ', hρf, hρs, ψ', hψ'⟩ := exists_surj_L L
  haveI : Etale (hV V L.R') := etale_hV V L.R'
  haveI : IsClosedImmersion (xL L) := isClosedImmersion_xL L
  have hv'' : ((s.pt ≫ gK) ≫ xL L) ≫ hV V L.R' ≫ hj = s.pt :=
    hvR s hj v L.R' _ (hv'_of K gK s v L.R' (xL L) _ (hxL L) rfl) hv
  have hsq := ysV_kapV K gK s π hj v L.R' (xL L) _ (hxL L) rfl hv
  exact ⟨pullback (hV V L.R' ≫ hj) (qV K gK), U', pullback.snd (hV V L.R' ≫ hj) (qV K gK), inferInstance,
    fibV K gK s (hV V L.R' ≫ hj) _ hv'', fibV_snd K gK s (hV V L.R' ≫ hj) _ hv'',
    isClosedImmersion_fibV K gK s (hV V L.R' ≫ hj) _ hv'',
    g_main π (pullback.snd (hV V L.R' ≫ hj) (qV K gK)) (kapV K gK π hj L.R') ρ'
      (fibV K gK s (hV V L.R' ≫ hj) _ hv'') (fibι (qV K gK) s) (fibV_snd K gK s (hV V L.R' ≫ hj) _ hv'')
      (ysV K gK s π (hV V L.R' ≫ hj) _ hv'') (ysV_fst K gK s π (hV V L.R' ≫ hj) _ hv'')
      (ysV_snd K gK s π (hV V L.R' ≫ hj) _ hv'') hρf hρs (eY'V K gK s π hj v hv) (yxL L)
      (eYV K gK s π hj v hv) (eYV_eY'V K gK s π hj v hv) hsq tq ψ' hψ'⟩

/-- **G2: `CoverLiftAt₂` at the neighbourhood point gives `LiftT`.** -/
theorem liftT_of_coverLiftAt₂
    (hL : @CoverLiftAt₂ K _ Γ(V, ⊤) _ (algKV K (hj ≫ gK)) (χV K (hj ≫ gK) (xV K gK s v) (xV_g K gK s hj v hv))) :
    T2.LiftT (qV K gK) s π := by
  intro T hf hs
  haveI : IsFinite T.hom := hf
  haveI : Surjective T.hom := hs
  exact liftT_core₂ K gK s π hj v hv hL T.hom

end Main

end RamanujanPetersson.EtPBC

end

end


