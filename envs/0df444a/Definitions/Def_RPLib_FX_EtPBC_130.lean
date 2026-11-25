-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_130
-- name    : RPLib_FX_EtPBC_130
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:27:15.738875+00:00
-- url     : https://prove2.me/theorems/25450c49-381b-5a6b-a6ba-061fb0812dd8
-- title:
--   Proper base change for the projective line, library file 130
-- statement:
--   File 130 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat3`: S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property
--   * `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
--   * `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
--   * `S4.Def_RP_EtPBC_A_CovAs6b`: S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover
--   * `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
--   * `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
--   * `S4.Def_RP_EtPBC_A_Z4FibC`: S4-EtPBC-A, (Z) geometric layer 13 (G-f, part 3): the `π₀` extension theorem
--   * `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
--   * `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
--   * `S4.Def_RP_EtPBC_A_T2I`: S4-EtPBC-A, R4-T2 interface: `HypT` from T1 and the lifting statement `LiftT`
--   * `S4.Def_RP_EtPBC_A_O2Rel2`: S4-EtPBC-A, O2 REL (O2R3a): the target term of the relation lies in `G`
--   * `S4.Def_RP_EtPBC_A_CovFix`: S4-EtPBC-A, R4-T2 (G'): the geometric half of T2 from the corrected statement `CoverLiftAt₂`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_082
import Definitions.Def_RPLib_FX_EtPBC_122

/-!
# Proper base change for the projective line, library file 130

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat3`: S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property
* `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
* `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
* `S4.Def_RP_EtPBC_A_CovAs6b`: S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover
* `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
* `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
* `S4.Def_RP_EtPBC_A_Z4FibC`: S4-EtPBC-A, (Z) geometric layer 13 (G-f, part 3): the `π₀` extension theorem
* `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
* `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
* `S4.Def_RP_EtPBC_A_T2I`: S4-EtPBC-A, R4-T2 interface: `HypT` from T1 and the lifting statement `LiftT`
* `S4.Def_RP_EtPBC_A_O2Rel2`: S4-EtPBC-A, O2 REL (O2R3a): the target term of the relation lies in `G`
* `S4.Def_RP_EtPBC_A_CovFix`: S4-EtPBC-A, R4-T2 (G'): the geometric half of T2 from the corrected statement `CoverLiftAt₂`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovHat3 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property

* **`β₀ : B₀ →+* hE₀`**, **`β₁ : B₁ →+* hE₁`**, **`β : N →+* hE`**, with `β₀_val`, `β₁_val`, `β_val`;
* **`hψ₀_β₀`**, **`hψ₁_β₁`**: `hψᵢ ∘ βᵢ = β ∘ φᵢ`;
* **`aw_hψ₀`**: `IsAwayMap hψ₀ (β₀ t₀)`, **`aw_hψ₁`**: `IsAwayMap hψ₁ (β₁ t₁)`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Hat3

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))
  (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀)) (hφ₁ : IsAwayMap φ₁ t₁)
  (hu₁ : IsUnit (φ₁ t₁))

/-- **`B₀ → Ê₀`**: `b ↦ ((a₀ b)ₖ, φ₀ b ∈ L₁)`. -/
def β₀ : B₀ →+* hE₀ C H hts :=
  ((fB₀ C).prod ((liftN₁ C hφ₁ hu₁).comp φ₀)).codRestrict (hE₀ C H hts) fun b => by
    obtain ⟨d, b', hb'⟩ := hφ₁.1 (φ₀ b)
    have hd : φ₀ t₀ ^ d * φ₁ t₁ ^ d = 1 := by rw [← mul_pow, hts, one_pow]
    refine (mem_hE₀ C H hts _).2 ⟨d, (fB₀ C b, fB₁ C b'), famB_mem C H ?_, rfl, ?_⟩
    · rw [← hb']
      linear_combination (-(φ₀ b)) * hd
    · show jL₁ C (sFm C ^ d) * liftN₁ C hφ₁ hu₁ (φ₀ b) = jL₁ C (fB₁ C b')
      rw [← liftN₁_φ₁ C hφ₁ hu₁ b', ← hb']
      simp only [map_mul, map_pow, liftN₁_φ₁]

theorem β₀_val (b : B₀) : (β₀ C H hts hφ₁ hu₁ b : (∀ k, (C k).E₀) × L₁ C) = (fB₀ C b, liftN₁ C hφ₁ hu₁ (φ₀ b)) :=
  rfl

end Hat3

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat4 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts

* **`frac₀ d x hx : hE₀`**, `frac₀_val`, `frac₀_spec`, `hE₀_ext`, **`eq_frac₀`**, `frac₀_congr`, **`frac₀_T₀`**,
  `frac₀_add`, `frac₀_mul`; chart 1: `frac₁`, `frac₁_spec`, `hE₁_ext`, `eq_frac₁`, `frac₁_congr`, `frac₁_T₁`, `frac₁_add`,
  `frac₁_mul`;
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Frac

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))
  (hts : φ₀ t₀ * φ₁ t₁ = 1)

/-- **`x / T₀ᵈ ∈ Ê₀`**. -/
def frac₀ (d : ℕ) (x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)) (hx : x ∈ Gam C H d) : hE₀ C H hts :=
  ⟨(x.1, IsLocalization.mk' (L₁ C) x.2 (⟨sFm C ^ d, d, rfl⟩ : Submonoid.powers (sFm C))),
    (mem_hE₀ C H hts _).2 ⟨d, x, hx, rfl, by rw [mul_comm]; exact IsLocalization.mk'_spec (L₁ C) x.2 _⟩⟩

variable {C H}

theorem frac₀_val {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) :
    (frac₀ C H hts d x hx : (∀ k, (C k).E₀) × L₁ C) =
      (x.1, IsLocalization.mk' (L₁ C) x.2 (⟨sFm C ^ d, d, rfl⟩ : Submonoid.powers (sFm C))) :=
  rfl

theorem frac₀_spec {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) :
    jL₁ C (sFm C ^ d) * (frac₀ C H hts d x hx : (∀ k, (C k).E₀) × L₁ C).2 = jL₁ C x.2 := by
  rw [mul_comm]
  exact IsLocalization.mk'_spec (L₁ C) x.2 _

/-- **Every element of `Ê₀` is a fraction** (with its own witness). -/
theorem eq_frac₀ (z : hE₀ C H hts) {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d)
    (h1 : (z : (∀ k, (C k).E₀) × L₁ C).1 = x.1)
    (h2 : jL₁ C (sFm C ^ d) * (z : (∀ k, (C k).E₀) × L₁ C).2 = jL₁ C x.2) : z = frac₀ C H hts d x hx :=
  hE₀_ext hts d h1 (h2.trans (frac₀_spec hts hx).symm)

theorem frac₀_congr {d : ℕ} {x y : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (h : x = y) (hx : x ∈ Gam C H d)
    (hy : y ∈ Gam C H d) : frac₀ C H hts d x hx = frac₀ C H hts d y hy := by
  subst h
  rfl

end Frac

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat6 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective

* **`θ₀ k : hE₀ →+* E₀(k)`**, **`θ₁ k : hE₁ →+* E₁(k)`** (evaluation of the first, resp. second, coordinate);
  `θ₀_frac₀`, `θ₁_frac₁`, `ρ₀_θ₀`, `ρ₁_θ₁` (compatible with the transitions), `θ₀_β₀`, `θ₁_β₁`;
* **`gen_sys`**: lifts of level-`0` generators of `O(d)`; **`gam_lev_surj`**: every level-`m` section of `O(d)` is
  the level-`m` part of a compatible family;
* **`θ₀_surj`**, **`θ₁_surj`** (all `k`), when the transitions are surjective on sections and `FilProp` holds in all
  degrees `≥ D`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Theta

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (hts : φ₀ t₀ * φ₁ t₁ = 1)

def θ₀_β₀ (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁)) (k : ℕ) (b : B₀) :
    θ₀ C H hts k (β₀ C H hts hφ₁ hu₁ b) = (C k).a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) b) := rfl

end Theta

section Surj

end Surj

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs6b =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover

Over `R'` (via `σ : C →ₐ[A] R'`) the charts are `Pres (gmap (tsC σ Bᵢ) gCᵢ)` and the overlap is
`Pres (gmap (tsC σ N) (gmap (bcC φ₀ C) gC₀))`.
* `psi0`: `presMap (bcS R' φ₀)` followed by `presCongr`; `psi0_alg`, `psi0_tmul`, `psi0_X`, `psi0_away`.
* `isoN`, `psi1`: `presMap (bcS R' φ₁)`, `presCongr`, then `presIso` of the pushed substitution data;
  `psi1_alg`, `psi1_tmul`, `psi1_X`, `psi1_away`.
* `ctheta0`, `ctheta1`: compatibility of residue maps with `psi0`/`psi1` from values on constants and variables.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section Psi

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S] {R' : Type u} [CommRing R']
  [Algebra A R'] {B₀ B₁ N : Type u} [CommRing B₀] [Algebra A B₀] [CommRing B₁] [Algebra A B₁] [CommRing N]
  [Algebra A N] (φ₀ : B₀ →ₐ[A] N) (φ₁ : B₁ →ₐ[A] N) {C : Subalgebra A S} (σ : C →ₐ[A] R') {r₀ r₁ : ℕ}
  (gC₀ : Fin r₀ → MvPolynomial (Fin r₀) (C ⊗[A] B₀)) (gC₁ : Fin r₁ → MvPolynomial (Fin r₁) (C ⊗[A] B₁))

variable (uC : Fin r₀ → MvPolynomial (Fin r₁) (C ⊗[A] N)) (vC : Fin r₁ → MvPolynomial (Fin r₀) (C ⊗[A] N))
  (H : (∀ j, MvPolynomial.bind₁ uC (gmap (bcC φ₀ C) gC₀ j) ∈ Ideal.span (Set.range (gmap (bcC φ₁ C) gC₁))) ∧
    (∀ i, MvPolynomial.bind₁ vC (gmap (bcC φ₁ C) gC₁ i) ∈ Ideal.span (Set.range (gmap (bcC φ₀ C) gC₀))) ∧
    (∀ i, MvPolynomial.bind₁ uC (vC i) - MvPolynomial.X i ∈ Ideal.span (Set.range (gmap (bcC φ₁ C) gC₁))) ∧
    (∀ j, MvPolynomial.bind₁ vC (uC j) - MvPolynomial.X j ∈ Ideal.span (Set.range (gmap (bcC φ₀ C) gC₀))))

theorem psi1_X (j : Fin r₁) :
    psi1 φ₀ φ₁ σ gC₀ gC₁ uC vC H (Ideal.Quotient.mk _ (MvPolynomial.X j)) =
      Ideal.Quotient.mk _ (MvPolynomial.map (tsC σ N) (vC j)) := by
  unfold psi1
  rw [RingHom.comp_apply, presMap_mk, MvPolynomial.map_X]
  show (isoN φ₀ φ₁ σ gC₀ gC₁ uC vC H) (Ideal.Quotient.mk _ (MvPolynomial.X j)) = _
  rw [isoN, AlgEquiv.trans_apply, presCongr_mk, presIso_mk, MvPolynomial.bind₁_X_right]

theorem psi1_away [Module.Flat A R'] (t : B₁) (h : IsAwayMap (φ₁ : B₁ →+* N) t) :
    IsAwayMap (psi1 φ₀ φ₁ σ gC₀ gC₁ uC vC H)
      (algebraMap (R' ⊗[A] B₁) (Pres (gmap (tsC σ B₁) gC₁)) ((1 : R') ⊗ₜ[A] t)) :=
  presMap_away_equiv (bcS R' φ₁) ((1 : R') ⊗ₜ[A] t) (away_bc (S := R') φ₁ t h) (gmap (tsC σ B₁) gC₁)
    (isoN φ₀ φ₁ σ gC₀ gC₁ uC vC H).toRingEquiv

end Psi

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3Alg =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`

`A = Γ(V)`, `B₀ = Γ(Y, Y₀)`, `B₁ = Γ(Y, Y₁)`, `N = Γ(Y, Y₀ ⊓ Y₁)`:
* `A[X]`-structures `algX0` (via `t`), `algX1` (via `s`), `algXN` (via `t`); `A`-structures `algA0`, `algA1`, `algAN`
  (structure maps of `Y ⟶ V`); towers `tow0`, `tow1`, `towN`; `res_struct`.
* `φY0 : B₀ →ₐ[A[X]] N`, `φY1 : B₁ →ₐ[A] N` (restrictions); `hts_Y`, `hs0_Y`, `hs1_Y`, `hz0_Y`, `hz1_Y`.
* **`exists_etale_idem_Y`**: chart elements idempotent mod `p` and agreeing mod `p` on the overlap come from an
  idempotent of `R' ⊗_A secAlg φY0 φY1` after an etale `R'` with a prime over `p` with the same residue field.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace HomogeneousLocalization
open RamanujanPetersson.EtCompact
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV)

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN

attribute [local instance] tow0 tow1 towN

variable [IsAffine V] [IsFinite π]

/-- **The `π₀` lemma for a finite `Y ⟶ P¹_V`.** -/
theorem exists_etale_idem_Y [IsNoetherianRing Γ(V, ⊤)] (p : Ideal Γ(V, ⊤)) [p.IsPrime]
    (ε₀ : Γ(Y, Yc K gV π 0)) (ε₁ : Γ(Y, Yc K gV π 1))
    (h₀ : ε₀ * ε₀ - ε₀ ∈ p.map (algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 0)))
    (h₁ : ε₁ * ε₁ - ε₁ ∈ p.map (algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 1)))
    (h₀₁ : φY0 K gV π ε₀ - φY1 K gV π ε₁ ∈ p.map (algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1))) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra Γ(V, ⊤) R') (_ : Algebra.Etale Γ(V, ⊤) R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p)
      (hbij : Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)))
      (e' : R' ⊗[Γ(V, ⊤)] Z2.secAlg (φY0 K gV π) (φY1 K gV π)), IsIdempotentElem e' ∧
        Algebra.TensorProduct.lift
          (((Z2.fibreUnit p Γ(Y, Yc K gV π 0) Γ(Y, Yc K gV π 1)).comp
            (AlgEquiv.ofBijective _ hbij).symm.toAlgHom).comp
            (IsScalarTower.toAlgHom Γ(V, ⊤) R' P.ResidueField)) (Z2.fibreMap p (φY0 K gV π) (φY1 K gV π))
            (fun _ _ => Commute.all _ _) e' =
          ((Algebra.TensorProduct.includeRight :
              Γ(Y, Yc K gV π 0) →ₐ[Γ(V, ⊤)] p.ResidueField ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) ε₀,
            (Algebra.TensorProduct.includeRight :
              Γ(Y, Yc K gV π 1) →ₐ[Γ(V, ⊤)] p.ResidueField ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) ε₁) := by
  have : Module.Finite (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) := finite_σY K gV π 0 1 (by decide)
  have : Module.Finite (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) := finite_σY K gV π 1 0 (by decide)
  exact Z2.exists_etale_idem_of_loc p (φY0 K gV π) (φY1 K gV π) (hts_Y K gV π) (hs0_Y K gV π) (hs1_Y K gV π)
    (hz0_Y K gV π) (hz1_Y K gV π) ε₀ ε₁ h₀ h₁ h₀₁

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_CovGl2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`

Chart algebras `E₀`, `E₁`, `E₀₁` over `R' ⊗ Γ(Y₀)`, `R' ⊗ Γ(Y₁)`, `R' ⊗ Γ(Y₀₁)`, glued by localizations `ψ₀`, `ψ₁` (the
data of `CoverLift`), give a relative gluing datum **`glD`** over the chart cover `covV`; its glued scheme maps to
`Y_{V'}` by **`toBase`**, which is finite and etale when `E₀`, `E₁` are.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV)

variable [IsAffine V] [IsFinite π] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R'] {E₀ E₁ E₀₁ : Type u}
  [CommRing E₀] [CommRing E₁] [CommRing E₀₁] [Algebra (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀]
  [Algebra (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁] [Algebra (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁]
  (ψ₀ : E₀ →+* E₀₁) (ψ₁ : E₁ →+* E₀₁)
  (hψ₀ : ∀ (r : R') (b : Γ(Y, Yc K gV π 0)), ψ₀ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀ (r ⊗ₜ b)) =
    algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁ (r ⊗ₜ φY0 K gV π b))
  (hψ₁ : ∀ (r : R') (b : Γ(Y, Yc K gV π 1)), ψ₁ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁ (r ⊗ₜ b)) =
    algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁ (r ⊗ₜ φY1 K gV π b))
  (aw₀ : IsAwayMap ψ₀ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀
    ((1 : R') ⊗ₜ algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X)))
  (aw₁ : IsAwayMap ψ₁ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁
    ((1 : R') ⊗ₜ algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) Polynomial.X)))

include hψ₀ aw₀ in
/-- **The left localization square is a pullback.** -/
theorem pb0 : IsPullback (Spec.map (CommRingCat.ofHom ψ₀))
    (Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁)))
    (Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀))) (a0 K gV π R') :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_loc (φ0V K gV π) _ (away0 K gV π) (unit0 K gV π) ψ₀ hψ₀ aw₀)

section FinEt

end FinEt

section Et

end Et

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFib =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover

For lift data `L : LiftD K gV π x q hx` of a fibre cover `q : T ⟶ Y_x`: the glued cover `dL L` of `Y_{V'}`
(`V' = Spec L.R'`), the lift `xL L` of `x`, and **`ψL L : U_x ⟶ T`** on `U_x = (dL L).glued ×_{Y_{V'}} Y_x`, glued
from the chart lifts `gW` (`g0`, `g1`; `overlap` on `Y₀₁`), with **`ψL_q`**: `ψL L ≫ q = pullback.snd`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algKY algT CoverLift.cR CoverLift.aR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁

universe u

variable {K : Type u} [Field K] {V : Scheme.{u}} {gV : V ⟶ Spec (CommRingCat.of K)} {Y : Scheme.{u}}
  {π : Y ⟶ PV K gV} {x : Spec (CommRingCat.of K) ⟶ V} [IsAffine V] [IsFinite π] {hx : x ≫ gV = 𝟙 _}
  {T : Scheme.{u}} {q : T ⟶ Yx K gV π x} [IsAffineHom q] (L : LiftD K gV π x q hx)

theorem unitL0 : letI := algKV K gV; IsUnit (L.ψ₀ (algebraMap (L.R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) L.E₀
    ((1 : L.R') ⊗ₜ algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X))) := by
  letI := algKV K gV
  rw [L.hψ₀]
  exact ((unit0 K gV π).map (Algebra.TensorProduct.includeRight (R := Γ(V, ⊤)) (A := L.R')
    (B := Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)))).map
    (algebraMap (L.R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) L.E₀₁)

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4FibC =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 13 (G-f, part 3): the `π₀` extension theorem

* `fibLift` (the fibre map of `exists_etale_idem_Y`), `fibLift_fst`, `fibLift_snd`; `chart_eq` (on a chart, the
  pulled-back idempotent is computed in `κ(p) ⊗ Γ(Y, U)`).
* **`exists_clopen_ext`**: `V` affine noetherian over `K`, `π : Y ⟶ P¹_V` finite, `x : Spec K ⟶ V` a `K`-point
  (`x ≫ gV = 𝟙`), `C₀ ⊆ Y_x` clopen. Then there are an etale `Γ(V)`-algebra `R'`, a lift `x' : Spec K ⟶ Spec R'` of
  `x` and a clopen `C ⊆ Y ×_V Spec R'` whose preimage in `Y_x` (under `yxMap`) is `C₀`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algYV

section Chart

end Chart

section Main

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V]

/-- **The `π₀` extension theorem for a finite `Y ⟶ P¹_V`.** A clopen of the fibre over a `K`-point `x` of `V`
extends, after an etale neighbourhood `Spec R' ⟶ V` of `x`, to a clopen of `Y ×_V Spec R'`. -/
theorem exists_clopen_ext [IsFinite π] [IsNoetherianRing Γ(V, ⊤)] (x : Spec (CommRingCat.of K) ⟶ V)
    (hx : x ≫ gV = 𝟙 _) (C₀ : (Yx K gV π x).Opens) (hC₀ : IsClosed (C₀ : Set (Yx K gV π x))) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra Γ(V, ⊤) R') (_ : Algebra.Etale Γ(V, ⊤) R')
      (x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R')) (hx' : x' ≫ hV V R' = x)
      (C : (YV K gV π R').Opens), IsClosed (C : Set (YV K gV π R')) ∧ yxMap K gV π R' x x' hx' ⁻¹ᵁ C = C₀ := by
  obtain ⟨ε, hε, hεC⟩ := exists_idem_basicOpen_eq C₀ hC₀
  have hA0 : algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 0) = (strU K gV π (Yc K gV π 0)).hom :=
    congrArg CommRingCat.Hom.hom (struct_res K gV π 0)
  have hA1 : algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 1) = (strU K gV π (Yc K gV π 1)).hom :=
    congrArg CommRingCat.Hom.hom (struct_res K gV π 1)
  have hA01 : algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) =
      (strU K gV π (Yc K gV π 0 ⊓ Yc K gV π 1)).hom := rfl
  have hker : ∀ (U : Y.Opens), IsAffineOpen U → ∀ b : Γ(Y, U), ((fx K gV π x).app U).hom b = 0 →
      b ∈ (px K x).map (strU K gV π U).hom := by
    intro U hU b hb
    rw [← ker_appTop_eq, ← ker_fx_app K gV π x U hx hU]
    exact hb
  obtain ⟨ε₀, hε₀⟩ := fx_app_surj K gV π x _ hx (isAffineOpen_Yc K gV π 0)
    ((Yx K gV π x).presheaf.map (homOfLE le_top : fx K gV π x ⁻¹ᵁ Yc K gV π 0 ⟶ ⊤).op ε)
  obtain ⟨ε₁, hε₁⟩ := fx_app_surj K gV π x _ hx (isAffineOpen_Yc K gV π 1)
    ((Yx K gV π x).presheaf.map (homOfLE le_top : fx K gV π x ⁻¹ᵁ Yc K gV π 1 ⟶ ⊤).op ε)
  have h₀ : ε₀ * ε₀ - ε₀ ∈ (px K x).map (algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 0)) := by
    rw [hA0]
    apply hker _ (isAffineOpen_Yc K gV π 0)
    rw [map_sub, map_mul, hε₀, ← map_mul, hε.eq, sub_self]
  have h₁ : ε₁ * ε₁ - ε₁ ∈ (px K x).map (algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 1)) := by
    rw [hA1]
    apply hker _ (isAffineOpen_Yc K gV π 1)
    rw [map_sub, map_mul, hε₁, ← map_mul, hε.eq, sub_self]
  have h₀₁ : φY0 K gV π ε₀ - φY1 K gV π ε₁ ∈
      (px K x).map (algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) := by
    rw [hA01]
    apply hker _ (isAffineOpen_Y01 K gV π)
    rw [map_sub, sub_eq_zero]
    change (fx K gV π x).app _
        (Y.presheaf.map (homOfLE inf_le_left : Yc K gV π 0 ⊓ Yc K gV π 1 ⟶ Yc K gV π 0).op ε₀) =
      (fx K gV π x).app _
        (Y.presheaf.map (homOfLE inf_le_right : Yc K gV π 0 ⊓ Yc K gV π 1 ⟶ Yc K gV π 1).op ε₁)
    rw [← pull_res (fx K gV π x) (inf_le_left : Yc K gV π 0 ⊓ Yc K gV π 1 ≤ Yc K gV π 0)
        (Scheme.Hom.preimage_mono _ inf_le_left) ε₀,
      ← pull_res (fx K gV π x) (inf_le_right : Yc K gV π 0 ⊓ Yc K gV π 1 ≤ Yc K gV π 1)
        (Scheme.Hom.preimage_mono _ inf_le_right) ε₁]
    change (Yx K gV π x).presheaf.map _ (((fx K gV π x).app _).hom ε₀) =
      (Yx K gV π x).presheaf.map _ (((fx K gV π x).app _).hom ε₁)
    rw [hε₀, hε₁, map_map, map_map]
  obtain ⟨R', _, _, _, P, _, _, hbij, e', he', hlift⟩ :=
    exists_etale_idem_Y K gV π (px K x) ε₀ ε₁ h₀ h₁ h₀₁
  have key : (yxMap K gV π R' x _ (hxχ K x P hbij)).appTop (PhiY K gV π R' e') = ε := by
    apply eq_of_res_x K gV π x
    · exact (chart_eq K gV π x P hbij (Yc K gV π 0) hA0
        ((RingHom.fst _ _).comp (fibLift K gV π x P hbij).toRingHom) (fibLift_fst K gV π x P hbij) e' ε₀
        ((congrArg Prod.fst hlift).trans (Algebra.TensorProduct.includeRight_apply ε₀))).trans hε₀
    · exact (chart_eq K gV π x P hbij (Yc K gV π 1) hA1
        ((RingHom.snd _ _).comp (fibLift K gV π x P hbij).toRingHom) (fibLift_snd K gV π x P hbij) e' ε₁
        ((congrArg Prod.snd hlift).trans (Algebra.TensorProduct.includeRight_apply ε₁))).trans hε₁
  refine ⟨R', inferInstance, inferInstance, inferInstance, _, hxχ K x P hbij,
    (YV K gV π R').basicOpen (PhiY K gV π R' e'), (isClopen_PhiY K gV π R' he').1, ?_⟩
  rw [Scheme.preimage_basicOpen_top, key, hεC]

end Main

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG5 =====
section

/-!
# S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`

* `sheet_cover`: the sheets `sheetE ν : V ⟶ U0E` cover `U0E` (every prime of `B(U)` comes from a sheet).
* `cU_kL`, `cval_dif_sheet`, `dif_sheet`: if `gi ≫ sheetE i = gj ≫ sheetE j` then `dif gi gj = j - i`
  (pointwise: the pair `(gi, gj)` lands in `Spec (C ⊗ C)` over an affine `U`, and `key_sheet`).
* `exists_sigma`: the sections `e + a(ν)` on the sheets glue to `σ ∈ E(U₀)`; `b_sigma`: `b σ` is the pull-back of `q`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Gen

end Gen

section Pt

end Pt

section Cover

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom] [Surjective V.hom] {Λ : Type u} [CommRing Λ]
  {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M] {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q)
  (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

/-- **The descended section** `σ ∈ E(U₀)`: `e + a(ν)` on the `ν`-th sheet. -/
theorem exists_sigma : ∃! s : E.obj.obj (op (U0E V a b hab hS e he)), ∀ ν : M,
    (E.obj.map (sheetE V a b hab hS e he ν).op).hom s = e + (a.hom.app (op V)).hom ((constUnit M V).hom ν) := by
  refine existsUnique_glue E (sheetE V a b hab hS e he) (sheet_cover V a b hab hS e he)
    (fun ν => e + (a.hom.app (op V)).hom ((constUnit M V).hom ν)) fun i j W gi gj hij => ?_
  have hnat : ∀ (g : W ⟶ V) (n : M), (E.obj.map g.op).hom ((a.hom.app (op V)).hom ((constUnit M V).hom n)) =
      (a.hom.app (op W)).hom ((constUnit M W).hom n) := fun g n => by
    have hn := congrArg (fun φ => φ.hom ((constUnit M V).hom n)) (a.hom.naturality g.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn
    rw [← hn, constUnit_map]
  have hd := f_dif a b hab hS e he W gi gj
  rw [dif_sheet V a b hab hS e he i j gi gj hij, map_sub, map_sub] at hd
  simp only [difX] at hd
  rw [map_add, map_add, hnat, hnat]
  have hx : (E.obj.map gi.op).hom e = (a.hom.app (op W)).hom ((constUnit M W).hom j) -
      (a.hom.app (op W)).hom ((constUnit M W).hom i) + (E.obj.map gj.op).hom e := by
    rw [hd]
    abel
  rw [hx]
  abel

end Cover

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_DescK2 =====
section

/-!
# S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`

For `q : Y_s ⟶ P_s` and a short exact `0 → q_* N → E' → Λ → 0` on `P_s`:
* `Epp` (`E'' = q^* E' ⊔_{q^* q_* N} N`), `aPP`, `bPP`, **`shortExact_Epp`**: `0 → N → E'' → Λ → 0`;
* `kap0`, **`a_kap0`**: a map `τ : E'' ⟶ ψ'_* N_Z` extending `uC` gives `κ₀ : E' ⟶ (ψ' ≫ q)_* N_Z` extending `q_*(uC)`;
* `kapU_eq`, `push_uC_comp`, `rU_congr`: `q_*(uC) = rU`;
* **`T1`**: there is a finite etale surjective `T ⟶ Y_s` such that every `ψ : U_s ⟶ T` over `Y_s` yields `κ₀` with
  `a' ≫ κ₀ = rUs` (the input of `T3d.HypT`, up to the lifting `T2`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescK

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.SgUnit RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.FBC

universe u

section RU

end RU

section Gen

end Gen

section Push

end Push

section T1

variable {Λ : Type u} [CommRing Λ]

/-- **T1**: the torsor of liftings of `1` in `E''` is a finite etale surjective `T ⟶ Y_s`; every map
`ψ : U_s ⟶ T` over `Y_s` kills the extension `E'` after restriction to `U_s`. -/
theorem T1 {P Ps Y : Scheme.{u}} (π : Y ⟶ P) (ι : Ps ⟶ P) (N : ModuleCat.{u} Λ) [Fintype N] [DecidableEq N]
    [CompactSpace (pullback π ι : Scheme.{u})] (hA : ∀ V : (pullback π ι).Etale, IsAffine V.left → IsAffineHom V.hom)
    {E' : EtSh Λ Ps} (a' : (push (pullback.snd π ι) Λ).obj (constSh Λ (pullback π ι) N) ⟶ E')
    (b' : E' ⟶ unitSh Λ Ps) (w' : a' ≫ b' = 0) (hS' : (ShortComplex.mk a' b' w').ShortExact) :
    ∃ T : (pullback π ι).Etale, IsFinite T.hom ∧ Surjective T.hom ∧
      ∀ {P' U : Scheme.{u}} (f : P' ⟶ P) (ι' : Ps ⟶ P') (hι : ι' ≫ f = ι) (Φ : U ⟶ P') (h : U ⟶ Y)
        (hh : h ≫ π = Φ ≫ f) (ψ : pullback Φ ι' ⟶ T.left)
        (_ : ψ ≫ T.hom = T3d.hsU π f Φ h hh ι' ι hι),
        ∃ κ₀ : E' ⟶ (push (pullback.snd Φ ι') Λ).obj (constSh Λ (pullback Φ ι') N),
          a' ≫ κ₀ = T3d.rUs N π f Φ h hh ι' ι hι := by
  have hS := shortExact_Epp (pullback.snd π ι) N a' b' w' hS'
  obtain ⟨V, fV, hVa, hVs, e, he1⟩ := exists_cover_lift hS
    ((constUnit (ModuleCat.of Λ Λ) (etId (pullback π ι))).hom 1)
  haveI : IsAffineHom V.hom := hA V hVa
  have hw : fV.left ≫ (etId (pullback π ι)).hom = V.hom := MorphismProperty.Over.w fV
  haveI : Surjective V.hom := by
    have : Surjective (fV.left ≫ (etId (pullback π ι)).hom) := by
      change Surjective (fV.left ≫ 𝟙 _)
      rw [Category.comp_id]
      exact ⟨hVs⟩
    exact hw ▸ this
  have hn : ∀ (W : (pullback π ι).Etale) (w : W ⟶ V),
      ((bPP (pullback.snd π ι) N a' b' w').hom.app (op W)).hom
        (((Epp (pullback.snd π ι) N a').obj.map w.op).hom e) =
      ((unitSh Λ (pullback π ι)).obj.map (w ≫ fV).op).hom
        ((constUnit (ModuleCat.of Λ Λ) (etId (pullback π ι))).hom 1) := fun W w => by
    have h1 := congrArg (fun φ => φ.hom e) ((bPP (pullback.snd π ι) N a' b' w').hom.naturality w.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    exact h1.trans ((congrArg ((unitSh Λ (pullback π ι)).obj.map w.op).hom he1).trans (map_map_apply _ _ _ _))
  have he : ∀ (W : (pullback π ι).Etale) (w₁ w₂ : W ⟶ V),
      ((bPP (pullback.snd π ι) N a' b' w').hom.app (op W)).hom
        (((Epp (pullback.snd π ι) N a').obj.map w₁.op).hom e) =
      ((bPP (pullback.snd π ι) N a' b' w').hom.app (op W)).hom
        (((Epp (pullback.snd π ι) N a').obj.map w₂.op).hom e) := fun W w₁ w₂ => by
    rw [hn W w₁, hn W w₂, (PtSec.etId_isTerminal _).hom_ext (w₁ ≫ fV) (w₂ ≫ fV)]
  have hq : ((bPP (pullback.snd π ι) N a' b' w').hom.app (op V)).hom e =
      ((unitSh Λ (pullback π ι)).obj.map ((PtSec.etId_isTerminal _).from V).op).hom
        ((constUnit (ModuleCat.of Λ Λ) (etId (pullback π ι))).hom 1) := by
    rw [he1, (PtSec.etId_isTerminal _).hom_ext fV ((PtSec.etId_isTerminal _).from V)]
  obtain ⟨σ, hσ1, -⟩ := DescG.exists_sigma V (aPP (pullback.snd π ι) N a') (bPP (pullback.snd π ι) N a' b' w')
    (aPP_bPP (pullback.snd π ι) N a' b' w') hS e he
  have hσ : ((bPP (pullback.snd π ι) N a' b' w').hom.app
      (op (DescG.U0E V (aPP (pullback.snd π ι) N a') (bPP (pullback.snd π ι) N a' b' w')
        (aPP_bPP (pullback.snd π ι) N a' b' w') hS e he))).hom σ =
      (constUnit (ModuleCat.of Λ Λ) (DescG.U0E V (aPP (pullback.snd π ι) N a') (bPP (pullback.snd π ι) N a' b' w')
        (aPP_bPP (pullback.snd π ι) N a' b' w') hS e he)).hom 1 :=
    (DescG.b_sigma V (aPP (pullback.snd π ι) N a') (bPP (pullback.snd π ι) N a' b' w')
      (aPP_bPP (pullback.snd π ι) N a' b' w') hS e he σ hσ1 _ hq).trans (DescG.constUnit_map _ _)
  refine ⟨DescG.U0E V (aPP (pullback.snd π ι) N a') (bPP (pullback.snd π ι) N a' b' w')
      (aPP_bPP (pullback.snd π ι) N a' b' w') hS e he,
    inferInstanceAs (IsFinite (DescG.toU0 V (aPP (pullback.snd π ι) N a') (bPP (pullback.snd π ι) N a' b' w')
      (aPP_bPP (pullback.snd π ι) N a' b' w') hS e he)),
    inferInstanceAs (Surjective (DescG.toU0 V (aPP (pullback.snd π ι) N a') (bPP (pullback.snd π ι) N a' b' w')
      (aPP_bPP (pullback.snd π ι) N a' b' w') hS e he)), ?_⟩
  intro P' U f ι' hι Φ h hh ψ hψ
  have h₀ : (ψ ≫ (DescG.U0E V (aPP (pullback.snd π ι) N a') (bPP (pullback.snd π ι) N a' b' w')
      (aPP_bPP (pullback.snd π ι) N a' b' w') hS e he).hom) ≫ pullback.snd π ι = pullback.snd Φ ι' :=
    (congrArg (· ≫ pullback.snd π ι) hψ).trans (T3d.hsU_snd π f Φ h hh ι' ι hι)
  refine ⟨kap0 (pullback.snd π ι) N a' _ (tau (aPP (pullback.snd π ι) N a') (bPP (pullback.snd π ι) N a' b' w')
      (aPP_bPP (pullback.snd π ι) N a' b' w') hS σ hσ ψ) ≫ eqToHom (push_obj_eq_of_eq h₀ _), ?_⟩
  exact (Category.assoc _ _ _).symm.trans ((eq_whisker (a_kap0 (pullback.snd π ι) N a' _ _
    (a_tau (aPP (pullback.snd π ι) N a') (bPP (pullback.snd π ι) N a' b' w')
      (aPP_bPP (pullback.snd π ι) N a' b' w') hS σ hσ ψ)) _).trans
    ((eq_whisker (push_uC_comp _ _) _).trans (rU_congr _ hψ h₀ (T3d.hsU_snd π f Φ h hh ι' ι hι))))

end T1

end RamanujanPetersson.EtPBC.DescK

end

end

-- ===== S4.Def_RP_EtPBC_A_T2I =====
section

/-!
# S4-EtPBC-A, R4-T2 interface: `HypT` from T1 and the lifting statement `LiftT`

* **`LiftT g s π`** (the remaining input, pure geometry): every finite etale surjective `T ⟶ Y_s` is dominated, over
  `Y_s`, by the fibre `U_s` of a finite `U ⟶ P'` over an etale neighbourhood `P' ⟶ P` of the fibre, with `U`
  covering `P' ×_P Y`.
* **`hypT_of_liftT`**: `T1` turns `LiftT` into `T3d.HypT` (given compactness of `Y_s` and affineness of etale maps
  from affine schemes to `Y_s`); `hypT_of_liftT'` discharges both for `g` separated, `fib g s` compact, `π` finite.
* **`bcSurj_one_push_of_liftT`**: degree-one base change for `π_* N_Y` from degree zero and `LiftT`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.T2

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **T1 + T2 ⇒ `HypT`.** -/
theorem hypT_of_liftT {Y : Scheme.{u}} (π : Y ⟶ P) (N : ModuleCat.{u} Λ) [Finite N]
    [CompactSpace (pullback π (fibι g s) : Scheme.{u})]
    (hA : ∀ V : (pullback π (fibι g s)).Etale, IsAffine V.left → IsAffineHom V.hom)
    (hL : LiftT g s π) : T3d.HypT Λ g s π N := by
  intro E' a' b' w' hS'
  letI : Fintype N := Fintype.ofFinite N
  classical
  obtain ⟨T, hTf, hTs, hT⟩ := DescK.T1 π (fibι g s) N hA a' b' w' hS'
  obtain ⟨P', U, f, hf, ι', hι, hcl, Φ, hΦ, h, hh, hsurj, ψ, hψ⟩ := hL T hTf hTs
  obtain ⟨κ₀, hκ⟩ := hT f ι' hι Φ h hh ψ hψ
  exact ⟨P', U, f, hf, ι', hι, hcl, Φ, hΦ, h, hh, hsurj, κ₀, hκ⟩

/-- `hypT_of_liftT` for `g` separated, `fib g s` compact and `π` finite. -/
theorem hypT_of_liftT' [IsSeparated g] [CompactSpace (fib g s)] {Y : Scheme.{u}} (π : Y ⟶ P) [IsFinite π]
    (N : ModuleCat.{u} Λ) [Finite N] (hL : LiftT g s π) : T3d.HypT Λ g s π N :=
  haveI := compactSpace_fibY g s π
  hypT_of_liftT g s π N (isAffineHom_to_fibY g s π) hL

end RamanujanPetersson.EtPBC.T2

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel2 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2R3a): the target term of the relation lies in `G`

REL PLAN v2 (s126), file R3, generic part. In the setting of `relation_sum` (O2R4):
* **`term_mem_of_rest`**: if every term `k ≠ k₀` lies in an additive subgroup `G`, so does the term `k₀`;
* **`term_mem_of_good`**: the same when every term `k ≠ k₀` is at a good point (one-point classes there lie in `G`) or
  is `0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  (S : ι → P.Etale) (U₀ : P.Opens)
  (z : ι → P) (hzi : Function.Injective z) (hU : ∀ x : P, x ∈ U₀ ↔ ∀ k, x ≠ z k)
  (hD : ∀ k, Subsingleton ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDn : ∀ k, Nonempty ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDr : ∀ k (v : (S k).left), (S k).hom v ∈ U₀ ∨ (S k).hom v = z k)
  (Uz : ι → P.Opens) (hz : ∀ k (x : P), x ∈ Uz k ↔ x ≠ z k)

include hzi hU hD hDn hDr hz in
/-- **The term `k₀` lies in `G` when every other term is at a good point or is `0`.** -/
theorem term_mem_of_good {F : EtSh Λ P} (G : AddSubgroup (Ext.{u} (freeSh Λ (etId P)) F 2)) (good : P → Prop)
    (hG : ∀ x, good x → ∀ β, IsLoc Λ F x β → β ∈ G)
    (κ : Ext.{u} (freeSh Λ (opEt U₀)) F 1) (k₀ : ι)
    (hk : ∀ k, k ≠ k₀ → good (z k) ∨ (locC_shortExact (Λ := Λ) (S k) (locLe U₀ z hU Uz hz k) (z k) (hz k) (hD k)
      (hDn k) (hDr k)).extClass.comp ((Ext.mk₀ (freeMap Λ (prT (S k) (opEt U₀)))).comp κ (zero_add 1))
        (show 1 + 1 = 2 from rfl) = 0) :
    (locC_shortExact (Λ := Λ) (S k₀) (locLe U₀ z hU Uz hz k₀) (z k₀) (hz k₀) (hD k₀) (hDn k₀)
      (hDr k₀)).extClass.comp ((Ext.mk₀ (freeMap Λ (prT (S k₀) (opEt U₀)))).comp κ (zero_add 1))
        (show 1 + 1 = 2 from rfl) ∈ G := by
  refine term_mem_of_rest S U₀ z hzi hU hD hDn hDr Uz hz G κ k₀ fun k hk' => ?_
  rcases hk k hk' with hg | h0
  · exact hG _ hg _ (isLoc_relation_term S U₀ z hzi hU hD hDn hDr Uz hz κ k)
  · rw [h0]
    exact zero_mem G

end RamanujanPetersson.EtPBC.EtMV

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

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) (x : Spec (CommRingCat.of K) ⟶ V)

attribute [local instance] algKY

variable {T : Scheme.{u}} (q : T ⟶ Yx K gV π x)

attribute [local instance] algT

/-- **`CoverLiftAt₂` at `x` gives the lift data of every finite etale cover of `Y_x`.** -/
theorem nonempty_liftD₂ [IsAffine V] [IsFinite π] (hx : x ≫ gV = 𝟙 _) [IsFinite q] [Etale q]
    (hL : @CoverLiftAt₂ K _ Γ(V, ⊤) _ (algKV K gV) (χV K gV x hx)) : Nonempty (LiftD K gV π x q hx) := by
  letI := algKV K gV
  have : Module.Finite (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) := finite_σY K gV π 0 1 (by decide)
  have : Module.Finite (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) := finite_σY K gV π 1 0 (by decide)
  have hW0 := isAffineOpen_Wx K gV π x _ (isAffineOpen_Yc K gV π 0)
  have hW1 := isAffineOpen_Wx K gV π x _ (isAffineOpen_Yc K gV π 1)
  have hb0 : ∀ a : Γ(V, ⊤), ((fx K gV π x).app (Yc K gV π 0)).hom (algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 0) a) =
      algebraMap K _ (χV K gV x hx a) := fun a => by
    rw [show algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 0) a = (strU K gV π (Yc K gV π 0)).hom a from
      congrArg (fun φ => CommRingCat.Hom.hom φ a) (struct_res K gV π 0)]
    exact beta_alg K gV π x _ a
  have hb1 : ∀ a : Γ(V, ⊤), ((fx K gV π x).app (Yc K gV π 1)).hom (algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 1) a) =
      algebraMap K _ (χV K gV x hx a) := fun a => by
    rw [show algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 1) a = (strU K gV π (Yc K gV π 1)).hom a from
      congrArg (fun φ => CommRingCat.Hom.hom φ a) (struct_res K gV π 1)]
    exact beta_alg K gV π x _ a
  have hb01 : ∀ a : Γ(V, ⊤), ((fx K gV π x).app (Yc K gV π 0 ⊓ Yc K gV π 1)).hom
      (algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) a) = algebraMap K _ (χV K gV x hx a) :=
    fun a => beta_alg K gV π x _ a
  have hk0 := ker_beta K gV π x hx (Yc K gV π 0) (isAffineOpen_Yc K gV π 0) (algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 0))
    (congrArg CommRingCat.Hom.hom (struct_res K gV π 0))
  have hk1 := ker_beta K gV π x hx (Yc K gV π 1) (isAffineOpen_Yc K gV π 1) (algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 1))
    (congrArg CommRingCat.Hom.hom (struct_res K gV π 1))
  have hk01 := ker_beta K gV π x hx (Yc K gV π 0 ⊓ Yc K gV π 1) (isAffineOpen_Y01 K gV π)
    (algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) (RingHom.ext fun _ => rfl)
  exact hL Γ(Y, Yc K gV π 0) Γ(Y, Yc K gV π 1) Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) (φY0 K gV π) (φY1 K gV π) (hts_Y K gV π) (hs0_Y K gV π) (hs1_Y K gV π) (hz0_Y K gV π) (hz1_Y K gV π)
      Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ Yc K gV π 0) Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ Yc K gV π 1)
      Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1)) ((fx K gV π x).app (Yc K gV π 0)).hom ((fx K gV π x).app (Yc K gV π 1)).hom
      ((fx K gV π x).app (Yc K gV π 0 ⊓ Yc K gV π 1)).hom hb0 hb1 hb01
      (fx_app_surj K gV π x _ hx (isAffineOpen_Yc K gV π 0)) (fx_app_surj K gV π x _ hx (isAffineOpen_Yc K gV π 1))
      (fx_app_surj K gV π x _ hx (isAffineOpen_Y01 K gV π)) hk0 hk1 hk01 (ρx0 K gV π x) (ρx1 K gV π x)
      (hρ0 K gV π x) (hρ1 K gV π x) Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ Yc K gV π 0))
      Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ Yc K gV π 1)) Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1)))
      (etale_T K gV π x q hW0) (etale_T K gV π x q hW1) (finite_T K gV π x q hW0) (finite_T K gV π x q hW1)
      (ψT0 K gV π x q) (ψT1 K gV π x q) (hψT0 K gV π x q) (hψT1 K gV π x q) (away_T0 K gV π x q) (away_T1 K gV π x q)

end Cover

end RamanujanPetersson.EtPBC.Cov

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.Cov

universe u

section Main

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algKY algT CoverLift.cR CoverLift.aR CoverLift.eR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁ CoverLift.f₀ CoverLift.f₁ CoverLift.et₀ CoverLift.et₁

end Main

end RamanujanPetersson.EtPBC

end

end


