-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_016
-- name    : RPLib_FX_EtPBC_016
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T18:42:02.83799+00:00
-- url     : https://prove2.me/theorems/d1fe32d2-3034-5923-9b69-4e5eae5c12c7
-- title:
--   Proper base change for the projective line, library file 016
-- statement:
--   File 016 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovFil1`: S4-EtPBC-A, R4-T2 (A2c-1d): overlap relations with entries in `p^j` split into chart relations
--   * `S4.Def_RP_EtPBC_A_CovGlob`: S4-EtPBC-A, R4-T2 (A2c-5a): closed loci on `P¹` that miss the closed fibre are empty
--   * `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
--   * `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
--   * `S4.Def_RP_EtPBC_A_O2N1c`: S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)
--   * `S4.Def_RP_EtPBC_A_O2P3a`: S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps
--   * `S4.Def_RP_EtPBC_A_O2E5`: S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)
--   * `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2Gl1c`: S4-EtPBC-A, O2 GLOB (O2Gl1c): the geometric inputs of stages S1-S2
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_007
import Definitions.Def_RPLib_FX_EtPBC_008
import Definitions.Def_RPLib_FX_EtPBC_009
import Definitions.Def_RPLib_FX_EtPBC_010
import Definitions.Def_RPLib_FX_EtPBC_011

/-!
# Proper base change for the projective line, library file 016

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovFil1`: S4-EtPBC-A, R4-T2 (A2c-1d): overlap relations with entries in `p^j` split into chart relations
* `S4.Def_RP_EtPBC_A_CovGlob`: S4-EtPBC-A, R4-T2 (A2c-5a): closed loci on `P¹` that miss the closed fibre are empty
* `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
* `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
* `S4.Def_RP_EtPBC_A_O2N1c`: S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)
* `S4.Def_RP_EtPBC_A_O2P3a`: S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps
* `S4.Def_RP_EtPBC_A_O2E5`: S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)
* `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
* `S4.Def_RP_EtPBC_A_O2Gl1c`: S4-EtPBC-A, O2 GLOB (O2Gl1c): the geometric inputs of stages S1-S2
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_CovFil1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-1d): overlap relations with entries in `p^j` split into chart relations

For a level-`k` cover `C` (charts `Bᵢ ⧸ Jᵢ^(k+1)`, `Jᵢ = p Bᵢ`):
* `decomp_succ`: an element of `p^(j+1) B` is `∑ αᵢ yᵢ` with `yᵢ ∈ p^j B`;
* `lψθ₀`, `lψθ₁`, `mem_lι₀`, `mem_lι₁`: bookkeeping for the level-`k` charts;
* `chart0_decomp`: a chart-0 relation with entries in `p^j` is `∑ cₗ ρ0ₗ + v` (base relations, flatness);
* `split_rel`: such a decomposition splits on the two charts (uniform `H¹` vanishing);
* **`lift_rel`**: an overlap relation `w` with entries in `p^j` is `ψ₀ a - u^d ψ₁ b` with `a`, `b` chart relations
  with entries in `p^j`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lv

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁) (p : Ideal R)

/-- **A chart-0 relation with entries in `p^j`** is `∑ cₗ ρ0ₗ + v` with `cₗ ∈ p^(j-n')`, `v ∈ p^k`. -/
theorem chart0_decomp [IsNoetherianRing R] {g : ℕ} (α : Fin g → R) (hα : p = Ideal.span (Set.range α))
    (hJ₀ : J₀ = p.map ιB₀) {k : ℕ} (C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k) {j : ℕ} (hj : j ≤ k) {n' L : ℕ}
    (ρ0 : Fin L → Fin g → B₀)
    (hgen : ∀ w ∈ RelV p α ιB₀ j, ∃ β : Fin L → B₀, (∀ l, β l ∈ (p ^ (j - n')).map ιB₀) ∧
      w = ∑ l, β l • ρ0 l)
    (w' : Fin g → C.E₀) (hw' : ∀ i, w' i ∈ (p ^ j).map (lι₀ ιB₀ C))
    (hμ : ∑ i, lι₀ ιB₀ C (α i) * w' i = 0) :
    ∃ (c : Fin L → C.E₀) (v : Fin g → C.E₀), (∀ l, c l ∈ (p ^ (j - n')).map (lι₀ ιB₀ C)) ∧
      (∀ i, v i ∈ (p ^ k).map (lι₀ ιB₀ C)) ∧
      ∀ i, w' i = ∑ l, c l * C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i)) + v i := by
  letI := C.a₀.toAlgebra
  haveI : Module.Flat (B₀ ⧸ J₀ ^ (k + 1)) C.E₀ :=
    RingHom.flat_algebraMap_iff.1 (RingHom.Etale.iff_flat_and_formallyUnramified.1 C.et₀).1
  have hk0 : RingHom.ker (Ideal.Quotient.mk (J₀ ^ (k + 1))) = (p.map ιB₀) ^ (k + 1) := by
    rw [Ideal.mk_ker, hJ₀]
  have e : ((algebraMap (B₀ ⧸ J₀ ^ (k + 1)) C.E₀).comp (Ideal.Quotient.mk (J₀ ^ (k + 1)))).comp ιB₀ =
      lι₀ ιB₀ C := RingHom.ext fun _ => rfl
  obtain ⟨K, y, r, v, hr, hv, hwr⟩ := flat_rel p α ιB₀ hα (Ideal.Quotient.mk (J₀ ^ (k + 1)))
    Ideal.Quotient.mk_surjective k hk0 j hj w' (by rw [e]; exact hw')
    (by simpa only [← e, RingHom.comp_apply] using hμ)
  rw [e] at hv
  choose β hβ hβr using fun κ => hgen (r κ) (hr κ)
  obtain ⟨c, hc⟩ : ∃ c : Fin L → C.E₀, ∀ l, c l =
      ∑ κ, y κ * C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (β κ l)) := ⟨_, fun _ => rfl⟩
  refine ⟨c, v, fun l => ?_, hv, fun i => ?_⟩
  · rw [hc]
    exact Ideal.sum_mem _ fun κ _ => Ideal.mul_mem_left _ _ (mem_lι₀ ιB₀ p C (hβ κ l))
  · have hwi : w' i = ∑ κ, y κ * C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (r κ i)) + v i := hwr i
    rw [hwi]
    congr 1
    simp only [hc, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [hβr κ]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

end Lv

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovGlob =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5a): closed loci on `P¹` that miss the closed fibre are empty

* `nak_poly`: if `B` is finite over `R[X]` (via `X ↦ t`) and `K + m B = ⊤`, then every ring map `g : B → S` killing
  `K` sends some polynomial `P(t)` with coefficients in `m` to `1` (Nakayama over `R[X]`);
* **`glob`**: for two charts `B₀`, `B₁` finite over `R[X]` (via `t₀`, `t₁`) glued along `N = B₀[1/t₀]`,
  `t₀ t₁ = 1` in `N`, `m ≤ jacobson ⊥`, and ideals `K₀`, `K₁` with `Kᵢ + m Bᵢ = ⊤` whose zero loci are compatible on the
  overlap, `K₀ = ⊤` (Atiyah-Macdonald 5.21 via `not_top_and_top`).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Glob

variable {R : Type u} [CommRing R]

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N]

/-- **Closed loci on the two-chart `P¹` that miss the closed fibre are empty.** -/
theorem glob (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁) (φ₀ : B₀ →+* N) (φ₁ : B₁ →+* N) (t₀ : B₀) (t₁ : B₁)
    (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀)) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁)
    (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (m : Ideal R)
    (hm : m ≤ Ideal.jacobson ⊥) (K₀ : Ideal B₀) (K₁ : Ideal B₁) (h₀ : K₀ ⊔ m.map ιB₀ = ⊤)
    (h₁ : K₁ ⊔ m.map ιB₁ = ⊤) (hc : ∀ Q : Ideal N, Q.IsPrime → K₀ ≤ Q.comap φ₀ → K₁ ≤ Q.comap φ₁) :
    K₀ = ⊤ := by
  by_contra hne
  obtain ⟨𝔪, h𝔪, hK𝔪⟩ := Ideal.exists_le_maximal K₀ hne
  by_cases ht : t₀ ∈ 𝔪
  · haveI : Nontrivial (B₀ ⧸ 𝔪) := Ideal.Quotient.nontrivial_iff.2 h𝔪.ne_top
    obtain ⟨P, hPm, hP⟩ := nak_poly ιB₀ t₀ hB₀ m K₀ h₀ (Ideal.Quotient.mk 𝔪) (by rwa [Ideal.mk_ker])
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ht, eval₂_at_zero, RingHom.comp_apply] at hP
    have hu : IsUnit (ιB₀ (P.coeff 0 * -1 + 1)) := (Ideal.mem_jacobson_bot.1 (hm (hPm 0)) (-1)).map ιB₀
    have h0 : Ideal.Quotient.mk 𝔪 (ιB₀ (P.coeff 0 * -1 + 1)) = 0 := by
      simp only [map_add, map_mul, map_neg, map_one, hP]
      ring
    exact (hu.map (Ideal.Quotient.mk 𝔪)).ne_zero h0
  · haveI : 𝔪.IsPrime := h𝔪.isPrime
    letI := φ₀.toAlgebra
    haveI := isLocalization_of_isAwayMap φ₀ t₀ hφ₀ hu₀
    have hdisj : Disjoint (Submonoid.powers t₀ : Set B₀) ↑𝔪 :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime t₀).2 ht
    have hQ : (𝔪.map φ₀).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (M := Submonoid.powers t₀) (S := N) 𝔪 h𝔪.isPrime hdisj
    have hQc : (𝔪.map φ₀).comap φ₀ = 𝔪 :=
      IsLocalization.under_map_of_isPrime_disjoint (M := Submonoid.powers t₀) (S := N) h𝔪.isPrime hdisj
    have hK₀ : K₀ ≤ (𝔪.map φ₀).comap φ₀ := by rw [hQc]; exact hK𝔪
    have hK₁ := hc _ hQ hK₀
    haveI : Nontrivial (N ⧸ 𝔪.map φ₀) := Ideal.Quotient.nontrivial_iff.2 hQ.ne_top
    obtain ⟨P, hPm, hP⟩ := nak_poly ιB₀ t₀ hB₀ m K₀ h₀ ((Ideal.Quotient.mk (𝔪.map φ₀)).comp φ₀)
      (fun x hx => RingHom.mem_ker.2 (Ideal.Quotient.eq_zero_iff_mem.2 (hK₀ hx)))
    obtain ⟨P', hPm', hP'⟩ := nak_poly ιB₁ t₁ hB₁ m K₁ h₁ ((Ideal.Quotient.mk (𝔪.map φ₀)).comp φ₁)
      (fun x hx => RingHom.mem_ker.2 (Ideal.Quotient.eq_zero_iff_mem.2 (hK₁ hx)))
    have hι : ((Ideal.Quotient.mk (𝔪.map φ₀)).comp φ₁).comp ιB₁ =
        ((Ideal.Quotient.mk (𝔪.map φ₀)).comp φ₀).comp ιB₀ := by
      rw [RingHom.comp_assoc, RingHom.comp_assoc, hιB]
    rw [hι] at hP'
    refine not_top_and_top (((Ideal.Quotient.mk (𝔪.map φ₀)).comp φ₀).comp ιB₀) m hm
      ((Ideal.Quotient.mk (𝔪.map φ₀)).comp φ₀ t₀) ((Ideal.Quotient.mk (𝔪.map φ₀)).comp φ₁ t₁) ?_ P P' hPm hPm'
      hP hP'
    rw [RingHom.comp_apply, RingHom.comp_apply, ← map_mul, hts, map_one]

end Glob

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_LshEt =====
section

/-!
# S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`

For an etale `e : U ⟶ X`, a geometric point `x` of `X` and a module `J`, the restriction
`res e (x_* J)` of the skyscraper sheaf is assembled from the skyscraper sheaves `l_* J` at the
lifts `l` of `x` along `e` (`pr`, `assemble`, `assemble_pr`, `hom_ext_pr`). Hence:
* `injective_res_sky`: `res e (x_* J)` is injective for `J` injective;
* `res e` preserves injective objects (every injective is a retract of its god sheaf);
* **`lsh e Λ = e_!` preserves monomorphisms** (Mathlib's
  `preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite
open RamanujanPetersson.EtCompact

noncomputable section

namespace RamanujanPetersson.EtSheaves.LshEt

universe u

variable {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] (x : GeomPt X)

/-- `b` as a `U`-map from its lift. -/
def dec {W : U.Etale} (b : x.point.fiber.obj ((etComp e).obj W)) :
    (liftPt e x (liftOf e x b)).point.fiber.obj W :=
  (Over.homMk (fl x b) rfl : Over.mk (liftOf e x b).1 ⟶ (Scheme.Etale.forget U).obj W)

end RamanujanPetersson.EtSheaves.LshEt

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N1a =====
section

/-!
# S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`

For an etale `g : U ⟶ X` and `y : U` (generalizing `GalTr`, which treats open immersions):
* `eE g y`: the geometric points `ȳ ≫ g` and `(g y)‾` are isomorphic (`κ(y)/κ(g y)` is finite separable, so
  `κ(y)^sep` is a separable closure of `κ(g y)`); `sepE g y : κ(g y)^sep ≃ κ(y)^sep`;
* `galTrE g y : Gal y →* Gal (g y)` (conjugation by `sepE`, `galTrE_left`);
* `resTrIsoE g y Λ F : (g^* F)_ȳ ≅ F_(g y)‾`, natural (`resTrIsoE_natural`) and **Galois equivariant**
  (`galRep_resTrE`: `galRep (g^* F) y σ` corresponds to `galRep F (g y) (galTrE σ)`);
* `unitRes g Λ : Λ_U ⟶ g^* Λ_X` (the section `1` goes to the restriction of `1`), `resTrIsoE_unitRes`
  (`1 ↦ 1` on stalks), **`isIso_unitRes`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTr
  RamanujanPetersson.EtCompact.GGerm RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) (y : U)

variable [Etale g]

variable (Λ : Type u) [CommRing Λ]

/-- **Galois equivariance of `resTrIsoE`**. -/
theorem stalkAut_resTrE (F : EtSh Λ X) (σ : Gal y) :
    ((geomPtAt y).stalkAut Λ (galSpec y σ) (galSpec_comp y σ)).app ((res g Λ).obj F) ≫
        (resTrIsoE g y Λ F).hom =
      (resTrIsoE g y Λ F).hom ≫
        ((geomPtAt (g y)).stalkAut Λ (galSpec (g y) (galTrE g y σ)) (galSpec_comp (g y) _)).app F := by
  have hτs : ((eE g y).hom.left ≫ galSpec (g y) (galTrE g y σ) ≫ (eE g y).inv.left) ≫ ((geomPtAt y).map g).pt =
      ((geomPtAt y).map g).pt := by
    rw [galTrE_left]
    exact map_aut g (geomPtAt y) (galSpec_comp y _)
  have hP := stalkAut_ptIso Λ (eE g y) (galSpec (g y) (galTrE g y σ)) (galSpec_comp (g y) _) hτs
  have hP' : (ptIsoSheafFiber Λ (GPtIso.ptIso (eE g y))).inv ≫
      (geomPtAt (g y)).stalkAut Λ (galSpec (g y) (galTrE g y σ)) (galSpec_comp (g y) _) =
      ((geomPtAt y).map g).stalkAut Λ _ hτs ≫ (ptIsoSheafFiber Λ (GPtIso.ptIso (eE g y))).inv := by
    erw [Iso.inv_comp_eq, ← Category.assoc, ← hP, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hA := resFib_stalkAut g (geomPtAt y) Λ (galSpec_comp y σ) F
  have hC := stalkAut_congr Λ ((geomPtAt y).map g) (map_aut g (geomPtAt y) (galSpec_comp y σ)) hτs
    (galTrE_left g y σ).symm
  rw [resTrIsoE_hom]
  erw [← Category.assoc, hA, hC, Category.assoc, ← NatTrans.comp_app, ← hP', NatTrans.comp_app, Category.assoc]
  rfl

theorem galRep_resTrE (F : EtSh Λ X) (σ : Gal y) (v : stalk Λ ((res g Λ).obj F) y) :
    (resTrIsoE g y Λ F).hom.hom (galRep Λ ((res g Λ).obj F) y σ v) =
      galRep Λ F (g y) (galTrE g y σ) ((resTrIsoE g y Λ F).hom.hom v) :=
  congrArg (fun φ => ModuleCat.Hom.hom φ v) (stalkAut_resTrE g y Λ F σ)

/-- `resTrIsoE` on germs of restricted global sections. -/
theorem resTrIsoE_gg (F : EtSh Λ X) (z : F.obj.obj (op (etId X))) :
    (resTrIsoE g y Λ F).hom.hom (gg (geomPtAt y) ((res g Λ).obj F)
      ((F.obj.map (toTop ((etComp g).obj (etId U))).op).hom z)) = gg (geomPtAt (g y)) F z := by
  rw [resTrIsoE_hom]
  exact (congrArg ((ptIsoSheafFiber Λ (GPtIso.ptIso (eE g y))).inv.app F).hom
    (resFib_gg g (geomPtAt y) F _ z)).trans (sheafFiber_gg _ F z)

/-! ### `Λ_U ⟶ g^* Λ_X` -/

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N1c =====
section

/-!
# S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)

* `trIso g h Λ F : (g^* F)_ȳ ≅ F_x̄` and `galTrX g h : Gal y → Gal x` for `h : g y = x` (`resTrIsoE`, `galTrE`
  transported along `h`), `galRep_trIso`, `trIso_natural`, `trIso_hom_injective`, `trIso_inv_natural`,
  `trIso_unitRes`, `isoHomInv`, `isoInvHom`;
* **`resHE_kappa`** (NAT): for `g : Spec A' ⟶ Spec A` etale between noetherian integrally closed domains with
  `g η' = η`, `resHE g (κ_A c) = κ_{A'} c'` whenever `trIso (c' (σ|)) = c ((galTrX σ)|)` for all `σ ∈ Gal(η')`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec

universe u

section Pt

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {y : U} {x : X} (h : g y = x) (Λ : Type u) [CommRing Λ]

theorem galRep_trIso (F : EtSh Λ X) (σ : Gal y) (v : stalk Λ ((res g Λ).obj F) y) :
    (trIso g h Λ F).hom.hom (galRep Λ ((res g Λ).obj F) y σ v) =
      galRep Λ F x (galTrX g h σ) ((trIso g h Λ F).hom.hom v) := by
  subst h
  exact galRep_resTrE g y Λ F σ v

end Pt

section Kappa

end Kappa

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2P3a =====
section

/-!
# S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps

* `ChL A K Λ`: the additive group of additive locally constant characters `π₁(A) → Λ`; `mem_ChL`, `chl_cyc`;
* `zetaE_prim`, `zetaE_fix`: a primitive root `ζ₀ ∈ K` in `maxUnram A K`;
* `kumTau hζ hζΓ hτ hΛ : Λ →+ ChL`, `c ↦ kumChi ζ τ c`;
* **`kappaLH A K Λ : ChL A K Λ →+ H¹(Spec A, Λ)`** (`kappaL`, additive by `kappa_add`), **`kappaLH_surj`**;
* `resLEHom g n : H^n(X, Λ) →+ H^n(U, Λ)` (`resLE` is additive).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer RamanujanPetersson.EtPi1
  RamanujanPetersson.EtCompact.GalTrE

section ChL

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (Λ : Type) [AddCommGroup Λ]

variable {A K Λ}

variable {N : ℕ} [NeZero N] {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 A K)), σ ζ = ζ) {τ : (maxUnram A K)ˣ}
  (hτ : τ ∈ rad (⊤ : Subgroup (Pi1 A K)) N) (hΛ : ∀ x : Λ, N • x = 0)

theorem kumTau_apply (c : Λ) : (kumTau hζ hζΓ hτ hΛ c : Pi1 A K → Λ) = kumChi hζ τ c := rfl

end ChL

section KappaLH

end KappaLH

section ResH

universe u

end ResH

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E5 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)

* generic: **`mapExact_comp_iso`**: for exact `Φ`, `Ψ`, `Φ'` and `τ : Φ ⋙ Ψ ≅ Φ'`, `Ψ(Φ ξ) ∘ τ_B = τ_A ∘ Φ' ξ`
  on `Ext¹` (enough injectives);
* for `m : W' ⟶ W` in `P.Etale`: `Etale m.left`, `etCompCompIso m`, `resCompIso Λ m : res W ⋙ res m ≅ res W'`;
* `diagSec Λ W : Λ_W ⟶ Λ[W]|_W` with `extFree_eq` (`extFree β = diagSec ∘ β|_W`) and `diagSec_sec`;
* **`diagSec_natural`**: `diagSec W' ≫ Λ[m]|_W' = unitRes m.left ≫ (diagSec W)|_W' ≫ (resCompIso m)_{Λ[W]}`.
`extFree_natural` is in O2E5b.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

section Gen

universe w v₁ u₁ v₂ u₂ v₃ u₃

end Gen

section Nat

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {W W' : P.Etale} (m : W' ⟶ W)

theorem etCompTop_comp :
    (etCompTop W').hom ≫ m = (etCompCompIso m).inv.app (etId W'.left) ≫
      (etComp W.hom).map (toTop ((etComp m.left).obj (etId W'.left))) ≫ (etCompTop W).hom :=
  MorphismProperty.Over.Hom.ext (by
    change 𝟙 _ ≫ m.left = 𝟙 _ ≫ (𝟙 _ ≫ m.left) ≫ 𝟙 _
    simp)

end Nat

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh2 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree

* `dg W`: the diagonal of `W ×_P W` (clopen: `isClopen_dg`); `dsec Λ W`: its indicator section of `Λ_W`;
* `shapφ Λ W : Λ[W] ⟶ π_* Λ_W` is the map given by `dsec` (`shapφ_taut`);
* `cval_S`: values of `Σ_a l_a · τ_a^* dsec` along a sheet;
* **`isIso_shapφ`**, **`shapIso`**: `shapφ` is an isomorphism (stalkwise: `stalk_inj`, `stalk_surj`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtTr

universe u

variable {P : Scheme.{u}}

section Dg

end Dg

section Iso

variable (Λ : Type u) [CommRing Λ] (W : P.Etale) [IsSeparated W.hom]

/-- The indicator section of the diagonal, a section of `π_* Λ_W` over `W`. -/
def dsec : (unitSh Λ W.left).obj.obj (op ((etPull W.hom).obj W)) :=
  (exists_indicator (Λ := Λ) (M := ModuleCat.of Λ Λ) (T := (etPull W.hom).obj W) (dg W) (isClopen_dg W)
    (1 : Λ)).choose

theorem cval_dsec (u : ((etPull W.hom).obj W).left) :
    cval (dsec Λ W) u = (dg W).indicator (fun _ => (1 : Λ)) u :=
  (exists_indicator (Λ := Λ) (M := ModuleCat.of Λ Λ) (T := (etPull W.hom).obj W) (dg W) (isClopen_dg W)
    (1 : Λ)).choose_spec u

theorem germ_S (x : P) {T : P.Etale} [Fintype ((geomPtAt x).point.fiber.obj W)]
    (τ : (geomPtAt x).point.fiber.obj W → (T ⟶ W)) (t : (geomPtAt x).point.fiber.obj T)
    (hτ : ∀ p, (geomPtAt x).point.fiber.map (τ p) t = p) (l : (geomPtAt x).point.fiber.obj W → Λ) :
    germ ((push W.hom Λ).obj (unitSh Λ W.left)) x t
      ((∑ a, l a • ((unitSh Λ W.left).obj.map ((etPull W.hom).map (τ a)).op).hom (dsec Λ W) :
        (unitSh Λ W.left).obj.obj (op ((etPull W.hom).obj T)))) =
      ∑ a, l a • germ ((push W.hom Λ).obj (unitSh Λ W.left)) x a (dsec Λ W) := by
  refine (map_sum ((geomPtAt x).point.toPresheafFiber T t
    ((push W.hom Λ).obj (unitSh Λ W.left)).obj).hom _ Finset.univ).trans ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine (map_smul _ _ _).trans (congrArg (l a • ·) ?_)
  exact (GenAlg.germ_map ((push W.hom Λ).obj (unitSh Λ W.left)) x (τ a) t (dsec Λ W)).trans
    (congrArg (fun c => germ ((push W.hom Λ).obj (unitSh Λ W.left)) x c (dsec Λ W)) (hτ a))

end Iso

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl1c =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl1c): the geometric inputs of stages S1-S2

GLOB/REL PLAN v1, stage S1. For an affine `X` with `g : X ⟶ Spec A` etale (`A` a domain, e.g. `A = k[X]`):
* `gamMap g : A →+* Γ(X)`;
* `exists_frac_dvd` (3a): `u ≠ 0` in `Frac(Γ(X) ⧸ p)` is `x / y` with `x ∣ c_x`, `y ∣ c_y`, `c_x, c_y ∈ A ∖ 0`;
* `toPiQ_gamMap_ne_zero`: a nonzero `r ∈ A` is nonzero on every piece (flatness);
* `exists_L` (3b): one `L ≠ 0` with `L^N y` integral over `A` for every `y`;
* `mem_adjoin_wm` (Gen): `Γ(W₁) = B'[Γ(W)]` along a chart map `d` with `d.left = Spec.map ι`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap

open scoped nonZeroDivisors

universe u

section Gam

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (CommRingCat.of A)) [Etale g]

variable [IsDomain A]

/-- (3b) **Density**: one `L ≠ 0` with `L^N • y` integral over `A` for every `y`. -/
theorem exists_L : letI := gamAlg g; ∃ L : A, L ≠ 0 ∧ ∀ y : Γ(X, ⊤), ∃ N : ℕ, IsIntegral A (L ^ N • y) := by
  let _ : Algebra A Γ(X, ⊤) := gamAlg g
  have : Algebra.Etale A Γ(X, ⊤) := etale_gamAlg g
  have : Algebra.IsAlgebraic A Γ(X, ⊤) := algebra_isAlgebraic_of_etale
  exact exists_pow_smul_isIntegral

end Gam

section Gen

end Gen

end RamanujanPetersson.EtPBC.EtKum

end

end


