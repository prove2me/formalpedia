-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_155
-- name    : RPLib_FX_EtPBC_155
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:23:27.933152+00:00
-- url     : https://prove2.me/theorems/403c7bbc-709b-5743-980e-000c41426d7a
-- title:
--   Proper base change for the projective line, library file 155
-- statement:
--   File 155 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat5`: S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations
--   * `S4.Def_RP_EtPBC_A_CovHat7`: S4-EtPBC-A, R4-T2 (A2c-3g): the kernels of the level reductions of the completed charts
--   * `S4.Def_RP_EtPBC_A_O2T4a0`: S4-EtPBC-A, O2 S5d (O2T4a0): `extFree_thetaM`, `thetaM_comp`, `thetaM_add` (`thetaM` itself is in O2T4a00)
--   * `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
--   * `S4.Def_RP_EtPBC_A_O2L6a`: S4-EtPBC-A, L6a: MV-theta classes under a morphism of MV data
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_132
import Definitions.Def_RPLib_FX_EtPBC_146

/-!
# Proper base change for the projective line, library file 155

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat5`: S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations
* `S4.Def_RP_EtPBC_A_CovHat7`: S4-EtPBC-A, R4-T2 (A2c-3g): the kernels of the level reductions of the completed charts
* `S4.Def_RP_EtPBC_A_O2T4a0`: S4-EtPBC-A, O2 S5d (O2T4a0): `extFree_thetaM`, `thetaM_comp`, `thetaM_add` (`thetaM` itself is in O2T4a00)
* `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
* `S4.Def_RP_EtPBC_A_O2L6a`: S4-EtPBC-A, L6a: MV-theta classes under a morphism of MV data
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovHat5 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations

* `ιP : R →+* ∏E₀ × ∏E₁`, `ιh₀ = β₀ ∘ ιB₀`, `ιh₁ = β₁ ∘ ιB₁`, **`levF_eq`** (`levF σ a = ∑ ιP (aᵢ) σᵢ`),
  **`frac₀_lin`**, **`frac₁_lin`**: fractions of `R`-combinations are combinations of fractions.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lin

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))
  (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

/-- **Fractions of combinations** (chart 1). -/
theorem frac₁_lin (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) {r d : ℕ} {w : Fin r → (∀ k, (C k).E₀) × (∀ k, (C k).E₁)}
    (hw : ∀ i, w i ∈ Gam C H d) (c : Fin r → R) {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d)
    (hsum : x = ∑ i, ιP C ιB₀ ιB₁ (c i) * w i) :
    frac₁ C H d x hx = ∑ i, ιh₁ C H ιB₁ hφ₀ hu₀ (c i) * frac₁ C H d (w i) (hw i) := by
  refine hE₁_ext d ?_ ?_
  · rw [frac₁_spec, AddSubmonoidClass.coe_finsetSum, Prod.fst_sum, Finset.mul_sum, hsum, Prod.fst_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hιc : φ₀ (ιB₀ (c i)) = φ₁ (ιB₁ (c i)) := RingHom.congr_fun hιB (c i)
    show jL₀ C (fB₀ C (ιB₀ (c i)) * (w i).1) = jL₀ C (tFm C ^ d) * (liftN₀ C hφ₀ hu₀ (φ₁ (ιB₁ (c i))) *
      (frac₁ C H d (w i) (hw i) : L₀ C × ∀ k, (C k).E₁).1)
    rw [map_mul, ← liftN₀_φ₀ C hφ₀ hu₀ (ιB₀ (c i)), hιc, ← frac₁_spec (hw i)]
    ring
  · show x.2 = _
    rw [AddSubmonoidClass.coe_finsetSum, Prod.snd_sum, hsum, Prod.snd_sum]
    exact Finset.sum_congr rfl fun i _ => rfl

end Lin

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat7 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3g): the kernels of the level reductions of the completed charts

Over a noetherian `p`-precomplete `R`: **`θ₀_ker`**: `ker (θ₀ k) = p^(k+1) Ê₀`, **`θ₁_ker`**: `ker (θ₁ k) = p^(k+1) Ê₁`
(a fraction vanishing at level `k` becomes, after multiplying by a power of `T₀` resp. `T₁`, a family vanishing at
level `k` (`van₀`, `van₁`), hence a `p^(k+1)`-combination of generators by `gam_ker` (`frac₀_mem_of_van`,
`frac₁_mem_of_van`)).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Van

end Van

section Ker

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))
  (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

include hts in
/-- A fraction of a family vanishing at level `k` lies in `p^(k+1) Ê₁`. -/
def frac₁_mem_of_van [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) {e : ℕ}
    (hs : ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) e))
    (hfil : ∀ k, FilProp ιB₀ ιB₁ p α (C k) e) {y : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hy : y ∈ Gam C H e)
    (k : ℕ) (h0 : y.1 k = 0) (h1 : y.2 k = 0) :
    frac₁ C H e y hy ∈ (p ^ (k + 1)).map (ιh₁ C H ιB₁ hφ₀ hu₀) := by
  obtain ⟨r, σ, hσ, hgen0⟩ := gen_sys C H ιB₀ ιB₁ hts hιB hB₀ hB₁ hs
  obtain ⟨a, ha, hlev⟩ := gam_ker C H ιB₀ ιB₁ p σ α hα hιB hJ₀ hJ₁ hσ hgen0 hfil hy k h0 h1
  have hyeq : y = ∑ i, ιP C ιB₀ ιB₁ (a i) * σ i := by
    rw [← levF_eq]
    exact Prod.ext (funext fun n => congrArg Prod.fst (hlev n)) (funext fun n => congrArg Prod.snd (hlev n))
  rw [frac₁_lin C H ιB₀ ιB₁ hφ₀ hu₀ hιB hσ a hy hyeq]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ha i))

end Ker

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T4a0 =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4a0): `extFree_thetaM`, `thetaM_comp`, `thetaM_add` (`thetaM` itself is in O2T4a00)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}}

theorem thetaM_comp {W T T' : P.Etale} (m : W ⟶ T) (s : T ⟶ T') (n : ℕ) (κ : H Λ (unitSh Λ W.left) n) :
    thetaM Λ (m ≫ s) n κ = (thetaM Λ m n κ).comp (Ext.mk₀ (freeMap Λ s)) (add_zero n) := by
  apply (extFree Λ W (freeSh Λ T') n).injective
  rw [extFree_comp_mk₀, extFree_thetaM, extFree_thetaM, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    secMap_comp]

end Theta

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gd =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes

* `graph_left_eq_of_fib`: sections with the same value at a geometric point have meeting graphs there;
* `mem_graph_of_card`: if disjoint graphs of sections `τ i : W ⟶ T` are at least as many as the points of every
  geometric fibre of `T` (finite), every point of `W ×_P T` lies on one of the graphs;
* `isZero_freeSh_of_isEmpty`, `ext_eq_zero_of_isZero`;
* **`isLoc_free_good`**: for `T` quasi-compact separated etale over `P` and `z = c (X = a)` a point where the fibre of
  `T` is as large as any fibre (a good point: constant degree near `z`), every one-point class at `z` with
  coefficients `Λ[T]` is in the subgroup generated by the point classes `PtCls` (the residual of `isLoc_free_decomp`
  is EMPTY).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk RamanujanPetersson.EtPBC.EtDed

universe u w

section GoodGeo

end GoodGeo

section Zero

end Zero

section GenZero

universe w' v₁ u₁ v₂ u₂ v₃ u₃

end GenZero

section Good

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P)
  [IsOpenImmersion c] (a : k) {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (hΛ : ∀ x : Λ, N • x = 0)

set_option backward.isDefEq.respectTransparency false in
theorem clsD_eq_zero_of_isEmpty {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
    {Uz : P.Opens} (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
    (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact) {F : EtSh Λ P} {R : (chEt c φ).left.Etale}
    (hR : IsEmpty R.left) (f : freeSh Λ R ⟶ (res (chEt c φ).hom Λ).obj F)
    (YR : H Λ ((res (toD1 c φ a).left Λ).obj (freeSh Λ R)) 1) : clsD c φ a hUz hS f YR = 0 :=
  comp_symm_eq_zero_gen YR (Functor.map_isZero _ (isZero_freeSh_of_isEmpty Λ R hR))
    ((res (toD1 c φ a).left Λ).map f ≫ (resCompIso Λ (toD1 c φ a)).hom.app F)
    (hS.extClass.comp (Ext.mk₀ (freeMap Λ (isoT c φ hUz).inv)) (add_zero 1)) (extFree Λ (W1 c φ a) F 1)

end Good

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6a =====
section

/-!
# S4-EtPBC-A, L6a: MV-theta classes under a morphism of MV data

For a morphism `(a', a, b, c)` of MV data `S₁ ⟶ S₂` (both short exact), **`mvTheta_map`**:
`Λ[c] ∘ ε₂ ∘ θ(q₁, κ) ∘ Λ[r] = ε₁ ∘ θ(p₁, a'^* κ) ∘ Λ[a ≫ r]`.
Consequently (**`mvTheta_eq_of_map`**) two MV-theta classes agree after `Λ[c₁]`, `Λ[c₂]` as soon as a common source
square maps to both with the same pulled back Kummer class and the same composite to `R`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk RamanujanPetersson.EtCompact.GalTrE

universe u

section Map

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}
  {W'₁ W₁ U₁ Z₁ W'₂ W₂ U₂ Z₂ : P.Etale} {p₁ : W'₁ ⟶ W₁} {p₂ : W'₁ ⟶ U₁} {w : W₁ ⟶ Z₁} {v : U₁ ⟶ Z₁}
  {hsq : p₁ ≫ w = p₂ ≫ v} {q₁ : W'₂ ⟶ W₂} {q₂ : W'₂ ⟶ U₂} {x : W₂ ⟶ Z₂} {y : U₂ ⟶ Z₂} {hsq₂ : q₁ ≫ x = q₂ ≫ y}
  (a' : W'₁ ⟶ W'₂) (a : W₁ ⟶ W₂) (b : U₁ ⟶ U₂) (c : Z₁ ⟶ Z₂)
  (h₁ : a' ≫ q₁ = p₁ ≫ a) (h₂ : a' ≫ q₂ = p₂ ≫ b) (h₃ : a ≫ x = w ≫ c) (h₄ : b ≫ y = v ≫ c)

include a' a b c h₁ h₂ h₃ h₄ in
/-- **MV-theta classes under a morphism of MV data.** -/
theorem mvTheta_map (hS₁ : (mvC Λ p₁ p₂ w v hsq).ShortExact) (hS₂ : (mvC Λ q₁ q₂ x y hsq₂).ShortExact)
    {R : P.Etale} (r : W₂ ⟶ R) (κ : H Λ (unitSh Λ W'₂.left) 1) :
    (Ext.mk₀ (freeMap Λ c)).comp (hS₂.extClass.comp ((thetaM Λ q₁ 1 κ).comp (Ext.mk₀ (freeMap Λ r)) (add_zero 1))
        (show 1 + 1 = 2 from rfl)) (zero_add 2) =
      hS₁.extClass.comp ((thetaM Λ p₁ 1 (resLE a'.left 1 κ)).comp (Ext.mk₀ (freeMap Λ (a ≫ r))) (add_zero 1))
        (show 1 + 1 = 2 from rfl) := by
  have hn := mv_naturality a' a b c h₁ h₂ h₃ h₄ hS₁ hS₂
  rw [← Ext.comp_assoc (Ext.mk₀ (freeMap Λ c)) hS₂.extClass _ (zero_add 1) (show 1 + 1 = 2 from rfl)
    (show 0 + 1 + 1 = 2 from rfl), ← hn,
    Ext.comp_assoc hS₁.extClass (Ext.mk₀ (freeMap Λ a')) _ (add_zero 1) (zero_add 1) (show 1 + 0 + 1 = 2 from rfl),
    ← Ext.comp_assoc (Ext.mk₀ (freeMap Λ a')) (thetaM Λ q₁ 1 κ) _ (zero_add 1) (add_zero 1)
      (show 0 + 1 + 0 = 1 from rfl),
    ← thetaM_res Λ a' q₁ κ, h₁, thetaM_comp Λ p₁ a 1, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    ← freeMap_comp]

end Map

end RamanujanPetersson.EtPBC.EtMV

end

end


