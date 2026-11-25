-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_017
-- name    : RPLib_FX_EtPBC_017
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T18:52:27.826388+00:00
-- url     : https://prove2.me/theorems/2f8f3bf7-62df-5b7d-b396-7437692d6f3b
-- title:
--   Proper base change for the projective line, library file 017
-- statement:
--   File 017 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_FreeSh`: S4-EtPBC-A, L1a: free sheaves on objects of the small etale site
--   * `S4.Def_RP_EtPBC_A_CovH1`: S4-EtPBC-A, R4-T2 (A2c-1a): `H¹` of `p^n O(d)` vanishes, and overlap relations come from chart 0
--   * `S4.Def_RP_EtPBC_A_CovFil1`: S4-EtPBC-A, R4-T2 (A2c-1d): overlap relations with entries in `p^j` split into chart relations
--   * `S4.Def_RP_EtPBC_A_CovLim1`: S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers
--   * `S4.Def_RP_EtPBC_A_CovLim0`: S4-EtPBC-A, R4-T2 (A2c-2e): sections of `O(d)` at one level: finiteness and multiplication surjectivity
--   * `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
--   * `S4.Def_RP_EtPBC_A_CovHat11`: S4-EtPBC-A, R4-T2 (A2c-3h): the level reductions of the completed overlap
--   * `S4.Def_RP_EtPBC_A_SecCoc`: S4-EtPBC-A, L1c (part 1): cocycles of `I^•(W)` as `Ext` classes
--   * `S4.Def_RP_EtPBC_A_EAlg`: S4-EtPBC-A, M4(E), ALG: maps out of a finitely generated sheaf via relations between germs
--   * `S4.Def_RP_EtPBC_A_O2Fs`: S4-EtPBC-A, O2 (MV route), Fs: stalks of free sheaves
--   * `S4.Def_RP_EtPBC_A_O2U`: S4-EtPBC-A, O2 (MV route), U: `Λ[P] ≅ Λ_P`
--   * `S4.Def_RP_EtPBC_A_O2Pf`: S4-EtPBC-A, O2 (MV route), Pf: pullback of free sheaves
--   * `S4.Def_RP_EtPBC_A_O2L1`: S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes
--   * `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
--   * `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
--   * `S4.Def_RP_EtPBC_A_O2R1`: S4-EtPBC-A, O2 (MV route), M6a (1): the free sheaf on a coproduct is a biproduct; fibres of a coproduct
--   * `S4.Def_RP_EtPBC_A_O2R3`: S4-EtPBC-A, O2 (MV route), M6a (3): the multi-point MV complex maps to each one-point complex
--   * `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
--   * `S4.Def_RP_EtPBC_A_O2T1`: S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps
--   * `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
--   * `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_006
import Definitions.Def_RPLib_FX_EtPBC_010
import Definitions.Def_RPLib_FX_EtPBC_011

/-!
# Proper base change for the projective line, library file 017

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_FreeSh`: S4-EtPBC-A, L1a: free sheaves on objects of the small etale site
* `S4.Def_RP_EtPBC_A_CovH1`: S4-EtPBC-A, R4-T2 (A2c-1a): `H¹` of `p^n O(d)` vanishes, and overlap relations come from chart 0
* `S4.Def_RP_EtPBC_A_CovFil1`: S4-EtPBC-A, R4-T2 (A2c-1d): overlap relations with entries in `p^j` split into chart relations
* `S4.Def_RP_EtPBC_A_CovLim1`: S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers
* `S4.Def_RP_EtPBC_A_CovLim0`: S4-EtPBC-A, R4-T2 (A2c-2e): sections of `O(d)` at one level: finiteness and multiplication surjectivity
* `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
* `S4.Def_RP_EtPBC_A_CovHat11`: S4-EtPBC-A, R4-T2 (A2c-3h): the level reductions of the completed overlap
* `S4.Def_RP_EtPBC_A_SecCoc`: S4-EtPBC-A, L1c (part 1): cocycles of `I^•(W)` as `Ext` classes
* `S4.Def_RP_EtPBC_A_EAlg`: S4-EtPBC-A, M4(E), ALG: maps out of a finitely generated sheaf via relations between germs
* `S4.Def_RP_EtPBC_A_O2Fs`: S4-EtPBC-A, O2 (MV route), Fs: stalks of free sheaves
* `S4.Def_RP_EtPBC_A_O2U`: S4-EtPBC-A, O2 (MV route), U: `Λ[P] ≅ Λ_P`
* `S4.Def_RP_EtPBC_A_O2Pf`: S4-EtPBC-A, O2 (MV route), Pf: pullback of free sheaves
* `S4.Def_RP_EtPBC_A_O2L1`: S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes
* `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
* `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
* `S4.Def_RP_EtPBC_A_O2R1`: S4-EtPBC-A, O2 (MV route), M6a (1): the free sheaf on a coproduct is a biproduct; fibres of a coproduct
* `S4.Def_RP_EtPBC_A_O2R3`: S4-EtPBC-A, O2 (MV route), M6a (3): the multi-point MV complex maps to each one-point complex
* `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
* `S4.Def_RP_EtPBC_A_O2T1`: S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps
* `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
* `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_FreeSh =====
section

/-!
# S4-EtPBC-A, L1a: free sheaves on objects of the small etale site

For `W : X.Etale`, `freeSh Λ W` is the sheafification of `V ↦ Λ[Hom(V, W)]`. It represents evaluation at `W`:
`freeEquiv Λ W F : (freeSh Λ W ⟶ F) ≃+ F(W)`, natural in `F` and in `W`. With Mathlib's `Ext`, the groups
`Ext^q(freeSh Λ W, F)` are the cohomology of `W` with coefficients in `F` and carry long exact sequences in `F`;
the stalks of derived pushforwards are computed with them (unit S4-EtPBC-A, layer L1).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

/-- `Λ[W]` represents evaluation at `W` (as types). -/
def freeEquivT (W : X.Etale) (F : EtSh Λ X) : (freeSh Λ W ⟶ F) ≃ F.val.obj (op W) :=
  ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u} Λ)).homEquiv _ F).trans
    (preEquiv Λ W F.val)

theorem freeEquivT_apply (W : X.Etale) (F : EtSh Λ X) (f : freeSh Λ W ⟶ F) :
    freeEquivT Λ W F f =
      (toSheafify X.smallEtaleTopology (freePre Λ W) ≫ f.hom).app (op W)
        (ModuleCat.freeMk (𝟙 W)) := by
  simp only [freeEquivT, Equiv.trans_apply, preEquiv_apply, Adjunction.homEquiv_unit,
    sheafificationAdjunction_unit_app]
  rfl

/-- `Λ[W]` represents evaluation at `W`. -/
def freeEquiv (W : X.Etale) (F : EtSh Λ X) : (freeSh Λ W ⟶ F) ≃+ F.val.obj (op W) where
  toEquiv := freeEquivT Λ W F
  map_add' f g := by
    simp only [Equiv.toFun_as_coe, freeEquivT_apply]
    rfl

theorem freeEquiv_apply (W : X.Etale) (F : EtSh Λ X) (f : freeSh Λ W ⟶ F) :
    freeEquiv Λ W F f =
      (toSheafify X.smallEtaleTopology (freePre Λ W) ≫ f.hom).app (op W)
        (ModuleCat.freeMk (𝟙 W)) :=
  freeEquivT_apply Λ W F f

/-- Naturality in the sheaf. -/
theorem freeEquiv_comp (W : X.Etale) {F G : EtSh Λ X} (f : freeSh Λ W ⟶ F) (φ : F ⟶ G) :
    freeEquiv Λ W G (f ≫ φ) = φ.hom.app (op W) (freeEquiv Λ W F f) := by
  simp only [freeEquiv_apply]
  rfl

/-- Naturality in the object of the site. -/
theorem freeEquiv_freeMap {W' W : X.Etale} (w : W' ⟶ W) (F : EtSh Λ X) (f : freeSh Λ W ⟶ F) :
    freeEquiv Λ W' F (freeMap Λ w ≫ f) = F.val.map w.op (freeEquiv Λ W F f) := by
  rw [freeEquiv_apply, freeEquiv_apply]
  have h1 : toSheafify X.smallEtaleTopology (freePre Λ W') ≫ (freeMap Λ w ≫ f).hom =
      Functor.whiskerRight (yoneda.map w) (ModuleCat.free Λ) ≫
        toSheafify X.smallEtaleTopology (freePre Λ W) ≫ f.hom := by
    change _ ≫ ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).map _).hom ≫ f.hom = _
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact (toSheafify_naturality X.smallEtaleTopology _).symm
  rw [h1]
  have h2 := NatTrans.naturality_apply
    (φ := toSheafify X.smallEtaleTopology (freePre Λ W) ≫ f.hom) w.op
    (ModuleCat.freeMk (R := Λ) (𝟙 W))
  refine Eq.trans ?_ h2
  change (ConcreteCategory.hom ((toSheafify X.smallEtaleTopology (freePre Λ W) ≫ f.hom).app (op W')))
    ((Functor.whiskerRight (yoneda.map w) (ModuleCat.free Λ)).app (op W') (ModuleCat.freeMk (𝟙 W'))) = _
  congr 1
  simp [freePre]

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_CovH1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-1a): `H¹` of `p^n O(d)` vanishes, and overlap relations come from chart 0

For a two-chart cover `C` with ring maps `ιᵢ : R → Eᵢ` agreeing on the overlap:
* **`TwoCov.Spl ι₀ ι₁ 𝔞 d z`**: `z = ψ₀ x₀ - u^d ψ₁ x₁` with `xᵢ ∈ 𝔞 Eᵢ`; `Spl.add`, `Spl.zero`, `Spl.mono`, `Spl.mul`;
* **`TwoCov.spl_pow`**: `H¹ = 0` modulo `p E` and `p^N E = 0` give `Spl (p^n)` on all of `p^n E`;
* **`TwoCov.to_chart0`**: a relation vector on the overlap with entries in `𝔞 E` is `u^{-e} ψ₀` of one on chart 0;
* **`spl_tower`**: one `d₀` with `Spl (p^n) d` on `p^n E` at every level of the tower, all `n`, all `d ≥ d₀`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Spl

variable {b₀ b₁ n : Type u} [CommRing b₀] [CommRing b₁] [CommRing n] {φb₀ : b₀ →+* n} {φb₁ : b₁ →+* n}
  {τ₀ : b₀} {τ₁ : b₁} (C : TwoCov φb₀ φb₁ τ₀ τ₁) {R : Type u} [CommRing R] (ι₀ : R →+* C.E₀) (ι₁ : R →+* C.E₁)

variable {C ι₀ ι₁}

/-- **`H¹` of `p^n E` vanishes** when `H¹ = 0` modulo `p E` and `p^N E = 0`. -/
theorem TwoCov.spl_pow (hι : C.ψ₀.comp ι₀ = C.ψ₁.comp ι₁) (p : Ideal R) (d : ℕ)
    (h1 : ∀ z : C.E, ∃ (x₀ : C.E₀) (x₁ : C.E₁), z - (C.ψ₀ x₀ - C.u ^ d * C.ψ₁ x₁) ∈ p.map (C.ψ₀.comp ι₀))
    (N : ℕ) (hN : (p ^ N).map (C.ψ₀.comp ι₀) = ⊥) :
    ∀ n, ∀ z ∈ (p ^ n).map (C.ψ₀.comp ι₀), C.Spl ι₀ ι₁ (p ^ n) d z := by
  have key : ∀ m n, N ≤ n + m → ∀ z ∈ (p ^ n).map (C.ψ₀.comp ι₀), C.Spl ι₀ ι₁ (p ^ n) d z := by
    intro m
    induction m with
    | zero =>
      intro n hn z hz
      have hle : (p ^ n).map (C.ψ₀.comp ι₀) ≤ (p ^ N).map (C.ψ₀.comp ι₀) :=
        Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
      rw [hN] at hle
      have h0 : z = 0 := (Submodule.mem_bot _).1 (hle hz)
      rw [h0]
      exact TwoCov.Spl.zero _ _
    | succ m ih =>
      intro n hn z hz
      have hmain : ∀ δ ∈ (p ^ n).map (C.ψ₀.comp ι₀), ∀ c, C.Spl ι₀ ι₁ (p ^ n) d (c * δ) := by
        intro δ hδ
        change δ ∈ Submodule.span C.E _ at hδ
        induction hδ using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨π, hπ, rfl⟩ := hx
          intro c
          obtain ⟨x₀, x₁, hx⟩ := h1 c
          have hs : C.Spl ι₀ ι₁ (p ^ n * ⊤) d (C.ψ₀ (ι₀ π) * (C.ψ₀ x₀ - C.u ^ d * C.ψ₁ x₁)) :=
            TwoCov.Spl.mul hι (TwoCov.spl_top x₀ x₁ rfl) hπ
          rw [Ideal.mul_top] at hs
          have hi : C.ψ₀ (ι₀ π) * (c - (C.ψ₀ x₀ - C.u ^ d * C.ψ₁ x₁)) ∈
              (p ^ (n + 1)).map (C.ψ₀.comp ι₀) := by
            rw [pow_succ, Ideal.map_mul]
            exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem (C.ψ₀.comp ι₀) hπ) hx
          have hs2 := (ih (n + 1) (by omega) _ hi).mono (Ideal.pow_le_pow_right (Nat.le_succ n))
          have hsum := hs.add hs2
          have e : C.ψ₀ (ι₀ π) * (C.ψ₀ x₀ - C.u ^ d * C.ψ₁ x₁) +
              C.ψ₀ (ι₀ π) * (c - (C.ψ₀ x₀ - C.u ^ d * C.ψ₁ x₁)) = c * (C.ψ₀.comp ι₀) π := by
            rw [RingHom.comp_apply]
            ring
          rwa [e] at hsum
        | zero =>
          intro c
          rw [mul_zero]
          exact TwoCov.Spl.zero _ _
        | add x y _ _ hx hy =>
          intro c
          rw [mul_add]
          exact (hx c).add (hy c)
        | smul a x _ hx =>
          intro c
          rw [smul_eq_mul, ← mul_assoc]
          exact hx (c * a)
      have := hmain z hz 1
      rwa [one_mul] at this
  intro n
  exact key N n (by omega)

end Spl

section Tower

end Tower

end RamanujanPetersson.EtPBC.Cov

end

end

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

/-- **Splitting a decomposed relation** on the two charts, by uniform `H¹` vanishing. -/
theorem split_rel {g : ℕ} (α : Fin g → R) (hαp : ∀ i, α i ∈ p) (hts : φ₀ t₀ * φ₁ t₁ = 1)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) {k : ℕ} (C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
    (d d₀ F : ℕ) (hd : d₀ + F ≤ d)
    (hspl : ∀ d', d₀ ≤ d' → ∀ n, ∀ z ∈ (p ^ n).map (C.ψ₀.comp (lι₀ ιB₀ C)),
      C.Spl (lι₀ ιB₀ C) (lι₁ ιB₁ C) (p ^ n) d' z)
    {j n' : ℕ} (hj : j ≤ k) (hn' : n' ≤ j) {L : ℕ} (ρ0 : Fin L → Fin g → B₀) (ρ1 : Fin L → Fin g → B₁)
    (f : Fin L → ℕ) (hf : ∀ l, f l ≤ F) (hρ0 : ∀ l, ρ0 l ∈ RelV p α ιB₀ n')
    (hρ1 : ∀ l, ρ1 l ∈ RelV p α ιB₁ n') (hρ : ∀ l i, φ₀ (ρ0 l i) = φ₀ t₀ ^ f l * φ₁ (ρ1 l i))
    (e : ℕ) (w : Fin g → C.E) (c : Fin L → C.E₀) (v : Fin g → C.E₀)
    (hc : ∀ l, c l ∈ (p ^ (j - n')).map (lι₀ ιB₀ C)) (hv : ∀ i, v i ∈ (p ^ k).map (lι₀ ιB₀ C))
    (hw : ∀ i, C.u ^ e * w i =
      C.ψ₀ (∑ l, c l * C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i)) + v i)) :
    ∃ (a : Fin g → C.E₀) (b : Fin g → C.E₁), (∀ i, a i ∈ (p ^ j).map (lι₀ ιB₀ C)) ∧
      (∀ i, b i ∈ (p ^ j).map (lι₁ ιB₁ C)) ∧ ∑ i, lι₀ ιB₀ C (α i) * a i = 0 ∧
      ∑ i, lι₁ ιB₁ C (α i) * b i = 0 ∧ ∀ i, w i = C.ψ₀ (a i) - C.u ^ d * C.ψ₁ (b i) := by
  obtain ⟨ν, hν⟩ : ∃ ν : C.E, ν = C.ψ₁ (C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) := ⟨_, rfl⟩
  have huν : C.u * ν = 1 := by
    rw [hν]
    exact lhv hts C
  have hwi : ∀ i, w i = ν ^ e *
      C.ψ₀ (∑ l, c l * C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i)) + v i) := fun i => by
    rw [← hw i, ← mul_assoc, ← mul_pow, mul_comm ν, huν, one_pow, one_mul]
  have hmem : ∀ {m : ℕ} {x : C.E₀}, x ∈ (p ^ m).map (lι₀ ιB₀ C) →
      ν ^ e * C.ψ₀ x ∈ (p ^ m).map (C.ψ₀.comp (lι₀ ιB₀ C)) := by
    intro m x hx
    refine Ideal.mul_mem_left _ _ ?_
    rw [← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hx
  have hs1 : ∀ l, ∃ x₀ ∈ (p ^ (j - n')).map (lι₀ ιB₀ C), ∃ x₁ ∈ (p ^ (j - n')).map (lι₁ ιB₁ C),
      ν ^ e * C.ψ₀ (c l) = C.ψ₀ x₀ - C.u ^ (d - f l) * C.ψ₁ x₁ :=
    fun l => hspl (d - f l) (by have := hf l; omega) (j - n') _ (hmem (hc l))
  have hs2 : ∀ i, ∃ x₀ ∈ (p ^ k).map (lι₀ ιB₀ C), ∃ x₁ ∈ (p ^ k).map (lι₁ ιB₁ C),
      ν ^ e * C.ψ₀ (v i) = C.ψ₀ x₀ - C.u ^ d * C.ψ₁ x₁ :=
    fun i => hspl d (by omega) k _ (hmem (hv i))
  choose A hA Bl hBl hAB using hs1
  choose A' hA' B' hB' hAB' using hs2
  have hu : C.u = C.a (Ideal.Quotient.mk (JN ^ (k + 1)) (φ₀ t₀)) := lψθ₀ C t₀
  have hρE : ∀ l i, C.ψ₀ (C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i))) =
      C.u ^ f l * C.ψ₁ (C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) (ρ1 l i))) := fun l i => by
    rw [hu, lψθ₀ C (ρ0 l i), lψθ₁ C (ρ1 l i), hρ]
    simp only [map_mul, map_pow]
  obtain ⟨a, ha⟩ : ∃ a : Fin g → C.E₀, ∀ i,
      a i = ∑ l, A l * C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i)) + A' i := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin g → C.E₁, ∀ i,
      b i = ∑ l, Bl l * C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) (ρ1 l i)) + B' i := ⟨_, fun _ => rfl⟩
  have hαp₀ : ∀ i, lι₀ ιB₀ C (α i) ∈ p.map (lι₀ ιB₀ C) := fun i => Ideal.mem_map_of_mem _ (hαp i)
  have hαp₁ : ∀ i, lι₁ ιB₁ C (α i) ∈ p.map (lι₁ ιB₁ C) := fun i => Ideal.mem_map_of_mem _ (hαp i)
  refine ⟨a, b, fun i => ?_, fun i => ?_, ?_, ?_, fun i => ?_⟩
  · rw [ha]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun l _ => ?_)
      (Ideal.map_mono (Ideal.pow_le_pow_right hj) (hA' i))
    have hm := Ideal.mul_mem_mul (hA l) (mem_lι₀ ιB₀ p C ((hρ0 l).1 i))
    rw [← Ideal.map_mul, ← pow_add, Nat.sub_add_cancel hn'] at hm
    exact hm
  · rw [hb]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun l _ => ?_)
      (Ideal.map_mono (Ideal.pow_le_pow_right hj) (hB' i))
    have hm := Ideal.mul_mem_mul (hBl l) (mem_lι₁ ιB₁ p C ((hρ1 l).1 i))
    rw [← Ideal.map_mul, ← pow_add, Nat.sub_add_cancel hn'] at hm
    exact hm
  · have h1 : ∀ l, ∑ i, lι₀ ιB₀ C (α i) * (A l * C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i))) = 0 := by
      intro l
      have e : ∑ i, lι₀ ιB₀ C (α i) * (A l * C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i))) =
          A l * C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (∑ i, ιB₀ (α i) * ρ0 l i)) := by
        simp only [map_sum, map_mul, Finset.mul_sum, lι₀, RingHom.comp_apply]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, (hρ0 l).2, map_zero, map_zero, mul_zero]
    have h2 : ∀ i, lι₀ ιB₀ C (α i) * A' i = 0 := by
      intro i
      have hm := Ideal.mul_mem_mul (hαp₀ i) (hA' i)
      rw [← Ideal.map_mul, ← pow_succ', lpow_bot₀ _ _ _ _ _ _ _ _ _ ιB₀ p hJ₀ C le_rfl] at hm
      exact (Submodule.mem_bot _).1 hm
    simp only [ha, mul_add, Finset.sum_add_distrib, Finset.mul_sum, h2, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun l _ => h1 l
  · have h1 : ∀ l, ∑ i, lι₁ ιB₁ C (α i) * (Bl l * C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) (ρ1 l i))) = 0 := by
      intro l
      have e : ∑ i, lι₁ ιB₁ C (α i) * (Bl l * C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) (ρ1 l i))) =
          Bl l * C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) (∑ i, ιB₁ (α i) * ρ1 l i)) := by
        simp only [map_sum, map_mul, Finset.mul_sum, lι₁, RingHom.comp_apply]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, (hρ1 l).2, map_zero, map_zero, mul_zero]
    have h2 : ∀ i, lι₁ ιB₁ C (α i) * B' i = 0 := by
      intro i
      have hm := Ideal.mul_mem_mul (hαp₁ i) (hB' i)
      rw [← Ideal.map_mul, ← pow_succ', lpow_bot₁ _ _ _ _ _ _ _ _ _ ιB₁ p hJ₁ C le_rfl] at hm
      exact (Submodule.mem_bot _).1 hm
    simp only [hb, mul_add, Finset.sum_add_distrib, Finset.mul_sum, h2, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun l _ => h1 l
  · have key : ∀ l, ν ^ e * (C.ψ₀ (c l) * C.ψ₀ (C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i)))) =
        C.ψ₀ (A l) * C.ψ₀ (C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i))) -
          C.u ^ d * (C.ψ₁ (Bl l) * C.ψ₁ (C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) (ρ1 l i)))) := by
      intro l
      have hdf : C.u ^ d = C.u ^ (d - f l) * C.u ^ f l := by
        rw [← pow_add, Nat.sub_add_cancel (le_trans (hf l) (by omega))]
      rw [hρE l i, hdf]
      linear_combination (C.u ^ f l * C.ψ₁ (C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) (ρ1 l i)))) * hAB l
    have S0 : C.ψ₀ (∑ l, c l * C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i))) =
        ∑ l, C.ψ₀ (c l) * C.ψ₀ (C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i))) := by
      simp only [map_sum, map_mul]
    have SA : C.ψ₀ (∑ l, A l * C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i))) =
        ∑ l, C.ψ₀ (A l) * C.ψ₀ (C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i))) := by
      simp only [map_sum, map_mul]
    have SB : C.ψ₁ (∑ l, Bl l * C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) (ρ1 l i))) =
        ∑ l, C.ψ₁ (Bl l) * C.ψ₁ (C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) (ρ1 l i))) := by
      simp only [map_sum, map_mul]
    have hsum : ν ^ e * ∑ l, C.ψ₀ (c l) * C.ψ₀ (C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i))) =
        ∑ l, C.ψ₀ (A l) * C.ψ₀ (C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ρ0 l i))) -
          C.u ^ d * ∑ l, C.ψ₁ (Bl l) * C.ψ₁ (C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) (ρ1 l i))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => key l
    rw [hwi i, ha, hb, map_add, map_add, map_add, S0, SA, SB]
    linear_combination hsum + hAB' i

end Lv

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovLim1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers

* `dep_choice`, `seq_choice`: sequences by choice along `ℕ`;
* `ker_ρ₀`, `ker_ρ₁`: the kernels of a transition are `p^(k+1)` on the charts; `mem_of_ρ₀`, `mem_of_ρ₁`: an element whose
  image has entries in `p^n` (`n ≤ k+1`) has entries in `p^n`;
* **`Gam C H d`**: compatible families of sections of `O(d)` along a tower `C`, `H`; **`exists_gam`**: every level-`0`
  section lifts when all transitions are surjective on sections.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Ker

end Ker

section Fam

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

/-- **Compatible families of sections of `O(d)`** along the tower `C`, `H`. -/
def Gam (d : ℕ) : AddSubgroup ((∀ k, (C k).E₀) × (∀ k, (C k).E₁)) where
  carrier := {x | ∀ k, (H k).ρ₀ (x.1 (k + 1)) = x.1 k ∧ (H k).ρ₁ (x.2 (k + 1)) = x.2 k ∧
    (C k).ψ₀ (x.1 k) = (C k).u ^ d * (C k).ψ₁ (x.2 k)}
  add_mem' := by
    intro x y hx hy k
    obtain ⟨a1, a2, a3⟩ := hx k
    obtain ⟨b1, b2, b3⟩ := hy k
    refine ⟨?_, ?_, ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, map_add, a1, b1]
    · simp only [Prod.snd_add, Pi.add_apply, map_add, a2, b2]
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, a3, b3, mul_add]
  zero_mem' := by
    intro k
    simp
  neg_mem' := by
    intro x hx k
    obtain ⟨a1, a2, a3⟩ := hx k
    refine ⟨?_, ?_, ?_⟩
    · simp only [Prod.fst_neg, Pi.neg_apply, map_neg, a1]
    · simp only [Prod.snd_neg, Pi.neg_apply, map_neg, a2]
    · simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, map_neg, a3, mul_neg]

end Fam

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovLim0 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2e): sections of `O(d)` at one level: finiteness and multiplication surjectivity

For a level cover `C` (charts finite over `R[t]`, `R[s]`, `R` noetherian):
* **`sec_fg`**: the sections of `O(d)` are finitely many `R`-combinations of fixed sections (via `Z1.twoChart_fg`);
* **`sec_mul_surj`**: `Γ(e+2) = T₀ Γ(e+1) + T₁ Γ(e+1)` when `H¹(O(e)) = 0` (`T₀ = (1, s)`, `T₁ = (t, 1)`);
* `sec_gen_T`: generators of `Γ(e+2)` of the form `T₀ τⱼ`, `T₁ τⱼ`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lv

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁)

/-- **Multiplication surjectivity**: `Γ(e+2) = T₀ Γ(e+1) + T₁ Γ(e+1)` when `H¹(O(e)) = 0`. -/
theorem sec_mul_surj (hts : φ₀ t₀ * φ₁ t₁ = 1) {k : ℕ} (C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k) (e : ℕ)
    (hspl : ∀ z : C.E, ∃ (x₀ : C.E₀) (x₁ : C.E₁), z = C.ψ₀ x₀ - C.u ^ e * C.ψ₁ x₁) (y : C.E₀ × C.E₁)
    (hy : y ∈ C.sec (e + 2)) :
    ∃ x z : C.E₀ × C.E₁, x ∈ C.sec (e + 1) ∧ z ∈ C.sec (e + 1) ∧
      y = (x.1, C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁) * x.2) +
        (C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀) * z.1, z.2) := by
  have hv := lhv hts C
  have hu : C.ψ₀ (C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀)) = C.u := rfl
  have hy' : C.ψ₀ y.1 = C.u ^ (e + 2) * C.ψ₁ y.2 := hy
  obtain ⟨z₀, x₁, hw⟩ := hspl (C.ψ₁ (C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) * C.ψ₀ y.1)
  refine ⟨(y.1 - C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀) * z₀, -x₁),
    (z₀, y.2 - C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁) * -x₁), ?_, ?_, ?_⟩
  · show C.ψ₀ (y.1 - C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀) * z₀) = C.u ^ (e + 1) * C.ψ₁ (-x₁)
    rw [map_sub, map_mul, hu, map_neg]
    linear_combination C.u * hw - C.ψ₀ y.1 * hv
  · show C.ψ₀ z₀ = C.u ^ (e + 1) * C.ψ₁ (y.2 - C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁) * -x₁)
    rw [map_sub, map_mul, map_neg]
    linear_combination (-1 : C.E) * hw + C.ψ₁ (C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) * hy' +
      (C.u ^ (e + 1) * C.ψ₁ y.2 - C.u ^ e * C.ψ₁ x₁) * hv
  · refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]
      ring
    · simp only [Prod.snd_add]
      ring

end Lv

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts

* **`hE`** `⊆ L₀ × L₁` (fractions `x / T₁ᵃ T₀ᵇ`, `x ∈ Gam (a + b)`); **`hψ₀ : hE₀ →+* hE`**, **`hψ₁ : hE₁ →+* hE`**;
* `ρ₀_fB`, `ρ₁_fB`, **`famB_mem`**: `(fB₀ b₀, fB₁ b₁) ∈ Gam d` when `φ₀ b₀ = φ₀ t₀ ^ d * φ₁ b₁`;
* **`liftN₀ : N →+* L₀`**, **`liftN₁ : N →+* L₁`** (from `N = B₀[1/t₀] = B₁[1/t₁]`), `liftN₀_φ₀`, `liftN₁_φ₁`,
  `liftN₀_inv`, `liftN₁_inv`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Hat2

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

theorem ρ₀_fB (b : B₀) (k : ℕ) : (H k).ρ₀ (fB₀ C b (k + 1)) = fB₀ C b k := by
  have e := RingHom.congr_fun (H k).c₀ (Ideal.Quotient.mk (J₀ ^ (k + 1 + 1)) b)
  simp only [RingHom.comp_apply] at e
  rw [fB₀_apply, fB₀_apply, e]
  exact congrArg (C k).a₀ (Ideal.Quotient.factor_mk _ _)

theorem ρ₁_fB (b : B₁) (k : ℕ) : (H k).ρ₁ (fB₁ C b (k + 1)) = fB₁ C b k := by
  have e := RingHom.congr_fun (H k).c₁ (Ideal.Quotient.mk (J₁ ^ (k + 1 + 1)) b)
  simp only [RingHom.comp_apply] at e
  rw [fB₁_apply, fB₁_apply, e]
  exact congrArg (C k).a₁ (Ideal.Quotient.factor_mk _ _)

end Hat2

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat11 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3h): the level reductions of the completed overlap

* `ev₀ k : L₀ → E(k)` (the lift of `ψ₀ ∘ eval k`, `t ↦ u` is a unit), `ev₀_jL₀`;
* **`θ k : Ê → E(k)`**, compatible with the chart reductions: **`θ_hψ₀`** (`θ ∘ ψ̂₀ = ψ₀ ∘ θ₀`), **`θ_hψ₁`**
  (`θ ∘ ψ̂₁ = ψ₁ ∘ θ₁`), and with the structure maps: **`θ_β`** (`θ ∘ β = a ∘ mk`).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Ov

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (hts : φ₀ t₀ * φ₁ t₁ = 1)
  (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀)) (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

include hts in
theorem isUnit_ev (k : ℕ) :
    IsUnit (((C k).ψ₀.comp (Pi.evalRingHom (fun k => ((C k).E₀ : Type u)) k)) (tFm C)) := by
  show IsUnit (C k).u
  exact IsUnit.of_mul_eq_one _ (lhv hts (C k))

/-- `L₀ = (∏ E₀(k))[1/t] → E(k)`. -/
def ev₀ (k : ℕ) : L₀ C →+* (C k).E :=
  IsLocalization.Away.lift (tFm C) (isUnit_ev C hts k)

end Ov

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_SecCoc =====
section

/-!
# S4-EtPBC-A, L1c (part 1): cocycles of `I^•(W)` as `Ext` classes

For an injective resolution `I` of `F`, `W : X.Etale` and `p : ℕ`: `secSc Λ I W p` is the short complex `sc (p+1)` of
the complex of sections `I^•(W)`; `cocExtFun` sends a cocycle `z` (an element of `ker g`) to the class
`InjectiveResolution.extMk` of the map `Λ[W] ⟶ I^(p+1)` given by `z` (`freeEquiv`); it is additive (`cocExtFun_add`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} {F : EtSh Λ X} (I : InjectiveResolution F)

theorem cocExt_aux (W : X.Etale) (p : ℕ) (z : LinearMap.ker (secSc Λ I W p).g.hom) :
    (freeEquiv Λ W (I.cocomplex.X (p + 1))).symm (cocSec Λ I z) ≫
      I.cocomplex.d (p + 1) ((ComplexShape.up ℕ).next (p + 1)) = 0 := by
  apply (freeEquiv Λ W _).injective
  rw [freeEquiv_comp, AddEquiv.apply_symm_apply, map_zero]
  exact cocSec_d Λ I z

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_EAlg =====
section

/-!
# S4-EtPBC-A, M4(E), ALG: maps out of a finitely generated sheaf via relations between germs

Fix `e : ∐ Λ[W j] ↠ F` (`J` finite). The generators `gen W e j ∈ F(W j)` are the images of the tautological
sections `taut Λ (W j) ∈ Λ[W j](W j)`. For sections `f j ∈ H(W j)` and `x : P`, `rel W H f x` is the linear map
`(Σ j, fibre of W j at x̄) →₀ Λ → H_x̄`, `l ↦ Σ l(j, a) · germ_a (f j)`.

* `free_stalk_span`, `coprod_span`, **`free_range`**: the stalk of `∐ Λ[W j]` at `x̄` is spanned by the germs of the
  tautological sections (the range of `rel` for `tg W` is everything);
* **`exists_desc`**: if at every `x` the relations of the generators `gen W e` are relations of `f`, there is
  `φ : F ⟶ H` with `φ (gen W e j) = f j`;
* **`mono_stalk`**: if at `x` the relations of `φ (gen W e j)` are relations of `gen W e`, then `φ` is injective on
  the stalk at `x̄`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenAlg

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

variable (Λ) in
/-- The tautological section of `Λ[W]` over `W`. -/
def taut (W : P.Etale) : (freeSh Λ W).obj.obj (op W) := freeEquiv Λ W (freeSh Λ W) (𝟙 _)

theorem taut_eq (W : P.Etale) :
    taut Λ W = ((toSheafify P.smallEtaleTopology (freePre Λ W)).app (op W)).hom (ModuleCat.freeMk (𝟙 W)) := by
  rw [taut, freeEquiv_apply]
  rfl

/-- **The stalk of `Λ[W]` is spanned by the germs of the tautological section.** -/
theorem free_stalk_span (W : P.Etale) (x : P) (v : stalk Λ (freeSh Λ W) x) :
    v ∈ Submodule.span Λ (Set.range fun a : (geomPtAt x).point.fiber.obj W => germ (freeSh Λ W) x a (taut Λ W)) := by
  have hiso : IsIso (((geomPtAt x).point.presheafFiber (A := ModuleCat.{u} Λ)).map
      (toSheafify P.smallEtaleTopology (freePre Λ W))) := inferInstance
  have hsurj : Function.Surjective (((geomPtAt x).point.presheafFiber (A := ModuleCat.{u} Λ)).map
      (toSheafify P.smallEtaleTopology (freePre Λ W))).hom :=
    (ModuleCat.epi_iff_surjective _).1 (@IsIso.epi_of_iso _ _ _ _ _ hiso)
  obtain ⟨v', rfl⟩ := hsurj v
  obtain ⟨V, b, p, rfl⟩ := (geomPtAt x).point.toPresheafFiber_jointly_surjective v'
  have key : ∀ h : V ⟶ W, (((geomPtAt x).point.presheafFiber (A := ModuleCat.{u} Λ)).map
      (toSheafify P.smallEtaleTopology (freePre Λ W))).hom
        (((geomPtAt x).point.toPresheafFiber V b (freePre Λ W)).hom (ModuleCat.freeMk h)) =
      germ (freeSh Λ W) x ((geomPtAt x).point.fiber.map h b) (taut Λ W) := by
    intro h
    have e1 : (freePre Λ W).map h.op (ModuleCat.freeMk (𝟙 W)) = ModuleCat.freeMk h := by
      simp [freePre]
    have e2 := congrArg (fun ψ => ψ.hom (ModuleCat.freeMk (R := Λ) (𝟙 W)))
      (GrothendieckTopology.Point.toPresheafFiber_w (Φ := (geomPtAt x).point) h b (freePre Λ W))
    have e3 := congrArg (fun ψ => ψ.hom (ModuleCat.freeMk (R := Λ) (𝟙 W)))
      (GrothendieckTopology.Point.toPresheafFiber_naturality (Φ := (geomPtAt x).point)
        (toSheafify P.smallEtaleTopology (freePre Λ W)) W ((geomPtAt x).point.fiber.map h b))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e2 e3
    rw [taut_eq]
    rw [← e1]
    refine (congrArg _ e2).trans ?_
    exact e3
  let L : ((V ⟶ W) →₀ Λ) →ₗ[Λ] stalk Λ (freeSh Λ W) x :=
    (((geomPtAt x).point.presheafFiber (A := ModuleCat.{u} Λ)).map (toSheafify P.smallEtaleTopology (freePre Λ W))).hom ∘ₗ
      ((geomPtAt x).point.toPresheafFiber V b (freePre Λ W)).hom
  change L p ∈ _
  induction p using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  | single h c =>
    have e : Finsupp.single h c = c • Finsupp.single h (1 : Λ) := (Finsupp.smul_single_one h c).symm
    rw [e, map_smul]
    refine Submodule.smul_mem _ c (Submodule.subset_span ⟨(geomPtAt x).point.fiber.map h b, ?_⟩)
    exact (key h).symm

variable {J : Type u} [Finite J] (W : J → P.Etale)

/-- The tautological sections of `∐ Λ[W j]`. -/
def tg (j : J) : (∐ fun j => freeSh Λ (W j)).obj.obj (op (W j)) :=
  ((Sigma.ι (fun j => freeSh Λ (W j)) j).hom.app (op (W j))).hom (taut Λ (W j))

variable {W}

/-- The generators `e (tg W j) ∈ F(W j)` of a quotient `e : ∐ Λ[W j] ⟶ F`. -/
def gen {F : EtSh Λ P} (e : (∐ fun j => freeSh Λ (W j)) ⟶ F) (j : J) : F.obj.obj (op (W j)) :=
  freeEquiv Λ (W j) F (Sigma.ι (fun j => freeSh Λ (W j)) j ≫ e)

theorem gen_eq {F : EtSh Λ P} (e : (∐ fun j => freeSh Λ (W j)) ⟶ F) (j : J) :
    gen e j = (e.hom.app (op (W j))).hom (tg W j) := by
  rw [gen, ← Category.id_comp (Sigma.ι (fun j => freeSh Λ (W j)) j ≫ e), freeEquiv_comp]
  rfl

theorem rel_gen {F : EtSh Λ P} (e : (∐ fun j => freeSh Λ (W j)) ⟶ F) (x : P)
    (l : (Σ j, (geomPtAt x).point.fiber.obj (W j)) →₀ Λ) :
    (((geomPtAt x).stalkF Λ).map e).hom (rel W _ (tg W) x l) = rel W F (gen e) x l := by
  rw [rel_map]
  congr 2

end RamanujanPetersson.EtPBC.GenAlg

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Fs =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fs: stalks of free sheaves

For `W : P.Etale` and `x : P`, the stalk of `Λ[W]` at `x̄ = geomPtAt x` is the free module on the geometric fibre of
`W` over `x̄`:
* `fibDesc`: the map `presheafFiber (Λ[Hom(-, W)]) → (fibre →₀ Λ)`, `h ↦ fiber.map h b` at `(V, b)`;
* `stalkFree`: the induced map out of the stalk of `Λ[W]`, `stalkFree_germ` (germ of the tautological section at `a`
  goes to `single a 1`);
* `freeLin W x : (fibre →₀ Λ) →ₗ stalk`, `a ↦ germ_a(taut)`; **`freeStalkEquiv`** (bijective);
* `freeMap_taut`, **`freeLin_natural`**: the stalk map of `Λ[w]` is `lmapDomain (fiber.map w)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.FreeStk

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

variable (Λ) in
/-- `a ↦ germ_a (taut)`. -/
def freeLin (W : P.Etale) (x : P) : ((geomPtAt x).point.fiber.obj W →₀ Λ) →ₗ[Λ] stalk Λ (freeSh Λ W) x :=
  Finsupp.linearCombination Λ fun a => germ (freeSh Λ W) x a (taut Λ W)

theorem freeLin_surjective (W : P.Etale) (x : P) : Function.Surjective (freeLin Λ W x) := by
  intro v
  have hv := free_stalk_span W x v
  rw [← Finsupp.range_linearCombination] at hv
  exact hv

/-- `Λ[w]` sends the tautological section of `Λ[W']` to the restriction of that of `Λ[W]`. -/
theorem freeMap_taut {W' W : P.Etale} (w : W' ⟶ W) :
    ((freeMap Λ w).hom.app (op W')).hom (taut Λ W') = ((freeSh Λ W).obj.map w.op).hom (taut Λ W) := by
  have h1 := freeEquiv_comp Λ W' (𝟙 (freeSh Λ W')) (freeMap Λ w)
  have h2 := freeEquiv_freeMap Λ w (freeSh Λ W) (𝟙 _)
  rw [Category.id_comp] at h1
  rw [Category.comp_id] at h2
  exact h1.symm.trans h2

/-- **Naturality**: on stalks, `Λ[w]` is `lmapDomain (fiber.map w)`. -/
theorem freeLin_natural {W' W : P.Etale} (w : W' ⟶ W) (x : P) (l : (geomPtAt x).point.fiber.obj W' →₀ Λ) :
    (((geomPtAt x).stalkF Λ).map (freeMap Λ w)).hom (freeLin Λ W' x l) =
      freeLin Λ W x (Finsupp.mapDomain ((geomPtAt x).point.fiber.map w) l) := by
  induction l using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, Finsupp.mapDomain_zero, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Finsupp.mapDomain_add, map_add]
  | single a c =>
    rw [freeLin, Finsupp.linearCombination_single, map_smul, germ_natural, freeMap_taut, germ_map,
      Finsupp.mapDomain_single, freeLin, Finsupp.linearCombination_single]

end RamanujanPetersson.EtPBC.FreeStk

end

end

-- ===== S4.Def_RP_EtPBC_A_O2U =====
section

/-!
# S4-EtPBC-A, O2 (MV route), U: `Λ[P] ≅ Λ_P`

* `oneSec`: the section `1` of `Λ_P` over `P`; `freeToUnit : Λ[etId P] ⟶ Λ_P` (`taut ↦ 1`, `freeToUnit_taut`);
* `stalk_freeToUnit`: on stalks the germ of `taut` goes to `oneStalk`; **`isIso_freeToUnit`**, `unitIso`;
* `extUnit F n : H^n(P, F) ≃+ Ext^n(Λ[etId P], F)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg
  RamanujanPetersson.EtPBC.FreeStk RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] (P : Scheme.{u})

/-- `Λ[P] ⟶ Λ_P`, `taut ↦ 1`. -/
def freeToUnit : freeSh Λ (etId P) ⟶ unitSh Λ P := (freeEquiv Λ (etId P) (unitSh Λ P)).symm (oneSec Λ P)

variable {Λ P}

theorem freeToUnit_taut :
    ((freeToUnit Λ P).hom.app (op (etId P))).hom (taut Λ (etId P)) = oneSec Λ P := by
  have h := freeEquiv_comp Λ (etId P) (𝟙 (freeSh Λ (etId P))) (freeToUnit Λ P)
  rw [Category.id_comp] at h
  refine Eq.trans ?_ (h.symm.trans ?_)
  · rfl
  · rw [freeToUnit, AddEquiv.apply_symm_apply]

theorem stalk_freeToUnit (x : P) :
    (((geomPtAt x).stalkF Λ).map (freeToUnit Λ P)).hom
      (germ (freeSh Λ (etId P)) x (topPt x) (taut Λ (etId P))) = oneStalk Λ x := by
  rw [germ_natural, freeToUnit_taut]
  exact congrArg (fun φ => φ.hom (1 : Λ)) (constUnit_germ (geomPtAt x) (ModuleCat.of Λ Λ) (etId P) (topPt x))

theorem free_top_gen (x : P) (v : stalk Λ (freeSh Λ (etId P)) x) :
    ∃ c : Λ, v = c • germ (freeSh Λ (etId P)) x (topPt x) (taut Λ (etId P)) := by
  obtain ⟨l, rfl⟩ := freeLin_surjective (Λ := Λ) (etId P) x v
  refine ⟨l (topPt x), ?_⟩
  have hl : l = Finsupp.single (topPt x) (l (topPt x)) :=
    Finsupp.ext fun a => by rw [Subsingleton.elim a (topPt x), Finsupp.single_eq_same]
  conv_lhs => rw [hl]
  rw [freeLin, Finsupp.linearCombination_single]

theorem stalk_freeToUnit_smul (x : P) (c : Λ) :
    (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom.hom ((((geomPtAt x).stalkF Λ).map (freeToUnit Λ P)).hom
      (c • germ (freeSh Λ (etId P)) x (topPt x) (taut Λ (etId P)))) = c := by
  rw [map_smul, stalk_freeToUnit, map_smul, oneStalk_hom, smul_eq_mul, mul_one]

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Pf =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Pf: pullback of free sheaves

For `f : X ⟶ Y` and `W : Y.Etale`:
* `pullTaut`: the pullback of the tautological section, a section of `f^*Λ[W]` over `f^{-1}W`;
* `pullFreeHom : Λ[f^{-1}W] ⟶ f^*Λ[W]` (`taut ↦ pullTaut`), `pullFreeInv` (adjoint to `taut`);
* **`pullFreeIso`**: `Λ[f^{-1}W] ≅ f^*Λ[W]`; **`pullFreeHom_natural`**: natural in `W`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg
  RamanujanPetersson.EtPBC.FreeStk

universe u

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

variable (Λ) in
/-- The pullback of the tautological section of `Λ[W]`. -/
def pullTaut (W : Y.Etale) : ((pull f Λ).obj (freeSh Λ W)).obj.obj (op ((etPull f).obj W)) :=
  (((pullAdj f Λ).unit.app (freeSh Λ W)).hom.app (op W)).hom (taut Λ W)

variable (Λ) in
/-- `Λ[f^{-1}W] ⟶ f^*Λ[W]`. -/
def pullFreeHom (W : Y.Etale) : freeSh Λ ((etPull f).obj W) ⟶ (pull f Λ).obj (freeSh Λ W) :=
  (freeEquiv Λ ((etPull f).obj W) ((pull f Λ).obj (freeSh Λ W))).symm (pullTaut Λ f W)

variable (Λ) in
/-- The tautological section of `Λ[f^{-1}W]`, as a section of `f_*Λ[f^{-1}W]` over `W`. -/
def pushTaut (W : Y.Etale) : ((push f Λ).obj (freeSh Λ ((etPull f).obj W))).obj.obj (op W) :=
  taut Λ ((etPull f).obj W)

variable (Λ) in
/-- `f^*Λ[W] ⟶ Λ[f^{-1}W]`, adjoint to the tautological section of `Λ[f^{-1}W]`. -/
def pullFreeInv (W : Y.Etale) : (pull f Λ).obj (freeSh Λ W) ⟶ freeSh Λ ((etPull f).obj W) :=
  ((pullAdj f Λ).homEquiv _ _).symm
    ((freeEquiv Λ W ((push f Λ).obj (freeSh Λ ((etPull f).obj W)))).symm (pushTaut Λ f W))

theorem pullFreeHom_taut (W : Y.Etale) :
    ((pullFreeHom Λ f W).hom.app (op ((etPull f).obj W))).hom (taut Λ ((etPull f).obj W)) = pullTaut Λ f W := by
  have h := freeEquiv_comp Λ ((etPull f).obj W) (𝟙 (freeSh Λ ((etPull f).obj W))) (pullFreeHom Λ f W)
  rw [Category.id_comp] at h
  refine Eq.trans ?_ (h.symm.trans ?_)
  · rfl
  · rw [pullFreeHom, AddEquiv.apply_symm_apply]

theorem freeEquiv_unit (W : Y.Etale) :
    freeEquiv Λ W _ ((pullAdj f Λ).unit.app (freeSh Λ W)) = pullTaut Λ f W := by
  have h := freeEquiv_comp Λ W (𝟙 (freeSh Λ W)) ((pullAdj f Λ).unit.app (freeSh Λ W))
  rw [Category.id_comp] at h
  exact h

theorem pullFreeInv_adj (W : Y.Etale) :
    (pullAdj f Λ).unit.app (freeSh Λ W) ≫ (push f Λ).map (pullFreeInv Λ f W) =
      (freeEquiv Λ W ((push f Λ).obj (freeSh Λ ((etPull f).obj W)))).symm (pushTaut Λ f W) := by
  have h1 : (pullAdj f Λ).homEquiv _ _ (pullFreeInv Λ f W) =
      (freeEquiv Λ W ((push f Λ).obj (freeSh Λ ((etPull f).obj W)))).symm (pushTaut Λ f W) :=
    Equiv.apply_symm_apply _ _
  exact ((pullAdj f Λ).homEquiv_unit _ _ _).symm.trans h1

theorem pullFree_hom_inv (W : Y.Etale) : pullFreeHom Λ f W ≫ pullFreeInv Λ f W = 𝟙 _ := by
  apply (freeEquiv Λ ((etPull f).obj W) (freeSh Λ ((etPull f).obj W))).injective
  rw [freeEquiv_comp, pullFreeHom, AddEquiv.apply_symm_apply]
  have h2 := congrArg (freeEquiv Λ W ((push f Λ).obj (freeSh Λ ((etPull f).obj W)))) (pullFreeInv_adj f W)
  rw [freeEquiv_comp, AddEquiv.apply_symm_apply] at h2
  exact (congrArg (fun z => (((push f Λ).map (pullFreeInv Λ f W)).hom.app (op W)).hom z)
    (freeEquiv_unit f W).symm).trans h2

theorem pullFree_inv_hom (W : Y.Etale) : pullFreeInv Λ f W ≫ pullFreeHom Λ f W = 𝟙 _ := by
  apply ((pullAdj f Λ).homEquiv (freeSh Λ W) ((pull f Λ).obj (freeSh Λ W))).injective
  rw [Adjunction.homEquiv_naturality_right, pullFreeInv, Equiv.apply_symm_apply, Adjunction.homEquiv_id]
  apply (freeEquiv Λ W _).injective
  rw [freeEquiv_comp, AddEquiv.apply_symm_apply]
  exact (pullFreeHom_taut f W).trans (freeEquiv_unit f W).symm

variable (Λ) in
/-- **`Λ[f^{-1}W] ≅ f^*Λ[W]`.** -/
def pullFreeIso (W : Y.Etale) : freeSh Λ ((etPull f).obj W) ≅ (pull f Λ).obj (freeSh Λ W) where
  hom := pullFreeHom Λ f W
  inv := pullFreeInv Λ f W
  hom_inv_id := pullFree_hom_inv f W
  inv_hom_id := pullFree_inv_hom f W

/-- **Naturality**: `Λ[f^{-1}w] ≫ (Λ[f^{-1}W] → f^*Λ[W]) = (Λ[f^{-1}W'] → f^*Λ[W']) ≫ f^*Λ[w]`. -/
theorem pullFreeHom_natural {W' W : Y.Etale} (w : W' ⟶ W) :
    freeMap Λ ((etPull f).map w) ≫ pullFreeHom Λ f W = pullFreeHom Λ f W' ≫ (pull f Λ).map (freeMap Λ w) := by
  apply (freeEquiv Λ ((etPull f).obj W') ((pull f Λ).obj (freeSh Λ W))).injective
  rw [freeEquiv_freeMap, freeEquiv_comp, pullFreeHom, pullFreeHom, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  have hn : (((pullAdj f Λ).unit.app (freeSh Λ W)).hom.app (op W')).hom
        (((freeMap Λ w).hom.app (op W')).hom (taut Λ W')) =
      (((pull f Λ).map (freeMap Λ w)).hom.app (op ((etPull f).obj W'))).hom (pullTaut Λ f W') :=
    congrArg (fun φ => (φ.hom.app (op W')).hom (taut Λ W')) ((pullAdj f Λ).unit.naturality (freeMap Λ w))
  rw [freeMap_taut] at hn
  have hu := NatTrans.naturality_apply (φ := ((pullAdj f Λ).unit.app (freeSh Λ W)).hom) w.op (taut Λ W)
  exact hu.symm.trans hn

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L1 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes

* `mvMapHom`, **`mv_naturality`**: a morphism of MV data gives a morphism of MV complexes, so
  `ε₁ ∘ Λ[a'] = Λ[c] ∘ ε₂` in `Ext¹`.
* `mvPullHom`: `mvC(f⁻¹ data) ⟶ f^* mvC(data)` (an isomorphism), `mvPull_shortExact`;
  **`mapExact_mv`**: `f^*` of `ε.comp κ` is `ε(f⁻¹ data).comp (f^* κ)`.
* `freeToUnit_bcUnit`, **`bc_mv`**: the base change of `ε.comp κ` at a neighbourhood `j` of `s` is
  `σ_j^*(ε(ι⁻¹ data).comp (ι^* κ))`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe u

section Nat

end Nat

section Pull

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

instance isIso_pullFreeHom (W : Y.Etale) : IsIso (pullFreeHom Λ f W) := (pullFreeIso Λ f W).isIso_hom

variable {W' W U Z : Y.Etale} (p₁ : W' ⟶ W) (p₂ : W' ⟶ U) (w : W ⟶ Z) (v : U ⟶ Z) (hsq : p₁ ≫ w = p₂ ≫ v)

variable (Λ) in
/-- The middle comparison `Λ[f⁻¹W] ⊞ Λ[f⁻¹U] ⟶ f^*(Λ[W] ⊞ Λ[U])`. -/
def pullMid (A B : Y.Etale) :
    freeSh Λ ((etPull f).obj A) ⊞ freeSh Λ ((etPull f).obj B) ⟶ (pull f Λ).obj (freeSh Λ A ⊞ freeSh Λ B) :=
  biprod.map (pullFreeHom Λ f A) (pullFreeHom Λ f B) ≫ ((pull f Λ).mapBiprod (freeSh Λ A) (freeSh Λ B)).inv

theorem inl_pullMid (A B : Y.Etale) :
    biprod.inl ≫ pullMid Λ f A B = pullFreeHom Λ f A ≫ (pull f Λ).map biprod.inl := by
  simp only [pullMid, Functor.mapBiprod_inv, biprod.inl_map_assoc, biprod.inl_desc]

theorem inr_pullMid (A B : Y.Etale) :
    biprod.inr ≫ pullMid Λ f A B = pullFreeHom Λ f B ≫ (pull f Λ).map biprod.inr := by
  simp only [pullMid, Functor.mapBiprod_inv, biprod.inr_map_assoc, biprod.inr_desc]

instance isIso_pullMid (A B : Y.Etale) : IsIso (pullMid Λ f A B) := by
  have : IsIso (biprod.map (pullFreeHom Λ f A) (pullFreeHom Λ f B)) :=
    (biprod.mapIso (pullFreeIso Λ f A) (pullFreeIso Λ f B)).isIso_hom
  unfold pullMid
  infer_instance

end Pull

section BC

end BC

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Fl =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero

For an etale `e : U ⟶ X` and `V : U.Etale`:
* `res e` is additive and exact (left and right adjoint);
* **`lshFreeIso`**: `Λ[e ∘ V] ≅ e_! Λ[V]`.
For `W : P.Etale`:
* **`freeLshIso`**: `Λ[W] ≅ e_! Λ_W` (`e = W.hom`);
* **`extFree`**: `Ext_P(Λ[W], F) ≃ H(W, F|_W)`, with `extFree_comp_mk₀` (natural in `F`) and `ext_free_eq_zero`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ]

section Free

variable {U X : Scheme.{u}} (e : U ⟶ X) [Etale e]

variable (Λ) in
/-- The tautological section of `Λ[e ∘ V]`, as a section of `res e Λ[e ∘ V]` over `V`. -/
def resTaut (V : U.Etale) : ((res e Λ).obj (freeSh Λ ((etComp e).obj V))).obj.obj (op V) :=
  taut Λ ((etComp e).obj V)

variable (Λ) in
/-- The image of the tautological section of `Λ[V]` in `e_! Λ[V]` over `e ∘ V`. -/
def lshTaut (V : U.Etale) : ((lsh e Λ).obj (freeSh Λ V)).obj.obj (op ((etComp e).obj V)) :=
  (((lshAdj e Λ).unit.app (freeSh Λ V)).hom.app (op V)).hom (taut Λ V)

variable (Λ) in
/-- `Λ[e ∘ V] ⟶ e_! Λ[V]` (`taut ↦ lshTaut`). -/
def lshFreeHom (V : U.Etale) : freeSh Λ ((etComp e).obj V) ⟶ (lsh e Λ).obj (freeSh Λ V) :=
  (freeEquiv Λ ((etComp e).obj V) ((lsh e Λ).obj (freeSh Λ V))).symm (lshTaut Λ e V)

variable (Λ) in
/-- `e_! Λ[V] ⟶ Λ[e ∘ V]`, adjoint to the tautological section. -/
def lshFreeInv (V : U.Etale) : (lsh e Λ).obj (freeSh Λ V) ⟶ freeSh Λ ((etComp e).obj V) :=
  ((lshAdj e Λ).homEquiv _ _).symm
    ((freeEquiv Λ V ((res e Λ).obj (freeSh Λ ((etComp e).obj V)))).symm (resTaut Λ e V))

theorem lshFreeHom_taut (V : U.Etale) :
    ((lshFreeHom Λ e V).hom.app (op ((etComp e).obj V))).hom (taut Λ ((etComp e).obj V)) =
      lshTaut Λ e V := by
  have h := freeEquiv_comp Λ ((etComp e).obj V) (𝟙 (freeSh Λ ((etComp e).obj V))) (lshFreeHom Λ e V)
  rw [Category.id_comp] at h
  refine Eq.trans ?_ (h.symm.trans ?_)
  · rfl
  · rw [lshFreeHom, AddEquiv.apply_symm_apply]

theorem freeEquiv_lshUnit (V : U.Etale) :
    freeEquiv Λ V _ ((lshAdj e Λ).unit.app (freeSh Λ V)) = lshTaut Λ e V := by
  have h := freeEquiv_comp Λ V (𝟙 (freeSh Λ V)) ((lshAdj e Λ).unit.app (freeSh Λ V))
  rw [Category.id_comp] at h
  exact h

theorem lshFreeInv_adj (V : U.Etale) :
    (lshAdj e Λ).unit.app (freeSh Λ V) ≫ (res e Λ).map (lshFreeInv Λ e V) =
      (freeEquiv Λ V ((res e Λ).obj (freeSh Λ ((etComp e).obj V)))).symm (resTaut Λ e V) := by
  have h1 : (lshAdj e Λ).homEquiv _ _ (lshFreeInv Λ e V) =
      (freeEquiv Λ V ((res e Λ).obj (freeSh Λ ((etComp e).obj V)))).symm (resTaut Λ e V) :=
    Equiv.apply_symm_apply _ _
  exact ((lshAdj e Λ).homEquiv_unit _ _ _).symm.trans h1

theorem lshFree_hom_inv (V : U.Etale) : lshFreeHom Λ e V ≫ lshFreeInv Λ e V = 𝟙 _ := by
  apply (freeEquiv Λ ((etComp e).obj V) (freeSh Λ ((etComp e).obj V))).injective
  rw [freeEquiv_comp, lshFreeHom, AddEquiv.apply_symm_apply]
  have h2 := congrArg (freeEquiv Λ V ((res e Λ).obj (freeSh Λ ((etComp e).obj V)))) (lshFreeInv_adj e V)
  rw [freeEquiv_comp, AddEquiv.apply_symm_apply] at h2
  exact (congrArg (fun z => (((res e Λ).map (lshFreeInv Λ e V)).hom.app (op V)).hom z)
    (freeEquiv_lshUnit e V).symm).trans h2

theorem lshFree_inv_hom (V : U.Etale) : lshFreeInv Λ e V ≫ lshFreeHom Λ e V = 𝟙 _ := by
  apply ((lshAdj e Λ).homEquiv (freeSh Λ V) ((lsh e Λ).obj (freeSh Λ V))).injective
  rw [Adjunction.homEquiv_naturality_right, lshFreeInv, Equiv.apply_symm_apply, Adjunction.homEquiv_id]
  apply (freeEquiv Λ V _).injective
  rw [freeEquiv_comp, AddEquiv.apply_symm_apply]
  exact (lshFreeHom_taut e V).trans (freeEquiv_lshUnit e V).symm

variable (Λ) in
/-- **`Λ[e ∘ V] ≅ e_! Λ[V]`.** -/
def lshFreeIso (V : U.Etale) : freeSh Λ ((etComp e).obj V) ≅ (lsh e Λ).obj (freeSh Λ V) where
  hom := lshFreeHom Λ e V
  inv := lshFreeInv Λ e V
  hom_inv_id := lshFree_hom_inv e V
  inv_hom_id := lshFree_inv_hom e V

end Free

section GenFl

universe w₁ v₁ u₁ v₂ u₂

end GenFl

section Obj

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Fl2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`

* `extAdjMap_mk₀_comp`: the adjunction map on `Ext` is natural in the source;
* `lshFreeHom_natural`, `lshFreeInv_natural`: `Λ[e ∘ V] ≅ e_! Λ[V]` is natural in `V`;
* `toW W V : e ∘ V ⟶ W` (`e = W.hom`, `V : W.left.Etale`), `extFreeV : Ext_P(Λ[e ∘ V], F) ≃ Ext_W(Λ[V], F|_W)`;
* **`extFreeV_restrict`**: restricting `β ∈ Ext_P(Λ[W], F)` along `toW W V` is restricting `extFree β ∈ H(W, F|_W)`
  to `V`; **`restrict_eq_zero`**: if `extFree β` dies on `V`, then `β` dies on `e ∘ V`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe w v v' u₁ u₂ u

section Adj

end Adj

variable {Λ : Type u} [CommRing Λ]

section Nat

variable {U X : Scheme.{u}} (e : U ⟶ X) [Etale e]

theorem lshFreeIso_hom (V : U.Etale) : (lshFreeIso Λ e V).hom = lshFreeHom Λ e V := rfl

theorem lshFreeIso_inv (V : U.Etale) : (lshFreeIso Λ e V).inv = lshFreeInv Λ e V := rfl

end Nat

section Obj

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2R1 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M6a (1): the free sheaf on a coproduct is a biproduct; fibres of a coproduct

For a family `S : ι → P.Etale` with coproduct `cop S` (`Cech.cop`):
* `freeCop_hom_ext`: maps out of `Λ[cop S]` agree if they agree on every `Λ[S k]`;
* `copPr Λ S z : Λ[cop S] ⟶ Λ[S z]` with `copι_copPr_self`, `copι_copPr_ne`, **`sum_copPr`**
  (`Σ z, copPr z ≫ Λ[copι z] = 𝟙`);
* fibres: `fib_cop_surj` (every fibre point of `cop S` comes from some `S k`), `fib_cop_idx` (from one `k` only),
  `fib_cop_inj` (`copι k` is injective on fibres).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} (S : ι → P.Etale)

/-- Maps out of `Λ[cop S]` are determined on the summands. -/
theorem freeCop_hom_ext {F : EtSh Λ P} {f g : freeSh Λ (cop S) ⟶ F}
    (h : ∀ k, freeMap Λ (copι S k) ≫ f = freeMap Λ (copι S k) ≫ g) : f = g := by
  apply (freeEquiv Λ (cop S) F).injective
  refine sep_of_cover F (copι S) (cop_cover S) _ _ (fun k => ?_)
  have h1 := freeEquiv_freeMap Λ (copι S k) F f
  have h2 := freeEquiv_freeMap Λ (copι S k) F g
  rw [h k] at h1
  exact h1.symm.trans h2

section Fib

end Fib

variable [DecidableEq ι]

variable (Λ) in
/-- **The projection** `Λ[cop S] ⟶ Λ[S z]`. -/
def copPr (z : ι) : freeSh Λ (cop S) ⟶ freeSh Λ (S z) :=
  (freeEquiv Λ (cop S) _).symm (Classical.choose (cop_glue S (freeSh Λ (S z))
    (fun k => freeEquiv Λ (S k) _ (copPrSec S z k))))

theorem copι_copPr (z k : ι) : freeMap Λ (copι S k) ≫ copPr Λ S z = copPrSec S z k := by
  apply (freeEquiv Λ (S k) _).injective
  rw [freeEquiv_freeMap]
  have hs := Classical.choose_spec (cop_glue S (freeSh Λ (S z))
    (fun k => freeEquiv Λ (S k) _ (copPrSec (Λ := Λ) S z k))) k
  refine Eq.trans ?_ hs
  show (freeSh Λ (S z)).obj.map (copι S k).op ((freeEquiv Λ (cop S) _)
    ((freeEquiv Λ (cop S) _).symm _)) = _
  rw [AddEquiv.apply_symm_apply]

theorem copι_copPr_self (z : ι) : freeMap Λ (copι S z) ≫ copPr Λ S z = 𝟙 _ := by
  rw [copι_copPr, copPrSec_self]

theorem copι_copPr_ne {z k : ι} (h : k ≠ z) : freeMap Λ (copι S k) ≫ copPr Λ S z = 0 := by
  rw [copι_copPr, copPrSec_ne S h]

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2R3 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M6a (3): the multi-point MV complex maps to each one-point complex

For `k : ι`, an open `Uz ⊇ U₀` containing every point of every `S j` (`j ≠ k`):
* `copDescF` (maps out of `Λ[cop S]` from maps on the summands), `copι_copDescF`;
* `restSec`, `locτ₂`: the middle map `Λ[cop S] ⊞ Λ[U₀] ⟶ Λ[S k] ⊞ Λ[Uz]`;
* `loc_comm₁₂`, `loc_comm₂₃`, **`mvLocHom`**: a morphism of short complexes `mvCop ⟶ locC (S k)` with
  `τ₁ = copPr k` and `τ₃ = 𝟙`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  (S : ι → P.Etale)

variable (Λ) in
/-- The map out of `Λ[cop S]` with given restrictions to the summands. -/
def copDescF {G : EtSh Λ P} (φ : ∀ j, freeSh Λ (S j) ⟶ G) : freeSh Λ (cop S) ⟶ G :=
  ∑ j, copPr Λ S j ≫ φ j

theorem copDescF_eq {G : EtSh Λ P} (φ : ∀ j, freeSh Λ (S j) ⟶ G) :
    copDescF Λ S φ = ∑ j, copPr Λ S j ≫ φ j := rfl

variable (U₀ : P.Opens) (k : ι) {Uz : P.Opens} (h : U₀ ≤ Uz)
  (hrng : ∀ j, j ≠ k → ∀ v : (S j).left, (S j).hom v ∈ Uz)

variable (Λ) in
/-- The middle map `Λ[cop S] ⊞ Λ[U₀] ⟶ Λ[S k] ⊞ Λ[Uz]`. -/
def locτ₂ : freeSh Λ (cop S) ⊞ freeSh Λ (opEt U₀) ⟶ freeSh Λ (S k) ⊞ freeSh Λ (opEt Uz) :=
  biprod.desc (biprod.lift (copPr Λ S k) (copDescF Λ S (restSec Λ S k hrng)))
    (biprod.lift 0 (freeMap Λ (opEtMap h)))

theorem locτ₂_eq : locτ₂ Λ S U₀ k h hrng = biprod.desc (biprod.lift (copPr Λ S k) (copDescF Λ S (restSec Λ S k hrng)))
    (biprod.lift 0 (freeMap Λ (opEtMap h))) := rfl

end RamanujanPetersson.EtPBC.EtMV

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

/-! ### `Λ_U ⟶ g^* Λ_X` -/

theorem freeEquiv_symm_taut {P : Scheme.{u}} (W : P.Etale) (F : EtSh Λ P) (s : F.obj.obj (op W)) :
    (((freeEquiv Λ W F).symm s).hom.app (op W)).hom (taut Λ W) = s := by
  have h := freeEquiv_comp Λ W (𝟙 (freeSh Λ W)) ((freeEquiv Λ W F).symm s)
  rw [Category.id_comp] at h
  refine Eq.trans ?_ (h.symm.trans ?_)
  · rfl
  · rw [AddEquiv.apply_symm_apply]

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T1 =====
section

/-!
# S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps

* `resFreeIso Λ e T : Λ_U[e⁻¹T] ≅ (Λ[T])|_U` for etale `e : U ⟶ X` (`pullFreeIso` + `pullIsoRes`);
* `resFreeIso_taut`: its value on the tautological section is the pullback of `taut T` along the counit;
* `graph m : etId W.left ⟶ e⁻¹T` for `m : W ⟶ T` in `P.Etale` (adjoint to `W ≅ etComp (etId) ⟶ T`);
* `secMap Λ m := diagSec Λ W ≫ (res W.hom Λ).map Λ[m] : Λ_W ⟶ (Λ[T])|_W`, `secMap_comp`;
* **`secMap_graph`**: `unitIso.hom ≫ secMap m = Λ[graph m] ≫ resFreeIso.hom`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe u

section Res

variable (Λ : Type u) [CommRing Λ] {U X : Scheme.{u}} (e : U ⟶ X) [Etale e]

/-- **`Λ_U[e⁻¹T] ≅ Λ[T]|_U`** for etale `e`. -/
def resFreeIso (T : X.Etale) : freeSh Λ ((etPull e).obj T) ≅ (res e Λ).obj (freeSh Λ T) :=
  pullFreeIso Λ e T ≪≫ (pullIsoRes e Λ).app (freeSh Λ T)

theorem resFreeIso_taut (T : X.Etale) :
    freeEquiv Λ _ _ (resFreeIso Λ e T).hom =
      ((freeSh Λ T).obj.map ((etCompAdj e).counit.app T).op).hom (taut Λ T) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (pullAdj e Λ) (resAdj e Λ) (freeSh Λ T)
  have h2 := congrArg (fun φ => ((φ.hom.app (op T)).hom (taut Λ T))) h
  rw [resFreeIso, Iso.trans_hom, Iso.app_hom, freeEquiv_comp]
  show ((((pullIsoRes e Λ).hom.app (freeSh Λ T)).hom.app (op ((etPull e).obj T))).hom
    (freeEquiv Λ _ _ (pullFreeHom Λ e T))) = _
  rw [pullFreeHom, AddEquiv.apply_symm_apply, pullTaut]
  exact h2

end Res

section Graph

end Graph

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

/-- `Λ[W] = 0` when `W` is empty. -/
theorem isZero_freeSh_of_isEmpty {X : Scheme.{u}} (Λ : Type u) [CommRing Λ] (W : X.Etale) (hW : IsEmpty W.left) :
    IsZero (freeSh Λ W) := by
  rw [IsZero.iff_id_eq_zero]
  apply (freeEquivT Λ W (freeSh Λ W)).injective
  have := (ModuleCat.isZero_iff_subsingleton).1 (isZero_obj_of_isEmpty Λ (freeSh Λ W) W hW)
  exact Subsingleton.elim _ _

end Zero

section GenZero

universe w' v₁ u₁ v₂ u₂ v₃ u₃

end GenZero

section Good

end Good

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB2a =====
section

/-!
# S4-EtPBC-A, L3b (TB2a): section calculus for base change

* `etPull_hom_ext`: maps into `X ×_Y T` agree if their first components agree;
* `etIdPull g : etId X ≅ X ×_Y Y`, `pullUnit g : Λ_X ≅ g^*Λ_Y`, `pullUnit_one`;
* `unit_hom_ext`: maps out of `Λ_X` are determined by the image of `1`;
* transport of pulled-back sections along `pullIsoRes`, `pullCompIso`, `pullCongr`, `(pull g).map`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

section TB2

end TB2

section TB2o

/-! Op-form section calculus: restriction maps are op-morphisms `a : op T ⟶ op Z` that are passed through
unchanged, so consecutive steps meet in syntactically equal terms (this keeps kernel checks cheap). -/

variable {Λ : Type u} [CommRing Λ]

theorem resPullFree_secO {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Etale) (T : Y.Etale)
    (r : op ((etPull f).obj T) ⟶ op ((etComp V.hom).obj (etId V.left))) :
    ((((res V.hom Λ).map (pullFreeHom Λ f T)).hom.app (op (etId V.left))).hom
        (((freeSh Λ ((etPull f).obj T)).obj.map r).hom (taut Λ ((etPull f).obj T)))) =
      ((((pull f Λ).obj (freeSh Λ T)).obj.map r).hom (pbSec f (taut Λ T))) := by
  refine (res_map_app V.hom (pullFreeHom Λ f T) (etId V.left) _).trans ?_
  show _ = ((((pull f Λ).obj (freeSh Λ T)).obj.map r).hom (pullTaut Λ f T))
  rw [← pullFreeHom_taut (Λ := Λ) f T]
  exact congrArg (fun ψ => ψ.hom (taut Λ ((etPull f).obj T))) ((pullFreeHom Λ f T).hom.naturality r)

end TB2o

end RamanujanPetersson.EtPBC.EtMV

end

end


