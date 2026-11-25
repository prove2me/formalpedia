-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_088
-- name    : RPLib_FX_EtPBC_088
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:58:52.48049+00:00
-- url     : https://prove2.me/theorems/21900f18-45fd-5456-86a4-77ad67c8c86c
-- title:
--   Proper base change for the projective line, library file 088
-- statement:
--   File 088 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovLim3`: S4-EtPBC-A, R4-T2 (A2c-2c): generation of sections at every level by finitely many compatible families
--   * `S4.Def_RP_EtPBC_A_CovPr14`: S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts
--   * `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
--   * `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_FBCv`: S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre
--   * `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
--   * `S4.Def_RP_EtPBC_A_O2L1`: S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes
--   * `S4.Def_RP_EtPBC_A_O2Gl2h`: S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`
--   * `S4.Def_RP_EtPBC_A_O2Rel1`: S4-EtPBC-A, O2 REL (O2Rel1): a bad term of the relation as a class on a small nbhd over `U₀`
--   * `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
--   * `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
--   * `S4.Def_RP_EtPBC_A_O2L6b3`: S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`
--   * `S4.Def_RP_EtPBC_A_O2L6c1`: S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_077
import Definitions.Def_RPLib_FX_EtPBC_079
import Definitions.Def_RPLib_FX_EtPBC_081

/-!
# Proper base change for the projective line, library file 088

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovLim3`: S4-EtPBC-A, R4-T2 (A2c-2c): generation of sections at every level by finitely many compatible families
* `S4.Def_RP_EtPBC_A_CovPr14`: S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts
* `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
* `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
* `S4.Def_RP_EtPBC_A_FBCv`: S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre
* `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
* `S4.Def_RP_EtPBC_A_O2L1`: S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes
* `S4.Def_RP_EtPBC_A_O2Gl2h`: S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`
* `S4.Def_RP_EtPBC_A_O2Rel1`: S4-EtPBC-A, O2 REL (O2Rel1): a bad term of the relation as a class on a small nbhd over `U₀`
* `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
* `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
* `S4.Def_RP_EtPBC_A_O2L6b3`: S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`
* `S4.Def_RP_EtPBC_A_O2L6c1`: S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovLim3 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2c): generation of sections at every level by finitely many compatible families

For compatible families `σ : Fin r → Gam C H d` whose level-`0` combinations give all level-`0` sections:
* `gen_mod_p`: every level-`m` section is a combination of the `σᵢ` modulo `p`;
* `gen_step`: a section with entries in `p^n` is a combination with coefficients in `p^n` modulo `p^(n+1)`
  (from `FilProp` at every level);
* **`gen_lev`**: a level-`m` section with entries in `p^j` is a combination with coefficients in `p^j`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Gen

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) {r : ℕ} (σ : Fin r → (∀ k, (C k).E₀) × (∀ k, (C k).E₁)) {g : ℕ}
  (α : Fin g → R)

/-- **Every level-`m` section is a combination of the `σᵢ` modulo `p`.** -/
theorem gen_mod_p (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) {d : ℕ} (hσ : ∀ i, σ i ∈ Gam C H d)
    (hgen0 : ∀ y ∈ (C 0).sec d, ∃ c, y = lev C ιB₀ ιB₁ σ 0 c) :
    ∀ m, ∀ y ∈ (C m).sec d, ∃ c : Fin r → R,
      (y - lev C ιB₀ ιB₁ σ m c).1 ∈ (p ^ 1).map (lι₀ ιB₀ (C m)) ∧
      (y - lev C ιB₀ ιB₁ σ m c).2 ∈ (p ^ 1).map (lι₁ ιB₁ (C m)) := by
  intro m
  induction m with
  | zero =>
    intro y hy
    obtain ⟨c, hc⟩ := hgen0 y hy
    refine ⟨c, ?_, ?_⟩
    · rw [hc, sub_self]
      exact Ideal.zero_mem _
    · rw [hc, sub_self]
      exact Ideal.zero_mem _
  | succ m ih =>
    intro y hy
    have hy' : ((H m).ρ₀ y.1, (H m).ρ₁ y.2) ∈ (C m).sec d :=
      ((H m).secMap (Ideal.Quotient.factor_mk _ _) d ⟨y, hy⟩).2
    obtain ⟨c, hc₀, hc₁⟩ := ih _ hy'
    refine ⟨c, mem_of_ρ₀ ιB₀ p (H m) hJ₀ (by omega) ?_, mem_of_ρ₁ ιB₁ p (H m) hJ₁ (by omega) ?_⟩
    · rw [Prod.fst_sub, map_sub, lev_ρ₀ C H ιB₀ ιB₁ σ hσ m c]
      simpa only [Prod.fst_sub] using hc₀
    · rw [Prod.snd_sub, map_sub, lev_ρ₁ C H ιB₀ ιB₁ σ hσ m c]
      simpa only [Prod.snd_sub] using hc₁

end Gen

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovPr14 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts

With `fh = σh ⊗ id : C ⊗ B → Ah ⊗ B`, `f' = σ ⊗ id : C ⊗ B → R' ⊗ B`, `θh : Pres (gmap fh gC) → Q` restricting to
`kap res` on `Ah ⊗ B`:
* `exists_cov`, **`hκT`** (the compatibility needed by `resid`), `lamT` (`lamT_apply`, `lamT_hlam`);
* **`resid_surj_T`**, **`resid_ker_T`**: the residue `resid fh f' gC θh (kap χ') _` is onto with kernel
  `Jt B χ' · Pres (gmap f' gC)`, when `ker θh = pI · Pres` with `pI ≤ ker res`.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

variable {K A R' B Ah C Q : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B]
  [CommRing Ah] [Algebra A Ah] [CommRing C] [Algebra A C] [CommRing Q]
  (χ : A →+* K) (χ' : R' →+* K) (res : Ah →+* K)
  (hres : ∀ a, res (algebraMap A Ah a) = χ a) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a)
  (ν : K →+* Q) (βQ : B →+* Q) (hβ : ∀ a, βQ (algebraMap A B a) = ν (χ a))

variable {r : ℕ} (σh : C →ₐ[A] Ah) (σ : C →ₐ[A] R') (gC : Fin r → MvPolynomial (Fin r) (C ⊗[A] B))
  (θh : Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC) →+* Q)

/-- **The kernel of the residue** is `(ker χ') · Pres (gmap f' gC)`. -/
theorem resid_ker_T (s : K →+* R') (hs : ∀ k, χ' (s k) = k) (sh : K →+* Ah) (hsh : ∀ k, res (sh k) = k)
    (hσ : ∀ c, χ' (σ c) = res (σh c))
    (hθk : ∀ x, θh (algebraMap (Ah ⊗[A] B) (Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC))
      x) = kap χ ν βQ hβ res hres x) (hθ : Function.Surjective θh) (pI : Ideal Ah) (hp : ∀ x ∈ pI, res x = 0)
    (hI : RingHom.ker θh = (pI.map (Algebra.TensorProduct.includeLeftRingHom : Ah →+* Ah ⊗[A] B)).map
      (algebraMap (Ah ⊗[A] B) (Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC))))
    (hκ : (kap χ ν βQ hβ χ' hχ').comp (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom =
      (θh.comp (algebraMap (Ah ⊗[A] B)
        (Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC)))).comp
        (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom) :
    RingHom.ker (resid (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom
      (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC θh (kap χ ν βQ hβ χ' hχ') hκ) =
      (Jt B χ').map (algebraMap (R' ⊗[A] B) (Pres (gmap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC))) := by
  have hlamI : pI.map (Algebra.TensorProduct.includeLeftRingHom : Ah →+* Ah ⊗[A] B) ≤
      RingHom.ker (lamT χ χ' res hres hχ' σ gC s hs) := by
    intro x hx
    rw [RingHom.mem_ker, lamT_apply,
      RingHom.mem_ker.mp (I_le_ker_lamQ (B := B) χ χ' res s hres hχ' hs pI hp hx), map_zero]
  have hsec : ∀ a : R' ⊗[A] B, ∃ x : Ah ⊗[A] B,
      θh (algebraMap (Ah ⊗[A] B) (Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC)) x) =
        kap χ ν βQ hβ χ' hχ' a ∧
      lamT χ χ' res hres hχ' σ gC s hs x =
        presMap (Ideal.Quotient.mk (Jt B χ')) (gmap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC)
          (algebraMap (R' ⊗[A] B) (Pres (gmap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC)) a) := by
    intro a
    obtain ⟨x, h1, h2⟩ := exists_sec χ χ' res s hres hχ' hs ν βQ hβ sh hsh a
    exact ⟨x, (hθk x).trans h1, (congrArg (algebraMap ((R' ⊗[A] B) ⧸ Jt B χ')
      (Pres (gmap (Ideal.Quotient.mk (Jt B χ')) (gmap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC)))) h2).trans
      (presMap_algebraMap _ _ _).symm⟩
  exact resid_ker_pm _ _ gC θh _ hκ hθ (Jt B χ') (Jt_le_ker_kap χ ν βQ hβ χ' hχ')
    (lamT χ χ' res hres hχ' σ gC s hs) (lamT_hlam χ χ' res hres hχ' σh σ gC s hs hσ) _ hI hlamI hsec

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovY =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`

For an affine open `U ⊆ Y` (with `Γ(V) → Γ(Y, U)` the structure map), **`chY hU hA`** `: Spec (R' ⊗ Γ(Y, U)) ⟶ Y_{V'}`
is the base change of `hU.fromSpec` along `Y_{V'} ⟶ Y` (**`isPullback_chY`**), an open immersion with range
`fst⁻¹ U` (**`opensRange_chY`**), compatible with restrictions (**`chY_res`**).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

section Chart

variable {U : Y.Opens} (hU : IsAffineOpen U) [Algebra Γ(V, ⊤) Γ(Y, U)]
  (hA : CommRingCat.ofHom (algebraMap Γ(V, ⊤) Γ(Y, U)) = strU K gV π U)

theorem opensRange_chY : (chY K gV π R' hU hA).opensRange = pullback.fst (π ≫ qV K gV) (hV V R') ⁻¹ᵁ U := by
  have e := Scheme.Hom.opensRange_comp_of_isIso (isPullback_chY K gV π R' hU hA).isoPullback.hom
    (pullback.fst (pullback.fst (π ≫ qV K gV) (hV V R')) hU.fromSpec)
  simp only [IsPullback.isoPullback_hom_fst] at e
  rw [e, Scheme.Hom.opensRange_pullbackFst, hU.opensRange_fromSpec]

end Chart

section Res

end Res

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovCv =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`

`directed_of_range`: directedness of an open cover from its ranges. **`covV`**: the open cover of `Y_{V'} = Y ×_V Spec R'`
by the charts `Spec (R' ⊗ Γ(Y₀₁))`, `Spec (R' ⊗ Γ(Y₀))`, `Spec (R' ⊗ Γ(Y₁))`, indexed by `WalkingSpan`
(`zero ↦ Y₀₁`), with transition maps the `span` of the chart restrictions `a0`, `a1`; instance `LocallyDirected`.
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
  (π : Y ⟶ PV K gV) [IsAffine V] [IsAffineHom π] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

instance : IsOpenImmersion (ch01 K gV π R') := isOpenImmersion_chY K gV π R' _ (hA01 K gV π)

omit [IsAffineHom π] in
theorem range_ch {U : Y.Opens} (hU : IsAffineOpen U) [Algebra Γ(V, ⊤) Γ(Y, U)]
    (hA : CommRingCat.ofHom (algebraMap Γ(V, ⊤) Γ(Y, U)) = strU K gV π U) :
    Set.range (chY K gV π R' hU hA) = (oV K gV π R' U : Set (YV K gV π R')) := by
  rw [← Scheme.Hom.coe_opensRange, opensRange_chY]

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_FBCv =====
section

/-!
# S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre

For `π : Y ⟶ P` finite, a geometric point `t` of `P`, a neighbourhood `j` of `t` and any `v : π⁻¹(j) → M`, after
refining `j` there is a section `z` of `M_Y` over `π⁻¹(j')` whose values along the fibre `fib π t` are those of `v`.
* `PhiU`: `R' ⊗_{Γ(W)} Γ(U) → Γ(U')` for a square `U' → U → W`, `U' → Spec R' → W`; `comap_PhiU_left/right`;
* `exists_sec_vals_aff` (affine `j`), **`exists_sec_vals`** (Stacks 00UL via
  `Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.FBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.Z3

universe u

section Phi

end Phi

section Main

variable {Λ : Type u} [CommRing Λ] {Y P : Scheme.{u}} (π : Y ⟶ P) [IsFinite π] (t : GeomPt P)
  {M : ModuleCat.{u} Λ}

/-- **Prescribed values along the fibre**, affine neighbourhood. -/
theorem exists_sec_vals_aff (j : Nbhd t) [IsAffine j.1.left] (v : ↑(pullback j.1.hom π) → M) :
    ∃ (j' : Nbhd t) (_ : j' ⟶ j) (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj j'.1))),
      ∀ x : fib π t, cval z (fibToNbhd π t j' x) = v (fibToNbhd π t j x) := by
  classical
  letI algU : Algebra Γ(j.1.left, ⊤) Γ(pullback j.1.hom π, ⊤) := (pullback.fst j.1.hom π).appTop.hom.toAlgebra
  have : IsAffine ((𝟭 Scheme.{u}).obj j.1.left) := ‹IsAffine j.1.left›
  have : Module.Finite Γ(j.1.left, ⊤) Γ(pullback j.1.hom π, ⊤) := Scheme.Hom.finite_appTop (pullback.fst j.1.hom π)
  have : (PrimeSpectrum.asIdeal (j.1.left.toSpecΓ (nbv t j default))).IsPrime := PrimeSpectrum.isPrime _
  obtain ⟨R', _, _, _, P', _, hP', n, e, he, Q, _, _, -, -, hall⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq (S := Γ(pullback j.1.hom π, ⊤))
      (PrimeSpectrum.asIdeal (j.1.left.toSpecΓ (nbv t j default)))
  let v' : Spec (CommRingCat.of R') := ⟨P', inferInstance⟩
  have hv : (hV j.1.left R') v' = nbv t j default := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap Γ(j.1.left, ⊤) R')) v' =
        j.1.left.isoSpec.hom (nbv t j default) := PrimeSpectrum.ext hP'.over.symm
    have h2 := congrArg (fun φ => φ.base (nbv t j default)) j.1.left.isoSpec.hom_inv_id
    show j.1.left.isoSpec.inv (Spec.map (CommRingCat.ofHom (algebraMap Γ(j.1.left, ⊤) R')) v') = _
    rw [h1]
    exact h2
  let f : etR t j R' ⟶ j.1 := MorphismProperty.Over.homMk (hV j.1.left R') rfl trivial
  obtain ⟨b, hb, hbv⟩ := exists_lift_fib' t f j.2 v' hv
  let j' : Nbhd t := ⟨etR t j R', b⟩
  let a : j' ⟶ j := ⟨f, hb⟩
  have hf : ((etPull π).map a.1).left ≫ pullback.fst j.1.hom π = pullback.fst j'.1.hom π ≫ hV j.1.left R' :=
    etPull_map_left_fst π a.1
  letI algU' : Algebra Γ(j.1.left, ⊤) Γ(pullback j'.1.hom π, ⊤) :=
    (pullback.fst j'.1.hom π ≫ hV j.1.left R').appTop.hom.toAlgebra
  let Φ := PhiU (W := j.1.left) (U := pullback j.1.hom π) (U' := pullback j'.1.hom π)
      (pullback.fst j.1.hom π) R' (pullback.fst j'.1.hom π) ((etPull π).map a.1).left rfl rfl hf
  let q : fib π t → Ideal (R' ⊗[Γ(j.1.left, ⊤)] Γ(pullback j.1.hom π, ⊤)) := fun x =>
    Ideal.comap Φ (PrimeSpectrum.asIdeal ((pullback j'.1.hom π).toSpecΓ (fibToNbhd π t j' x)))
  have hsub : ∀ p : Spec (CommRingCat.of t.Ω), p = default := fun p =>
    Subsingleton.elim (α := PrimeSpectrum t.Ω) _ _
  have hfx : ∀ x : fib π t, (pullback.fst j'.1.hom π) (fibToNbhd π t j' x) = v' := by
    intro x
    have h := congrArg (fun φ => φ.base x) (fibToNbhd_fst π t j')
    refine h.trans ?_
    show (t.liftOf b).left (pullback.snd π t.pt x) = v'
    rw [hsub (pullback.snd π t.pt x)]
    exact hbv
  have hqp : ∀ x, (q x).IsPrime := fun x => by
    haveI := PrimeSpectrum.isPrime ((pullback j'.1.hom π).toSpecΓ (fibToNbhd π t j' x))
    exact Ideal.comap_isPrime _ _
  have hql : ∀ x, (q x).LiesOver P' := fun x =>
    ⟨((comap_PhiU_left (W := j.1.left) (U := pullback j.1.hom π) (U' := pullback j'.1.hom π)
      (pullback.fst j.1.hom π) R' (pullback.fst j'.1.hom π) ((etPull π).map a.1).left rfl rfl
      hf (fibToNbhd π t j' x)).trans (congrArg PrimeSpectrum.asIdeal (hfx x))).symm⟩
  have hex : ∀ x, ∃ i : Fin n, e i.castSucc ∉ q x := by
    intro x
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hall' : ∀ k, e k ∈ q x := by
      intro k
      refine Fin.lastCases ?_ (fun i => hcon i) k
      exact (hall (q x) (hqp x) (hql x)).1
    have h1 : (1 : R' ⊗[Γ(j.1.left, ⊤)] Γ(pullback j.1.hom π, ⊤)) ∈ q x := by
      rw [← he.complete]
      exact Ideal.sum_mem _ fun k _ => hall' k
    exact (hqp x).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have huniq : ∀ x (i k : Fin n), e i.castSucc ∉ q x → e k.castSucc ∉ q x → i = k := by
    intro x i k hi hk
    by_contra hik
    have h0 : e i.castSucc * e k.castSucc = 0 := he.ortho (fun h => hik (Fin.castSucc_injective n h))
    have h0' : e i.castSucc * e k.castSucc ∈ q x := by
      rw [h0]
      exact (q x).zero_mem
    exact ((hqp x).mem_or_mem h0').elim hi hk
  have himg : ∀ x₁ x₂ : fib π t, q x₁ = q x₂ → fibToNbhd π t j x₁ = fibToNbhd π t j x₂ := by
    intro x₁ x₂ hq
    have h1 := comap_PhiU_right (W := j.1.left) (U := pullback j.1.hom π) (U' := pullback j'.1.hom π)
      (pullback.fst j.1.hom π) R' (pullback.fst j'.1.hom π) ((etPull π).map a.1).left
      rfl rfl hf (fibToNbhd π t j' x₁)
    have h2 := comap_PhiU_right (W := j.1.left) (U := pullback j.1.hom π) (U' := pullback j'.1.hom π)
      (pullback.fst j.1.hom π) R' (pullback.fst j'.1.hom π) ((etPull π).map a.1).left
      rfl rfl hf (fibToNbhd π t j' x₂)
    have hq' := congrArg (Ideal.comap (Algebra.TensorProduct.includeRight :
      Γ(pullback j.1.hom π, ⊤) →ₐ[Γ(j.1.left, ⊤)] R' ⊗[Γ(j.1.left, ⊤)] Γ(pullback j.1.hom π, ⊤))) hq
    have h3 : (pullback j.1.hom π).toSpecΓ (((etPull π).map a.1).left (fibToNbhd π t j' x₁)) =
        (pullback j.1.hom π).toSpecΓ (((etPull π).map a.1).left (fibToNbhd π t j' x₂)) :=
      PrimeSpectrum.ext (h1.symm.trans (hq'.trans h2))
    have h4 := Scheme.Hom.injective _ h3
    have e1 := congrArg (fun φ => φ.base x₁) (fibToNbhd_map π t a)
    have e2 := congrArg (fun φ => φ.base x₂) (fibToNbhd_map π t a)
    exact e1.symm.trans (h4.trans e2)
  let D : Fin n → Set ((etPull π).obj j'.1).left := fun i =>
    (SetLike.coe ((pullback j'.1.hom π).basicOpen (Φ (e i.castSucc))) : Set ↑(pullback j'.1.hom π))
  have hD : ∀ i, IsClopen (D i) := fun i => isClopen_basicOpen ((he.idem i.castSucc).map Φ)
  have mem_D : ∀ x i, fibToNbhd π t j' x ∈ D i ↔ e i.castSucc ∉ q x := fun x i =>
    mem_basicOpen_iff (Φ (e i.castSucc)) (fibToNbhd π t j' x)
  let m : Fin n → M := fun i => if h : ∃ x, e i.castSucc ∉ q x then v (fibToNbhd π t j h.choose) else 0
  let c : Fin n → (constSh Λ Y M).obj.obj (op ((etPull π).obj j'.1)) := fun i =>
    (exists_indicator (Λ := Λ) (M := M) (T := (etPull π).obj j'.1) (D i) (hD i) (m i)).choose
  have hc : ∀ i w, cval (c i) w = (D i).indicator (fun _ => m i) w := fun i =>
    (exists_indicator (Λ := Λ) (M := M) (T := (etPull π).obj j'.1) (D i) (hD i) (m i)).choose_spec
  refine ⟨j', a, ∑ i, c i, fun x => ?_⟩
  obtain ⟨i₀, hi₀⟩ := hex x
  have hsum : ∑ i, cval (c i) (fibToNbhd π t j' x) = cval (c i₀) (fibToNbhd π t j' x) := by
    refine Finset.sum_eq_single i₀ (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ _) h)
    exact (hc k _).trans (Set.indicator_of_notMem (fun hk' => hk (huniq x k i₀ ((mem_D x k).1 hk') hi₀)) _)
  have hE : ∃ x', e i₀.castSucc ∉ q x' := ⟨x, hi₀⟩
  have hm : m i₀ = v (fibToNbhd π t j x) :=
    (dif_pos hE).trans (congrArg v (himg _ _ (((hall _ (hqp _) (hql _)).2 i₀ hE.choose_spec).trans
      ((hall _ (hqp x) (hql x)).2 i₀ hi₀).symm)))
  exact (cval_sum Finset.univ c (fibToNbhd π t j' x)).trans (hsum.trans ((hc i₀ _).trans
    ((Set.indicator_of_mem ((mem_D x i₀).2 hi₀) _).trans hm)))

end Main

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_T3dC =====
section

/-!
# S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly

`π : Y ⟶ P`, `f : P' ⟶ P`, `Φ : U ⟶ P'`, `h : U ⟶ Y` with `h ≫ π = Φ ≫ f`, `ι' : Ps ⟶ P'`, `ι = ι' ≫ f`:
* `hsU : U_s ⟶ Y_s` and `rUs : π_{s*} M_{Y_s} ⟶ φs_* M_{U_s}` (restriction on the fibre);
* **`C1`**: `eC M π ι ≫ rUs = ι^*(restriction) ≫ eC M Φ ι'` (both base change maps are restriction of sections);
* `HypT`: the input that T1 + T2 supply (every extension of `Λ` by `π_{s*} M_{Y_s}` is split by such data);
* **`bcSurj_one_push_of_hypT`**: base change is surjective in degree one for `π_* M_Y`, given `HypT`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.T3d

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.FBC RamanujanPetersson.EtPBC.PushKill

universe u

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

section C1

variable {P P' Y U Ps : Scheme.{u}} (π : Y ⟶ P) (f : P' ⟶ P) (Φ : U ⟶ P') (h : U ⟶ Y)
  (hh : h ≫ π = Φ ≫ f) (ι' : Ps ⟶ P')

/-- **C1 on sections**: both composites `π_* M_Y ⟶ f_* ι'_* φs_* M_{U_s}` are restriction of sections. -/
theorem C1s : (rC M π (ι' ≫ f) ≫ (push (ι' ≫ f) Λ).map (rUs M π f Φ h hh ι' (ι' ≫ f) rfl)) ≫
      (pushCompIso Λ ι' f).inv.app _ = mS M π f Φ h hh ≫ (push f Λ).map (rC M Φ ι') := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  obtain ⟨V⟩ := V
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  rw [sh_comp_apply, sh_comp_apply, sh_comp_apply, push_map_app, push_map_app]
  refine sec_ext_cval (M := M)
    (T := (etPull (pullback.snd Φ ι')).obj ((etPull ι').obj ((etPull f).obj V))) _ _ fun w => ?_
  have l1 := cval_pushCompIso_inv_push (M := M) (pullback.snd Φ ι') ι' f V
    (((rUs M π f Φ h hh ι' (ι' ≫ f) rfl).hom.app (op ((etPull (ι' ≫ f)).obj V))).hom
      (((rC M π (ι' ≫ f)).hom.app (op V)).hom z)) w
  have l2 := cval_rUs (M := M) π f Φ h hh ι' (ι' ≫ f) rfl ((etPull (ι' ≫ f)).obj V)
    (((rC M π (ι' ≫ f)).hom.app (op V)).hom z)
    (((etPull (pullback.snd Φ ι')).map ((etPullCompIso ι' f).inv.app V)).left w)
  have l3 := cval_rC (M := M) π (ι' ≫ f) V z
    (muq (hsU π f Φ h hh ι' (ι' ≫ f) rfl) (pullback.snd π (ι' ≫ f)) (pullback.snd Φ ι')
      (hsU_snd π f Φ h hh ι' (ι' ≫ f) rfl) ((etPull (ι' ≫ f)).obj V)
      (((etPull (pullback.snd Φ ι')).map ((etPullCompIso ι' f).inv.app V)).left w))
  have r1 := cval_rC (M := M) Φ ι' ((etPull f).obj V) (((mS M π f Φ h hh).hom.app (op V)).hom z) w
  have r2 := cval_mS (M := M) π f Φ h hh V z
    (muq (pullback.fst Φ ι') Φ (pullback.snd Φ ι' ≫ ι') pullback.condition ((etPull f).obj V)
      (((etPullCompIso (pullback.snd Φ ι') ι').inv.app ((etPull f).obj V)).left w))
  have kw := congrArg (cval (M := M) (T := (etPull π).obj V) z) (C1s_key_pt π f Φ h hh ι' V w)
  exact (l1.trans (l2.trans l3)).trans (kw.trans (r1.trans r2).symm)

/-- **C1** with `ι = ι' ≫ f`. -/
theorem C1' : eC M π (ι' ≫ f) ≫ rUs M π f Φ h hh ι' (ι' ≫ f) rfl =
    (pullCompIso Λ ι' f).hom.app _ ≫ ((pull ι' Λ).map (mP M π f Φ h hh) ≫ eC M Φ ι' :
      (pull ι' Λ).obj ((pull f Λ).obj ((push π Λ).obj (constSh Λ Y M))) ⟶ _) := by
  have L : (pullAdj (ι' ≫ f) Λ).homEquiv _ _ (eC M π (ι' ≫ f) ≫ rUs M π f Φ h hh ι' (ι' ≫ f) rfl) =
      rC M π (ι' ≫ f) ≫ (push (ι' ≫ f) Λ).map (rUs M π f Φ h hh ι' (ι' ≫ f) rfl) := by
    rw [Adjunction.homEquiv_naturality_right, eC, Equiv.apply_symm_apply]
  have R : (pullAdj (ι' ≫ f) Λ).homEquiv _ _ ((pullCompIso Λ ι' f).hom.app _ ≫
      ((pull ι' Λ).map (mP M π f Φ h hh) ≫ eC M Φ ι' :
        (pull ι' Λ).obj ((pull f Λ).obj ((push π Λ).obj (constSh Λ Y M))) ⟶ _)) =
      (mS M π f Φ h hh ≫ (push f Λ).map (rC M Φ ι')) ≫ (pushCompIso Λ ι' f).hom.app _ := by
    rw [Adjunction.homEquiv_naturality_right, pullCompIso, Adjunction.homEquiv_leftAdjointUniq_hom_app,
      ← Adjunction.homEquiv_unit, Adjunction.homEquiv_ofNatIsoRight_apply]
    simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_left, eC, Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
      mP, Equiv.apply_symm_apply]
    try rfl
  apply ((pullAdj (ι' ≫ f) Λ).homEquiv _ _).injective
  exact L.trans (((Iso.comp_inv_eq ((pushCompIso Λ ι' f).app _)).1 (C1s π f Φ h hh ι')).trans R.symm)

/-- **C1**: the base change map of `π` followed by the fibre restriction is the base change of the
restriction map `mP` (for any `ι` with `ι' ≫ f = ι`). -/
theorem C1 (ι : Ps ⟶ P) (hι : ι' ≫ f = ι) :
    eC M π ι ≫ rUs M π f Φ h hh ι' ι hι =
      ((pullCongr Λ hι).inv.app _ ≫ (pullCompIso Λ ι' f).hom.app _) ≫
        (pull ι' Λ).map (mP M π f Φ h hh) ≫ eC M Φ ι' := by
  subst hι
  have e0 : (pullCongr Λ (rfl : ι' ≫ f = ι' ≫ f)).inv.app ((push π Λ).obj (constSh Λ Y M)) = 𝟙 _ := by
    first
      | simp [pullCongr]
      | rfl
  refine (C1' π f Φ h hh ι').trans ?_
  exact eq_whisker ((Category.id_comp _).symm.trans (eq_whisker e0.symm _)) _

end C1

section B3

end B3

end RamanujanPetersson.EtPBC.T3d

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

end Pull

section BC

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

variable {Λ g s}

/-- **Base change of MV classes**: for MV data over `g⁻¹V` (`j = (V, v)`), the base change of `ε ∘ κ` is
`Λ_{P_s} ≅ Λ[P_s] → Λ[ι⁻¹g⁻¹V]` (`σ_j`) followed by `ε(ι⁻¹ data) ∘ ι^*κ`. -/
theorem bc_mv (G : EtSh Λ P) (j : Nbhd s) {W' W U : P.Etale} {p₁ : W' ⟶ W} {p₂ : W' ⟶ U}
    {w : W ⟶ (etPull g).obj j.1} {v : U ⟶ (etPull g).obj j.1} {hsq : p₁ ≫ w = p₂ ≫ v}
    (hS : (mvC Λ p₁ p₂ w v hsq).ShortExact)
    (hS' : (mvC Λ ((etPull (fibι g s)).map p₁) ((etPull (fibι g s)).map p₂) ((etPull (fibι g s)).map w)
      ((etPull (fibι g s)).map v) (pull_sq (fibι g s) p₁ p₂ w v hsq)).ShortExact)
    {n m : ℕ} (κ : Ext (freeSh Λ W') G n) (h : 1 + n = m) :
    Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j G m
        (hS.extClass.comp κ h) =
      (Ext.mk₀ ((unitIso Λ (fib g s)).inv ≫ freeMap Λ (nbhdSec g s j))).comp
        (hS'.extClass.comp ((Ext.mk₀ (pullFreeHom Λ (fibι g s) W')).comp
          (κ.mapExactFunctor (pull (fibι g s) Λ)) (zero_add n)) h) (zero_add m) := by
  have hu : bcUnit Λ g s j = ((unitIso Λ (fib g s)).inv ≫ freeMap Λ (nbhdSec g s j)) ≫
      pullFreeHom Λ (fibι g s) ((etPull g).obj j.1) := by
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg ((unitIso Λ (fib g s)).inv ≫ ·) (freeToUnit_bcUnit Λ g s j))
    exact (Iso.inv_hom_id_assoc (unitIso Λ (fib g s)) (bcUnit Λ g s j)).symm
  refine (Delta.bc_apply _ _ _ _ j G m _).trans ?_
  refine (congrArg (fun u => (Ext.mk₀ u).comp ((hS.extClass.comp κ h).mapExactFunctor (pull (fibι g s) Λ))
    (zero_add m)) hu).trans ?_
  refine (Ext.mk₀_comp_mk₀_assoc _ _ _).symm.trans ?_
  exact congrArg (fun t => (Ext.mk₀ ((unitIso Λ (fib g s)).inv ≫ freeMap Λ (nbhdSec g s j))).comp t (zero_add m))
    (mapExact_mv (fibι g s) hS hS' G κ h)

end BC

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2h =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`

GLOB/REL PLAN v1, stage S4. `d = d₂₁ ≫ d₀ : D₂ ⟶ D₁ ⟶ D_{g₀}` with `Γ(W₂) = Γ(W₁)[1/s]` along `d₂₁` (Zariski) and
`d₂₁.left = Spec.map ι`; `H · ρ(r)^N = ρ y` on `Y₁`, `(prdMap d₀)^* y = r^N ũ (1 - r z)` in `Π_q Frac(Γ(W₁) ⧸ q)`
(`ũ = (u₁ on p₁, 1 elsewhere)`, `z` integral over `B₁`):
* **`exists_S4`**: `e`, a monic `g ∈ B₂[X]` of positive degree with `g(e q) = 0` (`he`), and for the piece `p₂` over `p₁`:
  `m^* H = Ψ u₁ (1 + bK(φ₂ r) e p₂)` (`hHp`, any compatible `Ψ`), `m^* H = 1 + bK(φ₂ r) e q` for `q ≠ p₂` (`hHq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section S4GenB

end S4GenB

section S4

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {g₀ G : k[X]} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  [IsAffine (prd (chEt c φ₁) (opEt Uo)).left]
  {B₂ : CommRingCat.{0}} (φ₂ : CommRingCat.of k[X] ⟶ B₂) [Etale (Spec.map φ₂ ≫ c)]
  [IsAffine (prd (chEt c φ₂) (opEt Uo)).left]
  (hD₂ : ∀ v : (prd (chEt c φ₂) (opEt Uo)).left, (prd (chEt c φ₂) (opEt Uo)).hom v ∈ opnDg c G)
  (d₂₁ : chEt c φ₂ ⟶ chEt c φ₁) (d₀ : chEt c φ₁ ⟶ chEt c (locF (B := CommRingCat.of k[X]) g₀))

/-- `ρ`-relation on `Y₁` gives `m^* H · bW(φ₂ r)^N = (prdMap d₂₁)^* ((prdMap d₀)^* y)` on `W₂`. -/
theorem wm_mG_H₂ (r : k[X]) (N : ℕ)
    {y : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)}
    {H : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)}
    (hH : H * (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop
      (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) r) ^ N =
      (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop y) :
    (wm (R := R) (mG c hle (chEt c φ₂) hD₂)).appTop H * (bW (Spec.map φ₂ ≫ c) (opEt Uo) R).hom (φ₂.hom r) ^ N =
      (wm (R := R) (prdMap d₂₁ (opEt Uo))).appTop ((wm (R := R) (prdMap d₀ (opEt Uo))).appTop y) := by
  have e := wm_mG_H c R hG₀ hle φ₂ hD₂ (d₂₁ ≫ d₀) r N hH
  rw [wm_prdMap_comp_appTop] at e
  exact e

end S4

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel1 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Rel1): a bad term of the relation as a class on a small nbhd over `U₀`

REL PLAN v2 (s126). For `U₁ ≤ U₀ ≤ U_z = P ∖ {z}`, `S` (the `z`-term of `relation_sum` over `U₁`), `d' : D' ⟶ S` with
`D' ×_P U₀ ⊆ U₁`, `σ : U₁ ⟶ T` and `κ ∈ Ext¹(Λ[T], F)`:
* **`bad_term_eq`**: `ε(S, U₁) ∘ Λ[prT]^* (Λ[σ]^* κ) = ε(D', U₀) ∘ Λ[toOpEt ≫ σ]^* κ`
  (`locCls_shrink` (O2S2), `opEt_ext`, `mk₀_freeMap_comp_comp` (O2Gl3f), `locCls_opn_toOpEt` (O2LocU) reversed).
  With `σ := sigG`, `κ := θ⁻¹ c_Y`, the right side is the `uk_kill_glob` (O2UKd3) class `ε(D') ∘ Λ[mG]^* θ⁻¹ c_Y`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section BadTerm

variable {Λ : Type} [CommRing Λ] {P : Scheme.{0}} {U₁ Uo Uz : P.Opens} (h₁₀ : U₁ ≤ Uo) (h : Uo ≤ Uz) (h₁ : U₁ ≤ Uz)
  {z : P} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ z) {S D' : P.Etale} (d' : D' ⟶ S)
  (hSs : Subsingleton ((geomPtAt z).point.fiber.obj S)) (hSn : Nonempty ((geomPtAt z).point.fiber.obj S))
  (hSr : ∀ v : S.left, S.hom v ∈ U₁ ∨ S.hom v = z)
  (hDs : Subsingleton ((geomPtAt z).point.fiber.obj D')) (hDn : Nonempty ((geomPtAt z).point.fiber.obj D'))
  (hDr₁ : ∀ v : D'.left, D'.hom v ∈ U₁ ∨ D'.hom v = z) (hDr : ∀ v : D'.left, D'.hom v ∈ Uo ∨ D'.hom v = z)
  (hD' : ∀ v : (prd D' (opEt Uo)).left, (prd D' (opEt Uo)).hom v ∈ U₁)

include h₁₀ d' hDr₁ in
/-- **A term of the relation over `U₁`, moved to a small nbhd `D'` and to `U₀`.** -/
theorem bad_term_eq {T : P.Etale} (σ : opEt U₁ ⟶ T) {F : EtSh Λ P} (κ : Ext.{0} (freeSh Λ T) F 1) :
    (locC_shortExact (Λ := Λ) S h₁ z hz hSs hSn hSr).extClass.comp
      ((Ext.mk₀ (freeMap Λ (prT S (opEt U₁)))).comp ((Ext.mk₀ (freeMap Λ σ)).comp κ (zero_add 1)) (zero_add 1))
      (show 1 + 1 = 2 from rfl) =
    (locC_shortExact (Λ := Λ) D' h z hz hDs hDn hDr).extClass.comp
      ((Ext.mk₀ (freeMap Λ (toOpEt (prd D' (opEt Uo)) U₁ hD' ≫ σ))).comp κ (zero_add 1))
      (show 1 + 1 = 2 from rfl) := by
  rw [locCls_shrink h₁ d' (locC_shortExact (Λ := Λ) D' h₁ z hz hDs hDn hDr₁)
      (locC_shortExact (Λ := Λ) S h₁ z hz hSs hSn hSr),
    ← mk₀_freeMap_comp_comp (prdMap d' (opEt U₁)) (prT S (opEt U₁)),
    ← mk₀_freeMap_comp_comp (prdMap d' (opEt U₁) ≫ prT S (opEt U₁)) σ,
    opEt_ext (prdMap d' (opEt U₁) ≫ prT S (opEt U₁)) (prT D' (opEt U₁))]
  exact (locCls_opn_toOpEt h₁₀ h h₁ D' (locC_shortExact (Λ := Λ) D' h₁ z hz hDs hDn hDr₁)
    (locC_shortExact (Λ := Λ) D' h z hz hDs hDn hDr) σ hD' κ).symm

end BadTerm

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB2b =====
section

/-!
# S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

section TB2b

variable {Λ : Type u} [CommRing Λ]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Etale)

/-- **KEY (TB2), generic form**: for `f_V : V ⟶ W` over `f` and `m' : V ⟶ X ×_Y T` over `m`, the section map of `m'`
followed by `tauAppG` is the pullback of the section map of `m`. -/
theorem secMap_pullG (V : X.Etale) (fV : V.left ⟶ W.left) (sq : V.hom ≫ f = fV ≫ W.hom) {T : Y.Etale}
    (m : W ⟶ T) (m' : V ⟶ (etPull f).obj T) (hm : m'.left ≫ pullback.fst T.hom f = fV ≫ m.left) :
    secMap Λ m' ≫ (res V.hom Λ).map (pullFreeHom Λ f T) ≫ tauAppG Λ f W V fV sq (freeSh Λ T) =
      (pullUnit Λ fV).hom ≫ (pull fV Λ).map (secMap Λ m) :=
  unit_hom_extW2 (Λ := Λ) (A := V.left)
    (@CategoryStruct.comp (EtSh Λ ((𝟭 Scheme).obj V.left)) _ _ _ _ (secMap Λ m')
      ((res V.hom Λ).map (pullFreeHom Λ f T) ≫ tauAppG Λ f W V fV sq (freeSh Λ T)))
    (pullUnit Λ fV).hom ((pull fV Λ).map (secMap Λ m))
    (Eq.trans
      (appN3 (Λ := Λ) (X := (𝟭 Scheme).obj V.left) _ _ _ (secMap_oneI (Λ := Λ) m') (resPullFree_secO2 f V T _)
        (appN5f (Λ := Λ) _ _ _ _ _ (pullIsoRes_inv_graph m' (pbSec f (taut Λ T)))
          (pullCompInv_pbSecO V.hom f _ _) (pullCongr_pbSecO sq _ _)
          (pullCompHom_pbSecO fV W.hom _ _) (pullMap_pullIsoRes_pbSecO W T fV (freeSh Λ T) _ _)
          (tauAppG Λ f W V fV sq (freeSh Λ T)) rfl))
      (Eq.trans (map4_congr _ _ _ _ _ _ _ (rhoO_eqG f W V fV sq m m' hm) _)
        (Eq.symm (app2 _ _ (pullUnit_one fV) (pull_secMap_secO fV m _)))))

end TB2b

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6b2 =====
section

/-!
# S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`

For a chart `D = chEt c φ` (`B` Dedekind, `(X - a)` a nonzero prime) and `s' : D ⟶ ιP^* W`:
* the point `d₀ = (X - a)` of `D` over `z = c a` and its `K`-point `δ₀` (`δ₀_hom : δ₀ ≫ D.hom = ptz`);
* `wK = s'(d₀)`, the `K`-point `v'` of `Vs` over `sK` (`v'_hom`), `gE₀ : D ⟶ Es` (`v ↦ (s' v, σ₀ v)`);
* `Vb = gE₀⁻¹(Og)`, `Db = opn D Vb` (`d₀ ∈ Vb`), its fibre at `z` (subsingleton, nonempty) and `hSb`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum

section Sq

end Sq

section Pt

end Pt

section Fib

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)] [IsDedekindDomain B]
  (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime)
  (s' : chEt c φ ⟶ (etPull (ιP gS s)).obj W)

theorem gE₀_snd : gE₀ gS s c a W φ ht hP s' ≫ pullback.snd W.hom
    (Zs (σz K gS (zc c a) (chart_hclA c a)) (qV K gS) W).hom =
      (chEt c φ).hom ≫ σ₁ gS s c a W φ ht hP s' :=
  pullback.lift_snd _ _ _

theorem gE₀_hom : gE₀ gS s c a W φ ht hP s' ≫ (Es (σz K gS (zc c a) (chart_hclA c a)) (qV K gS) W).hom =
    (chEt c φ).hom ≫ ιP gS s :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (gE₀_snd gS s c a W φ ht hP s') _).trans
    ((Category.assoc _ _ _).trans (whisker_eq _ (σ₀_snd gS s c a W _ (v'_hom gS s c a W φ ht hP s')))))

/-- `δ₀ ≫ gE₀ = v' ≫ τz`. -/
theorem δ₀_gE₀ : δ₀ c a φ ht hP ≫ gE₀ gS s c a W φ ht hP s' =
    v' gS s c a W φ ht hP s' ≫ τz W (σz_qV K gS (zc c a) (chart_hclA c a)) := by
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ((whisker_eq _ (gE₀_fst gS s c a W φ ht hP s')).trans ?_)
    exact (v'_fst gS s c a W φ ht hP s').symm.trans ((whisker_eq _ (τz_fst W _)).symm.trans
      (Category.assoc _ _ _).symm)
  · refine (Category.assoc _ _ _).trans ((whisker_eq _ (gE₀_snd gS s c a W φ ht hP s')).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ((eq_whisker (δ₀_hom c a φ ht hP) _).trans ?_)
    exact (ptz_σ₁ gS s c a W φ ht hP s').trans ((whisker_eq _ (τz_snd W _)).symm.trans
      (Category.assoc _ _ _).symm)

/-- The open `Vb = gE₀⁻¹(Og) ⊆ D`. -/
def Vb : (chEt c φ).left.Opens :=
  gE₀ gS s c a W φ ht hP s' ⁻¹ᵁ Og W (σz_qV K gS (zc c a) (chart_hclA c a)) (Qc gS c)

theorem d₀_mem_Vb : d₀ c a φ hP ∈ Vb gS s c a W φ ht hP s' := by
  let x : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hx : δ₀ c a φ ht hP x = d₀ c a φ hP := δ₀_apply c a φ ht hP x
  have e1 : gE₀ gS s c a W φ ht hP s' (d₀ c a φ hP) =
      pullback.fst (Es (σz K gS (zc c a) (chart_hclA c a)) (qV K gS) W).hom (σz K gS (zc c a) (chart_hclA c a))
        ((δz W (σz_qV K gS (zc c a) (chart_hclA c a))).left (v' gS s c a W φ ht hP s' x)) := by
    refine (congrArg (gE₀ gS s c a W φ ht hP s') hx.symm).trans ((Scheme.Hom.comp_apply _ _ _).symm.trans ?_)
    refine (congrArg (fun f => f x) (δ₀_gE₀ gS s c a W φ ht hP s')).trans ((Scheme.Hom.comp_apply _ _ _).trans ?_)
    exact (congrArg (fun f => f (v' gS s c a W φ ht hP s' x))
      (δz_fst W (σz_qV K gS (zc c a) (chart_hclA c a))).symm).trans
      (Scheme.Hom.comp_apply (δz W (σz_qV K gS (zc c a) (chart_hclA c a))).left
        (pullback.fst (Es (σz K gS (zc c a) (chart_hclA c a)) (qV K gS) W).hom
          (σz K gS (zc c a) (chart_hclA c a))) (v' gS s c a W φ ht hP s' x))
  have e2 : pr K gS ((Es (σz K gS (zc c a) (chart_hclA c a)) (qV K gS) W).hom
      (gE₀ gS s c a W φ ht hP s' (d₀ c a φ hP))) = zc c a := by
    have hm : gE₀ gS s c a W φ ht hP s' ≫ (Es (σz K gS (zc c a) (chart_hclA c a)) (qV K gS) W).hom ≫ pr K gS =
        (chEt c φ).hom :=
      (Category.assoc _ _ _).symm.trans ((eq_whisker (gE₀_hom gS s c a W φ ht hP s') _).trans
        ((Category.assoc _ _ _).trans ((whisker_eq _ (ιP_pr gS s)).trans (Category.comp_id _))))
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans ((Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun f => f (d₀ c a φ hP)) hm).trans (d₀_hom c a φ hP)))
  show gE₀ gS s c a W φ ht hP s' (d₀ c a φ hP) ∈ (Bz W (σz_qV K gS (zc c a) (chart_hclA c a)))ᶜ ∩
    (Es (σz K gS (zc c a) (chart_hclA c a)) (qV K gS) W).hom ⁻¹' ((Qc gS c : (PV K gS).Opens) : Set (PV K gS))
  refine ⟨?_, hQc gS c a _ e2⟩
  rintro ⟨e, he, hκ⟩
  exact he ⟨_, ((pullback.fst (Es (σz K gS (zc c a) (chart_hclA c a)) (qV K gS) W).hom
    (σz K gS (zc c a) (chart_hclA c a))).isClosedEmbedding.injective (e1.symm.trans hκ.symm))⟩

/-- `D♭ = opn D Vb`. -/
abbrev Db : (P1 K).Etale := opn (chEt c φ) (Vb gS s c a W φ ht hP s')

theorem fibDb_sub : Subsingleton ((geomPtAt (zc c a)).point.fiber.obj (Db gS s c a W φ ht hP s')) := by
  have := fibD_sub c a φ ht hP
  exact (fib_opn_injective (chEt c φ) (Vb gS s c a W φ ht hP s') (zc c a)).subsingleton

theorem fibDb_nonempty : Nonempty ((geomPtAt (zc c a)).point.fiber.obj (Db gS s c a W φ ht hP s')) :=
  nonempty_fib_of_mem _ (zc c a) ⟨d₀ c a φ hP, d₀_mem_Vb gS s c a W φ ht hP s'⟩ (d₀_hom c a φ hP)

/-- **The one-point MV square of `D♭` is short exact.** -/
theorem hSb (Λ : Type) [CommRing Λ] (Uz' : (P1 K).Opens) (hUz' : ∀ x : P1 K, x ∈ Uz' ↔ x ≠ zc c a) :
    (locC Λ (Db gS s c a W φ ht hP s') (le_refl Uz')).ShortExact :=
  locC_shortExact (Λ := Λ) _ (le_refl Uz') (zc c a) hUz' (fibDb_sub gS s c a W φ ht hP s')
    (fibDb_nonempty gS s c a W φ ht hP s')
    (fun _ => (em _).imp_right fun h => not_not.mp fun h' => h ((hUz' _).mpr h'))

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6b3 =====
section

/-!
# S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`

`a' : D♭ ×_P Uz' ⟶ ιP^* DzO`, `a : D♭ ⟶ ιP^* Dz`, `b : Uz' ⟶ ιP^*(Zz ×_P Uz)`, `c := σP`, with the four squares
`h₁ .. h₄` (all proved on underlying scheme maps through `toPull`), and **`mvTheta_Db`**:
`Λ[σP] ∘ (ιP^*MVZ-class of κ, r) = (locC D♭-class of a'^*κ, a ≫ r)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

section Mor

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)] [IsDedekindDomain B]
  (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime)
  (s' : chEt c φ ⟶ (etPull (ιP gS s)).obj W)
  (Uz' : (P1 K).Opens) (hUz' : ∀ x : P1 K, x ∈ Uz' ↔ x ≠ zc c a)

/-- `a` on underlying schemes: `gE₀` restricted to `Vb ⟶ Og`. -/
def mA : (Db gS s c a W φ ht hP s').left ⟶ (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)).left :=
  (gE₀ gS s c a W φ ht hP s').resLE (Og W (σz_qV K gS (zc c a) (chart_hclA c a)) (Qc gS c))
    (Vb gS s c a W φ ht hP s') le_rfl

theorem mA_ι : mA gS s c a W φ ht hP s' ≫ (Og W (σz_qV K gS (zc c a) (chart_hclA c a)) (Qc gS c)).ι =
    (Vb gS s c a W φ ht hP s').ι ≫ gE₀ gS s c a W φ ht hP s' :=
  Scheme.Hom.resLE_comp_ι _ _

theorem hA : mA gS s c a W φ ht hP s' ≫ (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)).hom =
    (Db gS s c a W φ ht hP s').hom ≫ ιP gS s :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (mA_ι gS s c a W φ ht hP s') _).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ (gE₀_hom gS s c a W φ ht hP s')).trans
      (Category.assoc _ _ _).symm)))

/-- `a : D♭ ⟶ ιP^* Dz`. -/
def aM : Db gS s c a W φ ht hP s' ⟶ (etPull (ιP gS s)).obj (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) :=
  toPull (ιP gS s) (mA gS s c a W φ ht hP s') (hA gS s c a W φ ht hP s')

/-- `b` on underlying schemes: `u ↦ (σ₁ u, u)`. -/
def mB : (opEt Uz').left ⟶
    (prd (Zz K gS (zc c a) (chart_hclA c a) W) (opEt (Uz K gS (zc c a) (chart_hclA c a)))).left :=
  pullback.lift (Uz'.ι ≫ σ₁ gS s c a W φ ht hP s') (ιU gS s c a Uz' hUz') (hB0 gS s c a W φ ht hP s' Uz' hUz')

theorem hB : mB gS s c a W φ ht hP s' Uz' hUz' ≫
    (prd (Zz K gS (zc c a) (chart_hclA c a) W) (opEt (Uz K gS (zc c a) (chart_hclA c a)))).hom =
      (opEt Uz').hom ≫ ιP gS s :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (pullback.lift_snd _ _ _) _).trans (ιU_eq gS s c a Uz' hUz'))

/-- `b : Uz' ⟶ ιP^*(Zz ×_P Uz)`. -/
def bM : opEt Uz' ⟶ (etPull (ιP gS s)).obj
    (prd (Zz K gS (zc c a) (chart_hclA c a) W) (opEt (Uz K gS (zc c a) (chart_hclA c a)))) :=
  toPull (ιP gS s) (mB gS s c a W φ ht hP s' Uz' hUz') (hB gS s c a W φ ht hP s' Uz' hUz')

theorem hA0 : (pullback.fst (Db gS s c a W φ ht hP s').hom (opEt Uz').hom ≫ mA gS s c a W φ ht hP s') ≫
    (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)).hom =
      (pullback.snd (Db gS s c a W φ ht hP s').hom (opEt Uz').hom ≫ ιU gS s c a Uz' hUz') ≫
        (opEt (Uz K gS (zc c a) (chart_hclA c a))).hom :=
  ((Category.assoc _ _ _).trans ((whisker_eq _ (hA gS s c a W φ ht hP s')).trans
    ((Category.assoc _ _ _).symm.trans ((eq_whisker pullback.condition _).trans (Category.assoc _ _ _))))).trans
    ((Category.assoc _ _ _).trans (whisker_eq _ (ιU_eq gS s c a Uz' hUz'))).symm

/-- `a'` on underlying schemes. -/
def mA' : (prd (Db gS s c a W φ ht hP s') (opEt Uz')).left ⟶ (prd (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) (opEt (Uz K gS (zc c a) (chart_hclA c a)))).left :=
  pullback.lift (pullback.fst (Db gS s c a W φ ht hP s').hom (opEt Uz').hom ≫ mA gS s c a W φ ht hP s')
    (pullback.snd (Db gS s c a W φ ht hP s').hom (opEt Uz').hom ≫ ιU gS s c a Uz' hUz')
    (hA0 gS s c a W φ ht hP s' Uz' hUz')

theorem hA' : mA' gS s c a W φ ht hP s' Uz' hUz' ≫ (prd (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) (opEt (Uz K gS (zc c a) (chart_hclA c a)))).hom =
    (prd (Db gS s c a W φ ht hP s') (opEt Uz')).hom ≫ ιP gS s :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (pullback.lift_snd _ _ _) _).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ (ιU_eq gS s c a Uz' hUz')).trans (Category.assoc _ _ _).symm)))

/-- `a' : D♭ ×_P Uz' ⟶ ιP^* DzO`. -/
def aM' : prd (Db gS s c a W φ ht hP s') (opEt Uz') ⟶ (etPull (ιP gS s)).obj (prd (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) (opEt (Uz K gS (zc c a) (chart_hclA c a)))) :=
  toPull (ιP gS s) (mA' gS s c a W φ ht hP s' Uz' hUz') (hA' gS s c a W φ ht hP s' Uz' hUz')

theorem hm₁ : mA' gS s c a W φ ht hP s' Uz' hUz' ≫
    pullback.fst (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)).hom (opEt (Uz K gS (zc c a) (chart_hclA c a))).hom =
      pullback.fst (Db gS s c a W φ ht hP s').hom (opEt Uz').hom ≫ mA gS s c a W φ ht hP s' :=
  pullback.lift_fst (pullback.fst (Db gS s c a W φ ht hP s').hom (opEt Uz').hom ≫ mA gS s c a W φ ht hP s')
    (pullback.snd (Db gS s c a W φ ht hP s').hom (opEt Uz').hom ≫ ιU gS s c a Uz' hUz')
    (hA0 gS s c a W φ ht hP s' Uz' hUz')

theorem hm₁L : mA' gS s c a W φ ht hP s' Uz' hUz' ≫ (prW (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) (opEt (Uz K gS (zc c a) (chart_hclA c a)))).left =
    (prW (Db gS s c a W φ ht hP s') (opEt Uz')).left ≫ mA gS s c a W φ ht hP s' :=
  (whisker_eq _ (prW_left' _ _)).trans ((hm₁ gS s c a W φ ht hP s' Uz' hUz').trans
    (eq_whisker (prW_left' _ _).symm _))

theorem h₁M : aM' gS s c a W φ ht hP s' Uz' hUz' ≫ (etPull (ιP gS s)).map
    (prW (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) (opEt (Uz K gS (zc c a) (chart_hclA c a)))) =
      prW (Db gS s c a W φ ht hP s') (opEt Uz') ≫ aM gS s c a W φ ht hP s' :=
  (toPull_map (ιP gS s) (mA' gS s c a W φ ht hP s' Uz' hUz') (hA' gS s c a W φ ht hP s' Uz' hUz')
    (prW (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) (opEt (Uz K gS (zc c a) (chart_hclA c a))))).trans
    ((toPull_ext (ιP gS s) _ _ (hm₁L gS s c a W φ ht hP s' Uz' hUz')).trans
      (toPull_comp (ιP gS s) (mA gS s c a W φ ht hP s') (hA gS s c a W φ ht hP s')
        (prW (Db gS s c a W φ ht hP s') (opEt Uz'))).symm)

theorem hm₃ : mA gS s c a W φ ht hP s' ≫
    (wz K gS (zc c a) (chart_hclA c a) W (Qc gS c)).left =
      (toTop (Db gS s c a W φ ht hP s')).left ≫ σ₁ gS s c a W φ ht hP s' :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (mA_ι gS s c a W φ ht hP s') _).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ (gE₀_snd gS s c a W φ ht hP s')).trans
      (Category.assoc _ _ _).symm)))

theorem h₃M : aM gS s c a W φ ht hP s' ≫ (etPull (ιP gS s)).map (wz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) =
    toTop (Db gS s c a W φ ht hP s') ≫
      σP gS s c a W (v' gS s c a W φ ht hP s') (v'_hom gS s c a W φ ht hP s') :=
  (toPull_map _ _ _ _).trans ((toPull_ext _ _ _ (hm₃ gS s c a W φ ht hP s')).trans (toPull_comp _ _ _ _).symm)

theorem hm₄ : mB gS s c a W φ ht hP s' Uz' hUz' ≫ pullback.fst (Zz K gS (zc c a) (chart_hclA c a) W).hom
    (opEt (Uz K gS (zc c a) (chart_hclA c a))).hom = (toTop (opEt Uz')).left ≫ σ₁ gS s c a W φ ht hP s' :=
  (pullback.lift_fst _ _ _).trans (eq_whisker (Category.comp_id _).symm _)

theorem h₄M : bM gS s c a W φ ht hP s' Uz' hUz' ≫ (etPull (ιP gS s)).map
    (prW (Zz K gS (zc c a) (chart_hclA c a) W) (opEt (Uz K gS (zc c a) (chart_hclA c a)))) =
      toTop (opEt Uz') ≫ σP gS s c a W (v' gS s c a W φ ht hP s') (v'_hom gS s c a W φ ht hP s') :=
  (toPull_map _ _ _ _).trans ((toPull_ext _ _ _ (hm₄ gS s c a W φ ht hP s' Uz' hUz')).trans
    (toPull_comp _ _ _ _).symm)

theorem hm₂L : mA' gS s c a W φ ht hP s' Uz' hUz' ≫
    (p₂z K gS (zc c a) (chart_hclA c a) W (Qc gS c)).left =
      pullback.snd (Db gS s c a W φ ht hP s').hom (opEt Uz').hom ≫ mB gS s c a W φ ht hP s' Uz' hUz' := by
  apply pullback.hom_ext
  · refine ((Category.assoc _ _ _).trans ((whisker_eq _ (pullback.lift_fst _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans ((eq_whisker (pullback.lift_fst _ _ _) _).trans
        ((Category.assoc _ _ _).trans ((whisker_eq _ (hm₃ gS s c a W φ ht hP s')).trans
          ((Category.assoc _ _ _).symm.trans (eq_whisker pullback.condition _)))))))).trans ?_
    exact (((Category.assoc _ _ _).trans (whisker_eq _ (hm₄ gS s c a W φ ht hP s' Uz' hUz'))).trans
      (Category.assoc _ _ _).symm).symm
  · exact ((Category.assoc _ _ _).trans ((whisker_eq _ (pullback.lift_snd _ _ _)).trans
      (pullback.lift_snd _ _ _))).trans ((Category.assoc _ _ _).trans
        (whisker_eq _ (pullback.lift_snd _ _ _))).symm

theorem h₂M : aM' gS s c a W φ ht hP s' Uz' hUz' ≫ (etPull (ιP gS s)).map
    (p₂z K gS (zc c a) (chart_hclA c a) W (Qc gS c)) =
      (prT (Db gS s c a W φ ht hP s') (opEt Uz') ≫ opEtMap (le_refl Uz')) ≫ bM gS s c a W φ ht hP s' Uz' hUz' := by
  refine (toPull_map _ _ _ _).trans ((toPull_ext _ _ _ ?_).trans (toPull_comp _ _ _ _).symm)
  exact (hm₂L gS s c a W φ ht hP s' Uz' hUz').trans (eq_whisker ((Category.comp_id _).symm.trans
    (whisker_eq _ (opEtMap_refl_left Uz').symm)) _)

end Mor

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6c1 =====
section

/-!
# S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square

For the data of a point class `x = pcD c' ∘ Λ[s']` with coefficients `T = ιP^* W`:
* `pcD_s'`: `x = ε(locC D) ∘ θ(prW, κ_D) ∘ Λ[s']`, `κ_D = isoT⁻¹^* toWa^* ξ`;
* `shrink_Db`: the same class through `D♭ = opn D Vb`;
* `hrM : aM ≫ ιP^*(rW) = opnι ≫ s'`, `hmapA`, `hκ` (the Kummer classes agree on `D♭ ×_P Uz'`);
* **`ptCls_Db`**: `x = Λ[σP] ∘ (ιP^*MVZ-class of fW^* κZ and ιP^* rW)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

section Cls

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)] [IsDedekindDomain B]
  (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime)
  (s' : chEt c φ ⟶ (etPull (ιP gS s)).obj W)
  (Uz' : (P1 K).Opens) (hUz' : ∀ x : P1 K, x ∈ Uz' ↔ x ≠ zc c a)
  {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) (Λ : Type) [CommRing Λ] (hΛ : ∀ x : Λ, N • x = 0)
  (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz' ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz')).ShortExact) (c' : Λ)

theorem hk₂ : prdMap (opnι (chEt c φ) (Vb gS s c a W φ ht hP s')) (opEt Uz') ≫
    (prT (chEt c φ) (opEt Uz') ≫ opEtMap (le_refl Uz')) =
      (prT (Db gS s c a W φ ht hP s') (opEt Uz') ≫ opEtMap (le_refl Uz')) ≫ 𝟙 _ :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (prdMap_prT _ _) _).trans (Category.comp_id _).symm)

theorem hrW : mA gS s c a W φ ht hP s' ≫ (rW gS c a W).left =
    (opnι (chEt c φ) (Vb gS s c a W φ ht hP s') ≫ s').left ≫ pullback.fst W.hom (ιP gS s) :=
  (whisker_eq _ (show (rW gS c a W).left = (Og W (σz_qV K gS (zc c a) (chart_hclA c a)) (Qc gS c)).ι ≫
      pullback.fst W.hom (Zz K gS (zc c a) (chart_hclA c a) W).hom from rfl)).trans
    ((Category.assoc _ _ _).symm.trans ((eq_whisker (mA_ι gS s c a W φ ht hP s') _).trans
      ((Category.assoc _ _ _).trans ((whisker_eq _ (gE₀_fst gS s c a W φ ht hP s')).trans
        ((Category.assoc _ _ _).symm.trans (eq_whisker (show (Vb gS s c a W φ ht hP s').ι ≫ s'.left =
          (opnι (chEt c φ) (Vb gS s c a W φ ht hP s') ≫ s').left from rfl) _))))))

theorem hrM : aM gS s c a W φ ht hP s' ≫ (etPull (ιP gS s)).map (rW gS c a W) =
    opnι (chEt c φ) (Vb gS s c a W φ ht hP s') ≫ s' :=
  (toPull_map (ιP gS s) (mA gS s c a W φ ht hP s') (hA gS s c a W φ ht hP s') (rW gS c a W)).trans
    (etPull_hom_ext (ιP gS s) ((toPull_fst (ιP gS s) _ _).trans (hrW gS s c a W φ ht hP s')))

theorem hmapR : ((prdMap (opnι (chEt c φ) (Vb gS s c a W φ ht hP s')) (opEt Uz')).left ≫
    (isoT c φ hUz).inv.left ≫ (toWa c a φ).left) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K[X] (LA K a))) ≫ c =
        (prd (Db gS s c a W φ ht hP s') (opEt Uz')).hom :=
  ((Category.assoc _ _ _).trans (whisker_eq _ ((Category.assoc _ _ _).trans
    ((whisker_eq _ (MorphismProperty.Over.w (toWa c a φ))).trans
      (MorphismProperty.Over.w (isoT c φ hUz).inv))))).trans
    (MorphismProperty.Over.w (prdMap (opnι (chEt c φ) (Vb gS s c a W φ ht hP s')) (opEt Uz')))

end Cls

end RamanujanPetersson.EtPBC.EtMV

end

end


