-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_099
-- name    : RPLib_FX_EtPBC_099
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:17:43.707413+00:00
-- url     : https://prove2.me/theorems/2a9727b9-81d0-5e38-9292-c644c0ad77d9
-- title:
--   Proper base change for the projective line, library file 099
-- statement:
--   File 099 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovLim3`: S4-EtPBC-A, R4-T2 (A2c-2c): generation of sections at every level by finitely many compatible families
--   * `S4.Def_RP_EtPBC_A_CovLim4`: S4-EtPBC-A, R4-T2 (A2c-2d): compatible families are combinations with coefficients in a `p`-precomplete ring
--   * `S4.Def_RP_EtPBC_A_CovPr15`: S4-EtPBC-A, R4-T2 (A3o): one chart of the lift, in the shape of the `CoverLift` fields
--   * `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_Inj0b`: S4-EtPBC-A, G1b: base change in degree `0` on sections
--   * `S4.Def_RP_EtPBC_A_O2R4`: S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes
--   * `S4.Def_RP_EtPBC_A_O2Bd4`: S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`
--   * `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
--   * `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
--   * `S4.Def_RP_EtPBC_A_O2L6c1`: S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_088

/-!
# Proper base change for the projective line, library file 099

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovLim3`: S4-EtPBC-A, R4-T2 (A2c-2c): generation of sections at every level by finitely many compatible families
* `S4.Def_RP_EtPBC_A_CovLim4`: S4-EtPBC-A, R4-T2 (A2c-2d): compatible families are combinations with coefficients in a `p`-precomplete ring
* `S4.Def_RP_EtPBC_A_CovPr15`: S4-EtPBC-A, R4-T2 (A3o): one chart of the lift, in the shape of the `CoverLift` fields
* `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
* `S4.Def_RP_EtPBC_A_Inj0b`: S4-EtPBC-A, G1b: base change in degree `0` on sections
* `S4.Def_RP_EtPBC_A_O2R4`: S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes
* `S4.Def_RP_EtPBC_A_O2Bd4`: S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`
* `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
* `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
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

/-- **One step of `p`-adic generation**: entries in `p^n` give coefficients in `p^n` modulo `p^(n+1)`. -/
theorem gen_step (hα : ∀ i, α i ∈ p) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) {d : ℕ}
    (hσ : ∀ i, σ i ∈ Gam C H d) (hgen0 : ∀ y ∈ (C 0).sec d, ∃ c, y = lev C ιB₀ ιB₁ σ 0 c)
    (hfil : ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) (m : ℕ) :
    ∀ n, ∀ y ∈ (C m).sec d, y.1 ∈ (p ^ n).map (lι₀ ιB₀ (C m)) → y.2 ∈ (p ^ n).map (lι₁ ιB₁ (C m)) →
      ∃ c : Fin r → R, (∀ i, c i ∈ p ^ n) ∧
        (y - lev C ιB₀ ιB₁ σ m c).1 ∈ (p ^ (n + 1)).map (lι₀ ιB₀ (C m)) ∧
        (y - lev C ιB₀ ιB₁ σ m c).2 ∈ (p ^ (n + 1)).map (lι₁ ιB₁ (C m)) := by
  intro n
  induction n with
  | zero =>
    intro y hy _ _
    obtain ⟨c, h₀, h₁⟩ := gen_mod_p C H ιB₀ ιB₁ p σ hJ₀ hJ₁ hσ hgen0 m y hy
    refine ⟨c, fun i => ?_, h₀, h₁⟩
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    intro y hy hy₀ hy₁
    obtain ⟨z, hz, hz₀, hz₁, hyz⟩ := hfil m n y hy hy₀ hy₁
    choose c hc hc₀ hc₁ using fun i => ih (z i) (hz i) (hz₀ i) (hz₁ i)
    refine ⟨fun l => ∑ i, α i * c i l, fun l => ?_, ?_, ?_⟩
    · refine Ideal.sum_mem _ fun i _ => ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul (hα i) (hc i l)
    · rw [hyz, lev_comb]
      simp only [Prod.fst_sub, Prod.fst_sum, ← Finset.sum_sub_distrib, ← mul_sub]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [pow_succ' p (n + 1), Ideal.map_mul]
      have h := hc₀ i
      rw [Prod.fst_sub] at h
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hα i)) h
    · rw [hyz, lev_comb]
      simp only [Prod.snd_sub, Prod.snd_sum, ← Finset.sum_sub_distrib, ← mul_sub]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [pow_succ' p (n + 1), Ideal.map_mul]
      have h := hc₁ i
      rw [Prod.snd_sub] at h
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hα i)) h

/-- **Generation at every level**: a level-`m` section with entries in `p^j` is a combination of the `σᵢ` with
coefficients in `p^j`. -/
theorem gen_lev (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hJ₀ : J₀ = p.map ιB₀)
    (hJ₁ : J₁ = p.map ιB₁) {d : ℕ} (hσ : ∀ i, σ i ∈ Gam C H d)
    (hgen0 : ∀ y ∈ (C 0).sec d, ∃ c, y = lev C ιB₀ ιB₁ σ 0 c) (hfil : ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    (m : ℕ) : ∀ j, ∀ y ∈ (C m).sec d, y.1 ∈ (p ^ j).map (lι₀ ιB₀ (C m)) →
      y.2 ∈ (p ^ j).map (lι₁ ιB₁ (C m)) → ∃ c : Fin r → R, (∀ i, c i ∈ p ^ j) ∧ y = lev C ιB₀ ιB₁ σ m c := by
  have key : ∀ t j, m + 1 ≤ j + t → ∀ y ∈ (C m).sec d, y.1 ∈ (p ^ j).map (lι₀ ιB₀ (C m)) →
      y.2 ∈ (p ^ j).map (lι₁ ιB₁ (C m)) → ∃ c : Fin r → R, (∀ i, c i ∈ p ^ j) ∧
        y = lev C ιB₀ ιB₁ σ m c := by
    intro t
    induction t with
    | zero =>
      intro j hj y _ hy₀ hy₁
      rw [lpow_bot₀ _ _ _ _ _ _ _ _ _ ιB₀ p hJ₀ (C m) (by omega)] at hy₀
      rw [lpow_bot₁ _ _ _ _ _ _ _ _ _ ιB₁ p hJ₁ (C m) (by omega)] at hy₁
      refine ⟨0, fun _ => Ideal.zero_mem _, ?_⟩
      rw [lev_zero]
      exact Prod.ext ((Submodule.mem_bot _).1 hy₀) ((Submodule.mem_bot _).1 hy₁)
    | succ t ih =>
      intro j hj y hy hy₀ hy₁
      obtain ⟨c, hc, h₀, h₁⟩ := gen_step C H ιB₀ ιB₁ p σ α hα hJ₀ hJ₁ hσ hgen0 hfil m j y hy hy₀ hy₁
      have hm : y - lev C ιB₀ ιB₁ σ m c ∈ (C m).sec d :=
        AddSubgroup.sub_mem _ hy (lev_mem C H ιB₀ ιB₁ σ hιB hσ m c)
      obtain ⟨c', hc', he⟩ := ih (j + 1) (by omega) _ hm h₀ h₁
      refine ⟨c + c', fun i => Ideal.add_mem _ (hc i) (Ideal.pow_le_pow_right (Nat.le_succ j) (hc' i)), ?_⟩
      rw [lev_add, ← he, add_sub_cancel]
  intro j
  exact key (m + 1) j (by omega)

end Gen

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovLim4 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2d): compatible families are combinations with coefficients in a `p`-precomplete ring

For compatible families `σ : Fin r → Gam C H d` generating level `0`, over `R` with `IsPrecomplete p R`:
* `gam_agree`: two compatible families that agree at level `k` agree at every level `m ≤ k`;
* `gam_seq`: a level-`k₀` combination extends to a combination at all levels with congruent coefficients;
* **`gam_gen`**: every compatible family is `∑ aᵢ σᵢ` at all levels;
* **`gam_ker`**: a compatible family vanishing at level `k` is `∑ aᵢ σᵢ` with all `aᵢ ∈ p^(k+1)`;
* `gen_all`: every level-`m` section is a combination of the `σᵢ`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Agree

end Agree

section Lim

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) {r : ℕ} (σ : Fin r → (∀ k, (C k).E₀) × (∀ k, (C k).E₁)) {g : ℕ}
  (α : Fin g → R)

/-- **Every level-`m` section is a combination of the `σᵢ`.** -/
theorem gen_all (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hJ₀ : J₀ = p.map ιB₀)
    (hJ₁ : J₁ = p.map ιB₁) {d : ℕ} (hσ : ∀ i, σ i ∈ Gam C H d)
    (hgen0 : ∀ y ∈ (C 0).sec d, ∃ c, y = lev C ιB₀ ιB₁ σ 0 c) (hfil : ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    (m : ℕ) (y : (C m).E₀ × (C m).E₁) (hy : y ∈ (C m).sec d) : ∃ c : Fin r → R, y = lev C ιB₀ ιB₁ σ m c := by
  have htop₀ : y.1 ∈ (p ^ 0).map (lι₀ ιB₀ (C m)) := by
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
    exact Submodule.mem_top
  have htop₁ : y.2 ∈ (p ^ 0).map (lι₁ ιB₁ (C m)) := by
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
    exact Submodule.mem_top
  obtain ⟨c, -, hc⟩ := gen_lev C H ιB₀ ιB₁ p σ α hα hιB hJ₀ hJ₁ hσ hgen0 hfil m 0 y hy htop₀ htop₁
  exact ⟨c, hc⟩

end Lim

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovPr15 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3o): one chart of the lift, in the shape of the `CoverLift` fields

**`chart_resid`**: from a descended presentation `gC` over `C ⊗ B`, a residue `θh : Pres (gmap (σh ⊗ id) gC) ↠ G`
(`θh (x ⊗ b) = res x · β b` in the `F`-algebra `G`, kernel `pI · Pres` with `pI ≤ ker res`) and an approximation
`σ : C → R'` (`χ' ∘ σ = res ∘ σh`), the residue `θ'` on `Pres (gmap (σ ⊗ id) gC)` has the `hθ`, `sθ`, `kθ` shapes of
`CoverLift` and is compatible with `θh` through `presMap`.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

variable {K A R' B Ah C : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B]
  [CommRing Ah] [Algebra A Ah] [CommRing C] [Algebra A C]

/-- **One chart of the lift.** -/
theorem chart_resid (χ : A →+* K) (χ' : R' →+* K) (res : Ah →+* K)
    (hres : ∀ a, res (algebraMap A Ah a) = χ a) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a)
    {F G : Type u} [CommRing F] [CommRing G] [Algebra K F] [Algebra F G]
    (β : B →+* F) (hβ : ∀ a, β (algebraMap A B a) = algebraMap K F (χ a))
    (s : K →+* R') (hs : ∀ k, χ' (s k) = k) (sh : K →+* Ah) (hsh : ∀ k, res (sh k) = k)
    (σh : C →ₐ[A] Ah) (σ : C →ₐ[A] R') (hσ : ∀ c, χ' (σ c) = res (σh c)) {r : ℕ}
    (gC : Fin r → MvPolynomial (Fin r) (C ⊗[A] B))
    (θh : Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC) →+* G)
    (hθk : ∀ (x : Ah) (b : B), θh (algebraMap (Ah ⊗[A] B)
      (Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC)) (x ⊗ₜ b)) =
        algebraMap F G (algebraMap K F (res x) * β b))
    (hθ : Function.Surjective θh) (pI : Ideal Ah) (hp : ∀ x ∈ pI, res x = 0)
    (hI : RingHom.ker θh = (pI.map (Algebra.TensorProduct.includeLeftRingHom : Ah →+* Ah ⊗[A] B)).map
      (algebraMap (Ah ⊗[A] B) (Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC)))) :
    ∃ θ' : Pres (gmap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC) →+* G,
      (∀ (x : R') (b : B), θ' (algebraMap (R' ⊗[A] B)
        (Pres (gmap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC)) (x ⊗ₜ b)) =
          algebraMap F G (algebraMap K F (χ' x) * β b)) ∧
      Function.Surjective θ' ∧
      RingHom.ker θ' = (RingHom.ker χ').map
        ((algebraMap (R' ⊗[A] B) (Pres (gmap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC))).comp
          Algebra.TensorProduct.includeLeftRingHom) ∧
      θ'.comp (presMap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC) =
        θh.comp (presMap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC) := by
  have hβ' : ∀ a, ((algebraMap F G).comp β) (algebraMap A B a) =
      ((algebraMap F G).comp (algebraMap K F)) (χ a) := fun a => congrArg (algebraMap F G) (hβ a)
  have hθk' : ∀ x, θh (algebraMap (Ah ⊗[A] B)
      (Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC)) x) =
        kap χ ((algebraMap F G).comp (algebraMap K F)) ((algebraMap F G).comp β) hβ' res hres x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul y b =>
      rw [hθk, kap_tmul]
      exact map_mul (algebraMap F G) _ _
    | add x y hx hy => simp only [map_add, hx, hy]
  have hκ := hκT χ χ' res hres hχ' ((algebraMap F G).comp (algebraMap K F)) ((algebraMap F G).comp β) hβ'
    σh σ gC θh hσ hθk'
  refine ⟨resid _ _ gC θh _ hκ, ?_,
    resid_surj_T χ χ' res hres hχ' _ _ hβ' σh σ gC θh s hs hθk' hθ hκ,
    (resid_ker_T χ χ' res hres hχ' _ _ hβ' σh σ gC θh s hs sh hsh hσ hθk' hθ pI hp hI hκ).trans
      (Ideal.map_map _ _),
    resid_comp_presMap _ _ gC θh _ hκ⟩
  intro x b
  rw [resid_algebraMap, kap_tmul]
  exact (map_mul (algebraMap F G) _ _).symm

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

instance : IsOpenImmersion (a0 K gV π R') := by
  have : IsOpenImmersion (a0 K gV π R' ≫ ch0 K gV π R') := by rw [a0_ch0]; infer_instance
  exact IsOpenImmersion.of_comp _ (ch0 K gV π R')

instance : IsOpenImmersion (a1 K gV π R') := by
  have : IsOpenImmersion (a1 K gV π R' ≫ ch1 K gV π R') := by rw [a1_ch1]; infer_instance
  exact IsOpenImmersion.of_comp _ (ch1 K gV π R')

/-- **The chart cover of `Y_{V'}`**, indexed by `WalkingSpan`. -/
def covV : (YV K gV π R').OpenCover :=
  Scheme.Cover.mkOfCovers WalkingSpan (span (a0 K gV π R') (a1 K gV π R')).obj (fV K gV π R')
    (fun z => by
      have hz : z ∈ oV K gV π R' (Yc K gV π 0) ⊔ oV K gV π R' (Yc K gV π 1) := by
        rw [oV_sup]
        trivial
      rcases (TopologicalSpace.Opens.mem_sup.mp hz) with h | h
      · obtain ⟨y, hy⟩ : z ∈ Set.range (ch0 K gV π R') := by
          rw [show Set.range (ch0 K gV π R') = _ from range_ch K gV π R' _ (struct_res K gV π 0)]
          exact h
        exact ⟨WalkingSpan.left, y, hy⟩
      · obtain ⟨y, hy⟩ : z ∈ Set.range (ch1 K gV π R') := by
          rw [show Set.range (ch1 K gV π R') = _ from range_ch K gV π R' _ (struct_res K gV π 1)]
          exact h
        exact ⟨WalkingSpan.right, y, hy⟩)
    (fun j => by
      rcases j with _ | _ | _
      · exact (inferInstance : IsOpenImmersion (ch01 K gV π R'))
      · exact (inferInstance : IsOpenImmersion (ch0 K gV π R'))
      · exact (inferInstance : IsOpenImmersion (ch1 K gV π R')))

instance : Category (covV K gV π R').I₀ := inferInstanceAs (Category WalkingSpan)

instance : Quiver.IsThin (covV K gV π R').I₀ := inferInstanceAs (Quiver.IsThin WalkingSpan)

instance : Small.{u} (covV K gV π R').I₀ := inferInstanceAs (Small.{u} WalkingSpan)

theorem mem_range_zero (z : YV K gV π R') (h0 : z ∈ Set.range (ch0 K gV π R'))
    (h1 : z ∈ Set.range (ch1 K gV π R')) : z ∈ Set.range (ch01 K gV π R') := by
  rw [show Set.range (ch0 K gV π R') = _ from range_ch K gV π R' _ (struct_res K gV π 0)] at h0
  rw [show Set.range (ch1 K gV π R') = _ from range_ch K gV π R' _ (struct_res K gV π 1)] at h1
  rw [show Set.range (ch01 K gV π R') = _ from range_ch K gV π R' _ (hA01 K gV π), ← oV_inf]
  exact ⟨h0, h1⟩

instance : (covV K gV π R').LocallyDirected where
  trans h := (span (a0 K gV π R') (a1 K gV π R')).map h
  trans_id i := (span (a0 K gV π R') (a1 K gV π R')).map_id i
  trans_comp f g := (span (a0 K gV π R') (a1 K gV π R')).map_comp f g
  w h := trans_fV K gV π R' h
  directed {i j} x := directed_of_range (covV K gV π R') (fun h => (span (a0 K gV π R') (a1 K gV π R')).map h)
    (fun h => trans_fV K gV π R' h) (fun i j z hi hj => by
      rcases i with _ | (_ | _) <;> rcases j with _ | (_ | _)
      all_goals first
        | exact ⟨_, 𝟙 _, 𝟙 _, hi⟩
        | exact ⟨WalkingSpan.zero, fromZ _, fromZ _, hi⟩
        | exact ⟨WalkingSpan.zero, fromZ _, fromZ _, hj⟩
        | exact ⟨WalkingSpan.zero, fromZ _, fromZ _, mem_range_zero K gV π R' z hi hj⟩
        | exact ⟨WalkingSpan.zero, fromZ _, fromZ _, mem_range_zero K gV π R' z hj hi⟩) x
  property_trans {i j} h := by
    have hj : IsOpenImmersion ((covV K gV π R').f j) := (covV K gV π R').map_prop j
    have hc : IsOpenImmersion ((span (a0 K gV π R') (a1 K gV π R')).map h ≫ (covV K gV π R').f j) := by
      rw [show (span (a0 K gV π R') (a1 K gV π R')).map h ≫ (covV K gV π R').f j = (covV K gV π R').f i from
        trans_fV K gV π R' h]
      exact (covV K gV π R').map_prop i
    exact @IsOpenImmersion.of_comp _ _ _ _ _ hj hc

end RamanujanPetersson.EtPBC.Cov

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

/-- The chart schemes `Spec E₀₁ ⟶ Spec E₀`, `Spec E₀₁ ⟶ Spec E₁`, indexed by `WalkingSpan`. -/
abbrev glF : (covV K gV π R').I₀ ⥤ Scheme.{u} :=
  span (Spec.map (CommRingCat.ofHom ψ₀)) (Spec.map (CommRingCat.ofHom ψ₁))

section FinEt

end FinEt

section Et

end Et

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Inj0b =====
section

/-!
# S4-EtPBC-A, G1b: base change in degree `0` on sections

For `g : P ⟶ S`, a geometric point `s`, an etale neighbourhood `j = (V, v)` and a class
`α ∈ Ext^0(Λ[g⁻¹ V], G)`, let `sec0 α ∈ G(g⁻¹ V)` be the corresponding section.
* `bc_zero_eq`: `bc_j α = mk₀ (u_v ≫ ι^* α)`;
* **`sec_of_bc_zero`**: if `bc_j α = 0` then the section `σ_v^* η_G(sec0 α)` of `ι^* G` over `P_s` vanishes
  (`η` the unit of `ι^* ⊣ ι_*`, `σ_v = nbhdSec` the section of `ι⁻¹(g⁻¹ V) ⟶ P_s` given by `v`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.PtSec
  RamanujanPetersson.EtCompact.Supp

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **Degree `0`**: `bc_j α = 0` makes `σ_v^* η_G(sec0 α)` vanish. -/
theorem sec_of_bc_zero (j : Nbhd s) (G : EtSh Λ P) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 0)
    (h : Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j G 0 α = 0) :
    ((((pull (fibι g s) Λ).obj G).obj.map (nbhdSec g s j).op).hom
      ((((pullAdj (fibι g s) Λ).unit.app G).hom.app (op ((etPull g).obj j.1))).hom (sec0 Λ g s j G α))) = 0 := by
  have h1 : bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map (Ext.addEquiv₀ α) = 0 :=
    (Ext.mk₀_eq_zero_iff _).1 ((bc_zero_eq Λ g s j G α).symm.trans h)
  rw [bcUnit, ofSec_comp] at h1
  have h2 := sc_ofSec ((((pull (fibι g s) Λ).map (Ext.addEquiv₀ α)).hom.app (op (etId (fib g s)))).hom
    (fibSec Λ g s j))
  rw [h1] at h2
  have h0 : sc (0 : unitSh Λ (fib g s) ⟶ (pull (fibι g s) Λ).obj G) (etId (fib g s)) = 0 := by
    have := sc_sub (0 : unitSh Λ (fib g s) ⟶ (pull (fibι g s) Λ).obj G) 0 (etId (fib g s))
    rwa [sub_self, sub_self] at this
  have hq := h2.symm.trans h0
  have hn := ConcreteCategory.congr_hom
    (((pull (fibι g s) Λ).map (Ext.addEquiv₀ α)).hom.naturality (nbhdSec g s j).op) (unitSec Λ g s j)
  have hp := pull_unitSec Λ g s j G (Ext.addEquiv₀ α)
  exact (congrArg (((pull (fibι g s) Λ).obj G).obj.map (nbhdSec g s j).op).hom hp.symm).trans (hn.symm.trans hq)

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2R4 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes

* `ext_comp_sum`, `ext_sum_comp`, `ext_mk₀_sum` (finite sums and `Ext`);
* `locLe`, `locRng`; `extClass_loc_eq`: the one-point class at `z k` is the multi-point MV class followed by
  `copPr k` (naturality along `mvLocHom`);
* **`relation_sum`**: `Σ_k ε_loc(S k) ∘ (Λ[S k ×_P U₀ ⟶ U₀]^* κ) = 0` for every `κ ∈ Ext¹(Λ[U₀], F)`;
* `isLoc_relation_term`: each summand is a one-point class (`IsLoc`) at `z k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe w u

section ExtSum

end ExtSum

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  (S : ι → P.Etale) (U₀ : P.Opens)
  (z : ι → P) (hzi : Function.Injective z) (hU : ∀ x : P, x ∈ U₀ ↔ ∀ k, x ≠ z k)
  (hD : ∀ k, Subsingleton ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDn : ∀ k, Nonempty ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDr : ∀ k (v : (S k).left), (S k).hom v ∈ U₀ ∨ (S k).hom v = z k)
  (Uz : ι → P.Opens) (hz : ∀ k (x : P), x ∈ Uz k ↔ x ≠ z k)

include hzi hU hD hDn hDr hz in
/-- **The relation**: the one-point classes of a class restricted from `U₀` sum to zero. -/
theorem relation_sum {F : EtSh Λ P} (κ : Ext.{u} (freeSh Λ (opEt U₀)) F 1) :
    ∑ k, (locC_shortExact (Λ := Λ) (S k) (locLe U₀ z hU Uz hz k) (z k) (hz k) (hD k) (hDn k) (hDr k)).extClass.comp
      ((Ext.mk₀ (freeMap Λ (prT (S k) (opEt U₀)))).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) =
      (0 : Ext.{u} (freeSh Λ (etId P)) F 2) := by
  have hmv := mvCop_shortExact (Λ := Λ) S U₀ z hzi hU hD hDn hDr
  have step : ∀ k, (locC_shortExact (Λ := Λ) (S k) (locLe U₀ z hU Uz hz k) (z k) (hz k) (hD k) (hDn k)
      (hDr k)).extClass.comp ((Ext.mk₀ (freeMap Λ (prT (S k) (opEt U₀)))).comp κ (zero_add 1))
        (show 1 + 1 = 2 from rfl) =
      hmv.extClass.comp ((Ext.mk₀ (copPr Λ (fun j => prd (S j) (opEt U₀)) k ≫
        freeMap Λ (prT (S k) (opEt U₀)))).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) := by
    intro k
    rw [extClass_loc_eq S U₀ z hzi hU hD hDn hDr Uz hz k, Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀_assoc]
  rw [Finset.sum_congr rfl (fun k _ => step k)]
  calc ∑ k, hmv.extClass.comp ((Ext.mk₀ (copPr Λ (fun j => prd (S j) (opEt U₀)) k ≫
        freeMap Λ (prT (S k) (opEt U₀)))).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl)
      = hmv.extClass.comp (∑ k, (Ext.mk₀ (copPr Λ (fun j => prd (S j) (opEt U₀)) k ≫
          freeMap Λ (prT (S k) (opEt U₀)))).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) :=
        (ext_comp_sum _ _ _ _).symm
    _ = hmv.extClass.comp ((∑ k, Ext.mk₀ (copPr Λ (fun j => prd (S j) (opEt U₀)) k ≫
          freeMap Λ (prT (S k) (opEt U₀)))).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) := by
        rw [ext_sum_comp]
    _ = hmv.extClass.comp ((Ext.mk₀ (∑ k, copPr Λ (fun j => prd (S j) (opEt U₀)) k ≫
          freeMap Λ (prT (S k) (opEt U₀)))).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) := by
        rw [ext_mk₀_sum]
    _ = 0 := by
        rw [sum_copPr_prT]
        exact mv_res_U hmv κ _

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Bd4 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`

s128 fix of REL PLAN v2: a bad point `c(b)` has `g₀(b) = 0` (`c(D(g₀)) ⊆ U₀ ∪ {z}`), so no chart `D' ∋ b` maps to
`D_{g₀}`. The map `W(D') → Y₀` is `m^* ∘ ρ` instead (`m := mG : D' ×_P U₀ ⟶ D_G ×_P U₀`, `ρ := (prdMap (toDG c hG₀))^*`):
* **`wD_hom`**, **`shG_wm_any`**: `wm m ≫ shG φ₁ = shG φ₂` for ANY `m : D₂ ×_P U₀ ⟶ D₁ ×_P U₀` between chart products;
* **`mG_rho_gamMap`**, **`mG_H_any`**: `m^* (ρ r) = bW'(φ' r)`; the `H`-relation pulled back along `m`;
* **`exists_bad_e'`**: `exists_bad_e` (O2Bd2) without `d : D' ⟶ D_{g₀}`;
* **`exists_S4H'`**: `exists_S4H` (O2Gl2k) for a generic `G` (`hG₀ : g₀ ∣ G`), also returning `H ρ(t)^N = ρ(y)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section WDHom

end WDHom

section AnyM

end AnyM

section BadChart'

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {g₀ G : k[X]} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  {B' : CommRingCat.{0}} (φ' : CommRingCat.of k[X] ⟶ B') [Etale (Spec.map φ' ≫ c)]
  [IsAffine (prd (chEt c φ') (opEt Uo)).left]
  (hD' : ∀ v : (prd (chEt c φ') (opEt Uo)).left, (prd (chEt c φ') (opEt Uo)).hom v ∈ opnDg c G)

/-- **`hHq` at a bad point** (no chart map to `D_{g₀}`): on every piece `q` of `W(D')`, `m^* H = 1 + bK(φ'(X - C b)) e q`,
all `e q` roots of one monic `g ∈ B'[X]`. -/
def exists_bad_e'
    [Algebra k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hAY : algebraMap k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤) =
      gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R))
    (hY : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
      [m.IsMaximal], IsDomain (Localization.AtPrime m))
    [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    {a b : k} {N : ℕ} (hta : IsUnit (φ'.hom (X - C a)))
    (uS : integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
    (hu : uS - algebraMap k[X] (integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (X - C a) ^ N ∈
      Ideal.span {algebraMap k[X] (integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (X - C b)})
    {Hg : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)}
    (hH : Hg * (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop
        (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X - C a)) ^ N =
      (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop
        (liveMod hY (uS : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
          (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X - C a) ^ N)))
    [Nontrivial B'] :
    ∃ e : ∀ q : minimalPrimes Γ(((etPull (prd (chEt c φ') (opEt Uo)).hom).obj R).left, ⊤),
        FractionRing (Γ(((etPull (prd (chEt c φ') (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1),
      ∃ g : B'[X], g.Monic ∧ 0 < g.natDegree ∧ (∀ q, g.eval₂ (bK (Spec.map φ' ≫ c) (opEt Uo) R q) (e q) = 0) ∧
      ∀ q : minimalPrimes Γ(((etPull (prd (chEt c φ') (opEt Uo)).hom).obj R).left, ⊤),
        algebraMap _ (FractionRing (Γ(((etPull (prd (chEt c φ') (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1))
          (Ideal.Quotient.mk q.1 ((wm (R := R) (mG c hle (chEt c φ') hD')).appTop Hg)) =
        1 + bK (Spec.map φ' ≫ c) (opEt Uo) R q (φ'.hom (X - C b)) * e q :=
  exists_bad_genC hY (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R)) hAY φ'.hom
    (bW (Spec.map φ' ≫ c) (opEt Uo) R).hom
    (((wm (R := R) (mG c hle (chEt c φ') hD')).appTop.hom).comp
      (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop.hom)
    (mG_rho_gamMap c R hG₀ hle φ' hD')
    (bK (Spec.map φ' ≫ c) (opEt Uo) R) (bK_eq (Spec.map φ' ≫ c) (opEt Uo) R) hta uS hu
    (mG_H_any c R hG₀ hle φ' hD' (X - C a) N hH)

end BadChart'

section S4H'

end S4H'

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

/-- **KEY (TB2)**: the section map of `f^{-1} m` is the pullback of the section map of `m`, through `tauApp2`. -/
theorem secMap_pull {T : Y.Etale} (m : W ⟶ T) :
    secMap Λ ((etPull f).map m) ≫ (res ((etPull f).obj W).hom Λ).map (pullFreeHom Λ f T) ≫
        tauApp2 Λ f W (freeSh Λ T) =
      (pullUnit Λ (fW f W)).hom ≫ (pull (fW f W) Λ).map (secMap Λ m) :=
  secMap_pullG f W ((etPull f).obj W) (fW f W) (etPull_sq f W) m ((etPull f).map m) (pullback.lift_fst _ _ _)

end TB2b

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB3 =====
section

/-!
# S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`

* `pullH Λ g n κ := u ∘ g^*κ ∘ u⁻¹ ∈ H^n(X, Λ)` for `κ ∈ H^n(Y, Λ)` and any `g : X ⟶ Y` (`u := pullUnit Λ g`);
* `secMap_id`, `diagSec_pull` (the KEY identity at `m = 𝟙`);
* **`thetaM_pull`**: `Λ[f⁻¹W] ⟶ f^*Λ[W]` followed by `f^*(thetaM m 1 κ)` equals
  `thetaM (f⁻¹ m) 1 (pullH f_W 1 κ)` followed by `Λ[f⁻¹T] ⟶ f^*Λ[T]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenAlg

universe u

section TB3

variable {Λ : Type u} [CommRing Λ]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The KEY identity at `m = 𝟙 W`. -/
theorem diagSec_pull (W : Y.Etale) :
    diagSec Λ ((etPull f).obj W) ≫ (res ((etPull f).obj W).hom Λ).map (pullFreeHom Λ f W) ≫
        tauApp2 Λ f W (freeSh Λ W) =
      (pullUnit Λ (fW f W)).hom ≫ (pull (fW f W) Λ).map (diagSec Λ W) := by
  have h := secMap_pull (Λ := Λ) f W (𝟙 W)
  rw [CategoryTheory.Functor.map_id, secMap_id, secMap_id] at h
  exact h

section GenPL

universe w' v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

end GenPL

end TB3

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

theorem hmapL : ((aM' gS s c a W φ ht hP s' Uz' hUz').left ≫ fW (ιP gS s) (DzO gS c a W) ≫ fA gS c a W) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K[X] (LA K a))) ≫ c = (prd (Db gS s c a W φ ht hP s') (opEt Uz')).hom := by
  have h2 : fW (ιP gS s) (DzO gS c a W) ≫ (DzO gS c a W).hom ≫ pr K gS =
      ((etPull (ιP gS s)).obj (DzO gS c a W)).hom :=
    (Category.assoc _ _ _).symm.trans ((eq_whisker (etPull_sq (ιP gS s) (DzO gS c a W)).symm _).trans
      ((Category.assoc _ _ _).trans ((whisker_eq _ (ιP_pr gS s)).trans (Category.comp_id _))))
  exact ((Category.assoc _ _ _).trans (whisker_eq _ ((Category.assoc _ _ _).trans
    ((whisker_eq _ (fA_fac gS c a W)).trans h2)))).trans (MorphismProperty.Over.w (aM' gS s c a W φ ht hP s' Uz' hUz'))

theorem hmapA : (aM' gS s c a W φ ht hP s' Uz' hUz').left ≫ fW (ιP gS s) (DzO gS c a W) ≫ fA gS c a W =
    (prdMap (opnι (chEt c φ) (Vb gS s c a W φ ht hP s')) (opEt Uz')).left ≫
      (isoT c φ hUz).inv.left ≫ (toWa c a φ).left :=
  (cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap K[X] (LA K a))) ≫ c)).mp
    ((hmapL gS s c a W φ ht hP s' Uz' hUz').trans (hmapR gS s c a W φ ht hP s' Uz' hUz).symm)

end Cls

end RamanujanPetersson.EtPBC.EtMV

end

end


