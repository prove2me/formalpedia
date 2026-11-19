-- Prove2me | Definitions.Def_RPLib_S4_CDPack32c
-- name    : RPLib_S4_CDPack32c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T10:08:24.845923+00:00
-- url     : https://prove2.me/theorems/0f76a385-ba44-4325-80a0-193cac416495
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 32c of 71
-- statement:
--   Part 32c of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacFrob_BrPsi`: S4-JacFrob, part BrPsi (bridge 5): `Pic(X-bar) ≃ Pic(F-bar / k-bar)`
--   * `Def_RP_JacFrob_BrSig`: S4-JacFrob, part BrSig (bridge 6): the bridge intertwines the two Frobenius actions
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack32b

/-!
# Curve-duality library package, part 32c of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacFrob_BrPsi`: S4-JacFrob, part BrPsi (bridge 5): `Pic(X-bar) ≃ Pic(F-bar / k-bar)`
* `Def_RP_JacFrob_BrSig`: S4-JacFrob, part BrSig (bridge 6): the bridge intertwines the two Frobenius actions
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacFrob_BrPsi =====
section

/-!
# S4-JacFrob, part BrPsi (bridge 5): `Pic(X-bar) ≃ Pic(F-bar / k-bar)`

* `psiD j`: pull a level divisor back to `F-bar` (`psiD j D P = D (contB j P)`); injective, compatible with conorm,
  `psiD j (div f) = div f`, degree preserving (`card_fibreB`);
* `psiPic j`: the induced map on classes; `Psi0 : PicBar →+ PicK` (direct-limit lift);
* **`Psi : PicBar ≃+ PicK (kbar) (Fbar)`**, `degPicK_Psi`, **`Psi0Equiv : PicBar0 ≃+ Pic0K`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places ZetaSB RamanujanPetersson.JacComplete

section Psi

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

/-- Pull a level divisor back to `F-bar`: `psiD j D P = D (contB j P)`. -/
noncomputable def psiD (j : ℕ) :
    Places.Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) →+ Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω) where
  toFun D := by
    classical
    exact Finsupp.onFinset (D.support.biUnion (fibreB Fq F Ω hk j)) (fun P => D (contB Fq F Ω hk j P))
      (fun P hP => Finset.mem_biUnion.2 ⟨contB Fq F Ω hk j P, Finsupp.mem_support_iff.2 hP,
        (mem_fibreB Fq F Ω hk _ _ _).2 rfl⟩)
  map_zero' := by ext; simp
  map_add' D E := by ext; simp

theorem psiD_apply (j : ℕ) (D : Places.Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)))
    (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) : psiD Fq F Ω hk j D P = D (contB Fq F Ω hk j P) := by
  simp [psiD]

include hk in
theorem psiD_injective (j : ℕ) : Function.Injective (psiD Fq F Ω hk j) := by
  refine (injective_iff_map_eq_zero _).2 fun D hD => ?_
  ext Q
  obtain ⟨P, rfl⟩ := exists_contB_eq Fq F Ω hk j Q
  rw [← psiD_apply Fq F Ω hk j D P, hD]
  rfl

theorem psiD_conormNN {i j : ℕ} [Fact (lev i ∣ lev j)] (D : Places.Divisor (Lc Fq Ω (lev i)) (Fc Fq F Ω (lev i))) :
    psiD Fq F Ω hk j (conormNN Ω hk (lev i) (lev j) D) = psiD Fq F Ω hk i D := by
  ext P
  rw [psiD_apply, psiD_apply, conormNN_apply, contractNN_contB Fq F Ω hk (i := i) (j := j) P]

theorem psiD_div (j : ℕ) (f : Fc Fq F Ω (lev j)) :
    psiD Fq F Ω hk j (Places.div f) = PlacesK.div (incF Fq F Ω j f) := by
  ext P
  rw [psiD_apply, Places.div_apply, PlacesK.div_apply, ord_contB]

theorem psiD_single (j : ℕ) (Q : Places.Place (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (n : ℤ) :
    psiD Fq F Ω hk j (Finsupp.single Q n) = ∑ P ∈ fibreB Fq F Ω hk j Q, Finsupp.single P n := by
  classical
  ext P
  rw [psiD_apply, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  by_cases h : contB Fq F Ω hk j P = Q
  · rw [if_pos h.symm, if_pos ((mem_fibreB Fq F Ω hk j Q P).2 h)]
  · rw [if_neg (Ne.symm h), if_neg (fun h' => h ((mem_fibreB Fq F Ω hk j Q P).1 h'))]

include hk in
/-- **Degree** is preserved. -/
theorem deg_psiD (j : ℕ) (D : Places.Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    Places.Divisor.deg (psiD Fq F Ω hk j D) = Places.Divisor.deg D := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero]; simp [Places.Divisor.deg]
  | add D E hD hE => rw [map_add, PlacesK.Divisor.deg_add, Places.Divisor.deg_add, hD, hE]
  | single Q n =>
    rw [psiD_single, Places.Divisor.deg_single]
    have hs := map_sum (degHomK (kbar Fq Ω) (Fbar Fq F Ω)) (fun P => Finsupp.single P n) (fibreB Fq F Ω hk j Q)
    simp only [degHomK_apply, deg_single'] at hs
    rw [hs, Finset.sum_const, card_fibreB Fq F Ω hk j Q, nsmul_eq_mul, mul_comm]

/-- The induced map on divisor classes at level `lev j`. -/
noncomputable def psiPic (j : ℕ) : PicL Fq F Ω j →+ PicK (kbar Fq Ω) (Fbar Fq F Ω) :=
  QuotientAddGroup.map _ _ (psiD Fq F Ω hk j) (by
    rintro _ ⟨f, hf, rfl⟩
    rw [AddSubgroup.mem_comap, psiD_div]
    exact div_mem_PrincK _ _ ((map_ne_zero (incF Fq F Ω j)).2 hf))

theorem psiPic_mk (j : ℕ) (D : Places.Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    psiPic Fq F Ω hk j (QuotientAddGroup.mk D) = clsK _ _ (psiD Fq F Ω hk j D) := rfl

theorem psiPic_tr {i j : ℕ} (h : i ≤ j) (x : PicL Fq F Ω i) :
    psiPic Fq F Ω hk j (tr Ω hk i j h x) = psiPic Fq F Ω hk i x := by
  have : Fact (lev i ∣ lev j) := ⟨lev_dvd_lev h⟩
  induction x using QuotientAddGroup.induction_on with
  | H D => rw [tr_apply hk h, conNN_mk, psiPic_mk, psiPic_mk, psiD_conormNN]

/-- The direct-limit lift `Pic(X-bar) → Pic(F-bar / k-bar)`. -/
noncomputable def Psi0 : PicBar Ω hk →+ PicK (kbar Fq Ω) (Fbar Fq F Ω) :=
  AddCommGroup.DirectLimit.lift (PicL Fq F Ω) (tr Ω hk) _ (psiPic Fq F Ω hk) fun _ _ h x => psiPic_tr Fq F Ω hk h x

theorem Psi0_of (j : ℕ) (y : PicL Fq F Ω j) : Psi0 Fq F Ω hk (ofBar Ω hk j y) = psiPic Fq F Ω hk j y :=
  AddCommGroup.DirectLimit.lift_of _ _ _ j y

theorem degPicK_Psi0 (z : PicBar Ω hk) : degPicK _ _ (Psi0 Fq F Ω hk z) = degBar Ω hk z := by
  refine AddCommGroup.DirectLimit.induction_on z fun j y => ?_
  change degPicK _ _ (Psi0 Fq F Ω hk (ofBar Ω hk j y)) = degBar Ω hk (ofBar Ω hk j y)
  rw [Psi0_of, degBar_of]
  induction y using QuotientAddGroup.induction_on with
  | H D => rw [psiPic_mk, degPicK_clsK, deg_psiD, degPic_mk]

theorem Psi0_injective : Function.Injective (Psi0 Fq F Ω hk) := by
  refine (injective_iff_map_eq_zero _).2 fun z => ?_
  refine AddCommGroup.DirectLimit.induction_on z fun j y => ?_
  intro hz
  change Psi0 Fq F Ω hk (ofBar Ω hk j y) = 0 at hz
  change ofBar Ω hk j y = 0
  rw [Psi0_of] at hz
  induction y using QuotientAddGroup.induction_on with
  | H D =>
    rw [psiPic_mk, clsK, QuotientAddGroup.eq_zero_iff, mem_PrincK] at hz
    obtain ⟨g, hg0, hg⟩ := hz
    obtain ⟨M, hM⟩ := exists_lev_of_mem_Fbar g.2
    have hjM : j ≤ max j M := le_max_left j M
    haveI : Fact (lev j ∣ lev (max j M)) := ⟨lev_dvd_lev hjM⟩
    have hmem : (g : Ω) ∈ Fc Fq F Ω (lev (max j M)) := Fc_le (lev_dvd_lev (le_max_right j M)) hM
    let g' : Fc Fq F Ω (lev (max j M)) := ⟨g, hmem⟩
    have hgg : incF Fq F Ω (max j M) g' = g := Subtype.ext ((coe_incF Fq F Ω (max j M) g').trans rfl)
    have hg'0 : g' ≠ 0 := fun h0 => hg0 (by rw [← hgg, h0, map_zero])
    have hc : conormNN Ω hk (lev j) (lev (max j M)) D = Places.div g' := by
      apply psiD_injective Fq F Ω hk (max j M)
      rw [psiD_conormNN, psiD_div, hgg, hg]
    have h0 : tr Ω hk j (max j M) hjM (QuotientAddGroup.mk D) = tr Ω hk j (max j M) hjM 0 := by
      rw [map_zero, tr_apply hk hjM, conNN_mk, hc, QuotientAddGroup.eq_zero_iff]
      exact ⟨g', hg'0, rfl⟩
    rw [tr_injective hk hjM h0, map_zero]

theorem Psi0_surjective : Function.Surjective (Psi0 Fq F Ω hk) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H D =>
    induction D using Finsupp.induction_linear with
    | zero => exact ⟨0, by rw [map_zero]; exact (QuotientAddGroup.mk_zero _).symm⟩
    | add D E hD hE =>
      obtain ⟨z1, h1⟩ := hD
      obtain ⟨z2, h2⟩ := hE
      exact ⟨z1 + z2, by rw [map_add, h1, h2]; exact (QuotientAddGroup.mk_add _ _ _).symm⟩
    | single P n =>
      obtain ⟨M0, hM0⟩ := exists_fibreB_singleton Fq F Ω hk P
      refine ⟨ofBar Ω hk M0 (QuotientAddGroup.mk (Finsupp.single (contB Fq F Ω hk M0 P) n)), ?_⟩
      rw [Psi0_of, psiPic_mk, psiD_single, hM0 M0 le_rfl, Finset.sum_singleton]

/-- **The bridge** `Pic(X-bar) ≃ Pic(F-bar / k-bar)`. -/
noncomputable def Psi : PicBar Ω hk ≃+ PicK (kbar Fq Ω) (Fbar Fq F Ω) :=
  AddEquiv.ofBijective (Psi0 Fq F Ω hk) ⟨Psi0_injective Fq F Ω hk, Psi0_surjective Fq F Ω hk⟩

theorem Psi_apply (z : PicBar Ω hk) : Psi Fq F Ω hk z = Psi0 Fq F Ω hk z := rfl

theorem Psi_of (j : ℕ) (y : PicL Fq F Ω j) : Psi Fq F Ω hk (ofBar Ω hk j y) = psiPic Fq F Ω hk j y :=
  Psi0_of Fq F Ω hk j y

theorem degPicK_Psi (z : PicBar Ω hk) : degPicK _ _ (Psi Fq F Ω hk z) = degBar Ω hk z :=
  degPicK_Psi0 Fq F Ω hk z

theorem degBar_Psi_symm (w : PicK (kbar Fq Ω) (Fbar Fq F Ω)) :
    degBar Ω hk ((Psi Fq F Ω hk).symm w) = degPicK _ _ w := by
  rw [← degPicK_Psi, AddEquiv.apply_symm_apply]

/-- **`Pic⁰(X-bar) ≃ Pic⁰(F-bar / k-bar)`**. -/
noncomputable def Psi0Equiv : PicBar0 Ω hk ≃+ Pic0K (kbar Fq Ω) (Fbar Fq F Ω) where
  toFun z := ⟨Psi Fq F Ω hk (z : PicBar Ω hk), (mem_Pic0K _ _).2 (by rw [degPicK_Psi]; exact (mem_PicBar0 hk _).1 z.2)⟩
  invFun w := ⟨(Psi Fq F Ω hk).symm (w : PicK (kbar Fq Ω) (Fbar Fq F Ω)), (mem_PicBar0 hk _).2 (by rw [degBar_Psi_symm]; exact (mem_Pic0K _ _).1 w.2)⟩
  left_inv z := Subtype.ext ((Psi Fq F Ω hk).symm_apply_apply (z : PicBar Ω hk))
  right_inv w := Subtype.ext ((Psi Fq F Ω hk).apply_symm_apply (w : PicK (kbar Fq Ω) (Fbar Fq F Ω)))
  map_add' a b := Subtype.ext (map_add (Psi Fq F Ω hk) (a : PicBar Ω hk) (b : PicBar Ω hk))

theorem coe_Psi0Equiv (z : PicBar0 Ω hk) : (Psi0Equiv Fq F Ω hk z : PicK (kbar Fq Ω) (Fbar Fq F Ω)) = Psi Fq F Ω hk (z : PicBar Ω hk) :=
  rfl

end Psi

end RamanujanPetersson.JacFrob

end

-- ===== S4.Def_RP_JacFrob_BrSig =====
section

/-!
# S4-JacFrob, part BrSig (bridge 6): the bridge intertwines the two Frobenius actions

* `sig_incF`: on a level, `σ` is the level Frobenius `frobF`;
* `plE_contB`: `frob⁻¹ (contB j P) = contB j (σ⁻¹ P)`;
* `psiD_actD`, **`Psi_piBar`**: `Ψ ∘ π = σ_* ∘ Ψ` on `Pic(X-bar)`; `Psi_symm_sigPic`, `Psi0Equiv_piBar`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places ZetaSB RamanujanPetersson.JacComplete

section BrSig

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

theorem isLeft_sigPl_symm (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :
    ((sigPl Fq F Ω hk).symm P).isLeft = P.isLeft := by
  rcases P with w | w <;> rfl

theorem ord_sigPl_symm (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) (f : Fbar Fq F Ω) :
    ((sigPl Fq F Ω hk).symm P).ord f = P.ord (sig Fq F Ω hk f) := by
  have h := ord_sigPl Fq F Ω hk ((sigPl Fq F Ω hk).symm P) (sig Fq F Ω hk f)
  rw [Equiv.apply_symm_apply, AlgEquiv.symm_apply_apply] at h
  exact h.symm

/-- On a level, `σ` is the level Frobenius. -/
theorem sig_incF (j : ℕ) (f : Fc Fq F Ω (lev j)) :
    sig Fq F Ω hk (incF Fq F Ω j f) = incF Fq F Ω j (frobF (isConstExt_Fc Fq F Ω hk (lev j)) f) := by
  have hy : ((incF Fq F Ω j f : Fbar Fq F Ω) : Ω) ∈ Fc Fq F Ω (lev j) := by
    rw [coe_incF]; exact f.2
  have he : (⟨((incF Fq F Ω j f : Fbar Fq F Ω) : Ω), hy⟩ : Fc Fq F Ω (lev j)) = f :=
    Subtype.ext (coe_incF Fq F Ω j f)
  apply Subtype.ext
  rw [coe_sig_of_mem Fq F Ω hk _ hy, he, coe_incF]

/-- `frob⁻¹ (contB j P) = contB j (σ⁻¹ P)`. -/
theorem plE_contB (j : ℕ) (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :
    plE (isConstExt_Fc Fq F Ω hk (lev j)) (frobL Fq (Lc Fq Ω (lev j))) (contB Fq F Ω hk j P) =
      contB Fq F Ω hk j ((sigPl Fq F Ω hk).symm P) := by
  apply placeN_ext Ω (lev j)
  · rw [isLeft_plE, isLeft_contB, isLeft_contB, isLeft_sigPl_symm]
  · intro f
    rw [ord_plE, ← frobF_apply, ord_contB, ord_contB, ord_sigPl_symm, sig_incF]

theorem psiD_actD (j : ℕ) (D : Places.Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    psiD Fq F Ω hk j (actD (isConstExt_Fc Fq F Ω hk (lev j)) (frobL Fq (Lc Fq Ω (lev j))) D) =
      sigD Fq F Ω hk (psiD Fq F Ω hk j D) := by
  ext P
  rw [psiD_apply, actD_apply, plE_contB, sigD_apply, psiD_apply]

/-- **`Ψ ∘ π = σ_* ∘ Ψ`**: the bridge intertwines the arithmetic Frobenius of `Pic(X-bar)` with `σ_*`. -/
theorem Psi_piBar (z : PicBar Ω hk) : Psi Fq F Ω hk (piBar Ω hk z) = sigPic Fq F Ω hk (Psi Fq F Ω hk z) := by
  refine AddCommGroup.DirectLimit.induction_on z fun j y => ?_
  change Psi Fq F Ω hk (piBar Ω hk (ofBar Ω hk j y)) = sigPic Fq F Ω hk (Psi Fq F Ω hk (ofBar Ω hk j y))
  rw [piBar_of, Psi_of, Psi_of]
  induction y using QuotientAddGroup.induction_on with
  | H D =>
    rw [frobN, actPic_mk, psiPic_mk, psiPic_mk, psiD_actD, sigPic_mk]

theorem Psi_symm_sigPic (w : PicK (kbar Fq Ω) (Fbar Fq F Ω)) :
    (Psi Fq F Ω hk).symm (sigPic Fq F Ω hk w) = piBar Ω hk ((Psi Fq F Ω hk).symm w) := by
  rw [AddEquiv.symm_apply_eq, Psi_piBar, AddEquiv.apply_symm_apply]

theorem Psi0Equiv_piBar (z : PicBar0 Ω hk) (hz : piBar Ω hk z ∈ PicBar0 Ω hk) :
    (Psi0Equiv Fq F Ω hk ⟨piBar Ω hk z, hz⟩ : PicK (kbar Fq Ω) (Fbar Fq F Ω)) =
      sigPic Fq F Ω hk (Psi0Equiv Fq F Ω hk z) := by
  rw [coe_Psi0Equiv, coe_Psi0Equiv]
  exact Psi_piBar Fq F Ω hk z

end BrSig

end RamanujanPetersson.JacFrob

end


