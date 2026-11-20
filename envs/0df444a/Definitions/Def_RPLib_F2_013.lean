-- Prove2me | Definitions.Def_RPLib_F2_013
-- name    : RPLib_F2_013
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T08:41:54.786189+00:00
-- url     : https://prove2.me/theorems/13530c94-5415-40c8-968a-e011a7e93a2b
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 013 of 70
-- statement:
--   File 013 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacComplete_PicLw`: The Jacobian (unit S4-JacComplete), part `PicLw` (L20: Weil's law in `Pic`)
--   * `S4.Def_RP_JacComplete_PicMv`: The Jacobian (unit S4-JacComplete), part `PicMv` (L20: generators of `Pic⁰` by the moving lemma)
--   * `S4.Def_RP_JacComplete_PicSurj`: The Jacobian (unit S4-JacComplete), part `PicSurj` (L20: `jacPic0` is surjective)
--   * `S4.Def_RP_JacComplete_AJLoc`: The Jacobian (unit S4-JacComplete), part `AJLoc`: the local `ν`-piece through a closed point
--   * `S4.Def_RP_JacSymB_Chart`: S4-JacSymB, file F1: the affine charts of a curve (L12)
--   * `S4.Def_RP_JacSymB_ChartDed`: S4-JacSymB, file F3: the chart rings are finitely generated; the singleton charts are Dedekind (L12)
--   * `S4.Def_RP_JacComplete_Syn`: The Jacobian (unit S4-JacComplete), part `Syn` (dictionary D2: the chart coordinate `1/(x - c)`)
--   * `S4.Def_RP_JacComplete_RfinSyn`: The Jacobian (unit S4-JacComplete), part `RfinSyn`: chart rings are finite rings of the chart synonyms
--   * `S4.Def_RP_JacComplete_Center`: The Jacobian (unit S4-JacComplete), part `Center` (the place of a `K`-point of a chart of `X1`)
--   * `S4.Def_RP_JacComplete_Dict`: The Jacobian (unit S4-JacComplete), part `Dict` (dictionary D3 along `σ : F ≃ₐ[K] F'`)
--   * `S4.Def_RP_JacComplete_AJConv`: The Jacobian (unit S4-JacComplete), part `AJConv`: moving points from the chart synonym back to `F`
--   * `S4.Def_RP_JacComplete_AJPiece`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`
--   * `S4.Def_RP_JacComplete_AJVal`: The Jacobian (unit S4-JacComplete), part `AJVal`: the Abel-Jacobi map on a piece and its values
--   * `S4.Def_RP_JacComplete_AJVal2`: The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`
--   * `S4.Def_RP_JacComplete_AJGreedy`: The Jacobian (unit S4-JacComplete), part `AJGreedy`: generic points off a hypersurface of `Sym^n`
--   * `S4.Def_RP_JacComplete_AJGen`: The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`
--   * `S4.Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
--   * `S4.Def_RP_JacSymB_Glue`: S4-JacSymB, file G1: gluing the charts `Sym^g B_A` to `Sym^g X` (L12)
--   * `S4.Def_RP_JacComplete_AJSurj`: The Jacobian (unit S4-JacComplete), part `AJSurj` (L19 route AJ: K-point surjectivity of `Σ [Q_i] - g [P0]`)
--   * `S4.Def_RP_CoreB_Dim`: Core B, O1: the heights on the Jacobian are bounded
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_012

/-!
# Ramanujan-Petersson curve library (flat edition), file 013 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacComplete_PicLw`: The Jacobian (unit S4-JacComplete), part `PicLw` (L20: Weil's law in `Pic`)
* `S4.Def_RP_JacComplete_PicMv`: The Jacobian (unit S4-JacComplete), part `PicMv` (L20: generators of `Pic⁰` by the moving lemma)
* `S4.Def_RP_JacComplete_PicSurj`: The Jacobian (unit S4-JacComplete), part `PicSurj` (L20: `jacPic0` is surjective)
* `S4.Def_RP_JacComplete_AJLoc`: The Jacobian (unit S4-JacComplete), part `AJLoc`: the local `ν`-piece through a closed point
* `S4.Def_RP_JacSymB_Chart`: S4-JacSymB, file F1: the affine charts of a curve (L12)
* `S4.Def_RP_JacSymB_ChartDed`: S4-JacSymB, file F3: the chart rings are finitely generated; the singleton charts are Dedekind (L12)
* `S4.Def_RP_JacComplete_Syn`: The Jacobian (unit S4-JacComplete), part `Syn` (dictionary D2: the chart coordinate `1/(x - c)`)
* `S4.Def_RP_JacComplete_RfinSyn`: The Jacobian (unit S4-JacComplete), part `RfinSyn`: chart rings are finite rings of the chart synonyms
* `S4.Def_RP_JacComplete_Center`: The Jacobian (unit S4-JacComplete), part `Center` (the place of a `K`-point of a chart of `X1`)
* `S4.Def_RP_JacComplete_Dict`: The Jacobian (unit S4-JacComplete), part `Dict` (dictionary D3 along `σ : F ≃ₐ[K] F'`)
* `S4.Def_RP_JacComplete_AJConv`: The Jacobian (unit S4-JacComplete), part `AJConv`: moving points from the chart synonym back to `F`
* `S4.Def_RP_JacComplete_AJPiece`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`
* `S4.Def_RP_JacComplete_AJVal`: The Jacobian (unit S4-JacComplete), part `AJVal`: the Abel-Jacobi map on a piece and its values
* `S4.Def_RP_JacComplete_AJVal2`: The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`
* `S4.Def_RP_JacComplete_AJGreedy`: The Jacobian (unit S4-JacComplete), part `AJGreedy`: generic points off a hypersurface of `Sym^n`
* `S4.Def_RP_JacComplete_AJGen`: The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`
* `S4.Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
* `S4.Def_RP_JacSymB_Glue`: S4-JacSymB, file G1: gluing the charts `Sym^g B_A` to `Sym^g X` (L12)
* `S4.Def_RP_JacComplete_AJSurj`: The Jacobian (unit S4-JacComplete), part `AJSurj` (L19 route AJ: K-point surjectivity of `Σ [Q_i] - g [P0]`)
* `S4.Def_RP_CoreB_Dim`: Core B, O1: the heights on the Jacobian are bounded
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_PicLw =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicLw` (L20: Weil's law in `Pic`)

* `cls_mOut`: `[m(a,b)] = [a] + [b] - [Θ]` (`Θ = ThetaD = Hn3 - Hn2 - c0 + c1`), from `div_sec3`, `div_sec2`;
  `card_mBase_L`: inputs of the law are reduced of degree `g`.
* `psiL L y = [supp y] - [Θ]`: additive for the law (`lawData_add`) and (`lawData_rigid` is in `PicLr`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Pt

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {T : Type*} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]
  {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3)) (D2 : NuData K F (genusFK K F + r2))
  (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))

end Pt

section Law

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (L : LawData K F)

/-- `ψ(y) = [supp y] - [Θ]` on `K`-points of `S_g`. -/
noncomputable def psiL (y : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K) : PicK K F :=
  clsK K F (Zdiv (ptSet y)) - clsK K F (ThetaD L.Dm3 L.Dm2 L.c0 L.c1)

end Law

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_PicMv =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicMv` (L20: generators of `Pic⁰` by the moving lemma)

Over an algebraically closed `K`:
* `placeDeg_one`, `deg_single_one`, `eq_zero_of_nonneg_of_deg` (an effective divisor of degree `0` is `0`);
* `exists_move` (Riemann-Roch moving lemma): for a finite set `S` of places, `P ∈ S` and `Q0 ∉ S` there is `h ≠ 0` with
  `div h = E + P - (2g+1) Q0`, `E ≥ 0` vanishing on `S`;
* `pic0_le_of_gen`: a subgroup `R` of `Pic` containing `[v] - [Q0]` for all `v ∉ S` contains `Pic⁰`;
* `clsK_eq_zero_of_genus_zero`: for `g = 0` every degree-`0` class is trivial.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacLaw RamanujanPetersson.RR

section PicMv

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- An effective divisor of degree `0` is `0`. -/
theorem eq_zero_of_nonneg_of_deg {E : Places.Divisor K F} (hE : 0 ≤ E) (hd : E.deg = 0) : E = 0 := by
  have h1 : E.deg = ∑ v ∈ E.support, E v := by
    rw [Places.Divisor.deg, Finsupp.sum]
    exact Finset.sum_congr rfl fun v _ => by rw [placeDeg_one]; simp
  rw [h1] at hd
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => by simpa using Finsupp.le_def.1 hE v)).1 hd
  ext v
  rw [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hv
  exact hv (h2 v (Finsupp.mem_support_iff.2 hv))

/-- **Moving lemma** (Riemann-Roch): `div h = E + P - (2g+1) Q0` with `E ≥ 0` vanishing on `S`. -/
theorem exists_move (S : Finset (Places.Place K F)) {P Q0 : Places.Place K F} (hP : P ∈ S) (hQ0 : Q0 ∉ S) :
    ∃ h : F, h ≠ 0 ∧ ∃ E : Places.Divisor K F, 0 ≤ E ∧ (∀ v ∈ S, E v = 0) ∧
      PlacesK.div h = E + Finsupp.single P 1 - Finsupp.single Q0 (2 * (genusFK K F : ℤ) + 1) := by
  classical
  set D : Places.Divisor K F := Finsupp.single Q0 (2 * (genusFK K F : ℤ) + 1) - Finsupp.single P 1 with hD
  have hdegD : D.deg = 2 * (genusFK K F : ℤ) := by
    rw [hD, PlacesK.Divisor.deg_sub, deg_single', deg_single']; ring
  have hk := constField_eq_bot' (K := K) (F := F)
  have hell : (ellFK K F D : ℤ) = genusFK K F + 1 := by
    rw [ellFK_eq_of_deg hk (by rw [hdegD]; omega), hdegD]; ring
  have hellv : ∀ v : Places.Place K F, (ellFK K F (D - Finsupp.single v 1) : ℤ) = genusFK K F := by
    intro v
    have hd : (D - Finsupp.single v 1).deg = 2 * (genusFK K F : ℤ) - 1 := by
      rw [PlacesK.Divisor.deg_sub, hdegD, deg_single_one]
    rw [ellFK_eq_of_deg hk (by rw [hd]), hd]; ring
  let p : S → Submodule K (LFK K F D) := fun v =>
    (LFK K F (D - Finsupp.single v.1 1)).comap (LFK K F D).subtype
  have hne : ∀ v : S, p v ≠ ⊤ := by
    intro v hv
    have hle : LFK K F D ≤ LFK K F (D - Finsupp.single v.1 1) := by
      intro x hx
      have hm : (⟨x, hx⟩ : LFK K F D) ∈ p v := by rw [hv]; exact Submodule.mem_top
      exact Submodule.mem_comap.1 hm
    have := finiteDimensional_LFK (K := K) (F := F) (D - Finsupp.single v.1 1)
    have h1 := Submodule.finrank_mono hle
    have e1 := ellFK_def (K := K) (F := F) D
    have e2 := ellFK_def (K := K) (F := F) (D - Finsupp.single v.1 1)
    have h2 := hellv v.1
    omega
  obtain ⟨⟨h, hhD⟩, hh⟩ : ∃ x : LFK K F D, ∀ v : S, x ∉ p v := by
    by_contra hcon
    push_neg at hcon
    have hcov : ⋃ v, (p v : Set (LFK K F D)) = Set.univ :=
      Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (hcon x)
    obtain ⟨v, hv⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
    exact hne v hv
  have hh' : ∀ v ∈ S, h ∉ LFK K F (D - Finsupp.single v 1) := fun v hv hm =>
    hh ⟨v, hv⟩ (Submodule.mem_comap.2 hm)
  have h0 : h ≠ 0 := fun e => hh' P hP (e ▸ Submodule.zero_mem _)
  have hE := (mem_LFK h0).1 hhD
  refine ⟨h, h0, PlacesK.div h + D, hE, ?_, by rw [hD]; abel⟩
  intro v hv
  have hn := hh' v hv
  rw [mem_LFK h0] at hn
  by_contra hne0
  apply hn
  rw [Finsupp.le_def] at hE ⊢
  intro w
  have hw0 := hE w
  simp only [Finsupp.coe_add, Finsupp.coe_sub, Finsupp.coe_zero, Pi.add_apply, Pi.sub_apply,
    Pi.zero_apply] at hw0 hne0 ⊢
  by_cases hw : w = v
  · subst hw
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hw)]
    omega

/-- `D ↦ [D] - deg D • [Q0]`. -/
noncomputable def clsQ (Q0 : Places.Place K F) : Places.Divisor K F →+ PicK K F :=
  AddMonoidHom.mk' (fun D => clsK K F D - D.deg • clsK K F (Finsupp.single Q0 1)) fun D E => by
    have h1 : clsK K F (D + E) = clsK K F D + clsK K F E := QuotientAddGroup.mk_add _ D E
    beta_reduce
    rw [h1, PlacesK.Divisor.deg_add, add_zsmul]
    abel

theorem clsQ_apply (Q0 : Places.Place K F) (D : Places.Divisor K F) :
    clsQ Q0 D = clsK K F D - D.deg • clsK K F (Finsupp.single Q0 1) := rfl

/-- **Generators of `Pic⁰`**: a subgroup containing `[v] - [Q0]` for every `v ∉ S` contains `Pic⁰`. -/
theorem pic0_le_of_gen (R : AddSubgroup (PicK K F)) (Q0 : Places.Place K F) (S : Finset (Places.Place K F))
    (hQ0 : Q0 ∉ S)
    (hU : ∀ v, v ∉ S → clsK K F (Finsupp.single v 1) - clsK K F (Finsupp.single Q0 1) ∈ R) :
    Pic0K K F ≤ R := by
  classical
  let R' : AddSubgroup (Places.Divisor K F) := R.comap (clsQ Q0)
  have hsing : ∀ v, v ∉ S → Finsupp.single v (1 : ℤ) ∈ R' := fun v hv => by
    show clsQ Q0 (Finsupp.single v 1) ∈ R
    rw [clsQ_apply, deg_single_one, one_zsmul]
    exact hU v hv
  have hsupp : ∀ E : Places.Divisor K F, (∀ v ∈ S, E v = 0) → E ∈ R' := by
    intro E hE
    rw [← Finsupp.sum_single E]
    refine AddSubmonoidClass.finsuppSum_mem R' E _ fun v hv => ?_
    rw [← Finsupp.smul_single_one]
    exact R'.zsmul_mem (hsing v fun hvS => hv (hE v hvS)) _
  have hdiv : ∀ h : F, h ≠ 0 → PlacesK.div h ∈ R' := fun h hh => by
    show clsQ Q0 (PlacesK.div h) ∈ R
    rw [clsQ_apply, PlacesK.deg_div hh, zero_zsmul, sub_zero]
    have : clsK K F (PlacesK.div h) = 0 := (QuotientAddGroup.eq_zero_iff _).2 (div_mem_PrincK K F hh)
    rw [this]
    exact R.zero_mem
  have hQ : Finsupp.single Q0 (1 : ℤ) ∈ R' := by
    show clsQ Q0 _ ∈ R
    rw [clsQ_apply, deg_single_one, one_zsmul, sub_self]
    exact R.zero_mem
  have hall : ∀ P, Finsupp.single P (1 : ℤ) ∈ R' := by
    intro P
    by_cases hPQ : P = Q0
    · rw [hPQ]; exact hQ
    obtain ⟨h, hh, E, -, hES, he⟩ := exists_move (insert P S) (Finset.mem_insert_self P S)
      (by rw [Finset.mem_insert, not_or]; exact ⟨Ne.symm hPQ, hQ0⟩)
    have hE : E ∈ R' := hsupp E fun v hv => hES v (Finset.mem_insert_of_mem hv)
    have key : Finsupp.single P (1 : ℤ) =
        PlacesK.div h - E + Finsupp.single Q0 (2 * (genusFK K F : ℤ) + 1) := by
      rw [he]; abel
    rw [key]
    refine R'.add_mem (R'.sub_mem (hdiv h hh) hE) ?_
    rw [← Finsupp.smul_single_one]
    exact R'.zsmul_mem hQ _
  intro c hc
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hD : D.deg = 0 := by rw [← degPicK_clsK]; exact (mem_Pic0K K F).1 hc
  have hDR : D ∈ R' := by
    rw [← Finsupp.sum_single D]
    refine AddSubmonoidClass.finsuppSum_mem R' D _ fun v _ => ?_
    rw [← Finsupp.smul_single_one]
    exact R'.zsmul_mem (hall v) _
  have h3 : clsQ Q0 D ∈ R := hDR
  rw [clsQ_apply, hD, zero_zsmul, sub_zero] at h3
  exact h3

/-- For `g = 0` every class of degree `0` is trivial. -/
theorem clsK_eq_zero_of_genus_zero (hg : genusFK K F = 0) {D : Places.Divisor K F} (hD : D.deg = 0) :
    clsK K F D = 0 := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have hell : (ellFK K F D : ℤ) = 1 := by
    rw [ellFK_eq_of_deg hk (by rw [hD, hg]; norm_num), hD, hg]; norm_num
  have hpos : LFK K F D ≠ ⊥ := by
    intro hb
    have e := ellFK_def (K := K) (F := F) D
    rw [hb, finrank_bot] at e
    omega
  obtain ⟨h, hhD, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpos
  have hz : PlacesK.div h + D = 0 := eq_zero_of_nonneg_of_deg ((mem_LFK h0).1 hhD)
    (by rw [PlacesK.Divisor.deg_add, PlacesK.deg_div h0, hD, add_zero])
  have hD' : D = PlacesK.div h⁻¹ := by
    rw [divK_inv K h0, ← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact hz
  exact (QuotientAddGroup.eq_zero_iff D).2 ⟨h⁻¹, inv_ne_zero h0, hD'.symm⟩

end PicMv

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_PicSurj =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicSurj` (L20: `jacPic0` is surjective)

* `phi1 : Sym¹ B → B` (identity on points), `ptSet_phi1`, `liftTuple_phi1`;
* `rangeJ K F`: the image of `jacPic0` in `Pic`; `psiJ_mem_rangeJ`; `psiJ_of_pt` (points `y` of `S_g` with `y u0 ≠ 0`);
* **`jacPic0_surjective`**: for `g ≥ 1` the points `Q + c` (`c` = all but one point of a fixed point of `X0`) give
  `[Q] - [q0] ∈ rangeJ` for all `Q` off the zeros of `f = padMap phi1 c u0`, and `pic0_le_of_gen` finishes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section One

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B] [IsReduced B]
  [Algebra.FiniteType k B]

/-- `Sym¹ B → B`, the identity on points. -/
noncomputable def phi1 : SymRing k B 1 →ₐ[k] B :=
  liftPts (fun x => symPt (fun _ => x)) fun w => ⟨w, fun x => by rw [symPt_normS]; simp⟩

theorem comp_phi1 (x : B →ₐ[k] k) : x.comp (phi1 (k := k) (B := B)) = symPt (fun _ => x) :=
  comp_liftPts _ _ x

open Classical in
theorem ptSet_phi1 (x : B →ₐ[k] k) : ptSet (x.comp (phi1 (k := k) (B := B))) = {x} := by
  rw [comp_phi1, ptSet_symPt]
  ext y
  simp [eq_comm]

theorem liftTuple_phi1 (x : B →ₐ[k] k) : liftTuple (x.comp (phi1 (k := k) (B := B))) = fun _ => x := by
  classical
  funext i
  have h := (mem_ptSet (x.comp (phi1 (k := k) (B := B))) (liftTuple (x.comp phi1) i)).2 ⟨i, rfl⟩
  rw [ptSet_phi1] at h
  exact Finset.mem_singleton.1 h

end One

section Surj

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {K F} in
theorem div_incB_ne_zero_iff {f : Places.Rfin K F} (hf : f ≠ 0) (Q : Places.Rfin K F →ₐ[K] K) :
    PlacesK.div (incB K F f) (Sum.inl (ptP Q)) ≠ 0 ↔ Q f = 0 := by
  rw [PlacesK.div_apply]
  show Places.ord (ptP Q) (incB K F f) ≠ 0 ↔ _
  rw [incB_apply, PlacesK.ord_algebraMap _ hf, Nat.cast_ne_zero, cnt_ne_zero_iff _ hf, mem_ptP]

end Surj

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJLoc =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJLoc`: the local `ν`-piece through a closed point

* `exists_secE`: through a closed point `φ0` and any finite `E` avoiding the roots of some `b ≠ 0` (in `x`),
  a section `s` with exact poles, only simple zeros, and zero set `Z ⊇ E ∪ {φ0}` of any size.
* `exists_nuE`: `ν`-data `D` with `ν(Z \ E) = E` (`exists_role`), `Z \ E = {φ0} ∪ c`.
* `pieceF D c` (`good` at `Q + c`), `PieceR D c = B[1/pieceF]`, **`pieceMap D c : Sym^g B → B[1/pieceF]`**
  (points `Q ↦ ν(Q + c)`, `ptSet_pieceMap`); `clsK_nuF`: `[ν(A)] = [Hn] - [A]`.
* **`exists_piece`**: the package for a closed point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section AJLoc

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **Sections through `φ0` and a generic finite set `E`.** -/
theorem exists_secE (φ0 : Rfin K F →ₐ[K] K) : ∃ b : K[X], b ≠ 0 ∧
    ∀ E : Finset (Rfin K F →ₐ[K] K), (∀ e ∈ E, b.eval (e (xB K F)) ≠ 0) → ∀ m : ℕ,
      ∃ s : Rfin K F, ∃ Z : Finset (Rfin K F →ₐ[K] K), s ≠ 0 ∧
        ExactPoleH s (poleDiv (K := K) (incB K F s)) ∧ (∀ φ, φ ∈ Z ↔ φ s = 0) ∧
        (Z.card : ℤ) = (poleDiv (K := K) (incB K F s)).deg ∧ φ0 ∈ Z ∧ E ⊆ Z ∧ φ0 ∉ E ∧ m ≤ Z.card := by
  obtain ⟨g, hg0, hφ0, a, ha, N, hfam⟩ := exists_secP φ0
  obtain ⟨a1, ha1, hfib⟩ := exists_fib_data (K := K) (F := F)
  obtain ⟨b, hb⟩ : ∃ b : K[X], b = a * a1 * (X - C (φ0 (xB K F))) := ⟨_, rfl⟩
  have hb0 : b ≠ 0 := by rw [hb]; exact mul_ne_zero (mul_ne_zero ha ha1) (X_sub_C_ne_zero _)
  refine ⟨b, hb0, fun E hE m => ?_⟩
  obtain ⟨Λ1, hΛ1, hΛ1c⟩ :=
    (finite_setOfPred_isRoot hb0).infinite_compl.exists_subset_card_eq (N + m)
  have hΛ1b : ∀ c ∈ Λ1, b.eval c ≠ 0 := fun c hc h => hΛ1 (Finset.mem_coe.2 hc) h
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : Finset K, Λ = E.image (fun e => e (xB K F)) ∪ Λ1 := ⟨_, rfl⟩
  have hΛb : ∀ c ∈ Λ, b.eval c ≠ 0 := by
    intro c hc
    rw [hΛ] at hc
    rcases Finset.mem_union.1 hc with h | h
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      exact hE e he
    · exact hΛ1b c h
  have hΛa : ∀ c ∈ Λ, a.eval c ≠ 0 := fun c hc => by
    have h := hΛb c hc
    rw [hb, eval_mul, eval_mul] at h
    exact left_ne_zero_of_mul (left_ne_zero_of_mul h)
  have hΛ1a1 : ∀ c ∈ Λ1, a1.eval c ≠ 0 := fun c hc => by
    have h := hΛ1b c hc
    rw [hb, eval_mul, eval_mul] at h
    exact right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have hΛ1Λ : Λ1 ⊆ Λ := by rw [hΛ]; exact Finset.subset_union_right
  have hN : N ≤ Λ.card := by
    have := Finset.card_le_card hΛ1Λ
    omega
  obtain ⟨hex, h1⟩ := hfam Λ hΛa hN
  have hs0 : secOf g Λ ≠ 0 := secOf_ne_zero hg0 Λ
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset (Rfin K F →ₐ[K] K), ∀ φ, φ ∈ Z ↔ φ (secOf g Λ) = 0 :=
    ⟨(finite_zero hs0).toFinset, fun φ => by rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]⟩
  obtain ⟨s1, Z1, -, -, -, -, hZ1x, hZ1c⟩ := hfib Λ1 hΛ1a1
  have hn : 0 < finrank K[X] (Rfin K F) :=
    (Module.finrank_pos_iff_of_free (R := K[X]) (M := Rfin K F)).2 inferInstance
  refine ⟨secOf g Λ, Z, hs0, hex, hZ, card_of_cnt_le_one hs0 (isInf_poleDiv _) hex h1 hZ, ?_, ?_, ?_, ?_⟩
  · exact (hZ φ0).2 ((apply_secOf φ0 g Λ).2 (Or.inl hφ0))
  · intro e he
    refine (hZ e).2 ((apply_secOf e g Λ).2 (Or.inr ?_))
    rw [hΛ]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
  · intro h0
    have h := hE φ0 h0
    rw [hb, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero] at h
    exact h rfl
  · have hsub : Z1 ⊆ Z := fun φ hφ =>
      (hZ φ).2 ((apply_secOf φ g Λ).2 (Or.inr (hΛ1Λ ((hZ1x φ).1 hφ))))
    have h2 := Finset.card_le_card hsub
    rw [hZ1c, hΛ1c] at h2
    have h3 : N + m ≤ (N + m) * finrank K[X] (Rfin K F) := Nat.le_mul_of_pos_right _ hn
    omega

/-- **`ν`-data of a piece**: `A = Z \ E = {φ0} ∪ c` has `ν(A) = E`. -/
theorem exists_nuE {s : Rfin K F} {Z E : Finset (Rfin K F →ₐ[K] K)} {φ0 : Rfin K F →ₐ[K] K}
    (hs0 : s ≠ 0) (hex : ExactPoleH s (poleDiv (K := K) (incB K F s))) (hZ : ∀ φ, φ ∈ Z ↔ φ s = 0)
    (hZc : (Z.card : ℤ) = (poleDiv (K := K) (incB K F s)).deg) (hφ0 : φ0 ∈ Z) (hEZ : E ⊆ Z)
    (hφ0E : φ0 ∉ E) (hEc : E.card = genusFK K F) (hNS : IsNS K F E) (hm : 2 * genusFK K F ≤ Z.card) :
    ∃ r : ℕ, ∃ D : NuData K F (1 + r), ∃ c : Fin r → (Rfin K F →ₐ[K] K),
      D.Hn = poleDiv (K := K) (incB K F s) ∧ insert φ0 (Finset.univ.image c) = Z \ E ∧
      ∀ y : SymRing K (Rfin K F) (1 + r) →ₐ[K] K, ptSet y = Z \ E → y D.good ≠ 0 ∧ D.nuF y = E := by
  have hA : φ0 ∈ Z \ E := Finset.mem_sdiff.2 ⟨hφ0, hφ0E⟩
  have hEle := Finset.card_le_card hEZ
  have hAc : (Z \ E).card + genusFK K F = Z.card := by
    rw [Finset.card_sdiff_of_subset hEZ, hEc]; omega
  obtain ⟨r, hr⟩ : ∃ r, (Z \ E).card = 1 + r :=
    ⟨(Z \ E).card - 1, by have := Finset.card_pos.2 ⟨φ0, hA⟩; omega⟩
  have hdeg : Places.Divisor.deg (poleDiv (K := K) (incB K F s)) = ((1 + r + genusFK K F : ℕ) : ℤ) := by
    rw [← hZc]
    exact_mod_cast (by omega : Z.card = 1 + r + genusFK K F)
  obtain ⟨D, hD, hrole⟩ := exists_role (d := 1 + r) (by omega) (isInf_poleDiv _) le_sup_right hdeg hs0 hex
    hZ (by omega) Finset.sdiff_subset hr (by rw [Finset.sdiff_sdiff_eq_self hEZ]; exact hNS)
  obtain ⟨c, -, hc⟩ := exists_enum (d := r) ((Z \ E).erase φ0) (by rw [Finset.card_erase_of_mem hA, hr]; omega)
  refine ⟨r, D, c, hD, ?_, fun y hy => ?_⟩
  · have e1 : Finset.univ.image c = (Z \ E).erase φ0 := by
      ext φ
      rw [Finset.mem_image, hc φ]
      simp only [Finset.mem_univ, true_and]
    rw [e1, Finset.insert_erase hA]
  · obtain ⟨h1, h2⟩ := hrole y hy
    exact ⟨h1, by rw [h2, Finset.sdiff_sdiff_eq_self hEZ]⟩

/-- **The class of `ν(A)`**: `[ν(A)] = [Hn] - [A]`. -/
theorem clsK_nuF {d : ℕ} {D : NuData K F d} {y : SymRing K (Rfin K F) d →ₐ[K] K} (hy : y D.good ≠ 0) :
    clsK K F (Zdiv (D.nuF y)) = clsK K F D.Hn - clsK K F (Zdiv (ptSet y)) := by
  have h0 : clsK K F (PlacesK.div (incB K F (D.sec y))) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 (div_mem_PrincK K F (incB_sec_ne_zero hy))
  rw [div_sec' hy, clsK_sub, clsK_add] at h0
  rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← h0]
  abel

variable {r : ℕ} (D : NuData K F (1 + r)) (c : Fin r → (Rfin K F →ₐ[K] K))

/-- The basic function of a piece: `good` at `Q + c`. -/
noncomputable def pieceF : Rfin K F :=
  padMap (phi1 (k := K) (B := Rfin K F)) c rfl D.good

theorem apply_pieceF (Q : Rfin K F →ₐ[K] K) : Q (pieceF D c) = padPt phi1 c rfl Q D.good := by
  rw [pieceF, ← comp_padMap, AlgHom.comp_apply]

theorem ptSet_padPt1 (Q : Rfin K F →ₐ[K] K) :
    ptSet (padPt (phi1 (k := K) (B := Rfin K F)) c rfl Q) = insert Q (Finset.univ.image c) := by
  rw [ptSet_padPt, ptSet_phi1, Finset.insert_eq]

/-- The coordinate ring `B[1/f]` of a piece. -/
abbrev PieceR : Type u := Localization.Away (pieceF D c)

/-- `B → B[1/f]`. -/
noncomputable abbrev pieceι : Rfin K F →ₐ[K] PieceR D c := IsScalarTower.toAlgHom K (Rfin K F) (PieceR D c)

theorem isUnit_pieceGood : IsUnit (((pieceι D c).comp (padMap phi1 c rfl)) D.good) :=
  IsLocalization.Away.algebraMap_isUnit (pieceF D c)

/-- `D(good) ← D(f)`, `Q ↦ Q + c`. -/
noncomputable def pieceLift : D.Rg →ₐ[K] PieceR D c :=
  IsLocalization.Away.liftAlgHom D.good (isUnit_pieceGood D c)

theorem yOf_pieceLift (x : PieceR D c →ₐ[K] K) :
    D.yOf (x.comp (pieceLift D c)) = padPt phi1 c rfl (x.comp (pieceι D c)) := by
  rw [← comp_padMap]
  ext t
  rw [NuData.yOf_apply, AlgHom.comp_apply, pieceLift, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

theorem good_padPt (x : PieceR D c →ₐ[K] K) : padPt phi1 c rfl (x.comp (pieceι D c)) D.good ≠ 0 := by
  rw [← apply_pieceF, AlgHom.comp_apply]
  exact ((IsLocalization.Away.algebraMap_isUnit (pieceF D c)).map x).ne_zero

end AJLoc

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacSymB_Chart =====
section

/-!
# S4-JacSymB, file F1: the affine charts of a curve (L12)

Curve data: a field `F` over `k` with a transcendental `x`. For a finite set `A ⊆ k` the chart ring `B_A` is the integral
closure in `F` of `P_A = k[1/(x - c) : c ∈ A]` (functions regular away from the poles of `x - c`, `c ∈ A`, i.e. on the
preimage of `ℙ¹ ∖ A`). For `c0 ∈ A ⊆ A'` the element `w = ∏_{d ∈ A' \ A} (x - d)/(x - c0)` lies in `P_A`, is a unit of
`P_A'`, and every element of `B_A'` becomes an element of `B_A` after multiplying by a power of `w`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section Chart

open Polynomial

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {x : F}

theorem sub_mul_uc {x : F} (hx : Transcendental k x) (c d : k) :
    (x - algebraMap k F d) * uc x c = 1 + algebraMap k F (c - d) * uc x c := by
  have h := sub_ne_zero_of_tr hx c
  rw [uc, map_sub]
  field_simp
  ring

/-- `P_A = k[1/(x - c) : c ∈ A]`. -/
noncomputable def polyA (x : F) (A : Finset k) : Subalgebra k F := Algebra.adjoin k (uc x '' (A : Set k))

theorem uc_mem_polyA (x : F) {A : Finset k} {c : k} (hc : c ∈ A) : uc x c ∈ polyA x A :=
  Algebra.subset_adjoin ⟨c, hc, rfl⟩

theorem polyA_mono (x : F) {A A' : Finset k} (h : A ⊆ A') : polyA x A ≤ polyA x A' :=
  Algebra.adjoin_mono (Set.image_mono (Finset.coe_subset.mpr h))

/-- The chart ring `B_A`: the integral closure of `P_A` in `F`. -/
noncomputable def chartRing (x : F) (A : Finset k) : Subalgebra k F :=
  (integralClosure (polyA x A) F).restrictScalars k

theorem mem_chartRing {x : F} {A : Finset k} {y : F} : y ∈ chartRing x A ↔ IsIntegral (polyA x A) y := Iff.rfl

theorem isIntegral_of_subalgebra_le {R R' : Subalgebra k F} (h : R ≤ R') {y : F} (hy : IsIntegral R y) :
    IsIntegral R' y := by
  obtain ⟨p, hp, hpy⟩ := hy
  refine ⟨p.map (Subalgebra.inclusion h).toRingHom, hp.map _, ?_⟩
  rw [eval₂_map]
  exact hpy

theorem polyA_le_chartRing (x : F) (A : Finset k) : polyA x A ≤ chartRing x A := fun y hy =>
  mem_chartRing.mpr (isIntegral_algebraMap (R := polyA x A) (x := ⟨y, hy⟩))

theorem chartRing_mono (x : F) {A A' : Finset k} (h : A ⊆ A') : chartRing x A ≤ chartRing x A' := fun _ hy =>
  mem_chartRing.mpr (isIntegral_of_subalgebra_le (polyA_mono x h) (mem_chartRing.mp hy))

/-- `w = ∏_{d ∈ D} (x - d)/(x - c0)`. -/
noncomputable def wt (x : F) (c0 : k) (D : Finset k) : F := ∏ d ∈ D, (x - algebraMap k F d) * uc x c0

theorem wt_mem (hx : Transcendental k x) {A : Finset k} {c0 : k} (hc0 : c0 ∈ A) (D : Finset k) :
    wt x c0 D ∈ polyA x A := by
  refine Subalgebra.prod_mem _ fun d _ => ?_
  rw [sub_mul_uc hx]
  exact Subalgebra.add_mem _ (Subalgebra.one_mem _)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (uc_mem_polyA x hc0))

theorem wt_ne_zero {x : F} (hx : Transcendental k x) (c0 : k) (D : Finset k) : wt x c0 D ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun d _ =>
    mul_ne_zero (sub_ne_zero_of_tr hx d) (inv_ne_zero (sub_ne_zero_of_tr hx c0))

theorem wt_inv_mem (hx : Transcendental k x) {A' D : Finset k} (hD : D ⊆ A') (c0 : k) :
    (wt x c0 D)⁻¹ ∈ polyA x A' := by
  rw [wt, ← Finset.prod_inv_distrib]
  refine Subalgebra.prod_mem _ fun d hd => ?_
  have h1 : ((x - algebraMap k F d) * uc x c0)⁻¹ = (x - algebraMap k F c0) * uc x d := by
    rw [uc, uc, mul_inv, inv_inv, mul_comm]
  rw [h1, sub_mul_uc hx]
  exact Subalgebra.add_mem _ (Subalgebra.one_mem _)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (uc_mem_polyA x (hD hd)))

theorem uc_mul_wt_mem (hx : Transcendental k x) {A D : Finset k} {c0 d : k} (hc0 : c0 ∈ A) (hd : d ∈ D) :
    uc x d * wt x c0 D ∈ polyA x A := by
  classical
  rw [wt, ← Finset.mul_prod_erase D _ hd, ← mul_assoc, ← mul_assoc]
  have h1 : uc x d * (x - algebraMap k F d) = 1 := inv_mul_cancel₀ (sub_ne_zero_of_tr hx d)
  rw [h1, one_mul]
  exact Subalgebra.mul_mem _ (uc_mem_polyA x hc0) (wt_mem hx hc0 _)

theorem pow_mul_mem_of_le {R : Subalgebra k F} {w y : F} (hw : w ∈ R) {m n : ℕ} (hmn : m ≤ n)
    (h : w ^ m * y ∈ R) : w ^ n * y ∈ R := by
  rw [← Nat.sub_add_cancel hmn, pow_add, mul_assoc]
  exact R.mul_mem (R.pow_mem hw _) h

theorem exists_pow_mul_mem_polyA [DecidableEq k] (hx : Transcendental k x) {A A' : Finset k} {c0 : k} (hc0 : c0 ∈ A)
    {y : F} (hy : y ∈ polyA x A') : ∃ n : ℕ, wt x c0 (A' \ A) ^ n * y ∈ polyA x A := by
  have hw := wt_mem hx hc0 (A' \ A)
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    by_cases hcA : c ∈ A
    · exact ⟨0, by rw [pow_zero, one_mul]; exact uc_mem_polyA x hcA⟩
    · refine ⟨1, ?_⟩
      rw [pow_one, mul_comm]
      exact uc_mul_wt_mem hx hc0 (Finset.mem_sdiff.mpr ⟨hc, hcA⟩)
  | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [mul_add]
    exact Subalgebra.add_mem _ (pow_mul_mem_of_le hw (Nat.le_add_right m n) hm)
      (pow_mul_mem_of_le hw (Nat.le_add_left n m) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [pow_add, mul_mul_mul_comm]
    exact Subalgebra.mul_mem _ hm hn

/-- Clearing denominators in an integral equation: if `R'` lies in `R[1/w]`, then a multiple `w^n b` of an element `b`
integral over `R'` is integral over `R`. -/
theorem exists_pow_mul_isIntegral {R R' : Subalgebra k F} {w : F} (hw : w ∈ R)
    (h : ∀ y ∈ R', ∃ n : ℕ, w ^ n * y ∈ R) {b : F} (hb : IsIntegral R' b) :
    ∃ n : ℕ, IsIntegral R (w ^ n * b) := by
  obtain ⟨p, hp, hpb⟩ := hb
  set q : F[X] := p.map (algebraMap R' F) with hqdef
  have hq : q.Monic := hp.map _
  have hqb : q.eval b = 0 := by rw [hqdef, eval_map]; exact hpb
  have hcoeff : ∀ i, q.coeff i ∈ R' := fun i => by
    rw [hqdef, coeff_map]
    exact (p.coeff i).2
  choose m hm using fun i => h _ (hcoeff i)
  set N := ∑ i ∈ Finset.range (q.natDegree + 1), m i
  have hN : ∀ i ≤ q.natDegree, w ^ N * q.coeff i ∈ R := fun i hi =>
    pow_mul_mem_of_le hw (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))) (hm i)
  have hc : ∀ i, q.coeff i * (w ^ N) ^ (q.natDegree - i) ∈ R := by
    intro i
    rcases lt_trichotomy i q.natDegree with hi | hi | hi
    · obtain ⟨j, hj⟩ : ∃ j, q.natDegree - i = j + 1 := ⟨q.natDegree - i - 1, by omega⟩
      have e : q.coeff i * (w ^ N) ^ (j + 1) = (w ^ N) ^ j * (w ^ N * q.coeff i) := by ring
      rw [hj, e]
      exact R.mul_mem (R.pow_mem (R.pow_mem hw _) _) (hN i hi.le)
    · rw [hi, hq.coeff_natDegree, Nat.sub_self, pow_zero, one_mul]
      exact R.one_mem
    · rw [coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact R.zero_mem
  have hlift : q.scaleRoots (w ^ N) ∈ Polynomial.lifts (algebraMap R F) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    exact ⟨⟨_, hc i⟩, rfl⟩
  obtain ⟨p', hp'1, -, hp'2⟩ :=
    lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff _).mpr hq)
  refine ⟨N, p', hp'2, ?_⟩
  rw [← eval_map, hp'1, scaleRoots_eval_mul, hqb, mul_zero]

theorem exists_pow_mul_mem_chartRing [DecidableEq k] (hx : Transcendental k x) {A A' : Finset k} {c0 : k} (hc0 : c0 ∈ A)
    {y : F} (hy : y ∈ chartRing x A') : ∃ n : ℕ, wt x c0 (A' \ A) ^ n * y ∈ chartRing x A :=
  exists_pow_mul_isIntegral (wt_mem hx hc0 _) (fun _ hz => exists_pow_mul_mem_polyA hx hc0 hz) (mem_chartRing.mp hy)

theorem wt_mem_chartRing (hx : Transcendental k x) {A : Finset k} {c0 : k} (hc0 : c0 ∈ A) (D : Finset k) :
    wt x c0 D ∈ chartRing x A :=
  polyA_le_chartRing x A (wt_mem hx hc0 D)

theorem wt_inv_mem_chartRing (hx : Transcendental k x) {A' D : Finset k} (hD : D ⊆ A') (c0 : k) :
    (wt x c0 D)⁻¹ ∈ chartRing x A' :=
  polyA_le_chartRing x A' (wt_inv_mem hx hD c0)

end Chart

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymB_ChartDed =====
section

/-!
# S4-JacSymB, file F3: the chart rings are finitely generated; the singleton charts are Dedekind (L12)

Curve data as in file F1, plus: `F / k⟮x⟯` finite separable. Then `B_{c} = ` integral closure of `k[1/(x - c)] ≅ k[X]`
in `F` is a Dedekind domain, finite over `k[1/(x-c)]`, and not a field; every chart ring `B_A` is a finitely generated
`k`-algebra (`B_A = B_{c0}[1/w]`).
-/

set_option autoImplicit false

open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

namespace RamanujanPetersson.JacSym

section ChartDed

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {x : F}

theorem transcendental_uc (hx : Transcendental k x) (c : k) : Transcendental k (uc x c) := by
  intro h
  apply hx
  have h1 : IsAlgebraic k (x - algebraMap k F c) := IsAlgebraic.inv_iff.mp h
  simpa using h1.add (isAlgebraic_algebraMap (R := k) (A := F) c)

theorem polyA_singleton (x : F) (c : k) : polyA x {c} = Algebra.adjoin k {uc x c} := by
  rw [polyA, Finset.coe_singleton, Set.image_singleton]

theorem adjoin_uc_eq (hx : Transcendental k x) (c : k) : k⟮uc x c⟯ = k⟮x⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (sub_mem (IntermediateField.mem_adjoin_simple_self k x) (IntermediateField.algebraMap_mem _ c))
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h : (uc x c)⁻¹ + algebraMap k F c = x := by rw [uc, inv_inv, sub_add_cancel]
    exact (congrArg (· ∈ k⟮uc x c⟯) h).mp
      (add_mem (inv_mem (IntermediateField.mem_adjoin_simple_self k (uc x c))) (IntermediateField.algebraMap_mem _ c))

theorem isPrincipalIdealRing_adjoin_uc (hx : Transcendental k x) (c : k) :
    IsPrincipalIdealRing (Algebra.adjoin k {uc x c}) :=
  IsPrincipalIdealRing.of_surjective
    (Polynomial.algEquivOfTranscendental k (uc x c) (transcendental_uc hx c)).toRingEquiv.toRingHom
    (Polynomial.algEquivOfTranscendental k (uc x c) (transcendental_uc hx c)).surjective

theorem not_isField_adjoin_uc (hx : Transcendental k x) (c : k) : ¬IsField (Algebra.adjoin k {uc x c}) := fun h =>
  Polynomial.not_isField k
    (MulEquiv.isField h (Polynomial.algEquivOfTranscendental k (uc x c) (transcendental_uc hx c)).toMulEquiv)

theorem not_isField_chartRing_single (hx : Transcendental k x) (c : k) : ¬IsField (chartRing x {c}) := by
  have key : ∀ P : Subalgebra k F, P = Algebra.adjoin k {uc x c} →
      ¬IsField ((integralClosure P F).restrictScalars k) := by
    intro P hP h
    subst hP
    have hinj : Function.Injective
        (algebraMap (Algebra.adjoin k {uc x c}) (integralClosure (Algebra.adjoin k {uc x c}) F)) := by
      intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simpa using this
    exact not_isField_adjoin_uc hx c ((Algebra.IsIntegral.isField_iff_isField hinj).mpr h)
  exact key _ (polyA_singleton x c)

variable [FiniteDimensional k⟮x⟯ F] [Algebra.IsSeparable k⟮x⟯ F]

theorem finite_integralClosure_uc (hx : Transcendental k x) (c : k) :
    Module.Finite (Algebra.adjoin k {uc x c}) (integralClosure (Algebra.adjoin k {uc x c}) F) := by
  have hK : k⟮uc x c⟯ = k⟮x⟯ := adjoin_uc_eq hx c
  have : FiniteDimensional k⟮uc x c⟯ F := hK ▸ inferInstance
  have : Algebra.IsSeparable k⟮uc x c⟯ F := hK ▸ inferInstance
  have := isPrincipalIdealRing_adjoin_uc hx c
  exact IsIntegralClosure.finite (Algebra.adjoin k {uc x c}) k⟮uc x c⟯ F _

theorem isDedekindDomain_chartRing_single (hx : Transcendental k x) (c : k) : IsDedekindDomain (chartRing x {c}) := by
  have hK : k⟮uc x c⟯ = k⟮x⟯ := adjoin_uc_eq hx c
  have : FiniteDimensional k⟮uc x c⟯ F := hK ▸ inferInstance
  have : Algebra.IsSeparable k⟮uc x c⟯ F := hK ▸ inferInstance
  have := isPrincipalIdealRing_adjoin_uc hx c
  have key : ∀ P : Subalgebra k F, P = Algebra.adjoin k {uc x c} →
      IsDedekindDomain ((integralClosure P F).restrictScalars k) := by
    intro P hP
    subst hP
    exact integralClosure.isDedekindDomain (Algebra.adjoin k {uc x c}) k⟮uc x c⟯ F
  exact key _ (polyA_singleton x c)

theorem fg_chartRing_single (hx : Transcendental k x) (c : k) : (chartRing x {c}).FG := by
  classical
  have key : ∀ P : Subalgebra k F, P = Algebra.adjoin k {uc x c} → ((integralClosure P F).restrictScalars k).FG := by
    intro P hP
    subst hP
    have hfin := finite_integralClosure_uc hx c
    have hfg : (integralClosure (Algebra.adjoin k {uc x c}) F).FG :=
      Subalgebra.fg_of_fg_toSubmodule (Module.Finite.iff_fg.mp hfin)
    obtain ⟨t, ht⟩ := hfg
    refine ⟨insert (uc x c) t, ?_⟩
    rw [Finset.coe_insert, Set.insert_eq, Algebra.adjoin_union_eq_adjoin_adjoin, ht]
  exact key _ (polyA_singleton x c)

theorem fg_chartRing [DecidableEq k] (hx : Transcendental k x) {A : Finset k} {c0 : k} (hc0 : c0 ∈ A) :
    (chartRing x A).FG := by
  classical
  obtain ⟨t, ht⟩ := fg_chartRing_single hx c0
  refine ⟨insert (wt x c0 (A \ {c0}))⁻¹ t, le_antisymm ?_ ?_⟩
  · rw [Algebra.adjoin_le_iff]
    intro y hy
    rw [Finset.coe_insert] at hy
    rcases hy with rfl | hy
    · exact wt_inv_mem_chartRing hx Finset.sdiff_subset c0
    · refine chartRing_mono x (Finset.singleton_subset_iff.mpr hc0) ?_
      rw [← ht]
      exact Algebra.subset_adjoin hy
  · intro y hy
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartRing (A := {c0}) hx (Finset.mem_singleton_self c0) hy
    have hy' : y = ((wt x c0 (A \ {c0}))⁻¹) ^ n * (wt x c0 (A \ {c0}) ^ n * y) := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (wt_ne_zero hx c0 _), one_pow, one_mul]
    rw [hy']
    refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Algebra.subset_adjoin ?_) _) ?_
    · rw [Finset.coe_insert]
      exact Set.mem_insert _ _
    · rw [← ht] at hn
      refine Algebra.adjoin_mono ?_ hn
      rw [Finset.coe_insert]
      exact Set.subset_insert _ _

theorem finiteType_chartRing (hx : Transcendental k x) {A : Finset k} (hA : A.Nonempty) :
    Algebra.FiniteType k (chartRing x A) := by
  classical
  obtain ⟨c0, hc0⟩ := hA
  exact (Subalgebra.fg_iff_finiteType _).mp (fg_chartRing hx hc0)

end ChartDed

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacComplete_Syn =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Syn` (dictionary D2: the chart coordinate `1/(x - c)`)

* `mobU K c = 1/(X - c)` and the Möbius automorphism `tau K c : K(X) →ₐ[K] K(X)`, `X ↦ 1/(X - c)`
  (`tau_algebraMap`, `tau_X`, `tau_surjective`, `tauEquiv`);
* `SynF K F c`: a type synonym of `F` carrying the function-field package whose coordinate is
  `x' = 1/(x - c)` (`synAlg_apply`, `synAlg_X`), with `FunctionField` and separability transported;
* `synEquiv K F c : F ≃ₐ[K] SynF K F c` and the induced bijection of places `synPlace` preserving `ord`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place)

section Mob

variable (K : Type*) [Field K]

/-- The Möbius coordinate `1/(X - c)` of `K(X)`. -/
noncomputable def mobU (c : K) : RatFunc K := JacSym.uc (RatFunc.X : RatFunc K) c

theorem transcendental_mobU (c : K) : Transcendental K (mobU K c) :=
  JacSym.transcendental_uc RatFunc.transcendental_X c

theorem le_comap_mobU (c : K) :
    nonZeroDivisors K[X] ≤ (nonZeroDivisors (RatFunc K)).comap (aeval (mobU K c) : K[X] →ₐ[K] RatFunc K) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (transcendental_iff_injective.1 (transcendental_mobU K c))

/-- The `K`-algebra endomorphism `X ↦ 1/(X - c)` of `K(X)`. -/
noncomputable def tau (c : K) : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.liftAlgHom (aeval (mobU K c)) (le_comap_mobU K c)

theorem tau_algebraMap (c : K) (p : K[X]) :
    tau K c (algebraMap K[X] (RatFunc K) p) = aeval (mobU K c) p := by
  have h := RatFunc.liftAlgHom_apply_div (aeval (mobU K c)) (le_comap_mobU K c) p 1
  simp only [map_one, div_one] at h
  exact h

theorem tau_X (c : K) : tau K c RatFunc.X = mobU K c := by
  rw [← RatFunc.algebraMap_X, tau_algebraMap, aeval_X]

theorem tau_X_inv (c : K) :
    tau K c ((RatFunc.X : RatFunc K)⁻¹ + algebraMap K (RatFunc K) c) = RatFunc.X := by
  rw [map_add, map_inv₀, tau_X, AlgHom.commutes, mobU, JacSym.uc, inv_inv, sub_add_cancel]

theorem algebraMap_eq_aeval_X (p : K[X]) :
    algebraMap K[X] (RatFunc K) p = aeval (RatFunc.X : RatFunc K) p := by
  rw [← RatFunc.algebraMap_X, aeval_algebraMap_apply, aeval_X_left_apply]

theorem tau_surjective (c : K) : Function.Surjective (tau K c) := by
  intro f
  have hp : ∀ p : K[X], algebraMap K[X] (RatFunc K) p =
      tau K c (aeval ((RatFunc.X : RatFunc K)⁻¹ + algebraMap K (RatFunc K) c) p) := fun p => by
    rw [← Polynomial.aeval_algHom_apply (tau K c), tau_X_inv, algebraMap_eq_aeval_X]
  refine ⟨aeval ((RatFunc.X : RatFunc K)⁻¹ + algebraMap K (RatFunc K) c) f.num /
    aeval ((RatFunc.X : RatFunc K)⁻¹ + algebraMap K (RatFunc K) c) f.denom, ?_⟩
  rw [map_div₀, ← hp, ← hp, RatFunc.num_div_denom]

/-- `tau K c` as an automorphism. -/
noncomputable def tauEquiv (c : K) : RatFunc K ≃ₐ[K] RatFunc K :=
  AlgEquiv.ofBijective (tau K c) ⟨(tau K c).toRingHom.injective, tau_surjective K c⟩

theorem tau_tauEquiv_symm (c : K) (r : RatFunc K) : tau K c ((tauEquiv K c).symm r) = r :=
  (tauEquiv K c).apply_symm_apply r

end Mob

section Syn

variable (K : Type*) [Field K] (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F]
  [Algebra (RatFunc K) F] [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] (c : K)

/-- The function field `F` with the coordinate `1/(x - c)` (a type synonym of `F`). -/
def SynF (K : Type*) [Field K] (F : Type*) (_c : K) : Type _ := F

noncomputable instance : Field (SynF K F c) := inferInstanceAs (Field F)

noncomputable instance : Algebra K (SynF K F c) := inferInstanceAs (Algebra K F)

/-- The new structure map `K(X) → F`, `X ↦ 1/(x - c)`. -/
noncomputable def synMap : RatFunc K →+* SynF K F c :=
  (algebraMap (RatFunc K) F).comp (tau K c).toRingHom

noncomputable instance : Algebra (RatFunc K) (SynF K F c) := (synMap K F c).toAlgebra

noncomputable instance : Algebra K[X] (SynF K F c) :=
  ((algebraMap (RatFunc K) (SynF K F c)).comp (algebraMap K[X] (RatFunc K))).toAlgebra

instance : IsScalarTower K[X] (RatFunc K) (SynF K F c) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The identification `F ≃ SynF K F c` (the identity map). -/
def synEquiv : F ≃ₐ[K] SynF K F c where
  toFun y := y
  invFun y := y
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem ratAlg_const (a : K) :
    algebraMap (RatFunc K) F (algebraMap K (RatFunc K) a) = algebraMap K F a := by
  rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) F,
    ← IsScalarTower.algebraMap_apply K K[X] F]

theorem ratAlg_X : algebraMap (RatFunc K) F RatFunc.X = algebraMap K[X] F X := by
  rw [← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply]

instance : IsScalarTower K K[X] (SynF K F c) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap K F a = algebraMap (RatFunc K) F (tau K c (algebraMap K[X] (RatFunc K) (algebraMap K K[X] a)))
    have h1 : tau K c (algebraMap K[X] (RatFunc K) (algebraMap K K[X] a)) =
        algebraMap K[X] (RatFunc K) (algebraMap K K[X] a) := by
      rw [← IsScalarTower.algebraMap_apply K K[X] (RatFunc K), AlgHom.commutes]
    rw [h1, ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) F, ← IsScalarTower.algebraMap_apply K K[X] F])

theorem ratAlg_mobU :
    algebraMap (RatFunc K) F (mobU K c) = JacSym.uc (algebraMap K[X] F X) c := by
  simp only [mobU, JacSym.uc, map_inv₀, map_sub, ratAlg_const, ratAlg_X]

/-- The new structure map on polynomials: `p ↦ p(1/(x - c))`. -/
theorem synAlg_apply (p : K[X]) :
    algebraMap K[X] (SynF K F c) p = synEquiv K F c (aeval (JacSym.uc (algebraMap K[X] F X) c) p) := by
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq (fun a => (ratAlg_const K F a).symm)
  show algebraMap (RatFunc K) F (tau K c (algebraMap K[X] (RatFunc K) p)) =
    aeval (JacSym.uc (algebraMap K[X] F X) c) p
  rw [tau_algebraMap, ← Polynomial.aeval_algebraMap_apply, ratAlg_mobU]

/-- The new coordinate is `x' = 1/(x - c)`. -/
theorem synAlg_X :
    algebraMap K[X] (SynF K F c) X = synEquiv K F c (JacSym.uc (algebraMap K[X] F X) c) := by
  rw [synAlg_apply, aeval_X]

instance [FunctionField K F] : FunctionField K (SynF K F c) := by
  have h1 : (algebraMap (RatFunc K) F).Finite := RingHom.finite_algebraMap.2 inferInstance
  have h2 : ((tau K c).toRingHom : RatFunc K →+* RatFunc K).Finite :=
    RingHom.Finite.of_surjective _ (tau_surjective K c)
  have h : (synMap K F c).Finite := h1.comp h2
  exact RingHom.finite_algebraMap.1 h

instance [Algebra.IsSeparable (RatFunc K) F] : Algebra.IsSeparable (RatFunc K) (SynF K F c) :=
  Algebra.IsSeparable.of_equiv_equiv (tauEquiv K c).symm.toRingEquiv (synEquiv K F c).toRingEquiv
    (RingHom.ext fun r => by
      show algebraMap (RatFunc K) F (tau K c ((tauEquiv K c).symm r)) = algebraMap (RatFunc K) F r
      rw [tau_tauEquiv_symm])

end Syn

section SynPlace

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- The places of `F` and of the chart synonym `SynF K F c` agree. -/
noncomputable def synPlace (c : K) : Place K F ≃ Place K (SynF K F c) := placeEquiv (synEquiv K F c)

end SynPlace

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_RfinSyn =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `RfinSyn`: chart rings are finite rings of the chart synonyms

For `x = algebraMap K[X] F X` and `c : K`, the chart ring `chartRing x {c}` (the integral closure of `K[1/(x - c)]`)
is the ring of `x'`-integers of the synonym `SynF K F c` (coordinate `x' = 1/(x - c)`), as subsets of `F`:
* `ucPoly c : K[X] →ₐ[K] K[1/(x - c)]` (surjective), `synAlg_eq` (the structure map of `SynF` factors through it);
* **`mem_rfinSyn_iff`**, `chartRing_map_synEquiv`, `rfinSynEquiv : chartRing x {c} ≃ₐ[K] (x'-integers)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

section RfinSyn

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F]
  [Algebra (RatFunc K) F] [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] (c : K)

/-- `K[X] → K[1/(x - c)]`, `X ↦ 1/(x - c)`. -/
noncomputable def ucPoly : K[X] →ₐ[K] JacSym.polyA (algebraMap K[X] F X) {c} :=
  aeval (⟨JacSym.uc (algebraMap K[X] F X) c, JacSym.uc_mem_polyA _ (Finset.mem_singleton_self c)⟩ :
    JacSym.polyA (algebraMap K[X] F X) {c})

theorem ucPoly_coe (p : K[X]) :
    ((ucPoly (F := F) c p : JacSym.polyA (algebraMap K[X] F X) {c}) : F) =
      aeval (JacSym.uc (algebraMap K[X] F X) c) p :=
  (Polynomial.aeval_algHom_apply (JacSym.polyA (algebraMap K[X] F X) {c}).val _ p).symm

theorem ucPoly_surjective : Function.Surjective (ucPoly (F := F) c) := by
  rintro ⟨y, hy⟩
  have hy' : y ∈ Algebra.adjoin K {JacSym.uc (algebraMap K[X] F X) c} := by
    simpa [JacSym.polyA, Finset.coe_singleton, Set.image_singleton] using hy
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
  obtain ⟨p, rfl⟩ := hy'
  exact ⟨p, Subtype.ext (ucPoly_coe c p)⟩

/-- The structure map of `SynF K F c` is `K[X] → K[1/(x - c)] ⊆ F`. -/
theorem synAlg_eq :
    (algebraMap K[X] (SynF K F c) : K[X] →+* F) =
      (algebraMap (JacSym.polyA (algebraMap K[X] F X) {c}) F).comp (ucPoly (F := F) c).toRingHom :=
  RingHom.ext fun p => by
    show algebraMap K[X] (SynF K F c) p = ((ucPoly (F := F) c p : JacSym.polyA (algebraMap K[X] F X) {c}) : F)
    rw [synAlg_apply, ucPoly_coe]
    rfl

/-- **The chart ring `B_{c}` is the ring of `x'`-integers of `SynF K F c`.** -/
theorem mem_rfinSyn_iff (y : F) :
    synEquiv K F c y ∈ integralClosure K[X] (SynF K F c) ↔ y ∈ JacSym.chartRing (algebraMap K[X] F X) {c} := by
  rw [mem_integralClosure_iff, JacSym.mem_chartRing]
  constructor
  · intro h
    exact h.map_of_comp_eq (ucPoly (F := F) c).toRingHom (synEquiv K F c).symm.toRingEquiv.toRingHom
      (by rw [← synAlg_eq]; rfl)
  · rintro ⟨p, hp, hpy⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective (f := (ucPoly (F := F) c).toRingHom) (ucPoly_surjective c) p) hp
    refine ⟨q, hqm, ?_⟩
    show eval₂ (algebraMap K[X] (SynF K F c) : K[X] →+* F) y q = 0
    refine (congrArg (fun φ : K[X] →+* F => eval₂ φ y q) (synAlg_eq (F := F) c)).trans ?_
    show eval₂ ((algebraMap (JacSym.polyA (algebraMap K[X] F X) {c}) F).comp (ucPoly (F := F) c).toRingHom) y q = 0
    rw [← eval₂_map, hq, hpy]

theorem chartRing_map_synEquiv :
    (JacSym.chartRing (algebraMap K[X] F X) {c}).map (synEquiv K F c).toAlgHom =
      (integralClosure K[X] (SynF K F c)).restrictScalars K := by
  ext z
  rw [Subalgebra.mem_restrictScalars, Subalgebra.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_rfinSyn_iff c y).2 hy
  · intro hz
    exact ⟨(synEquiv K F c).symm z, (mem_rfinSyn_iff c _).1 (by simpa using hz), by simp⟩

/-- `B_{c} ≃ₐ[K]` the `x'`-integers of the chart synonym. -/
noncomputable def rfinSynEquiv : JacSym.chartRing (algebraMap K[X] F X) {c} ≃ₐ[K]
    (integralClosure K[X] (SynF K F c)).restrictScalars K :=
  ((synEquiv K F c).subalgebraMap _).trans (Subalgebra.equivOfEq _ _ (chartRing_map_synEquiv c))

theorem rfinSynEquiv_coe (y : JacSym.chartRing (algebraMap K[X] F X) {c}) :
    ((rfinSynEquiv c y : (integralClosure K[X] (SynF K F c)).restrictScalars K) : SynF K F c) =
      synEquiv K F c y := rfl

end RfinSyn

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_Center =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Center` (the place of a `K`-point of a chart of `X1`)

For `x = algebraMap K[X] F X` and a nonempty finset `A ⊆ K`, the chart ring `B_A = chartRing x A`.
* `IsCenter R ψ`: the place `R` is `≤ 1` on `B_A` and `< 1` exactly on `ker ψ` (`ψ : B_A →ₐ[K] K`).
* `isCenter_restrict` / `isCenter_extend`: centers pass between `B_A ⊆ B_A'` (`B_A' ⊆ B_A[1/w]`, `wt` lemmas).
* `rfinG c : B_{c} ≃ₐ[K] Rfin K (SynF K F c)`, `ptSyn c ψ`, **`plc c ψ`** `:= (synPlace c).symm (inl (ptP (ptSyn c ψ)))`.
* **`isCenter_plc`**, **`eq_plc_of_isCenter`** (uniqueness), `isCenter_unique`, **`plc_eq_plc`** (chart independence).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial
open scoped WithZero

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw
open RamanujanPetersson.JacSym (chartRing wt chartRing_mono)

section Center

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- The place `R` is the center of the `K`-point `ψ` of the chart ring `B_A`. -/
def IsCenter (R : Place K F) {A : Finset K} (ψ : chartRing (algebraMap K[X] F X) A →ₐ[K] K) : Prop :=
  (∀ y : chartRing (algebraMap K[X] F X) A, placeVal R (y : F) ≤ 1) ∧
    ∀ y : chartRing (algebraMap K[X] F X) A, placeVal R (y : F) < 1 ↔ ψ y = 0

theorem isCenter_restrict {R : Place K F} {A A' : Finset K} (h : A ⊆ A')
    (ψ : chartRing (algebraMap K[X] F X) A' →ₐ[K] K) (hR : IsCenter R ψ) :
    IsCenter R (ψ.comp (Subalgebra.inclusion (chartRing_mono _ h))) := by
  refine ⟨fun y => ?_, fun y => ?_⟩
  · have h1 := hR.1 (Subalgebra.inclusion (chartRing_mono _ h) y)
    rwa [Subalgebra.coe_inclusion] at h1
  · have h1 := hR.2 (Subalgebra.inclusion (chartRing_mono _ h) y)
    rwa [Subalgebra.coe_inclusion, ← AlgHom.comp_apply] at h1

theorem isCenter_extend [DecidableEq K] {R : Place K F} {A A' : Finset K} (h : A ⊆ A') {c0 : K} (hc0 : c0 ∈ A)
    (ψ : chartRing (algebraMap K[X] F X) A' →ₐ[K] K)
    (hR : IsCenter R (ψ.comp (Subalgebra.inclusion (chartRing_mono _ h)))) : IsCenter R ψ := by
  have hx := transcendental_xF K F
  have hR2 : ∀ y : chartRing (algebraMap K[X] F X) A, placeVal R (y : F) < 1 ↔
      ψ (Subalgebra.inclusion (chartRing_mono _ h) y) = 0 := fun y => by
    rw [hR.2 y, AlgHom.comp_apply]
  have hwA : wt (algebraMap K[X] F X) c0 (A' \ A) ∈ chartRing (algebraMap K[X] F X) A := JacSym.wt_mem_chartRing hx hc0 _
  have hwinv : (wt (algebraMap K[X] F X) c0 (A' \ A))⁻¹ ∈ chartRing (algebraMap K[X] F X) A' :=
    JacSym.wt_inv_mem_chartRing hx Finset.sdiff_subset c0
  have hψw : ψ (Subalgebra.inclusion (chartRing_mono _ h) ⟨_, hwA⟩) ≠ 0 := by
    intro h0
    have e1 : Subalgebra.inclusion (chartRing_mono _ h) ⟨_, hwA⟩ * ⟨_, hwinv⟩ = 1 :=
      Subtype.ext (mul_inv_cancel₀ (JacSym.wt_ne_zero hx c0 _))
    have e2 := congrArg ψ e1
    rw [map_mul, h0, zero_mul, map_one] at e2
    exact zero_ne_one e2
  have hvw : placeVal R (wt (algebraMap K[X] F X) c0 (A' \ A)) = 1 :=
    le_antisymm (hR.1 ⟨_, hwA⟩) (not_lt.1 fun hlt => hψw ((hR2 ⟨_, hwA⟩).1 hlt))
  have e1 : ∀ (n : ℕ) (y : F), placeVal R (wt (algebraMap K[X] F X) c0 (A' \ A) ^ n * y) = placeVal R y := fun n y => by
    rw [map_mul, map_pow, hvw, one_pow, one_mul]
  refine ⟨fun y => ?_, fun y => ?_⟩
  · obtain ⟨n, hn⟩ := JacSym.exists_pow_mul_mem_chartRing hx hc0 y.2
    have h1 : placeVal R (wt (algebraMap K[X] F X) c0 (A' \ A) ^ n * y) ≤ 1 := hR.1 ⟨_, hn⟩
    rwa [e1] at h1
  · obtain ⟨n, hn⟩ := JacSym.exists_pow_mul_mem_chartRing hx hc0 y.2
    have h1 : placeVal R (wt (algebraMap K[X] F X) c0 (A' \ A) ^ n * y) < 1 ↔
        ψ (Subalgebra.inclusion (chartRing_mono _ h) ⟨_, hn⟩) = 0 := hR2 ⟨_, hn⟩
    have e2 : Subalgebra.inclusion (chartRing_mono _ h) (⟨_, hn⟩ : chartRing (algebraMap K[X] F X) A) =
        (Subalgebra.inclusion (chartRing_mono _ h) ⟨_, hwA⟩) ^ n * y := Subtype.ext (by simp)
    rw [e1, e2, map_mul, map_pow] at h1
    rw [h1, mul_eq_zero, or_iff_right (pow_ne_zero n hψw)]

variable (c : K)

/-- `B_{c}` as the ring of `x'`-integers `Rfin K (SynF K F c)`. -/
noncomputable def rfinG : chartRing (algebraMap K[X] F X) {c} ≃ₐ[K] Rfin K (SynF K F c) :=
  (rfinSynEquiv c).trans
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }

theorem rfinG_coe (y : chartRing (algebraMap K[X] F X) {c}) :
    ((rfinG c y : Rfin K (SynF K F c)) : SynF K F c) = synEquiv K F c y := rfl

theorem placeVal_synPlace (R : Place K F) (f : F) :
    placeVal (synPlace c R) (synEquiv K F c f) = placeVal R f := by
  rw [synPlace, placeEquiv_apply, placeVal_placeMap, Valuation.comap_apply]
  have e : ((synEquiv K F c).symm : SynF K F c →+* F) (synEquiv K F c f) = f :=
    (synEquiv K F c).symm_apply_apply f
  rw [e]

variable [IsAlgClosed K]

/-- The `K`-point of `Rfin K (SynF K F c)` attached to a `K`-point of `B_{c}`. -/
noncomputable def ptSyn (ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K) : Rfin K (SynF K F c) →ₐ[K] K :=
  ψ.comp (rfinG c).symm.toAlgHom

theorem ptSyn_rfinG (ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K) (y : chartRing (algebraMap K[X] F X) {c}) :
    ptSyn c ψ (rfinG c y) = ψ y := by
  simp [ptSyn]

/-- **The place of a `K`-point of the chart `{c}`.** -/
noncomputable def plc (ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K) : Place K F :=
  (synPlace c).symm (Sum.inl (ptP (ptSyn c ψ)))

theorem synPlace_plc (ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K) :
    synPlace c (plc c ψ) = Sum.inl (ptP (ptSyn c ψ)) :=
  Equiv.apply_symm_apply _ _

theorem placeVal_plc (ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K) (y : chartRing (algebraMap K[X] F X) {c}) :
    placeVal (plc c ψ) (y : F) = (ptP (ptSyn c ψ)).valuation (SynF K F c)
      (algebraMap (Rfin K (SynF K F c)) (SynF K F c) (rfinG c y)) := by
  rw [← placeVal_synPlace c, synPlace_plc, placeVal_inl]
  rfl

theorem isCenter_plc (ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K) : IsCenter (plc c ψ) ψ := by
  refine ⟨fun y => ?_, fun y => ?_⟩
  · rw [placeVal_plc]
    exact HeightOneSpectrum.valuation_le_one (K := SynF K F c) _ _
  · rw [placeVal_plc, HeightOneSpectrum.valuation_lt_one_iff_mem (K := SynF K F c), mem_ptP, ptSyn_rfinG]

/-- **Uniqueness of the center on the chart `{c}`.** -/
theorem eq_plc_of_isCenter {R : Place K F} {ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K}
    (hR : IsCenter R ψ) : R = plc c ψ := by
  apply (synPlace c).injective
  rw [synPlace_plc]
  have hbv : ∀ b : Rfin K (SynF K F c), placeVal (synPlace c R) (b : SynF K F c) =
      placeVal R (((rfinG c).symm b : chartRing (algebraMap K[X] F X) {c}) : F) := fun b => by
    have e : (b : SynF K F c) = synEquiv K F c (((rfinG c).symm b : chartRing (algebraMap K[X] F X) {c}) : F) := by
      rw [← rfinG_coe, AlgEquiv.apply_symm_apply]
    rw [e, placeVal_synPlace]
  rcases hRc : synPlace c R with P | Q
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    have h1 : ∀ b, ptSyn c ψ b = 0 → φ b = 0 := fun b hb0 => by
      have h2 : placeVal R (((rfinG c).symm b : chartRing (algebraMap K[X] F X) {c}) : F) < 1 :=
        (hR.2 _).2 hb0
      rw [← hbv b, hRc, placeVal_inl] at h2
      exact mem_ptP.1 ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := SynF K F c) _ b).1 h2)
    suffices hφ : φ = ptSyn c ψ by rw [hφ]
    refine AlgHom.ext fun b => ?_
    have ht := h1 (b - algebraMap K (Rfin K (SynF K F c)) (ptSyn c ψ b))
      (by rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at ht
    exact ht
  · exfalso
    have h1 := one_lt_placeVal_inr_x (K := K) (F := SynF K F c) Q
    have h2 := hR.1 ((rfinG c).symm (algebraMap K[X] (Rfin K (SynF K F c)) X))
    rw [← hbv, hRc] at h2
    have e : ((algebraMap K[X] (Rfin K (SynF K F c)) X : Rfin K (SynF K F c)) : SynF K F c) =
        algebraMap K[X] (SynF K F c) X := rfl
    rw [e] at h2
    exact absurd h2 (not_le.2 h1)

variable {c}

/-- The center of a `K`-point of `B_A` is the chart-`{c}` center for any `c ∈ A`. -/
theorem isCenter_plc_of_mem [DecidableEq K] {A : Finset K} (hc : c ∈ A)
    (ψ : chartRing (algebraMap K[X] F X) A →ₐ[K] K) :
    IsCenter (plc c (ψ.comp (Subalgebra.inclusion (chartRing_mono _ (Finset.singleton_subset_iff.2 hc))))) ψ :=
  isCenter_extend (Finset.singleton_subset_iff.2 hc) (Finset.mem_singleton_self c) ψ (isCenter_plc c _)

theorem eq_plc_of_isCenter_of_mem [DecidableEq K] {A : Finset K} (hc : c ∈ A)
    {ψ : chartRing (algebraMap K[X] F X) A →ₐ[K] K} {R : Place K F} (hR : IsCenter R ψ) :
    R = plc c (ψ.comp (Subalgebra.inclusion (chartRing_mono _ (Finset.singleton_subset_iff.2 hc)))) :=
  eq_plc_of_isCenter c (isCenter_restrict (Finset.singleton_subset_iff.2 hc) ψ hR)

theorem isCenter_unique [DecidableEq K] {A : Finset K} (hc : c ∈ A)
    {ψ : chartRing (algebraMap K[X] F X) A →ₐ[K] K} {R R' : Place K F} (hR : IsCenter R ψ)
    (hR' : IsCenter R' ψ) : R = R' :=
  (eq_plc_of_isCenter_of_mem hc hR).trans (eq_plc_of_isCenter_of_mem hc hR').symm

end Center

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_Dict =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Dict` (dictionary D3 along `σ : F ≃ₐ[K] F'`)

For two function-field structures related by `σ : F ≃ₐ[K] F'` (e.g. `synEquiv K F c`):
* `divMap σ : Divisor K F ≃+ Divisor K F'` (along `placeEquiv σ`), `divMap_div`, `divMap_nonneg`,
  `deg_divMap` (`K` algebraically closed);
* `mem_LFK_divMap`, `LFK_divMap`, **`ellFK_divMap`**, **`genusFK_eq`**;
* `picMap σ : PicK K F ≃+ PicK K F'` with `picMap_clsK`, `degPicK_picMap`, `mem_Pic0K_picMap`, `pic0Map`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Divisor)
open RamanujanPetersson.RR

section Dict

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]
variable {F' : Type*} [Field F'] [Algebra K F'] [Algebra K[X] F'] [Algebra (RatFunc K) F']
  [IsScalarTower K[X] (RatFunc K) F'] [IsScalarTower K K[X] F'] [FunctionField K F']
  [Algebra.IsSeparable (RatFunc K) F']
variable (σ : F ≃ₐ[K] F')

/-- Transport of divisors along `σ`. -/
noncomputable def divMap : Divisor K F ≃+ Divisor K F' := Finsupp.domCongr (placeEquiv σ)

theorem divMap_apply (D : Divisor K F) (P' : Place K F') :
    divMap σ D P' = D ((placeEquiv σ).symm P') := rfl

theorem divMap_single (P : Place K F) (n : ℤ) :
    divMap σ (Finsupp.single P n) = Finsupp.single (placeEquiv σ P) n :=
  Finsupp.equivMapDomain_single _ _ _

theorem divMap_div (f : F) : divMap σ (PlacesK.div f) = PlacesK.div (σ f) := by
  ext P'
  rw [divMap_apply, PlacesK.div_apply, PlacesK.div_apply, ord_placeEquiv_symm]

theorem divMap_nonneg (E : Divisor K F) : 0 ≤ divMap σ E ↔ 0 ≤ E := by
  rw [Finsupp.le_def, Finsupp.le_def]
  constructor
  · intro h P
    simpa only [divMap_apply, Equiv.symm_apply_apply, Finsupp.coe_zero, Pi.zero_apply] using h (placeEquiv σ P)
  · intro h P'
    simpa only [divMap_apply, Finsupp.coe_zero, Pi.zero_apply] using h ((placeEquiv σ).symm P')

theorem mem_LFK_divMap (D : Divisor K F) (f : F) :
    σ f ∈ LFK K F' (divMap σ D) ↔ f ∈ LFK K F D := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp only [map_zero, Submodule.zero_mem]
  · rw [mem_LFK hf, mem_LFK ((map_ne_zero σ).2 hf), ← divMap_div, ← map_add, divMap_nonneg]

theorem LFK_divMap (D : Divisor K F) :
    LFK K F' (divMap σ D) = (LFK K F D).map (σ.toLinearEquiv : F →ₗ[K] F') := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · intro hy
    refine ⟨σ.symm y, ?_, by simp⟩
    rw [← mem_LFK_divMap σ, AlgEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨f, hf, rfl⟩
    exact (mem_LFK_divMap σ D f).2 hf

/-- `ℓ` is invariant under the transport. -/
theorem ellFK_divMap (D : Divisor K F) : ellFK K F' (divMap σ D) = ellFK K F D := by
  show Module.finrank K (LFK K F' (divMap σ D)) = Module.finrank K (LFK K F D)
  rw [LFK_divMap]
  exact LinearEquiv.finrank_map_eq σ.toLinearEquiv _

theorem deg_divMap [IsAlgClosed K] (D : Divisor K F) :
    Places.Divisor.deg (divMap σ D) = Places.Divisor.deg D := by
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero]; simp [Places.Divisor.deg]
  | add D E hD hE => rw [map_add, PlacesK.Divisor.deg_add, PlacesK.Divisor.deg_add, hD, hE]
  | single P n => rw [divMap_single, deg_single', deg_single']

include σ in
/-- **The genus is invariant under the transport.** -/
theorem genusFK_eq [IsAlgClosed K] : genusFK K F' = genusFK K F := by
  have hne : poleBK K F ≠ 0 := by
    intro h
    have h1 := degD_poleBK_pos (K := K) (F := F)
    rw [h] at h1
    simp [Places.Divisor.deg] at h1
  obtain ⟨P, -⟩ := Finsupp.ne_iff.1 hne
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 * ((genusFK K F : ℤ) + genusFK K F') + 1 := ⟨_, rfl⟩
  have hdeg : Places.Divisor.deg (Finsupp.single P n : Divisor K F) = n := deg_single' P n
  have hdeg' : Places.Divisor.deg (divMap σ (Finsupp.single P n)) = n := by rw [deg_divMap, hdeg]
  have h0 : ellFK K F' 0 = ellFK K F 0 := by simpa using ellFK_divMap σ 0
  have e1 := ellFK_eq_of_large_deg (K := K) (F := F) (D := Finsupp.single P n) (by rw [hdeg]; omega)
  have e2 := ellFK_eq_of_large_deg (K := K) (F := F') (D := divMap σ (Finsupp.single P n))
    (by rw [hdeg']; omega)
  rw [ellFK_divMap, hdeg', h0] at e2
  rw [hdeg] at e1
  omega

theorem map_PrincK :
    (PrincK K F).map (divMap σ : Divisor K F →+ Divisor K F') = PrincK K F' := by
  ext D'
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨D, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨σ f, (map_ne_zero σ).2 hf, (divMap_div σ f).symm⟩
  · rintro ⟨f', hf', rfl⟩
    refine ⟨PlacesK.div (σ.symm f'), div_mem_PrincK K F ((map_ne_zero σ.symm).2 hf'), ?_⟩
    show divMap σ (PlacesK.div (σ.symm f')) = _
    rw [divMap_div, AlgEquiv.apply_symm_apply]

/-- Transport of divisor classes. -/
noncomputable def picMap : PicK K F ≃+ PicK K F' :=
  QuotientAddGroup.congr (PrincK K F) (PrincK K F') (divMap σ) (map_PrincK σ)

theorem picMap_clsK (D : Divisor K F) : picMap σ (clsK K F D) = clsK K F' (divMap σ D) := rfl

end Dict

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJConv =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJConv`: moving points from the chart synonym back to `F`

`F' = SynF K F c0` has coordinate `x' = 1/(x - c0)`. Every `w ∈ Rfin K F` has `x'^n w ∈ Rfin K F'`
(`exists_uc_pow_mul_chartRing`), so a `K`-point `e'` of `Rfin K F'` with `e'(x') ≠ 0` gives the `K`-point
`tpH e' : w ↦ e'(x'^n w)/e'(x')^n` of `Rfin K F` (`tp_eq`: independent of `n`), with the same place
(`synPlace_tpH`). `convSym`: a map `Sym^n(Rfin F') → R` with `N(x')` a unit becomes `Sym^n(Rfin F) → R`
(`liftPts`), with `divMap_Zdiv_convSym` for the divisors of its points.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym

universe u

section AJConv

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (K F) in
/-- `K[x] ⊆ F` as a `K`-subalgebra. -/
noncomputable abbrev polyX : Subalgebra K F := Algebra.adjoin K {algebraMap K[X] F X}

/-- `K[X] → K[x]`. -/
noncomputable def xPoly : K[X] →ₐ[K] polyX K F :=
  aeval (⟨algebraMap K[X] F X, Algebra.self_mem_adjoin_singleton K _⟩ : polyX K F)

theorem xPoly_coe (p : K[X]) : ((xPoly p : polyX K F) : F) = algebraMap K[X] F p := by
  rw [algebraMap_eq_aeval]
  exact (Polynomial.aeval_algHom_apply (polyX K F).val _ p).symm

theorem xPoly_surjective : Function.Surjective (xPoly (K := K) (F := F)) := by
  rintro ⟨y, hy⟩
  have hy' : y ∈ Algebra.adjoin K {algebraMap K[X] F X} := hy
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
  obtain ⟨p, rfl⟩ := hy'
  exact ⟨p, Subtype.ext (by rw [xPoly_coe, algebraMap_eq_aeval]; rfl)⟩

theorem algebraMap_polyX_comp :
    (algebraMap (polyX K F) F).comp (xPoly (K := K) (F := F)).toRingHom = algebraMap K[X] F :=
  RingHom.ext fun p => xPoly_coe p

theorem isIntegral_polyX_iff (y : F) : IsIntegral K[X] y ↔ IsIntegral (polyX K F) y := by
  constructor
  · intro h
    exact h.map_of_comp_eq (xPoly (K := K) (F := F)).toRingHom (RingHom.id F)
      (by rw [algebraMap_polyX_comp]; rfl)
  · rintro ⟨p, hp, hpy⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective (f := (xPoly (K := K) (F := F)).toRingHom) xPoly_surjective p) hp
    refine ⟨q, hqm, ?_⟩
    rw [← algebraMap_polyX_comp, ← eval₂_map, hq, hpy]

variable (c0 : K)

theorem uc_mul_x : uc (algebraMap K[X] F X) c0 * algebraMap K[X] F X =
    1 + algebraMap K F c0 * uc (algebraMap K[X] F X) c0 := by
  have h := sub_mul_uc (transcendental_xF K F) c0 0
  simp only [map_zero, sub_zero] at h
  rw [mul_comm]
  exact h

theorem uc_mul_sub : uc (algebraMap K[X] F X) c0 * (algebraMap K[X] F X - algebraMap K F c0) = 1 :=
  inv_mul_cancel₀ (sub_ne_zero_of_tr (transcendental_xF K F) c0)

theorem exists_uc_pow_mul_polyA {y : F} (hy : y ∈ polyX K F) :
    ∃ n : ℕ, uc (algebraMap K[X] F X) c0 ^ n * y ∈ polyA (algebraMap K[X] F X) {c0} := by
  have hw := uc_mem_polyA (algebraMap K[X] F X) (Finset.mem_singleton_self c0)
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    refine ⟨1, ?_⟩
    rw [pow_one, uc_mul_x]
    exact Subalgebra.add_mem _ (Subalgebra.one_mem _) (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c0) hw)
  | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [mul_add]
    exact Subalgebra.add_mem _ (pow_mul_mem_of_le hw (Nat.le_add_right m n) hm)
      (pow_mul_mem_of_le hw (Nat.le_add_left n m) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [pow_add, mul_mul_mul_comm]
    exact Subalgebra.mul_mem _ hm hn

theorem exists_sub_pow_mul_polyX {y : F} (hy : y ∈ polyA (algebraMap K[X] F X) {c0}) :
    ∃ n : ℕ, (algebraMap K[X] F X - algebraMap K F c0) ^ n * y ∈ polyX K F := by
  have hw : algebraMap K[X] F X - algebraMap K F c0 ∈ polyX K F :=
    Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton K _) (Subalgebra.algebraMap_mem _ c0)
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    have hc' : c = c0 := Finset.mem_singleton.1 (Finset.mem_coe.1 hc)
    subst hc'
    exact ⟨1, by rw [pow_one, mul_comm, uc_mul_sub]; exact Subalgebra.one_mem _⟩
  | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [mul_add]
    exact Subalgebra.add_mem _ (pow_mul_mem_of_le hw (Nat.le_add_right m n) hm)
      (pow_mul_mem_of_le hw (Nat.le_add_left n m) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [pow_add, mul_mul_mul_comm]
    exact Subalgebra.mul_mem _ hm hn

/-- **`Rfin K F ⊆ B_{c0}[1/x']`.** -/
theorem exists_uc_pow_mul_chartRing (w : Rfin K F) :
    ∃ n : ℕ, uc (algebraMap K[X] F X) c0 ^ n * (w : F) ∈ chartRing (algebraMap K[X] F X) {c0} :=
  exists_pow_mul_isIntegral (uc_mem_polyA _ (Finset.mem_singleton_self c0))
    (fun _ hy => exists_uc_pow_mul_polyA c0 hy) ((isIntegral_polyX_iff _).1 w.2)

/-- **`B_{c0} ⊆ Rfin K F [1/(x - c0)]`.** -/
theorem exists_sub_pow_mul_rfin {b : F} (hb : b ∈ chartRing (algebraMap K[X] F X) {c0}) :
    ∃ n : ℕ, ∃ w : Rfin K F, (w : F) = (algebraMap K[X] F X - algebraMap K F c0) ^ n * b := by
  have hw : algebraMap K[X] F X - algebraMap K F c0 ∈ polyX K F :=
    Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton K _) (Subalgebra.algebraMap_mem _ c0)
  obtain ⟨n, hn⟩ := exists_pow_mul_isIntegral hw (fun _ hy => exists_sub_pow_mul_polyX c0 hy) hb
  exact ⟨n, ⟨_, (isIntegral_polyX_iff _).2 hn⟩, rfl⟩

variable (K F) in
/-- The coordinate `x'` of the chart synonym, as an element of its ring of `x'`-integers. -/
noncomputable abbrev xS : Rfin K (SynF K F c0) := algebraMap K[X] (Rfin K (SynF K F c0)) X

theorem coe_xS : ((xS K F c0 : Rfin K (SynF K F c0)) : SynF K F c0) =
    synEquiv K F c0 (uc (algebraMap K[X] F X) c0) :=
  synAlg_X K F c0

/-- The exponent `n` with `x'^n w ∈ Rfin K F'`. -/
noncomputable def convN (w : Rfin K F) : ℕ := (exists_uc_pow_mul_chartRing c0 w).choose

/-- `x'^n w` as an element of `Rfin K F'`. -/
noncomputable def convW (w : Rfin K F) : Rfin K (SynF K F c0) :=
  rfinG c0 ⟨_, (exists_uc_pow_mul_chartRing c0 w).choose_spec⟩

theorem coe_convW (w : Rfin K F) : ((convW c0 w : Rfin K (SynF K F c0)) : SynF K F c0) =
    synEquiv K F c0 (uc (algebraMap K[X] F X) c0 ^ convN c0 w * (w : F)) := rfl

/-- The transported value `e'(x'^n w) / e'(x')^n`. -/
noncomputable def tpFun (e' : Rfin K (SynF K F c0) →ₐ[K] K) (w : Rfin K F) : K :=
  e' (convW c0 w) / e' (xS K F c0) ^ convN c0 w

variable (e' : Rfin K (SynF K F c0) →ₐ[K] K) (hx : e' (xS K F c0) ≠ 0)

include hx in
/-- **Independence of the exponent.** -/
theorem tp_eq (w : Rfin K F) (n : ℕ) (b : Rfin K (SynF K F c0))
    (hb : (b : SynF K F c0) = synEquiv K F c0 (uc (algebraMap K[X] F X) c0 ^ n * (w : F))) :
    tpFun c0 e' w = e' b / e' (xS K F c0) ^ n := by
  have key : convW c0 w * xS K F c0 ^ n = b * xS K F c0 ^ convN c0 w := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_xS, coe_convW, hb]
    simp only [← map_pow, ← map_mul]
    congr 1
    ring
  have h := congrArg e' key
  rw [map_mul, map_mul, map_pow, map_pow] at h
  rw [tpFun, div_eq_div_iff (pow_ne_zero _ hx) (pow_ne_zero _ hx)]
  exact h

include hx in
theorem tpFun_one : tpFun c0 e' 1 = 1 := by
  rw [tp_eq c0 e' hx 1 0 1 (by simp), map_one, pow_zero, div_one]

include hx in
theorem tpFun_zero : tpFun c0 e' 0 = 0 := by
  rw [tp_eq c0 e' hx 0 0 0 (by simp), map_zero, zero_div]

include hx in
theorem tpFun_mul (w1 w2 : Rfin K F) : tpFun c0 e' (w1 * w2) = tpFun c0 e' w1 * tpFun c0 e' w2 := by
  rw [tp_eq c0 e' hx (w1 * w2) (convN c0 w1 + convN c0 w2) (convW c0 w1 * convW c0 w2)
    (by simp only [MulMemClass.coe_mul, coe_convW, ← map_mul]; congr 1; ring), map_mul, pow_add,
    mul_div_mul_comm]
  rfl

include hx in
theorem tpFun_add (w1 w2 : Rfin K F) : tpFun c0 e' (w1 + w2) = tpFun c0 e' w1 + tpFun c0 e' w2 := by
  rw [tp_eq c0 e' hx (w1 + w2) (convN c0 w1 + convN c0 w2)
    (convW c0 w1 * xS K F c0 ^ convN c0 w2 + convW c0 w2 * xS K F c0 ^ convN c0 w1)
    (by simp only [AddMemClass.coe_add, MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_xS, coe_convW]
        simp only [← map_pow, ← map_mul, ← map_add]; congr 1; ring)]
  simp only [tpFun]
  rw [map_add, map_mul, map_mul, map_pow, map_pow, div_add_div _ _ (pow_ne_zero _ hx) (pow_ne_zero _ hx), pow_add]
  ring

include hx in
theorem tpFun_algebraMap (r : K) : tpFun c0 e' (algebraMap K (Rfin K F) r) = algebraMap K K r := by
  rw [tp_eq c0 e' hx _ 0 (algebraMap K (Rfin K (SynF K F c0)) r) (by rw [pow_zero, one_mul]; rfl),
    AlgHom.commutes, pow_zero, div_one]

/-- **The transported `K`-point** of `Rfin K F`. -/
noncomputable def tpH : Rfin K F →ₐ[K] K where
  toFun := tpFun c0 e'
  map_one' := tpFun_one c0 e' hx
  map_mul' := tpFun_mul c0 e' hx
  map_zero' := tpFun_zero c0 e' hx
  map_add' := tpFun_add c0 e' hx
  commutes' := tpFun_algebraMap c0 e' hx

theorem tpH_apply (w : Rfin K F) : tpH c0 e' hx w = tpFun c0 e' w := rfl

theorem tpH_sub : tpH c0 e' hx (algebraMap K[X] (Rfin K F) (X - C c0)) = (e' (xS K F c0))⁻¹ := by
  rw [tpH_apply, tp_eq c0 e' hx _ 1 1 ?_, map_one, pow_one, one_div]
  rw [pow_one, OneMemClass.coe_one]
  show (1 : F) = uc (algebraMap K[X] F X) c0 * algebraMap K[X] F (X - C c0)
  rw [map_sub, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, uc_mul_sub]

variable [IsAlgClosed K]

theorem placeVal_ptP_eq_one (φ : Rfin K F →ₐ[K] K) {w : Rfin K F} (hw : φ w ≠ 0) :
    placeVal (Sum.inl (ptP φ) : Place K F) (algebraMap (Rfin K F) F w) = 1 := by
  rw [placeVal_inl]
  refine le_antisymm (HeightOneSpectrum.valuation_le_one (K := F) _ _) (not_lt.1 fun h => hw ?_)
  exact mem_ptP.1 ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) _ _).1 h)

theorem sub_eq_algebraMap : algebraMap K[X] F X - algebraMap K F c0 =
    algebraMap (Rfin K F) F (algebraMap K[X] (Rfin K F) (X - C c0)) := by
  show _ = algebraMap K[X] F (X - C c0)
  rw [map_sub, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

theorem placeVal_uc_eq_one (φ : Rfin K F →ₐ[K] K) (hφ : φ (algebraMap K[X] (Rfin K F) (X - C c0)) ≠ 0) :
    placeVal (Sum.inl (ptP φ) : Place K F) (uc (algebraMap K[X] F X) c0) = 1 := by
  rw [uc, map_inv₀, sub_eq_algebraMap, placeVal_ptP_eq_one φ hφ, inv_one]

theorem not_inr_of_uc (R : Place K F) (hR : placeVal R (uc (algebraMap K[X] F X) c0) = 1)
    (Q : HeightOneSpectrum (Rinf K (SynF K F c0))) : synPlace c0 R ≠ Sum.inr Q := fun hRc => by
  have h1 := one_lt_placeVal_inr_x (K := K) (F := SynF K F c0) Q
  rw [← hRc, synAlg_X, placeVal_synPlace, hR] at h1
  exact lt_irrefl _ h1

/-- **Place dictionary**: `tpH e'` has the place of `e'`. -/
theorem synPlace_tpH : synPlace c0 (Sum.inl (ptP (tpH c0 e' hx))) = Sum.inl (ptP e') := by
  have hφ : tpH c0 e' hx (algebraMap K[X] (Rfin K F) (X - C c0)) ≠ 0 := by
    rw [tpH_sub]; exact inv_ne_zero hx
  have hv1 := placeVal_uc_eq_one c0 _ hφ
  have hv2 : placeVal (Sum.inl (ptP (tpH c0 e' hx)) : Place K F) (algebraMap K[X] F X - algebraMap K F c0) = 1 := by
    rw [sub_eq_algebraMap, placeVal_ptP_eq_one _ hφ]
  rcases hRc : synPlace c0 (Sum.inl (ptP (tpH c0 e' hx))) with P | Q
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    suffices hφe : φ = e' by rw [hφe]
    have h1 : ∀ b, e' b = 0 → φ b = 0 := fun b hb0 => by
      set y : chartRing (algebraMap K[X] F X) {c0} := (rfinG c0).symm b with hy
      have eb : (b : SynF K F c0) = synEquiv K F c0 (y : F) := by
        rw [hy, ← rfinG_coe, AlgEquiv.apply_symm_apply]
      obtain ⟨n, w, hw⟩ := exists_sub_pow_mul_rfin c0 y.2
      have htw : tpH c0 e' hx w = 0 := by
        rw [tpH_apply, tp_eq c0 e' hx w n b ?_, hb0, zero_div]
        rw [eb, hw, ← mul_assoc, ← mul_pow, uc_mul_sub, one_pow, one_mul]
      have hlt : placeVal (Sum.inl (ptP (tpH c0 e' hx)) : Place K F) (algebraMap (Rfin K F) F w) < 1 := by
        rw [placeVal_inl]
        exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) _ _).2 (mem_ptP.2 htw)
      have heq : placeVal (Sum.inl (ptP (tpH c0 e' hx)) : Place K F) (algebraMap (Rfin K F) F w) =
          placeVal (Sum.inl (ptP (tpH c0 e' hx)) : Place K F) (y : F) := by
        show placeVal _ (w : F) = _
        rw [hw, map_mul, map_pow, hv2, one_pow, one_mul]
      have h2 := placeVal_synPlace c0 (Sum.inl (ptP (tpH c0 e' hx)) : Place K F) (y : F)
      rw [hRc, ← heq, ← eb, placeVal_inl] at h2
      exact mem_ptP.1 ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := SynF K F c0) (ptP φ) b).1 (h2 ▸ hlt))
    refine AlgHom.ext fun b => ?_
    have ht := h1 (b - algebraMap K _ (e' b))
      (by rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at ht
    exact ht
  · exact absurd hRc (not_inr_of_uc c0 _ hv1 Q)

omit hx in
theorem eq_of_tpH_eq {e1 e2 : Rfin K (SynF K F c0) →ₐ[K] K} {h1 : e1 (xS K F c0) ≠ 0} {h2 : e2 (xS K F c0) ≠ 0}
    (h : tpH c0 e1 h1 = tpH c0 e2 h2) : e1 = e2 := by
  have h3 := synPlace_tpH c0 e1 h1
  rw [h, synPlace_tpH] at h3
  exact ptP_injective (Sum.inl_injective h3).symm

open Classical in
theorem Zdiv_apply_eq {G : Type u} [Field G] [Algebra K G] [Algebra K[X] G] [Algebra (RatFunc K) G]
    [IsScalarTower K[X] (RatFunc K) G] [IsScalarTower K K[X] G] [FunctionField K G]
    [Algebra.IsSeparable (RatFunc K) G] (S : Finset (Rfin K G →ₐ[K] K)) (P : Place K G) :
    Zdiv S P = if ∃ φ ∈ S, P = Sum.inl (ptP φ) then 1 else 0 := by
  rcases P with P | Q
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    rw [Zdiv_inl_ptP]
    refine if_congr ⟨fun h => ⟨φ, h, rfl⟩, fun ⟨φ2, h2, he⟩ => ?_⟩ rfl rfl
    rwa [ptP_injective (Sum.inl_injective he)]
  · rw [Zdiv_inr, if_neg]
    rintro ⟨φ, -, h⟩
    exact Sum.inl_ne_inr h.symm

open Classical in
/-- **Transport of reduced divisors** under a matching of points with equal places. -/
theorem divMap_Zdiv (S : Finset (Rfin K F →ₐ[K] K)) (S' : Finset (Rfin K (SynF K F c0) →ₐ[K] K))
    (h1 : ∀ φ ∈ S, ∃ e' ∈ S', synPlace c0 (Sum.inl (ptP φ)) = Sum.inl (ptP e'))
    (h2 : ∀ e' ∈ S', ∃ φ ∈ S, synPlace c0 (Sum.inl (ptP φ)) = Sum.inl (ptP e')) :
    divMap (synEquiv K F c0) (Zdiv S) = Zdiv S' := by
  ext P'
  rw [divMap_apply, Zdiv_apply_eq, Zdiv_apply_eq]
  have hs : placeEquiv (synEquiv K F c0) = synPlace c0 := rfl
  rw [hs]
  refine if_congr ⟨fun ⟨φ, hφ, hR⟩ => ?_, fun ⟨e', he', hP⟩ => ?_⟩ rfl rfl
  · obtain ⟨e', he', he⟩ := h1 φ hφ
    refine ⟨e', he', ?_⟩
    rw [← he, ← hR, Equiv.apply_symm_apply]
  · obtain ⟨φ, hφ, he⟩ := h2 e' he'
    exact ⟨φ, hφ, by rw [hP, ← he, Equiv.symm_apply_apply]⟩

section ConvSym

variable {R : Type*} [CommRing R] [Algebra K R] {n n' : ℕ}
variable (φ' : SymRing K (Rfin K (SynF K F c0)) n' →ₐ[K] R) (hu : IsUnit (φ' (normS K (xS K F c0))))

omit hx in
include hu in
theorem tuple_ne_zero (y : R →ₐ[K] K) (l : Fin n') : liftTuple (y.comp φ') l (xS K F c0) ≠ 0 := by
  have h := hu.map y
  have e := symPt_normS (liftTuple (y.comp φ')) (xS K F c0)
  rw [symPt_liftTuple, AlgHom.comp_apply] at e
  rw [e] at h
  exact Finset.prod_ne_zero_iff.1 h.ne_zero l (Finset.mem_univ l)

/-- The transported tuple of points. -/
noncomputable def convPt (hn : n = n') (y : R →ₐ[K] K) : Fin n → (Rfin K F →ₐ[K] K) :=
  fun i => tpH c0 (liftTuple (y.comp φ') (Fin.cast hn i)) (tuple_ne_zero c0 φ' hu y _)

omit hx in
theorem convPt_normS (hn : n = n') (w : Rfin K F) :
    ∃ r : R, ∀ y : R →ₐ[K] K, y r = symPt (convPt c0 φ' hu hn y) (normS K w) := by
  subst hn
  refine ⟨φ' (normS K (convW c0 w)) * ↑(hu.unit⁻¹) ^ convN c0 w, fun y => ?_⟩
  have e1 : ∀ b : Rfin K (SynF K F c0), y (φ' (normS K b)) = ∏ l, liftTuple (y.comp φ') l b := fun b => by
    have h := symPt_normS (liftTuple (y.comp φ')) b
    rwa [symPt_liftTuple, AlgHom.comp_apply] at h
  have hinv : y ↑(hu.unit⁻¹) = (y (φ' (normS K (xS K F c0))))⁻¹ := by
    have h0 := congrArg y hu.mul_val_inv
    rw [map_mul, map_one] at h0
    exact eq_inv_of_mul_eq_one_right h0
  rw [map_mul, map_pow, hinv, e1, e1, symPt_normS]
  simp only [convPt, tpH_apply, tpFun, Fin.cast_eq_self]
  rw [Finset.prod_div_distrib, Finset.prod_pow, div_eq_mul_inv, inv_pow]

/-- **Conversion `Sym^n(Rfin F') → R` to `Sym^n(Rfin F) → R`** (when `N(x')` is a unit). -/
noncomputable def convSym [IsReduced R] [Algebra.FiniteType K R] (hn : n = n') :
    SymRing K (Rfin K F) n →ₐ[K] R :=
  liftPts (fun y => symPt (convPt c0 φ' hu hn y)) (convPt_normS c0 φ' hu hn)

omit hx in
theorem comp_convSym [IsReduced R] [Algebra.FiniteType K R] (hn : n = n') (y : R →ₐ[K] K) :
    y.comp (convSym c0 φ' hu hn) = symPt (convPt c0 φ' hu hn y) :=
  comp_liftPts _ _ y

omit hx in
open Classical in
/-- **The divisor of a converted point** is the transported divisor. -/
theorem divMap_Zdiv_convSym [IsReduced R] [Algebra.FiniteType K R] (hn : n = n') (y : R →ₐ[K] K) :
    divMap (synEquiv K F c0) (Zdiv (ptSet (y.comp (convSym c0 φ' hu hn)))) = Zdiv (ptSet (y.comp φ')) := by
  rw [comp_convSym, ptSet_symPt]
  apply divMap_Zdiv c0
  · intro φ hφ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hφ
    exact ⟨_, (mem_ptSet _ _).2 ⟨_, rfl⟩, synPlace_tpH c0 _ _⟩
  · intro e' he'
    obtain ⟨l, rfl⟩ := (mem_ptSet _ _).1 he'
    subst hn
    refine ⟨convPt c0 φ' hu rfl y l, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    exact synPlace_tpH c0 _ _

end ConvSym

end AJConv

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJPiece =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`

In `F' = SynF K F c0` (coordinate `x' = 1/(x - c0)`), the `ν`-piece `pieceMap D c : Sym^g(B') → B'[1/f]` of
`AJLoc` is localized at `N(x')` (`ConvR`), converted to `F`-coordinates by `convSym` (`convS`), and localized at
the image of `u0` (`LocR`). This gives **`lawMapP : LawRing K F → LocR`**, i.e. `Spec LocR → X0`, on the open
`Spec LocR ⊆ Spec B'` (`pieceIn`), with the class formula **`psiJ_lawMapP`**: `ψ(piece(Q)) = κ - [Θ] - [Q]`.
`exists_pieceIn`: a point `Q` of `B'` lies on the piece when `f`, `N(x')` and `u0` do not vanish there.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section AwayPt

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A `K`-point not killing `ω` extends to `A[1/ω]`. -/
theorem exists_away_pt {A : Type u} [CommRing A] [Algebra K A] (Q : A →ₐ[K] K) (ω : A) (h : Q ω ≠ 0) :
    ∃ x : Localization.Away ω →ₐ[K] K, x.comp (awayι (K := K) ω) = Q :=
  ⟨liftPt (B := K) Q ω fun y => by rw [show y (Q ω) = Q ω from y.commutes (Q ω)]; exact h,
    liftPt_comp (B := K) Q ω _⟩

end AwayPt

section AJPiece

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

omit [IsAlgClosed K] in
theorem clsK_single_syn (P' : Place K (SynF K F c0)) :
    (picMap (synEquiv K F c0)).symm (clsK K (SynF K F c0) (Finsupp.single P' 1)) =
      clsK K F (Finsupp.single ((synPlace c0).symm P') 1) := by
  rw [AddEquiv.symm_apply_eq, picMap_clsK, divMap_single]
  show clsK K (SynF K F c0) (Finsupp.single P' 1) =
    clsK K (SynF K F c0) (Finsupp.single (synPlace c0 ((synPlace c0).symm P')) 1)
  rw [Equiv.apply_symm_apply]

end AJPiece

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJVal =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJVal`: the Abel-Jacobi map on a piece and its values

* `specO K R`, `kptO x` (the `K`-point of `Spec R` at `x : R →ₐ[K] K`), `SpecMap_closedPoint`.
* `jMap φ : Spec R ⟶ J` (`Spec φ ≫ jX0`); its `K`-points have value `ψ(x ∘ φ)` (`jacPicEquiv_jMap`).
* `ajCls P0 Q = [Q] - [P0] ∈ Pic⁰`, `ajK P0 Q = jacPicEquiv⁻¹ (ajCls P0 Q)`, `ajPt P0 Q` (its point of `J`).
* **`ajMap P0 φ κ = const (κ - [Θ] - [P0]) * (jMap φ)⁻¹`** (group law on `Spec R ⟶ J`), with value
  `ajK P0 Q` at every `K`-point `x` with `ψ(x ∘ φ) = κ - [Θ] - [Q]` (`kptO_ajMap`, `ajMap_kpt`).
* **`ajPiece P0 c0 D c := ajMap P0 (lawMapP c0 D c) (kapP c0 D c)`** on the piece `Spec LocR`: value `ajPt P0 Q`
  (value lemmas for the piece: next file; see NOTES session 19).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section SpecPt

variable {K : Type u} [Field K]

theorem SpecMap_sR {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) :
    Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ sR K A = sR K B := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]

variable (K) in
/-- `Spec R` as an object over `Spec K`. -/
noncomputable abbrev specO (R : Type u) [CommRing R] [Algebra K R] : Over (Spec (.of K)) := Over.mk (sR K R)

/-- The `K`-point of `Spec R` at `x : R →ₐ[K] K`. -/
noncomputable def kptO {R : Type u} [CommRing R] [Algebra K R] (x : R →ₐ[K] K) :
    𝟙_ (Over (Spec (.of K))) ⟶ specO K R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (x : R →+* K))) (by
    refine (SpecMap_sR x).trans ?_
    show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id])

theorem SpecMap_closedPoint {A : Type u} [CommRing A] [Algebra K A] (x : A →ₐ[K] K) :
    Spec.map (CommRingCat.ofHom (x : A →+* K)) (IsLocalRing.closedPoint K) = kpt x :=
  PrimeSpectrum.ext (R := A) (Ideal.ext fun a => by
    rw [kpt_asIdeal, RingHom.mem_ker]
    change (x : A →+* K) a ∈ IsLocalRing.maximalIdeal K ↔ _
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
    rfl)

end SpecPt

section JMap

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

end JMap

section Piece

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

end Piece

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJVal2 =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`

* `plC c0 Q` (the place of `F` at a `K`-point `Q` of `B'`), `plP c0 D c x`, `psiJ_plP`.
* **`kptO_ajPiece`**, **`ajPiece_kpt`**: the piece takes the value `ajPt P0 (plP c0 D c x)` (class `[Q] - [P0]`).
* `isOpenImmersion_pieceIn`: `Spec LocR → Spec B'` is an open immersion; `pieceIn_over`.
* **`ajChart P0 c0 : Spec B' ⟶ J`** glued (`JacChunk.glueY`) from the pieces; `ajChart_over`,
  **`ajChart_kpt`**: value `ajPt P0 (plC c0 Q)` at every closed point `kpt Q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- the instance diamonds on the nested localizations need nested synthPending (diagnostics, session 20)
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section PlP

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K)

/-- The place of `F` at a `K`-point of the chart ring `B' = Rfin (SynF K F c0)`. -/
noncomputable def plC (Q : Rfin K (SynF K F c0) →ₐ[K] K) : Place K F :=
  (synPlace c0).symm (Sum.inl (ptP Q))

variable {r : ℕ} (D : NuData K (SynF K F c0) (1 + r)) (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

end PlP

section PieceVal

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

end PieceVal

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJGreedy =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGreedy`: generic points off a hypersurface of `Sym^n`

* `exists_update_elt`: moving one entry of a tuple, `Q ↦ symPt (update t j Q) u` is a function on `B`.
* **`exists_greedy`**: if `u` does not vanish at some point of `Sym^n`, and good finite sets of candidates
  (`τ : Y ↪ Spec_max B`) can always be extended off any finite set, there is a good injective `n`-tuple `a`
  of candidates with `u(τ ∘ a) ≠ 0` (one point at a time).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacSym RamanujanPetersson.JacLaw

section Greedy

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B] [IsReduced B]
  [Algebra.FiniteType k B]

theorem map_univ_succAbove {α : Type*} {r : ℕ} (f : Fin (r + 1) → α) (j : Fin (r + 1)) :
    (Finset.univ.val.map f : Multiset α) = f j ::ₘ Finset.univ.val.map (f ∘ j.succAbove) := by
  rw [Fin.univ_succAbove r j]
  simp
  exact List.Perm.refl _

theorem symPt_update_eq {r : ℕ} (t : Fin (r + 1) → (B →ₐ[k] k)) (j : Fin (r + 1)) (Q : B →ₐ[k] k) :
    symPt (fun i => Fin.append (fun _ : Fin 1 => Q) (t ∘ j.succAbove) (Fin.cast (Nat.add_comm 1 r).symm i)) =
      symPt (Function.update t j Q) := by
  apply symPt_eq_of_mset_eq
  apply Sym.coe_injective
  rw [mset_coe, mset_coe]
  conv_lhs => rw [map_univ_succAbove _ 0]
  conv_rhs => rw [map_univ_succAbove _ j]
  congr 1
  · have e : Fin.cast (Nat.add_comm 1 r).symm (0 : Fin (r + 1)) = Fin.castAdd r (0 : Fin 1) :=
      Fin.ext (by simp)
    simp only [e, Fin.append_left, Function.update_self]
  · congr 1
    funext m
    have e : Fin.cast (Nat.add_comm 1 r).symm ((0 : Fin (r + 1)).succAbove m) = Fin.natAdd 1 m :=
      Fin.ext (by simp; omega)
    simp only [Function.comp_apply, e, Fin.append_right, Function.update_of_ne (Fin.succAbove_ne j m)]

/-- **Moving one entry**: `Q ↦ u(t[j := Q])` is a function on `B`. -/
theorem exists_update_elt {n : ℕ} (t : Fin n → (B →ₐ[k] k)) (j : Fin n) (u : SymRing k B n) :
    ∃ w : B, ∀ Q : B →ₐ[k] k, Q w = symPt (Function.update t j Q) u := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by have := j.isLt; omega⟩
  refine ⟨padMap (phi1 (k := k) (B := B)) (t ∘ j.succAbove) (Nat.add_comm 1 r) u, fun Q => ?_⟩
  have e := comp_padMap (phi1 (k := k) (B := B)) (t ∘ j.succAbove) (Nat.add_comm 1 r) Q
  rw [padPt, liftTuple_phi1, symPt_update_eq] at e
  exact AlgHom.congr_fun e u

/-- **Greedy choice**: a good injective tuple of candidates on which `u` does not vanish. -/
theorem exists_greedy {n : ℕ} {Y : Type*} [DecidableEq Y] (τ : Y → (B →ₐ[k] k)) (hτ : Function.Injective τ)
    (hfin : ∀ w : B, w ≠ 0 → {φ : B →ₐ[k] k | φ w = 0}.Finite)
    (Good : Finset Y → Prop) (h0 : Good ∅)
    (hext : ∀ C : Finset Y, Good C → C.card < n → ∀ Bad : Finset Y, ∃ q, q ∉ C ∧ q ∉ Bad ∧ Good (insert q C))
    (u : SymRing k B n) (t0 : Fin n → (B →ₐ[k] k)) (ht0 : symPt t0 u ≠ 0) :
    ∃ a : Fin n → Y, Function.Injective a ∧ Good (Finset.univ.image a) ∧ symPt (τ ∘ a) u ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨Fin.elim0, fun i => i.elim0, ?_, ?_⟩
    · rw [Finset.univ_eq_empty, Finset.image_empty]; exact h0
    · have e : τ ∘ (Fin.elim0 : Fin 0 → Y) = t0 := funext fun i => i.elim0
      rw [e]; exact ht0
  obtain ⟨y0, -, -, -⟩ := hext ∅ h0 (by rw [Finset.card_empty]; exact hn) ∅
  have key : ∀ m ≤ n, ∃ a : Fin n → Y, ∃ t : Fin n → (B →ₐ[k] k), symPt t u ≠ 0 ∧
      (∀ i : Fin n, i.val < m → t i = τ (a i)) ∧ Set.InjOn a {i | i.val < m} ∧
      Good ((Finset.univ.filter fun i : Fin n => i.val < m).image a) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun _ => y0, t0, ht0, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
      have e : (Finset.univ.filter fun i : Fin n => i.val < 0) = ∅ :=
        Finset.filter_false_of_mem fun i _ => Nat.not_lt_zero _
      rw [e, Finset.image_empty]; exact h0
    | succ m ih =>
      intro hm
      obtain ⟨a, t, ht, hat, hinj, hgood⟩ := ih (by omega)
      obtain ⟨j, hj⟩ : ∃ j : Fin n, j.val = m := ⟨⟨m, by omega⟩, rfl⟩
      obtain ⟨C, hC⟩ : ∃ C : Finset Y, C = (Finset.univ.filter fun i : Fin n => i.val < m).image a := ⟨_, rfl⟩
      have hCc : C.card < n := by
        have h1 : C.card ≤ (Finset.univ.filter fun i : Fin n => i.val < m).card := by
          rw [hC]; exact Finset.card_image_le
        have h2 : (Finset.univ.filter fun i : Fin n => i.val < m).card ≤ m := by
          calc _ ≤ (Finset.range m).card := Finset.card_le_card_of_injOn (fun i => i.val)
                (fun i hi => Finset.mem_range.2 (Finset.mem_filter.1 hi).2) (fun i _ i' _ h => Fin.ext h)
            _ = m := Finset.card_range m
        omega
      obtain ⟨w, hw⟩ := exists_update_elt t j u
      have hw0 : (t j) w ≠ 0 := by rw [hw, Function.update_eq_self]; exact ht
      have hwne : w ≠ 0 := fun h => hw0 (by rw [h, map_zero])
      obtain ⟨Bad, hBad⟩ : ∃ Bad : Finset Y, ∀ q, q ∈ Bad ↔ τ q w = 0 :=
        ⟨((hfin w hwne).preimage hτ.injOn).toFinset, fun q => by simp⟩
      obtain ⟨q, hqC, hqB, hgq⟩ := hext C (hC ▸ hgood) hCc Bad
      have hqw : τ q w ≠ 0 := fun h => hqB ((hBad q).2 h)
      have hlt : ∀ i : Fin n, i ≠ j → i.val < m + 1 → i.val < m := fun i hij hi => by
        have : i.val ≠ m := fun h => hij (Fin.ext (h.trans hj.symm))
        omega
      refine ⟨Function.update a j q, Function.update t j (τ q), ?_, ?_, ?_, ?_⟩
      · rw [← hw]; exact hqw
      · intro i hi
        by_cases hij : i = j
        · rw [hij, Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hij, Function.update_of_ne hij]
          exact hat i (hlt i hij hi)
      · intro i1 hi1 i2 hi2 h
        simp only [Set.mem_ofPred_eq] at hi1 hi2
        have hmem : ∀ i : Fin n, i ≠ j → i.val < m + 1 → a i ∈ C := fun i hij hi => by
          rw [hC]
          exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt i hij hi⟩)
        by_cases h1 : i1 = j <;> by_cases h2 : i2 = j
        · rw [h1, h2]
        · rw [h1, Function.update_self, Function.update_of_ne h2] at h
          exact absurd (h ▸ hmem i2 h2 hi2) hqC
        · rw [h2, Function.update_self, Function.update_of_ne h1] at h
          exact absurd (h.symm ▸ hmem i1 h1 hi1) hqC
        · rw [Function.update_of_ne h1, Function.update_of_ne h2] at h
          exact hinj (hlt i1 h1 hi1) (hlt i2 h2 hi2) h
      · have e : (Finset.univ.filter fun i : Fin n => i.val < m + 1).image (Function.update a j q) =
            insert q C := by
          ext y
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hC]
          constructor
          · rintro ⟨i, hi, rfl⟩
            by_cases hij : i = j
            · left; rw [hij, Function.update_self]
            · right; exact ⟨i, hlt i hij hi, (Function.update_of_ne hij _ _).symm⟩
          · rintro (rfl | ⟨i, hi, rfl⟩)
            · exact ⟨j, by omega, Function.update_self _ _ _⟩
            · have hij : i ≠ j := fun h => by rw [h] at hi; omega
              exact ⟨i, by omega, Function.update_of_ne hij _ _⟩
        rw [e]; exact hgq
  obtain ⟨a, t, ht, hat, hinj, hgood⟩ := key n le_rfl
  have e1 : (Finset.univ.filter fun i : Fin n => i.val < n) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => i.isLt
  have e2 : τ ∘ a = t := funext fun i => (hat i i.isLt).symm
  refine ⟨a, fun i1 i2 h => hinj i1.isLt i2.isLt h, ?_, ?_⟩
  · rw [e1] at hgood; exact hgood
  · rw [e2]; exact ht

end Greedy

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJGen =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`

* `exists_pool`: arbitrarily large finite sets of points off the roots of `b(x)`.
* `PtY K F c0` (points of `B' = Rfin F'` off `x = ∞`), `tpY` (their `F`-points, injective).
* `goodY_ext`: nonspecial `b`-generic sets of such points extend off any finite set.
* `symPt_convPt_eq`: the converted point depends only on the support.
* **`exists_piece_through`**: every closed point `Q0` of `B'` lies on some piece `Spec LocR c0 D c`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section AJGen

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **Large pools of points** off the roots of `b(x)`. -/
theorem exists_pool (b : K[X]) (hb : b ≠ 0) (m : ℕ) :
    ∃ T : Finset (Rfin K F →ₐ[K] K), m ≤ T.card ∧ ∀ φ ∈ T, b.eval (φ (xB K F)) ≠ 0 := by
  obtain ⟨a1, ha1, hfib⟩ := exists_fib_data (K := K) (F := F)
  have hab : a1 * b ≠ 0 := mul_ne_zero ha1 hb
  obtain ⟨Λ, hΛ, hΛc⟩ := (finite_setOfPred_isRoot hab).infinite_compl.exists_subset_card_eq m
  have hΛab : ∀ c ∈ Λ, (a1 * b).eval c ≠ 0 := fun c hc h => hΛ (Finset.mem_coe.2 hc) h
  obtain ⟨s, Z, -, -, -, -, hZx, hZc⟩ := hfib Λ fun c hc => by
    have h := hΛab c hc
    rw [eval_mul] at h
    exact left_ne_zero_of_mul h
  refine ⟨Z, ?_, fun φ hφ => ?_⟩
  · have hn : 0 < Module.finrank K[X] (Rfin K F) :=
      (Module.finrank_pos_iff_of_free (R := K[X]) (M := Rfin K F)).2 inferInstance
    rw [hZc, hΛc]
    exact Nat.le_mul_of_pos_right _ hn
  · have h := hΛab _ ((hZx φ).1 hφ)
    rw [eval_mul] at h
    exact right_ne_zero_of_mul h

variable (c0 : K)

variable (K F) in
/-- Points of `B' = Rfin F'` off `x = ∞`. -/
abbrev PtY : Type u := {e : Rfin K (SynF K F c0) →ₐ[K] K // e (xS K F c0) ≠ 0}

/-- Their `F`-points. -/
noncomputable def tpY (e : PtY K F c0) : Rfin K F →ₐ[K] K := tpH c0 e.1 e.2

theorem tpY_injective : Function.Injective (tpY (K := K) (F := F) c0) :=
  fun _ _ h => Subtype.ext (eq_of_tpH_eq c0 h)

theorem tpH_congr {e1 e2 : Rfin K (SynF K F c0) →ₐ[K] K} (h : e1 = e2) (h1 : e1 (xS K F c0) ≠ 0)
    (h2 : e2 (xS K F c0) ≠ 0) : tpH c0 e1 h1 = tpH c0 e2 h2 := by
  subst h; rfl

/-- Good sets: nonspecial and `b`-generic. -/
def GoodY (b : K[X]) (C : Finset (PtY K F c0)) : Prop :=
  ellFK K (SynF K F c0) (Zdiv (C.map (Function.Embedding.subtype _))) = 1 ∧
    ∀ e ∈ C, b.eval (e.1 (xB K (SynF K F c0))) ≠ 0

theorem goodY_empty (b : K[X]) : GoodY (K := K) (F := F) c0 b ∅ := by
  refine ⟨?_, fun e he => absurd he (Finset.notMem_empty e)⟩
  rw [Finset.map_empty, Zdiv_empty]
  exact ellFK_zero'

/-- **Extension step** for good sets (`exists_add_nonspecial` on a pool). -/
theorem goodY_ext {b : K[X]} (hb : b ≠ 0) (C : Finset (PtY K F c0)) (hC : GoodY c0 b C)
    (hCc : C.card < genusFK K F) (Bad : Finset (PtY K F c0)) :
    ∃ q, q ∉ C ∧ q ∉ Bad ∧ GoodY c0 b (insert q C) := by
  obtain ⟨hC1, hCb⟩ := hC
  have hg : genusFK K (SynF K F c0) = genusFK K F := genusFK_eq (synEquiv K F c0)
  obtain ⟨T0, hT0c, hT0⟩ := exists_pool (F := SynF K F c0) (X * b) (mul_ne_zero X_ne_zero hb)
    (2 * genusFK K (SynF K F c0) + (Bad ∪ C).card)
  let ι := Function.Embedding.subtype (fun e : Rfin K (SynF K F c0) →ₐ[K] K => e (xS K F c0) ≠ 0)
  have hdis : Disjoint (C.map ι) (T0 \ (Bad ∪ C).map ι) := by
    rw [Finset.disjoint_left]
    intro φ hφ hφT
    exact (Finset.mem_sdiff.1 hφT).2 (Finset.map_subset_map.2 Finset.subset_union_right hφ)
  have hcard : 2 * genusFK K (SynF K F c0) ≤ (T0 \ (Bad ∪ C).map ι).card := by
    have h1 := Finset.le_card_sdiff ((Bad ∪ C).map ι) T0
    rw [Finset.card_map] at h1
    omega
  obtain ⟨P, hP, hP1⟩ := exists_add_nonspecial hdis hC1 (by rw [Finset.card_map, hg]; exact hCc) (by omega)
  obtain ⟨hPT, hPB⟩ := Finset.mem_sdiff.1 hP
  have hPe := hT0 P hPT
  rw [eval_mul, eval_X] at hPe
  let q : PtY K F c0 := ⟨P, left_ne_zero_of_mul hPe⟩
  have hqP : ι q = P := rfl
  refine ⟨q, fun h => hPB (Finset.mem_map.2 ⟨q, Finset.mem_union_right _ h, rfl⟩),
    fun h => hPB (Finset.mem_map.2 ⟨q, Finset.mem_union_left _ h, rfl⟩), ?_, ?_⟩
  · show ellFK K (SynF K F c0) (Zdiv ((insert q C).map ι)) = 1
    rw [Finset.map_insert, hqP]; exact hP1
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact right_ne_zero_of_mul hPe
    · exact hCb e he

/-- **The converted point depends only on its support.** -/
theorem symPt_convPt_eq {R : Type*} [CommRing R] [Algebra K R] {n' : ℕ}
    (φ' : SymRing K (Rfin K (SynF K F c0)) n' →ₐ[K] R) (hu : IsUnit (φ' (normS K (xS K F c0))))
    (hn : genusFK K F = n') (y : R →ₐ[K] K) (a : Fin (genusFK K F) → PtY K F c0) (ha : Function.Injective a)
    (hE : ptSet (y.comp φ') = (Finset.univ.image a).map (Function.Embedding.subtype _)) :
    symPt (convPt c0 φ' hu hn y) = symPt (tpY c0 ∘ a) := by
  subst hn
  have himg : Finset.univ.image (convPt c0 φ' hu rfl y) = Finset.univ.image (tpY c0 ∘ a) := by
    ext φ
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨i, rfl⟩
      have hm : liftTuple (y.comp φ') i ∈ ptSet (y.comp φ') := (mem_ptSet _ _).2 ⟨_, rfl⟩
      rw [hE] at hm
      obtain ⟨e, he, hee⟩ := Finset.mem_map.1 hm
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 he
      exact ⟨l, tpH_congr c0 hee _ _⟩
    · rintro ⟨l, rfl⟩
      have hm : (a l).1 ∈ ptSet (y.comp φ') := by
        rw [hE]; exact Finset.mem_map_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      obtain ⟨i, hi⟩ := (mem_ptSet _ _).1 hm
      exact ⟨i, tpH_congr c0 hi _ _⟩
  have hinj2 : Function.Injective (tpY c0 ∘ a) := (tpY_injective c0).comp ha
  have hinj1 : Function.Injective (convPt c0 φ' hu rfl y) := by
    have h := Finset.card_image_of_injective Finset.univ hinj2
    rw [← himg] at h
    exact fun i1 i2 e => Finset.card_image_iff.1 h (Finset.mem_coe.2 (Finset.mem_univ i1))
      (Finset.mem_coe.2 (Finset.mem_univ i2)) e
  exact symPt_eq_of_image_eq hinj1 hinj2 himg

end AJGen

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJGlue =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces

`B' = Rfin (SynF K F c0)`.
* `locallyOfFiniteType_sR`; the piece index `PIdx K F c0` and the open immersions `pj c0 i : Spec LocR → Spec B'`.
* `pj_kpt` (closed points), `pj_cov` (the pieces cover the closed points), `pj_over`.
The glued map `ajChart` is in part `AJGlue2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- the instance diamonds on the nested localizations need nested synthPending (diagnostics, session 20)
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Glue

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K]

/-- `Spec R → Spec K` is locally of finite type for a finite type `K`-algebra `R`. -/
instance locallyOfFiniteType_sR (R : Type u) [CommRing R] [Algebra K R] [Algebra.FiniteType K R] :
    LocallyOfFiniteType (sR K R) := by
  show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K R)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

variable [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K)

end Glue

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacSymB_Glue =====
section

/-!
# S4-JacSymB, file G1: gluing the charts `Sym^g B_A` to `Sym^g X` (L12)

The charts `Spec Sym^g B_A` (`A` a nonempty finite subset of `k`) form a diagram of open immersions
(`Sym^g B_A' = (Sym^g B_A)[1/N w]`, file SymLoc), and the diagram is locally directed: a prime of `Sym^g B_K` that
avoids `N w_{K,I}` and `N w_{K,J}` avoids `N w_{K,I ∪ J}`, because `w_{K,I} w_{K,J} = w_{K,I ∪ J} w_{K,(I∖K) ∩ (J∖K)}`.
`Sym^g X` is the colimit (Mathlib's locally directed gluing).
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

namespace RamanujanPetersson.JacSym

section GlueAlg

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {x : F} {g : ℕ}

variable (x g) in
/-- The restriction map `Sym^g B_A → Sym^g B_A'` for `A ⊆ A'`. -/
noncomputable def chartMap {A A' : Finset k} (h : A ⊆ A') :
    SymRing k (chartRing x A) g →ₐ[k] SymRing k (chartRing x A') g :=
  symMap (Subalgebra.inclusion (chartRing_mono x h))

theorem chartMap_refl {A : Finset k} (h : A ⊆ A) : chartMap x g h = AlgHom.id k _ := by
  rw [chartMap, Subalgebra.inclusion_self, symMap_id]

end GlueAlg

section GlueScheme

universe u

variable {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]

/-- Index category of the charts: nonempty finite subsets of `k`. -/
abbrev ChartIdx (k : Type u) : Type u := {A : Finset k // A.Nonempty}

variable (k) (x : F) (g : ℕ) [hx : Fact (Transcendental k x)]

end GlueScheme

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacComplete_AJSurj =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJSurj` (L19 route AJ: K-point surjectivity of `Σ [Q_i] - g [P0]`)

Over an algebraically closed `K`, with `g` the genus:
* `exists_sum_single_of_nonneg`: an effective divisor of degree `n` is a sum of `n` places;
* **`exists_eff_rep P0 hc`**: every class `c ∈ Pic⁰` is `Σ_{i < g} [t_i] - g • [P0]` (Riemann's inequality).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacLaw RamanujanPetersson.RR

section AJSurj

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem deg_zero' : Places.Divisor.deg (0 : Places.Divisor K F) = 0 := Finsupp.sum_zero_index

end AJSurj

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_CoreB_Dim =====
section

/-!
# Core B, O1: the heights on the Jacobian are bounded

* `ringKrullDim_le_of_finiteType`: a finite type algebra over a field has finite Krull dimension.
* `exists_coheight_le_of_isAffineOpen`: on an affine open of a scheme locally of finite type over a field,
  the coheights are bounded.
* `exists_height_le`: a quasi-compact scheme locally of finite type over a field has bounded heights
  (for the specialization order).
* `exists_height_max`: a bound on heights is attained by a least bound `g`.
* `exists_dim_Jac`: `∃ g, (∀ x, height x ≤ g) ∧ ∃ x, g ≤ height x` on `Jac K F`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CoreB

open CategoryTheory AlgebraicGeometry Order

universe u

lemma ringKrullDim_le_of_finiteType {K B : Type*} [Field K] [CommRing B] (φ : K →+* B)
    (hφ : φ.FiniteType) : ∃ n : ℕ, ringKrullDim B ≤ n := by
  let _ := φ.toAlgebra
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hφ
  refine ⟨n, (ringKrullDim_le_of_surjective f.toRingHom hf).trans ?_⟩
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

end RamanujanPetersson.CoreB


end


