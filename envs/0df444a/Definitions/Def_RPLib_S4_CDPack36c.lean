-- Prove2me | Definitions.Def_RPLib_S4_CDPack36c
-- name    : RPLib_S4_CDPack36c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T12:14:50.5677+00:00
-- url     : https://prove2.me/theorems/a48ca993-b76f-4f90-8139-91021f60152e
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 36c of 71
-- statement:
--   Part 36c of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_PicSurj`: The Jacobian (unit S4-JacComplete), part `PicSurj` (L20: `jacPic0` is surjective)
--   * `Def_RP_JacComplete_AJLoc`: The Jacobian (unit S4-JacComplete), part `AJLoc`: the local `ν`-piece through a closed point
--   * `Def_RP_JacComplete_PicJ`: The Jacobian (unit S4-JacComplete), part `PicJ` (L20, final form)
--   * `Def_RP_JacComplete_AJGreedy`: The Jacobian (unit S4-JacComplete), part `AJGreedy`: generic points off a hypersurface of `Sym^n`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack36b
import Definitions.Def_RPLib_S4_CDPack31
import Definitions.Def_RPLib_S4_CDPack29
import Definitions.Def_RPLib_S4_CDPack32
import Definitions.Def_RPLib_S4_CDPack28c

/-!
# Curve-duality library package, part 36c of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_PicSurj`: The Jacobian (unit S4-JacComplete), part `PicSurj` (L20: `jacPic0` is surjective)
* `Def_RP_JacComplete_AJLoc`: The Jacobian (unit S4-JacComplete), part `AJLoc`: the local `ν`-piece through a closed point
* `Def_RP_JacComplete_PicJ`: The Jacobian (unit S4-JacComplete), part `PicJ` (L20, final form)
* `Def_RP_JacComplete_AJGreedy`: The Jacobian (unit S4-JacComplete), part `AJGreedy`: generic points off a hypersurface of `Sym^n`
-/

set_option autoImplicit false

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

/-- The image of `jacPic0` in `Pic`. -/
noncomputable def rangeJ : AddSubgroup (PicK K F) where
  carrier := {c | ∃ σ : (lawChunk K F).H, ((Multiplicative.toAdd (jacPic0 K F σ) : Pic0K K F) : PicK K F) = c}
  add_mem' := by
    rintro _ _ ⟨σ, rfl⟩ ⟨τ, rfl⟩
    exact ⟨σ * τ, congrArg (fun z => ((Multiplicative.toAdd z : Pic0K K F) : PicK K F)) (map_mul (jacPic0 K F) σ τ)⟩
  zero_mem' := ⟨1, congrArg (fun z => ((Multiplicative.toAdd z : Pic0K K F) : PicK K F)) (map_one (jacPic0 K F))⟩
  neg_mem' := by
    rintro _ ⟨σ, rfl⟩
    exact ⟨σ⁻¹, congrArg (fun z => ((Multiplicative.toAdd z : Pic0K K F) : PicK K F)) (map_inv (jacPic0 K F) σ)⟩

theorem psiJ_mem_rangeJ (a : X0 K F) (ha : IsClosed ({a} : Set (X0 K F))) : psiJ K F a ∈ rangeJ K F :=
  ⟨_, jacPic0_lamB K F a ha⟩

open Classical in
theorem psiJ_of_pt (y : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K) (hy : y (lawPre K F).u0 ≠ 0) :
    ∃ a : X0 K F, IsClosed ({a} : Set (X0 K F)) ∧ (ptSet y).card = genusFK K F ∧
      psiJ K F a = clsK K F (Zdiv (ptSet y)) -
        clsK K F (ThetaD (lawData K F).Dm3 (lawData K F).Dm2 (lawData K F).c0 (lawData K F).c1) := by
  have hu : IsUnit (y (lawPre K F).u0) := isUnit_iff_ne_zero.2 hy
  obtain ⟨yR, e⟩ : ∃ yR : LawRing K F →ₐ[K] K, yR.comp (awayι (K := K) (lawPre K F).u0) = y :=
    ⟨IsLocalization.Away.liftAlgHom (lawPre K F).u0 hu, by
      refine AlgHom.ext fun t => ?_
      rw [AlgHom.comp_apply, awayι_apply, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
      rfl⟩
  refine ⟨kpt yR, isClosed_kpt yR, ?_, ?_⟩
  · rw [← e]; exact card_lawPt K F yR
  · rw [psiJ, psiS_kpt, psiA, e, psiL]

variable {K F} in
theorem div_incB_ne_zero_iff {f : Places.Rfin K F} (hf : f ≠ 0) (Q : Places.Rfin K F →ₐ[K] K) :
    PlacesK.div (incB K F f) (Sum.inl (ptP Q)) ≠ 0 ↔ Q f = 0 := by
  rw [PlacesK.div_apply]
  show Places.ord (ptP Q) (incB K F f) ≠ 0 ↔ _
  rw [incB_apply, PlacesK.ord_algebraMap _ hf, Nat.cast_ne_zero, cnt_ne_zero_iff _ hf, mem_ptP]

open Classical in
set_option maxHeartbeats 400000 in
/-- **L20, surjectivity**: every degree-`0` class is `[σ(D) - D]`. -/
theorem jacPic0_surjective : Function.Surjective (jacPic0 K F) := by
  suffices hle : Pic0K K F ≤ rangeJ K F by
    intro c
    obtain ⟨σ, hσ⟩ := hle (Multiplicative.toAdd c).2
    exact ⟨σ, Multiplicative.toAdd.injective (Subtype.ext hσ)⟩
  rcases Nat.eq_zero_or_pos (genusFK K F) with hg | hg
  · intro c hc
    obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective c
    have hD : D.deg = 0 := by rw [← degPicK_clsK]; exact (mem_Pic0K K F).1 hc
    show clsK K F D ∈ rangeJ K F
    rw [clsK_eq_zero_of_genus_zero hg hD]
    exact (rangeJ K F).zero_mem
  have hd : 1 + (genusFK K F - 1) = genusFK K F := by omega
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (LawRing K F)
  obtain ⟨y0R, -⟩ := exists_algHom_ker_eq (k := K) m
  let y0 := y0R.comp (awayι (K := K) (lawPre K F).u0)
  let t := liftTuple y0
  let c : Fin (genusFK K F - 1) → (Places.Rfin K F →ₐ[K] K) := fun j => t (Fin.cast hd (Fin.natAdd 1 j))
  let q0 := t (Fin.cast hd (Fin.castAdd (genusFK K F - 1) 0))
  let f := padMap (phi1 (k := K) (B := Places.Rfin K F)) c hd (lawPre K F).u0
  have hyQ : ∀ Q : Places.Rfin K F →ₐ[K] K, Q f = padPt phi1 c hd Q (lawPre K F).u0 := fun Q => by
    rw [← comp_padMap]; rfl
  have hq0 : padPt phi1 c hd q0 = y0 := by
    rw [padPt, liftTuple_phi1]
    conv_rhs => rw [← symPt_liftTuple y0]
    congr 1
    funext i
    have hl : (fun _ : Fin 1 => q0) = fun j => t (Fin.cast hd (Fin.castAdd (genusFK K F - 1) j)) := by
      funext j; rw [Fin.fin_one_eq_zero j]
    rw [hl]
    exact (congrFun (Fin.append_castAdd_natAdd (f := fun j => t (Fin.cast hd j))) (Fin.cast hd.symm i)).trans
      (by simp [t])
  have hy0u : y0 (lawPre K F).u0 ≠ 0 :=
    ((IsLocalization.Away.algebraMap_isUnit (lawPre K F).u0).map y0R).ne_zero
  have hq0f : q0 f ≠ 0 := by rw [hyQ, hq0]; exact hy0u
  have hf : f ≠ 0 := fun h => hq0f (by rw [h, map_zero])
  set Θ := ThetaD (lawData K F).Dm3 (lawData K F).Dm2 (lawData K F).c0 (lawData K F).c1
  have hQ : ∀ Q : Places.Rfin K F →ₐ[K] K, Q f ≠ 0 → ∃ a : X0 K F, IsClosed ({a} : Set (X0 K F)) ∧
      psiJ K F a = clsK K F (Zdiv (Finset.univ.image c)) + clsK K F (Finsupp.single (Sum.inl (ptP Q)) 1) -
        clsK K F Θ := by
    intro Q hQf
    obtain ⟨a, ha, hcard, hpsi⟩ := psiJ_of_pt K F (padPt phi1 c hd Q) (by rw [← hyQ]; exact hQf)
    have hpt : ptSet (padPt phi1 c hd Q) = insert Q (Finset.univ.image c) := by
      rw [ptSet_padPt, ptSet_phi1, Finset.insert_eq]
    have hQc : Q ∉ Finset.univ.image c := by
      intro hmem
      rw [hpt, Finset.insert_eq_of_mem hmem] at hcard
      have := Finset.card_image_le (s := Finset.univ) (f := c)
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    refine ⟨a, ha, ?_⟩
    rw [hpsi, hpt, Zdiv_insert hQc, clsK_add]
  obtain ⟨a0, ha0, hpsi0⟩ := hQ q0 hq0f
  let S : Finset (Places.Place K F) := (PlacesK.div (incB K F f)).support ∪
    (Set.finite_range (Sum.inr : IsDedekindDomain.HeightOneSpectrum (Places.Rinf K F) → Places.Place K F)).toFinset
  refine pic0_le_of_gen (rangeJ K F) (Sum.inl (ptP q0)) S ?_ ?_
  · intro hmem
    rcases Finset.mem_union.1 hmem with h1 | h1
    · exact (div_incB_ne_zero_iff hf q0).1 (Finsupp.mem_support_iff.1 h1) |> hq0f
    · obtain ⟨P, hP⟩ := (Set.Finite.mem_toFinset _).1 h1
      exact Sum.inr_ne_inl hP
  · intro v hv
    rcases v with P | P
    · obtain ⟨Q, rfl⟩ := exists_ptP P
      have hQf : Q f ≠ 0 := fun h0 => hv (Finset.mem_union_left _
        (Finsupp.mem_support_iff.2 ((div_incB_ne_zero_iff hf Q).2 h0)))
      obtain ⟨a, ha, hpsi⟩ := hQ Q hQf
      have key : clsK K F (Finsupp.single (Sum.inl (ptP Q)) 1) - clsK K F (Finsupp.single (Sum.inl (ptP q0)) 1) =
          psiJ K F a - psiJ K F a0 := by
        rw [hpsi, hpsi0]; abel
      rw [key]
      exact (rangeJ K F).sub_mem (psiJ_mem_rangeJ K F a ha) (psiJ_mem_rangeJ K F a0 ha0)
    · exact (hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 (Set.mem_range_self P)))).elim

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

/-- **The `ν`-piece** `Q ↦ ν(Q + c)` on `D(f)`. -/
noncomputable def pieceMap : SymRing K (Rfin K F) (genusFK K F) →ₐ[K] PieceR D c :=
  (pieceLift D c).comp D.nuMap

theorem ptSet_pieceMap (x : PieceR D c →ₐ[K] K) :
    ptSet (x.comp (pieceMap D c)) = D.nuF (padPt phi1 c rfl (x.comp (pieceι D c))) := by
  rw [pieceMap, ← AlgHom.comp_assoc, NuData.comp_nuMap, NuData.ptSet_nuPt, NuData.nuSet_eq_nuF,
    yOf_pieceLift]

theorem good_padPt (x : PieceR D c →ₐ[K] K) : padPt phi1 c rfl (x.comp (pieceι D c)) D.good ≠ 0 := by
  rw [← apply_pieceF, AlgHom.comp_apply]
  exact ((IsLocalization.Away.algebraMap_isUnit (pieceF D c)).map x).ne_zero

/-- **Value of the piece**: `[ν(Q + c)] = [Hn] - [Q] - [c]`. -/
theorem clsK_pieceMap (x : PieceR D c →ₐ[K] K) :
    clsK K F (Zdiv (ptSet (x.comp (pieceMap D c)))) = clsK K F D.Hn -
      clsK K F (Finsupp.single (Sum.inl (ptP (x.comp (pieceι D c)))) 1) - clsK K F (Zdiv (Finset.univ.image c)) := by
  have hy := good_padPt D c x
  have hcard := NuData.card_ptSet hy
  rw [ptSet_padPt1] at hcard
  have hQc : x.comp (pieceι D c) ∉ Finset.univ.image c := by
    intro hmem
    rw [Finset.insert_eq_of_mem hmem] at hcard
    have := Finset.card_image_le (s := Finset.univ) (f := c)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [ptSet_pieceMap, clsK_nuF hy, ptSet_padPt1, Zdiv_insert hQc, clsK_add]
  abel

end AJLoc

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacComplete_PicJ =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicJ` (L20, final form)

**`jacPicEquiv K F : J(K) ≃* Multiplicative Pic⁰(X_K)`** (Milne III.7.5-7.6): `kptEquiv` followed by the bijective
class map `jacPic0` (`jacPic0_injective`, `jacPic0_surjective`).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section PicJ

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **L20 (Milne III.7.5-7.6)**: `J(K) ≃* Pic⁰(X_K)`, `a ↦ [σ_a(D) - D]`. -/
noncomputable def jacPicEquiv : (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) ≃* Multiplicative (Pic0K K F) :=
  (kptEquiv K F).trans (MulEquiv.ofBijective (jacPic0 K F) ⟨jacPic0_injective K F, jacPic0_surjective K F⟩)

theorem jacPicEquiv_apply (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    jacPicEquiv K F a = jacPic0 K F (kptEquiv K F a) := rfl

end PicJ

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


