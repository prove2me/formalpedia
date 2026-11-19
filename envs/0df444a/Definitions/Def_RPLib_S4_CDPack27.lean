-- Prove2me | Definitions.Def_RPLib_S4_CDPack27
-- name    : RPLib_S4_CDPack27
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:32:13.701459+00:00
-- url     : https://prove2.me/theorems/f9390fa1-4aa0-4be4-8a66-c7a1277380fc
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 27 of 71
-- statement:
--   Part 27 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_Gram`: S4-JacLaw O5: the trace matrix of a point of `Sym^d` and its kernel line
--   * `Def_RP_JacLaw_MonPts`: S4-JacLaw, file O6c: monic generic polynomial, the zero set of a section, exact division
--   * `Def_RP_ThetaSquare_Plus`: Unit S4-ThetaSquare, file Plus: the plus-curve on coordinate rings
--   * `Def_RP_JacSymB_Height`: S4-JacSymB, file E2: every maximal ideal of `Sym^g X` has height at least `g`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack25
import Definitions.Def_RPLib_S4_CDPack26
import Definitions.Def_RPLib_S4_CDPack20

/-!
# Curve-duality library package, part 27 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_Gram`: S4-JacLaw O5: the trace matrix of a point of `Sym^d` and its kernel line
* `Def_RP_JacLaw_MonPts`: S4-JacLaw, file O6c: monic generic polynomial, the zero set of a section, exact division
* `Def_RP_ThetaSquare_Plus`: Unit S4-ThetaSquare, file Plus: the plus-curve on coordinate rings
* `Def_RP_JacSymB_Height`: S4-JacSymB, file E2: every maximal ideal of `Sym^g X` has height at least `g`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_Gram =====
section

/-!
# S4-JacLaw O5: the trace matrix of a point of `Sym^d` and its kernel line

For `χ : Fin d → B` and `h : Fin (d+1) → B` the trace matrix `M[m, l] = tr(χ_m h_l)` has entries in
`S_d = SymRing k B d`. At the point `a_1 + ... + a_d` it equals `Eᵀ F` with `E[i, m] = a_i(χ_m)`,
`F[i, l] = a_i(h_l)`, so its cofactor vector is `det E • crossVec F` (`symPt_kerVec`). The section
`sPt = Σ_l c_l(A) h_l` vanishes at every `a_i`, and when one cofactor is nonzero every combination of
the `h_l` vanishing at all `a_i` is a multiple of it (`exists_eq_smul_sPt`).
Also: Nullstellensatz units (`isUnit_of_forall_ne_zero`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym Matrix

section CrossMul

variable {R : Type*} [CommRing R] {m : ℕ}

theorem crossVec_mul (E : Matrix (Fin m) (Fin m) R) (F : Matrix (Fin m) (Fin (m + 1)) R) :
    crossVec (E * F) = E.det • crossVec F := by
  funext j
  have hs : (E * F).submatrix id j.succAbove = E * F.submatrix id j.succAbove := by
    ext a b
    simp [Matrix.mul_apply]
  simp only [crossVec, Pi.smul_apply, smul_eq_mul, hs, Matrix.det_mul]
  ring

end CrossMul

section Unit

variable {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]

/-- Nullstellensatz: an element nonvanishing at every `k`-point is a unit. -/
theorem isUnit_of_forall_ne_zero [IsAlgClosed k] [Algebra.FiniteType k R] (r : R)
    (h : ∀ x : R →ₐ[k] k, x r ≠ 0) : IsUnit r := by
  by_contra hr
  obtain ⟨m, hm, hrm⟩ := Ideal.exists_le_maximal (Ideal.span {r}) (Ideal.span_singleton_ne_top hr)
  obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (k := k) m
  refine h φ ?_
  rw [← RingHom.mem_ker, hφ]
  exact hrm (Ideal.subset_span (Set.mem_singleton r))

end Unit

section Trace

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {d : ℕ}

variable (k) in
/-- The trace `tr w = Σ_l w_l`, an `S_d`-invariant. -/
noncomputable def traceS (w : B) : SymRing k B d :=
  ⟨∑ l, inc l w, (mem_symRing _).mpr fun σ => by
    rw [perm_smul_def, map_sum]
    exact Fintype.sum_equiv σ _ _ fun l => AlgHom.congr_fun (permHom_comp_inc σ l) w⟩

theorem symPt_traceS (a : Fin d → (B →ₐ[k] k)) (w : B) : symPt a (traceS k w) = ∑ l, a l w := by
  rw [symPt_apply]
  show ptOf a (∑ l, inc l w) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun l _ => AlgHom.congr_fun (ptOf_inc a l) w

variable (k) in
/-- The trace matrix `M[m, l] = tr(χ_m h_l)`. -/
noncomputable def traceMat (χ : Fin d → B) (h : Fin (d + 1) → B) :
    Matrix (Fin d) (Fin (d + 1)) (SymRing k B d) :=
  Matrix.of fun m l => traceS k (χ m * h l)

/-- The evaluation matrix `E[i, m] = a_i(f_m)`. -/
def evMat {n : ℕ} (a : Fin d → (B →ₐ[k] k)) (f : Fin n → B) : Matrix (Fin d) (Fin n) k :=
  Matrix.of fun i m => a i (f m)

theorem traceMat_map (a : Fin d → (B →ₐ[k] k)) (χ : Fin d → B) (h : Fin (d + 1) → B) :
    (traceMat k χ h).map (symPt a) = (evMat a χ)ᵀ * evMat a h := by
  ext m l
  simp only [traceMat, evMat, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
    Matrix.transpose_apply, symPt_traceS, map_mul]

variable (k) in
/-- The kernel vector `c(A)`, entries in `S_d`. -/
noncomputable def kerVec (χ : Fin d → B) (h : Fin (d + 1) → B) : Fin (d + 1) → SymRing k B d :=
  crossVec (traceMat k χ h)

theorem symPt_kerVec (a : Fin d → (B →ₐ[k] k)) (χ : Fin d → B) (h : Fin (d + 1) → B) (l : Fin (d + 1)) :
    symPt a (kerVec k χ h l) = (evMat a χ).det * crossVec (evMat a h) l := by
  have h1 := congr_fun (crossVec_map (symPt a).toRingHom (traceMat k χ h)) l
  have h2 : (traceMat k χ h).map (symPt a).toRingHom = (evMat a χ)ᵀ * evMat a h :=
    traceMat_map a χ h
  rw [h2, crossVec_mul, det_transpose] at h1
  exact h1.symm

/-- The section `s_A = Σ_l c_l(A) h_l` at the point `a`. -/
noncomputable def sPt (a : Fin d → (B →ₐ[k] k)) (χ : Fin d → B) (h : Fin (d + 1) → B) : B :=
  ∑ l, symPt a (kerVec k χ h l) • h l

variable (a : Fin d → (B →ₐ[k] k)) (χ : Fin d → B) (h : Fin (d + 1) → B)

theorem apply_sPt (i : Fin d) : a i (sPt a χ h) = 0 := by
  have h0 : ∑ l, a i (h l) * crossVec (evMat a h) l = 0 := congr_fun (mulVec_crossVec (evMat a h)) i
  simp only [sPt, map_sum, map_smul, symPt_kerVec, smul_eq_mul]
  calc ∑ l, (evMat a χ).det * crossVec (evMat a h) l * a i (h l)
      = (evMat a χ).det * ∑ l, a i (h l) * crossVec (evMat a h) l := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = 0 := by rw [h0, mul_zero]

variable {a χ h}

theorem det_ne_zero_of_kerVec {l0 : Fin (d + 1)} (hl : symPt a (kerVec k χ h l0) ≠ 0) :
    (evMat a χ).det ≠ 0 := by
  intro h0
  rw [symPt_kerVec, h0, zero_mul] at hl
  exact hl rfl

theorem crossVec_ne_zero_of_kerVec {l0 : Fin (d + 1)} (hl : symPt a (kerVec k χ h l0) ≠ 0) :
    crossVec (evMat a h) ≠ 0 := by
  intro h0
  rw [symPt_kerVec, h0, Pi.zero_apply, mul_zero] at hl
  exact hl rfl

/-- The points of a good `A` are distinct. -/
theorem injective_of_kerVec {l0 : Fin (d + 1)} (hl : symPt a (kerVec k χ h l0) ≠ 0) :
    Function.Injective a := by
  intro i j hij
  by_contra hne
  exact det_ne_zero_of_kerVec hl
    (Matrix.det_zero_of_row_eq hne (funext fun m => by simp [evMat, hij]))

theorem sPt_ne_zero (hli : LinearIndependent k h) {l0 : Fin (d + 1)}
    (hl : symPt a (kerVec k χ h l0) ≠ 0) : sPt a χ h ≠ 0 :=
  fun h0 => hl (Fintype.linearIndependent_iff.1 hli _ h0 l0)

/-- **The kernel line.** A combination of the `h_l` vanishing at every `a_i` is a multiple of `s_A`. -/
theorem exists_eq_smul_sPt {l0 : Fin (d + 1)} (hl : symPt a (kerVec k χ h l0) ≠ 0) (y : Fin (d + 1) → k)
    (hy : ∀ i, a i (∑ l, y l • h l) = 0) : ∃ t : k, ∑ l, y l • h l = t • sPt a χ h := by
  have hc := crossVec_ne_zero_of_kerVec hl
  have hE := det_ne_zero_of_kerVec hl
  have hmem : y ∈ LinearMap.ker (evMat a h).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    have := hy i
    simp only [map_sum, map_smul, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, evMat, Matrix.of_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [ker_eq_span_crossVec_self _ hc, Submodule.mem_span_singleton] at hmem
  obtain ⟨t, ht⟩ := hmem
  refine ⟨t * ((evMat a χ).det)⁻¹, ?_⟩
  rw [← ht]
  simp only [sPt, symPt_kerVec, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  field_simp

theorem mem_span_sPt {l0 : Fin (d + 1)} (hl : symPt a (kerVec k χ h l0) ≠ 0) {f : B}
    (hf : f ∈ Submodule.span k (Set.range h)) (hz : ∀ i, a i f = 0) : f ∈ k ∙ sPt a χ h := by
  obtain ⟨y, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hf
  obtain ⟨t, ht⟩ := exists_eq_smul_sPt hl y hz
  rw [ht]
  exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _)

theorem sPt_mem_span : sPt a χ h ∈ Submodule.span k (Set.range h) :=
  Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

end Trace

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_MonPts =====
section

/-!
# S4-JacLaw, file O6c: monic generic polynomial, the zero set of a section, exact division

* `monPoly w ∈ Sym^d(B)[X]`: the monic polynomial `∏_l (X - w_l)` with symmetric coefficients
  (`map_symPt_monPoly`: its value at the point `a_1 + ... + a_d` is `∏_l (X - a_l(w))`).
* `exists_zeroSet`: for `s ∈ B` with `B/(s)` finite-dimensional over the algebraically closed `k` and
  one `w0` whose multiplication has separable characteristic polynomial, the `k`-points of `B` vanishing
  at `s` form a finset `Z` with `#Z = dim B/(s)` and `charpoly (w mod s) = ∏_{φ ∈ Z} (X - φ(w))`.
* `prod_divByMonic_sdiff`, `enumF` / `prod_enumF`, `prod_eq_sign_coeff_zero`: the exact division
  `∏_Z /ₘ ∏_A = ∏_{Z \ A}`, an enumeration of a finset, and `∏ u = (-1)^# · coeff 0 (∏ (X - u))`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym Polynomial Module

section MonPoly

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {g : ℕ}

/-- `∏_l (X - w_l)` over `X^g(B)`. -/
noncomputable def monE (w : B) : (XPow k B g)[X] := ∏ l, (X - C (inc l w))

theorem map_permHom_monE (σ : Equiv.Perm (Fin g)) (w : B) :
    (monE (k := k) (g := g) w).map (permHom σ).toRingHom = monE w := by
  have h : ∀ l : Fin g, (permHom σ) (inc (k := k) l w) = inc (σ l) w := fun l => by
    rw [← AlgHom.comp_apply, permHom_comp_inc]
  simp only [monE, Polynomial.map_prod, Polynomial.map_sub, map_C, map_X,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h]
  exact Fintype.prod_equiv σ _ _ (fun _ => rfl)

theorem monE_coeff_mem (w : B) (j : ℕ) : (monE (k := k) (g := g) w).coeff j ∈ SymRing k B g := by
  rw [mem_symRing]
  intro σ
  rw [perm_smul_def]
  have := congrArg (fun p => p.coeff j) (map_permHom_monE (k := k) σ w)
  simp only [coeff_map] at this
  exact this

theorem monE_mem_lifts (w : B) : monE (k := k) (g := g) w ∈ lifts (SymRing k B g).val.toRingHom := by
  rw [lifts_iff_coeff_lifts]
  intro j
  exact ⟨⟨_, monE_coeff_mem w j⟩, rfl⟩

/-- `∏_l (X - w_l)` with coefficients in `Sym^g(B)`. -/
noncomputable def monPoly (w : B) : (SymRing k B g)[X] :=
  Classical.choose ((mem_lifts _).mp (monE_mem_lifts (k := k) (g := g) w))

theorem map_monPoly (w : B) : (monPoly (k := k) (g := g) w).map (SymRing k B g).val.toRingHom = monE w :=
  Classical.choose_spec ((mem_lifts _).mp (monE_mem_lifts (k := k) (g := g) w))

theorem monic_monE (w : B) : (monE (k := k) (g := g) w).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem monic_monPoly (w : B) : (monPoly (k := k) (g := g) w).Monic := by
  have hinj : Function.Injective (SymRing k B g).val.toRingHom := fun _ _ h => Subtype.ext h
  rw [hinj.monic_map_iff, map_monPoly]
  exact monic_monE w

/-- The monic generic polynomial at the point `a_1 + ... + a_g`. -/
theorem map_symPt_monPoly (a : Fin g → (B →ₐ[k] k)) (w : B) :
    (monPoly (k := k) (g := g) w).map (symPt a).toRingHom = ∏ l, (X - C (a l w)) := by
  have h : (symPt a).toRingHom = (ptOf a).toRingHom.comp (SymRing k B g).val.toRingHom := rfl
  rw [h, ← Polynomial.map_map, map_monPoly, monE, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Polynomial.map_sub, map_C, map_X]
  congr 2
  exact AlgHom.congr_fun (ptOf_inc a l) w

end MonPoly

section Zero

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B]

/-- **Zero set of a section.** If `B/(s)` is finite-dimensional and some `w0` has separable characteristic
polynomial on it, the `k`-points of `B` killing `s` are `dim B/(s)` many and diagonalise every `w`. -/
theorem exists_zeroSet (s : B) [FiniteDimensional k (B ⧸ Ideal.span {s})] (w0 : B)
    (hsep : (LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {s})
      (Ideal.Quotient.mkₐ k (Ideal.span {s}) w0))).Separable) :
    ∃ Z : Finset (B →ₐ[k] k), (∀ φ, φ ∈ Z ↔ φ s = 0) ∧ Z.card = finrank k (B ⧸ Ideal.span {s}) ∧
      ∀ w, LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {s}) (Ideal.Quotient.mkₐ k (Ideal.span {s}) w)) =
        ∏ φ ∈ Z, (X - C (φ w)) := by
  classical
  set I := Ideal.span {s}
  obtain ⟨v, hv0, hv, hcard⟩ := exists_eigen_of_separable (Ideal.Quotient.mkₐ k I w0) hsep
  have hlam : Function.Injective (fun μ : (LinearMap.charpoly (Algebra.lmul k (B ⧸ I)
      (Ideal.Quotient.mkₐ k I w0))).roots.toFinset => (μ : k)) := Subtype.val_injective
  set ψ := eigChar hlam hv0 hv hcard
  have hinj : Function.Injective fun j => (ψ j).comp (Ideal.Quotient.mkₐ k I) := by
    intro i j hij
    exact eigChar_injective hlam hv0 hv hcard (Ideal.Quotient.algHom_ext k hij)
  refine ⟨Finset.univ.image fun j => (ψ j).comp (Ideal.Quotient.mkₐ k I), fun φ => ?_, ?_, fun w => ?_⟩
  · constructor
    · intro hφ
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hφ
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton_self s), map_zero]
    · intro hφ
      have hI : ∀ a : B, a ∈ I → φ a = 0 := by
        intro a ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [map_mul, hφ, mul_zero]
      obtain ⟨j, hj⟩ := exists_eq_eigChar hlam hv0 hv hcard (Ideal.Quotient.liftₐ I φ hI)
      refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
      change (eigChar hlam hv0 hv hcard j).comp _ = φ
      rw [← hj, Ideal.Quotient.liftₐ_comp]
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard]
  · rw [charpoly_lmul_eq hlam hv0 hv hcard, Finset.prod_image fun x _ y _ h => hinj h]
    rfl

end Zero

section Div

/-- Exact division `∏_{φ ∈ Z} (X - u φ) /ₘ ∏_i (X - u (a i)) = ∏_{φ ∈ Z \ a} (X - u φ)`. -/
theorem prod_divByMonic_sdiff {R ι : Type*} [CommRing R] [DecidableEq ι] {d : ℕ} (Z : Finset ι)
    (a : Fin d → ι) (ha : Function.Injective a) (haZ : ∀ i, a i ∈ Z) (u : ι → R) :
    (∏ φ ∈ Z, (X - C (u φ))) /ₘ (∏ i, (X - C (u (a i)))) =
      ∏ φ ∈ Z \ Finset.univ.image a, (X - C (u φ)) := by
  have hsub : Finset.univ.image a ⊆ Z := by
    intro φ hφ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hφ
    exact haZ i
  have hprod : ∏ i, (X - C (u (a i))) = ∏ φ ∈ Finset.univ.image a, (X - C (u φ)) := by
    rw [Finset.prod_image fun x _ y _ h => ha h]
  rw [hprod, ← Finset.prod_sdiff hsub, mul_comm (∏ φ ∈ Z \ Finset.univ.image a, (X - C (u φ)))]
  exact mul_divByMonic_cancel_left _ (monic_prod_of_monic _ _ fun φ _ => monic_X_sub_C (u φ))

theorem prod_eq_sign_coeff_zero {R ι : Type*} [CommRing R] (T : Finset ι) (u : ι → R) :
    ∏ φ ∈ T, u φ = (-1) ^ T.card * (∏ φ ∈ T, (X - C (u φ))).coeff 0 := by
  rw [coeff_zero_eq_eval_zero, eval_prod]
  simp only [eval_sub, eval_X, eval_C, zero_sub]
  rw [Finset.prod_neg, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- An enumeration of a finset of known cardinality. -/
noncomputable def enumF {α : Type*} (T : Finset α) {n : ℕ} (h : T.card = n) : Fin n → α :=
  fun l => ((Fintype.equivFinOfCardEq ((Fintype.card_coe T).trans h)).symm l : α)

theorem enumF_mem {α : Type*} (T : Finset α) {n : ℕ} (h : T.card = n) (l : Fin n) : enumF T h l ∈ T :=
  ((Fintype.equivFinOfCardEq ((Fintype.card_coe T).trans h)).symm l).2

theorem enumF_injective {α : Type*} (T : Finset α) {n : ℕ} (h : T.card = n) : Function.Injective (enumF T h) :=
  fun _ _ hl => (Fintype.equivFinOfCardEq ((Fintype.card_coe T).trans h)).symm.injective (Subtype.ext hl)

theorem prod_enumF {α M : Type*} [CommMonoid M] (T : Finset α) {n : ℕ} (h : T.card = n) (f : α → M) :
    ∏ l, f (enumF T h l) = ∏ φ ∈ T, f φ := by
  rw [← Finset.prod_coe_sort T f]
  exact Fintype.prod_equiv (Fintype.equivFinOfCardEq ((Fintype.card_coe T).trans h)).symm _ _ fun _ => rfl

end Div

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_ThetaSquare_Plus =====
section

/-!
# Unit S4-ThetaSquare, file Plus: the plus-curve on coordinate rings

For a `g`-tuple `a` of `k`-points of `B` and a slot `i0`, `plusMap a i0 : Sym^g B → R` sends a symmetric tensor to its
value at `(a_1, .., P, .., a_g)` with the generic point `P` of `B` in slot `i0`, where `ι : B →ₐ R` is any map
(the inclusion of the curve's coordinate ring in a larger chart ring). On `R`-points it is
`y ∘ plusMap = symPt (update a i0 (y ∘ ι))` (`comp_plusMap`), and on norms
`plusMap (Nm w) = ι w * ∏_{i ≠ i0} a_i(w)` (`plusMap_normS`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.JacSym

section PlusRing

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {R : Type*} [CommRing R] [Algebra k R]
  {R' : Type*} [CommRing R'] [Algebra k R'] {g : ℕ}

/-- The multilinear map `(b_i) ↦ ∏ a_i (b_i)` with values in a `k`-algebra `R`. -/
noncomputable def ptMLR (a : Fin g → (B →ₐ[k] R)) : MultilinearMap k (fun _ : Fin g => B) R :=
  (MultilinearMap.mkPiAlgebra k (Fin g) R).compLinearMap (fun i => (a i).toLinearMap)

theorem ptMLR_apply (a : Fin g → (B →ₐ[k] R)) (b : Fin g → B) : ptMLR a b = ∏ i, a i (b i) := by
  simp [ptMLR, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-- `b_1 ⊗ ... ⊗ b_g ↦ ∏ a_i (b_i)` as an algebra map `X^g → R`. -/
noncomputable def ptOfR (a : Fin g → (B →ₐ[k] R)) : XPow k B g →ₐ[k] R :=
  PiTensorProduct.liftAlgHom (ptMLR a) (by rw [ptMLR_apply]; simp)
    (fun x y => by rw [ptMLR_apply, ptMLR_apply, ptMLR_apply, ← Finset.prod_mul_distrib]; simp)

@[simp] theorem ptOfR_tprod (a : Fin g → (B →ₐ[k] R)) (b : Fin g → B) :
    ptOfR a (PiTensorProduct.tprod k b) = ∏ i, a i (b i) := by
  rw [ptOfR, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod, ptMLR_apply]

theorem ptOfR_comp_inc (a : Fin g → (B →ₐ[k] R)) (i : Fin g) : (ptOfR a).comp (inc i) = a i := by
  ext b
  simp only [inc, AlgHom.comp_apply, PiTensorProduct.singleAlgHom_apply, ptOfR_tprod]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem ptOfR_inc (a : Fin g → (B →ₐ[k] R)) (i : Fin g) (b : B) : ptOfR a (inc i b) = a i b :=
  AlgHom.congr_fun (ptOfR_comp_inc a i) b

theorem comp_ptOfR (φ : R →ₐ[k] R') (a : Fin g → (B →ₐ[k] R)) :
    φ.comp (ptOfR a) = ptOfR (fun i => φ.comp (a i)) := by
  apply PiTensorProduct.algHom_ext
  intro i
  change φ.comp ((ptOfR a).comp (inc i)) = (ptOfR _).comp (inc i)
  rw [ptOfR_comp_inc, ptOfR_comp_inc]

theorem ptOfR_eq_ptOf (a : Fin g → (B →ₐ[k] k)) : ptOfR a = ptOf a := by
  apply PiTensorProduct.algHom_ext
  intro i
  change (ptOfR a).comp (inc i) = (ptOf a).comp (inc i)
  rw [ptOfR_comp_inc, ptOf_inc]

/-- The tuple `a` with slot `i0` replaced by `ι : B →ₐ R` (the other slots are the constants `a i`). -/
noncomputable def plusTuple (ι : B →ₐ[k] R) (a : Fin g → (B →ₐ[k] k)) (i0 : Fin g) : Fin g → (B →ₐ[k] R) :=
  Function.update (fun i => (Algebra.ofId k R).comp (a i)) i0 ι

theorem plusTuple_apply (ι : B →ₐ[k] R) (a : Fin g → (B →ₐ[k] k)) (i0 l : Fin g) (w : B) :
    plusTuple ι a i0 l w = if l = i0 then ι w else algebraMap k R (a l w) := by
  by_cases h : l = i0
  · subst h; simp [plusTuple]
  · simp [plusTuple, h]

/-- **The plus-curve on coordinate rings**: `Sym^g B → R`, `x ↦ x(a_1, .., P, .., a_g)` (`P` in slot `i0`). -/
noncomputable def plusMap (ι : B →ₐ[k] R) (a : Fin g → (B →ₐ[k] k)) (i0 : Fin g) : SymRing k B g →ₐ[k] R :=
  (ptOfR (plusTuple ι a i0)).comp (SymRing k B g).val

theorem plusMap_apply (ι : B →ₐ[k] R) (a : Fin g → (B →ₐ[k] k)) (i0 : Fin g) (x : SymRing k B g) :
    plusMap ι a i0 x = ptOfR (plusTuple ι a i0) (x : XPow k B g) := rfl

/-- `R`-points of the plus-curve: `y ∘ plusMap = symPt (update a i0 (y ∘ ι))`. -/
theorem comp_plusMap (ι : B →ₐ[k] R) (a : Fin g → (B →ₐ[k] k)) (i0 : Fin g) (y : R →ₐ[k] k) :
    y.comp (plusMap ι a i0) = symPt (Function.update a i0 (y.comp ι)) := by
  have h : y.comp (ptOfR (plusTuple ι a i0)) = ptOf (Function.update a i0 (y.comp ι)) := by
    rw [comp_ptOfR, ← ptOfR_eq_ptOf]
    congr 1
    funext i
    by_cases hi : i = i0
    · subst hi; simp [plusTuple]
    · rw [Function.update_of_ne hi]
      simp only [plusTuple, Function.update_of_ne hi]
      ext b
      simp only [AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply]
  ext x
  change y (ptOfR (plusTuple ι a i0) (x : XPow k B g)) = ptOf _ (x : XPow k B g)
  rw [← h]
  rfl

theorem plusMap_normS (ι : B →ₐ[k] R) (a : Fin g → (B →ₐ[k] k)) (i0 : Fin g) (w : B) :
    plusMap ι a i0 (normS k w) = ι w * ∏ i ∈ Finset.univ.erase i0, algebraMap k R (a i w) := by
  rw [plusMap_apply, normS_coe, map_prod]
  simp only [ptOfR_inc]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0), plusTuple_apply, if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [plusTuple_apply, if_neg (Finset.ne_of_mem_erase hl)]

end PlusRing

end RamanujanPetersson.ThetaSquare

end

-- ===== S4.Def_RP_JacSymB_Height =====
section

/-!
# S4-JacSymB, file E2: every maximal ideal of `Sym^g X` has height at least `g`

Specialising the first `j` coordinates at a `k`-point gives a strictly increasing chain of `g + 1` primes of `X^g`
below the point; integrality (incomparability) keeps it strict on `Sym^g X`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section Height

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.FiniteType k B] {g : ℕ}

/-- Specialise the coordinates `l < j` at `a l`. -/
noncomputable def specHom (a : Fin g → (B →ₐ[k] k)) (j : ℕ) : XPow k B g →ₐ[k] XPow k B g :=
  liftFam (fun l => if (l : ℕ) < j then (Algebra.ofId k (XPow k B g)).comp (a l) else inc l)

omit [IsAlgClosed k] [IsDomain B] [Algebra.FiniteType k B] in
theorem specHom_inc (a : Fin g → (B →ₐ[k] k)) (j : ℕ) (l : Fin g) :
    (specHom a j).comp (inc l) = if (l : ℕ) < j then (Algebra.ofId k (XPow k B g)).comp (a l) else inc l :=
  liftFam_inc _ l

omit [IsAlgClosed k] [IsDomain B] [Algebra.FiniteType k B] in
theorem specHom_succ (a : Fin g → (B →ₐ[k] k)) (j : ℕ) :
    specHom a (j + 1) = (liftFam (fun l : Fin g =>
      if (l : ℕ) = j then (Algebra.ofId k (XPow k B g)).comp (a l) else inc l)).comp (specHom a j) := by
  apply PiTensorProduct.algHom_ext
  intro l
  change (specHom a (j + 1)).comp (inc l) = ((liftFam _).comp (specHom a j)).comp (inc l)
  rw [AlgHom.comp_assoc, specHom_inc, specHom_inc]
  by_cases h1 : (l : ℕ) < j
  · rw [if_pos (by omega : (l : ℕ) < j + 1), if_pos h1]
    ext b
    simp only [AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.commutes]
  · rw [if_neg h1, liftFam_inc]
    by_cases h2 : (l : ℕ) = j
    · rw [if_pos (by omega : (l : ℕ) < j + 1), if_pos h2]
    · rw [if_neg (by omega), if_neg h2]

omit [IsAlgClosed k] [IsDomain B] [Algebra.FiniteType k B] in
theorem ker_specHom_le_succ (a : Fin g → (B →ₐ[k] k)) (j : ℕ) :
    RingHom.ker (specHom a j) ≤ RingHom.ker (specHom a (j + 1)) := by
  intro t ht
  rw [RingHom.mem_ker] at ht ⊢
  rw [specHom_succ, AlgHom.comp_apply, ht, map_zero]

theorem exists_mem_ker_specHom_succ (hB : ¬ IsField B) (a : Fin g → (B →ₐ[k] k)) (j : ℕ) (hj : j < g) :
    ∃ t, t ∈ RingHom.ker (specHom a (j + 1)) ∧ t ∉ RingHom.ker (specHom a j) := by
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ring.ne_bot_of_isMaximal_of_not_isField (ker_isMaximal (a ⟨j, hj⟩)) hB)
  refine ⟨inc ⟨j, hj⟩ π, ?_, ?_⟩
  · rw [RingHom.mem_ker, ← AlgHom.comp_apply, specHom_inc, if_pos (by simp), AlgHom.comp_apply,
      (RingHom.mem_ker).1 hπ, map_zero]
  · rw [RingHom.mem_ker, ← AlgHom.comp_apply, specHom_inc, if_neg (by simp)]
    intro h0
    apply hπ0
    apply eq_zero_of_forall_pt (k := k)
    intro x0
    have h1 := congrArg (ptOf (fun _ : Fin g => x0)) h0
    rw [← AlgHom.comp_apply, ptOf_inc, map_zero] at h1
    exact h1

omit [IsAlgClosed k] [IsDomain B] [Algebra.FiniteType k B] in
theorem specHom_top (a : Fin g → (B →ₐ[k] k)) :
    specHom a g = (Algebra.ofId k (XPow k B g)).comp (ptOf a) := by
  apply PiTensorProduct.algHom_ext
  intro l
  change (specHom a g).comp (inc l) = ((Algebra.ofId k (XPow k B g)).comp (ptOf a)).comp (inc l)
  rw [specHom_inc, if_pos l.2, AlgHom.comp_assoc, ptOf_inc]

/-- Height of a `k`-point of `Sym^g X` is at least `g`. -/
theorem le_height_ker (hB : ¬ IsField B) (a : Fin g → (B →ₐ[k] k)) :
    (g : ℕ∞) ≤ (RingHom.ker (symPt a)).height := by
  have : IsDomain (XPow k B g) := isDomain_xPow k B g
  have hpr : ∀ j, (RingHom.ker (specHom a j)).IsPrime := fun j => RingHom.ker_isPrime _
  have key : ∀ j ≤ g, (j : ℕ∞) ≤
      ((RingHom.ker (specHom a j)).comap (algebraMap (SymRing k B g) (XPow k B g))).height := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨t, ht1, ht2⟩ := exists_mem_ker_specHom_succ hB a j (by omega)
      have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := SymRing k B g) (ker_specHom_le_succ a j)
        ⟨ht1, ht2⟩ (Algebra.IsIntegral.isIntegral t)
      calc ((j + 1 : ℕ) : ℕ∞) = (j : ℕ∞) + 1 := by push_cast; rfl
        _ ≤ ((RingHom.ker (specHom a j)).comap (algebraMap (SymRing k B g) (XPow k B g))).height + 1 := by
          gcongr
          exact ih (by omega)
        _ ≤ _ := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  refine (key g le_rfl).trans (Ideal.height_mono ?_)
  intro s hs
  rw [Ideal.mem_comap, RingHom.mem_ker, specHom_top, AlgHom.comp_apply, Algebra.ofId_apply] at hs
  rw [RingHom.mem_ker]
  exact (algebraMap k (XPow k B g)).injective (by rw [map_zero]; exact hs)

/-- The local ring of `Sym^g X` at a closed point has dimension at least `g`. -/
theorem le_ringKrullDim_localization (hB : ¬ IsField B) (M : Ideal (SymRing k B g)) [M.IsMaximal] :
    (g : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime M) := by
  obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (k := k) M
  have h := IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M)
  refine le_of_le_of_eq ?_ h.symm
  rw [← hφ, ← symPt_liftTuple φ]
  exact_mod_cast le_height_ker hB (liftTuple φ)

end Height

end RamanujanPetersson.JacSym

end


