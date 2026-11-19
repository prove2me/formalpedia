-- Prove2me | Definitions.Def_RPLib_S4_CDPack26
-- name    : RPLib_S4_CDPack26
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:12:21.883029+00:00
-- url     : https://prove2.me/theorems/47c244a9-e896-48b0-91b7-27aed8389ccd
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 26 of 71
-- statement:
--   Part 26 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_LinAlg`: S4-JacLaw, file O3: linear algebra for the negation step
--   * `Def_RP_JacLaw_Pres`: S4-JacLaw, file O4b: the Δ-ratio presentation of `B ⧸ (s)`
--   * `Def_RP_JacLaw_Fam`: S4-JacLaw, file O6b: the Δ-ratio presentation in families
--   * `Def_RP_JacLaw_Diag`: S4-JacLaw, file O4a: diagonalising a finite commutative algebra by one element
--   * `Def_RP_JacChunkA_Pts`: Group chunk A0 (unit S4-JacChunkA): closed points over an algebraically closed field
--   * `Def_RP_JacChunkA_Trans`: Group chunk A1 (unit S4-JacChunkA): translations of a strict group chunk
--   * `Def_RP_JacLaw_Sep`: S4-JacLaw, file O9 (part Sep): Lagrange elements, separating elements, reduced quotients
--   * `Def_RP_JacChunkA_Val`: Group chunk A2 (unit S4-JacChunkA): pointwise calculus for partial maps, the germ monoid
--   * `Def_RP_JacChunkA_Germ`: Group chunk A2, part 2 (unit S4-JacChunkA): the germ group and the translation subgroup
--   * `Def_RP_JacDivisors_R`: S4-JacDivisors R (O10, algebra part): étale over a regular ring is regular
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib

/-!
# Curve-duality library package, part 26 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_LinAlg`: S4-JacLaw, file O3: linear algebra for the negation step
* `Def_RP_JacLaw_Pres`: S4-JacLaw, file O4b: the Δ-ratio presentation of `B ⧸ (s)`
* `Def_RP_JacLaw_Fam`: S4-JacLaw, file O6b: the Δ-ratio presentation in families
* `Def_RP_JacLaw_Diag`: S4-JacLaw, file O4a: diagonalising a finite commutative algebra by one element
* `Def_RP_JacChunkA_Pts`: Group chunk A0 (unit S4-JacChunkA): closed points over an algebraically closed field
* `Def_RP_JacChunkA_Trans`: Group chunk A1 (unit S4-JacChunkA): translations of a strict group chunk
* `Def_RP_JacLaw_Sep`: S4-JacLaw, file O9 (part Sep): Lagrange elements, separating elements, reduced quotients
* `Def_RP_JacChunkA_Val`: Group chunk A2 (unit S4-JacChunkA): pointwise calculus for partial maps, the germ monoid
* `Def_RP_JacChunkA_Germ`: Group chunk A2, part 2 (unit S4-JacChunkA): the germ group and the translation subgroup
* `Def_RP_JacDivisors_R`: S4-JacDivisors R (O10, algebra part): étale over a regular ring is regular
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_LinAlg =====
section

/-!
# S4-JacLaw, file O3: linear algebra for the negation step

* `crossVec M`: the cofactor vector of an `m × (m+1)` matrix (`M *ᵥ crossVec M = 0`, entries are signed maximal
  minors, compatible with ring maps). Over a field, if `crossVec M' ≠ 0` for `M'` made of `m` rows of `M` and
  `ker M ≠ 0`, then `ker M = K ∙ crossVec M'` (Cramer's rule for the kernel line).
* `det_fromCols_eq`: if `V = Aα F + Z E` then `det [Aα | V] = det [Aα | Z] · det E` (block triangular).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open Matrix

section Cross

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The cofactor vector of an `m × (m+1)` matrix. -/
def crossVec (M : Matrix (Fin m) (Fin (m + 1)) R) : Fin (m + 1) → R :=
  fun j => (-1) ^ (j : ℕ) * (M.submatrix id j.succAbove).det

theorem det_cons (M : Matrix (Fin m) (Fin (m + 1)) R) (v : Fin (m + 1) → R) :
    (Matrix.of (Fin.cons v (fun i => M i) : Fin (m + 1) → Fin (m + 1) → R)).det =
      ∑ j, v j * crossVec M j := by
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : (Matrix.of (Fin.cons v (fun i => M i) : Fin (m + 1) → Fin (m + 1) → R)).submatrix Fin.succ
      j.succAbove = M.submatrix id j.succAbove := by
    ext a b
    simp
  rw [hs, crossVec, Matrix.of_apply, Fin.cons_zero]
  ring

theorem mulVec_crossVec (M : Matrix (Fin m) (Fin (m + 1)) R) : M *ᵥ crossVec M = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [← det_cons M (M i)]
  refine Matrix.det_zero_of_row_eq (i := 0) (j := i.succ) (Fin.succ_ne_zero i).symm ?_
  funext l
  simp

theorem crossVec_map {S : Type*} [CommRing S] (f : R →+* S) (M : Matrix (Fin m) (Fin (m + 1)) R) :
    crossVec (M.map f) = fun j => f (crossVec M j) := by
  funext j
  simp only [crossVec, map_mul, map_pow, map_neg, map_one, RingHom.map_det]
  rfl

end Cross

section Field

variable {K : Type*} [Field K] {m p : ℕ}

theorem surjective_of_crossVec_ne_zero (M : Matrix (Fin m) (Fin (m + 1)) K) (hc : crossVec M ≠ 0) :
    Function.Surjective M.mulVecLin := by
  obtain ⟨j, hj⟩ : ∃ j, crossVec M j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  have hdet : (M.submatrix id j.succAbove).det ≠ 0 := by
    intro h0
    apply hj
    rw [crossVec, h0, mul_zero]
  have hsurj : Function.Surjective (M.submatrix id j.succAbove).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨Fin.insertNth j 0 x, ?_⟩
  rw [← hx]
  funext i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
  rw [Fin.sum_univ_succAbove _ j, Fin.insertNth_apply_same, mul_zero, zero_add]
  simp only [Fin.insertNth_apply_succAbove]

theorem finrank_ker_of_crossVec_ne_zero (M : Matrix (Fin m) (Fin (m + 1)) K) (hc : crossVec M ≠ 0) :
    Module.finrank K (LinearMap.ker M.mulVecLin) = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [LinearMap.range_eq_top.mpr (surjective_of_crossVec_ne_zero M hc), finrank_top] at h
  simp only [Module.finrank_fin_fun] at h
  omega

theorem ker_eq_span_crossVec_self (M : Matrix (Fin m) (Fin (m + 1)) K) (hc : crossVec M ≠ 0) :
    LinearMap.ker M.mulVecLin = K ∙ crossVec M := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact mulVec_crossVec M
  · rw [finrank_span_singleton hc, finrank_ker_of_crossVec_ne_zero M hc]

/-- **Cramer's rule for the kernel line.** -/
theorem ker_eq_span_crossVec (M : Matrix (Fin p) (Fin (m + 1)) K) (r : Fin m → Fin p)
    (hc : crossVec (M.submatrix r id) ≠ 0) (hker : LinearMap.ker M.mulVecLin ≠ ⊥) :
    LinearMap.ker M.mulVecLin = K ∙ crossVec (M.submatrix r id) := by
  rw [← ker_eq_span_crossVec_self _ hc]
  have hle : LinearMap.ker M.mulVecLin ≤ LinearMap.ker (M.submatrix r id).mulVecLin := by
    intro v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    funext i
    have := congr_fun hv (r i)
    simpa [Matrix.mulVec, dotProduct] using this
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_ker_of_crossVec_ne_zero _ hc]
  have h1 : Module.finrank K (LinearMap.ker M.mulVecLin) ≤ 1 := by
    exact (Submodule.finrank_mono hle).trans (finrank_ker_of_crossVec_ne_zero _ hc).le
  have h2 : Module.finrank K (LinearMap.ker M.mulVecLin) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero]
    exact hker
  omega

end Field

section Block

variable {R : Type*} [CommRing R] {a N : ℕ}

/-- Block-triangular determinant: `det [Aα | Aα F + Z E] = det [Aα | Z] · det E`. -/
theorem det_fromCols_eq (Aα : Matrix (Fin a ⊕ Fin N) (Fin a) R) (Z V : Matrix (Fin a ⊕ Fin N) (Fin N) R)
    (F : Matrix (Fin a) (Fin N) R) (E : Matrix (Fin N) (Fin N) R) (hV : V = Aα * F + Z * E) :
    (Matrix.fromCols Aα V).det = (Matrix.fromCols Aα Z).det * E.det := by
  have h : Matrix.fromCols Aα V = Matrix.fromCols Aα Z * Matrix.fromBlocks 1 F 0 E := by
    rw [Matrix.fromCols_mul_fromBlocks, Matrix.mul_one, Matrix.mul_zero, add_zero, hV]
  rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

end Block

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_Pres =====
section

/-!
# S4-JacLaw, file O4b: the Δ-ratio presentation of `B ⧸ (s)`

`L' , L ⊆ B` finite-dimensional `k`-subspaces with `s • L' ⊆ L`, bases `α` of `L'` and `β` of `L`
(indexed by `Fin a ⊕ Fin N`), and `e : Fin N → L`. `presDet = Δ_1 = det_β [s α | e]`.
* `linIndep_mk_of_presDet`: if `L ∩ (s) = s L'` and `Δ_1 ≠ 0`, the images of `e` in `B ⧸ (s)` are independent.
* `presDet_ne_zero_of_linIndep`: conversely (`B` a domain, `s ≠ 0`), independence of the images gives `Δ_1 ≠ 0`.
* `det_pres_charpoly`: if `Δ_1 ≠ 0`, the images of `e` form a basis and `w e_i ∈ L`, then
  `det [s α | X e - w e] = Δ_1 · charpoly (mult. by w on B ⧸ (s))` (all columns in `β`-coordinates).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open Polynomial Module Matrix

section Pres

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
variable (s : B) {L L' : Submodule k B} (hsL : ∀ y ∈ L', s * y ∈ L)
variable {a N : ℕ} (α : Basis (Fin a) k L') (β : Basis (Fin a ⊕ Fin N) k L)
variable {e : Fin N → B} (he : ∀ i, e i ∈ L)

/-- The family `s α_b, e_i` in `L`. -/
noncomputable def presFam : Fin a ⊕ Fin N → L :=
  Sum.elim (fun b => ⟨s * α b, hsL _ (α b).2⟩) (fun i => ⟨e i, he i⟩)

/-- `Δ_1 = det_β [s α | e]`. -/
noncomputable def presDet : k := β.det (presFam s hsL α he)

theorem coe_presFam_sum (G : Fin a ⊕ Fin N → k) :
    ((∑ r, G r • presFam s hsL α he r : L) : B) =
      ∑ b, G (Sum.inl b) • (s * (α b : B)) + ∑ i, G (Sum.inr i) • e i := by
  rw [Fintype.sum_sum_type]
  simp [presFam]

theorem presDet_ne_zero_iff :
    presDet s hsL α β he ≠ 0 ↔ LinearIndependent k (presFam s hsL α he) := by
  have : FiniteDimensional k L := Module.Finite.of_basis β
  constructor
  · intro h
    exact (β.is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr h)).1
  · intro h
    have hsp := h.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis β).symm
    exact (β.is_basis_iff_det.mp ⟨h, hsp⟩).ne_zero

theorem linIndep_mk_of_presDet (hP : ∀ z ∈ L, z ∈ Ideal.span {s} → ∃ y ∈ L', z = s * y)
    (h : presDet s hsL α β he ≠ 0) :
    LinearIndependent k (fun i => Ideal.Quotient.mkₐ k (Ideal.span {s}) (e i)) := by
  have hli := (presDet_ne_zero_iff s hsL α β he).mp h
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro g hg
  have hz : (∑ i, g i • e i) ∈ Ideal.span {s} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk k, map_sum]
    simpa only [map_smul] using hg
  have hzL : (∑ i, g i • e i) ∈ L := Submodule.sum_mem _ fun i _ => L.smul_mem _ (he i)
  obtain ⟨y, hy, hyz⟩ := hP _ hzL hz
  set c := α.repr ⟨y, hy⟩
  have hyc : y = ∑ b, c b • (α b : B) := by
    have h2 := congrArg Subtype.val (α.sum_repr ⟨y, hy⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    exact h2.symm
  have key := hli (Sum.elim (fun b => -c b) g) (by
    apply Subtype.ext
    rw [coe_presFam_sum]
    simp only [Sum.elim_inl, Sum.elim_inr, ZeroMemClass.coe_zero]
    rw [hyz, hyc, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [mul_smul_comm, neg_smul, neg_add_cancel])
  intro i
  simpa using key (Sum.inr i)

theorem presDet_ne_zero_of_linIndep [IsDomain B] (hs : s ≠ 0)
    (h : LinearIndependent k (fun i => Ideal.Quotient.mkₐ k (Ideal.span {s}) (e i))) :
    presDet s hsL α β he ≠ 0 := by
  rw [presDet_ne_zero_iff, Fintype.linearIndependent_iff]
  rw [Fintype.linearIndependent_iff] at h
  intro G hG
  have hB := congrArg Subtype.val hG
  rw [coe_presFam_sum, ZeroMemClass.coe_zero] at hB
  have hmk := congrArg (Ideal.Quotient.mkₐ k (Ideal.span {s})) hB
  have hs0 : Ideal.Quotient.mkₐ k (Ideal.span {s}) s = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_span_singleton_self s
  simp only [map_add, map_sum, map_smul, map_mul, hs0, zero_mul, smul_zero, Finset.sum_const_zero, zero_add,
    map_zero] at hmk
  have hr := h _ hmk
  simp only [hr, zero_smul, Finset.sum_const_zero, add_zero] at hB
  have hl : ∑ b, G (Sum.inl b) • α b = 0 := by
    apply Subtype.ext
    have : s * ∑ b, G (Sum.inl b) • (α b : B) = 0 := by
      rw [Finset.mul_sum]; simpa only [mul_smul_comm] using hB
    simpa using (mul_eq_zero.mp this).resolve_left hs
  have hl' := (Fintype.linearIndependent_iff.mp α.linearIndependent) _ hl
  rintro (b | i)
  · exact hl' b
  · exact hr i

variable (w : B) (hw : ∀ i, w * e i ∈ L)

theorem det_pres_charpoly [Module.Finite k (B ⧸ Ideal.span {s})] (h : presDet s hsL α β he ≠ 0) (bC : Basis (Fin N) k (B ⧸ Ideal.span {s}))
    (hbC : ∀ i, bC i = Ideal.Quotient.mkₐ k (Ideal.span {s}) (e i)) :
    (fromCols ((β.toMatrix fun b => (⟨s * α b, hsL _ (α b).2⟩ : L)).map C)
      ((β.toMatrix fun i => (⟨e i, he i⟩ : L)).map C * scalar (Fin N) (X : k[X]) -
        (β.toMatrix fun i => (⟨w * e i, hw i⟩ : L)).map C)).det =
      C (presDet s hsL α β he) *
        LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {s}) (Ideal.Quotient.mkₐ k (Ideal.span {s}) w)) := by
  have : FiniteDimensional k L := Module.Finite.of_basis β
  have hli := (presDet_ne_zero_iff s hsL α β he).mp h
  set u := presFam s hsL α he
  let bu : Basis (Fin a ⊕ Fin N) k L :=
    Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis β).symm).ge
  have hbu : ⇑bu = u := Basis.coe_mk _ _
  set Aα := β.toMatrix fun b => (⟨s * α b, hsL _ (α b).2⟩ : L)
  set Zm := β.toMatrix fun i => (⟨e i, he i⟩ : L)
  set Wv : Fin N → L := fun i => ⟨w * e i, hw i⟩
  set G := bu.toMatrix Wv
  have hfc : β.toMatrix u = fromCols Aα Zm := by
    ext r (b | i) <;> simp [Basis.toMatrix_apply, u, presFam, Aα, Zm]
  have hW : β.toMatrix Wv = Aα * G.toRows₁ + Zm * G.toRows₂ := by
    rw [← fromCols_mul_fromRows, fromRows_toRows, ← hfc, ← hbu, β.toMatrix_mul_toMatrix]
  -- the matrix of multiplication by `w` on `B ⧸ (s)`
  have hs0 : Ideal.Quotient.mkₐ k (Ideal.span {s}) s = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_span_singleton_self s
  have hmat : LinearMap.toMatrix bC bC
      (Algebra.lmul k (B ⧸ Ideal.span {s}) (Ideal.Quotient.mkₐ k (Ideal.span {s}) w)) = G.toRows₂ := by
    ext j i
    rw [LinearMap.toMatrix_apply]
    have hsum := congrArg Subtype.val (bu.sum_repr (Wv i))
    rw [hbu] at hsum
    have hsum' : w * e i = ∑ b, G (Sum.inl b) i • (s * (α b : B)) + ∑ j, G (Sum.inr j) i • e j := by
      rw [← coe_presFam_sum s hsL α he (fun r => G r i)]
      simpa [G, Basis.toMatrix_apply, Wv] using hsum.symm
    have hq : Ideal.Quotient.mkₐ k (Ideal.span {s}) w * bC i = ∑ j, G.toRows₂ j i • bC j := by
      rw [hbC, ← map_mul, hsum']
      simp only [map_add, map_sum, map_smul, map_mul, hs0, zero_mul, smul_zero, Finset.sum_const_zero,
        zero_add, hbC, toRows₂_apply]
    change bC.repr (Ideal.Quotient.mkₐ k (Ideal.span {s}) w * bC i) j = _
    rw [hq, bC.repr_sum_self]
  have hcp : LinearMap.charpoly
      (Algebra.lmul k (B ⧸ Ideal.span {s}) (Ideal.Quotient.mkₐ k (Ideal.span {s}) w)) = G.toRows₂.charpoly := by
    rw [← LinearMap.charpoly_toMatrix _ bC, hmat]
  have hV : Zm.map C * scalar (Fin N) (X : k[X]) - (β.toMatrix Wv).map C =
      Aα.map C * -(G.toRows₁.map C) + Zm.map C * charmatrix G.toRows₂ := by
    rw [hW, Matrix.map_add _ (map_add C), Matrix.map_mul, Matrix.map_mul, charmatrix, RingHom.mapMatrix_apply, Matrix.mul_sub,
      Matrix.mul_neg]
    abel
  rw [hV, det_fromCols_eq _ _ _ _ _ rfl, hcp, Matrix.charpoly, ← fromCols_map, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, ← hfc, ← Basis.det_apply]
  rfl

end Pres

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_Fam =====
section

/-!
# S4-JacLaw, file O6b: the Δ-ratio presentation in families

`c : Fin n → S` (coefficients in a `k`-algebra `S`, e.g. the kernel vector in `S_d`) and `h : Fin n → B`
give at each `k`-point `x` of `S` the section `secAt c h x = Σ_l x(c_l) h_l`. With `h_l L' ⊆ L` the
presentation matrices of `O4b` (`Pres`) become matrices over `S` (`famPres`, `famDet`), polynomial in `c`,
whose values at `x` are `presDet` and the `Δ_{X - w}` determinant at `secAt c h x` (`map_famPres`,
`map_famDet`); with `det_pres_charpoly` this is `C presDet * charpoly` (`map_famDet_eq`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open Polynomial Module Matrix

section Fam

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {n : ℕ} (c : Fin n → S) (h : Fin n → B)

/-- The section `Σ_l x(c_l) h_l` at the point `x`. -/
noncomputable def secAt (x : S →ₐ[k] k) : B := ∑ l, x (c l) • h l

variable {L L' : Submodule k B} (hhL : ∀ l, ∀ y ∈ L', h l * y ∈ L)

include hhL in
theorem secAt_mul_mem (x : S →ₐ[k] k) : ∀ y ∈ L', secAt c h x * y ∈ L := by
  intro y hy
  simp only [secAt, Finset.sum_mul, smul_mul_assoc]
  exact Submodule.sum_mem _ fun l _ => L.smul_mem _ (hhL l y hy)

variable {a N : ℕ} (α : Basis (Fin a) k L') (β : Basis (Fin a ⊕ Fin N) k L)
variable {e : Fin N → B} (he : ∀ i, e i ∈ L)

/-- The block `[s α]` with entries in `S`. -/
noncomputable def famBlock : Matrix (Fin a ⊕ Fin N) (Fin a) S :=
  Matrix.of fun r b => ∑ l, c l * algebraMap k S (β.repr ⟨h l * α b, hhL l _ (α b).2⟩ r)

theorem map_famBlock (x : S →ₐ[k] k) :
    (famBlock c h hhL α β).map x =
      β.toMatrix fun b => (⟨secAt c h x * α b, secAt_mul_mem c h hhL x _ (α b).2⟩ : L) := by
  ext r b
  have hsum : (⟨secAt c h x * α b, secAt_mul_mem c h hhL x _ (α b).2⟩ : L) =
      ∑ l, x (c l) • (⟨h l * α b, hhL l _ (α b).2⟩ : L) := by
    apply Subtype.ext
    simp [secAt, Finset.sum_mul, smul_mul_assoc]
  rw [Basis.toMatrix_apply, hsum, map_sum]
  simp only [famBlock, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]

/-- `Δ_1` in the family. -/
noncomputable def famPres : S :=
  (fromCols (famBlock c h hhL α β) ((β.toMatrix fun i => (⟨e i, he i⟩ : L)).map (algebraMap k S))).det

theorem map_famPres (x : S →ₐ[k] k) :
    x (famPres c h hhL α β he) = presDet (secAt c h x) (secAt_mul_mem c h hhL x) α β he := by
  rw [presDet, Basis.det_apply, famPres, AlgHom.map_det]
  congr 1
  ext r (b | i)
  · have := congr_fun (congr_fun (map_famBlock c h hhL α β x) r) b
    simp only [Matrix.map_apply] at this
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, fromCols_apply_inl, this,
      Basis.toMatrix_apply, presFam, Sum.elim_inl]
  · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, fromCols_apply_inr, Basis.toMatrix_apply,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, presFam, Sum.elim_inr]

variable (w : B) (hw : ∀ i, w * e i ∈ L)

/-- `Δ_{X - w}` in the family, a polynomial over `S`. -/
noncomputable def famDet : S[X] :=
  (fromCols ((famBlock c h hhL α β).map C)
    (((β.toMatrix fun i => (⟨e i, he i⟩ : L)).map C * scalar (Fin N) (X : k[X]) -
      (β.toMatrix fun i => (⟨w * e i, hw i⟩ : L)).map C).map (Polynomial.map (algebraMap k S)))).det

theorem map_famDet (x : S →ₐ[k] k) :
    (famDet c h hhL α β he w hw).map x.toRingHom =
      (fromCols ((β.toMatrix fun b => (⟨secAt c h x * α b, secAt_mul_mem c h hhL x _ (α b).2⟩ : L)).map C)
        ((β.toMatrix fun i => (⟨e i, he i⟩ : L)).map C * scalar (Fin N) (X : k[X]) -
          (β.toMatrix fun i => (⟨w * e i, hw i⟩ : L)).map C)).det := by
  rw [famDet, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext r (b | i)
  · have := congr_fun (congr_fun (map_famBlock c h hhL α β x) r) b
    simp only [Matrix.map_apply] at this
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, fromCols_apply_inl, Polynomial.coe_mapRingHom,
      Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, this]
  · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, fromCols_apply_inr, Polynomial.coe_mapRingHom,
      Polynomial.map_map]
    have hx : (x : S →+* k).comp (algebraMap k S) = RingHom.id k := by
      ext t; simp
    rw [AlgHom.toRingHom_eq_coe, hx, Polynomial.map_id]

theorem map_famDet_eq (x : S →ₐ[k] k) [Module.Finite k (B ⧸ Ideal.span {secAt c h x})]
    (hP : presDet (secAt c h x) (secAt_mul_mem c h hhL x) α β he ≠ 0)
    (bC : Basis (Fin N) k (B ⧸ Ideal.span {secAt c h x}))
    (hbC : ∀ i, bC i = Ideal.Quotient.mkₐ k (Ideal.span {secAt c h x}) (e i)) :
    (famDet c h hhL α β he w hw).map x.toRingHom =
      C (x (famPres c h hhL α β he)) * LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {secAt c h x})
        (Ideal.Quotient.mkₐ k (Ideal.span {secAt c h x}) w)) := by
  rw [map_famDet, map_famPres]
  exact det_pres_charpoly (secAt c h x) (secAt_mul_mem c h hhL x) α β he w hw hP bC hbC

end Fam

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_Diag =====
section

/-!
# S4-JacLaw, file O4a: diagonalising a finite commutative algebra by one element

`C` a commutative `k`-algebra of finite dimension `N`, `w : C`, and `N` eigenvectors `v i` of multiplication by `w`
with pairwise distinct eigenvalues `lam i`. Then `v` is a basis (`eigBasis`), every `c : C` acts diagonally
(`mul_eigen : c * v j = eigChar j c • v j`), the `eigChar j : C →ₐ[k] k` are the only `k`-points of `C`
(`exists_eq_eigChar`), they separate elements (`eq_zero_of_eigChar`), and
`charpoly (lmul c) = ∏ j, (X - C (eigChar j c))` (`charpoly_lmul_eq`).
`exists_eigen_of_separable`: over an algebraically closed field a separable `charpoly (lmul w)` gives such data,
indexed by its roots. `prod_divByMonic_image`: exact division of products of linear factors.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open Polynomial Module

section Diag

variable {k : Type*} [Field k] {C : Type*} [CommRing C] [Algebra k C] [FiniteDimensional k C]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {w : C} {lam : ι → k} {v : ι → C} (hlam : Function.Injective lam) (hv : ∀ i, v i ≠ 0)
  (hwv : ∀ i, w * v i = lam i • v i) (hcard : Fintype.card ι = finrank k C)

omit [FiniteDimensional k C] [Fintype ι] [DecidableEq ι] in
include hlam hv hwv in
theorem linearIndependent_eigen : LinearIndependent k v :=
  Module.End.eigenvectors_linearIndependent' (Algebra.lmul k C w) lam hlam v fun i =>
    ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using hwv i), hv i⟩

/-- The eigenvector basis. -/
noncomputable def eigBasis : Basis ι k C :=
  Basis.mk (linearIndependent_eigen hlam hv hwv)
    ((linearIndependent_eigen hlam hv hwv).span_eq_top_of_card_eq_finrank' hcard).ge

omit [DecidableEq ι] in
@[simp] theorem coe_eigBasis : ⇑(eigBasis hlam hv hwv hcard) = v := Basis.coe_mk _ _

theorem repr_v (j : ι) : (eigBasis hlam hv hwv hcard).repr (v j) = Finsupp.single j 1 := by
  have h := (eigBasis hlam hv hwv hcard).repr_self j
  rwa [coe_eigBasis] at h

include hlam hv hwv hcard in
theorem mul_w_eq (y : C) :
    w * y = ∑ i, (lam i * (eigBasis hlam hv hwv hcard).repr y i) • v i := by
  conv_lhs => rw [← (eigBasis hlam hv hwv hcard).sum_repr y]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_eigBasis, mul_smul_comm, hwv i, smul_smul, mul_comm]

include hlam hv hwv hcard in
theorem repr_mul_w (y : C) (i : ι) :
    (eigBasis hlam hv hwv hcard).repr (w * y) i = lam i * (eigBasis hlam hv hwv hcard).repr y i := by
  have h := (eigBasis hlam hv hwv hcard).repr_sum_self (fun i => lam i * (eigBasis hlam hv hwv hcard).repr y i)
  rw [coe_eigBasis, ← mul_w_eq hlam hv hwv hcard] at h
  exact congrFun h i

include hlam hv hwv hcard in
theorem mul_eigen_aux (c : C) (j : ι) :
    c * v j = (eigBasis hlam hv hwv hcard).repr (c * v j) j • v j := by
  set b := eigBasis hlam hv hwv hcard
  have hx : w * (c * v j) = lam j • (c * v j) := by
    rw [mul_left_comm, hwv j, mul_smul_comm]
  have hz : ∀ i, i ≠ j → b.repr (c * v j) i = 0 := by
    intro i hij
    have := repr_mul_w hlam hv hwv hcard (c * v j) i
    rw [hx, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
    have h2 : (lam i - lam j) * b.repr (c * v j) i = 0 := by rw [sub_mul, ← this, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr fun h => hij (hlam h))
  conv_lhs => rw [← b.sum_repr (c * v j)]
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [hz i hij, zero_smul]) (by simp), coe_eigBasis]

/-- The `k`-point of `C` given by the eigenline `k v j`. -/
noncomputable def eigChar (j : ι) : C →ₐ[k] k :=
  AlgHom.ofLinearMap
    ((Finsupp.lapply j).comp (((eigBasis hlam hv hwv hcard).repr : C →ₗ[k] ι →₀ k).comp
      (LinearMap.mulRight k (v j))))
    (by
      change (eigBasis hlam hv hwv hcard).repr (1 * v j) j = 1
      rw [one_mul, repr_v, Finsupp.single_eq_same])
    (by
      intro c c'
      change (eigBasis hlam hv hwv hcard).repr (c * c' * v j) j =
        (eigBasis hlam hv hwv hcard).repr (c * v j) j * (eigBasis hlam hv hwv hcard).repr (c' * v j) j
      set a := (eigBasis hlam hv hwv hcard).repr (c' * v j) j
      have h : c' * v j = a • v j := mul_eigen_aux hlam hv hwv hcard c' j
      rw [mul_assoc, h, mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm])

theorem eigChar_apply (j : ι) (c : C) :
    eigChar hlam hv hwv hcard j c = (eigBasis hlam hv hwv hcard).repr (c * v j) j := rfl

theorem mul_eigen (c : C) (j : ι) : c * v j = eigChar hlam hv hwv hcard j c • v j :=
  mul_eigen_aux hlam hv hwv hcard c j

theorem eigChar_w (j : ι) : eigChar hlam hv hwv hcard j w = lam j := by
  have h := mul_eigen hlam hv hwv hcard w j
  rw [hwv j] at h
  exact (smul_left_injective k (hv j) h).symm

theorem eigChar_injective : Function.Injective (eigChar hlam hv hwv hcard) := by
  intro i j h
  apply hlam
  rw [← eigChar_w hlam hv hwv hcard i, ← eigChar_w hlam hv hwv hcard j, h]

theorem eq_zero_of_eigChar (c : C) (h : ∀ j, eigChar hlam hv hwv hcard j c = 0) : c = 0 := by
  set b := eigBasis hlam hv hwv hcard
  have h1 : c = c * 1 := (mul_one c).symm
  rw [h1, ← b.sum_repr 1, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coe_eigBasis, mul_smul_comm, mul_eigen hlam hv hwv hcard c j, h j, zero_smul, smul_zero]

theorem exists_eq_eigChar (φ : C →ₐ[k] k) : ∃ j, φ = eigChar hlam hv hwv hcard j := by
  set b := eigBasis hlam hv hwv hcard
  have h1 : ∑ i, b.repr 1 i * φ (v i) = 1 := by
    have h0 : φ 1 = ∑ i, b.repr 1 i * φ (v i) := by
      conv_lhs => rw [← b.sum_repr 1]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, coe_eigBasis, smul_eq_mul]
    rw [← h0, map_one]
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1 ▸ one_ne_zero : ∑ i, b.repr 1 i * φ (v i) ≠ 0)
  have hφj : φ (v j) ≠ 0 := right_ne_zero_of_mul hj
  refine ⟨j, AlgHom.ext fun c => ?_⟩
  have := congrArg φ (mul_eigen hlam hv hwv hcard c j)
  rw [map_mul, map_smul, smul_eq_mul] at this
  exact mul_right_cancel₀ hφj this

theorem toMatrix_lmul_eq (c : C) :
    LinearMap.toMatrix (eigBasis hlam hv hwv hcard) (eigBasis hlam hv hwv hcard) (Algebra.lmul k C c) =
      Matrix.diagonal fun j => eigChar hlam hv hwv hcard j c := by
  ext i j
  rw [LinearMap.toMatrix_apply, coe_eigBasis]
  change (eigBasis hlam hv hwv hcard).repr (c * v j) i = _
  rw [mul_eigen hlam hv hwv hcard c j, map_smul, repr_v, Finsupp.smul_apply, Matrix.diagonal_apply,
    Finsupp.single_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem charpoly_lmul_eq (c : C) :
    LinearMap.charpoly (Algebra.lmul k C c) = ∏ j, (X - Polynomial.C (eigChar hlam hv hwv hcard j c)) := by
  rw [← LinearMap.charpoly_toMatrix (Algebra.lmul k C c) (eigBasis hlam hv hwv hcard), toMatrix_lmul_eq,
    Matrix.charpoly_diagonal]

end Diag

section Sep

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] {C : Type*} [CommRing C] [Algebra k C] [FiniteDimensional k C]

/-- Eigen-data from a separable characteristic polynomial, indexed by its roots. -/
theorem exists_eigen_of_separable (w : C) (hsep : (LinearMap.charpoly (Algebra.lmul k C w)).Separable) :
    ∃ v : (LinearMap.charpoly (Algebra.lmul k C w)).roots.toFinset → C,
      (∀ μ, v μ ≠ 0) ∧ (∀ μ, w * v μ = (μ : k) • v μ) ∧
      Fintype.card (LinearMap.charpoly (Algebra.lmul k C w)).roots.toFinset = finrank k C := by
  set p := LinearMap.charpoly (Algebra.lmul k C w)
  have hex : ∀ μ : p.roots.toFinset, ∃ x : C, x ≠ 0 ∧ w * x = (μ : k) • x := by
    intro μ
    have hr : p.IsRoot μ := by
      have := μ.2
      rw [Multiset.mem_toFinset, mem_roots (LinearMap.charpoly_monic _).ne_zero] at this
      exact this
    obtain ⟨x, hx⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hr).exists_hasEigenvector
    exact ⟨x, hx.2, by simpa using Module.End.mem_eigenspace_iff.mp hx.1⟩
  choose v hv0 hv using hex
  refine ⟨v, hv0, hv, ?_⟩
  rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
    LinearMap.charpoly_natDegree]

end Sep

/-- Exact division of a product of linear factors by a sub-product. -/
theorem prod_divByMonic_image {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (a : κ → R) :
    (∏ μ, (X - Polynomial.C (a μ))) /ₘ (∏ i, (X - Polynomial.C (a (f i)))) =
      ∏ μ ∈ (Finset.univ.image f)ᶜ, (X - Polynomial.C (a μ)) := by
  have hprod : ∏ i, (X - Polynomial.C (a (f i))) = ∏ μ ∈ Finset.univ.image f, (X - Polynomial.C (a μ)) := by
    rw [Finset.prod_image fun x _ y _ h => hf h]
  rw [hprod, ← Finset.prod_mul_prod_compl (Finset.univ.image f)]
  exact mul_divByMonic_cancel_left _ (monic_prod_of_monic _ _ fun μ _ => monic_X_sub_C (a μ))

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacChunkA_Pts =====
section

/-!
# Group chunk A0 (unit S4-JacChunkA): closed points over an algebraically closed field

For `k` algebraically closed and `k`-schemes locally of finite type:
* `isClosed_singleton_apply`: `k`-morphisms send closed points to closed points;
* `exists_closedPoint_pullback`, `closedPoint_pullback_ext`: closed points of `X ×_k Y` are exactly the pairs of
  closed points;
* `opens_le_of_closedPoints`, `opens_eq_of_closedPoints`: opens of a Jacobson scheme are determined by closed points.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- `k`-morphisms between `k`-schemes locally of finite type send closed points to closed points. -/
lemma isClosed_singleton_apply {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (x : X) (hx : IsClosed {x}) : IsClosed {f x} := by
  have h1 : (pointOfClosedPoint sX x hx ≫ f) ≫ sY = 𝟙 _ := by
    rw [Category.assoc, hf, pointOfClosedPoint_comp]
  have h2 := ((pointEquivClosedPoint sY) ⟨_, h1⟩).2
  have h3 : (pointOfClosedPoint sX x hx ≫ f) (IsLocalRing.closedPoint k) = f x := by
    exact congrArg f (pointOfClosedPoint_apply sX x hx _)
  rw [← h3]; exact h2

/-- Every pair of closed points of `X`, `Y` comes from a closed point of `X ×_k Y`. -/
lemma exists_closedPoint_pullback {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] (x : X) (hx : IsClosed {x}) (y : Y)
    (hy : IsClosed {y}) :
    ∃ z : (pullback sX sY : Scheme.{u}), IsClosed {z} ∧ pullback.fst sX sY z = x ∧
      pullback.snd sX sY z = y := by
  obtain ⟨r, hr1, hr2⟩ : ∃ r : Spec (.of k) ⟶ pullback sX sY,
      r ≫ pullback.fst sX sY = pointOfClosedPoint sX x hx ∧
      r ≫ pullback.snd sX sY = pointOfClosedPoint sY y hy :=
    ⟨pullback.lift _ _ (by simp), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hr : r ≫ (pullback.fst sX sY ≫ sX) = 𝟙 _ := by
    rw [← Category.assoc, hr1, pointOfClosedPoint_comp]
  refine ⟨r (IsLocalRing.closedPoint k), ?_, ?_, ?_⟩
  · exact ((pointEquivClosedPoint (pullback.fst sX sY ≫ sX)) ⟨r, hr⟩).2
  · calc (pullback.fst sX sY) (r (IsLocalRing.closedPoint k))
        = (r ≫ pullback.fst sX sY) (IsLocalRing.closedPoint k) := rfl
      _ = pointOfClosedPoint sX x hx (IsLocalRing.closedPoint k) := by rw [hr1]
      _ = x := pointOfClosedPoint_apply sX x hx _
  · calc (pullback.snd sX sY) (r (IsLocalRing.closedPoint k))
        = (r ≫ pullback.snd sX sY) (IsLocalRing.closedPoint k) := rfl
      _ = pointOfClosedPoint sY y hy (IsLocalRing.closedPoint k) := by rw [hr2]
      _ = y := pointOfClosedPoint_apply sY y hy _

/-- Two closed points of `X ×_k Y` with the same projections are equal. -/
lemma closedPoint_pullback_ext {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] (z z' : (pullback sX sY : Scheme.{u}))
    (hz : IsClosed {z}) (hz' : IsClosed {z'})
    (h1 : pullback.fst sX sY z = pullback.fst sX sY z')
    (h2 : pullback.snd sX sY z = pullback.snd sX sY z') : z = z' := by
  obtain ⟨r, hr, hrz⟩ : ∃ r : Spec (.of k) ⟶ pullback sX sY,
      r ≫ (pullback.fst sX sY ≫ sX) = 𝟙 _ ∧ r (IsLocalRing.closedPoint k) = z :=
    ⟨_, pointOfClosedPoint_comp _ z hz, pointOfClosedPoint_apply _ z hz _⟩
  obtain ⟨r', hr', hrz'⟩ : ∃ r : Spec (.of k) ⟶ pullback sX sY,
      r ≫ (pullback.fst sX sY ≫ sX) = 𝟙 _ ∧ r (IsLocalRing.closedPoint k) = z' :=
    ⟨_, pointOfClosedPoint_comp _ z' hz', pointOfClosedPoint_apply _ z' hz' _⟩
  have hs : pullback.snd sX sY ≫ sY = pullback.fst sX sY ≫ sX := pullback.condition.symm
  have e : r = r' := by
    apply pullback.hom_ext
    · refine ext_of_apply_closedPoint_eq sX ?_ ?_ ?_
      · rw [Category.assoc, hr]
      · rw [Category.assoc, hr']
      · exact (congrArg (pullback.fst sX sY) hrz).trans (h1.trans (congrArg _ hrz').symm)
    · refine ext_of_apply_closedPoint_eq sY ?_ ?_ ?_
      · rw [Category.assoc, hs, hr]
      · rw [Category.assoc, hs, hr']
      · exact (congrArg (pullback.snd sX sY) hrz).trans (h2.trans (congrArg _ hrz').symm)
  rw [← hrz, ← hrz', e]

/-- In a Jacobson space, an open set is contained in another one as soon as its closed points are. -/
lemma opens_le_of_closedPoints {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    (U V : TopologicalSpace.Opens X) (h : ∀ x ∈ U, IsClosed ({x} : Set X) → x ∈ V) : U ≤ V := by
  intro x hx
  by_contra hxV
  obtain ⟨y, ⟨hyU, hyV⟩, hy⟩ := nonempty_inter_closedPoints (Z := (U : Set X) ∩ (V : Set X)ᶜ)
    ⟨x, hx, hxV⟩ (U.2.isLocallyClosed.inter V.2.isClosed_compl.isLocallyClosed)
  exact hyV (h y hyU hy)

lemma opens_eq_of_closedPoints {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    (U V : TopologicalSpace.Opens X)
    (h : ∀ x, IsClosed ({x} : Set X) → (x ∈ U ↔ x ∈ V)) : U = V :=
  le_antisymm (opens_le_of_closedPoints U V fun x hx hc => (h x hc).1 hx)
    (opens_le_of_closedPoints V U fun x hx hc => (h x hc).2 hx)

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkA_Trans =====
section

/-!
# Group chunk A1 (unit S4-JacChunkA): translations of a strict group chunk

* `TransData`: a generic "translation" situation: an open `Ω ⊆ P`, an open immersion `Φ : Ω ⟶ P`, a law
  `m : Ω ⟶ X`, a section `i : X ⟶ P` of a projection `π : P ⟶ X`, with `Φ` moving points of `i(X)` inside
  `i(X)` by `m`. It yields the isomorphism `trIso : i⁻¹Ω ≅ i⁻¹(range Φ)` (all identities exact, no points).
* `StrictChunk sX`: a strict group chunk on a `k`-scheme `X` (structure map `sX`).
* `StrictChunk.lam`, `StrictChunk.rho`: the left and right translations `λ_a`, `ρ_b` by closed points, as
  `Scheme.PartialIso X X` over `Spec k`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

/-- Lift a morphism landing (pointwise) in an open subscheme to that open subscheme. -/
noncomputable def liftO {T Z : Scheme.{u}} (U : Z.Opens) (f : T ⟶ Z) (h : ∀ x, f x ∈ U) :
    T ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι f (by rw [Scheme.Opens.range_ι]; rintro _ ⟨x, rfl⟩; exact h x)

@[reassoc (attr := simp)]
lemma liftO_ι {T Z : Scheme.{u}} (U : Z.Opens) (f : T ⟶ Z) (h : ∀ x, f x ∈ U) :
    liftO U f h ≫ U.ι = f :=
  IsOpenImmersion.lift_fac _ _ _

/-- Generic translation data (see the module docstring). -/
structure TransData {X P : Scheme.{u}} (Ω : P.Opens) (Φ : Ω.toScheme ⟶ P) (m : Ω.toScheme ⟶ X)
    (i : X ⟶ P) (π : P ⟶ X) : Prop where
  sec : i ≫ π = 𝟙 X
  comp : Φ ≫ π = m
  fwd : ∀ {T : Scheme.{u}} (g : T ⟶ Ω.toScheme) (t : T ⟶ X), g ≫ Ω.ι = t ≫ i → g ≫ Φ = g ≫ m ≫ i
  bwd : ∀ {T : Scheme.{u}} (h : T ⟶ Ω.toScheme) (t : T ⟶ X), h ≫ Φ = t ≫ i →
    h ≫ Ω.ι = (h ≫ Ω.ι ≫ π) ≫ i

section Generic

variable {X P : Scheme.{u}} {Ω : P.Opens} {Φ : Ω.toScheme ⟶ P} [IsOpenImmersion Φ]
  {m : Ω.toScheme ⟶ X} {i : X ⟶ P} {π : P ⟶ X}

/-- `i` restricted to `i⁻¹Ω`, as a map into `Ω`. -/
noncomputable def trR {X P : Scheme.{u}} (i : X ⟶ P) (Ω : P.Opens) :
    (i ⁻¹ᵁ Ω).toScheme ⟶ Ω.toScheme :=
  i.resLE Ω (i ⁻¹ᵁ Ω) le_rfl

@[reassoc (attr := simp)]
lemma trR_ι {X P : Scheme.{u}} (i : X ⟶ P) (Ω : P.Opens) : trR i Ω ≫ Ω.ι = (i ⁻¹ᵁ Ω).ι ≫ i :=
  Scheme.Hom.resLE_comp_ι _ _

lemma trR_apply {X P : Scheme.{u}} (i : X ⟶ P) (Ω : P.Opens) (x : (i ⁻¹ᵁ Ω)) :
    Ω.ι (trR i Ω x) = i x.1 :=
  congrArg (fun f => f x) (trR_ι i Ω)

/-- `Φ⁻¹ ∘ i` on `i⁻¹(range Φ)`. -/
noncomputable def trS {X P : Scheme.{u}} {Ω : P.Opens} (i : X ⟶ P) (Φ : Ω.toScheme ⟶ P)
    [IsOpenImmersion Φ] : (i ⁻¹ᵁ Φ.opensRange).toScheme ⟶ Ω.toScheme :=
  IsOpenImmersion.lift Φ ((i ⁻¹ᵁ Φ.opensRange).ι ≫ i) (by
    rintro _ ⟨x, rfl⟩
    exact x.2)

@[reassoc (attr := simp)]
lemma trS_Φ {X P : Scheme.{u}} {Ω : P.Opens} (i : X ⟶ P) (Φ : Ω.toScheme ⟶ P)
    [IsOpenImmersion Φ] : trS i Φ ≫ Φ = (i ⁻¹ᵁ Φ.opensRange).ι ≫ i :=
  IsOpenImmersion.lift_fac _ _ _

lemma TransData.fwd_i (H : TransData Ω Φ m i π) : trR i Ω ≫ m ≫ i = trR i Ω ≫ Φ :=
  (H.fwd (trR i Ω) (i ⁻¹ᵁ Ω).ι (trR_ι i Ω)).symm

lemma TransData.bwd_i (H : TransData Ω Φ m i π) :
    trS i Φ ≫ Ω.ι ≫ π ≫ i = trS i Φ ≫ Ω.ι := by
  have := (H.bwd (trS i Φ) (i ⁻¹ᵁ Φ.opensRange).ι (trS_Φ i Φ)).symm
  simpa only [Category.assoc] using this

/-- The forward translation `i⁻¹Ω ⟶ i⁻¹(range Φ)`, `x ↦ m(i x)`. -/
noncomputable def TransData.fwdHom (H : TransData Ω Φ m i π) :
    (i ⁻¹ᵁ Ω).toScheme ⟶ (i ⁻¹ᵁ Φ.opensRange).toScheme :=
  liftO _ (trR i Ω ≫ m) (fun x => by
    have e := congrArg (fun f => f x) H.fwd_i
    exact (Scheme.Hom.mem_preimage _).2 (Scheme.Hom.mem_opensRange.2 ⟨trR i Ω x, e.symm⟩))

/-- The backward translation `i⁻¹(range Φ) ⟶ i⁻¹Ω`, `y ↦ π(Φ⁻¹(i y))`. -/
noncomputable def TransData.bwdHom (H : TransData Ω Φ m i π) :
    (i ⁻¹ᵁ Φ.opensRange).toScheme ⟶ (i ⁻¹ᵁ Ω).toScheme :=
  liftO _ (trS i Φ ≫ Ω.ι ≫ π) (fun x => by
    have e := congrArg (fun f => f x) H.bwd_i
    have e' : i ((trS i Φ ≫ Ω.ι ≫ π) x) = Ω.ι (trS i Φ x) := e
    refine (Scheme.Hom.mem_preimage _).2 ?_
    rw [e']
    exact (trS i Φ x).2)

@[reassoc (attr := simp)]
lemma TransData.fwdHom_ι (H : TransData Ω Φ m i π) :
    H.fwdHom ≫ (i ⁻¹ᵁ Φ.opensRange).ι = trR i Ω ≫ m := liftO_ι _ _ _

@[reassoc (attr := simp)]
lemma TransData.bwdHom_ι (H : TransData Ω Φ m i π) :
    H.bwdHom ≫ (i ⁻¹ᵁ Ω).ι = trS i Φ ≫ Ω.ι ≫ π := liftO_ι _ _ _

lemma TransData.fwdHom_trS (H : TransData Ω Φ m i π) : H.fwdHom ≫ trS i Φ = trR i Ω := by
  rw [← cancel_mono Φ]
  simp only [Category.assoc, trS_Φ, H.fwdHom_ι_assoc, H.fwd_i]

lemma TransData.bwdHom_trR (H : TransData Ω Φ m i π) : H.bwdHom ≫ trR i Ω = trS i Φ := by
  rw [← cancel_mono Ω.ι]
  simp only [Category.assoc, trR_ι, H.bwdHom_ι_assoc, H.bwd_i]

/-- The translation isomorphism `i⁻¹Ω ≅ i⁻¹(range Φ)`. -/
noncomputable def TransData.iso (H : TransData Ω Φ m i π) :
    (i ⁻¹ᵁ Ω).toScheme ≅ (i ⁻¹ᵁ Φ.opensRange).toScheme where
  hom := H.fwdHom
  inv := H.bwdHom
  hom_inv_id := by
    rw [← cancel_mono (i ⁻¹ᵁ Ω).ι, Category.assoc, H.bwdHom_ι, Category.id_comp,
      ← Category.assoc, H.fwdHom_trS, trR_ι_assoc, H.sec, Category.comp_id]
  inv_hom_id := by
    rw [← cancel_mono (i ⁻¹ᵁ Φ.opensRange).ι, Category.assoc, H.fwdHom_ι, Category.id_comp,
      ← Category.assoc, H.bwdHom_trR, ← H.comp, trS_Φ_assoc, H.sec, Category.comp_id]

/-- The translation as a partial isomorphism of `X` (needs `i⁻¹Ω` nonempty and `X` irreducible). -/
noncomputable def TransData.partialIso [IrreducibleSpace X] (H : TransData Ω Φ m i π)
    (hne : ((i ⁻¹ᵁ Ω : X.Opens) : Set X).Nonempty) : X.PartialIso X where
  source := i ⁻¹ᵁ Ω
  dense_source := (i ⁻¹ᵁ Ω).isOpen.dense hne
  target := i ⁻¹ᵁ Φ.opensRange
  dense_target := (i ⁻¹ᵁ Φ.opensRange).isOpen.dense (by
    obtain ⟨x, hx⟩ := hne
    exact ⟨_, (H.fwdHom (⟨x, hx⟩ : (i ⁻¹ᵁ Ω))).2⟩)
  iso := H.iso

lemma TransData.partialIso_hom [IrreducibleSpace X] (H : TransData Ω Φ m i π)
    (hne : ((i ⁻¹ᵁ Ω : X.Opens) : Set X).Nonempty) :
    (H.partialIso hne).toPartialMap.hom = trR i Ω ≫ m :=
  H.fwdHom_ι

lemma TransData.partialIso_isOver [IrreducibleSpace X] (H : TransData Ω Φ m i π)
    (hne : ((i ⁻¹ᵁ Ω : X.Opens) : Set X).Nonempty) {S : Scheme.{u}} (sX : X ⟶ S)
    (hover : m ≫ sX = Ω.ι ≫ π ≫ sX) : (H.partialIso hne).IsOver sX sX := by
  change H.fwdHom ≫ (i ⁻¹ᵁ Φ.opensRange).ι ≫ sX = (i ⁻¹ᵁ Ω).ι ≫ sX
  rw [H.fwdHom_ι_assoc, hover, trR_ι_assoc, reassoc_of% H.sec]

end Generic

section Chunk

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A strict group chunk on a `k`-scheme `X` with structure map `sX`: a law `m : Ω ⟶ X` on an open
`Ω ⊆ X ×_k X` such that `(x, y) ↦ (x, xy)` and `(x, y) ↦ (xy, y)` are open immersions `Φ`, `Ψ`, every closed
point occurs as a first and as a second coordinate of a closed point of `Ω`, and `m` is associative on closed
points: `m(m(a,b),c) = m(a,m(b,c))` whenever all four pairs are closed points of `Ω`. -/
structure StrictChunk {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) where
  Ω : (pullback sX sX).Opens
  m : Ω.toScheme ⟶ X
  Φ : Ω.toScheme ⟶ pullback sX sX
  Φ_fst : Φ ≫ pullback.fst sX sX = Ω.ι ≫ pullback.fst sX sX
  Φ_snd : Φ ≫ pullback.snd sX sX = m
  isOpenImmersion_Φ : IsOpenImmersion Φ
  Ψ : Ω.toScheme ⟶ pullback sX sX
  Ψ_fst : Ψ ≫ pullback.fst sX sX = m
  Ψ_snd : Ψ ≫ pullback.snd sX sX = Ω.ι ≫ pullback.snd sX sX
  isOpenImmersion_Ψ : IsOpenImmersion Ψ
  fib_left : ∀ a : X, IsClosed ({a} : Set X) →
    ∃ z ∈ Ω, IsClosed ({z} : Set (pullback sX sX : Scheme.{u})) ∧ pullback.fst sX sX z = a
  fib_right : ∀ b : X, IsClosed ({b} : Set X) →
    ∃ z ∈ Ω, IsClosed ({z} : Set (pullback sX sX : Scheme.{u})) ∧ pullback.snd sX sX z = b
  assoc : ∀ z₁ z₂ z₃ z₄ : Ω, IsClosed {z₁.1} → IsClosed {z₂.1} → IsClosed {z₃.1} → IsClosed {z₄.1} →
    pullback.snd sX sX z₁.1 = pullback.fst sX sX z₂.1 →
    pullback.fst sX sX z₃.1 = m z₁ → pullback.snd sX sX z₃.1 = pullback.snd sX sX z₂.1 →
    pullback.fst sX sX z₄.1 = pullback.fst sX sX z₁.1 → pullback.snd sX sX z₄.1 = m z₂ →
    m z₃ = m z₄

attribute [instance] StrictChunk.isOpenImmersion_Φ StrictChunk.isOpenImmersion_Ψ
attribute [reassoc] StrictChunk.Φ_fst StrictChunk.Φ_snd StrictChunk.Ψ_fst StrictChunk.Ψ_snd

variable {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX]

/-- The section `x ↦ (a, x)` of the second projection. -/
noncomputable def secL (a : X) (ha : IsClosed {a}) : X ⟶ pullback sX sX :=
  pullback.lift (sX ≫ pointOfClosedPoint sX a ha) (𝟙 X) (by simp)

/-- The section `x ↦ (x, b)` of the first projection. -/
noncomputable def secR (b : X) (hb : IsClosed {b}) : X ⟶ pullback sX sX :=
  pullback.lift (𝟙 X) (sX ≫ pointOfClosedPoint sX b hb) (by simp)

@[reassoc (attr := simp)] lemma secL_fst (a : X) (ha : IsClosed {a}) :
    secL a ha ≫ pullback.fst sX sX = sX ≫ pointOfClosedPoint sX a ha := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] lemma secL_snd (a : X) (ha : IsClosed {a}) :
    secL (sX := sX) a ha ≫ pullback.snd sX sX = 𝟙 X := pullback.lift_snd _ _ _
@[reassoc (attr := simp)] lemma secR_fst (b : X) (hb : IsClosed {b}) :
    secR (sX := sX) b hb ≫ pullback.fst sX sX = 𝟙 X := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] lemma secR_snd (b : X) (hb : IsClosed {b}) :
    secR b hb ≫ pullback.snd sX sX = sX ≫ pointOfClosedPoint sX b hb := pullback.lift_snd _ _ _

namespace StrictChunk

variable (C : StrictChunk sX)

@[reassoc] lemma m_over : C.m ≫ sX = C.Ω.ι ≫ pullback.fst sX sX ≫ sX := by
  rw [← C.Φ_snd, Category.assoc, ← pullback.condition, C.Φ_fst_assoc]

@[reassoc] lemma m_over' : C.m ≫ sX = C.Ω.ι ≫ pullback.snd sX sX ≫ sX := by
  rw [C.m_over, pullback.condition]

lemma transL (a : X) (ha : IsClosed {a}) :
    TransData C.Ω C.Φ C.m (secL a ha) (pullback.snd sX sX) where
  sec := secL_snd a ha
  comp := C.Φ_snd
  fwd := by
    intro T g t hg
    apply pullback.hom_ext
    · simp only [Category.assoc, C.Φ_fst, secL_fst, C.m_over_assoc]
      simp only [reassoc_of% hg, secL_fst, secL_fst_assoc, pointOfClosedPoint_comp_assoc]
    · simp only [Category.assoc, C.Φ_snd, secL_snd, Category.comp_id]
  bwd := by
    intro T h t hh
    apply pullback.hom_ext
    · simp only [Category.assoc, secL_fst]
      rw [← pullback.condition_assoc, ← C.Φ_fst, ← C.Φ_fst_assoc]
      simp only [reassoc_of% hh, secL_fst, secL_fst_assoc, pointOfClosedPoint_comp_assoc]
    · simp only [Category.assoc, secL_snd, Category.comp_id]

lemma transR (b : X) (hb : IsClosed {b}) :
    TransData C.Ω C.Ψ C.m (secR b hb) (pullback.fst sX sX) where
  sec := secR_fst b hb
  comp := C.Ψ_fst
  fwd := by
    intro T g t hg
    apply pullback.hom_ext
    · simp only [Category.assoc, C.Ψ_fst, secR_fst, Category.comp_id]
    · simp only [Category.assoc, C.Ψ_snd, secR_snd, C.m_over'_assoc]
      simp only [reassoc_of% hg, secR_snd, secR_snd_assoc, pointOfClosedPoint_comp_assoc]
  bwd := by
    intro T h t hh
    apply pullback.hom_ext
    · simp only [Category.assoc, secR_fst, Category.comp_id]
    · simp only [Category.assoc, secR_snd]
      rw [pullback.condition_assoc, ← C.Ψ_snd, ← C.Ψ_snd_assoc]
      simp only [reassoc_of% hh, secR_snd, secR_snd_assoc, pointOfClosedPoint_comp_assoc]

end StrictChunk

lemma secL_apply_fst (a : X) (ha : IsClosed {a}) (x : X) : pullback.fst sX sX (secL a ha x) = a := by
  change (secL a ha ≫ pullback.fst sX sX) x = a
  rw [secL_fst]
  exact pointOfClosedPoint_apply sX a ha _

lemma secL_apply_snd (a : X) (ha : IsClosed {a}) (x : X) : pullback.snd sX sX (secL a ha x) = x := by
  change (secL a ha ≫ pullback.snd sX sX) x = x
  simp

lemma secR_apply_fst (b : X) (hb : IsClosed {b}) (x : X) : pullback.fst sX sX (secR b hb x) = x := by
  change (secR b hb ≫ pullback.fst sX sX) x = x
  simp

lemma secR_apply_snd (b : X) (hb : IsClosed {b}) (x : X) : pullback.snd sX sX (secR b hb x) = b := by
  change (secR b hb ≫ pullback.snd sX sX) x = b
  rw [secR_snd]
  exact pointOfClosedPoint_apply sX b hb _

lemma secL_isClosed (a : X) (ha : IsClosed {a}) (x : X) (hx : IsClosed {x}) :
    IsClosed {secL (sX := sX) a ha x} :=
  isClosed_singleton_apply sX (pullback.fst sX sX ≫ sX) (secL a ha) (by simp) x hx

lemma secR_isClosed (b : X) (hb : IsClosed {b}) (x : X) (hx : IsClosed {x}) :
    IsClosed {secR (sX := sX) b hb x} :=
  isClosed_singleton_apply sX (pullback.fst sX sX ≫ sX) (secR b hb) (by simp) x hx

lemma isClosed_fst (z : (pullback sX sX : Scheme.{u})) (hz : IsClosed {z}) :
    IsClosed {pullback.fst sX sX z} :=
  isClosed_singleton_apply (pullback.fst sX sX ≫ sX) sX (pullback.fst sX sX) rfl z hz

lemma isClosed_snd (z : (pullback sX sX : Scheme.{u})) (hz : IsClosed {z}) :
    IsClosed {pullback.snd sX sX z} :=
  isClosed_singleton_apply (pullback.fst sX sX ≫ sX) sX (pullback.snd sX sX) pullback.condition.symm z hz

namespace StrictChunk

variable (C : StrictChunk sX)

lemma lam_ne (a : X) (ha : IsClosed {a}) : ((secL a ha ⁻¹ᵁ C.Ω : X.Opens) : Set X).Nonempty := by
  obtain ⟨z, hzΩ, hz, hza⟩ := C.fib_left a ha
  have hx := isClosed_snd z hz
  have e : secL a ha (pullback.snd sX sX z) = z :=
    closedPoint_pullback_ext sX sX _ _ (secL_isClosed a ha _ hx) hz
      (by rw [secL_apply_fst, hza]) (by rw [secL_apply_snd])
  exact ⟨_, (Scheme.Hom.mem_preimage _).2 (e ▸ hzΩ)⟩

lemma rho_ne (b : X) (hb : IsClosed {b}) : ((secR b hb ⁻¹ᵁ C.Ω : X.Opens) : Set X).Nonempty := by
  obtain ⟨z, hzΩ, hz, hzb⟩ := C.fib_right b hb
  have hx := isClosed_fst z hz
  have e : secR b hb (pullback.fst sX sX z) = z :=
    closedPoint_pullback_ext sX sX _ _ (secR_isClosed b hb _ hx) hz
      (by rw [secR_apply_fst]) (by rw [secR_apply_snd, hzb])
  exact ⟨_, (Scheme.Hom.mem_preimage _).2 (e ▸ hzΩ)⟩

variable [IrreducibleSpace X]

/-- The left translation `λ_a : x ↦ m(a, x)` by a closed point `a`, as a partial isomorphism of `X`. -/
noncomputable def lam (a : X) (ha : IsClosed {a}) : X.PartialIso X :=
  (C.transL a ha).partialIso (C.lam_ne a ha)

/-- The right translation `ρ_b : x ↦ m(x, b)` by a closed point `b`, as a partial isomorphism of `X`. -/
noncomputable def rho (b : X) (hb : IsClosed {b}) : X.PartialIso X :=
  (C.transR b hb).partialIso (C.rho_ne b hb)

lemma lam_source (a : X) (ha : IsClosed {a}) : (C.lam a ha).source = secL a ha ⁻¹ᵁ C.Ω := rfl

lemma rho_source (b : X) (hb : IsClosed {b}) : (C.rho b hb).source = secR b hb ⁻¹ᵁ C.Ω := rfl

lemma lam_hom (a : X) (ha : IsClosed {a}) :
    (C.lam a ha).toPartialMap.hom = trR (secL a ha) C.Ω ≫ C.m :=
  (C.transL a ha).partialIso_hom _

lemma rho_hom (b : X) (hb : IsClosed {b}) :
    (C.rho b hb).toPartialMap.hom = trR (secR b hb) C.Ω ≫ C.m :=
  (C.transR b hb).partialIso_hom _

lemma lam_isOver (a : X) (ha : IsClosed {a}) : (C.lam a ha).IsOver sX sX :=
  (C.transL a ha).partialIso_isOver _ sX C.m_over'

lemma rho_isOver (b : X) (hb : IsClosed {b}) : (C.rho b hb).IsOver sX sX :=
  (C.transR b hb).partialIso_isOver _ sX C.m_over

end StrictChunk

end Chunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacLaw_Sep =====
section

/-!
# S4-JacLaw, file O9 (part Sep): Lagrange elements, separating elements, reduced quotients

Pure algebra over a field `K` for a commutative `K`-algebra `B` and its `K`-points `B →ₐ[K] K`.

* `exists_sep_pair`, `exists_lagrange` (`e` with `φ e = 1`, `ψ e = 0` for the other points of `Z`), `exists_delta`.
* `exists_injOn` (`K` infinite): an element `w` taking distinct values on a finite set of points.
* `charpoly_eq_prod_of_card`: if `Z` consists of zeros of `s` and `#Z = dim B/(s)`, then multiplication by `w` on
  `B/(s)` has characteristic polynomial `∏_{φ ∈ Z} (X - φ w)`.
* `resultant_prod_ne_zero`: `Res(c ∏ (X - φ w0), its derivative)` (in degrees `#Z`, `#Z`) is nonzero when `w0` separates `Z`.
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

section Sep

variable {K : Type*} [Field K] {B : Type*} [CommRing B] [Algebra K B]

/-- Two distinct points are separated by an element equal to `1` at the first and `0` at the second. -/
theorem exists_sep_pair {φ ψ : B →ₐ[K] K} (h : φ ≠ ψ) : ∃ u : B, φ u = 1 ∧ ψ u = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, φ t ≠ ψ t := by
    by_contra hc
    exact h (AlgHom.ext fun t => by_contra fun ht => hc ⟨t, ht⟩)
  have hne : φ t - ψ t ≠ 0 := sub_ne_zero.mpr ht
  refine ⟨(t - algebraMap K B (ψ t)) * algebraMap K B (φ t - ψ t)⁻¹, ?_, ?_⟩
  · simp only [map_mul, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    exact mul_inv_cancel₀ hne
  · simp only [map_mul, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self, zero_mul]

/-- A Lagrange element: `1` at `φ`, `0` at every other point of `Z`. -/
theorem exists_lagrange (Z : Finset (B →ₐ[K] K)) (φ : B →ₐ[K] K) :
    ∃ e : B, φ e = 1 ∧ ∀ ψ ∈ Z, ψ ≠ φ → ψ e = 0 := by
  classical
  choose u hu1 hu0 using fun ψ : {ψ : B →ₐ[K] K // ψ ≠ φ} => exists_sep_pair (Ne.symm ψ.2)
  refine ⟨∏ ψ ∈ Z.subtype (· ≠ φ), u ψ, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_one fun ψ _ => hu1 ψ
  · intro ψ hψ hne
    rw [map_prod]
    exact Finset.prod_eq_zero (i := ⟨ψ, hne⟩) (Finset.mem_subtype.mpr hψ) (hu0 ⟨ψ, hne⟩)

/-- Kronecker elements for an injective tuple of points. -/
theorem exists_delta {d : ℕ} (a : Fin d → (B →ₐ[K] K)) (ha : Function.Injective a) :
    ∃ χ : Fin d → B, ∀ i j, a j (χ i) = if j = i then 1 else 0 := by
  classical
  choose e he1 he0 using fun i => exists_lagrange (Finset.univ.image a) (a i)
  refine ⟨e, fun i j => ?_⟩
  split_ifs with hij
  · subst hij
    exact he1 j
  · exact he0 i (a j) (Finset.mem_image_of_mem a (Finset.mem_univ j)) (fun h => hij (ha h))

/-- An element separating a finite set of points (`K` infinite). -/
theorem exists_injOn [Infinite K] (Z : Finset (B →ₐ[K] K)) :
    ∃ w : B, Set.InjOn (fun φ : B →ₐ[K] K => φ w) Z := by
  classical
  choose e he1 he0 using fun φ => exists_lagrange Z φ
  let c : ℕ ↪ K := Infinite.natEmbedding K
  let idx : (B →ₐ[K] K) → ℕ := fun φ => if h : φ ∈ Z then (Z.equivFin ⟨φ, h⟩ : ℕ) else 0
  refine ⟨∑ φ ∈ Z, algebraMap K B (c (idx φ)) * e φ, ?_⟩
  have key : ∀ ψ ∈ Z, ψ (∑ φ ∈ Z, algebraMap K B (c (idx φ)) * e φ) = c (idx ψ) := by
    intro ψ hψ
    rw [map_sum, Finset.sum_eq_single ψ]
    · simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, he1, mul_one]
    · intro φ _ hne
      simp only [map_mul, he0 φ ψ hψ (Ne.symm hne), mul_zero]
    · intro h
      exact absurd hψ h
  intro φ hφ ψ hψ h
  have hφ' : φ ∈ Z := Finset.mem_coe.mp hφ
  have hψ' : ψ ∈ Z := Finset.mem_coe.mp hψ
  have h' : c (idx φ) = c (idx ψ) := by
    rw [← key φ hφ', ← key ψ hψ']
    exact h
  have h2 := c.injective h'
  simp only [idx, dif_pos hφ', dif_pos hψ'] at h2
  have h3 := Z.equivFin.injective (Fin.ext h2)
  exact congrArg Subtype.val h3

/-- **Reduced quotient.** If `Z` consists of zeros of `s` and `#Z = dim_K B/(s)`, then multiplication by `w` on `B/(s)`
has characteristic polynomial `∏_{φ ∈ Z} (X - φ w)`. -/
theorem charpoly_eq_prod_of_card (s : B) (Z : Finset (B →ₐ[K] K)) (hZ : ∀ φ ∈ Z, φ s = 0)
    (hfin : Module.Finite K (B ⧸ Ideal.span {s})) (hcard : Z.card = finrank K (B ⧸ Ideal.span {s})) (w : B) :
    LinearMap.charpoly (Algebra.lmul K (B ⧸ Ideal.span {s}) (Ideal.Quotient.mkₐ K (Ideal.span {s}) w)) =
      ∏ φ ∈ Z, (X - C (φ w)) := by
  classical
  set I : Ideal B := Ideal.span {s} with hIdef
  let ev0 : B →ₐ[K] (Z → K) := Pi.algHom K (fun _ => K) fun φ => φ.1
  have hev0 : ∀ b (φ : Z), ev0 b φ = φ.1 b := fun _ _ => rfl
  have hI : ∀ b ∈ I, ev0 b = 0 := by
    intro b hb
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    funext φ
    rw [hev0, map_mul, hZ φ.1 φ.2, mul_zero]
    rfl
  let ev : B ⧸ I →ₐ[K] (Z → K) := Ideal.Quotient.liftₐ I ev0 hI
  have hevmk : ∀ b, ev (Ideal.Quotient.mk I b) = ev0 b := fun b => rfl
  have hsurj : Function.Surjective ev := by
    intro f
    choose e he1 he0 using fun φ => exists_lagrange Z φ
    refine ⟨Ideal.Quotient.mk I (∑ φ : Z, algebraMap K B (f φ) * e φ.1), ?_⟩
    funext ψ
    rw [hevmk, hev0, map_sum, Finset.sum_eq_single ψ]
    · simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, he1, mul_one]
    · intro φ _ hne
      have : ψ.1 ≠ φ.1 := fun h => hne (Subtype.ext h).symm
      simp only [map_mul, he0 φ.1 ψ.1 ψ.2 this, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ ψ) h
  have hdim : finrank K (B ⧸ I) = finrank K (Z → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hcard]
  have hinj : Function.Injective ev :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := ev.toLinearMap) hdim).mpr hsurj
  let e : (B ⧸ I) ≃ₗ[K] (Z → K) := LinearEquiv.ofBijective ev.toLinearMap ⟨hinj, hsurj⟩
  have he : ∀ x, e x = ev x := fun _ => rfl
  let g : Z → K := fun φ => φ.1 w
  have hconj : e.conj (Algebra.lmul K (B ⧸ I) (Ideal.Quotient.mkₐ K I w)) = Algebra.lmul K (Z → K) g := by
    apply LinearMap.ext
    intro f
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    show e (Ideal.Quotient.mkₐ K I w * e.symm f) = g * f
    rw [he, map_mul, ← he (e.symm f), LinearEquiv.apply_symm_apply]
    rfl
  rw [← LinearEquiv.charpoly_conj e, hconj, ← LinearMap.charpoly_toMatrix _ (Pi.basisFun K Z)]
  have hmat : LinearMap.toMatrix (Pi.basisFun K Z) (Pi.basisFun K Z) (Algebra.lmul K (Z → K) g) =
      Matrix.diagonal g := by
    ext i j
    rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
    show (g * (Pi.single j (1 : K) : Z → K)) i = Matrix.diagonal g i j
    rw [Matrix.diagonal_apply, Pi.mul_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [hmat, Matrix.charpoly_diagonal]
  exact Finset.prod_coe_sort Z (fun φ => X - C (φ w))

/-- The resultant of `c ∏_{φ ∈ Z} (X - φ w0)` and its derivative (degrees `#Z`, `#Z`) is nonzero when `c ≠ 0` and `w0`
separates `Z`. -/
theorem resultant_prod_ne_zero (Z : Finset (B →ₐ[K] K)) (w0 : B) (hw : Set.InjOn (fun φ : B →ₐ[K] K => φ w0) Z)
    {c : K} (hc : c ≠ 0) :
    resultant (C c * ∏ φ ∈ Z, (X - C (φ w0))) (derivative (C c * ∏ φ ∈ Z, (X - C (φ w0)))) Z.card Z.card ≠ 0 := by
  set q : K[X] := ∏ φ ∈ Z, (X - C (φ w0)) with hq
  have hmon : q.Monic := monic_prod_of_monic _ _ fun φ _ => monic_X_sub_C (φ w0)
  have hdeg : q.natDegree = Z.card := by
    rw [hq, natDegree_prod_of_monic _ _ fun φ _ => monic_X_sub_C (φ w0)]
    simp
  have hsep : q.Separable := (separable_prod_X_sub_C_iff' (f := fun φ : B →ₐ[K] K => φ w0)).mpr hw
  have hres : resultant q (derivative q) ≠ 0 := resultant_ne_zero q (derivative q) hsep
  have hd' : (derivative q).natDegree ≤ Z.card := (natDegree_derivative_le q).trans (by omega)
  have hres' : resultant q (derivative q) Z.card Z.card ≠ 0 := by
    have key := resultant_add_right_deg (f := q) (g := derivative q) (m := Z.card)
      (n := (derivative q).natDegree) (Z.card - (derivative q).natDegree) le_rfl
    have e1 : (derivative q).natDegree + (Z.card - (derivative q).natDegree) = Z.card := by omega
    rw [e1] at key
    rw [key]
    have hc1 : q.coeff Z.card = 1 := by
      rw [← hdeg]
      exact hmon.coeff_natDegree
    rw [hc1, one_pow, one_mul, ← hdeg]
    exact hres
  rw [derivative_mul, derivative_C, zero_mul, zero_add, resultant_C_mul_left, resultant_C_mul_right]
  exact mul_ne_zero (pow_ne_zero _ hc) (mul_ne_zero (pow_ne_zero _ hc) hres')

end Sep

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacChunkA_Val =====
section

/-!
# Group chunk A2 (unit S4-JacChunkA): pointwise calculus for partial maps, the germ monoid

* `restrict_hom_apply`, `mem_comp_domain`, `comp_hom_apply`, `id_hom_apply`: values of partial maps at points.
* `toRationalMap_eq_of_apply`: identity principle (two partial `k`-maps of a reduced lft separated `k`-scheme
  agreeing at the closed points of their common domain define the same rational map);
  `apply_eq_of_toRationalMap_eq`: values do not depend on the representative.
* `DomRat k X`: the monoid of dominant rational `k`-self-maps of `X` (`a * b = a ∘ b`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

section Values

variable {X Y Z : Scheme.{u}}

lemma val_eq_of_comp_ι {A : Scheme.{u}} {U : X.Opens} {φ : A ⟶ U.toScheme} {ψ : A ⟶ X}
    (h : φ ≫ U.ι = ψ) (a : A) : (φ a).1 = ψ a :=
  congrArg (fun f => f a) h

lemma restrict_hom_apply (f : X.PartialMap Y) (U : X.Opens) (hU : Dense (U : Set X))
    (hU' : U ≤ f.domain) (x : U) : (f.restrict U hU hU').hom x = f.hom ⟨x.1, hU' x.2⟩ := by
  change f.hom (X.homOfLE hU' x) = _
  exact congrArg f.hom (Subtype.ext (val_eq_of_comp_ι (X.homOfLE_ι hU') x))

lemma id_hom_apply (x : X) (hx : x ∈ (Scheme.PartialMap.id X).domain) :
    (Scheme.PartialMap.id X).hom ⟨x, hx⟩ = x := by
  simp only [Scheme.Hom.toPartialMap_hom, Category.comp_id, Scheme.topIso_hom]
  rfl

variable [PreirreducibleSpace X] [Nonempty Y]

lemma mem_comp_domain (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) {x : X} :
    x ∈ (f.comp g).domain ↔ ∃ hx : x ∈ f.domain, f.hom ⟨x, hx⟩ ∈ g.domain := by
  change x ∈ f.domain.ι '' ((f.hom ⁻¹ᵁ g.domain : f.domain.toScheme.Opens) : Set f.domain.toScheme) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

lemma comp_hom_apply (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    (x : (f.comp g).domain) (hx : x.1 ∈ f.domain) (hx' : f.hom ⟨x.1, hx⟩ ∈ g.domain) :
    (f.comp g).hom x = g.hom ⟨f.hom ⟨x.1, hx⟩, hx'⟩ := by
  have h1 : ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv x).1 = ⟨x.1, hx⟩ :=
    Subtype.ext (congrArg (fun φ => φ x) (Scheme.Hom.isoImage_inv_ι f.domain.ι (f.hom ⁻¹ᵁ g.domain)))
  have h2 := val_eq_of_comp_ι (morphismRestrict_ι f.hom g.domain)
    ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv x)
  change g.hom ((f.hom ∣_ g.domain) ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv x)) = _
  refine congrArg g.hom (Subtype.ext ?_)
  exact h2.trans (congrArg f.hom h1)

end Values

section Identity

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] in
include k in
lemma lft_opens (U : X.Opens) : LocallyOfFiniteType (U.toScheme ↘ Spec (.of k)) := by
  rw [← Scheme.Opens.ι_comp_over]; infer_instance

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] in
include k in
lemma isClosed_val (U : X.Opens) (x : U) (hx : IsClosed {x}) : IsClosed {x.1} := by
  have := lft_opens (k := k) U
  exact isClosed_singleton_apply (U.toScheme ↘ Spec (.of k)) (X ↘ Spec (.of k)) U.ι rfl x hx

/-- Identity principle on closed points for partial `k`-maps. -/
lemma toRationalMap_eq_of_apply {f g : X.PartialMap X} [f.IsOver (Spec (.of k))]
    [g.IsOver (Spec (.of k))]
    (h : ∀ x (hf : x ∈ f.domain) (hg : x ∈ g.domain), IsClosed {x} → f.hom ⟨x, hf⟩ = g.hom ⟨x, hg⟩) :
    f.toRationalMap = g.toRationalMap := by
  rw [Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_iff_of_isSeparated (S := Spec (.of k))]
  have hlft : LocallyOfFiniteType ((f.restrict _ (f.2.inter_of_isOpen_left g.2 f.domain.2)
      inf_le_left).hom ≫ X ↘ Spec (.of k)) := by
    rw [comp_over]
    exact lft_opens _
  refine ext_of_apply_eq (X ↘ Spec (.of k)) Set.univ isOpen_univ.isLocallyClosed dense_univ ?_ ?_
  · intro x _ hx
    refine (restrict_hom_apply _ _ _ _ x).trans (Eq.trans ?_ (restrict_hom_apply _ _ _ _ x).symm)
    exact h _ _ _ (isClosed_val (k := k) _ x hx)
  · exact (HomIsOver.comp_over (f := (f.restrict _ (f.2.inter_of_isOpen_left g.2 f.domain.2)
      inf_le_left).hom) (S := Spec (.of k))).trans (HomIsOver.comp_over (f := (g.restrict _
      (f.2.inter_of_isOpen_left g.2 f.domain.2) inf_le_right).hom) (S := Spec (.of k))).symm

/-- Values of representatives of the same rational map agree on the common domain. -/
lemma apply_eq_of_toRationalMap_eq {f g : X.PartialMap X} [f.IsOver (Spec (.of k))]
    [g.IsOver (Spec (.of k))] (e : f.toRationalMap = g.toRationalMap) (x : X) (hf : x ∈ f.domain)
    (hg : x ∈ g.domain) : f.hom ⟨x, hf⟩ = g.hom ⟨x, hg⟩ := by
  rw [Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_iff_of_isSeparated (S := Spec (.of k))] at e
  have := congrArg (fun φ => φ (⟨x, hf, hg⟩ : (f.domain ⊓ g.domain : X.Opens))) e
  exact (restrict_hom_apply _ _ _ _ _).symm.trans (this.trans (restrict_hom_apply _ _ _ _ _))

end Identity

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkA_Germ =====
section

/-!
# Group chunk A2, part 2 (unit S4-JacChunkA): the germ group and the translation subgroup

* `comp_isOver`, `comp_eq_comp_of_apply`: composition of partial `k`-maps, checked on closed points.
* `DomRat k X`: the monoid of dominant rational `k`-self-maps of `X` (`a * b = a ∘ b`); `Bir k X` its units.
* `toBir f hf`: a partial `k`-isomorphism `X ⇢ X` as an element of `Bir k X`.
* `StrictChunk.lamB` / `rhoB`: the left and right translations of a strict chunk in `Bir k X`; they commute,
  and every element of the subgroup `C.H` generated by the left translations commutes with every `rhoB`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

section Germ

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

variable (k X) in
/-- Dominant rational `k`-self-maps of `X`. -/
def DomRat : Type u := {f : X ⤏ X // f.IsDominant ∧ f.IsOver (Spec (.of k))}

variable [IrreducibleSpace X]

/-- Composition `a * b = a ∘ b` (first `b`, then `a`). -/
noncomputable instance : Monoid (DomRat k X) where
  mul a b := haveI := a.2.1; haveI := b.2.1; haveI := a.2.2; haveI := b.2.2
    ⟨b.1.comp a.1, inferInstance, inferInstance⟩
  one := ⟨Scheme.RationalMap.id X, inferInstance, inferInstance⟩
  mul_assoc a b c := by
    haveI := a.2.1; haveI := b.2.1; haveI := c.2.1
    exact Subtype.ext (Scheme.RationalMap.comp_assoc c.1 b.1 a.1).symm
  one_mul a := by
    haveI := a.2.1
    exact Subtype.ext (Scheme.RationalMap.comp_id a.1)
  mul_one a := Subtype.ext (Scheme.RationalMap.id_comp a.1)

lemma DomRat.mul_val (a b : DomRat k X) :
    haveI := b.2.1; (a * b).1 = b.1.comp a.1 := rfl

lemma DomRat.one_val : (1 : DomRat k X).1 = Scheme.RationalMap.id X := rfl

variable (k X) in
/-- Birational `k`-self-maps of `X`, as the units of `DomRat k X`. -/
abbrev Bir : Type u := (DomRat k X)ˣ

end Germ

section PartialIso

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

lemma pi_isDominant (f : X.PartialIso X) : IsDominant f.toPartialMap.hom := by
  have := AlgebraicGeometry.Opens.isDominant_ι f.dense_target
  change IsDominant (f.iso.hom ≫ f.target.ι)
  infer_instance

lemma pi_isOver (f : X.PartialIso X) (hf : f.IsOver (X ↘ Spec (.of k)) (X ↘ Spec (.of k))) :
    f.toPartialMap.IsOver (Spec (.of k)) :=
  ⟨by
    change (f.iso.hom ≫ f.target.ι) ≫ X ↘ Spec (.of k) = f.source.ι ≫ X ↘ Spec (.of k)
    rw [Category.assoc]
    exact hf⟩

variable [IsAlgClosed k] [IsReduced X] [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [IrreducibleSpace X]

lemma comp_isOver (f g : X.PartialMap X) [IsDominant f.hom] [IsDominant g.hom]
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))] : (f.comp g).IsOver (Spec (.of k)) := by
  rw [← Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated,
    ← Scheme.RationalMap.toRationalMap_comp]
  infer_instance

/-- Two composites of partial `k`-maps agreeing at closed points define the same rational map. -/
lemma comp_eq_comp_of_apply (f g f' g' : X.PartialMap X) [IsDominant f.hom] [IsDominant g.hom]
    [IsDominant f'.hom] [IsDominant g'.hom] [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]
    (h : ∀ x (hx : x ∈ f.domain) (hx' : f.hom ⟨x, hx⟩ ∈ g.domain) (hy : x ∈ f'.domain)
      (hy' : f'.hom ⟨x, hy⟩ ∈ g'.domain), IsClosed {x} →
      g.hom ⟨f.hom ⟨x, hx⟩, hx'⟩ = g'.hom ⟨f'.hom ⟨x, hy⟩, hy'⟩) :
    f.toRationalMap.comp g.toRationalMap = f'.toRationalMap.comp g'.toRationalMap := by
  haveI := comp_isOver (k := k) f g
  haveI := comp_isOver (k := k) f' g'
  rw [Scheme.RationalMap.toRationalMap_comp, Scheme.RationalMap.toRationalMap_comp]
  refine toRationalMap_eq_of_apply (k := k) ?_
  intro x h1 h2 hc
  obtain ⟨hx, hx'⟩ := (mem_comp_domain f g).1 h1
  obtain ⟨hy, hy'⟩ := (mem_comp_domain f' g').1 h2
  rw [comp_hom_apply f g ⟨x, h1⟩ hx hx', comp_hom_apply f' g' ⟨x, h2⟩ hy hy']
  exact h x hx hx' hy hy' hc

lemma pi_comp_symm (f : X.PartialIso X) (hf : f.IsOver (X ↘ Spec (.of k)) (X ↘ Spec (.of k))) :
    haveI := pi_isDominant f
    f.toRationalMap.comp f.symm.toRationalMap = Scheme.RationalMap.id X := by
  haveI := pi_isDominant f; haveI := pi_isDominant f.symm
  haveI := pi_isOver f hf; haveI := pi_isOver f.symm hf.symm
  haveI := comp_isOver (k := k) f.toPartialMap f.symm.toPartialMap
  rw [Scheme.RationalMap.toRationalMap_comp]
  refine toRationalMap_eq_of_apply (k := k) ?_
  intro x h1 h2 _
  obtain ⟨hx, hx'⟩ := (mem_comp_domain _ _).1 h1
  rw [comp_hom_apply _ _ ⟨x, h1⟩ hx hx', id_hom_apply]
  have h := congrArg (fun φ => (φ ⟨x, hx⟩ : f.source.toScheme)) f.iso.hom_inv_id
  exact congrArg Subtype.val h

/-- A partial `k`-isomorphism as a dominant rational `k`-map. -/
noncomputable def toDom (f : X.PartialIso X)
    (hf : f.IsOver (X ↘ Spec (.of k)) (X ↘ Spec (.of k))) : DomRat k X :=
  ⟨f.toRationalMap, haveI := pi_isDominant f; inferInstance, haveI := pi_isOver f hf; inferInstance⟩

/-- A partial `k`-isomorphism as a birational `k`-self-map. -/
noncomputable def toBir (f : X.PartialIso X)
    (hf : f.IsOver (X ↘ Spec (.of k)) (X ↘ Spec (.of k))) : Bir k X where
  val := toDom f hf
  inv := toDom f.symm hf.symm
  val_inv := Subtype.ext (pi_comp_symm f.symm hf.symm)
  inv_val := Subtype.ext (pi_comp_symm f hf)

lemma toBir_val (f : X.PartialIso X) (hf : f.IsOver (X ↘ Spec (.of k)) (X ↘ Spec (.of k))) :
    (toBir f hf).1.1 = f.toRationalMap := rfl

lemma toBir_inv_val (f : X.PartialIso X) (hf : f.IsOver (X ↘ Spec (.of k)) (X ↘ Spec (.of k))) :
    (toBir f hf)⁻¹.1.1 = f.symm.toRationalMap := rfl

end PartialIso

section Chunk

lemma isClosed_mk' {T : Type*} [TopologicalSpace T] (U : TopologicalSpace.Opens T) (x : T) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set T)) : IsClosed ({⟨x, hx⟩} : Set U) := by
  have e : ({⟨x, hx⟩} : Set U) = Subtype.val ⁻¹' {x} := by
    ext y; simp [Subtype.ext_iff]
  rw [e]; exact hc.preimage continuous_subtype_val

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] in
lemma isClosed_hom_apply (f : X.PartialMap X) [f.IsOver (Spec (.of k))] (x : X) (hx : x ∈ f.domain)
    (hc : IsClosed {x}) : IsClosed {f.hom ⟨x, hx⟩} := by
  have := lft_opens (k := k) f.domain
  exact isClosed_singleton_apply (f.domain.toScheme ↘ Spec (.of k)) (X ↘ Spec (.of k)) f.hom
    (HomIsOver.comp_over (f := f.hom) (S := Spec (.of k))) ⟨x, hx⟩ (isClosed_mk' f.domain x hx hc)

variable [IrreducibleSpace X]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] in
lemma lam_apply (a : X) (ha : IsClosed {a}) (x : X) (hx : x ∈ (C.lam a ha).toPartialMap.domain) :
    (C.lam a ha).toPartialMap.hom ⟨x, hx⟩ = C.m ⟨secL a ha x, hx⟩ :=
  (congrArg (fun φ => φ (⟨x, hx⟩ : (secL a ha ⁻¹ᵁ C.Ω).toScheme)) (C.lam_hom a ha)).trans
    (congrArg C.m (Subtype.ext (val_eq_of_comp_ι (trR_ι (secL a ha) C.Ω) _)))

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] in
lemma rho_apply (b : X) (hb : IsClosed {b}) (x : X) (hx : x ∈ (C.rho b hb).toPartialMap.domain) :
    (C.rho b hb).toPartialMap.hom ⟨x, hx⟩ = C.m ⟨secR b hb x, hx⟩ :=
  (congrArg (fun φ => φ (⟨x, hx⟩ : (secR b hb ⁻¹ᵁ C.Ω).toScheme)) (C.rho_hom b hb)).trans
    (congrArg C.m (Subtype.ext (val_eq_of_comp_ι (trR_ι (secR b hb) C.Ω) _)))

/-- Left translation `λ_a` in `Bir k X`. -/
noncomputable def lamB (a : X) (ha : IsClosed {a}) : Bir k X := toBir (C.lam a ha) (C.lam_isOver a ha)

/-- Right translation `ρ_b` in `Bir k X`. -/
noncomputable def rhoB (b : X) (hb : IsClosed {b}) : Bir k X := toBir (C.rho b hb) (C.rho_isOver b hb)

lemma lamB_comm_rhoB (a : X) (ha : IsClosed {a}) (b : X) (hb : IsClosed {b}) :
    C.lamB a ha * C.rhoB b hb = C.rhoB b hb * C.lamB a ha := by
  haveI := pi_isDominant (C.lam a ha); haveI := pi_isDominant (C.rho b hb)
  haveI := pi_isOver _ (C.lam_isOver a ha); haveI := pi_isOver _ (C.rho_isOver b hb)
  refine Units.ext (Subtype.ext ?_)
  change (C.rho b hb).toRationalMap.comp (C.lam a ha).toRationalMap =
    (C.lam a ha).toRationalMap.comp (C.rho b hb).toRationalMap
  refine comp_eq_comp_of_apply (k := k) _ _ _ _ ?_
  intro x hx hx' hy hy' hc
  refine (C.lam_apply a ha _ hx').trans (Eq.trans ?_ (C.rho_apply b hb _ hy').symm)
  refine (C.assoc ⟨secL a ha x, hy⟩ ⟨secR b hb x, hx⟩ ⟨secR b hb _, hy'⟩ ⟨secL a ha _, hx'⟩
    (secL_isClosed a ha x hc) (secR_isClosed b hb x hc)
    (secR_isClosed b hb _ (isClosed_hom_apply (k := k) _ x hy hc))
    (secL_isClosed a ha _ (isClosed_hom_apply (k := k) _ x hx hc)) ?_ ?_ ?_ ?_ ?_).symm
  · exact (secL_apply_snd a ha x).trans (secR_apply_fst b hb x).symm
  · exact (secR_apply_fst b hb _).trans (C.lam_apply a ha x hy)
  · exact (secR_apply_snd b hb _).trans (secR_apply_snd b hb x).symm
  · exact (secL_apply_fst a ha _).trans (secL_apply_fst a ha x).symm
  · exact (secL_apply_snd a ha _).trans (C.rho_apply b hb x hx)

/-- The subgroup of `Bir k X` generated by the left translations. -/
noncomputable def H : Subgroup (Bir k X) :=
  Subgroup.closure (Set.range fun a : {a : X // IsClosed ({a} : Set X)} => C.lamB a.1 a.2)

lemma lamB_mem_H (a : X) (ha : IsClosed {a}) : C.lamB a ha ∈ C.H :=
  Subgroup.subset_closure ⟨⟨a, ha⟩, rfl⟩

/-- Every element of `H` commutes with every right translation. -/
lemma H_comm_rhoB (σ : Bir k X) (hσ : σ ∈ C.H) (b : X) (hb : IsClosed {b}) :
    σ * C.rhoB b hb = C.rhoB b hb * σ := by
  have hle : C.H ≤ Subgroup.centralizer
      (Set.range fun b : {b : X // IsClosed ({b} : Set X)} => C.rhoB b.1 b.2) := by
    rw [H, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    exact (C.lamB_comm_rhoB a.1 a.2 b.1 b.2).symm
  exact ((Subgroup.mem_centralizer_iff.1 (hle hσ)) _ ⟨⟨b, hb⟩, rfl⟩).symm

end StrictChunk

end Chunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacDivisors_R =====
section

/-!
# S4-JacDivisors R (O10, algebra part): étale over a regular ring is regular
* `isRegularLocalRing_of_etale_of_liesOver`, `isRegularLocalRing_of_etale`: if `A` is a regular
  ring and `B` is an étale `A`-algebra, then `B_Q` is a regular local ring for every prime `Q`.
* `isRegularRing_of_etale`: `B` is a regular ring.
Proof: `m_{B_Q} = p B_Q` (unramified), so `m_{B_Q}` needs at most `dim A_p = ht p` generators,
and `ht p ≤ ht Q` by going-down (flat).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open IsLocalRing

universe u v

theorem isRegularLocalRing_of_etale_of_liesOver {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [Algebra A B] [IsRegularRing A] [Algebra.Etale A B] (p : Ideal A) [p.IsPrime]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have hun : Algebra.IsUnramifiedAt A Q := by
    show Algebra.FormallyUnramified A (Localization.AtPrime Q)
    have : Algebra.FormallyUnramified B (Localization.AtPrime Q) :=
      Algebra.FormallyUnramified.of_isLocalization Q.primeCompl
    exact Algebra.FormallyUnramified.comp A B _
  have hmap : p.map (algebraMap A (Localization.AtPrime Q)) = maximalIdeal _ :=
    ((Algebra.isUnramifiedAt_iff_map_eq A p Q).mp hun).2
  have e : p.map (algebraMap A (Localization.AtPrime Q)) =
      (maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  have h1 : (maximalIdeal (Localization.AtPrime Q)).spanFinrank ≤
      (maximalIdeal (Localization.AtPrime p)).spanFinrank := by
    rw [← hmap, e]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)
  have h2 : ((maximalIdeal (Localization.AtPrime p)).spanFinrank : WithBot ℕ∞) = p.height := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal,
      IsLocalization.AtPrime.ringKrullDim_eq_height p]
  have h3 : p.height ≤ Q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p Q]
    exact le_self_add
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q]
  calc ((maximalIdeal (Localization.AtPrime Q)).spanFinrank : WithBot ℕ∞)
      ≤ ((maximalIdeal (Localization.AtPrime p)).spanFinrank : WithBot ℕ∞) := by
        exact_mod_cast h1
    _ = p.height := h2
    _ ≤ Q.height := by exact_mod_cast h3

theorem isRegularLocalRing_of_etale {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [IsRegularRing A] [Algebra.Etale A B] (Q : Ideal B) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) :=
  isRegularLocalRing_of_etale_of_liesOver (Q.under A) Q

theorem isRegularRing_of_etale {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [IsRegularRing A] [Algebra.Etale A B] : IsRegularRing B := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  rw [isRegularRing_iff]
  intro Q _
  exact isRegularLocalRing_of_etale (A := A) Q

end RamanujanPetersson.JacDivisors

end


