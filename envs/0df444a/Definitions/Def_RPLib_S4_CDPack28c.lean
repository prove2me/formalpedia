-- Prove2me | Definitions.Def_RPLib_S4_CDPack28c
-- name    : RPLib_S4_CDPack28c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:56:37.869202+00:00
-- url     : https://prove2.me/theorems/54c6207a-ab33-4809-bea9-60bb57f82fdd
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 28c of 71
-- statement:
--   Part 28c of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_Uniq`: S4-JacLaw, file O8a: uniqueness of `ν`, supports of points, padding and sum maps
--   * `Def_RP_JacLaw_Step`: S4-JacLaw, file O8b: the set-level negation `nuF` and the step map `nuStep`
--   * `Def_RP_JacLaw_Div`: S4-JacLaw, file O8d: divisors of good sections
--   * `Def_RP_JacLaw_GenDiv`: S4-JacLaw, file O9d (G3b GenDiv): divisors of sections with reduced zero sets, and the rank condition
--   * `Def_RP_JacComplete_FibG`: The Jacobian (unit S4-JacComplete), part `FibG` (generic fibres of a function with a simple zero or pole)
--   * `Def_RP_JacComplete_SecA`: The Jacobian (unit S4-JacComplete), part `SecA` (a function with only simple zeros through a given point)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack28b
import Definitions.Def_RPLib_S4_CDPack25
import Definitions.Def_RPLib_S4_CDPack23
import Definitions.Def_RPLib_S4_CDPack24

/-!
# Curve-duality library package, part 28c of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_Uniq`: S4-JacLaw, file O8a: uniqueness of `ν`, supports of points, padding and sum maps
* `Def_RP_JacLaw_Step`: S4-JacLaw, file O8b: the set-level negation `nuF` and the step map `nuStep`
* `Def_RP_JacLaw_Div`: S4-JacLaw, file O8d: divisors of good sections
* `Def_RP_JacLaw_GenDiv`: S4-JacLaw, file O9d (G3b GenDiv): divisors of sections with reduced zero sets, and the rank condition
* `Def_RP_JacComplete_FibG`: The Jacobian (unit S4-JacComplete), part `FibG` (generic fibres of a function with a simple zero or pole)
* `Def_RP_JacComplete_SecA`: The Jacobian (unit S4-JacComplete), part `SecA` (a function with only simple zeros through a given point)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_Uniq =====
section

/-!
# S4-JacLaw, file O8a: uniqueness of `ν`, supports of points, padding and sum maps

* `ptSet y`: the support of a `k`-point `y` of `Sym^n` (a finset); `symPt_eq_of_image_eq` (reduced points with the same
  support are equal).
* `padMap φ c hd : Sym^d → R` with points `x ↦ φ(x) + c` and `sumMap φ ψ : Sym^(n+m) → R` with points
  `x ↦ φ(x) + ψ(x)`, both by the morphism criterion `liftPts`.
* `span_h`: the basis `h` of a `NuData` spans `L(Hn) ∩ B`; `nu_unique`: the zero set of the kernel section does not
  depend on the choice data, only on `Hn` and on any `d` of its zeros; `nuSet_eq_of_sub`: `ν(A') = Z \ A'` whenever
  `A' ⊆ Z = Z(s)` for a good section `s` with the same pole divisor.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

section Pts

open Classical

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}

/-- The support of a `k`-point of `Sym^n`. -/
noncomputable def ptSet (y : SymRing k B n →ₐ[k] k) : Finset (B →ₐ[k] k) :=
  Finset.univ.image (liftTuple y)

theorem mem_ptSet (y : SymRing k B n →ₐ[k] k) (φ : B →ₐ[k] k) : φ ∈ ptSet y ↔ ∃ i, liftTuple y i = φ := by
  simp [ptSet]

theorem image_eq_of_symPt_eq (a a' : Fin n → (B →ₐ[k] k)) (h : symPt a = symPt a') :
    Finset.univ.image a = Finset.univ.image a' := by
  obtain ⟨σ, rfl⟩ := exists_perm_of_symPt_eq a a' h
  ext φ
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  exact ⟨fun ⟨i, hi⟩ => ⟨σ.symm i, by simpa using hi⟩, fun ⟨i, hi⟩ => ⟨σ i, hi⟩⟩

theorem ptSet_symPt (a : Fin n → (B →ₐ[k] k)) : ptSet (symPt a) = Finset.univ.image a :=
  image_eq_of_symPt_eq _ _ (symPt_liftTuple _)

theorem symPt_eq_of_image_eq {a a' : Fin n → (B →ₐ[k] k)} (ha : Function.Injective a)
    (ha' : Function.Injective a') (h : Finset.univ.image a = Finset.univ.image a') : symPt a = symPt a' := by
  apply symPt_eq_of_mset_eq
  apply Subtype.ext
  show Finset.univ.val.map a = Finset.univ.val.map a'
  have e1 : (Finset.univ.image a).val = Finset.univ.val.map a :=
    (Finset.image_val _ _).trans (Multiset.Nodup.dedup (Finset.univ.nodup.map ha))
  have e2 : (Finset.univ.image a').val = Finset.univ.val.map a' :=
    (Finset.image_val _ _).trans (Multiset.Nodup.dedup (Finset.univ.nodup.map ha'))
  rw [← e1, ← e2, h]

theorem image_cast_append {r d : ℕ} {α : Type*} (a : Fin n → α) (c : Fin r → α) (hd : n + r = d) :
    Finset.univ.image (fun i : Fin d => Fin.append a c (Fin.cast hd.symm i)) =
      Finset.univ.image a ∪ Finset.univ.image c := by
  subst hd
  ext φ
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Fin.cast_eq_self]
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Or.inl ⟨j, by simp⟩
    · exact Or.inr ⟨j, by simp⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd r j, by simp⟩
    · exact ⟨Fin.natAdd n j, by simp⟩

theorem image_append {m : ℕ} {α : Type*} (a : Fin n → α) (b : Fin m → α) :
    Finset.univ.image (Fin.append a b) = Finset.univ.image a ∪ Finset.univ.image b := by
  have := image_cast_append a b (rfl : n + m = n + m)
  simpa only [Fin.cast_eq_self] using this

theorem image_enumF {α : Type*} (T : Finset α) {m : ℕ} (h : T.card = m) :
    Finset.univ.image (enumF T h) = T :=
  Finset.eq_of_subset_of_card_le (fun φ hφ => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hφ
      exact enumF_mem _ _ i)
    (by rw [Finset.card_image_of_injective _ (enumF_injective _ _), Finset.card_univ, Fintype.card_fin, h])

end Pts

section Morph

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B]
  {R : Type*} [CommRing R] [Algebra k R] [IsReduced R] [Algebra.FiniteType k R]

/-- The point `φ(x) + c` of `Sym^d` (`d = n + r`, padding by the fixed tuple `c`). -/
noncomputable def padPt {n r d : ℕ} (φ : SymRing k B n →ₐ[k] R) (c : Fin r → (B →ₐ[k] k)) (hd : n + r = d)
    (x : R →ₐ[k] k) : SymRing k B d →ₐ[k] k :=
  symPt (fun i => Fin.append (liftTuple (x.comp φ)) c (Fin.cast hd.symm i))

theorem padPt_normS {n r d : ℕ} (φ : SymRing k B n →ₐ[k] R) (c : Fin r → (B →ₐ[k] k)) (hd : n + r = d)
    (x : R →ₐ[k] k) (w : B) : padPt φ c hd x (normS k w) = x (φ (normS k w)) * ∏ i, c i w := by
  subst hd
  rw [padPt, symPt_normS]
  simp only [Fin.cast_eq_self]
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← symPt_normS, symPt_liftTuple]
  rfl

/-- **Padding map** `Sym^d → R`, points `x ↦ φ(x) + c`. -/
noncomputable def padMap {n r d : ℕ} (φ : SymRing k B n →ₐ[k] R) (c : Fin r → (B →ₐ[k] k)) (hd : n + r = d) :
    SymRing k B d →ₐ[k] R :=
  liftPts (padPt φ c hd) fun w => ⟨φ (normS k w) * algebraMap k R (∏ i, c i w), fun x => by
    rw [map_mul, AlgHom.commutes, padPt_normS]; rfl⟩

theorem comp_padMap {n r d : ℕ} (φ : SymRing k B n →ₐ[k] R) (c : Fin r → (B →ₐ[k] k)) (hd : n + r = d)
    (x : R →ₐ[k] k) : x.comp (padMap φ c hd) = padPt φ c hd x :=
  comp_liftPts _ _ x

/-- The point `φ(x) + ψ(x)` of `Sym^(n+m)`. -/
noncomputable def sumPt {n m : ℕ} (φ : SymRing k B n →ₐ[k] R) (ψ : SymRing k B m →ₐ[k] R) (x : R →ₐ[k] k) :
    SymRing k B (n + m) →ₐ[k] k :=
  symPt (Fin.append (liftTuple (x.comp φ)) (liftTuple (x.comp ψ)))

theorem sumPt_normS {n m : ℕ} (φ : SymRing k B n →ₐ[k] R) (ψ : SymRing k B m →ₐ[k] R) (x : R →ₐ[k] k) (w : B) :
    sumPt φ ψ x (normS k w) = x (φ (normS k w)) * x (ψ (normS k w)) := by
  rw [sumPt, symPt_append, symPt_liftTuple, symPt_liftTuple]
  rfl

/-- **Sum map** `Sym^(n+m) → R`, points `x ↦ φ(x) + ψ(x)`. -/
noncomputable def sumMap {n m : ℕ} (φ : SymRing k B n →ₐ[k] R) (ψ : SymRing k B m →ₐ[k] R) :
    SymRing k B (n + m) →ₐ[k] R :=
  liftPts (sumPt φ ψ) fun w => ⟨φ (normS k w) * ψ (normS k w), fun x => by rw [map_mul, sumPt_normS]⟩

theorem comp_sumMap {n m : ℕ} (φ : SymRing k B n →ₐ[k] R) (ψ : SymRing k B m →ₐ[k] R) (x : R →ₐ[k] k) :
    x.comp (sumMap φ ψ) = sumPt φ ψ x :=
  comp_liftPts _ _ x

open Classical in
theorem ptSet_padPt {n r d : ℕ} (φ : SymRing k B n →ₐ[k] R) (c : Fin r → (B →ₐ[k] k)) (hd : n + r = d)
    (x : R →ₐ[k] k) : ptSet (padPt φ c hd x) = ptSet (x.comp φ) ∪ Finset.univ.image c := by
  rw [padPt, ptSet_symPt, image_cast_append _ _ hd]
  rfl

open Classical in
theorem ptSet_sumPt {n m : ℕ} (φ : SymRing k B n →ₐ[k] R) (ψ : SymRing k B m →ₐ[k] R) (x : R →ₐ[k] k) :
    ptSet (sumPt φ ψ x) = ptSet (x.comp φ) ∪ ptSet (x.comp ψ) := by
  rw [sumPt, ptSet_symPt, image_append]
  rfl

end Morph

section Uniq

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]

theorem zeroFin_congr {s s' : B} (h : ∀ φ : B →ₐ[k] k, φ s = 0 ↔ φ s' = 0) :
    zeroFin (k := k) s = zeroFin (k := k) s' := by
  have e : {φ : B →ₐ[k] k | φ s = 0} = {φ | φ s' = 0} := Set.ext h
  unfold zeroFin
  rw [e]

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace NuData

variable {d : ℕ}

/-- The basis `h` spans `L(Hn) ∩ B` (Riemann-Roch, `deg Hn = d + g ≥ 2g - 1`). -/
theorem span_h (D : NuData K F d) (hd : genusFK K F ≤ d + 1) :
    Submodule.span K (Set.range D.h) = Linf K F D.Hn := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.2 (Set.range_subset_iff.2 D.h_mem)
  · rw [finrank_span_eq_card D.h_li, Fintype.card_fin]
    have := finrank_Linf_eq (constField_eq_bot' (K := K) (F := F)) D.Hn_inf
      (by rw [D.Hn_deg]; push_cast; omega)
    rw [D.Hn_deg] at this
    push_cast at this
    omega

variable {D : NuData K F d} {y : SymRing K (Places.Rfin K F) d →ₐ[K] K}

/-- Any element of `L(Hn) ∩ B` vanishing at the points of a good `y` is a multiple of `sec y`. -/
theorem exists_eq_smul_sec (hd : genusFK K F ≤ d + 1) (hy : y D.good ≠ 0) {f : Places.Rfin K F}
    (hf : f ∈ Linf K F D.Hn) (hz : ∀ i, liftTuple y i f = 0) : ∃ t : K, t • D.sec y = f := by
  rw [← D.span_h hd] at hf
  have := mem_span_sPt (kerVec_ne hy) hf hz
  rw [← sec_eq] at this
  exact Submodule.mem_span_singleton.1 this

theorem zeroFin_eq_of_mem (hd : genusFK K F ≤ d + 1) (hy : y D.good ≠ 0) {f : Places.Rfin K F}
    (hf : f ∈ Linf K F D.Hn) (hf0 : f ≠ 0) (hz : ∀ i, liftTuple y i f = 0) :
    zeroFin (k := K) f = zeroFin (k := K) (D.sec y) := by
  obtain ⟨t, rfl⟩ := exists_eq_smul_sec hd hy hf hz
  have ht : t ≠ 0 := by rintro rfl; exact hf0 (zero_smul _ _)
  exact zeroFin_congr fun φ => by rw [map_smul, smul_eq_mul, mul_eq_zero, or_iff_right ht]

/-- **ν-uniqueness.** Two good sections with the same pole divisor, the second vanishing... share their zero sets. -/
theorem nu_unique {D' : NuData K F d} (hd : genusFK K F ≤ d + 1) (hHn : D'.Hn = D.Hn) (hy : y D.good ≠ 0)
    {y' : SymRing K (Places.Rfin K F) d →ₐ[K] K} (hy' : y' D'.good ≠ 0)
    (hz : ∀ i, liftTuple y' i (D.sec y) = 0) :
    zeroFin (k := K) (D'.sec y') = zeroFin (k := K) (D.sec y) :=
  (zeroFin_eq_of_mem hd hy' (hHn ▸ D.sec_mem y) (sec_ne_zero hy) hz).symm

open Classical in
theorem nuSet_eq (D : NuData K F d) (x : D.Rg →ₐ[K] K) :
    D.nuSet x = zeroFin (k := K) (D.sec (D.yOf x)) \ ptSet (D.yOf x) := rfl

open Classical in
/-- **`ν(A') = Z \ A'`** for `A' ⊆ Z = Z(s)`, `s` any good section with the same pole divisor. -/
theorem nuSet_eq_of_sub {D' : NuData K F d} (hd : genusFK K F ≤ d + 1) (hHn : D'.Hn = D.Hn)
    (hy : y D.good ≠ 0) (x' : D'.Rg →ₐ[K] K) (hz : ptSet (D'.yOf x') ⊆ zeroFin (k := K) (D.sec y)) :
    D'.nuSet x' = zeroFin (k := K) (D.sec y) \ ptSet (D'.yOf x') := by
  have hz' : ∀ i, liftTuple (D'.yOf x') i (D.sec y) = 0 := fun i =>
    ((zero_spec hy).1 _).1 (hz ((mem_ptSet _ _).2 ⟨i, rfl⟩))
  rw [nuSet_eq, nu_unique hd hHn hy (D'.yOf_good x') hz']

open Classical in
/-- The point `ν(A)` is `symPt a` for any injective enumeration `a` of `nuSet`. -/
theorem nuPt_eq_symPt (D : NuData K F d) (x : D.Rg →ₐ[K] K) {a : Fin (genusFK K F) → (Places.Rfin K F →ₐ[K] K)}
    (ha : Function.Injective a) (h : D.nuSet x = Finset.univ.image a) : D.nuPt x = symPt a := by
  rw [nuPt]
  apply symPt_eq_of_image_eq (enumF_injective _ _) ha
  rw [image_enumF, h]

open Classical in
theorem ptSet_nuPt (D : NuData K F d) (x : D.Rg →ₐ[K] K) : ptSet (D.nuPt x) = D.nuSet x := by
  rw [nuPt, ptSet_symPt, image_enumF]

end NuData

end Uniq

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_Step =====
section

/-!
# S4-JacLaw, file O8b: the set-level negation `nuF` and the step map `nuStep`

* `nuF D y = Z(sec y) \ A` for a point `y = A` of `Sym^d` (the negation `ν` as a finset); `card_nuF`,
  `zeroFin_eq_union`, `disjoint_nuF`.
* `swap_step`: if `A = P ⊔ Q` and `A' = P ∪ ν(A)` then `ν'(A') = Q` (any choice data with the same `Hn`): every law
  identity `r(a, m(a,b)) = b`, `m(a, r(a,c)) = c`, ... is two applications of it.
* `nuStep D ψ : Sym^g → T[1/ψ(good)]` for any `ψ : Sym^d → T` (`T` reduced f.g.): the composite of `ψ` and `ν`;
  `ptSet_nuStep` (its points are `nuF D (ψ x)`), `baseAway`, `exists_baseAway`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

theorem disjoint_of_card_union {α : Type*} [DecidableEq α] {s t : Finset α} {m n : ℕ} (hs : s.card ≤ m)
    (ht : t.card ≤ n) (h : (s ∪ t).card = m + n) : Disjoint s t ∧ s.card = m ∧ t.card = n := by
  have h1 := Finset.card_union_add_card_inter s t
  have h0 : (s ∩ t).card = 0 := by omega
  exact ⟨Finset.disjoint_iff_inter_eq_empty.2 (Finset.card_eq_zero.1 h0), by omega, by omega⟩

open Classical in
theorem card_ptSet_le {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}
    (y : SymRing k B n →ₐ[k] k) : (ptSet y).card ≤ n := by
  refine (Finset.card_image_le).trans ?_
  simp

section Away

variable {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T]

instance (priority := high) finiteType_awayInst [Algebra.FiniteType K T] (u : T) :
    Algebra.FiniteType K (Localization.Away u) :=
  finiteType_away u

/-- The point of `T` below a point of `T[1/u]`. -/
noncomputable def baseAway (u : T) (x : Localization.Away u →ₐ[K] K) : T →ₐ[K] K :=
  x.comp (IsScalarTower.toAlgHom K T (Localization.Away u))

theorem baseAway_apply (u : T) (x : Localization.Away u →ₐ[K] K) (t : T) :
    baseAway u x t = x (algebraMap T _ t) := rfl

theorem baseAway_ne (u : T) (x : Localization.Away u →ₐ[K] K) : baseAway u x u ≠ 0 := by
  rw [baseAway_apply]
  exact ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away u) u).map x).ne_zero

theorem exists_baseAway (u : T) (y : T →ₐ[K] K) (hy : y u ≠ 0) :
    ∃ x : Localization.Away u →ₐ[K] K, baseAway u x = y := by
  have hf : ∀ m : Submonoid.powers u, IsUnit (y m) := by
    rintro ⟨_, n, rfl⟩
    show IsUnit (y (u ^ n))
    rw [map_pow]
    exact (isUnit_iff_ne_zero.mpr hy).pow n
  refine ⟨IsLocalization.liftAlgHom (S := Localization.Away u) hf, ?_⟩
  ext s
  rw [baseAway_apply, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

end Away

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace NuData

variable {d : ℕ}

open Classical in
/-- The negation `ν(A) = Z(s_A) \ A` at a point `y = A` of `Sym^d`, as a finset. -/
noncomputable def nuF (D : NuData K F d) (y : SymRing K (Places.Rfin K F) d →ₐ[K] K) :
    Finset (Places.Rfin K F →ₐ[K] K) :=
  zeroFin (k := K) (D.sec y) \ ptSet y

variable {D : NuData K F d} {y : SymRing K (Places.Rfin K F) d →ₐ[K] K}

theorem nuSet_eq_nuF (D : NuData K F d) (x : D.Rg →ₐ[K] K) : D.nuSet x = D.nuF (D.yOf x) := rfl

open Classical in
theorem ptSet_sub_zeroFin (hy : y D.good ≠ 0) : ptSet y ⊆ zeroFin (k := K) (D.sec y) := fun φ hφ => by
  obtain ⟨i, rfl⟩ := (mem_ptSet _ _).1 hφ
  exact lift_mem_zeroFin hy i

open Classical in
theorem zeroFin_eq_union (hy : y D.good ≠ 0) : zeroFin (k := K) (D.sec y) = ptSet y ∪ D.nuF y :=
  (Finset.union_sdiff_of_subset (ptSet_sub_zeroFin hy)).symm

open Classical in
theorem disjoint_nuF (D : NuData K F d) (y : SymRing K (Places.Rfin K F) d →ₐ[K] K) :
    Disjoint (ptSet y) (D.nuF y) :=
  Finset.disjoint_sdiff

open Classical in
theorem card_ptSet (hy : y D.good ≠ 0) : (ptSet y).card = d := by
  rw [ptSet, Finset.card_image_of_injective _ (injective_lift hy), Finset.card_univ, Fintype.card_fin]

theorem card_nuF (hy : y D.good ≠ 0) : (D.nuF y).card = genusFK K F := by
  classical
  rw [nuF, Finset.card_sdiff_of_subset (ptSet_sub_zeroFin hy), (zero_spec hy).2.1, card_ptSet hy]
  omega

open Classical in
theorem nuF_eq_of_sub {D' : NuData K F d} (hd : genusFK K F ≤ d + 1) (hHn : D'.Hn = D.Hn) (hy : y D.good ≠ 0)
    {y' : SymRing K (Places.Rfin K F) d →ₐ[K] K} (hy' : y' D'.good ≠ 0)
    (hz : ptSet y' ⊆ zeroFin (k := K) (D.sec y)) : D'.nuF y' = zeroFin (k := K) (D.sec y) \ ptSet y' := by
  have hz' : ∀ i, liftTuple y' i (D.sec y) = 0 := fun i =>
    ((zero_spec hy).1 _).1 (hz ((mem_ptSet _ _).2 ⟨i, rfl⟩))
  rw [nuF, nu_unique hd hHn hy hy' hz']

open Classical in
/-- **Swap step.** `A = P ⊔ Q`, `A' = P ∪ ν(A)` ⇒ `ν'(A') = Q`. -/
theorem swap_step {D' : NuData K F d} (hd : genusFK K F ≤ d + 1) (hHn : D'.Hn = D.Hn) (hy : y D.good ≠ 0)
    {y' : SymRing K (Places.Rfin K F) d →ₐ[K] K} (hy' : y' D'.good ≠ 0) {P Q : Finset (Places.Rfin K F →ₐ[K] K)}
    (hPQ : ptSet y = P ∪ Q) (hdisj : Disjoint P Q) (h' : ptSet y' = P ∪ D.nuF y) : D'.nuF y' = Q := by
  have hR : Disjoint (P ∪ Q) (D.nuF y) := hPQ ▸ D.disjoint_nuF y
  have hz : ptSet y' ⊆ zeroFin (k := K) (D.sec y) := by
    rw [h', zeroFin_eq_union hy, hPQ]
    intro φ hφ
    simp only [Finset.mem_union] at hφ ⊢
    tauto
  rw [nuF_eq_of_sub hd hHn hy hy' hz, zeroFin_eq_union hy, hPQ, h']
  ext φ
  have h1 : φ ∈ P → φ ∉ Q := fun h => Finset.disjoint_left.1 hdisj h
  have h2 : φ ∈ P ∪ Q → φ ∉ D.nuF y := fun h => Finset.disjoint_left.1 hR h
  simp only [Finset.mem_sdiff, Finset.mem_union] at h1 h2 ⊢
  tauto

end NuData

section Step

variable {T : Type*} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]

namespace NuData

variable {d : ℕ}

/-- **Step map** `Sym^g → T[1/ψ(good)]`: the composite `ν ∘ ψ` on the open where `ψ` lands in `D(good)`. -/
noncomputable def nuStep (D : NuData K F d) (ψ : SymRing K (Places.Rfin K F) d →ₐ[K] T) :
    SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] Localization.Away (ψ D.good) :=
  (Localization.awayMapₐ ψ D.good).comp D.nuMap

theorem yOf_awayMap (D : NuData K F d) (ψ : SymRing K (Places.Rfin K F) d →ₐ[K] T)
    (x : Localization.Away (ψ D.good) →ₐ[K] K) :
    D.yOf (x.comp (Localization.awayMapₐ ψ D.good)) = (baseAway (ψ D.good) x).comp ψ := by
  ext s
  rw [yOf_apply, AlgHom.comp_apply, AlgHom.comp_apply, baseAway_apply]
  congr 1
  simp only [Localization.awayMapₐ, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq]
  rfl

theorem good_base (D : NuData K F d) (ψ : SymRing K (Places.Rfin K F) d →ₐ[K] T)
    (x : Localization.Away (ψ D.good) →ₐ[K] K) : ((baseAway (ψ D.good) x).comp ψ) D.good ≠ 0 :=
  baseAway_ne _ x

open Classical in
theorem ptSet_nuStep (D : NuData K F d) (ψ : SymRing K (Places.Rfin K F) d →ₐ[K] T)
    (x : Localization.Away (ψ D.good) →ₐ[K] K) :
    ptSet (x.comp (D.nuStep ψ)) = D.nuF ((baseAway (ψ D.good) x).comp ψ) := by
  rw [nuStep, ← AlgHom.comp_assoc, comp_nuMap, ptSet_nuPt, nuSet_eq_nuF, yOf_awayMap]

theorem comp_nuStep (D : NuData K F d) (ψ : SymRing K (Places.Rfin K F) d →ₐ[K] T)
    (x : Localization.Away (ψ D.good) →ₐ[K] K) :
    x.comp (D.nuStep ψ) = D.nuPt (x.comp (Localization.awayMapₐ ψ D.good)) := by
  rw [nuStep, ← AlgHom.comp_assoc, comp_nuMap]

theorem card_ptSet_nuStep (D : NuData K F d) (ψ : SymRing K (Places.Rfin K F) d →ₐ[K] T)
    (x : Localization.Away (ψ D.good) →ₐ[K] K) :
    (ptSet (x.comp (D.nuStep ψ))).card = genusFK K F := by
  classical
  rw [ptSet_nuStep]
  exact card_nuF (D.good_base ψ x)

end NuData

end Step

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_Div =====
section

/-!
# S4-JacLaw, file O8d: divisors of good sections

* `not_isField_Rfin`; `ptP φ`: the prime divisor `ker φ` of a point `φ` of the chart `B = Rfin K F`
  (`ptP_injective`, `exists_ptP`, `mem_ptP`).
* `Zdiv S = Σ_{φ ∈ S} [ptP φ]`: `Zdiv_inl_ptP`, `Zdiv_inr`, `Zdiv_union`, `Zdiv_nonneg`, `Zdiv_injective`.
* `cnt_ne_zero_iff`: `cnt P b ≠ 0 ↔ b ∈ P`; `apply_eq_zero_of_ord`.
* **`div_sec`**: at a good point the `N` zeros of `s = sec y` are simple, `div s = Zdiv Z(s) - Hn`;
  `div_sec'`: `div s = Zdiv (ptSet y) + Zdiv (nuF y) - Hn`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

section Div

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
theorem not_isField_Rfin : ¬ IsField (Places.Rfin K F) := fun h => by
  have : Algebra.IsIntegral K[X] (Places.Rfin K F) :=
    IsIntegralClosure.isIntegral_algebra (R := K[X]) (A := Places.Rfin K F) (B := F)
  exact Polynomial.not_isField K
    ((Algebra.IsIntegral.isField_iff_isField (FunctionField.ringOfIntegers.algebraMap_injective K F)).2 h)

/-- The prime divisor of a point of the chart. -/
noncomputable def ptP (φ : Places.Rfin K F →ₐ[K] K) : HeightOneSpectrum (Places.Rfin K F) :=
  ptDivEquiv (not_isField_Rfin K F) φ

theorem mem_ptP {φ : Places.Rfin K F →ₐ[K] K} {b : Places.Rfin K F} : b ∈ (ptP φ).asIdeal ↔ φ b = 0 := by
  rw [ptP, ptDivEquiv_asIdeal]
  exact RingHom.mem_ker

theorem ptP_injective : Function.Injective (ptP (K := K) (F := F)) := (ptDivEquiv _).injective

theorem exists_ptP (P : HeightOneSpectrum (Places.Rfin K F)) : ∃ φ : Places.Rfin K F →ₐ[K] K, ptP φ = P :=
  (ptDivEquiv _).surjective P

/-- The reduced divisor of a finite set of points. -/
noncomputable def Zdiv (S : Finset (Places.Rfin K F →ₐ[K] K)) : Places.Divisor K F :=
  ∑ φ ∈ S, Finsupp.single (Sum.inl (ptP φ)) 1

theorem Zdiv_inl_ptP (S : Finset (Places.Rfin K F →ₐ[K] K)) (φ : Places.Rfin K F →ₐ[K] K) :
    Zdiv S (Sum.inl (ptP φ)) = if φ ∈ S then 1 else 0 := by
  rw [Zdiv, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Sum.inl.injEq, ptP_injective.eq_iff]
  exact Finset.sum_ite_eq' S φ (fun _ => (1 : ℤ))

theorem Zdiv_inr (S : Finset (Places.Rfin K F →ₐ[K] K)) (P : HeightOneSpectrum (Places.Rinf K F)) :
    Zdiv S (Sum.inr P) = 0 := by
  rw [Zdiv, Finsupp.finsetSum_apply]
  simp

theorem Zdiv_union {S T : Finset (Places.Rfin K F →ₐ[K] K)} (h : Disjoint S T) :
    Zdiv (S ∪ T) = Zdiv S + Zdiv T :=
  Finset.sum_union h

theorem Zdiv_nonneg (S : Finset (Places.Rfin K F →ₐ[K] K)) : 0 ≤ Zdiv S := by
  rw [Finsupp.le_def]
  rintro (P | P)
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    rw [Zdiv_inl_ptP]
    split_ifs <;> simp
  · rw [Zdiv_inr]; simp

theorem Zdiv_injective {S T : Finset (Places.Rfin K F →ₐ[K] K)} (h : Zdiv S = Zdiv T) : S = T := by
  ext φ
  have e := congrArg (fun D : Places.Divisor K F => D (Sum.inl (ptP φ))) h
  simp only [Zdiv_inl_ptP] at e
  by_cases hS : φ ∈ S <;> by_cases hT : φ ∈ T <;> simp_all

theorem cnt_ne_zero_iff (P : HeightOneSpectrum (Places.Rfin K F)) {b : Places.Rfin K F} (hb : b ≠ 0) :
    Places.cnt P b ≠ 0 ↔ b ∈ P.asIdeal := by
  rw [Places.cnt, Associates.count_ne_zero_iff_dvd
    (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]) P.irreducible, Ideal.dvd_span_singleton]

theorem apply_eq_zero_of_ord {φ : Places.Rfin K F →ₐ[K] K} {t : Places.Rfin K F} (ht : t ≠ 0)
    (h : 1 ≤ Places.ord (ptP φ) (incB K F t)) : φ t = 0 := by
  rw [incB_apply, PlacesK.ord_algebraMap _ ht] at h
  exact mem_ptP.1 ((cnt_ne_zero_iff _ ht).1 (by omega))

variable {d : ℕ} {D : NuData K F d} {y : SymRing K (Places.Rfin K F) d →ₐ[K] K}

/-- **Divisor of a good section**: `div (sec y) = Zdiv Z(sec y) - Hn` (the `N` zeros are simple). -/
theorem div_sec (hy : y D.good ≠ 0) :
    PlacesK.div (incB K F (D.sec y)) = Zdiv (zeroFin (k := K) (D.sec y)) - D.Hn := by
  have hs0 := NuData.sec_ne_zero hy
  obtain ⟨hZ, hcard, -⟩ := NuData.zero_spec hy
  have hnot : ∀ φ, φ ∉ zeroFin (k := K) (D.sec y) → Places.cnt (ptP φ) (D.sec y) = 0 := fun φ hφ => by
    by_contra h
    exact hφ ((hZ φ).2 (mem_ptP.1 ((cnt_ne_zero_iff _ hs0).1 h)))
  have hpos : ∀ φ ∈ zeroFin (k := K) (D.sec y), Places.cnt (ptP φ) (D.sec y) ≠ 0 := fun φ hφ =>
    (cnt_ne_zero_iff _ hs0).2 (mem_ptP.2 ((hZ φ).1 hφ))
  have hT : (PlacesK.finite_cnt hs0).toFinset = (zeroFin (k := K) (D.sec y)).image ptP := by
    ext P
    obtain ⟨φ, rfl⟩ := exists_ptP P
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_image]
    constructor
    · intro h
      exact ⟨φ, by_contra fun hφ => h (hnot φ hφ), rfl⟩
    · rintro ⟨ψ, hψ, e⟩
      rw [← e]
      exact hpos ψ hψ
  have hsum : ∑ φ ∈ zeroFin (k := K) (D.sec y), Places.cnt (ptP φ) (D.sec y) =
      (zeroFin (k := K) (D.sec y)).card := by
    have h1 := PlacesK.finrank_quot_span (K := K) hs0
    rw [NuData.finrank_quot hy, hT, Finset.sum_image (fun a _ b _ e => ptP_injective e)] at h1
    simp only [deg_eq_one, mul_one] at h1
    rw [hcard]
    exact h1.symm
  have hone : ∀ φ ∈ zeroFin (k := K) (D.sec y), Places.cnt (ptP φ) (D.sec y) = 1 := by
    intro φ hφ
    by_contra hne
    have hlt : 1 < Places.cnt (ptP φ) (D.sec y) := by have := hpos φ hφ; omega
    have := Finset.sum_lt_sum (f := fun _ => 1) (g := fun ψ => Places.cnt (ptP ψ) (D.sec y))
      (s := zeroFin (k := K) (D.sec y)) (fun ψ hψ => Nat.one_le_iff_ne_zero.2 (hpos ψ hψ)) ⟨φ, hφ, hlt⟩
    rw [Finset.sum_const, smul_eq_mul, mul_one, hsum] at this
    exact lt_irrefl _ this
  ext (P | P)
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    have e1 : PlacesK.div (incB K F (D.sec y)) (Sum.inl (ptP φ)) = Places.ord (ptP φ) (incB K F (D.sec y)) :=
      PlacesK.div_apply _ _
    rw [e1, incB_apply, PlacesK.ord_algebraMap _ hs0, Finsupp.coe_sub, Pi.sub_apply, Zdiv_inl_ptP, D.Hn_inf (ptP φ)]
    split_ifs with h
    · rw [hone φ h]; simp
    · rw [hnot φ h]; simp
  · have e1 : PlacesK.div (incB K F (D.sec y)) (Sum.inr P) = Places.ord P (incB K F (D.sec y)) :=
      PlacesK.div_apply _ _
    rw [e1, Finsupp.coe_sub, Pi.sub_apply, Zdiv_inr, NuData.exactPole hy P]
    simp

theorem div_sec' (hy : y D.good ≠ 0) :
    PlacesK.div (incB K F (D.sec y)) = Zdiv (ptSet y) + Zdiv (D.nuF y) - D.Hn := by
  rw [div_sec hy, NuData.zeroFin_eq_union hy, Zdiv_union (NuData.disjoint_nuF D y)]

theorem incB_sec_ne_zero (hy : y D.good ≠ 0) : incB K F (D.sec y) ≠ 0 := fun h =>
  NuData.sec_ne_zero hy (incB_injective (h.trans (map_zero _).symm))

end Div

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_GenDiv =====
section

/-!
# S4-JacLaw, file O9d (G3b GenDiv): divisors of sections with reduced zero sets, and the rank condition

* `div_of_card`: `s ≠ 0` with exact pole divisor `Hn` and a zero set `Z` of size `deg Hn` has
  `div s = Zdiv Z - Hn` (all zeros simple).
* `hrank_of_const`: if moreover `Z \ A` is nonspecial (`ℓ = 1`), every `t ∈ L(Hn) ∩ B` vanishing on `A` is a
  multiple of `s` (the `hrank` hypothesis of `exists_nuData`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

section GenDiv

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {s : Places.Rfin K F} {Hn : Places.Divisor K F}

/-- **Divisor of a section with a full reduced zero set**: `div s = Zdiv Z - Hn`. -/
theorem div_of_card (hs0 : s ≠ 0) (hHn : IsInf Hn) (hs : ExactPoleH s Hn)
    {Z : Finset (Places.Rfin K F →ₐ[K] K)} (hZ : ∀ φ, φ ∈ Z ↔ φ s = 0) (hcard : (Z.card : ℤ) = Hn.deg) :
    PlacesK.div (incB K F s) = Zdiv Z - Hn := by
  have hnot : ∀ φ, φ ∉ Z → Places.cnt (ptP φ) s = 0 := fun φ hφ => by
    by_contra h
    exact hφ ((hZ φ).2 (mem_ptP.1 ((cnt_ne_zero_iff _ hs0).1 h)))
  have hpos : ∀ φ ∈ Z, Places.cnt (ptP φ) s ≠ 0 := fun φ hφ =>
    (cnt_ne_zero_iff _ hs0).2 (mem_ptP.2 ((hZ φ).1 hφ))
  have hT : (PlacesK.finite_cnt hs0).toFinset = Z.image ptP := by
    ext P
    obtain ⟨φ, rfl⟩ := exists_ptP P
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_image]
    constructor
    · intro h
      exact ⟨φ, by_contra fun hφ => h (hnot φ hφ), rfl⟩
    · rintro ⟨ψ, hψ, e⟩
      rw [← e]
      exact hpos ψ hψ
  have hsum : ∑ φ ∈ Z, Places.cnt (ptP φ) s = Z.card := by
    have h1 := PlacesK.finrank_quot_span (K := K) hs0
    have h2 := finrank_quot_of_exactPoleH hs0 hHn hs
    rw [hT, Finset.sum_image (fun a _ b _ e => ptP_injective e)] at h1
    simp only [deg_eq_one, mul_one] at h1
    have h3 : ((∑ φ ∈ Z, Places.cnt (ptP φ) s : ℕ) : ℤ) = Z.card := by rw [← h1, h2, ← hcard]
    exact_mod_cast h3
  have hone : ∀ φ ∈ Z, Places.cnt (ptP φ) s = 1 := by
    intro φ hφ
    by_contra hne
    have hlt : 1 < Places.cnt (ptP φ) s := by have := hpos φ hφ; omega
    have := Finset.sum_lt_sum (f := fun _ => 1) (g := fun ψ => Places.cnt (ptP ψ) s)
      (s := Z) (fun ψ hψ => Nat.one_le_iff_ne_zero.2 (hpos ψ hψ)) ⟨φ, hφ, hlt⟩
    rw [Finset.sum_const, smul_eq_mul, mul_one, hsum] at this
    exact lt_irrefl _ this
  ext (P | P)
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    have e1 : PlacesK.div (incB K F s) (Sum.inl (ptP φ)) = Places.ord (ptP φ) (incB K F s) :=
      PlacesK.div_apply _ _
    rw [e1, incB_apply, PlacesK.ord_algebraMap _ hs0, Finsupp.coe_sub, Pi.sub_apply, Zdiv_inl_ptP, hHn (ptP φ)]
    split_ifs with h
    · rw [hone φ h]; simp
    · rw [hnot φ h]; simp
  · have e1 : PlacesK.div (incB K F s) (Sum.inr P) = Places.ord P (incB K F s) :=
      PlacesK.div_apply _ _
    rw [e1, Finsupp.coe_sub, Pi.sub_apply, Zdiv_inr, hs P]
    simp

/-- **Rank condition from a nonspecial complement.** -/
theorem hrank_of_const (hs0 : s ≠ 0) (hHn : IsInf Hn) {Z A : Finset (Places.Rfin K F →ₐ[K] K)}
    (hdiv : PlacesK.div (incB K F s) = Zdiv Z - Hn) (hA : A ⊆ Z)
    (hC : ∀ f ∈ LFK K F (Zdiv (Z \ A)), ∃ c : K, f = algebraMap K F c) {t : Places.Rfin K F}
    (ht : t ∈ Linf K F Hn) (htA : ∀ φ ∈ A, φ t = 0) : ∃ c : K, t = c • s := by
  by_cases ht0 : t = 0
  · exact ⟨0, by simp [ht0]⟩
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  have ht' : incB K F t ≠ 0 := fun h => ht0 (incB_injective (h.trans (map_zero _).symm))
  set f := incB K F t / incB K F s with hf
  have hf0 : f ≠ 0 := div_ne_zero ht' hs'
  have hmul : incB K F t = f * incB K F s := by rw [hf, div_mul_cancel₀ _ hs']
  have h1 := PlacesK.div_mul (K := K) hf0 hs'
  rw [← hmul, hdiv] at h1
  have hZ : Zdiv Z = Zdiv A + Zdiv (Z \ A) := by
    rw [← Zdiv_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hA]
  have key : PlacesK.div f + Zdiv (Z \ A) = PlacesK.div (incB K F t) + Hn - Zdiv A := by
    rw [h1, hZ]; abel
  rw [mem_Linf, mem_LFK ht'] at ht
  have hmem : f ∈ LFK K F (Zdiv (Z \ A)) := by
    rw [mem_LFK hf0, key, Finsupp.le_def]
    rintro (P | P)
    · obtain ⟨φ, rfl⟩ := exists_ptP P
      have e1 : PlacesK.div (incB K F t) (Sum.inl (ptP φ)) = Places.ord (ptP φ) (incB K F t) :=
        PlacesK.div_apply _ _
      simp only [Finsupp.coe_sub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply, Finsupp.coe_zero, Pi.zero_apply]
      rw [e1, incB_apply, PlacesK.ord_algebraMap _ ht0, Zdiv_inl_ptP, hHn (ptP φ)]
      split_ifs with hφ
      · have := (cnt_ne_zero_iff _ ht0).2 (mem_ptP.2 (htA φ hφ))
        omega
      · omega
    · have h2 := (Finsupp.le_def.1 ht) (Sum.inr P)
      simp only [Finsupp.coe_sub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply, Finsupp.coe_zero,
        Pi.zero_apply] at h2 ⊢
      rw [Zdiv_inr]
      omega
  obtain ⟨c, hc⟩ := hC f hmem
  refine ⟨c, incB_injective ?_⟩
  rw [map_smul, hmul, hc, Algebra.smul_def]

end GenDiv

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacComplete_FibG =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `FibG` (generic fibres of a function with a simple zero or pole)

* `ord_zero'`, `ord_algebraMap_K`, `placeVal_eq_exp_of_ord`: small facts on `Place.ord`.
* `transcendental_of_ord_ne_zero`: a function with a nonzero order somewhere is transcendental over `K`.
* `exists_fib_le_one_gen`: for `h` with the `GenF` package, `h - μ` has only simple zeros for all but finitely many `μ`
  (fibres of the coordinate `h` of `GenF K F h`, `exists_fib_card` + `div_of_card`, transported by `ord_genPlace`).
* **`exists_fib_le_one`**: if `ord_P h = 1` for some place `P`, there is a finite `B ⊆ K` with
  `ord_R (h - μ) ≤ 1` at every place `R` for all `μ ∉ B`.
* **`exists_fib_le_one_of_pole`**: the same when `ord_P h = -1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial IntermediateField
open scoped WithZero

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw

section FibG

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem ord_zero' (R : Place K F) : R.ord (0 : F) = 0 := by
  rw [ord_eq_neg_log]; simp

theorem ord_algebraMap_K (R : Place K F) {c : K} (hc : c ≠ 0) : R.ord (algebraMap K F c) = 0 := by
  rw [ord_eq_neg_log, placeVal_algebraMap R hc]; simp

theorem placeVal_eq_exp_of_ord {P : Place K F} {h : F} (hh0 : h ≠ 0) {n : ℤ} (hP : P.ord h = n) :
    placeVal P h = WithZero.exp (-n) := by
  rw [ord_eq_neg_log] at hP
  rw [← WithZero.exp_log ((Valuation.ne_zero_iff (placeVal P)).2 hh0), ← hP, neg_neg]

variable [IsAlgClosed K]

theorem transcendental_of_ord_ne_zero {h : F} {P : Place K F} (hP : P.ord h ≠ 0) : Transcendental K h := by
  intro halg
  have hint : IsIntegral K h := halg.isIntegral
  have hdeg : (minpoly K h).natDegree = 1 :=
    natDegree_eq_of_degree_eq_some (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint))
  obtain ⟨c, hc⟩ := RingHom.mem_range.1 (minpoly.natDegree_eq_one_iff.1 hdeg)
  subst hc
  apply hP
  by_cases hc0 : c = 0
  · rw [hc0, map_zero, ord_zero']
  · exact ord_algebraMap_K P hc0

section Gen

variable (h : F) [Fact (Transcendental K h)] [FiniteDimensional K⟮h⟯ F] [Algebra.IsSeparable K⟮h⟯ F]

theorem incB_genF (μ : K) :
    incB K (GenF K F h) (algebraMap K[X] (Rfin K (GenF K F h)) (X - C μ)) =
      genEquiv K F h (h - algebraMap K F μ) := by
  rw [incB_apply, ← IsScalarTower.algebraMap_apply, genAlg_apply, map_sub, aeval_X, aeval_C]

theorem Zdiv_le_one {G : Type*} [Field G] [Algebra K G] [Algebra K[X] G] [Algebra (RatFunc K) G]
    [IsScalarTower K[X] (RatFunc K) G] [IsScalarTower K K[X] G] [FunctionField K G]
    [Algebra.IsSeparable (RatFunc K) G] (Z : Finset (Rfin K G →ₐ[K] K)) (R : Place K G) : Zdiv Z R ≤ 1 := by
  rcases R with P | P
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    rw [Zdiv_inl_ptP]
    split_ifs <;> omega
  · rw [Zdiv_inr]; omega

/-- **Generic fibres of the coordinate of `GenF K F h` are reduced.** -/
theorem exists_fib_le_one_gen : ∃ B : Finset K, ∀ μ ∉ B, ∀ R : Place K F,
    R.ord (h - algebraMap K F μ) ≤ 1 := by
  obtain ⟨a, ha, hfib⟩ := exists_fib_card (K := K) (F := GenF K F h)
  refine ⟨a.roots.toFinset, fun μ hμ R => ?_⟩
  have haμ : a.eval μ ≠ 0 := fun e => hμ (Multiset.mem_toFinset.2 ((mem_roots ha).2 e))
  obtain ⟨hfin, hcard⟩ := hfib μ haμ
  have hq0 : (X - C μ : K[X]) ≠ 0 := X_sub_C_ne_zero μ
  have hs0 : algebraMap K[X] (Rfin K (GenF K F h)) (X - C μ) ≠ 0 :=
    (map_ne_zero_iff _ algebraMap_poly_injective).2 hq0
  have hZs : ∀ φ, φ ∈ hfin.toFinset ↔ φ (algebraMap K[X] (Rfin K (GenF K F h)) (X - C μ)) = 0 := by
    intro φ
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, apply_poly φ (X - C μ), eval_sub, eval_X, eval_C, sub_eq_zero]
  have e2 : Nat.card {φ : Rfin K (GenF K F h) →ₐ[K] K // φ (xB K (GenF K F h)) = μ} = hfin.toFinset.card :=
    Nat.card_eq_card_finite_toFinset hfin
  have hcardZ : (hfin.toFinset.card : ℤ) =
      (poleDiv (K := K) (incB K (GenF K F h) (algebraMap K[X] (Rfin K (GenF K F h)) (X - C μ)))).deg := by
    rw [deg_poleDiv_poly hq0, natDegree_X_sub_C, one_mul, ← hcard, e2]
  have hdiv := div_of_card hs0 (isInf_poleDiv _) (exactPoleH_poly hq0) hZs hcardZ
  have key : (genPlace h R).ord (incB K (GenF K F h) (algebraMap K[X] (Rfin K (GenF K F h)) (X - C μ))) ≤ 1 := by
    have e := congrArg (fun D : Places.Divisor K (GenF K F h) => D (genPlace h R)) hdiv
    simp only [PlacesK.div_apply, Finsupp.coe_sub, Pi.sub_apply] at e
    rw [e]
    have h1 := Zdiv_le_one hfin.toFinset (genPlace h R)
    have h2 : 0 ≤ poleDiv (K := K) (incB K (GenF K F h)
        (algebraMap K[X] (Rfin K (GenF K F h)) (X - C μ))) (genPlace h R) := by
      simp only [poleDiv, Finsupp.sup_apply]
      exact le_sup_right
    omega
  rwa [incB_genF, ord_genPlace] at key

end Gen

/-- **Generic fibres through a simple zero.** -/
theorem exists_fib_le_one {h : F} {P : Place K F} (hP : P.ord h = 1) :
    ∃ B : Finset K, ∀ μ ∉ B, ∀ R : Place K F, R.ord (h - algebraMap K F μ) ≤ 1 := by
  have hh : Transcendental K h := transcendental_of_ord_ne_zero (P := P) (by omega)
  have hh0 : h ≠ 0 := fun e => hh (e ▸ isAlgebraic_zero)
  have : Fact (Transcendental K h) := ⟨hh⟩
  have : FiniteDimensional K⟮h⟯ F :=
    finiteDimensional_adjoin_of_transcendental (x := algebraMap K[X] F X) hh
  have : Algebra.IsSeparable K⟮h⟯ F :=
    isSeparable_adjoin_of_val (x := algebraMap K[X] F X) hh (placeVal P) (placeVal_eq_exp_of_ord hh0 hP)
  exact exists_fib_le_one_gen h

/-- **Generic fibres through a simple pole.** -/
theorem exists_fib_le_one_of_pole {h : F} {P : Place K F} (hP : P.ord h = -1) :
    ∃ B : Finset K, ∀ μ ∉ B, ∀ R : Place K F, R.ord (h - algebraMap K F μ) ≤ 1 := by
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [ord_zero'] at hP
    omega
  have hinv : P.ord h⁻¹ = 1 := by
    have := PlacesK.Place.ord_mul P hh0 (inv_ne_zero hh0)
    rw [mul_inv_cancel₀ hh0, PlacesK.Place.ord_one (K := K) (F := F)] at this
    omega
  obtain ⟨B, hB⟩ := exists_fib_le_one hinv
  refine ⟨insert 0 (B.image (·⁻¹)), fun μ hμ R => ?_⟩
  have hμ0 : μ ≠ 0 := fun e => hμ (e ▸ Finset.mem_insert_self _ _)
  have hμB : μ⁻¹ ∉ B := fun e => hμ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨μ⁻¹, e, inv_inv μ⟩))
  have h1 := hB μ⁻¹ hμB R
  have hc0 : algebraMap K F μ ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).2 hμ0
  by_cases hhμ : h - algebraMap K F μ = 0
  · rw [hhμ, ord_zero']; omega
  by_cases hR : 0 < R.ord h
  · by_contra hcon
    have hnh : -h ≠ 0 := neg_ne_zero.2 hh0
    have hsum : h - algebraMap K F μ + -h = -algebraMap K F μ := by ring
    have hsum0 : h - algebraMap K F μ + -h ≠ 0 := by rw [hsum]; exact neg_ne_zero.2 hc0
    have h2 := PlacesK.Place.ord_add (K := K) (F := F) R hhμ hnh hsum0
    rw [hsum, PlacesK.Place.ord_neg (K := K) (F := F), PlacesK.Place.ord_neg (K := K) (F := F), ord_algebraMap_K R hμ0] at h2
    omega
  · have hm : h⁻¹ - algebraMap K F μ⁻¹ ≠ 0 := by
      intro e
      apply hhμ
      rw [map_inv₀, sub_eq_zero] at e
      rw [sub_eq_zero, ← inv_inv h, e, inv_inv]
    have hch : -(algebraMap K F μ * h) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hc0 hh0)
    have e : h - algebraMap K F μ = (-(algebraMap K F μ * h)) * (h⁻¹ - algebraMap K F μ⁻¹) := by
      rw [map_inv₀]
      field_simp
      ring
    rw [e, PlacesK.Place.ord_mul R hch hm, PlacesK.Place.ord_neg (K := K) (F := F), PlacesK.Place.ord_mul R hc0 hh0,
      ord_algebraMap_K R hμ0]
    omega

end FibG

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacComplete_SecA =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `SecA` (a function with only simple zeros through a given point)

* `ord_add_eq_of_lt'`: strict ultrametric equality for `Place.ord`.
* `cnt_eq_ord`: `cnt` at `ptP φ` is the order of `incB`.
* `exists_cnt_eq_one`: a uniformizer at a closed point; `finite_zero`: finitely many zeros.
* `exists_avoid`: prime avoidance: an element vanishing at `φ0` but at no point of a finite `S ∌ φ0`.
* **`exists_simple`**: for every closed point `φ0` of `Rfin` there is `g ≠ 0` with `φ0 g = 0` and only simple
  zeros (`g = t + μ (t·t + w·w·w)`, `t` a uniformizer at `φ0`, `w` vanishing at `φ0` but not at the other zeros of `t`,
  `μ` generic for the fibres of `(t·t + w·w·w)/t`, which has a simple zero at `φ0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial
open scoped WithZero

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw

section SecA

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem ord_add_eq_of_lt' (R : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : R.ord f < R.ord g) :
    R.ord (f + g) = R.ord f := by
  have hvf : placeVal R f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  have hvg : placeVal R g ≠ 0 := (Valuation.ne_zero_iff _).mpr hg
  rw [ord_eq_neg_log, ord_eq_neg_log] at h
  have hlt : placeVal R g < placeVal R f := (WithZero.log_lt_log hvg hvf).1 (by omega)
  rw [ord_eq_neg_log, ord_eq_neg_log, Valuation.map_add_eq_of_lt_left _ hlt]

variable [IsAlgClosed K]

theorem cnt_eq_ord (φ : Rfin K F →ₐ[K] K) {b : Rfin K F} (hb : b ≠ 0) :
    (Places.cnt (ptP φ) b : ℤ) = Places.Place.ord (Sum.inl (ptP φ) : Place K F) (incB K F b) := by
  show (Places.cnt (ptP φ) b : ℤ) = Places.ord (ptP φ) (incB K F b)
  rw [incB_apply, PlacesK.ord_algebraMap _ hb]

theorem incB_ne_zero {b : Rfin K F} (hb : b ≠ 0) : incB K F b ≠ 0 := fun h =>
  hb (incB_injective (h.trans (map_zero _).symm))

theorem exists_cnt_eq_one (φ : Rfin K F →ₐ[K] K) : ∃ t : Rfin K F, t ≠ 0 ∧ Places.cnt (ptP φ) t = 1 := by
  obtain ⟨π, hπ⟩ := (ptP φ).intValuation_exists_uniformizer
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨π, hπ0, ?_⟩
  have h2 : Places.ord (ptP φ) (algebraMap (Rfin K F) F π) = 1 := by
    rw [Places.ord, HeightOneSpectrum.valuation_of_algebraMap, hπ, WithZero.log_exp, neg_neg]
  rw [PlacesK.ord_algebraMap _ hπ0] at h2
  exact_mod_cast h2

theorem finite_zero {t : Rfin K F} (ht0 : t ≠ 0) : {φ : Rfin K F →ₐ[K] K | φ t = 0}.Finite := by
  refine ((PlacesK.finite_cnt ht0).preimage ptP_injective.injOn).subset fun φ hφ => ?_
  exact (cnt_ne_zero_iff _ ht0).2 (mem_ptP.2 hφ)

theorem exists_avoid (φ0 : Rfin K F →ₐ[K] K) (S : Finset (Rfin K F →ₐ[K] K)) (hS : φ0 ∉ S) :
    ∃ w : Rfin K F, φ0 w = 0 ∧ ∀ φ ∈ S, φ w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hsub : ((RingHom.ker φ0 : Ideal (Rfin K F)) : Set (Rfin K F)) ⊆
      ⋃ φ ∈ (↑S : Set (Rfin K F →ₐ[K] K)), ((RingHom.ker φ : Ideal (Rfin K F)) : Set (Rfin K F)) := by
    intro w hw
    obtain ⟨φ, hφ, hφw⟩ := hcon w (RingHom.mem_ker.1 hw)
    exact Set.mem_iUnion₂.2 ⟨φ, hφ, RingHom.mem_ker.2 hφw⟩
  obtain ⟨φ, hφ, hle⟩ := (Ideal.subset_union_prime (s := S)
    (f := fun φ : Rfin K F →ₐ[K] K => RingHom.ker φ) φ0 φ0
    (fun i _ _ _ => RingHom.ker_isPrime i)).1 hsub
  apply hS
  have e : φ = φ0 := by
    refine AlgHom.ext fun b => ?_
    have hb : b - algebraMap K (Rfin K F) (φ0 b) ∈ RingHom.ker φ0 := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have h1 : φ (b - algebraMap K (Rfin K F) (φ0 b)) = 0 := RingHom.mem_ker.1 (hle hb)
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h1
    exact h1
  rw [← e]
  exact hφ

/-- **A function with only simple zeros through a given closed point.** -/
theorem exists_simple (φ0 : Rfin K F →ₐ[K] K) :
    ∃ g : Rfin K F, g ≠ 0 ∧ φ0 g = 0 ∧ ∀ φ, Places.cnt (ptP φ) g ≤ 1 := by
  obtain ⟨t, ht0, ht1⟩ := exists_cnt_eq_one φ0
  have hφ0t : φ0 t = 0 := mem_ptP.1 ((cnt_ne_zero_iff _ ht0).1 (by omega))
  have hfin := finite_zero ht0
  obtain ⟨w, hw0, hwS⟩ := exists_avoid φ0 (hfin.toFinset.erase φ0) (Finset.notMem_erase φ0 _)
  set P0 : Place K F := Sum.inl (ptP φ0) with hP0
  set T := incB K F t with hT
  have hT0 : T ≠ 0 := incB_ne_zero ht0
  have hT1 : P0.ord T = 1 := (cnt_eq_ord φ0 ht0).symm.trans (by exact_mod_cast ht1)
  set v : Rfin K F := t * t + w * w * w with hv
  set V := incB K F v with hV
  have hVe : V = T * T + incB K F w * incB K F w * incB K F w := by rw [hV, hv, map_add, map_mul, map_mul, map_mul]
  have hTT : P0.ord (T * T) = 2 := by
    have := PlacesK.Place.ord_mul P0 hT0 hT0
    omega
  have hV2 : P0.ord V = 2 := by
    by_cases hw : w = 0
    · have e : V = T * T := by rw [hVe, hw, map_zero, mul_zero, add_zero]
      rw [e]
      exact hTT
    · have hW0 : incB K F w ≠ 0 := incB_ne_zero hw
      have hW1 : 1 ≤ P0.ord (incB K F w) := by
        have h0 : (Places.cnt (ptP φ0) w : ℤ) = P0.ord (incB K F w) := cnt_eq_ord φ0 hw
        have := (cnt_ne_zero_iff (ptP φ0) hw).2 (mem_ptP.2 hw0)
        omega
      have h3a := PlacesK.Place.ord_mul P0 hW0 hW0
      have h3 := PlacesK.Place.ord_mul P0 (mul_ne_zero hW0 hW0) hW0
      rw [hVe, ord_add_eq_of_lt' P0 (mul_ne_zero hT0 hT0) (mul_ne_zero (mul_ne_zero hW0 hW0) hW0) (by omega)]
      exact hTT
  have hV0 : V ≠ 0 := by
    intro e
    rw [e, ord_zero'] at hV2
    omega
  set h := V / T with hh
  have hh0 : h ≠ 0 := div_ne_zero hV0 hT0
  have e1 : h * T = V := div_mul_cancel₀ _ hT0
  have hh1 : P0.ord h = 1 := by
    have := PlacesK.Place.ord_mul P0 hh0 hT0
    rw [e1, hV2, hT1] at this
    omega
  obtain ⟨B, hB⟩ := exists_fib_le_one hh1
  obtain ⟨μ, hμ⟩ := Infinite.exists_notMem_finset (insert 0 (B.image fun b : K => -b⁻¹))
  have hμ0 : μ ≠ 0 := fun e => hμ (e ▸ Finset.mem_insert_self _ _)
  have hμB : -μ⁻¹ ∉ B := fun e => hμ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-μ⁻¹, e, by
    simp⟩))
  have hc0 : algebraMap K F μ ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).2 hμ0
  set g : Rfin K F := t + algebraMap K (Rfin K F) μ * v with hg
  have hG : incB K F g = T + algebraMap K F μ * V := by
    rw [hg, map_add, map_mul, AlgHom.commutes]
  have e2 : algebraMap K F μ * algebraMap K F μ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hμ0, map_one]
  have eG : incB K F g = T * (algebraMap K F μ * (h - algebraMap K F (-μ⁻¹))) := by
    rw [hG, map_neg]
    linear_combination (-(algebraMap K F μ)) * e1 + (-T) * e2
  have hcV : P0.ord (algebraMap K F μ * V) = 2 := by
    have := PlacesK.Place.ord_mul P0 hc0 hV0
    rw [ord_algebraMap_K P0 hμ0, hV2] at this
    omega
  have hG1 : P0.ord (incB K F g) = 1 := by
    rw [hG, ord_add_eq_of_lt' P0 hT0 (mul_ne_zero hc0 hV0) (by omega), hT1]
  have hG0 : incB K F g ≠ 0 := by
    intro e
    rw [e, ord_zero'] at hG1
    omega
  have hg0 : g ≠ 0 := by
    rintro e
    exact hG0 (by rw [e, map_zero])
  refine ⟨g, hg0, ?_, fun φ => ?_⟩
  · simp [hg, hv, hφ0t, hw0]
  have hcnt := cnt_eq_ord φ hg0
  by_cases hφ : φ = φ0
  · rw [hφ] at hcnt ⊢
    have : (Places.cnt (ptP φ0) g : ℤ) = 1 := hcnt.trans hG1
    omega
  by_cases hφt : φ t = 0
  · have hφS : φ ∈ hfin.toFinset.erase φ0 := Finset.mem_erase.2 ⟨hφ, hfin.mem_toFinset.2 hφt⟩
    have hφw := hwS φ hφS
    have hφg : φ g ≠ 0 := by
      simp [hg, hv, hφt, hμ0, hφw]
    have : Places.cnt (ptP φ) g = 0 := by
      by_contra hne
      exact hφg (mem_ptP.1 ((cnt_ne_zero_iff _ hg0).1 hne))
    omega
  · have htc : Places.cnt (ptP φ) t = 0 := by
      by_contra hne
      exact hφt (mem_ptP.1 ((cnt_ne_zero_iff _ ht0).1 hne))
    have hTφ : Places.Place.ord (Sum.inl (ptP φ) : Place K F) T = 0 := by
      have := cnt_eq_ord φ ht0
      rw [htc, Nat.cast_zero] at this
      exact this.symm
    have hm : h - algebraMap K F (-μ⁻¹) ≠ 0 := by
      intro e
      apply hG0
      rw [eG, e, mul_zero, mul_zero]
    have hle := hB (-μ⁻¹) hμB (Sum.inl (ptP φ))
    rw [eG, PlacesK.Place.ord_mul _ hT0 (mul_ne_zero hc0 hm), PlacesK.Place.ord_mul _ hc0 hm,
      ord_algebraMap_K _ hμ0, hTφ] at hcnt
    omega

end SecA

end RamanujanPetersson.JacComplete

end


