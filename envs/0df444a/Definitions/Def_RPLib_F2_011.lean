-- Prove2me | Definitions.Def_RPLib_F2_011
-- name    : RPLib_F2_011
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T08:28:31.742182+00:00
-- url     : https://prove2.me/theorems/482f811d-73f7-472a-b7aa-9e3e88261c95
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 011 of 70
-- statement:
--   File 011 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_Uniq`: S4-JacLaw, file O8a: uniqueness of `ν`, supports of points, padding and sum maps
--   * `S4.Def_RP_JacLaw_Step`: S4-JacLaw, file O8b: the set-level negation `nuF` and the step map `nuStep`
--   * `S4.Def_RP_JacLaw_Div`: S4-JacLaw, file O8d: divisors of good sections
--   * `S4.Def_RP_JacLaw_GenDiv`: S4-JacLaw, file O9d (G3b GenDiv): divisors of sections with reduced zero sets, and the rank condition
--   * `S4.Def_RP_JacComplete_FibG`: The Jacobian (unit S4-JacComplete), part `FibG` (generic fibres of a function with a simple zero or pole)
--   * `S4.Def_RP_JacComplete_SecA`: The Jacobian (unit S4-JacComplete), part `SecA` (a function with only simple zeros through a given point)
--   * `S4.Def_RP_JacComplete_SecB`: The Jacobian (unit S4-JacComplete), part `SecB` (sections with exact poles and a full reduced zero set)
--   * `S4.Def_RP_JacLaw_Bridge`: S4-JacLaw, file O10a: open immersions from maps that are inverse at points
--   * `S4.Def_RP_JacChunkA_Pts`: Group chunk A0 (unit S4-JacChunkA): closed points over an algebraically closed field
--   * `S4.Def_RP_JacChunkA_Trans`: Group chunk A1 (unit S4-JacChunkA): translations of a strict group chunk
--   * `S4.Def_RP_JacLaw_Sch`: S4-JacLaw, file O10b: from algebraic chunk data on `R` to a `StrictChunk` on `Spec R`
--   * `S4.Def_RP_JacLaw_ShrinkA`: S4-JacLaw, file O10d-1: tools for shrinking a chunk
--   * `S4.Def_RP_JacLaw_Shrink`: S4-JacLaw, file O10d-2: from a birational law on a domain `S` to an `AffChunk` on `S[1/u0]`
--   * `S4.Def_RP_JacLaw_ShrinkC`: S4-JacLaw, file O10d-3: the `AffChunk` on `S[1/u0]`
--   * `S4.Def_RP_JacLaw_Law`: S4-JacLaw, file O8c: the law maps `m`, `r` and the inverse identities
--   * `S4.Def_RP_JacLaw_Assoc`: S4-JacLaw, file O8e: associativity of the law
--   * `S4.Def_RP_JacLaw_Sep`: S4-JacLaw, file O9 (part Sep): Lagrange elements, separating elements, reduced quotients
--   * `S4.Def_RP_JacLaw_GenNS`: S4-JacLaw, file O9e (G4 GenNS): nonspecial sets of points
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_009

/-!
# Ramanujan-Petersson curve library (flat edition), file 011 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_Uniq`: S4-JacLaw, file O8a: uniqueness of `ν`, supports of points, padding and sum maps
* `S4.Def_RP_JacLaw_Step`: S4-JacLaw, file O8b: the set-level negation `nuF` and the step map `nuStep`
* `S4.Def_RP_JacLaw_Div`: S4-JacLaw, file O8d: divisors of good sections
* `S4.Def_RP_JacLaw_GenDiv`: S4-JacLaw, file O9d (G3b GenDiv): divisors of sections with reduced zero sets, and the rank condition
* `S4.Def_RP_JacComplete_FibG`: The Jacobian (unit S4-JacComplete), part `FibG` (generic fibres of a function with a simple zero or pole)
* `S4.Def_RP_JacComplete_SecA`: The Jacobian (unit S4-JacComplete), part `SecA` (a function with only simple zeros through a given point)
* `S4.Def_RP_JacComplete_SecB`: The Jacobian (unit S4-JacComplete), part `SecB` (sections with exact poles and a full reduced zero set)
* `S4.Def_RP_JacLaw_Bridge`: S4-JacLaw, file O10a: open immersions from maps that are inverse at points
* `S4.Def_RP_JacChunkA_Pts`: Group chunk A0 (unit S4-JacChunkA): closed points over an algebraically closed field
* `S4.Def_RP_JacChunkA_Trans`: Group chunk A1 (unit S4-JacChunkA): translations of a strict group chunk
* `S4.Def_RP_JacLaw_Sch`: S4-JacLaw, file O10b: from algebraic chunk data on `R` to a `StrictChunk` on `Spec R`
* `S4.Def_RP_JacLaw_ShrinkA`: S4-JacLaw, file O10d-1: tools for shrinking a chunk
* `S4.Def_RP_JacLaw_Shrink`: S4-JacLaw, file O10d-2: from a birational law on a domain `S` to an `AffChunk` on `S[1/u0]`
* `S4.Def_RP_JacLaw_ShrinkC`: S4-JacLaw, file O10d-3: the `AffChunk` on `S[1/u0]`
* `S4.Def_RP_JacLaw_Law`: S4-JacLaw, file O8c: the law maps `m`, `r` and the inverse identities
* `S4.Def_RP_JacLaw_Assoc`: S4-JacLaw, file O8e: associativity of the law
* `S4.Def_RP_JacLaw_Sep`: S4-JacLaw, file O9 (part Sep): Lagrange elements, separating elements, reduced quotients
* `S4.Def_RP_JacLaw_GenNS`: S4-JacLaw, file O9e (G4 GenNS): nonspecial sets of points
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

-- ===== S4.Def_RP_JacComplete_SecB =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `SecB` (sections with exact poles and a full reduced zero set)

* `card_of_cnt_le_one`: converse of `div_of_card`: if all zeros of `s` are simple, `#Z = deg Hn`.
* `exactPoleH_of_nonpos`: no zeros at infinity gives `ExactPoleH s (poleDiv s)`.
* `ord_inr_prod`: `q(x) = ∏_{c ∈ Λ} (x - c)` has a pole of order `≥ #Λ` at every infinite place.
* `secOf g Λ := g · q_Λ(x)`; **`exists_secOf`**: for `g ≠ 0` with simple zeros, for all large generic `Λ`,
  `secOf g Λ` has exact poles, only simple zeros, and zero set `Z(g) ∪ {x ∈ Λ}`.
* **`exists_secP`**: through every closed point there is such a family of sections.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial
open scoped WithZero

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw

section SecB

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **Converse of `div_of_card`.** -/
theorem card_of_cnt_le_one {s : Rfin K F} {Hn : Places.Divisor K F} (hs0 : s ≠ 0) (hHn : IsInf Hn)
    (hs : ExactPoleH s Hn) (h1 : ∀ φ, Places.cnt (ptP φ) s ≤ 1) {Z : Finset (Rfin K F →ₐ[K] K)}
    (hZ : ∀ φ, φ ∈ Z ↔ φ s = 0) : (Z.card : ℤ) = Hn.deg := by
  have hT : (PlacesK.finite_cnt hs0).toFinset = Z.image ptP := by
    ext P
    obtain ⟨φ, rfl⟩ := exists_ptP P
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_image]
    constructor
    · intro h
      exact ⟨φ, (hZ φ).2 (mem_ptP.1 ((cnt_ne_zero_iff _ hs0).1 h)), rfl⟩
    · rintro ⟨ψ, hψ, e⟩
      rw [← e]
      exact (cnt_ne_zero_iff _ hs0).2 (mem_ptP.2 ((hZ ψ).1 hψ))
  have hA := PlacesK.finrank_quot_span (K := K) hs0
  have h2 := finrank_quot_of_exactPoleH hs0 hHn hs
  rw [hT, Finset.sum_image (fun a _ b _ e => ptP_injective e)] at hA
  simp only [deg_eq_one, mul_one] at hA
  have hone : ∀ φ ∈ Z, Places.cnt (ptP φ) s = 1 := fun φ hφ => by
    have := (cnt_ne_zero_iff _ hs0).2 (mem_ptP.2 ((hZ φ).1 hφ))
    have := h1 φ
    omega
  rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one] at hA
  rw [← hA]
  exact h2

theorem exactPoleH_of_nonpos {s : Rfin K F} (hs : ∀ Q : HeightOneSpectrum (Rinf K F), Places.ord Q (incB K F s) ≤ 0) :
    ExactPoleH s (poleDiv (K := K) (incB K F s)) := by
  intro P
  have := hs P
  simp only [poleDiv, Finsupp.sup_apply, Finsupp.neg_apply, PlacesK.div_apply, Places.Place.ord_inr,
    Finsupp.coe_zero, Pi.zero_apply]
  omega

theorem ord_inr_x_sub (Q : HeightOneSpectrum (Rinf K F)) (c : K) :
    Places.ord Q (algebraMap K[X] F X - algebraMap K F c) ≤ -1 := by
  have hx := one_lt_placeVal_inr_x (K := K) (F := F) Q
  have hc : placeVal (Sum.inr Q : Place K F) (algebraMap K F c) < placeVal (Sum.inr Q : Place K F) (algebraMap K[X] F X) := by
    by_cases hc0 : c = 0
    · rw [hc0, map_zero, map_zero]; exact lt_trans zero_lt_one hx
    · rw [placeVal_algebraMap _ hc0]; exact hx
  have e := Valuation.map_sub_eq_of_lt_left (placeVal (Sum.inr Q : Place K F)) hc
  have hx0 : placeVal (Sum.inr Q : Place K F) (algebraMap K[X] F X) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog : (0 : ℤ) < WithZero.log (placeVal (Sum.inr Q : Place K F) (algebraMap K[X] F X)) := by
    have := (WithZero.log_lt_log one_ne_zero hx0).2 hx
    rwa [WithZero.log_one] at this
  have h := ord_eq_neg_log (Sum.inr Q : Place K F) (algebraMap K[X] F X - algebraMap K F c)
  change Places.ord Q _ = _ at h
  rw [e] at h
  omega

theorem ord_inr_prodF (Q : HeightOneSpectrum (Rinf K F)) (Λ : Finset K) :
    Places.ord Q (∏ c ∈ Λ, (algebraMap K[X] F X - algebraMap K F c)) ≤ -(Λ.card : ℤ) := by
  have hne : ∀ b : K, algebraMap K[X] F X - algebraMap K F b ≠ 0 := fun b h0 => by
    have := ord_inr_x_sub (F := F) Q b
    rw [h0] at this
    simp [Places.ord] at this
  induction Λ using Finset.induction_on with
  | empty => simp [Places.ord]
  | insert a Λ ha ih =>
    have h1 := ord_inr_x_sub (F := F) Q a
    have hP : ∏ c ∈ Λ, (algebraMap K[X] F X - algebraMap K F c) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun b _ => hne b
    rw [Finset.prod_insert ha, PlacesK.ord_mul Q (hne a) hP, Finset.card_insert_of_notMem ha]
    push_cast
    omega

theorem incB_prod (Λ : Finset K) :
    incB K F (algebraMap K[X] (Rfin K F) (∏ c ∈ Λ, (X - C c))) =
      ∏ c ∈ Λ, (algebraMap K[X] F X - algebraMap K F c) := by
  rw [incB_apply, ← IsScalarTower.algebraMap_apply, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [map_sub, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

theorem ord_inr_prod (Q : HeightOneSpectrum (Rinf K F)) (Λ : Finset K) :
    Places.ord Q (incB K F (algebraMap K[X] (Rfin K F) (∏ c ∈ Λ, (X - C c)))) ≤ -(Λ.card : ℤ) := by
  rw [incB_prod]
  exact ord_inr_prodF Q Λ

/-- `g · ∏_{c ∈ Λ} (x - c)`. -/
noncomputable def secOf (g : Rfin K F) (Λ : Finset K) : Rfin K F :=
  g * algebraMap K[X] (Rfin K F) (∏ c ∈ Λ, (X - C c))

theorem secOf_ne_zero {g : Rfin K F} (hg0 : g ≠ 0) (Λ : Finset K) : secOf g Λ ≠ 0 :=
  mul_ne_zero hg0 ((map_ne_zero_iff _ algebraMap_poly_injective).2
    (Finset.prod_ne_zero_iff.2 fun c _ => X_sub_C_ne_zero c))

theorem apply_secOf (φ : Rfin K F →ₐ[K] K) (g : Rfin K F) (Λ : Finset K) :
    φ (secOf g Λ) = 0 ↔ φ g = 0 ∨ φ (xB K F) ∈ Λ := by
  rw [secOf, map_mul, mul_eq_zero, apply_poly, eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

/-- **Sections through the zeros of `g` with exact poles and simple zeros.** -/
theorem exists_secOf {g : Rfin K F} (hg0 : g ≠ 0) (hg1 : ∀ φ, Places.cnt (ptP φ) g ≤ 1) :
    ∃ a : K[X], a ≠ 0 ∧ ∃ N : ℕ, ∀ Λ : Finset K, (∀ c ∈ Λ, a.eval c ≠ 0) → N ≤ Λ.card →
      ExactPoleH (secOf g Λ) (poleDiv (K := K) (incB K F (secOf g Λ))) ∧
        ∀ φ, Places.cnt (ptP φ) (secOf g Λ) ≤ 1 := by
  obtain ⟨a0, ha0, hfib⟩ := exists_fib_data (K := K) (F := F)
  set Zg := (finite_zero hg0).toFinset with hZg
  refine ⟨a0 * ∏ φ ∈ Zg, (X - C (φ (xB K F))), mul_ne_zero ha0 (Finset.prod_ne_zero_iff.2 fun φ _ =>
    X_sub_C_ne_zero _), ∑ Q ∈ (Set.finite_univ (α := HeightOneSpectrum (Rinf K F))).toFinset,
    (Places.ord Q (incB K F g)).toNat, fun Λ hΛ hN => ?_⟩
  have hΛ0 : ∀ c ∈ Λ, a0.eval c ≠ 0 := fun c hc => by
    have h := hΛ c hc
    rw [eval_mul] at h
    exact left_ne_zero_of_mul h
  have hΛg : ∀ c ∈ Λ, ∀ φ : Rfin K F →ₐ[K] K, φ g = 0 → φ (xB K F) ≠ c := fun c hc φ hφ e => by
    have h := hΛ c hc
    rw [eval_mul, eval_prod] at h
    exact h (mul_eq_zero.2 (Or.inr (Finset.prod_eq_zero ((finite_zero hg0).mem_toFinset.2 hφ)
      (by rw [eval_sub, eval_X, eval_C, e, sub_self]))))
  set q : K[X] := ∏ c ∈ Λ, (X - C c) with hq
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => X_sub_C_ne_zero c
  have hsq0 : algebraMap K[X] (Rfin K F) q ≠ 0 := (map_ne_zero_iff _ algebraMap_poly_injective).2 hq0
  obtain ⟨s', Zq, -, -, -, -, hZx, hZc⟩ := hfib Λ hΛ0
  have hZq : ∀ φ, φ ∈ Zq ↔ φ (algebraMap K[X] (Rfin K F) q) = 0 := fun φ => by
    rw [hZx, apply_poly φ q, hq, eval_prod, Finset.prod_eq_zero_iff]
    simp [sub_eq_zero]
  have hqdeg : q.natDegree = Λ.card := by
    rw [hq, natDegree_prod _ _ fun c _ => X_sub_C_ne_zero c]
    simp
  have hdiv := div_of_card hsq0 (isInf_poleDiv _) (exactPoleH_poly hq0) hZq
    (by rw [deg_poleDiv_poly hq0, hqdeg, hZc])
  have hq1 : ∀ φ, Places.cnt (ptP φ) (algebraMap K[X] (Rfin K F) q) ≤ 1 := fun φ => by
    have e := congrArg (fun D : Places.Divisor K F => D (Sum.inl (ptP φ))) hdiv
    simp only [PlacesK.div_apply, Finsupp.coe_sub, Pi.sub_apply] at e
    have h1 := Zdiv_le_one Zq (Sum.inl (ptP φ) : Place K F)
    have h2 := isInf_poleDiv (K := K) (F := F) (algebraMap K[X] (Rfin K F) q) (ptP φ)
    have h3 := cnt_eq_ord φ hsq0
    rw [h2] at e
    omega
  have hmul : ∀ φ, (Places.cnt (ptP φ) (secOf g Λ) : ℤ) =
      Places.cnt (ptP φ) g + Places.cnt (ptP φ) (algebraMap K[X] (Rfin K F) q) := fun φ => by
    rw [cnt_eq_ord φ (secOf_ne_zero hg0 Λ), cnt_eq_ord φ hg0, cnt_eq_ord φ hsq0, secOf, map_mul]
    exact PlacesK.Place.ord_mul _ (incB_ne_zero hg0) (incB_ne_zero hsq0)
  refine ⟨exactPoleH_of_nonpos fun Q => ?_, fun φ => ?_⟩
  · have h1 := ord_inr_prod (F := F) Q Λ
    have h2 : (Places.ord Q (incB K F g)).toNat ≤ ∑ Q ∈ (Set.finite_univ (α := HeightOneSpectrum (Rinf K F))).toFinset,
        (Places.ord Q (incB K F g)).toNat :=
      Finset.single_le_sum (f := fun Q => (Places.ord Q (incB K F g)).toNat) (fun _ _ => Nat.zero_le _)
        ((Set.Finite.mem_toFinset _).2 (Set.mem_univ Q))
    have h3 := Int.self_le_toNat (Places.ord Q (incB K F g))
    have h4 := PlacesK.ord_mul Q (incB_ne_zero hg0) (incB_ne_zero hsq0)
    rw [secOf, map_mul, h4]
    rw [← hq] at h1
    have h5 : ((Places.ord Q (incB K F g)).toNat : ℤ) ≤ (Λ.card : ℤ) := by exact_mod_cast h2.trans hN
    omega
  · have h := hmul φ
    by_cases hφ : φ g = 0
    · have hq' : Places.cnt (ptP φ) (algebraMap K[X] (Rfin K F) q) = 0 := by
        by_contra hne
        have h0 := (hZq φ).2 (mem_ptP.1 ((cnt_ne_zero_iff _ hsq0).1 hne))
        exact hΛg _ ((hZx φ).1 h0) φ hφ rfl
      have := hg1 φ
      omega
    · have hg' : Places.cnt (ptP φ) g = 0 := by
        by_contra hne
        exact hφ (mem_ptP.1 ((cnt_ne_zero_iff _ hg0).1 hne))
      have := hq1 φ
      omega

/-- **Sections through a closed point** (input of `exists_role`). -/
theorem exists_secP (φ0 : Rfin K F →ₐ[K] K) : ∃ g : Rfin K F, g ≠ 0 ∧ φ0 g = 0 ∧ ∃ a : K[X], a ≠ 0 ∧ ∃ N : ℕ,
    ∀ Λ : Finset K, (∀ c ∈ Λ, a.eval c ≠ 0) → N ≤ Λ.card →
      ExactPoleH (secOf g Λ) (poleDiv (K := K) (incB K F (secOf g Λ))) ∧
        ∀ φ, Places.cnt (ptP φ) (secOf g Λ) ≤ 1 := by
  obtain ⟨g, hg0, hφ0, hg1⟩ := exists_simple φ0
  exact ⟨g, hg0, hφ0, exists_secOf hg0 hg1⟩

end SecB

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacLaw_Bridge =====
section

/-!
# S4-JacLaw, file O10a: open immersions from maps that are inverse at points

`T` reduced of finite type over an algebraically closed field `K`. If `f : T → T[1/ω]` and `g : T → T[1/ω']`
are mutually inverse at `K`-points (`h3`, `h4`) and `f` sends `D(ω)` into `D(ω')` (`h1`), then
`Spec f : Spec T[1/ω] ⟶ Spec T` is an open immersion (`isOpenImmersion_of_ptInv`): `f` factors as
`T → T[1/ω'] → T[1/ω'][1/g(ω)] ≅ T[1/ω]`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open CategoryTheory AlgebraicGeometry

universe u

section Away

variable {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T]

/-- The structure map `T → T[1/ω]` as a `K`-algebra map. -/
noncomputable abbrev awayι (ω : T) : T →ₐ[K] Localization.Away ω := IsScalarTower.toAlgHom K T _

theorem awayι_apply (ω t : T) : awayι (K := K) ω t = algebraMap T _ t := rfl

/-- Maps out of `T[1/ω]` are determined on `T`. -/
theorem away_algHom_ext {ω : T} {C : Type*} [CommRing C] [Algebra K C]
    {f g : Localization.Away ω →ₐ[K] C} (h : f.comp (awayι ω) = g.comp (awayι ω)) : f = g := by
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext (Submonoid.powers ω) (RingHom.ext fun t => ?_)
  exact DFunLike.congr_fun h t

end Away

section OI

variable {K : Type u} [Field K] [IsAlgClosed K] {T : Type u} [CommRing T] [Algebra K T] [IsReduced T]
  [Algebra.FiniteType K T]

/-- If `f : T → T[1/ω]` and `g : T → T[1/ω']` are inverse at points and `f` maps `D(ω)` into `D(ω')`, then
`Spec f` is an open immersion. -/
theorem isOpenImmersion_of_ptInv {ω ω' : T} (f : T →ₐ[K] Localization.Away ω)
    (g : T →ₐ[K] Localization.Away ω')
    (h1 : ∀ x : Localization.Away ω →ₐ[K] K, x (f ω') ≠ 0)
    (h3 : ∀ (x : Localization.Away ω →ₐ[K] K) (y : Localization.Away ω' →ₐ[K] K),
      y.comp (awayι ω') = x.comp f → y.comp g = x.comp (awayι ω))
    (h4 : ∀ (y : Localization.Away ω' →ₐ[K] K) (x : Localization.Away ω →ₐ[K] K),
      x.comp (awayι ω) = y.comp g → x.comp f = y.comp (awayι ω')) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (f : T →+* Localization.Away ω))) := by
  have hu : IsUnit (f ω') := isUnit_of_forall_ne_zero (k := K) _ h1
  obtain ⟨ft, hft⟩ : ∃ ft : Localization.Away ω' →ₐ[K] Localization.Away ω, ft.comp (awayι ω') = f :=
    ⟨IsLocalization.Away.liftAlgHom ω' hu, by
      refine AlgHom.ext fun t => ?_; rw [AlgHom.comp_apply, awayι_apply, IsLocalization.Away.liftAlgHom_apply,
        IsLocalization.Away.lift_eq]; rfl⟩
  have hfg : ft.comp g = awayι ω := by
    apply algHom_ext_pts (k := K)
    intro x
    have := h3 x (x.comp ft) (by rw [AlgHom.comp_assoc, hft])
    rw [← AlgHom.comp_assoc, this]
  have hu2 : IsUnit (ft (g ω)) := by
    rw [← AlgHom.comp_apply, hfg]; exact IsLocalization.Away.algebraMap_isUnit ω
  obtain ⟨F, hF⟩ : ∃ F : Localization.Away (g ω) →ₐ[K] Localization.Away ω, F.comp (awayι (g ω)) = ft :=
    ⟨IsLocalization.Away.liftAlgHom (g ω) hu2, by
      refine AlgHom.ext fun t => ?_; rw [AlgHom.comp_apply, awayι_apply, IsLocalization.Away.liftAlgHom_apply,
        IsLocalization.Away.lift_eq]; rfl⟩
  have hι2 : IsUnit (((awayι (g ω)).comp g) ω) := IsLocalization.Away.algebraMap_isUnit (g ω)
  obtain ⟨G, hG⟩ : ∃ G : Localization.Away ω →ₐ[K] Localization.Away (g ω),
      G.comp (awayι ω) = (awayι (g ω)).comp g :=
    ⟨IsLocalization.Away.liftAlgHom ω hι2, by
      refine AlgHom.ext fun t => ?_; rw [AlgHom.comp_apply, awayι_apply, IsLocalization.Away.liftAlgHom_apply,
        IsLocalization.Away.lift_eq]; rfl⟩
  have hFG : F.comp G = AlgHom.id K _ := by
    apply away_algHom_ext
    rw [AlgHom.comp_assoc, hG, AlgHom.id_comp, ← AlgHom.comp_assoc, hF, hfg]
  have hGf : G.comp f = (awayι (g ω)).comp (awayι ω') := by
    apply algHom_ext_pts (k := K)
    intro y2
    have hx : (y2.comp G).comp (awayι ω) = ((y2.comp (awayι (g ω)))).comp g := by
      rw [AlgHom.comp_assoc, hG]; rfl
    have := h4 (y2.comp (awayι (g ω))) (y2.comp G) hx
    rw [← AlgHom.comp_assoc, this]; rfl
  have hGF : G.comp F = AlgHom.id K _ := by
    apply away_algHom_ext
    apply away_algHom_ext
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, ← AlgHom.comp_assoc F, hF, hft, hGf, AlgHom.id_comp]
  have hiso : IsIso (CommRingCat.ofHom (F : Localization.Away (g ω) →+* Localization.Away ω)) := by
    refine ⟨⟨CommRingCat.ofHom (G : Localization.Away ω →+* Localization.Away (g ω)), ?_, ?_⟩⟩
    · ext a; simpa using DFunLike.congr_fun hGF a
    · ext a; simpa using DFunLike.congr_fun hFG a
  have hfac : CommRingCat.ofHom (f : T →+* Localization.Away ω) =
      CommRingCat.ofHom (algebraMap T (Localization.Away ω')) ≫
        CommRingCat.ofHom (algebraMap (Localization.Away ω') (Localization.Away (g ω))) ≫
          CommRingCat.ofHom (F : Localization.Away (g ω) →+* Localization.Away ω) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    refine RingHom.ext fun t => ?_
    show f t = F (algebraMap _ _ (algebraMap T _ t))
    rw [← hft, ← hF]; rfl
  rw [hfac, Spec.map_comp, Spec.map_comp]
  infer_instance

end OI

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

-- ===== S4.Def_RP_JacLaw_Sch =====
section

/-!
# S4-JacLaw, file O10b: from algebraic chunk data on `R` to a `StrictChunk` on `Spec R`

* `kpt x`: the point of `Spec A` of a `K`-point `x : A →ₐ[K] K`; `comap_kpt`, `kpt_injective`, `isClosed_kpt`,
  `exists_kpt` (closed points are `kpt`s for `K` algebraically closed and `A` of finite type), `SpecMap_kpt`.
* `AffChunk K R`: a law `μ : R → (R ⊗ R)[1/ω]` with point-level inverse data for `Φ = (pr₁, m)` and `Ψ = (m, pr₂)`
  (the hypotheses of `isOpenImmersion_of_ptInv`), fibres and associativity at `K`-points.
* `AffChunk.toStrict`: the `StrictChunk` on `Spec R` (structure map `sR K R`), `Ω = D(ω) ⊆ Spec (R ⊗ R) ≅ X ×_K X`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open CategoryTheory Limits AlgebraicGeometry RamanujanPetersson.JacSym RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section Kpt

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]

/-- The point of `Spec A` of a `K`-point (its kernel). -/
def kpt (x : A →ₐ[K] K) : Spec (.of A) := (⟨RingHom.ker x, RingHom.ker_isPrime x⟩ : PrimeSpectrum A)

theorem kpt_asIdeal (x : A →ₐ[K] K) : PrimeSpectrum.asIdeal (R := A) (kpt x) = RingHom.ker x := rfl

theorem kpt_injective : Function.Injective (kpt (K := K) (A := A)) := fun _ _ h =>
  algHom_eq_of_ker_eq (congrArg (fun p : Spec (.of A) => PrimeSpectrum.asIdeal (R := A) p) h)

theorem isClosed_kpt (x : A →ₐ[K] K) : IsClosed ({kpt x} : Set (Spec (.of A))) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal (R := A) (kpt x)).2 (ker_isMaximal x)

theorem exists_kpt [IsAlgClosed K] [Algebra.FiniteType K A] (p : Spec (.of A))
    (hp : IsClosed ({p} : Set (Spec (.of A)))) : ∃ x : A →ₐ[K] K, kpt x = p := by
  have := (PrimeSpectrum.isClosed_singleton_iff_isMaximal (R := A) p).1 hp
  obtain ⟨x, hx⟩ := exists_algHom_ker_eq (k := K) (PrimeSpectrum.asIdeal (R := A) p)
  exact ⟨x, PrimeSpectrum.ext (R := A) hx⟩

theorem SpecMap_kpt {B : Type u} [CommRing B] [Algebra K B] (f : A →ₐ[K] B) (x : B →ₐ[K] K) :
    Spec.map (CommRingCat.ofHom (f : A →+* B)) (kpt x) = kpt (x.comp f) :=
  PrimeSpectrum.ext (R := A) (Ideal.ext fun _ => Iff.rfl)

end Kpt

section Sch

variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R]

theorem SpecMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B]
    [Algebra K C] (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    Spec.map (CommRingCat.ofHom (g : B →+* C)) ≫ Spec.map (CommRingCat.ofHom (f : A →+* B)) =
      Spec.map (CommRingCat.ofHom ((g.comp f : A →ₐ[K] C) : A →+* C)) := by
  rw [← Spec.map_comp]; rfl

instance isDomain_RR [IsAlgClosed K] [IsDomain R] [Algebra.FiniteType K R] : IsDomain (R ⊗[K] R) :=
  isDomain_tensor (k := K) (B := R) (A := R)

instance finiteType_RR [Algebra.FiniteType K R] : Algebra.FiniteType K (R ⊗[K] R) :=
  Algebra.FiniteType.trans (S := R) inferInstance inferInstance

/-- The structure map of `Spec R` over `Spec K`. -/
noncomputable abbrev sR (K R : Type u) [Field K] [CommRing R] [Algebra K R] : Spec (.of R) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K R))

/-- `(x, y) ↦ (x, m(x,y))` on functions. -/
noncomputable def phiS {ω : R ⊗[K] R} (μ : R →ₐ[K] Localization.Away ω) : R ⊗[K] R →ₐ[K] Localization.Away ω :=
  Algebra.TensorProduct.lift ((awayι ω).comp includeLeft) μ fun _ _ => Commute.all _ _

/-- `(x, y) ↦ (m(x,y), y)` on functions. -/
noncomputable def psiS {ω : R ⊗[K] R} (μ : R →ₐ[K] Localization.Away ω) : R ⊗[K] R →ₐ[K] Localization.Away ω :=
  Algebra.TensorProduct.lift μ ((awayι ω).comp includeRight) fun _ _ => Commute.all _ _

theorem phiS_incL {ω : R ⊗[K] R} (μ : R →ₐ[K] Localization.Away ω) :
    (phiS μ).comp includeLeft = (awayι ω).comp includeLeft :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

theorem phiS_incR {ω : R ⊗[K] R} (μ : R →ₐ[K] Localization.Away ω) : (phiS μ).comp includeRight = μ :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _

theorem psiS_incL {ω : R ⊗[K] R} (μ : R →ₐ[K] Localization.Away ω) : (psiS μ).comp includeLeft = μ :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

theorem psiS_incR {ω : R ⊗[K] R} (μ : R →ₐ[K] Localization.Away ω) :
    (psiS μ).comp includeRight = (awayι ω).comp includeRight :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _

/-- First coordinate of a `K`-point of `D(ω) ⊆ Spec (R ⊗ R)`. -/
noncomputable abbrev pL {ω : R ⊗[K] R} (x : Localization.Away ω →ₐ[K] K) : R →ₐ[K] K :=
  x.comp ((awayι ω).comp includeLeft)

/-- Second coordinate of a `K`-point of `D(ω) ⊆ Spec (R ⊗ R)`. -/
noncomputable abbrev pR {ω : R ⊗[K] R} (x : Localization.Away ω →ₐ[K] K) : R →ₐ[K] K :=
  x.comp ((awayι ω).comp includeRight)

/-- Algebraic strict-chunk data on `R`: a law `μ` on `D(ω) ⊆ Spec (R ⊗ R)`; `Φ = (pr₁, m)` and `Ψ = (m, pr₂)`
satisfy the hypotheses of `isOpenImmersion_of_ptInv`; fibres and associativity at `K`-points. -/
structure AffChunk (K R : Type u) [Field K] [CommRing R] [Algebra K R] where
  ω : R ⊗[K] R
  μ : R →ₐ[K] Localization.Away ω
  ωΦ : R ⊗[K] R
  gΦ : R ⊗[K] R →ₐ[K] Localization.Away ωΦ
  Φ1 : ∀ x : Localization.Away ω →ₐ[K] K, x (phiS μ ωΦ) ≠ 0
  Φ3 : ∀ (x : Localization.Away ω →ₐ[K] K) (y : Localization.Away ωΦ →ₐ[K] K),
    y.comp (awayι ωΦ) = x.comp (phiS μ) → y.comp gΦ = x.comp (awayι ω)
  Φ4 : ∀ (y : Localization.Away ωΦ →ₐ[K] K) (x : Localization.Away ω →ₐ[K] K),
    x.comp (awayι ω) = y.comp gΦ → x.comp (phiS μ) = y.comp (awayι ωΦ)
  ωΨ : R ⊗[K] R
  gΨ : R ⊗[K] R →ₐ[K] Localization.Away ωΨ
  Ψ1 : ∀ x : Localization.Away ω →ₐ[K] K, x (psiS μ ωΨ) ≠ 0
  Ψ3 : ∀ (x : Localization.Away ω →ₐ[K] K) (y : Localization.Away ωΨ →ₐ[K] K),
    y.comp (awayι ωΨ) = x.comp (psiS μ) → y.comp gΨ = x.comp (awayι ω)
  Ψ4 : ∀ (y : Localization.Away ωΨ →ₐ[K] K) (x : Localization.Away ω →ₐ[K] K),
    x.comp (awayι ω) = y.comp gΨ → x.comp (psiS μ) = y.comp (awayι ωΨ)
  fibL : ∀ a : R →ₐ[K] K, ∃ x : Localization.Away ω →ₐ[K] K, pL x = a
  fibR : ∀ b : R →ₐ[K] K, ∃ x : Localization.Away ω →ₐ[K] K, pR x = b
  assoc : ∀ x₁ x₂ x₃ x₄ : Localization.Away ω →ₐ[K] K, pR x₁ = pL x₂ → pL x₃ = x₁.comp μ →
    pR x₃ = pR x₂ → pL x₄ = pL x₁ → pR x₄ = x₂.comp μ → x₃.comp μ = x₄.comp μ

/-- `D(ω) ⊆ Spec (R ⊗ R) ≅ X ×_K X`. -/
noncomputable def jAway (ω : R ⊗[K] R) : Spec (.of (Localization.Away ω)) ⟶ pullback (sR K R) (sR K R) :=
  Spec.map (CommRingCat.ofHom (awayι (K := K) ω : R ⊗[K] R →+* Localization.Away ω)) ≫
    (pullbackSpecIso K R R).inv

instance isOpenImmersion_jAway (ω : R ⊗[K] R) : IsOpenImmersion (jAway ω) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (awayι (K := K) ω : R ⊗[K] R →+* Localization.Away ω))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of (R ⊗[K] R)) ω
  unfold jAway; infer_instance

@[reassoc] theorem eInv_fst : (pullbackSpecIso K R R).inv ≫ pullback.fst (sR K R) (sR K R) =
    Spec.map (CommRingCat.ofHom ((includeLeft : R →ₐ[K] R ⊗[K] R) : R →+* R ⊗[K] R)) :=
  pullbackSpecIso_inv_fst K R R

@[reassoc] theorem eInv_snd : (pullbackSpecIso K R R).inv ≫ pullback.snd (sR K R) (sR K R) =
    Spec.map (CommRingCat.ofHom ((includeRight : R →ₐ[K] R ⊗[K] R) : R →+* R ⊗[K] R)) :=
  pullbackSpecIso_inv_snd K R R

@[reassoc] theorem jAway_fst (ω : R ⊗[K] R) : jAway ω ≫ pullback.fst (sR K R) (sR K R) =
    Spec.map (CommRingCat.ofHom (((awayι ω).comp includeLeft : R →ₐ[K] Localization.Away ω) : R →+* _)) := by
  rw [jAway, Category.assoc, eInv_fst, SpecMap_comp]

@[reassoc] theorem jAway_snd (ω : R ⊗[K] R) : jAway ω ≫ pullback.snd (sR K R) (sR K R) =
    Spec.map (CommRingCat.ofHom (((awayι ω).comp includeRight : R →ₐ[K] Localization.Away ω) : R →+* _)) := by
  rw [jAway, Category.assoc, eInv_snd, SpecMap_comp]

theorem fst_jAway (ω : R ⊗[K] R) (x : Localization.Away ω →ₐ[K] K) :
    pullback.fst (sR K R) (sR K R) (jAway ω (kpt x)) = kpt (pL x) := by
  rw [← Scheme.Hom.comp_apply, jAway_fst, SpecMap_kpt]

theorem snd_jAway (ω : R ⊗[K] R) (x : Localization.Away ω →ₐ[K] K) :
    pullback.snd (sR K R) (sR K R) (jAway ω (kpt x)) = kpt (pR x) := by
  rw [← Scheme.Hom.comp_apply, jAway_snd, SpecMap_kpt]

theorem isClosed_jAway (ω : R ⊗[K] R) (x : Localization.Away ω →ₐ[K] K) :
    IsClosed ({jAway ω (kpt x)} : Set (pullback (sR K R) (sR K R) : Scheme.{u})) := by
  have h := (Scheme.homeoOfIso (pullbackSpecIso K R R).symm).isClosedMap _ (isClosed_kpt (x.comp (awayι ω)))
  rw [Set.image_singleton] at h
  rw [jAway, Scheme.Hom.comp_apply, SpecMap_kpt]
  exact h

variable [IsAlgClosed K] [IsDomain R] [Algebra.FiniteType K R]

omit [IsDomain R] in
theorem exists_pt_jAway (ω : R ⊗[K] R) (z : (jAway ω).opensRange)
    (hz : IsClosed ({z.1} : Set (pullback (sR K R) (sR K R) : Scheme.{u}))) :
    ∃ x : Localization.Away ω →ₐ[K] K, z.1 = jAway ω (kpt x) ∧ (jAway ω).isoOpensRange.inv z = kpt x := by
  obtain ⟨p, hp⟩ := Scheme.Hom.mem_opensRange.1 z.2
  have hinj := (jAway ω).isOpenEmbedding.injective
  have hpc : IsClosed ({p} : Set (Spec (.of (Localization.Away ω)) : Scheme.{u})) := by
    have e : (jAway ω) ⁻¹' {z.1} = {p} := by
      ext q; simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hp, hinj.eq_iff]
    rw [← e]; exact hz.preimage (jAway ω).continuous
  obtain ⟨x, rfl⟩ := exists_kpt (K := K) (A := Localization.Away ω) p hpc
  refine ⟨x, hp.symm, hinj ?_⟩
  exact (congrArg (fun f => f z) (Scheme.Hom.isoOpensRange_inv_comp (jAway ω))).trans hp.symm

omit [IsAlgClosed K] [IsDomain R] [Algebra.FiniteType K R] in
theorem mS_apply (ω : R ⊗[K] R) (μ : R →ₐ[K] Localization.Away ω) (z : (jAway ω).opensRange)
    (x : Localization.Away ω →ₐ[K] K) (h : (jAway ω).isoOpensRange.inv z = kpt x) :
    ((jAway ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (μ : R →+* _))) z = kpt (x.comp μ) := by
  have e : ((jAway ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (μ : R →+* _))) z =
      Spec.map (CommRingCat.ofHom (μ : R →+* _)) ((jAway ω).isoOpensRange.inv z) := rfl
  rw [e, h, SpecMap_kpt]

namespace AffChunk

variable (C : AffChunk K R)

/-- The strict group chunk on `Spec R` defined by algebraic chunk data. -/
noncomputable def toStrict : StrictChunk (k := K) (sR K R) where
  Ω := (jAway C.ω).opensRange
  m := (jAway C.ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (C.μ : R →+* _))
  Φ := (jAway C.ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (phiS C.μ : R ⊗[K] R →+* _)) ≫
    (pullbackSpecIso K R R).inv
  Φ_fst := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp (jAway C.ω)]
    simp only [Category.assoc, eInv_fst, jAway_fst, SpecMap_comp, phiS_incL]
  Φ_snd := by simp only [Category.assoc, eInv_snd, SpecMap_comp, phiS_incR]
  isOpenImmersion_Φ := by
    have := isOpenImmersion_of_ptInv (phiS C.μ) C.gΦ C.Φ1 C.Φ3 C.Φ4
    infer_instance
  Ψ := (jAway C.ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (psiS C.μ : R ⊗[K] R →+* _)) ≫
    (pullbackSpecIso K R R).inv
  Ψ_fst := by simp only [Category.assoc, eInv_fst, SpecMap_comp, psiS_incL]
  Ψ_snd := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp (jAway C.ω)]
    simp only [Category.assoc, eInv_snd, jAway_snd, SpecMap_comp, psiS_incR]
  isOpenImmersion_Ψ := by
    have := isOpenImmersion_of_ptInv (psiS C.μ) C.gΨ C.Ψ1 C.Ψ3 C.Ψ4
    infer_instance
  fib_left a ha := by
    obtain ⟨y, rfl⟩ := exists_kpt (K := K) (A := R) a ha
    obtain ⟨x, hx⟩ := C.fibL y
    exact ⟨jAway C.ω (kpt x), Scheme.Hom.mem_opensRange.2 ⟨kpt x, rfl⟩, isClosed_jAway C.ω x,
      by rw [fst_jAway, hx]⟩
  fib_right b hb := by
    obtain ⟨y, rfl⟩ := exists_kpt (K := K) (A := R) b hb
    obtain ⟨x, hx⟩ := C.fibR y
    exact ⟨jAway C.ω (kpt x), Scheme.Hom.mem_opensRange.2 ⟨kpt x, rfl⟩, isClosed_jAway C.ω x,
      by rw [snd_jAway, hx]⟩
  assoc z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ e₁ e₂ e₃ e₄ e₅ := by
    obtain ⟨x₁, hz₁, hi₁⟩ := exists_pt_jAway C.ω z₁ h₁
    obtain ⟨x₂, hz₂, hi₂⟩ := exists_pt_jAway C.ω z₂ h₂
    obtain ⟨x₃, hz₃, hi₃⟩ := exists_pt_jAway C.ω z₃ h₃
    obtain ⟨x₄, hz₄, hi₄⟩ := exists_pt_jAway C.ω z₄ h₄
    rw [hz₁, hz₂, snd_jAway, fst_jAway] at e₁
    rw [hz₃, fst_jAway, mS_apply C.ω C.μ z₁ x₁ hi₁] at e₂
    rw [hz₃, hz₂, snd_jAway, snd_jAway] at e₃
    rw [hz₄, hz₁, fst_jAway, fst_jAway] at e₄
    rw [hz₄, snd_jAway, mS_apply C.ω C.μ z₂ x₂ hi₂] at e₅
    rw [mS_apply C.ω C.μ z₃ x₃ hi₃, mS_apply C.ω C.μ z₄ x₄ hi₄, C.assoc x₁ x₂ x₃ x₄ (kpt_injective e₁)
      (kpt_injective e₂) (kpt_injective e₃) (kpt_injective e₄) (kpt_injective e₅)]

end AffChunk

end Sch

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_ShrinkA =====
section

/-!
# S4-JacLaw, file O10d-1: tools for shrinking a chunk

* `pair a b`: the `K`-point `(a, b)` of `S ⊗ S`; slices `slL a` (`t ↦ t(a, ·)`), `slR b`.
* Nullstellensatz on a domain: three nonempty basic opens meet (`exists_pt_ne3`).
* `numA e`: a numerator of `e ∈ T[1/ω]` vanishing off `D(ω)`.
* `liftPt`: extend `A → B` to `A[1/ω]` when `ω` vanishes at no point of `B`.
* Base change to `R = S[1/u]`: `jj`, `extW`, `extK`, `extN` and their point lemmas.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section Pair

variable {K : Type u} [Field K] {S : Type u} [CommRing S] [Algebra K S]

theorem tensor_ext {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] [CommRing C]
    [Algebra K C] {f g : A ⊗[K] B →ₐ[K] C} (h1 : f.comp includeLeft = g.comp includeLeft)
    (h2 : f.comp includeRight = g.comp includeRight) : f = g :=
  Algebra.TensorProduct.ext h1 (AlgHom.ext fun s => DFunLike.congr_fun h2 s)

/-- The `K`-point `(a, b)` of `S ⊗ S`. -/
noncomputable def pair (a b : S →ₐ[K] K) : S ⊗[K] S →ₐ[K] K :=
  Algebra.TensorProduct.lift a b fun _ _ => Commute.all _ _

theorem pair_incL (a b : S →ₐ[K] K) : (pair a b).comp includeLeft = a :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

theorem pair_incR (a b : S →ₐ[K] K) : (pair a b).comp includeRight = b :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _

theorem eq_pair (z : S ⊗[K] S →ₐ[K] K) : z = pair (z.comp includeLeft) (z.comp includeRight) :=
  tensor_ext (pair_incL _ _).symm (pair_incR _ _).symm

theorem base_pair {ω : S ⊗[K] S} (x : Localization.Away ω →ₐ[K] K) : x.comp (awayι ω) = pair (pL x) (pR x) :=
  eq_pair _

theorem pts_of_base {ω : S ⊗[K] S} {x : Localization.Away ω →ₐ[K] K} {a b : S →ₐ[K] K}
    (h : x.comp (awayι ω) = pair a b) : pL x = a ∧ pR x = b :=
  ⟨(congrArg (fun z => z.comp includeLeft) h).trans (pair_incL a b),
    (congrArg (fun z => z.comp includeRight) h).trans (pair_incR a b)⟩

theorem exists_over_pair {ω : S ⊗[K] S} {a b : S →ₐ[K] K} (h : pair a b ω ≠ 0) :
    ∃ x : Localization.Away ω →ₐ[K] K, x.comp (awayι ω) = pair a b ∧ pL x = a ∧ pR x = b := by
  obtain ⟨x, hx⟩ := exists_baseAway ω (pair a b) h
  have hx' : x.comp (awayι ω) = pair a b := hx
  exact ⟨x, hx', pts_of_base hx'⟩

theorem phiS_pt {ω : S ⊗[K] S} (μ : S →ₐ[K] Localization.Away ω) (x : Localization.Away ω →ₐ[K] K) :
    x.comp (phiS μ) = pair (pL x) (x.comp μ) := by
  refine tensor_ext ?_ ?_
  · show x.comp ((phiS μ).comp includeLeft) = (pair (pL x) (x.comp μ)).comp includeLeft
    rw [phiS_incL, pair_incL]
  · show x.comp ((phiS μ).comp includeRight) = (pair (pL x) (x.comp μ)).comp includeRight
    rw [phiS_incR, pair_incR]

theorem psiS_pt {ω : S ⊗[K] S} (μ : S →ₐ[K] Localization.Away ω) (x : Localization.Away ω →ₐ[K] K) :
    x.comp (psiS μ) = pair (x.comp μ) (pR x) := by
  refine tensor_ext ?_ ?_
  · show x.comp ((psiS μ).comp includeLeft) = (pair (x.comp μ) (pR x)).comp includeLeft
    rw [psiS_incL, pair_incL]
  · show x.comp ((psiS μ).comp includeRight) = (pair (x.comp μ) (pR x)).comp includeRight
    rw [psiS_incR, pair_incR]

/-- `t ↦ t(a, ·)`. -/
noncomputable def slL (a : S →ₐ[K] K) : S ⊗[K] S →ₐ[K] S :=
  Algebra.TensorProduct.lift ((Algebra.ofId K S).comp a) (AlgHom.id K S) fun _ _ => Commute.all _ _

/-- `t ↦ t(·, b)`. -/
noncomputable def slR (b : S →ₐ[K] K) : S ⊗[K] S →ₐ[K] S :=
  Algebra.TensorProduct.lift (AlgHom.id K S) ((Algebra.ofId K S).comp b) fun _ _ => Commute.all _ _

theorem slL_pt (a b : S →ₐ[K] K) : b.comp (slL a) = pair a b :=
  Algebra.TensorProduct.ext' fun s t => by simp [slL, pair]

theorem slR_pt (a b : S →ₐ[K] K) : a.comp (slR b) = pair a b :=
  Algebra.TensorProduct.ext' fun s t => by simp [slR, pair]

theorem ne_zero_of_pt {f : S} (h : ∃ x : S →ₐ[K] K, x f ≠ 0) : f ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := h
  exact hx (map_zero x)

variable [IsAlgClosed K] [IsDomain S] [Algebra.FiniteType K S]

theorem exists_pt_ne {f : S} (hf : f ≠ 0) : ∃ x : S →ₐ[K] K, x f ≠ 0 := by
  by_contra h
  refine hf (evPts_injective (k := K) (funext fun x => ?_))
  rw [evPts_apply, map_zero]
  exact not_not.1 fun hx => h ⟨x, hx⟩

theorem exists_pt_ne2 {f g : S} (hf : ∃ x : S →ₐ[K] K, x f ≠ 0) (hg : ∃ x : S →ₐ[K] K, x g ≠ 0) :
    ∃ x : S →ₐ[K] K, x f ≠ 0 ∧ x g ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_pt_ne (K := K) (mul_ne_zero (ne_zero_of_pt hf) (ne_zero_of_pt hg))
  rw [map_mul] at hx
  exact ⟨x, left_ne_zero_of_mul hx, right_ne_zero_of_mul hx⟩

theorem exists_pt_ne3 {f g h : S} (hf : ∃ x : S →ₐ[K] K, x f ≠ 0) (hg : ∃ x : S →ₐ[K] K, x g ≠ 0)
    (hh : ∃ x : S →ₐ[K] K, x h ≠ 0) : ∃ x : S →ₐ[K] K, x f ≠ 0 ∧ x g ≠ 0 ∧ x h ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_pt_ne (K := K)
    (mul_ne_zero (mul_ne_zero (ne_zero_of_pt hf) (ne_zero_of_pt hg)) (ne_zero_of_pt hh))
  rw [map_mul, map_mul] at hx
  exact ⟨x, left_ne_zero_of_mul (left_ne_zero_of_mul hx), right_ne_zero_of_mul (left_ne_zero_of_mul hx),
    right_ne_zero_of_mul hx⟩

end Pair

section Num

variable {K : Type u} [Field K] {T : Type u} [CommRing T] [Algebra K T]

/-- A numerator of `e ∈ T[1/ω]`, times `ω` so that it also vanishes off `D(ω)`. -/
noncomputable def numA {ω : T} (e : Localization.Away ω) : T :=
  ω * (IsLocalization.surj (Submonoid.powers ω) e).choose.1

theorem numA_base {ω : T} (e : Localization.Away ω) (z : T →ₐ[K] K) (h : z (numA e) ≠ 0) : z ω ≠ 0 := by
  rw [numA, map_mul] at h
  exact left_ne_zero_of_mul h

theorem numA_pt {ω : T} (e : Localization.Away ω) (x : Localization.Away ω →ₐ[K] K) :
    (x.comp (awayι ω)) (numA e) ≠ 0 ↔ x e ≠ 0 := by
  have h := (IsLocalization.surj (Submonoid.powers ω) e).choose_spec
  have h1 : x (algebraMap T _ ω) ≠ 0 :=
    ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away ω) ω).map x).ne_zero
  have h2 : x (algebraMap T _ (IsLocalization.surj (Submonoid.powers ω) e).choose.2) ≠ 0 :=
    ((IsLocalization.map_units (M := Submonoid.powers ω) (S := Localization.Away ω)
      (IsLocalization.surj (Submonoid.powers ω) e).choose.2).map x).ne_zero
  rw [AlgHom.comp_apply, awayι_apply, numA, map_mul (algebraMap T _), ← h, map_mul, map_mul]
  simp only [ne_eq, mul_eq_zero, h1, h2, false_or, or_false]

end Num

section Lift

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Extend `f : A → B` to `A[1/ω]` when `f ω` vanishes at no `K`-point of `B`. -/
noncomputable def liftPt {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B] (f : A →ₐ[K] B) (ω : A) (h : ∀ y : B →ₐ[K] K, y (f ω) ≠ 0) :
    Localization.Away ω →ₐ[K] B :=
  IsLocalization.Away.liftAlgHom (f := f) ω (isUnit_of_forall_ne_zero (k := K) (f ω) h)

theorem liftPt_comp {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B] (f : A →ₐ[K] B) (ω : A) (h : ∀ y : B →ₐ[K] K, y (f ω) ≠ 0) :
    (liftPt f ω h).comp (awayι ω) = f :=
  AlgHom.ext fun t => by
    rw [AlgHom.comp_apply, awayι_apply]
    unfold liftPt
    rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
    rfl

end Lift

/-- `S ⊗ S → S[1/u] ⊗ S[1/u]`. -/
noncomputable def jj (K : Type u) [Field K] {S : Type u} [CommRing S] [Algebra K S] (u : S) :
    S ⊗[K] S →ₐ[K] Localization.Away u ⊗[K] Localization.Away u :=
  Algebra.TensorProduct.map (awayι u) (awayι u)

section Ext

variable {K : Type u} [Field K] {S : Type u} [CommRing S] [Algebra K S] (u : S)

theorem jj_incL : (jj K u).comp includeLeft = includeLeft.comp (awayι (K := K) u) :=
  Algebra.TensorProduct.map_comp_includeLeft _ _

theorem jj_incR : (jj K u).comp includeRight = includeRight.comp (awayι (K := K) u) :=
  Algebra.TensorProduct.map_comp_includeRight _ _

theorem jj_ext {C : Type u} [CommRing C] [Algebra K C]
    {f g : Localization.Away u ⊗[K] Localization.Away u →ₐ[K] C}
    (h : f.comp (jj K u) = g.comp (jj K u)) : f = g := by
  refine tensor_ext (away_algHom_ext ?_) (away_algHom_ext ?_)
  · have := congrArg (fun F => F.comp includeLeft) h
    simp only [AlgHom.comp_assoc, jj_incL] at this
    exact this
  · have := congrArg (fun F => F.comp includeRight) h
    simp only [AlgHom.comp_assoc, jj_incR] at this
    exact this

theorem jj_pt {w : Localization.Away u ⊗[K] Localization.Away u} (y : Localization.Away w →ₐ[K] K) :
    (y.comp (awayι w)).comp (jj K u) = pair ((pL y).comp (awayι u)) ((pR y).comp (awayι u)) := by
  refine tensor_ext ?_ ?_
  · rw [pair_incL]
    show (y.comp (awayι w)).comp ((jj K u).comp includeLeft) =
      (y.comp (awayι w)).comp (includeLeft.comp (awayι u))
    rw [jj_incL]
  · rw [pair_incR]
    show (y.comp (awayι w)).comp ((jj K u).comp includeRight) =
      (y.comp (awayι w)).comp (includeRight.comp (awayι u))
    rw [jj_incR]

variable [IsAlgClosed K] [Algebra.FiniteType K S] {ω : S ⊗[K] S} (e : S ⊗[K] S)
  (ν : S →ₐ[K] Localization.Away ω)

/-- `w ∈ S[1/u] ⊗ S[1/u]`, the image of `e · num(ν u)`. -/
noncomputable def extW : Localization.Away u ⊗[K] Localization.Away u := jj K u (e * numA (ν u))

theorem extW_pt (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    pair ((pL y).comp (awayι u)) ((pR y).comp (awayι u)) (e * numA (ν u)) ≠ 0 := by
  rw [← jj_pt]
  exact baseAway_ne _ y

/-- `T[1/ω] → (S[1/u] ⊗ S[1/u])[1/w]`. -/
noncomputable def extK : Localization.Away ω →ₐ[K] Localization.Away (extW u e ν) :=
  liftPt ((awayι (extW u e ν)).comp (jj K u)) ω fun y => by
    have h := extW_pt u e ν y
    rw [map_mul] at h
    have h' := numA_base (ν u) _ (right_ne_zero_of_mul h)
    rw [← jj_pt] at h'
    exact h'

theorem extK_comp : (extK u e ν).comp (awayι ω) = (awayι (extW u e ν)).comp (jj K u) := liftPt_comp _ _ _

theorem extK_pt (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    (y.comp (extK u e ν)).comp (awayι ω) = pair ((pL y).comp (awayι u)) ((pR y).comp (awayι u)) := by
  rw [AlgHom.comp_assoc, extK_comp, ← AlgHom.comp_assoc, jj_pt]

theorem extK_base (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    (y.comp (extK u e ν)).comp (awayι ω) = (y.comp (awayι (extW u e ν))).comp (jj K u) := by
  rw [AlgHom.comp_assoc, extK_comp, ← AlgHom.comp_assoc]

theorem extK_pL (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    pL (y.comp (extK u e ν)) = (pL y).comp (awayι u) :=
  (congrArg (fun z => z.comp includeLeft) (extK_pt u e ν y)).trans (pair_incL _ _)

theorem extK_pR (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    pR (y.comp (extK u e ν)) = (pR y).comp (awayι u) :=
  (congrArg (fun z => z.comp includeRight) (extK_pt u e ν y)).trans (pair_incR _ _)

theorem extK_uL (y : Localization.Away (extW u e ν) →ₐ[K] K) : (pL (y.comp (extK u e ν))) u ≠ 0 := by
  rw [extK_pL]; exact baseAway_ne u (pL y)

theorem extK_uR (y : Localization.Away (extW u e ν) →ₐ[K] K) : (pR (y.comp (extK u e ν))) u ≠ 0 := by
  rw [extK_pR]; exact baseAway_ne u (pR y)

theorem extK_e (y : Localization.Away (extW u e ν) →ₐ[K] K) : ((y.comp (extK u e ν)).comp (awayι ω)) e ≠ 0 := by
  have h := extW_pt u e ν y
  rw [map_mul, ← extK_pt u e ν y] at h
  exact left_ne_zero_of_mul h

/-- `ν` extended to `S[1/u] → (S[1/u] ⊗ S[1/u])[1/w]`. -/
noncomputable def extN : Localization.Away u →ₐ[K] Localization.Away (extW u e ν) :=
  liftPt ((extK u e ν).comp ν) u fun y => by
    have h := extW_pt u e ν y
    rw [map_mul, ← extK_pt u e ν y] at h
    exact (numA_pt (ν u) (y.comp (extK u e ν))).1 (right_ne_zero_of_mul h)

theorem extN_comp : (extN u e ν).comp (awayι u) = (extK u e ν).comp ν := liftPt_comp _ _ _

theorem extK_nu (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    (y.comp (extK u e ν)).comp ν = (y.comp (extN u e ν)).comp (awayι u) := by
  rw [AlgHom.comp_assoc, ← extN_comp, ← AlgHom.comp_assoc]

theorem phiS_ext : (phiS (extN u e ν)).comp (jj K u) = (extK u e ν).comp (phiS ν) := by
  refine tensor_ext ?_ ?_
  · show (phiS (extN u e ν)).comp ((jj K u).comp includeLeft) = (extK u e ν).comp ((phiS ν).comp includeLeft)
    rw [jj_incL, phiS_incL]
    show ((phiS (extN u e ν)).comp includeLeft).comp (awayι u) = ((extK u e ν).comp (awayι ω)).comp includeLeft
    rw [phiS_incL, extK_comp]
    show (awayι (extW u e ν)).comp (includeLeft.comp (awayι u)) =
      (awayι (extW u e ν)).comp ((jj K u).comp includeLeft)
    rw [jj_incL]
  · show (phiS (extN u e ν)).comp ((jj K u).comp includeRight) = (extK u e ν).comp ((phiS ν).comp includeRight)
    rw [jj_incR, phiS_incR]
    show ((phiS (extN u e ν)).comp includeRight).comp (awayι u) = (extK u e ν).comp ν
    rw [phiS_incR, extN_comp]

theorem psiS_ext : (psiS (extN u e ν)).comp (jj K u) = (extK u e ν).comp (psiS ν) := by
  refine tensor_ext ?_ ?_
  · show (psiS (extN u e ν)).comp ((jj K u).comp includeLeft) = (extK u e ν).comp ((psiS ν).comp includeLeft)
    rw [jj_incL, psiS_incL]
    show ((psiS (extN u e ν)).comp includeLeft).comp (awayι u) = (extK u e ν).comp ν
    rw [psiS_incL, extN_comp]
  · show (psiS (extN u e ν)).comp ((jj K u).comp includeRight) = (extK u e ν).comp ((psiS ν).comp includeRight)
    rw [jj_incR, psiS_incR]
    show ((psiS (extN u e ν)).comp includeRight).comp (awayι u) = ((extK u e ν).comp (awayι ω)).comp includeRight
    rw [psiS_incR, extK_comp]
    show (awayι (extW u e ν)).comp (includeRight.comp (awayι u)) =
      (awayι (extW u e ν)).comp ((jj K u).comp includeRight)
    rw [jj_incR]

theorem extK_phi (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    (y.comp (extK u e ν)).comp (phiS ν) = (y.comp (phiS (extN u e ν))).comp (jj K u) := by
  rw [AlgHom.comp_assoc, ← phiS_ext, ← AlgHom.comp_assoc]

theorem extK_psi (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    (y.comp (extK u e ν)).comp (psiS ν) = (y.comp (psiS (extN u e ν))).comp (jj K u) := by
  rw [AlgHom.comp_assoc, ← psiS_ext, ← AlgHom.comp_assoc]

theorem exists_ext_pt (a b : S →ₐ[K] K) (ha : a u ≠ 0) (hb : b u ≠ 0) (h : pair a b (e * numA (ν u)) ≠ 0) :
    ∃ y : Localization.Away (extW u e ν) →ₐ[K] K, (pL y).comp (awayι u) = a ∧ (pR y).comp (awayι u) = b := by
  obtain ⟨a', ha'⟩ := exists_baseAway u a ha
  obtain ⟨b', hb'⟩ := exists_baseAway u b hb
  have hp : (pair a' b').comp (jj K u) = pair a b := by
    refine tensor_ext ?_ ?_
    · show (pair a' b').comp ((jj K u).comp includeLeft) = (pair a b).comp includeLeft
      rw [jj_incL, pair_incL]
      show ((pair a' b').comp includeLeft).comp (awayι u) = a
      rw [pair_incL]; exact ha'
    · show (pair a' b').comp ((jj K u).comp includeRight) = (pair a b).comp includeRight
      rw [jj_incR, pair_incR]
      show ((pair a' b').comp includeRight).comp (awayι u) = b
      rw [pair_incR]; exact hb'
  obtain ⟨y, hy⟩ := exists_baseAway (extW u e ν) (pair a' b') (by
    show ((pair a' b').comp (jj K u)) (e * numA (ν u)) ≠ 0
    rw [hp]; exact h)
  have hy' : y.comp (awayι (extW u e ν)) = pair a' b' := hy
  refine ⟨y, ?_, ?_⟩
  · show ((y.comp (awayι (extW u e ν))).comp includeLeft).comp (awayι u) = a
    rw [hy', pair_incL]; exact ha'
  · show ((y.comp (awayι (extW u e ν))).comp includeRight).comp (awayι u) = b
    rw [hy', pair_incR]; exact hb'

end Ext

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Shrink =====
section

/-!
# S4-JacLaw, file O10d-2: from a birational law on a domain `S` to an `AffChunk` on `S[1/u0]`

`PreChunk K S`: `m` on `D(ω)`, `r(a,c)` on `D(ωr)`, `l(c,b)` on `D(ωl)` (opens of `Spec (S ⊗ S)`), the inverse relations
and associativity at `K`-points, and one point of `D(ω)` where `(a, m(a,b)) ∈ D(ωr)` and `(m(a,b), b) ∈ D(ωl)`.
`PreChunk.toAff`: shrink `Spec S` to `D(u0)` so that all fibres of `D(ω') → X` are nonempty.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

/-- Birational group-law data on `S` (see the module doc). -/
structure PreChunk (K S : Type u) [Field K] [CommRing S] [Algebra K S] where
  ω : S ⊗[K] S
  μ : S →ₐ[K] Localization.Away ω
  ωr : S ⊗[K] S
  ρ : S →ₐ[K] Localization.Away ωr
  ωl : S ⊗[K] S
  la : S →ₐ[K] Localization.Away ωl
  r_m : ∀ (x : Localization.Away ω →ₐ[K] K) (x' : Localization.Away ωr →ₐ[K] K),
    pL x' = pL x → pR x' = x.comp μ → x'.comp ρ = pR x
  m_r : ∀ (x' : Localization.Away ωr →ₐ[K] K) (x : Localization.Away ω →ₐ[K] K),
    pL x = pL x' → pR x = x'.comp ρ → x.comp μ = pR x'
  l_m : ∀ (x : Localization.Away ω →ₐ[K] K) (x' : Localization.Away ωl →ₐ[K] K),
    pR x' = pR x → pL x' = x.comp μ → x'.comp la = pL x
  m_l : ∀ (x' : Localization.Away ωl →ₐ[K] K) (x : Localization.Away ω →ₐ[K] K),
    pR x = pR x' → pL x = x'.comp la → x.comp μ = pL x'
  assoc : ∀ x₁ x₂ x₃ x₄ : Localization.Away ω →ₐ[K] K, pR x₁ = pL x₂ → pL x₃ = x₁.comp μ →
    pR x₃ = pR x₂ → pL x₄ = pL x₁ → pR x₄ = x₂.comp μ → x₃.comp μ = x₄.comp μ
  wit : ∃ x : Localization.Away ω →ₐ[K] K, x (phiS μ ωr) ≠ 0 ∧ x (psiS μ ωl) ≠ 0

namespace PreChunk

variable {K : Type u} [Field K] {S : Type u} [CommRing S] [Algebra K S] (P : PreChunk K S)

theorem phi1 (x : Localization.Away P.ω →ₐ[K] K) (h1 : x (phiS P.μ P.ωr) ≠ 0) (s : S) (hs : (pR x) s ≠ 0) :
    x (phiS P.μ (numA (P.ρ s))) ≠ 0 := by
  have z : pair (pL x) (x.comp P.μ) P.ωr ≠ 0 := by rw [← phiS_pt]; exact h1
  obtain ⟨x', hx', hL, hR⟩ := exists_over_pair z
  have h2 : x' (P.ρ s) ≠ 0 := by rw [← AlgHom.comp_apply, P.r_m x x' hL hR]; exact hs
  have h3 := (numA_pt (P.ρ s) x').2 h2
  rw [hx', ← phiS_pt] at h3
  exact h3

theorem psi1 (x : Localization.Away P.ω →ₐ[K] K) (h1 : x (psiS P.μ P.ωl) ≠ 0) (s : S) (hs : (pL x) s ≠ 0) :
    x (psiS P.μ (numA (P.la s))) ≠ 0 := by
  have z : pair (x.comp P.μ) (pR x) P.ωl ≠ 0 := by rw [← psiS_pt]; exact h1
  obtain ⟨x', hx', hL, hR⟩ := exists_over_pair z
  have h2 : x' (P.la s) ≠ 0 := by rw [← AlgHom.comp_apply, P.l_m x x' hR hL]; exact hs
  have h3 := (numA_pt (P.la s) x').2 h2
  rw [hx', ← psiS_pt] at h3
  exact h3

theorem phi3 (x : Localization.Away P.ω →ₐ[K] K) (x' : Localization.Away P.ωr →ₐ[K] K)
    (h : x'.comp (awayι P.ωr) = x.comp (phiS P.μ)) : x'.comp (phiS P.ρ) = x.comp (awayι P.ω) := by
  obtain ⟨hL, hR⟩ := pts_of_base (h.trans (phiS_pt P.μ x))
  rw [phiS_pt, base_pair, hL, P.r_m x x' hL hR]

theorem phi4 (x' : Localization.Away P.ωr →ₐ[K] K) (x : Localization.Away P.ω →ₐ[K] K)
    (h : x.comp (awayι P.ω) = x'.comp (phiS P.ρ)) : x.comp (phiS P.μ) = x'.comp (awayι P.ωr) := by
  obtain ⟨hL, hR⟩ := pts_of_base (h.trans (phiS_pt P.ρ x'))
  rw [phiS_pt, base_pair, hL, P.m_r x' x hL hR]

theorem psi3 (x : Localization.Away P.ω →ₐ[K] K) (x' : Localization.Away P.ωl →ₐ[K] K)
    (h : x'.comp (awayι P.ωl) = x.comp (psiS P.μ)) : x'.comp (psiS P.la) = x.comp (awayι P.ω) := by
  obtain ⟨hL, hR⟩ := pts_of_base (h.trans (psiS_pt P.μ x))
  rw [psiS_pt, base_pair, hR, P.l_m x x' hR hL]

theorem psi4 (x' : Localization.Away P.ωl →ₐ[K] K) (x : Localization.Away P.ω →ₐ[K] K)
    (h : x.comp (awayι P.ω) = x'.comp (psiS P.la)) : x.comp (psiS P.μ) = x'.comp (awayι P.ωl) := by
  obtain ⟨hL, hR⟩ := pts_of_base (h.trans (psiS_pt P.la x'))
  rw [psiS_pt, base_pair, hR, P.m_l x' x hR hL]

/-- `(a, b) ↦ (a, m(a,b)) ∈ D(ωr)`. -/
noncomputable def t1 : S ⊗[K] S := numA (phiS P.μ P.ωr)

/-- `(a, b) ↦ (m(a,b), b) ∈ D(ωl)`. -/
noncomputable def t2 : S ⊗[K] S := numA (psiS P.μ P.ωl)

/-- The witness point. -/
noncomputable def x0 : Localization.Away P.ω →ₐ[K] K := P.wit.choose

/-- `u0(a) = (t1 t2)(a, b0) · (t1 t2)(a0, a)`. -/
noncomputable def u0 : S := slR (pR P.x0) (P.t1 * P.t2) * slL (pL P.x0) (P.t1 * P.t2)

theorem u0_left (a : S →ₐ[K] K) (ha : a P.u0 ≠ 0) : pair a (pR P.x0) (P.t1 * P.t2) ≠ 0 := by
  rw [u0, map_mul] at ha
  have h := left_ne_zero_of_mul ha
  rwa [← AlgHom.comp_apply, slR_pt] at h

theorem u0_right (b : S →ₐ[K] K) (hb : b P.u0 ≠ 0) : pair (pL P.x0) b (P.t1 * P.t2) ≠ 0 := by
  rw [u0, map_mul] at hb
  have h := right_ne_zero_of_mul hb
  rwa [← AlgHom.comp_apply, slL_pt] at h

variable [IsAlgClosed K] [IsDomain S] [Algebra.FiniteType K S]

theorem u0_ne : P.u0 ≠ 0 := by
  have h0 : pair (pL P.x0) (pR P.x0) (P.t1 * P.t2) ≠ 0 := by
    rw [← base_pair, map_mul]
    exact mul_ne_zero ((numA_pt _ _).2 P.wit.choose_spec.1) ((numA_pt _ _).2 P.wit.choose_spec.2)
  refine mul_ne_zero (ne_zero_of_pt (K := K) ⟨pL P.x0, ?_⟩) (ne_zero_of_pt (K := K) ⟨pR P.x0, ?_⟩)
  · rw [← AlgHom.comp_apply, slR_pt]; exact h0
  · rw [← AlgHom.comp_apply, slL_pt]; exact h0

instance isDomain_u0 : IsDomain (Localization.Away P.u0) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors P.u0_ne)

theorem fibL_S (a : S →ₐ[K] K) (ha : a P.u0 ≠ 0) :
    ∃ b : S →ₐ[K] K, b P.u0 ≠ 0 ∧ pair a b (P.t1 * P.t2 * numA (P.μ P.u0)) ≠ 0 := by
  have hF := P.u0_left a ha
  rw [map_mul] at hF
  have h1 : pair a (pR P.x0) P.t1 ≠ 0 := left_ne_zero_of_mul hF
  obtain ⟨x1, hx1, hL1, -⟩ := exists_over_pair (numA_base (phiS P.μ P.ωr) _ h1)
  have hx1r : x1 (phiS P.μ P.ωr) ≠ 0 := (numA_pt (phiS P.μ P.ωr) x1).1 (by rw [hx1]; exact h1)
  have z1 : pair (pL x1) (x1.comp P.μ) P.ωr ≠ 0 := by rw [← phiS_pt]; exact hx1r
  obtain ⟨x1', hx1', hL1', hR1'⟩ := exists_over_pair z1
  have hr1 := P.r_m x1 x1' hL1' hR1'
  have w1 : pair a (x1.comp P.μ) (numA (phiS P.ρ P.ω)) ≠ 0 := by
    rw [← hL1, ← hx1', numA_pt, ← AlgHom.comp_apply, phiS_pt, hL1', hr1, ← base_pair, hx1]
    exact numA_base (phiS P.μ P.ωr) _ h1
  obtain ⟨c, hc1, hc2⟩ := exists_pt_ne2 (K := K) (f := slL a (numA (phiS P.ρ P.ω))) (g := P.u0)
    ⟨x1.comp P.μ, by rw [← AlgHom.comp_apply, slL_pt]; exact w1⟩ ⟨a, ha⟩
  rw [← AlgHom.comp_apply, slL_pt] at hc1
  obtain ⟨x', hx', hL', hR'⟩ := exists_over_pair (numA_base (phiS P.ρ P.ω) _ hc1)
  have hx'w : x' (phiS P.ρ P.ω) ≠ 0 := (numA_pt (phiS P.ρ P.ω) x').1 (by rw [hx']; exact hc1)
  have z2 : pair (pL x') (x'.comp P.ρ) P.ω ≠ 0 := by rw [← phiS_pt]; exact hx'w
  obtain ⟨x2, -, hL2, hR2⟩ := exists_over_pair z2
  have hm2 := P.m_r x' x2 hL2 hR2
  obtain ⟨b, hb1, hb2, hb3⟩ := exists_pt_ne3 (K := K) (f := slL a (P.t1 * P.t2))
    (g := slL a (numA (P.μ P.u0))) (h := P.u0)
    ⟨pR P.x0, by rw [← AlgHom.comp_apply, slL_pt, map_mul]; exact hF⟩
    ⟨x'.comp P.ρ, by
      rw [← AlgHom.comp_apply, slL_pt, ← hL', ← hL2, ← hR2, ← base_pair, numA_pt, ← AlgHom.comp_apply, hm2, hR']
      exact hc2⟩
    ⟨a, ha⟩
  refine ⟨b, hb3, ?_⟩
  rw [← AlgHom.comp_apply, slL_pt] at hb1 hb2
  rw [map_mul]; exact mul_ne_zero hb1 hb2

theorem fibR_S (b : S →ₐ[K] K) (hb : b P.u0 ≠ 0) :
    ∃ a : S →ₐ[K] K, a P.u0 ≠ 0 ∧ pair a b (P.t1 * P.t2 * numA (P.μ P.u0)) ≠ 0 := by
  have hF := P.u0_right b hb
  rw [map_mul] at hF
  have h2 : pair (pL P.x0) b P.t2 ≠ 0 := right_ne_zero_of_mul hF
  obtain ⟨x1, hx1, -, hR1⟩ := exists_over_pair (numA_base (psiS P.μ P.ωl) _ h2)
  have hx1l : x1 (psiS P.μ P.ωl) ≠ 0 := (numA_pt (psiS P.μ P.ωl) x1).1 (by rw [hx1]; exact h2)
  have z1 : pair (x1.comp P.μ) (pR x1) P.ωl ≠ 0 := by rw [← psiS_pt]; exact hx1l
  obtain ⟨x1', hx1', hL1', hR1'⟩ := exists_over_pair z1
  have hl1 := P.l_m x1 x1' hR1' hL1'
  have w1 : pair (x1.comp P.μ) b (numA (psiS P.la P.ω)) ≠ 0 := by
    rw [← hR1, ← hx1', numA_pt, ← AlgHom.comp_apply, psiS_pt, hR1', hl1, ← base_pair, hx1]
    exact numA_base (psiS P.μ P.ωl) _ h2
  obtain ⟨c, hc1, hc2⟩ := exists_pt_ne2 (K := K) (f := slR b (numA (psiS P.la P.ω))) (g := P.u0)
    ⟨x1.comp P.μ, by rw [← AlgHom.comp_apply, slR_pt]; exact w1⟩ ⟨b, hb⟩
  rw [← AlgHom.comp_apply, slR_pt] at hc1
  obtain ⟨x', hx', hL', hR'⟩ := exists_over_pair (numA_base (psiS P.la P.ω) _ hc1)
  have hx'w : x' (psiS P.la P.ω) ≠ 0 := (numA_pt (psiS P.la P.ω) x').1 (by rw [hx']; exact hc1)
  have z2 : pair (x'.comp P.la) (pR x') P.ω ≠ 0 := by rw [← psiS_pt]; exact hx'w
  obtain ⟨x2, -, hL2, hR2⟩ := exists_over_pair z2
  have hm2 := P.m_l x' x2 hR2 hL2
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_pt_ne3 (K := K) (f := slR b (P.t1 * P.t2))
    (g := slR b (numA (P.μ P.u0))) (h := P.u0)
    ⟨pL P.x0, by rw [← AlgHom.comp_apply, slR_pt, map_mul]; exact hF⟩
    ⟨x'.comp P.la, by
      rw [← AlgHom.comp_apply, slR_pt, ← hR', ← hR2, ← hL2, ← base_pair, numA_pt, ← AlgHom.comp_apply, hm2, hL']
      exact hc2⟩
    ⟨b, hb⟩
  refine ⟨a, ha3, ?_⟩
  rw [← AlgHom.comp_apply, slR_pt] at ha1 ha2
  rw [map_mul]; exact mul_ne_zero ha1 ha2

end PreChunk

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_ShrinkC =====
section

/-!
# S4-JacLaw, file O10d-3: the `AffChunk` on `S[1/u0]`

`PreChunk.toAff`: the birational law of a `PreChunk K S`, base-changed to `R = S[1/u0]`, is an `AffChunk K R`
(`ω' = e·num(μ u0)` with `e = t1 t2`, `ωΦ = num(ρ u0)`, `ωΨ = num(λ u0)`); `PreChunk.toStrict'` is its strict chunk.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

namespace PreChunk

variable {K : Type u} [Field K] [IsAlgClosed K] {S : Type u} [CommRing S] [Algebra K S]
  [Algebra.FiniteType K S] (P : PreChunk K S)

theorem t12_left (x : Localization.Away (extW P.u0 (P.t1 * P.t2) P.μ) →ₐ[K] K) :
    (x.comp (extK P.u0 (P.t1 * P.t2) P.μ)) (phiS P.μ P.ωr) ≠ 0 := by
  have e1 := extK_e P.u0 (P.t1 * P.t2) P.μ x
  rw [map_mul] at e1
  exact (numA_pt (phiS P.μ P.ωr) _).1 (left_ne_zero_of_mul e1)

theorem t12_right (x : Localization.Away (extW P.u0 (P.t1 * P.t2) P.μ) →ₐ[K] K) :
    (x.comp (extK P.u0 (P.t1 * P.t2) P.μ)) (psiS P.μ P.ωl) ≠ 0 := by
  have e1 := extK_e P.u0 (P.t1 * P.t2) P.μ x
  rw [map_mul] at e1
  exact (numA_pt (psiS P.μ P.ωl) _).1 (right_ne_zero_of_mul e1)

variable [IsDomain S]

/-- The algebraic chunk data on `S[1/u0]`. -/
noncomputable def toAff : AffChunk K (Localization.Away P.u0) where
  ω := extW P.u0 (P.t1 * P.t2) P.μ
  μ := extN P.u0 (P.t1 * P.t2) P.μ
  ωΦ := extW P.u0 1 P.ρ
  gΦ := phiS (extN P.u0 1 P.ρ)
  Φ1 x := by
    have e : x (phiS (extN P.u0 (P.t1 * P.t2) P.μ) (extW P.u0 1 P.ρ)) =
        (x.comp (extK P.u0 (P.t1 * P.t2) P.μ)) (phiS P.μ (numA (P.ρ P.u0))) := by
      change x (((phiS (extN P.u0 (P.t1 * P.t2) P.μ)).comp (jj K P.u0)) (1 * numA (P.ρ P.u0))) = _
      rw [phiS_ext, one_mul]; rfl
    rw [e]
    exact P.phi1 _ (P.t12_left x) P.u0 (extK_uR P.u0 (P.t1 * P.t2) P.μ x)
  Φ3 x y h := by
    refine jj_ext P.u0 ?_
    rw [← extK_phi P.u0 1 P.ρ y, ← extK_base P.u0 (P.t1 * P.t2) P.μ x]
    exact P.phi3 _ _ (by rw [extK_base P.u0 1 P.ρ y, h, extK_phi P.u0 (P.t1 * P.t2) P.μ x])
  Φ4 y x h := by
    refine jj_ext P.u0 ?_
    rw [← extK_phi P.u0 (P.t1 * P.t2) P.μ x, ← extK_base P.u0 1 P.ρ y]
    exact P.phi4 _ _ (by rw [extK_base P.u0 (P.t1 * P.t2) P.μ x, h, extK_phi P.u0 1 P.ρ y])
  ωΨ := extW P.u0 1 P.la
  gΨ := psiS (extN P.u0 1 P.la)
  Ψ1 x := by
    have e : x (psiS (extN P.u0 (P.t1 * P.t2) P.μ) (extW P.u0 1 P.la)) =
        (x.comp (extK P.u0 (P.t1 * P.t2) P.μ)) (psiS P.μ (numA (P.la P.u0))) := by
      change x (((psiS (extN P.u0 (P.t1 * P.t2) P.μ)).comp (jj K P.u0)) (1 * numA (P.la P.u0))) = _
      rw [psiS_ext, one_mul]; rfl
    rw [e]
    exact P.psi1 _ (P.t12_right x) P.u0 (extK_uL P.u0 (P.t1 * P.t2) P.μ x)
  Ψ3 x y h := by
    refine jj_ext P.u0 ?_
    rw [← extK_psi P.u0 1 P.la y, ← extK_base P.u0 (P.t1 * P.t2) P.μ x]
    exact P.psi3 _ _ (by rw [extK_base P.u0 1 P.la y, h, extK_psi P.u0 (P.t1 * P.t2) P.μ x])
  Ψ4 y x h := by
    refine jj_ext P.u0 ?_
    rw [← extK_psi P.u0 (P.t1 * P.t2) P.μ x, ← extK_base P.u0 1 P.la y]
    exact P.psi4 _ _ (by rw [extK_base P.u0 (P.t1 * P.t2) P.μ x, h, extK_psi P.u0 1 P.la y])
  fibL a := by
    have ha : (a.comp (awayι P.u0)) P.u0 ≠ 0 := baseAway_ne P.u0 a
    obtain ⟨b, hb, hab⟩ := P.fibL_S _ ha
    obtain ⟨y, hy, -⟩ := exists_ext_pt P.u0 (P.t1 * P.t2) P.μ _ b ha hb hab
    exact ⟨y, away_algHom_ext hy⟩
  fibR b := by
    have hb : (b.comp (awayι P.u0)) P.u0 ≠ 0 := baseAway_ne P.u0 b
    obtain ⟨a, ha, hab⟩ := P.fibR_S _ hb
    obtain ⟨y, -, hy⟩ := exists_ext_pt P.u0 (P.t1 * P.t2) P.μ a _ ha hb hab
    exact ⟨y, away_algHom_ext hy⟩
  assoc x₁ x₂ x₃ x₄ e₁ e₂ e₃ e₄ e₅ := by
    refine away_algHom_ext ?_
    rw [← extK_nu P.u0 (P.t1 * P.t2) P.μ x₃, ← extK_nu P.u0 (P.t1 * P.t2) P.μ x₄]
    refine P.assoc (x₁.comp (extK P.u0 (P.t1 * P.t2) P.μ)) (x₂.comp (extK P.u0 (P.t1 * P.t2) P.μ)) _ _
      ?_ ?_ ?_ ?_ ?_
    · rw [extK_pR, extK_pL, e₁]
    · rw [extK_pL, e₂, extK_nu]
    · rw [extK_pR, extK_pR, e₃]
    · rw [extK_pL, extK_pL, e₄]
    · rw [extK_pR, e₅, extK_nu]

/-- The strict group chunk on `Spec S[1/u0]` defined by a `PreChunk`. -/
noncomputable def toStrict' : StrictChunk (k := K) (sR K (Localization.Away P.u0)) := P.toAff.toStrict

end PreChunk

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Law =====
section

/-!
# S4-JacLaw, file O8c: the law maps `m`, `r` and the inverse identities

* `eq_of_ptSet_eq`: reduced points of `Sym^n` with the same support are equal.
* `back_mr`, `back_rm` (supports, two swap steps each): `r(a, m(a,b)) = b` and `m(a, r(a,c)) = c`.
* Generic source `T` (reduced, f.g.): `mOut D3 D2 c0 c1 φa φb : Sym^g → T[1/u3][1/u2]` with points
  `ν2(ν3(a + b + c0) + c1)`, and `rOut D3 D2 c0 c1 φa φc` with points `ν3(a + ν2(c + c1) + c0)` (the inverse
  `l(c,b)` of the other translation is `rOut` with `φa := φb` and its own data); point lemmas `pts_mOut`, `pts_rOut`.
* Composite identities at points: `r_mOut`, `l_mOut`, `m_rOut`, `m_lOut`.
* `LawData K F`: padding tuples and six choice data (roles m, r, l at levels 3 and 2, same `Hn` per level).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

open Classical in
theorem eq_of_ptSet_eq {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}
    {y y' : SymRing k B n →ₐ[k] k} (h : ptSet y = ptSet y') (hc : (ptSet y).card = n) : y = y' := by
  have hi : ∀ z : SymRing k B n →ₐ[k] k, (ptSet z).card = n → Function.Injective (liftTuple z) := by
    intro z hz i j hij
    have h1 : (Finset.univ.image (liftTuple z)).card = (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact hz
    exact Finset.card_image_iff.1 h1 (Finset.mem_coe.2 (Finset.mem_univ i))
      (Finset.mem_coe.2 (Finset.mem_univ j)) hij
  have e := symPt_eq_of_image_eq (hi y hc) (hi y' (h ▸ hc)) h
  rwa [symPt_liftTuple, symPt_liftTuple] at e

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace NuData

open Classical in
/-- `r(a, m(a,b)) = b` on supports: `y3 = A ⊔ B ⊔ C0`, `y2 = ν3(y3) ∪ C1`, `y2' = ν2(y2) ∪ C1`,
`y3' = A ∪ ν2'(y2') ∪ C0` ⇒ `ν3'(y3') = B`. -/
theorem back_mr {d3 d2 r3 r2 : ℕ} (hd3 : d3 = genusFK K F + genusFK K F + r3) (hd2 : d2 = genusFK K F + r2)
    {D3 D3' : NuData K F d3} {D2 D2' : NuData K F d2} (h3 : D3'.Hn = D3.Hn) (h2 : D2'.Hn = D2.Hn)
    {y3 y3' : SymRing K (Places.Rfin K F) d3 →ₐ[K] K} {y2 y2' : SymRing K (Places.Rfin K F) d2 →ₐ[K] K}
    (hy3 : y3 D3.good ≠ 0) (hy2 : y2 D2.good ≠ 0) (hy2' : y2' D2'.good ≠ 0) (hy3' : y3' D3'.good ≠ 0)
    {A Bs C0 C1 : Finset (Places.Rfin K F →ₐ[K] K)} (hA : A.card ≤ genusFK K F) (hB : Bs.card ≤ genusFK K F)
    (hC0 : C0.card ≤ r3) (hC1 : C1.card ≤ r2) (e3 : ptSet y3 = A ∪ Bs ∪ C0) (e2 : ptSet y2 = D3.nuF y3 ∪ C1)
    (e2' : ptSet y2' = D2.nuF y2 ∪ C1) (e3' : ptSet y3' = A ∪ D2'.nuF y2' ∪ C0) : D3'.nuF y3' = Bs := by
  have hE := card_nuF hy3
  obtain ⟨hdE, -, -⟩ := disjoint_of_card_union hE.le hC1 (by rw [← e2, card_ptSet hy2, hd2])
  have s1 : D2'.nuF y2' = D3.nuF y3 :=
    swap_step (P := C1) (Q := D3.nuF y3) (by omega) h2 hy2 hy2' (by rw [e2, Finset.union_comm]) hdE.symm
      (by rw [e2', Finset.union_comm])
  have hAB : (A ∪ Bs).card ≤ genusFK K F + genusFK K F := (Finset.card_union_le _ _).trans (by omega)
  obtain ⟨hABC, hABc, -⟩ := disjoint_of_card_union hAB hC0 (by rw [← e3, card_ptSet hy3, hd3])
  obtain ⟨hAB', -, -⟩ := disjoint_of_card_union hA hB hABc
  exact swap_step (P := A ∪ C0) (Q := Bs) (by omega) h3 hy3 hy3' (by rw [e3, Finset.union_right_comm])
    (Finset.disjoint_union_left.2 ⟨hAB', (Finset.disjoint_union_left.1 hABC).2.symm⟩)
    (by rw [e3', s1, Finset.union_right_comm])

open Classical in
/-- `m(a, r(a,c)) = c` on supports: `y2 = C ⊔ C1`, `y3 = A ∪ ν2(y2) ∪ C0`, `y3' = A ∪ ν3(y3) ∪ C0`,
`y2' = ν3'(y3') ∪ C1` ⇒ `ν2'(y2') = C`. -/
theorem back_rm {d3 d2 r3 r2 : ℕ} (hd3 : d3 = genusFK K F + genusFK K F + r3) (hd2 : d2 = genusFK K F + r2)
    {D3 D3' : NuData K F d3} {D2 D2' : NuData K F d2} (h3 : D3'.Hn = D3.Hn) (h2 : D2'.Hn = D2.Hn)
    {y3 y3' : SymRing K (Places.Rfin K F) d3 →ₐ[K] K} {y2 y2' : SymRing K (Places.Rfin K F) d2 →ₐ[K] K}
    (hy2 : y2 D2.good ≠ 0) (hy3 : y3 D3.good ≠ 0) (hy3' : y3' D3'.good ≠ 0) (hy2' : y2' D2'.good ≠ 0)
    {A Cs C0 C1 : Finset (Places.Rfin K F →ₐ[K] K)} (hA : A.card ≤ genusFK K F) (hC : Cs.card ≤ genusFK K F)
    (hC0 : C0.card ≤ r3) (hC1 : C1.card ≤ r2) (e2 : ptSet y2 = Cs ∪ C1) (e3 : ptSet y3 = A ∪ D2.nuF y2 ∪ C0)
    (e3' : ptSet y3' = A ∪ D3.nuF y3 ∪ C0) (e2' : ptSet y2' = D3'.nuF y3' ∪ C1) : D2'.nuF y2' = Cs := by
  have hE := card_nuF hy2
  have hAE : (A ∪ D2.nuF y2).card ≤ genusFK K F + genusFK K F := (Finset.card_union_le _ _).trans (by omega)
  obtain ⟨hAEC, hAEc, -⟩ := disjoint_of_card_union hAE hC0 (by rw [← e3, card_ptSet hy3, hd3])
  obtain ⟨hAE', -, -⟩ := disjoint_of_card_union hA hE.le hAEc
  have s1 : D3'.nuF y3' = D2.nuF y2 :=
    swap_step (P := A ∪ C0) (Q := D2.nuF y2) (by omega) h3 hy3 hy3' (by rw [e3, Finset.union_right_comm])
      (Finset.disjoint_union_left.2 ⟨hAE', (Finset.disjoint_union_left.1 hAEC).2.symm⟩)
      (by rw [e3', Finset.union_right_comm])
  obtain ⟨hdC, -, -⟩ := disjoint_of_card_union hC hC1 (by rw [← e2, card_ptSet hy2, hd2])
  exact swap_step (P := C1) (Q := Cs) (by omega) h2 hy2 hy2' (by rw [e2, Finset.union_comm]) hdC.symm
    (by rw [e2', s1, Finset.union_comm])

end NuData

section Maps

variable {T : Type*} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]

variable {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3)) (D2 : NuData K F (genusFK K F + r2))
  (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))

end Maps

section Comp

variable {T : Type*} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]
  {T' : Type*} [CommRing T'] [Algebra K T'] [IsReduced T'] [Algebra.FiniteType K T']
  {r3 r2 : ℕ} {D3 D3' : NuData K F (genusFK K F + genusFK K F + r3)} {D2 D2' : NuData K F (genusFK K F + r2)}
  {c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)} {c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)}

theorem card_image_tuple {r : ℕ} (c : Fin r → (Places.Rfin K F →ₐ[K] K)) [DecidableEq (Places.Rfin K F →ₐ[K] K)] :
    (Finset.univ.image c).card ≤ r :=
  Finset.card_image_le.trans_eq (by simp)

end Comp

variable (K F) in
/-- Data of the birational law: padding tuples `c0, c1` and six choice data (roles m, r, l; levels 3 and 2). -/
structure LawData where
  r3 : ℕ
  r2 : ℕ
  c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)
  c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)
  Dm3 : NuData K F (genusFK K F + genusFK K F + r3)
  Dr3 : NuData K F (genusFK K F + genusFK K F + r3)
  Dl3 : NuData K F (genusFK K F + genusFK K F + r3)
  Dm2 : NuData K F (genusFK K F + r2)
  Dr2 : NuData K F (genusFK K F + r2)
  Dl2 : NuData K F (genusFK K F + r2)
  hr3 : Dr3.Hn = Dm3.Hn
  hl3 : Dl3.Hn = Dm3.Hn
  hr2 : Dr2.Hn = Dm2.Hn
  hl2 : Dl2.Hn = Dm2.Hn

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Assoc =====
section

/-!
# S4-JacLaw, file O8e: associativity of the law

* `const_of_mem` (`ℓ(ν(y)) = 1`): at a good `y`, every `f ∈ L(Zdiv (nuF y))` is constant
  (`f · sec y ∈ L(Hn) ∩ B` vanishes on the points of `y`, so it is a multiple of `sec y`).
* `eq_nuF_of_div`: `div u = Zdiv S - Zdiv (nuF y)` with `u ≠ 0` forces `S = nuF y`.
* `div_sec3`, `div_sec2`: the divisor of a good section split along a decomposition of the support.
* **`assoc_sets`**: four `m`-instances with the same data, `m(m(a,b),c)` and `m(a,m(b,c))` have the same support
  (`u = t3 t1 s4 s2 / (s3 s1 t4 t2)` has `div u = Zdiv f - Zdiv f'`).
* **`assoc_mOut`**: associativity at points of the targets of `mOut`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

section Assoc

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem div_mul4 {a b c e : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he : e ≠ 0) :
    (PlacesK.div (a * b * c * e) : Places.Divisor K F) =
      PlacesK.div a + PlacesK.div b + PlacesK.div c + PlacesK.div e := by
  rw [PlacesK.div_mul (mul_ne_zero (mul_ne_zero ha hb) hc) he, PlacesK.div_mul (mul_ne_zero ha hb) hc,
    PlacesK.div_mul ha hb]

namespace NuData

variable {d : ℕ} {D : NuData K F d} {y : SymRing K (Places.Rfin K F) d →ₐ[K] K}

theorem div_sec3 {r : ℕ} {D : NuData K F (genusFK K F + genusFK K F + r)}
    {y : SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F + r) →ₐ[K] K} (hy : y D.good ≠ 0)
    {P Q R : Finset (Places.Rfin K F →ₐ[K] K)} (hP : P.card ≤ genusFK K F) (hQ : Q.card ≤ genusFK K F)
    (hR : R.card ≤ r) (e : ptSet y = P ∪ Q ∪ R) :
    PlacesK.div (incB K F (D.sec y)) = Zdiv P + Zdiv Q + Zdiv R + Zdiv (D.nuF y) - D.Hn := by
  have hc := card_ptSet hy
  rw [e] at hc
  have hPQ : (P ∪ Q).card ≤ genusFK K F + genusFK K F := (Finset.card_union_le _ _).trans (by omega)
  obtain ⟨h1, h2, -⟩ := disjoint_of_card_union hPQ hR hc
  obtain ⟨h3, -, -⟩ := disjoint_of_card_union hP hQ h2
  rw [div_sec' hy, e, Zdiv_union h1, Zdiv_union h3]

theorem div_sec2 {r : ℕ} {D : NuData K F (genusFK K F + r)}
    {y : SymRing K (Places.Rfin K F) (genusFK K F + r) →ₐ[K] K} (hy : y D.good ≠ 0)
    {P R : Finset (Places.Rfin K F →ₐ[K] K)} (hP : P.card ≤ genusFK K F) (hR : R.card ≤ r) (e : ptSet y = P ∪ R) :
    PlacesK.div (incB K F (D.sec y)) = Zdiv P + Zdiv R + Zdiv (D.nuF y) - D.Hn := by
  have hc := card_ptSet hy
  rw [e] at hc
  obtain ⟨h1, -, -⟩ := disjoint_of_card_union hP hR hc
  rw [div_sec' hy, e, Zdiv_union h1]

end NuData

section Pt

variable {T1 T2 T3 T4 : Type*} [CommRing T1] [Algebra K T1] [IsReduced T1] [Algebra.FiniteType K T1]
  [CommRing T2] [Algebra K T2] [IsReduced T2] [Algebra.FiniteType K T2]
  [CommRing T3] [Algebra K T3] [IsReduced T3] [Algebra.FiniteType K T3]
  [CommRing T4] [Algebra K T4] [IsReduced T4] [Algebra.FiniteType K T4]
  {r3 r2 : ℕ} {D3 : NuData K F (genusFK K F + genusFK K F + r3)} {D2 : NuData K F (genusFK K F + r2)}
  {c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)} {c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)}

end Pt

end Assoc

end RamanujanPetersson.JacLaw


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

end Sep

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_GenNS =====
section

/-!
# S4-JacLaw, file O9e (G4 GenNS): nonspecial sets of points

Pure Riemann-Roch on `L(D) = LFK K F D` (no chart algebra):
* `LFK_inf`: `L(D1 ⊓ D2) = L(D1) ⊓ L(D2)`; `ellFK_mono`; `ellFK_step`:
  `ℓ(D + P) + ℓ(D') ≤ ℓ(D' + P) + ℓ(D)` for `D ≤ D'`, `D'(P) = D(P)`.
* `Zdiv_empty`, `Zdiv_insert`, `deg_Zdiv` (`deg (Zdiv S) = #S`); `one_mem_LFK`; `const_of_ellFK_eq_one`.
* the greedy step `exists_add_nonspecial`, `exists_nonspecial_card`;
* `IsNS C` (every `f ∈ L(Zdiv C)` is a constant, the `hC` input of `hrank_of_const`);
  **`exists_nonspecial_avoid`**: a pool `T` with `2g + #X ≤ #T + 1` contains a nonspecial `g`-set disjoint from `X`;
  **`exists_four_nonspecial`**: a pool with `5g ≤ #T + 1` contains four pairwise disjoint nonspecial `g`-sets.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

section GenNS

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem ellFK_def (D : Places.Divisor K F) : ellFK K F D = finrank K (LFK K F D) := rfl

variable [IsAlgClosed K]

theorem Zdiv_empty : Zdiv (∅ : Finset (Places.Rfin K F →ₐ[K] K)) = 0 := Finset.sum_empty

end GenNS

end RamanujanPetersson.JacLaw


end


