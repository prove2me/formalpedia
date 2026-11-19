-- Prove2me | Definitions.Def_RPLib_S4_CDPack30
-- name    : RPLib_S4_CDPack30
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T09:43:14.337066+00:00
-- url     : https://prove2.me/theorems/453861b0-27f5-4027-bb17-4c96b5041bd0
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 30 of 71
-- statement:
--   Part 30 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_Assoc`: S4-JacLaw, file O8e: associativity of the law
--   * `Def_RP_JacLaw_Inst`: S4-JacLaw, file O10e (part A): the law of a `LawData` on `S_g ⊗ S_g`, pulled back to `D(numA _)`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack28c
import Definitions.Def_RPLib_S4_CDPack29b

/-!
# Curve-duality library package, part 30 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_Assoc`: S4-JacLaw, file O8e: associativity of the law
* `Def_RP_JacLaw_Inst`: S4-JacLaw, file O10e (part A): the law of a `LawData` on `S_g ⊗ S_g`, pulled back to `D(numA _)`
-/

set_option autoImplicit false

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

/-- **`ℓ(ν(y)) = 1`**: the complement of a good support is nonspecial. -/
theorem const_of_mem (hd : genusFK K F ≤ d + 1) (hy : y D.good ≠ 0) {f : F}
    (hf : f ∈ LFK K F (Zdiv (D.nuF y))) : ∃ c : K, f = algebraMap K F c := by
  by_cases hf0 : f = 0
  · exact ⟨0, by simp [hf0]⟩
  have hs' := incB_sec_ne_zero hy
  have hfs : f * incB K F (D.sec y) ≠ 0 := mul_ne_zero hf0 hs'
  rw [mem_LFK hf0] at hf
  have hdiv : PlacesK.div (f * incB K F (D.sec y)) + D.Hn =
      (PlacesK.div f + Zdiv (D.nuF y)) + Zdiv (ptSet y) := by
    rw [PlacesK.div_mul hf0 hs', div_sec' hy]; abel
  have hmem : f * incB K F (D.sec y) ∈ LFK K F D.Hn := by
    rw [mem_LFK hfs, hdiv]; exact add_nonneg hf (Zdiv_nonneg _)
  obtain ⟨t, ht⟩ := exists_incB_eq D.Hn_inf hmem
  have ht0 : t ≠ 0 := by rintro rfl; rw [map_zero] at ht; exact hfs ht.symm
  have htL : t ∈ Linf K F D.Hn := by rw [mem_Linf, ht]; exact hmem
  have hz : ∀ i, liftTuple y i t = 0 := by
    intro i
    have hφ : liftTuple y i ∈ ptSet y := (mem_ptSet _ _).2 ⟨i, rfl⟩
    apply apply_eq_zero_of_ord ht0
    have h1 := congrArg (fun E : Places.Divisor K F => E (Sum.inl (ptP (liftTuple y i)))) hdiv
    have h2 := (Finsupp.le_def.1 hf) (Sum.inl (ptP (liftTuple y i)))
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_zero, Pi.zero_apply] at h1 h2
    rw [Zdiv_inl_ptP (ptSet y), if_pos hφ, D.Hn_inf (ptP (liftTuple y i)), add_zero, ← ht] at h1
    have e1 : PlacesK.div (incB K F t) (Sum.inl (ptP (liftTuple y i))) =
        Places.ord (ptP (liftTuple y i)) (incB K F t) := PlacesK.div_apply _ _
    rw [e1] at h1
    omega
  obtain ⟨c, hc⟩ := exists_eq_smul_sec hd hy htL hz
  refine ⟨c, mul_right_cancel₀ hs' ?_⟩
  rw [← ht, ← hc, map_smul, Algebra.smul_def]

/-- A function with divisor `Zdiv S - Zdiv (nuF y)` is constant, so `S = nuF y`. -/
theorem eq_nuF_of_div (hd : genusFK K F ≤ d + 1) (hy : y D.good ≠ 0) {u : F} (hu : u ≠ 0)
    {S : Finset (Places.Rfin K F →ₐ[K] K)}
    (h : (PlacesK.div u : Places.Divisor K F) = Zdiv S - Zdiv (D.nuF y)) : S = D.nuF y := by
  have hmem : u ∈ LFK K F (Zdiv (D.nuF y)) := by
    rw [mem_LFK hu, h, sub_add_cancel]; exact Zdiv_nonneg S
  obtain ⟨c, rfl⟩ := const_of_mem hd hy hmem
  have h0 : (PlacesK.div (algebraMap K F c) : Places.Divisor K F) = 0 :=
    (PlacesK.div_eq_zero_iff (K := K) (F := F) hu).2 ((Places.constField K F).algebraMap_mem c)
  rw [h0, eq_comm, sub_eq_zero] at h
  exact Zdiv_injective h

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

/-- **Associativity on supports.** `M1 = m(a,b)`, `M2 = m(b,c)`, `f = m(M1,c)`, `f' = m(a,M2)` (same data). -/
theorem assoc_sets {r3 r2 : ℕ} {D3 : NuData K F (genusFK K F + genusFK K F + r3)}
    {D2 : NuData K F (genusFK K F + r2)}
    {y31 y32 y33 y34 : SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F + r3) →ₐ[K] K}
    {y21 y22 y23 y24 : SymRing K (Places.Rfin K F) (genusFK K F + r2) →ₐ[K] K}
    (h31 : y31 D3.good ≠ 0) (h32 : y32 D3.good ≠ 0) (h33 : y33 D3.good ≠ 0) (h34 : y34 D3.good ≠ 0)
    (h21 : y21 D2.good ≠ 0) (h22 : y22 D2.good ≠ 0) (h23 : y23 D2.good ≠ 0) (h24 : y24 D2.good ≠ 0)
    {A Bs C C0 C1 : Finset (Places.Rfin K F →ₐ[K] K)} (hA : A.card ≤ genusFK K F) (hB : Bs.card ≤ genusFK K F)
    (hC : C.card ≤ genusFK K F) (hC0 : C0.card ≤ r3) (hC1 : C1.card ≤ r2)
    (e31 : ptSet y31 = A ∪ Bs ∪ C0) (e21 : ptSet y21 = D3.nuF y31 ∪ C1)
    (e32 : ptSet y32 = Bs ∪ C ∪ C0) (e22 : ptSet y22 = D3.nuF y32 ∪ C1)
    (e33 : ptSet y33 = D2.nuF y21 ∪ C ∪ C0) (e23 : ptSet y23 = D3.nuF y33 ∪ C1)
    (e34 : ptSet y34 = A ∪ D2.nuF y22 ∪ C0) (e24 : ptSet y24 = D3.nuF y34 ∪ C1) :
    D2.nuF y23 = D2.nuF y24 := by
  have d31 := div_sec3 h31 hA hB hC0 e31
  have d32 := div_sec3 h32 hB hC hC0 e32
  have d33 := div_sec3 h33 (card_nuF h21).le hC hC0 e33
  have d34 := div_sec3 h34 hA (card_nuF h22).le hC0 e34
  have d21 := div_sec2 h21 (card_nuF h31).le hC1 e21
  have d22 := div_sec2 h22 (card_nuF h32).le hC1 e22
  have d23 := div_sec2 h23 (card_nuF h33).le hC1 e23
  have d24 := div_sec2 h24 (card_nuF h34).le hC1 e24
  have n31 := incB_sec_ne_zero h31
  have n32 := incB_sec_ne_zero h32
  have n33 := incB_sec_ne_zero h33
  have n34 := incB_sec_ne_zero h34
  have n21 := incB_sec_ne_zero h21
  have n22 := incB_sec_ne_zero h22
  have n23 := incB_sec_ne_zero h23
  have n24 := incB_sec_ne_zero h24
  have hnum := mul_ne_zero (mul_ne_zero (mul_ne_zero n23 n21) n34) n32
  have hden := mul_ne_zero (mul_ne_zero (mul_ne_zero n33 n31) n24) n22
  refine eq_nuF_of_div (by omega) h24 (div_ne_zero hnum hden) ?_
  rw [PlacesK.div_div hnum hden, div_mul4 n23 n21 n34 n32, div_mul4 n33 n31 n24 n22, d23, d21, d34, d32, d33,
    d31, d24, d22]
  abel

end NuData

section Pt

variable {T1 T2 T3 T4 : Type*} [CommRing T1] [Algebra K T1] [IsReduced T1] [Algebra.FiniteType K T1]
  [CommRing T2] [Algebra K T2] [IsReduced T2] [Algebra.FiniteType K T2]
  [CommRing T3] [Algebra K T3] [IsReduced T3] [Algebra.FiniteType K T3]
  [CommRing T4] [Algebra K T4] [IsReduced T4] [Algebra.FiniteType K T4]
  {r3 r2 : ℕ} {D3 : NuData K F (genusFK K F + genusFK K F + r3)} {D2 : NuData K F (genusFK K F + r2)}
  {c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)} {c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)}

/-- **Associativity at points**: `m(m(a,b),c) = m(a,m(b,c))` (`x1 : m(a,b)`, `x2 : m(b,c)`, `x3 : m(m(a,b),c)`,
`x4 : m(a,m(b,c))`, glued by the base relations). -/
theorem assoc_mOut {φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T1}
    {φb' φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T2}
    {ψab ψc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T3}
    {χa χbc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T4}
    (x1 : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K)
    (x2 : Localization.Away (padMap (mIn D3 c0 φb' φc) c1 rfl D2.good) →ₐ[K] K)
    (x3 : Localization.Away (padMap (mIn D3 c0 ψab ψc) c1 rfl D2.good) →ₐ[K] K)
    (x4 : Localization.Away (padMap (mIn D3 c0 χa χbc) c1 rfl D2.good) →ₐ[K] K)
    (ha : (mBase D3 D2 c0 c1 χa χbc x4).comp χa = (mBase D3 D2 c0 c1 φa φb x1).comp φa)
    (hb : (mBase D3 D2 c0 c1 φb' φc x2).comp φb' = (mBase D3 D2 c0 c1 φa φb x1).comp φb)
    (hc : (mBase D3 D2 c0 c1 ψab ψc x3).comp ψc = (mBase D3 D2 c0 c1 φb' φc x2).comp φc)
    (hab : (mBase D3 D2 c0 c1 ψab ψc x3).comp ψab = x1.comp (mOut D3 D2 c0 c1 φa φb))
    (hbc : (mBase D3 D2 c0 c1 χa χbc x4).comp χbc = x2.comp (mOut D3 D2 c0 c1 φb' φc)) :
    x3.comp (mOut D3 D2 c0 c1 ψab ψc) = x4.comp (mOut D3 D2 c0 c1 χa χbc) := by
  obtain ⟨y31, y21, h31, h21, e31, e21, em1⟩ := pts_mOut D3 D2 c0 c1 φa φb x1
  obtain ⟨y32, y22, h32, h22, e32, e22, em2⟩ := pts_mOut D3 D2 c0 c1 φb' φc x2
  obtain ⟨y33, y23, h33, h23, e33, e23, em3⟩ := pts_mOut D3 D2 c0 c1 ψab ψc x3
  obtain ⟨y34, y24, h34, h24, e34, e24, em4⟩ := pts_mOut D3 D2 c0 c1 χa χbc x4
  rw [hb] at e32
  rw [hab, em1, hc] at e33
  rw [ha, hbc, em2] at e34
  have key := NuData.assoc_sets h31 h32 h33 h34 h21 h22 h23 h24 (card_ptSet_le _) (card_ptSet_le _)
    (card_ptSet_le _) (card_image_tuple c0) (card_image_tuple c1) e31 e21 e32 e22 e33 e23 e34 e24
  exact eq_of_ptSet_eq (by rw [em3, em4, key]) (by rw [em3, NuData.card_nuF h23])

end Pt

end Assoc

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_Inst =====
section

/-!
# S4-JacLaw, file O10e (part A): the law of a `LawData` on `S_g ⊗ S_g`, pulled back to `D(numA _)`

* `nestK v : T[1/w][1/v] → T[1/(w·num v)]` (`numA v`), `nestK_base`; `nestC f`, `tgtW f` read `v` off the type of `f`.
* `TT K S := S ⊗[K] S` with `iLg`, `iRg`: every `S`-instance through `CommRing S` (the path of `PreChunk K S`;
  a tensor product elaborated directly at `S_g` takes Subalgebra instances and its defeq checks time out).
* `LawData`: `mOutL rOutL lOutL`, `mU rU lU`, `ωm μm ωr ρr ωl lal`, bases `mB rB lB`.
  Base lemmas are in `Def_RP_JacLaw_InstBase`, the point relations in `Def_RP_JacLaw_InstL`.
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section Nest

variable {K : Type u} [Field K] [IsAlgClosed K] {T : Type u} [CommRing T] [Algebra K T] [Algebra.FiniteType K T]
  {w : T} (v : Localization.Away w)

/-- `T[1/w] → T[1/(w·num v)]`. -/
noncomputable def nest1 : Localization.Away w →ₐ[K] Localization.Away (numA v) :=
  liftPt (awayι (numA v)) w fun y => numA_base v (baseAway (numA v) y) (baseAway_ne (numA v) y)

theorem nest1_comp : (nest1 v).comp (awayι w) = awayι (K := K) (numA v) := liftPt_comp _ _ _

/-- `T[1/w][1/v] → T[1/(w·num v)]`. -/
noncomputable def nestK : Localization.Away v →ₐ[K] Localization.Away (numA v) :=
  liftPt (nest1 v) v fun y => (numA_pt v (y.comp (nest1 v))).1 (by
    rw [AlgHom.comp_assoc, nest1_comp]; exact baseAway_ne (numA v) y)

theorem nestK_comp : (nestK (K := K) v).comp (awayι v) = nest1 v := liftPt_comp _ _ _

theorem nestK_base {A : Type u} [CommRing A] [Algebra K A] (y : Localization.Away (numA v) →ₐ[K] K)
    (φ : A →ₐ[K] T) :
    (baseAway w (baseAway v (y.comp (nestK v)))).comp φ = y.comp ((awayι (numA v)).comp φ) := by
  have e : (y.comp (nestK v)).comp (awayι v) = y.comp (nest1 v) := by rw [AlgHom.comp_assoc, nestK_comp]
  show (((y.comp (nestK v)).comp (awayι v)).comp (awayι w)).comp φ = _
  rw [e, AlgHom.comp_assoc y (nest1 v), nest1_comp, AlgHom.comp_assoc]

end Nest

section NestC

variable {K : Type u} [Field K] [IsAlgClosed K] {T : Type u} [CommRing T] [Algebra K T] [Algebra.FiniteType K T]
  {w : T} {A : Type u} [CommRing A] [Algebra K A]

/-- `nestK v ∘ f`, with `v` read off the type of `f` (no re-elaboration of the target). -/
noncomputable abbrev nestC {v : Localization.Away w} (f : A →ₐ[K] Localization.Away v) :
    A →ₐ[K] Localization.Away (numA v) := (nestK v).comp f

/-- The element `v` inverted in the target of `f`. -/
abbrev tgtW {v : Localization.Away w} (_f : A →ₐ[K] Localization.Away v) : Localization.Away w := v

end NestC

section TT

variable (K : Type u) [Field K] (S : Type u) [CommRing S] [Algebra K S]

/-- `S ⊗ S`, with every `S`-instance taken through `CommRing S` (the instance path of `PreChunk K S`). -/
abbrev TT : Type u := S ⊗[K] S

/-- `S → S ⊗ S`, first factor. -/
noncomputable abbrev iLg : S →ₐ[K] TT K S := includeLeft

/-- `S → S ⊗ S`, second factor. -/
noncomputable abbrev iRg : S →ₐ[K] TT K S := includeRight

end TT

section Inst

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- `S_g ⊗ S_g`. -/
abbrev T0 : Type u := TT K (SymRing K (Places.Rfin K F) (genusFK K F))

variable (K F) in
/-- `S_g → S_g ⊗ S_g`, first factor. -/
noncomputable abbrev iL : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T0 K F := iLg K _

variable (K F) in
/-- `S_g → S_g ⊗ S_g`, second factor. -/
noncomputable abbrev iR : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T0 K F := iRg K _

namespace LawData

variable (L : LawData K F)

/-- The law `m(a,b)` of `L` on `T0[1/u3][1/u2]`. -/
noncomputable abbrev mOutL := mOut (T := T0 K F) L.Dm3 L.Dm2 L.c0 L.c1 (iL K F) (iR K F)
/-- `r(a,c)` on `T0[1/v2][1/v3]`. -/
noncomputable abbrev rOutL := rOut (T := T0 K F) L.Dr3 L.Dr2 L.c0 L.c1 (iL K F) (iR K F)
/-- `l(c,b) = ν3(b + ν2(c + c1) + c0)`. -/
noncomputable abbrev lOutL := rOut (T := T0 K F) L.Dl3 L.Dl2 L.c0 L.c1 (iR K F) (iL K F)

noncomputable abbrev mU := tgtW L.mOutL
noncomputable abbrev rU := tgtW L.rOutL
noncomputable abbrev lU := tgtW L.lOutL

noncomputable abbrev ωm : T0 K F := numA L.mU
noncomputable abbrev μm := nestC L.mOutL
noncomputable abbrev ωr : T0 K F := numA L.rU
noncomputable abbrev ρr := nestC L.rOutL
noncomputable abbrev ωl : T0 K F := numA L.lU
noncomputable abbrev lal := nestC L.lOutL

/-- The point of `T0` below a point of `T0[1/u3][1/u2]` (`m`), resp. of the `r`, `l` targets. -/
noncomputable abbrev mB (y : Localization.Away L.mU →ₐ[K] K) :=
  mBase (T := T0 K F) L.Dm3 L.Dm2 L.c0 L.c1 (iL K F) (iR K F) y
noncomputable abbrev rB (y : Localization.Away L.rU →ₐ[K] K) :=
  rBase (T := T0 K F) L.Dr3 L.Dr2 L.c0 L.c1 (iL K F) (iR K F) y
noncomputable abbrev lB (y : Localization.Away L.lU →ₐ[K] K) :=
  rBase (T := T0 K F) L.Dl3 L.Dl2 L.c0 L.c1 (iR K F) (iL K F) y



end LawData

end Inst

end RamanujanPetersson.JacLaw

end


