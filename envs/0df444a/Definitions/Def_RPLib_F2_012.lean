-- Prove2me | Definitions.Def_RPLib_F2_012
-- name    : RPLib_F2_012
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T08:34:35.445096+00:00
-- url     : https://prove2.me/theorems/2bef6603-ef23-41e7-aec6-826f15dc4846
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 012 of 70
-- statement:
--   File 012 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_Assoc`: S4-JacLaw, file O8e: associativity of the law
--   * `S4.Def_RP_JacLaw_Inst`: S4-JacLaw, file O10e (part A): the law of a `LawData` on `S_g ⊗ S_g`, pulled back to `D(numA _)`
--   * `S4.Def_RP_JacLaw_Sep`: S4-JacLaw, file O9 (part Sep): Lagrange elements, separating elements, reduced quotients
--   * `S4.Def_RP_JacLaw_GenNu`: S4-JacLaw, file O9 (part GenNu): existence of `ν`-data good at a given point
--   * `S4.Def_RP_JacLaw_GenNS`: S4-JacLaw, file O9e (G4 GenNS): nonspecial sets of points
--   * `S4.Def_RP_JacLaw_GenRole`: S4-JacLaw, file O9f (G5 GenRole): one role of the configuration, and the witness steps
--   * `S4.Def_RP_JacLaw_GenCfg`: S4-JacLaw, file O9g (G5 GenCfg): the configuration
--   * `S4.Def_RP_JacLaw_GenWit`: S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data
--   * `S4.Def_RP_JacLaw_GeoRed`: S4-JacLaw, file O10c: `Spec R` is geometrically reduced over `K`
--   * `S4.Def_RP_JacChunkA_Val`: Group chunk A2 (unit S4-JacChunkA): pointwise calculus for partial maps, the germ monoid
--   * `S4.Def_RP_JacChunkA_Germ`: Group chunk A2, part 2 (unit S4-JacChunkA): the germ group and the translation subgroup
--   * `S4.Def_RP_JacChunkA_Dom`: Group chunk A3 (unit S4-JacChunkA): maximal domains, iso domains and the cocycle
--   * `S4.Def_RP_JacChunkA_Glue`: Group chunk A4 (unit S4-JacChunkA): gluing copies of `X` from pointwise data
--   * `S4.Def_RP_JacChunkA_G`: Group chunk A5 (unit S4-JacChunkA): the glued scheme `G`
--   * `S4.Def_RP_JacChunkA_RC`: Group chunk A6, part 1 (unit S4-JacChunkA): re-charting
--   * `S4.Def_RP_JacChunkA_Pt`: Group chunk A6, part 2 (unit S4-JacChunkA): the closed points of `G` are `H`
--   * `S4.Def_RP_JacChunkB_Ext`: Group chunk B0 (unit S4-JacChunkB): morphisms into `G` are determined by closed points and glue pointwise
--   * `S4.Def_RP_JacChunkB_Act`: Group chunk B1 (unit S4-JacChunkB): the right action `act : G ×_k X ⟶ G`
--   * `S4.Def_RP_JacChunkB_R`: Group chunk B2 (unit S4-JacChunkB): right translations of `G`
--   * `S4.Def_RP_JacChunkB_Mul`: Group chunk B3 (unit S4-JacChunkB): the multiplication `μ : G ×_k G ⟶ G`
--   * `S4.Def_RP_JacChunkB_Inv`: Group chunk B3, part 2 (unit S4-JacChunkB): the inverse `G ⟶ G` and the unit point
--   * `S4.Def_RP_JacChunkB_Grp`: Group chunk B4 (unit S4-JacChunkB): `G` is a group object over `Spec k`
--   * `S4.Def_RP_JacChunkB_Smooth`: Group chunk B5, part 1 (unit S4-JacChunkB): smoothness, transitivity, the dense open `X`
--   * `S4.Def_RP_JacChunkB_Sep`: Group chunk B5, part 2 (unit S4-JacChunkB): `G` is separated
--   * `S4.Def_RP_JacChunkB_Uniq`: Group chunk B6, part 1 (unit S4-JacChunkB): uniqueness of maps out of `G`
--   * `S4.Def_RP_JacChunkB_GPt`: Group chunk B6, part 2a (unit S4-JacChunkB): `k`-points and translations of a group scheme `G'` over `k`
--   * `S4.Def_RP_JacComplete_Comm`: The Jacobian (unit S4-JacComplete), part `Comm` (L22, abstract half)
--   * `S4.Def_RP_JacComplete_CommH`: The Jacobian (unit S4-JacComplete), part `CommH` (L22: the chunk group is commutative)
--   * `S4.Def_RP_JacComplete_PicH`: The Jacobian (unit S4-JacComplete), part `PicH` (L20, abstract half)
--   * `S4.Def_RP_JacComplete_PicT`: The Jacobian (unit S4-JacComplete), part `PicT` (L20: transports of additivity and rigidity)
--   * `S4.Def_RP_JacComplete_PicK`: The Jacobian (unit S4-JacComplete), part `PicK`: divisor classes over an arbitrary constant field
--   * `S4.Def_RP_JacComplete_PicLw`: The Jacobian (unit S4-JacComplete), part `PicLw` (L20: Weil's law in `Pic`)
--   * `S4.Def_RP_JacComplete_PicMv`: The Jacobian (unit S4-JacComplete), part `PicMv` (L20: generators of `Pic⁰` by the moving lemma)
--   * `S4.Def_RP_JacSymB_Chart`: S4-JacSymB, file F1: the affine charts of a curve (L12)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_011

/-!
# Ramanujan-Petersson curve library (flat edition), file 012 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_Assoc`: S4-JacLaw, file O8e: associativity of the law
* `S4.Def_RP_JacLaw_Inst`: S4-JacLaw, file O10e (part A): the law of a `LawData` on `S_g ⊗ S_g`, pulled back to `D(numA _)`
* `S4.Def_RP_JacLaw_Sep`: S4-JacLaw, file O9 (part Sep): Lagrange elements, separating elements, reduced quotients
* `S4.Def_RP_JacLaw_GenNu`: S4-JacLaw, file O9 (part GenNu): existence of `ν`-data good at a given point
* `S4.Def_RP_JacLaw_GenNS`: S4-JacLaw, file O9e (G4 GenNS): nonspecial sets of points
* `S4.Def_RP_JacLaw_GenRole`: S4-JacLaw, file O9f (G5 GenRole): one role of the configuration, and the witness steps
* `S4.Def_RP_JacLaw_GenCfg`: S4-JacLaw, file O9g (G5 GenCfg): the configuration
* `S4.Def_RP_JacLaw_GenWit`: S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data
* `S4.Def_RP_JacLaw_GeoRed`: S4-JacLaw, file O10c: `Spec R` is geometrically reduced over `K`
* `S4.Def_RP_JacChunkA_Val`: Group chunk A2 (unit S4-JacChunkA): pointwise calculus for partial maps, the germ monoid
* `S4.Def_RP_JacChunkA_Germ`: Group chunk A2, part 2 (unit S4-JacChunkA): the germ group and the translation subgroup
* `S4.Def_RP_JacChunkA_Dom`: Group chunk A3 (unit S4-JacChunkA): maximal domains, iso domains and the cocycle
* `S4.Def_RP_JacChunkA_Glue`: Group chunk A4 (unit S4-JacChunkA): gluing copies of `X` from pointwise data
* `S4.Def_RP_JacChunkA_G`: Group chunk A5 (unit S4-JacChunkA): the glued scheme `G`
* `S4.Def_RP_JacChunkA_RC`: Group chunk A6, part 1 (unit S4-JacChunkA): re-charting
* `S4.Def_RP_JacChunkA_Pt`: Group chunk A6, part 2 (unit S4-JacChunkA): the closed points of `G` are `H`
* `S4.Def_RP_JacChunkB_Ext`: Group chunk B0 (unit S4-JacChunkB): morphisms into `G` are determined by closed points and glue pointwise
* `S4.Def_RP_JacChunkB_Act`: Group chunk B1 (unit S4-JacChunkB): the right action `act : G ×_k X ⟶ G`
* `S4.Def_RP_JacChunkB_R`: Group chunk B2 (unit S4-JacChunkB): right translations of `G`
* `S4.Def_RP_JacChunkB_Mul`: Group chunk B3 (unit S4-JacChunkB): the multiplication `μ : G ×_k G ⟶ G`
* `S4.Def_RP_JacChunkB_Inv`: Group chunk B3, part 2 (unit S4-JacChunkB): the inverse `G ⟶ G` and the unit point
* `S4.Def_RP_JacChunkB_Grp`: Group chunk B4 (unit S4-JacChunkB): `G` is a group object over `Spec k`
* `S4.Def_RP_JacChunkB_Smooth`: Group chunk B5, part 1 (unit S4-JacChunkB): smoothness, transitivity, the dense open `X`
* `S4.Def_RP_JacChunkB_Sep`: Group chunk B5, part 2 (unit S4-JacChunkB): `G` is separated
* `S4.Def_RP_JacChunkB_Uniq`: Group chunk B6, part 1 (unit S4-JacChunkB): uniqueness of maps out of `G`
* `S4.Def_RP_JacChunkB_GPt`: Group chunk B6, part 2a (unit S4-JacChunkB): `k`-points and translations of a group scheme `G'` over `k`
* `S4.Def_RP_JacComplete_Comm`: The Jacobian (unit S4-JacComplete), part `Comm` (L22, abstract half)
* `S4.Def_RP_JacComplete_CommH`: The Jacobian (unit S4-JacComplete), part `CommH` (L22: the chunk group is commutative)
* `S4.Def_RP_JacComplete_PicH`: The Jacobian (unit S4-JacComplete), part `PicH` (L20, abstract half)
* `S4.Def_RP_JacComplete_PicT`: The Jacobian (unit S4-JacComplete), part `PicT` (L20: transports of additivity and rigidity)
* `S4.Def_RP_JacComplete_PicK`: The Jacobian (unit S4-JacComplete), part `PicK`: divisor classes over an arbitrary constant field
* `S4.Def_RP_JacComplete_PicLw`: The Jacobian (unit S4-JacComplete), part `PicLw` (L20: Weil's law in `Pic`)
* `S4.Def_RP_JacComplete_PicMv`: The Jacobian (unit S4-JacComplete), part `PicMv` (L20: generators of `Pic⁰` by the moving lemma)
* `S4.Def_RP_JacSymB_Chart`: S4-JacSymB, file F1: the affine charts of a curve (L12)
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

end LawData

end Inst

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

-- ===== S4.Def_RP_JacLaw_GenNu =====
section

/-!
# S4-JacLaw, file O9 (part GenNu): existence of `ν`-data good at a given point

* `crossVec_ne_zero_of_finrank_ker`: an `m × (m+1)` matrix with kernel of dimension `≤ 1` has a nonzero cofactor vector.
* `crossVec_evMat_ne_zero`: if every element of `L` vanishing at `a_1..a_d` is a multiple of `s ≠ 0`, the evaluation
  matrix of a basis of `L` has a nonzero cofactor vector.
* `exists_dual_sep`, `exists_lift_li`: separating functionals, lifts of a basis of `B/(s)`.
* `NuData.good_ne_zero_of`: the four factors of `good` at `symPt a` from hyperplane, independence and separation data.
* `exists_nuData`: given `Hn ≥ 0` at infinity of degree `d + g`, `s` with exact pole divisor `Hn`, distinct points
  `a_1..a_d` such that `L(Hn) ∩ B` vanishing at them is the line of `s`, and the `d + g` zeros `Z` of `s`, there is
  `D : NuData` with `D.Hn = Hn`, `symPt a D.good ≠ 0` and `D.sec (symPt a) = c • s`, `c ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

section AbsNu

variable {k : Type*} [Field k]

theorem crossVec_ne_zero_of_finrank_ker {m : ℕ} (M : Matrix (Fin m) (Fin (m + 1)) k)
    (hk : finrank k (LinearMap.ker M.mulVecLin) ≤ 1) : crossVec M ≠ 0 := by
  intro hc
  have hsing : ∀ v : Fin (m + 1) → k, ∃ x : Fin (m + 1) → k, x ≠ 0 ∧ x ∈ LinearMap.ker M.mulVecLin ∧
      v ⬝ᵥ x = 0 := by
    intro v
    have hdet : (Matrix.of (Fin.cons v (fun i => M i) : Fin (m + 1) → Fin (m + 1) → k)).det = 0 := by
      rw [det_cons, hc]
      simp
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine ⟨x, hx0, ?_, ?_⟩
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      funext i
      have := congr_fun hx i.succ
      simpa [Matrix.mulVec] using this
    · have := congr_fun hx 0
      simpa [Matrix.mulVec] using this
  obtain ⟨x0, hx00, hx0k, -⟩ := hsing 0
  obtain ⟨u, hu⟩ := finrank_le_one_iff.mp hk
  have hu0 : (u : Fin (m + 1) → k) ≠ 0 := by
    intro h0
    obtain ⟨c, hc'⟩ := hu ⟨x0, hx0k⟩
    apply hx00
    have := congrArg Subtype.val hc'
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact this.symm
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hu0
  obtain ⟨x, hxne, hxk, hxv⟩ := hsing (Pi.single j 1)
  obtain ⟨c, hcx⟩ := hu ⟨x, hxk⟩
  have hx' : x = c • (u : Fin (m + 1) → k) := by
    have := congrArg Subtype.val hcx
    simpa using this.symm
  rw [hx', single_dotProduct, one_mul, Pi.smul_apply, smul_eq_mul] at hxv
  rcases mul_eq_zero.mp hxv with h | h
  · exact hxne (by rw [hx', h, zero_smul])
  · exact hj h

theorem crossVec_evMat_ne_zero {B : Type*} [CommRing B] [Algebra k B] {d : ℕ} {L : Submodule k B}
    (b : Basis (Fin (d + 1)) k L) (a : Fin d → (B →ₐ[k] k)) {s : B} (hsL : s ∈ L) (hs0 : s ≠ 0)
    (hrank : ∀ t ∈ L, (∀ i, a i t = 0) → ∃ c : k, t = c • s) :
    crossVec (evMat a (fun l => (b l : B))) ≠ 0 := by
  apply crossVec_ne_zero_of_finrank_ker
  have hv0 : b.equivFun ⟨s, hsL⟩ ≠ 0 := by
    intro h0
    apply hs0
    have h1 : (⟨s, hsL⟩ : L) = 0 := b.equivFun.injective (by rw [map_zero]; exact h0)
    exact congrArg Subtype.val h1
  have hle : LinearMap.ker (evMat a (fun l => (b l : B))).mulVecLin ≤ k ∙ b.equivFun ⟨s, hsL⟩ := by
    intro y hy
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy
    have ht : ((b.equivFun.symm y : L) : B) = ∑ l, y l • (b l : B) := by
      simp only [Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul]
    have hz : ∀ i, a i (b.equivFun.symm y : L) = 0 := by
      intro i
      have h1 := congr_fun hy i
      simp only [Matrix.mulVec, dotProduct, evMat, Matrix.of_apply, Pi.zero_apply] at h1
      rw [ht, map_sum]
      refine (Finset.sum_congr rfl fun l _ => ?_).trans h1
      rw [map_smul, smul_eq_mul, mul_comm]
    obtain ⟨c, hc⟩ := hrank _ (b.equivFun.symm y).2 hz
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    have h2 : b.equivFun.symm y = c • (⟨s, hsL⟩ : L) := Subtype.ext hc
    calc c • b.equivFun ⟨s, hsL⟩ = b.equivFun (c • (⟨s, hsL⟩ : L)) := (map_smul b.equivFun c _).symm
      _ = b.equivFun (b.equivFun.symm y) := by rw [h2]
      _ = y := b.equivFun.apply_symm_apply y
  calc finrank k (LinearMap.ker (evMat a (fun l => (b l : B))).mulVecLin) ≤
        finrank k (k ∙ b.equivFun ⟨s, hsL⟩) := Submodule.finrank_mono hle
    _ = 1 := finrank_span_singleton hv0

theorem exists_kerData {B : Type*} [CommRing B] [Algebra k B] {d : ℕ} (L : Submodule k B)
    (hL : FiniteDimensional k L) (hfr : finrank k L = d + 1) (a : Fin d → (B →ₐ[k] k)) (ha : Function.Injective a)
    {s : B} (hsL : s ∈ L) (hs0 : s ≠ 0) (hrank : ∀ t ∈ L, (∀ i, a i t = 0) → ∃ c : k, t = c • s) :
    ∃ (h : Fin (d + 1) → B) (χ : Fin d → B) (l0 : Fin (d + 1)), (∀ l, h l ∈ L) ∧ LinearIndependent k h ∧
      symPt a (kerVec k χ h l0) ≠ 0 ∧ ∃ c : k, c ≠ 0 ∧ sPt a χ h = c • s := by
  let b := finBasisSub L hL hfr
  have hcross := crossVec_evMat_ne_zero b a hsL hs0 hrank
  obtain ⟨χ, hχ⟩ := exists_delta a ha
  have hdetχ : (evMat a χ).det = 1 := by
    have he1 : evMat a χ = 1 := by
      ext i m
      rw [evMat, Matrix.of_apply, hχ, Matrix.one_apply]
    rw [he1, Matrix.det_one]
  obtain ⟨l0, hl0⟩ : ∃ l0, crossVec (evMat a (fun l => (b l : B))) l0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hcross (funext hc)
  have hker : symPt a (kerVec k χ (fun l => (b l : B)) l0) ≠ 0 := by
    rw [symPt_kerVec, hdetχ, one_mul]
    exact hl0
  have hli : LinearIndependent k (fun l => (b l : B)) :=
    b.linearIndependent.map' L.subtype (Submodule.ker_subtype _)
  have hS0 := sPt_ne_zero hli hker
  have hSmem : sPt a χ (fun l => (b l : B)) ∈ L :=
    Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (b l).2
  obtain ⟨c, hc⟩ := hrank _ hSmem (apply_sPt a χ _)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hS0 hc
  exact ⟨fun l => (b l : B), χ, l0, fun l => (b l).2, hli, hker, c, hc0, hc⟩

theorem exists_dual_sep {B : Type*} [AddCommGroup B] [Module k B] {n : ℕ} (h : Fin n → B) (W : Submodule k B)
    (v : Fin n → k) (hv : ∑ l, v l • h l ∉ W) :
    ∃ f : (Fin n → k) →ₗ[k] k, f v ≠ 0 ∧ ∀ y : Fin n → k, ∑ l, y l • h l ∈ W → f y = 0 := by
  set P : Submodule k (Fin n → k) := W.comap (Fintype.linearCombination k h) with hP
  have hvP : v ∉ P := hv
  obtain ⟨f, hf, hfP⟩ := P.exists_dual_map_eq_bot_of_notMem hvP inferInstance
  refine ⟨f, hf, fun y hy => ?_⟩
  have h1 : f y ∈ P.map f := Submodule.mem_map_of_mem (p := P) hy
  rw [hfP, Submodule.mem_bot] at h1
  exact h1

theorem exists_lift_li {B : Type*} [CommRing B] [Algebra k B] (s : B) (hfin : Module.Finite k (B ⧸ Ideal.span {s}))
    {N : ℕ} (hN : finrank k (B ⧸ Ideal.span {s}) = N) :
    ∃ e : Fin N → B, LinearIndependent k (fun i => Ideal.Quotient.mkₐ k (Ideal.span {s}) (e i)) := by
  let bq := Module.finBasisOfFinrankEq k (B ⧸ Ideal.span {s}) hN
  choose e he using fun i => Ideal.Quotient.mkₐ_surjective k (Ideal.span {s}) (bq i)
  refine ⟨e, ?_⟩
  have h1 : (fun i => Ideal.Quotient.mkₐ k (Ideal.span {s}) (e i)) = bq := funext he
  rw [h1]
  exact bq.linearIndependent

theorem famDet_res_ne_zero {B : Type*} [CommRing B] [Algebra k B] {S : Type*} [CommRing S] [Algebra k S] {n : ℕ}
    (c : Fin n → S) (h : Fin n → B) {L L' : Submodule k B} (hhL : ∀ l, ∀ y ∈ L', h l * y ∈ L) {a N : ℕ}
    (α : Basis (Fin a) k L') (β : Basis (Fin a ⊕ Fin N) k L) {e : Fin N → B} (he : ∀ i, e i ∈ L) (w : B)
    (hw : ∀ i, w * e i ∈ L) (x : S →ₐ[k] k) (hfin : Module.Finite k (B ⧸ Ideal.span {secAt c h x}))
    (hP : x (famPres c h hhL α β he) ≠ 0)
    (hli : LinearIndependent k fun i => Ideal.Quotient.mkₐ k (Ideal.span {secAt c h x}) (e i))
    (hcard : finrank k (B ⧸ Ideal.span {secAt c h x}) = N) (Z : Finset (B →ₐ[k] k))
    (hZ : ∀ φ ∈ Z, φ (secAt c h x) = 0) (hZc : Z.card = N) (hw0 : Set.InjOn (fun φ : B →ₐ[k] k => φ w) Z) :
    resultant ((famDet c h hhL α β he w hw).map x.toRingHom) (derivative ((famDet c h hhL α β he w hw).map
      x.toRingHom)) N N ≠ 0 := by
  have hmap := map_famDet_eq_li c h hhL α β he w hw x hfin hP hli hcard
  have hchar : LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {secAt c h x})
      (Ideal.Quotient.mkₐ k (Ideal.span {secAt c h x}) w)) = ∏ φ ∈ Z, (X - C (φ w)) :=
    charpoly_eq_prod_of_card (secAt c h x) Z hZ hfin (hZc.trans hcard.symm) w
  have hres := resultant_prod_ne_zero Z w hw0 hP
  rw [hZc] at hres
  rw [hmap]
  erw [hchar]
  exact hres

end AbsNu

section GenNu

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem notMem_Linf_of_exactPoleH {s : Places.Rfin K F} {Hn : Places.Divisor K F} (hs0 : s ≠ 0)
    (hs : ExactPoleH s Hn) (P' : HeightOneSpectrum (Places.Rinf K F)) : s ∉ Linf K F (Hn - ptInf P') := by
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  intro hm
  rw [mem_Linf, mem_LFK hs', Finsupp.le_def] at hm
  have h1 := hm (Sum.inr P')
  have h2 := hs P'
  simp [ptInf] at h1
  omega

theorem divDeg_nsmul (D : Places.Divisor K F) (n : ℕ) :
    Places.Divisor.deg (n • D) = n * Places.Divisor.deg D := by
  induction n with
  | zero => simp [Places.Divisor.deg]
  | succ n ih => rw [succ_nsmul, PlacesK.Divisor.deg_add, ih]; push_cast; ring

variable [IsAlgClosed K]

namespace NuData

variable {d : ℕ} (D : NuData K F d)

/-- **`good` at `symPt a`** from its four ingredients. -/
theorem good_ne_zero_of (a : Fin d → (Places.Rfin K F →ₐ[K] K))
    (hker : symPt a (kerVec K D.χ D.h D.l0) ≠ 0)
    (hlam : ∀ P', D.lam P' (fun l => symPt a (kerVec K D.χ D.h l)) ≠ 0)
    (hli : LinearIndependent K fun i => Ideal.Quotient.mkₐ K (Ideal.span {sPt a D.χ D.h}) (D.e i))
    (Z : Finset (Places.Rfin K F →ₐ[K] K)) (hZ : ∀ φ ∈ Z, φ (sPt a D.χ D.h) = 0)
    (hZc : Z.card = d + genusFK K F) (hw0 : Set.InjOn (fun φ : Places.Rfin K F →ₐ[K] K => φ D.w0) Z) :
    symPt a D.good ≠ 0 := by
  have hs0 : D.sec (symPt a) ≠ 0 := by rw [sec_symPt]; exact sPt_ne_zero D.h_li hker
  have hnot : ∀ P', D.sec (symPt a) ∉ Linf K F (D.Hn - ptInf P') := fun P' hm =>
    hlam P' (D.lam_spec P' _ hm)
  have hex : ExactPoleH (D.sec (symPt a)) D.Hn := exactPoleH_of_not_mem hs0 (D.sec_mem _) hnot
  have hfr : finrank K (Places.Rfin K F ⧸ Ideal.span {D.sec (symPt a)}) = d + genusFK K F := by
    have h := finrank_quot_of_exactPoleH hs0 D.Hn_inf hex
    rw [D.Hn_deg] at h
    exact_mod_cast h
  have hfin : Module.Finite K (Places.Rfin K F ⧸ Ideal.span {D.sec (symPt a)}) := PlacesK.FDQ.finite _ hs0
  have hpres : symPt a (D.pres D.w0) ≠ 0 := by
    rw [NuData.pres, map_famPres]
    exact presDet_ne_zero_of_linIndep (D.sec (symPt a)) _ (D.α D.w0) (D.β D.w0) (D.he D.w0) hs0 hli
  have hres : symPt a (resultant (D.det D.w0) (derivative (D.det D.w0)) (d + genusFK K F)
      (d + genusFK K F)) ≠ 0 := by
    intro h0
    have h1 : resultant ((D.det D.w0).map (symPt a).toRingHom)
        (derivative ((D.det D.w0).map (symPt a).toRingHom)) (d + genusFK K F) (d + genusFK K F) = 0 := by
      rw [derivative_map, resultant_map_map]
      exact h0
    exact famDet_res_ne_zero (kerVec K D.χ D.h) D.h (D.hhL D.w0) (D.α D.w0) (D.β D.w0) (D.he D.w0) D.w0
      (D.hw D.w0) (symPt a) hfin hpres hli hfr Z hZ hZc hw0 h1
  rw [NuData.good, map_mul, map_mul, map_mul, map_prod]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero hker ?_) hpres) hres
  rw [Finset.prod_ne_zero_iff]
  intro P' _
  rw [lamS_apply]
  exact hlam P'

end NuData

set_option maxHeartbeats 400000 in
/-- **Existence of `ν`-data good at a point** (G2). -/
theorem exists_nuData {d : ℕ} (hdg : genusFK K F ≤ d + 1) {Hn : Places.Divisor K F} (hHn : IsInf Hn)
    (hHn0 : 0 ≤ Hn) (hdeg : Places.Divisor.deg Hn = ((d + genusFK K F : ℕ) : ℤ))
    {s : Places.Rfin K F} (hs0 : s ≠ 0) (hs : ExactPoleH s Hn)
    (a : Fin d → (Places.Rfin K F →ₐ[K] K)) (ha : Function.Injective a)
    (hrank : ∀ t ∈ Linf K F Hn, (∀ i, a i t = 0) → ∃ c : K, t = c • s)
    (Z : Finset (Places.Rfin K F →ₐ[K] K)) (hZ : ∀ φ ∈ Z, φ s = 0) (hZc : Z.card = d + genusFK K F) :
    ∃ D : NuData K F d, D.Hn = Hn ∧ symPt a D.good ≠ 0 ∧ ∃ c : K, c ≠ 0 ∧ sPt a D.χ D.h = c • s := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have hfr : finrank K (Linf K F Hn) = d + 1 := by
    have h1 := finrank_Linf_eq hk hHn (by rw [hdeg]; push_cast; omega)
    rw [hdeg] at h1
    push_cast at h1
    omega
  have hsmem : s ∈ Linf K F Hn := mem_Linf_of_exactPoleH hHn hs
  obtain ⟨h, χ, l0, hmem, hli, hker, c, hc0, hc⟩ :=
    exists_kerData (Linf K F Hn) (finiteDimensional_Linf _) hfr a ha hsmem hs0 hrank
  have hS0 : sPt a χ h ≠ 0 := sPt_ne_zero hli hker
  have hSmem : sPt a χ h ∈ Linf K F Hn := by
    rw [hc]
    exact Submodule.smul_mem _ _ hsmem
  have hnot : ∀ P', sPt a χ h ∉ Linf K F (Hn - ptInf P') := by
    intro P' hm
    apply notMem_Linf_of_exactPoleH hs0 hs P'
    have := Submodule.smul_mem _ c⁻¹ hm
    rwa [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  have hex : ExactPoleH (sPt a χ h) Hn := exactPoleH_of_not_mem hS0 hSmem hnot
  have hfin : Module.Finite K (Places.Rfin K F ⧸ Ideal.span {sPt a χ h}) := PlacesK.FDQ.finite _ hS0
  have hfrq : finrank K (Places.Rfin K F ⧸ Ideal.span {sPt a χ h}) = d + genusFK K F := by
    have h1 := finrank_quot_of_exactPoleH hS0 hHn hex
    rw [hdeg] at h1
    exact_mod_cast h1
  obtain ⟨e, he⟩ := exists_lift_li (sPt a χ h) hfin hfrq
  choose lam hlam1 hlam2 using fun P' => exists_dual_sep h (Linf K F (Hn - ptInf P'))
    (fun l => symPt a (kerVec K χ h l)) (hnot P')
  obtain ⟨w0, hw0⟩ := exists_injOn (K := K) Z
  obtain ⟨G, hG0, hGinf, hGe⟩ : ∃ G : Places.Divisor K F, 0 ≤ G ∧ IsInf G ∧
      ∀ i, poleDiv (K := K) (incB K F (e i)) ≤ G :=
    ⟨∑ i, poleDiv (K := K) (incB K F (e i)), Finset.sum_nonneg fun i _ => le_sup_right,
      Finset.sum_induction _ IsInf (fun _ _ h1 h2 => h1.add h2) (fun _ => by simp) fun i _ => isInf_poleDiv (e i),
      fun i => Finset.single_le_sum (f := fun j => poleDiv (K := K) (incB K F (e j))) (fun j _ => le_sup_right)
        (Finset.mem_univ i)⟩
  refine ⟨⟨Hn, hHn, hdeg, h, hmem, hli, χ, l0, lam, hlam2, Hn + G + (2 * genusFK K F) • Hn,
    (hHn.add hGinf).add (hHn.nsmul _), ?_, e, fun i => ?_, w0⟩, rfl, ?_, c, hc0, hc⟩
  · have e1 : Hn + G + (2 * genusFK K F) • Hn - Hn = G + (2 * genusFK K F) • Hn := by abel
    rw [e1, PlacesK.Divisor.deg_add, divDeg_nsmul, hdeg]
    have h0 := deg_nonneg_of_nonneg hG0
    push_cast
    nlinarith [sq_nonneg ((genusFK K F : ℤ) - 1), sq_nonneg (genusFK K F : ℤ),
      mul_nonneg (Nat.cast_nonneg (α := ℤ) (genusFK K F)) (Nat.cast_nonneg (α := ℤ) d)]
  · refine Linf_mono ?_ (mem_Linf_poleDiv (e i))
    have h1 : poleDiv (K := K) (incB K F (e i)) ≤ G := hGe i
    have h2 : G ≤ Hn + G := le_add_of_nonneg_left hHn0
    have h3 : Hn + G ≤ Hn + G + (2 * genusFK K F) • Hn := le_add_of_nonneg_right (nsmul_nonneg hHn0 _)
    exact h1.trans (h2.trans h3)
  · exact NuData.good_ne_zero_of _ a hker hlam1 he Z (fun φ hφ => by
      show φ (sPt a χ h) = 0
      rw [hc, map_smul, hZ φ hφ, smul_zero]) hZc hw0

end GenNu

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

theorem LFK_inf (D1 D2 : Places.Divisor K F) : LFK K F (D1 ⊓ D2) = LFK K F D1 ⊓ LFK K F D2 := by
  ext f
  show f ∈ (ffDataK K F).LD (D1 ⊓ D2) ↔ f ∈ (ffDataK K F).LD D1 ⊓ (ffDataK K F).LD D2
  rw [Submodule.mem_inf, Data.mem_LD, Data.mem_LD, Data.mem_LD]
  constructor
  · intro h
    refine ⟨fun i => (h i).trans ?_, fun i => (h i).trans ?_⟩
    · rw [Finsupp.inf_apply, WithZero.exp_le_exp]; exact inf_le_left
    · rw [Finsupp.inf_apply, WithZero.exp_le_exp]; exact inf_le_right
  · rintro ⟨h1, h2⟩ i
    rw [Finsupp.inf_apply]
    rcases le_total (D1 i) (D2 i) with h | h
    · rw [inf_of_le_left h]; exact h1 i
    · rw [inf_of_le_right h]; exact h2 i

theorem ellFK_mono {D D' : Places.Divisor K F} (h : D ≤ D') : ellFK K F D ≤ ellFK K F D' := by
  have := finiteDimensional_LFK (K := K) (F := F) D'
  rw [ellFK_def, ellFK_def]
  exact Submodule.finrank_mono ((ffDataK K F).LD_mono h)

/-- The dimension step: `ℓ(D + P) + ℓ(D') ≤ ℓ(D' + P) + ℓ(D)` for `D ≤ D'` with `D'(P) = D(P)`. -/
theorem ellFK_step {D D' : Places.Divisor K F} (P : Places.Place K F) (hle : D ≤ D') (hP : D' P = D P) :
    ellFK K F (D + Finsupp.single P 1) + ellFK K F D' ≤ ellFK K F (D' + Finsupp.single P 1) + ellFK K F D := by
  have hinf : (D + Finsupp.single P 1) ⊓ D' = D := by
    ext Q
    rw [Finsupp.inf_apply, Finsupp.add_apply]
    by_cases hQ : Q = P
    · rw [hQ, Finsupp.single_eq_same, hP]
      exact inf_of_le_right (by omega)
    · rw [Finsupp.single_apply, if_neg (Ne.symm hQ), add_zero]
      exact inf_of_le_left (hle Q)
  have h0 : (0 : Places.Divisor K F) ≤ Finsupp.single P 1 := Finsupp.single_nonneg.2 zero_le_one
  have hsup : LFK K F (D + Finsupp.single P 1) ⊔ LFK K F D' ≤ LFK K F (D' + Finsupp.single P 1) :=
    sup_le ((ffDataK K F).LD_mono (add_le_add hle le_rfl))
      ((ffDataK K F).LD_mono (le_add_of_nonneg_right h0))
  have := finiteDimensional_LFK (K := K) (F := F) (D + Finsupp.single P 1)
  have := finiteDimensional_LFK (K := K) (F := F) D'
  have := finiteDimensional_LFK (K := K) (F := F) (D' + Finsupp.single P 1)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LFK K F (D + Finsupp.single P 1)) (LFK K F D')
  rw [← LFK_inf, hinf] at h1
  have h2 := Submodule.finrank_mono hsup
  rw [ellFK_def, ellFK_def, ellFK_def, ellFK_def]
  omega

variable [IsAlgClosed K]

theorem Zdiv_insert {S : Finset (Places.Rfin K F →ₐ[K] K)} {φ : Places.Rfin K F →ₐ[K] K} (h : φ ∉ S) :
    Zdiv (insert φ S) = Zdiv S + Finsupp.single (Sum.inl (ptP φ)) 1 := by
  unfold Zdiv
  rw [Finset.sum_insert h, add_comm]

theorem one_mem_LFK {D : Places.Divisor K F} (hD : 0 ≤ D) : (1 : F) ∈ LFK K F D := by
  have h : (1 : F) ∈ LFK K F 0 := by
    rw [LFK_zero_eq]
    exact (Subalgebra.mem_toSubmodule _).2 (Subalgebra.one_mem _)
  exact (ffDataK K F).LD_mono hD h

/-- `ℓ(D) = 1` for `D ≥ 0`: every element of `L(D)` is a constant. -/
theorem const_of_ellFK_eq_one {D : Places.Divisor K F} (hD : 0 ≤ D) (h : ellFK K F D = 1) :
    ∀ f ∈ LFK K F D, ∃ c : K, f = algebraMap K F c := by
  intro f hf
  have h1 : (⟨1, one_mem_LFK hD⟩ : LFK K F D) ≠ 0 := fun e => one_ne_zero (congrArg Subtype.val e)
  rw [ellFK_def] at h
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ h1).1 h ⟨f, hf⟩
  refine ⟨c, ?_⟩
  have e : c • (1 : F) = f := congrArg Subtype.val hc
  rw [← e, Algebra.smul_def, mul_one]

variable (K F) in
/-- `C` is nonspecial: `L(Zdiv C)` is the constants. -/
def IsNS (C : Finset (Places.Rfin K F →ₐ[K] K)) : Prop :=
  ∀ f ∈ LFK K F (Zdiv C), ∃ c : K, f = algebraMap K F c

theorem ellFK_union_ge {C T : Finset (Places.Rfin K F →ₐ[K] K)} (hCT : Disjoint C T)
    (h1 : ellFK K F (Zdiv C) = 1) (h2 : ∀ P ∈ T, 2 ≤ ellFK K F (Zdiv (insert P C))) :
    ∀ S ⊆ T, 1 + S.card ≤ ellFK K F (Zdiv (C ∪ S)) := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; rw [Finset.union_empty, Finset.card_empty, h1]
  | insert P S hP ih =>
    intro hS
    have hPT : P ∈ T := hS (Finset.mem_insert_self P S)
    have hST : S ⊆ T := (Finset.subset_insert P S).trans hS
    have hPC : P ∉ C := Finset.disjoint_right.1 hCT hPT
    have hPCS : P ∉ C ∪ S := by
      rw [Finset.mem_union]; exact fun h => h.elim hPC hP
    have hle : Zdiv C ≤ Zdiv (C ∪ S) := by
      rw [Zdiv_union (Finset.disjoint_of_subset_right hST hCT)]
      exact le_add_of_nonneg_right (Zdiv_nonneg S)
    have hval : Zdiv (C ∪ S) (Sum.inl (ptP P)) = Zdiv C (Sum.inl (ptP P)) := by
      rw [Zdiv_inl_ptP, Zdiv_inl_ptP, if_neg hPCS, if_neg hPC]
    have key := ellFK_step (Sum.inl (ptP P)) hle hval
    rw [← Zdiv_insert hPC, ← Zdiv_insert hPCS, h1] at key
    rw [Finset.union_insert, Finset.card_insert_of_notMem hP]
    have := ih hST
    have := h2 P hPT
    omega

theorem deg_Zdiv (S : Finset (Places.Rfin K F →ₐ[K] K)) : (Zdiv S).deg = (S.card : ℤ) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Zdiv_empty, Finset.card_empty]
    simp [Places.Divisor.deg]
  | insert a S ha ih =>
    have hd : Places.Place.deg (Sum.inl (ptP a) : Places.Place K F) = 1 := deg_eq_one (K := K) (ptP a)
    rw [Zdiv_insert ha, PlacesK.Divisor.deg_add, ih, PlacesK.Divisor.deg_single, hd,
      Finset.card_insert_of_notMem ha]
    push_cast; ring

theorem ellFK_zero' : ellFK K F 0 = 1 := ellFK_zero_of_bot constField_eq_bot'

/-- **Greedy step**: a nonspecial `C` with `#C < g` and a disjoint pool `T` with `#C + #T ≥ 2g - 1`
has a point `P ∈ T` with `C + P` nonspecial. -/
theorem exists_add_nonspecial {C T : Finset (Places.Rfin K F →ₐ[K] K)} (hCT : Disjoint C T)
    (h1 : ellFK K F (Zdiv C) = 1) (hC : C.card < genusFK K F) (hT : 2 * genusFK K F ≤ C.card + T.card + 1) :
    ∃ P ∈ T, ellFK K F (Zdiv (insert P C)) = 1 := by
  by_contra hne0
  have hne : ∀ P ∈ T, ellFK K F (Zdiv (insert P C)) ≠ 1 := fun P hP h => hne0 ⟨P, hP, h⟩
  have h2 : ∀ P ∈ T, 2 ≤ ellFK K F (Zdiv (insert P C)) := by
    intro P hP
    have := hne P hP
    have hPC : P ∉ C := Finset.disjoint_right.1 hCT hP
    have hm : ellFK K F (Zdiv C) ≤ ellFK K F (Zdiv (insert P C)) := ellFK_mono (by
      rw [Zdiv_insert hPC]; exact le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one))
    omega
  have hge := ellFK_union_ge hCT h1 h2 T (Finset.Subset.refl T)
  have hdeg : (Zdiv (C ∪ T)).deg = ((C.card + T.card : ℕ) : ℤ) := by
    rw [deg_Zdiv, Finset.card_union_of_disjoint hCT]
  have hrr := ellFK_eq_of_deg (constField_eq_bot' (K := K) (F := F)) (D := Zdiv (C ∪ T))
    (by rw [hdeg]; push_cast; omega)
  rw [hdeg] at hrr
  push_cast at hrr
  omega

theorem exists_nonspecial_card (T : Finset (Places.Rfin K F →ₐ[K] K)) (hT : 2 * genusFK K F ≤ T.card + 1) :
    ∀ i ≤ genusFK K F, ∃ C ⊆ T, C.card = i ∧ ellFK K F (Zdiv C) = 1 := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨∅, Finset.empty_subset _, Finset.card_empty, by rw [Zdiv_empty]; exact ellFK_zero'⟩
  | succ i ih =>
    intro hi
    obtain ⟨C, hCT, hCc, hC1⟩ := ih (by omega)
    have hdis : Disjoint C (T \ C) := Finset.disjoint_sdiff
    have hcard : (T \ C).card + C.card = T.card := Finset.card_sdiff_add_card_eq_card hCT
    obtain ⟨P, hP, hP1⟩ := exists_add_nonspecial hdis hC1 (by omega) (by omega)
    rw [Finset.mem_sdiff] at hP
    exact ⟨insert P C, Finset.insert_subset hP.1 hCT, by rw [Finset.card_insert_of_notMem hP.2, hCc], hP1⟩

/-- **A nonspecial `g`-set avoiding `X`** inside any pool `T` with `2g + #X ≤ #T + 1`. -/
theorem exists_nonspecial_avoid (T X : Finset (Places.Rfin K F →ₐ[K] K))
    (hT : 2 * genusFK K F + X.card ≤ T.card + 1) :
    ∃ C ⊆ T, Disjoint C X ∧ C.card = genusFK K F ∧ IsNS K F C := by
  have h := Finset.le_card_sdiff X T
  obtain ⟨C, hC, hCc, hC1⟩ := exists_nonspecial_card (T \ X) (by omega) _ le_rfl
  refine ⟨C, fun x hx => (Finset.mem_sdiff.1 (hC hx)).1,
    Finset.disjoint_left.2 fun x hx hxX => (Finset.mem_sdiff.1 (hC hx)).2 hxX, hCc,
    const_of_ellFK_eq_one (Zdiv_nonneg C) hC1⟩

/-- **Four pairwise disjoint nonspecial `g`-sets** in any pool `T` with `5g ≤ #T + 1`. -/
theorem exists_four_nonspecial (T : Finset (Places.Rfin K F →ₐ[K] K)) (hT : 5 * genusFK K F ≤ T.card + 1) :
    ∃ a b E c : Finset (Places.Rfin K F →ₐ[K] K), a ⊆ T ∧ b ⊆ T ∧ E ⊆ T ∧ c ⊆ T ∧
      a.card = genusFK K F ∧ b.card = genusFK K F ∧ E.card = genusFK K F ∧ c.card = genusFK K F ∧
      Disjoint a b ∧ Disjoint a E ∧ Disjoint a c ∧ Disjoint b E ∧ Disjoint b c ∧ Disjoint E c ∧
      IsNS K F a ∧ IsNS K F b ∧ IsNS K F E ∧ IsNS K F c := by
  obtain ⟨a, ha, -, hac, haN⟩ := exists_nonspecial_avoid T ∅ (by rw [Finset.card_empty]; omega)
  obtain ⟨b, hb, hba, hbc, hbN⟩ := exists_nonspecial_avoid T a (by omega)
  obtain ⟨E, hE, hEab, hEc, hEN⟩ := exists_nonspecial_avoid T (a ∪ b)
    (by have := Finset.card_union_le a b; omega)
  obtain ⟨c, hc, hcabE, hcc, hcN⟩ := exists_nonspecial_avoid T (a ∪ b ∪ E)
    (by have := Finset.card_union_le (a ∪ b) E; have := Finset.card_union_le a b; omega)
  simp only [Finset.disjoint_union_right] at hEab hcabE
  exact ⟨a, b, E, c, ha, hb, hE, hc, hac, hbc, hEc, hcc, hba.symm, hEab.1.symm, hcabE.1.1.symm,
    hEab.2.symm, hcabE.1.2.symm, hcabE.2.symm, haN, hbN, hEN, hcN⟩

end GenNS

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_GenRole =====
section

/-!
# S4-JacLaw, file O9f (G5 GenRole): one role of the configuration, and the witness steps

* `exists_enum`: an injective tuple enumerating a finset.
* **`exists_role`**: from a section `s` with exact pole divisor `Hn` and full reduced zero set `Z`, and `A ⊆ Z`
  with `#A = d` and `Z \ A` nonspecial: a `NuData` with `Hn` that is good on `A` with `ν(A) = Z \ A`.
* `ne_u3`, **`ne_numA_m`**, **`ne_numA_r`**: a point `z` of `T` where the inner and outer units of `mOut` /
  `rOut` do not vanish (so `z` lifts to `D(numA _)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

theorem exists_enum {α : Type*} (A : Finset α) {d : ℕ} (hA : A.card = d) :
    ∃ t : Fin d → α, Function.Injective t ∧ ∀ φ, φ ∈ A ↔ ∃ i, t i = φ := by
  let e : Fin d ≃ A := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hA])).symm
  refine ⟨fun i => (e i).1, fun i j h => e.injective (Subtype.ext h), fun φ => ?_⟩
  constructor
  · intro hφ; exact ⟨e.symm ⟨φ, hφ⟩, by simp⟩
  · rintro ⟨i, rfl⟩; exact (e i).2

section GenRole

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **One role**: a `NuData` good on `A` with `ν(A) = Z \ A`. -/
theorem exists_role {d : ℕ} (hdg : genusFK K F ≤ d + 1) {Hn : Places.Divisor K F} (hHn : IsInf Hn)
    (hHn0 : 0 ≤ Hn) (hdeg : Places.Divisor.deg Hn = ((d + genusFK K F : ℕ) : ℤ))
    {s : Places.Rfin K F} (hs0 : s ≠ 0) (hs : ExactPoleH s Hn)
    {Z A : Finset (Places.Rfin K F →ₐ[K] K)} (hZ : ∀ φ, φ ∈ Z ↔ φ s = 0) (hZc : Z.card = d + genusFK K F)
    (hA : A ⊆ Z) (hAc : A.card = d) (hNS : IsNS K F (Z \ A)) :
    ∃ D : NuData K F d, D.Hn = Hn ∧
      ∀ y : SymRing K (Places.Rfin K F) d →ₐ[K] K, ptSet y = A → y D.good ≠ 0 ∧ D.nuF y = Z \ A := by
  obtain ⟨t, ht, hti⟩ := exists_enum A hAc
  have hdiv := div_of_card hs0 hHn hs hZ (by rw [hZc, hdeg])
  have hrank : ∀ w ∈ Linf K F Hn, (∀ i, t i w = 0) → ∃ c : K, w = c • s := fun w hw hw0 =>
    hrank_of_const hs0 hHn hdiv hA hNS hw fun φ hφ => by
      obtain ⟨i, rfl⟩ := (hti φ).1 hφ
      exact hw0 i
  obtain ⟨D, hDH, hgood, c, hc0, hsec⟩ :=
    exists_nuData hdg hHn hHn0 hdeg hs0 hs t ht hrank Z (fun φ hφ => (hZ φ).1 hφ) hZc
  refine ⟨D, hDH, fun y hy => ?_⟩
  have hpt : ptSet (symPt t) = A := by
    rw [ptSet_symPt]
    ext φ
    rw [Finset.mem_image, hti φ]
    simp only [Finset.mem_univ, true_and]
  have hyt : y = symPt t := eq_of_ptSet_eq (hy.trans hpt.symm) (by rw [hy, hAc])
  subst hyt
  refine ⟨hgood, ?_⟩
  have hz : zeroFin (k := K) (D.sec (symPt t)) = Z := by
    refine zeroFin_eq fun φ => ?_
    rw [NuData.sec_symPt, hsec, map_smul, smul_eq_mul, mul_eq_zero, or_iff_right hc0]
    exact hZ φ
  rw [NuData.nuF, hz, hpt]

section Wit

variable {T : Type u} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]
  {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3)) (D2 : NuData K F (genusFK K F + r2))
  (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))

theorem ne_u3 (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) (z : T →ₐ[K] K)
    {A3 : Finset (Places.Rfin K F →ₐ[K] K)}
    (hA : ptSet (z.comp φa) ∪ ptSet (z.comp φb) ∪ Finset.univ.image c0 = A3)
    (h3 : ∀ y : SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F + r3) →ₐ[K] K, ptSet y = A3 → y D3.good ≠ 0) :
    z (padMap (sumMap φa φb) c0 rfl D3.good) ≠ 0 := by
  have e : z (padMap (sumMap φa φb) c0 rfl D3.good) = (z.comp (padMap (sumMap φa φb) c0 rfl)) D3.good := rfl
  rw [e, comp_padMap]
  refine h3 _ ?_
  rw [ptSet_padPt, comp_sumMap, ptSet_sumPt, hA]

end Wit

end GenRole

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_GenCfg =====
section

/-!
# S4-JacLaw, file O9g (G5 GenCfg): the configuration

* `role_sub`, `role_card`, `role_sdiff`: finset bookkeeping for one role `X ∪ (Z \ U)` with `X ∪ W = U`.
* `RoleOn D A W`: `D` is good on every point with point set `A`, and `ν = W` there.
* `exists_role_of`: `exists_role` in the configuration shape.
* `exists_pool`: fibre sections over any finset of good points, and a pool of `≥ 5g - 1` good points.
* **`exists_cfg`**: a `LawData` with point tuples `ta`, `tb` and the six roles of the law at `(ta, tb)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Sets

variable {α : Type*} [DecidableEq α]

theorem role_sub {Z U X W : Finset α} (hU : U ⊆ Z) (hXW : X ∪ W = U) : X ∪ (Z \ U) ⊆ Z := by
  refine Finset.union_subset (fun φ hφ => hU ?_) Finset.sdiff_subset
  rw [← hXW]
  exact Finset.mem_union_left W hφ

theorem role_card {Z U X W : Finset α} (hXW : X ∪ W = U) :
    (X ∪ (Z \ U)).card = X.card + (Z \ U).card := by
  refine Finset.card_union_of_disjoint ?_
  rw [Finset.disjoint_left]
  intro φ hX hZ
  refine (Finset.mem_sdiff.1 hZ).2 ?_
  rw [← hXW]
  exact Finset.mem_union_left W hX

theorem role_sdiff {Z U X W : Finset α} (hU : U ⊆ Z) (hXW : X ∪ W = U) (hd : Disjoint X W) :
    Z \ (X ∪ (Z \ U)) = W := by
  ext φ
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or, not_and, not_not]
  constructor
  · rintro ⟨hZ, hX, hU'⟩
    have h := hU' hZ
    rw [← hXW, Finset.mem_union] at h
    exact h.resolve_left hX
  · intro hW
    have hWU : φ ∈ U := by
      rw [← hXW]
      exact Finset.mem_union_right X hW
    exact ⟨hU hWU, Finset.disjoint_right.1 hd hW, fun _ => hWU⟩

theorem image_enum {n : ℕ} (t : Fin n → α) (S : Finset α) (hS : ∀ φ, φ ∈ S ↔ ∃ i, t i = φ) :
    Finset.univ.image t = S := by
  ext φ
  rw [Finset.mem_image, hS φ]
  simp only [Finset.mem_univ, true_and]

end Sets

section GenCfg

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- `D` is good on every point with point set `A`, with `ν = W` there. -/
abbrev RoleOn {d : ℕ} (D : NuData K F d) (A W : Finset (Places.Rfin K F →ₐ[K] K)) : Prop :=
  ∀ y : SymRing K (Places.Rfin K F) d →ₐ[K] K, ptSet y = A → y D.good ≠ 0 ∧ D.nuF y = W

/-- **One role in configuration shape**: `A = X ∪ (Z \ U)`, `ν(A) = W` where `X ∪ W = U`. -/
theorem exists_role_of {d : ℕ} (hdg : genusFK K F ≤ d + 1) {Hn : Places.Divisor K F} (hHn : IsInf Hn)
    (hHn0 : 0 ≤ Hn) (hdeg : Places.Divisor.deg Hn = ((d + genusFK K F : ℕ) : ℤ))
    {s : Places.Rfin K F} (hs0 : s ≠ 0) (hs : ExactPoleH s Hn)
    {Z U X W : Finset (Places.Rfin K F →ₐ[K] K)} (hZ : ∀ φ, φ ∈ Z ↔ φ s = 0)
    (hZc : Z.card = d + genusFK K F) (hU : U ⊆ Z) (hXW : X ∪ W = U) (hd : Disjoint X W)
    (hXc : X.card + (Z \ U).card = d) (hNS : IsNS K F W) :
    ∃ D : NuData K F d, D.Hn = Hn ∧ RoleOn D (X ∪ (Z \ U)) W := by
  have hsd := role_sdiff hU hXW hd
  obtain ⟨D, hD, h⟩ := exists_role hdg hHn hHn0 hdeg hs0 hs hZ hZc (role_sub hU hXW)
    ((role_card hXW).trans hXc) (by rw [hsd]; exact hNS)
  exact ⟨D, hD, fun y hy => ⟨(h y hy).1, (h y hy).2.trans hsd⟩⟩

/-- **Fibre sections and a pool of good points.** -/
theorem exists_pool : ∃ a0 : K[X],
    (∀ U : Finset (Places.Rfin K F →ₐ[K] K), (∀ φ ∈ U, a0.eval (φ (xB K F)) ≠ 0) →
      ∃ s : Places.Rfin K F, ∃ Z : Finset (Places.Rfin K F →ₐ[K] K),
        s ≠ 0 ∧ ExactPoleH s (poleDiv (K := K) (incB K F s)) ∧
        (poleDiv (K := K) (incB K F s)).deg = (Z.card : ℤ) ∧ (∀ φ, φ ∈ Z ↔ φ s = 0) ∧ U ⊆ Z) ∧
    ∃ T : Finset (Places.Rfin K F →ₐ[K] K), 5 * genusFK K F ≤ T.card + 1 ∧
      ∀ φ ∈ T, a0.eval (φ (xB K F)) ≠ 0 := by
  obtain ⟨a0, ha0, hfib⟩ := exists_fib_data (K := K) (F := F)
  refine ⟨a0, fun U hU => ?_, ?_⟩
  · obtain ⟨s, Z, hs0, hs, hdeg, hZ, hZx, hZc⟩ := hfib (U.image fun φ => φ (xB K F)) (by
      intro c hc
      obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.1 hc
      exact hU φ hφ)
    exact ⟨s, Z, hs0, hs, by rw [hdeg, hZc], hZ, fun φ hφ => (hZx φ).2 (Finset.mem_image_of_mem _ hφ)⟩
  · obtain ⟨Λ, hΛ, hΛc⟩ :=
      (finite_setOfPred_isRoot ha0).infinite_compl.exists_subset_card_eq (5 * genusFK K F)
    have hΛa : ∀ c ∈ Λ, a0.eval c ≠ 0 := fun c hc h => hΛ (Finset.mem_coe.2 hc) h
    obtain ⟨s, Z, -, -, -, -, hZx, hZc⟩ := hfib Λ hΛa
    have hn : 0 < finrank K[X] (Places.Rfin K F) :=
      (Module.finrank_pos_iff_of_free (R := K[X]) (M := Places.Rfin K F)).2 inferInstance
    refine ⟨Z, ?_, fun φ hφ => hΛa _ ((hZx φ).1 hφ)⟩
    rw [hZc, hΛc]
    exact Nat.le_succ_of_le (Nat.le_mul_of_pos_right _ hn)

end GenCfg

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_GenWit =====
section

/-!
# S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data

* `wit_mu_gen`: the point set of `m(a,b)` at a point of the `mOut` target, from the two `m`-roles (any `T`).
* `pair_iL`, `pair_iR`; `wit_m`, `wit_mu`, `wit_r`, `wit_l`: the four steps at `T0 = S_g ⊗ S_g`.
* **`exists_lawData_wit`**: `∃ L : LawData K F, ∃ x, x (phiS L.μm L.ωr) ≠ 0 ∧ x (psiS L.μm L.ωl) ≠ 0`
  (the hypothesis `hw` of `LawData.toPre` / `LawData.chunk`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section GenWit

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

section Gen

variable {T : Type u} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]

end Gen

theorem pair_iL (y y' : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K) : (pair y y').comp (iL K F) = y :=
  pair_incL y y'

theorem pair_iR (y y' : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K) : (pair y y').comp (iR K F) = y' :=
  pair_incR y y'

variable (L : LawData K F) {a b E c : Finset (Places.Rfin K F →ₐ[K] K)}

end GenWit

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_GeoRed =====
section

/-!
# S4-JacLaw, file O10c: `Spec R` is geometrically reduced over `K`

For `K` algebraically closed and `R` a finitely generated `K`-domain, `R ⊗[K] L` is a domain for every field `L`
(`isDomain_tensor`), so every base change of `sR K R` to a field is reduced (`geometricallyReduced_sR`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open CategoryTheory Limits AlgebraicGeometry RamanujanPetersson.JacSym
open scoped TensorProduct

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {R : Type u} [CommRing R] [IsDomain R] [Algebra K R]
  [Algebra.FiniteType K R]

/-- `Spec R` is geometrically reduced over `K`. -/
instance geometricallyReduced_sR : GeometricallyReduced (sR K R) := by
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing]
  intro L _ _ Y fst snd h
  have : IsDomain (R ⊗[K] L) := isDomain_tensor (k := K) (B := R) (A := L)
  exact ObjectProperty.prop_of_iso _ (h.isoPullback ≪≫ pullbackSpecIso K R L).symm inferInstance

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

-- ===== S4.Def_RP_JacChunkA_Dom =====
section

/-!
# Group chunk A3 (unit S4-JacChunkA): maximal domains, iso domains and the cocycle

For `σ : Bir k X`, `rep σ` is the representative of `σ` on its maximal domain of definition.
* `rep_of_rep` (KL): any representative of `σ` defined at `x` shows `x ∈ dom σ`, with the same value.
* `rep_comp_apply`: KL for a composite `τ ∘ σ`.
* `W σ`: the open where `σ` is defined and `σ⁻¹` is defined at the image; `tW σ τ h : W σ ⟶ W τ`
  (`τ = σ⁻¹`), `x ↦ σ x`.
* `mem_W_cocycle` / `apply_cocycle`: for `ρ = τσ` and `x ∈ W σ ∩ W ρ`: `σ x ∈ W τ` and `τ (σ x) = ρ x`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]

omit [IsReduced X] in
lemma hom_congr {Y : Scheme.{u}} (f : X.PartialMap Y) {x y : X} (h : x = y) (hx : x ∈ f.domain)
    (hy : y ∈ f.domain) : f.hom ⟨x, hx⟩ = f.hom ⟨y, hy⟩ := by
  subst h; rfl

omit [IsReduced X] in
lemma homOfLE_comp_apply {Y : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (f : V.toScheme ⟶ Y) (x : U) :
    (X.homOfLE h ≫ f) x = f ⟨x.1, h x.2⟩ := by
  change f (X.homOfLE h x) = _
  exact congrArg f (Subtype.ext (val_eq_of_comp_ι (X.homOfLE_ι h) x))

variable [X.IsSeparated] [IrreducibleSpace X]

/-- The representative of `σ` on its maximal domain of definition. -/
noncomputable def rep (σ : Bir k X) : X.PartialMap X := σ.1.1.toPartialMap

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
lemma rep_toRationalMap (σ : Bir k X) : (rep σ).toRationalMap = σ.1.1 :=
  Scheme.RationalMap.toRationalMap_toPartialMap _

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
instance rep_isDominant (σ : Bir k X) : IsDominant (rep σ).hom := by
  have := σ.1.2.1
  rw [← rep_toRationalMap σ, Scheme.PartialMap.isDominant_toRationalMap_iff] at this
  exact this

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
instance rep_isOver (σ : Bir k X) : (rep σ).IsOver (Spec (.of k)) :=
  haveI := σ.1.2.2; inferInstanceAs (σ.1.1.toPartialMap.IsOver (Spec (.of k)))

/-- KL: a representative of `σ` defined at `x` shows that `rep σ` is defined at `x`, with the same value. -/
lemma rep_of_rep (f : X.PartialMap X) [f.IsOver (Spec (.of k))] (σ : Bir k X)
    (e : f.toRationalMap = σ.1.1) (x : X) (hx : x ∈ f.domain) :
    ∃ h : x ∈ (rep σ).domain, (rep σ).hom ⟨x, h⟩ = f.hom ⟨x, hx⟩ := by
  have h : x ∈ (rep σ).domain := by
    have := f.le_domain_toRationalMap hx
    rw [e] at this
    exact this
  exact ⟨h, apply_eq_of_toRationalMap_eq (k := k) ((rep_toRationalMap σ).trans e.symm) x h hx⟩

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
lemma comp_rep_toRationalMap (σ τ : Bir k X) :
    ((rep σ).comp (rep τ)).toRationalMap = (τ * σ).1.1 := by
  rw [← Scheme.RationalMap.toRationalMap_comp]
  have key : ∀ (f f' g g' : X ⤏ X) [f.IsDominant] [f'.IsDominant], f = f' → g = g' →
      f.comp g = f'.comp g' := by
    intro f f' g g' _ _ h h'; subst h h'; rfl
  haveI := σ.1.2.1
  exact key _ σ.1.1 _ τ.1.1 (rep_toRationalMap σ) (rep_toRationalMap τ)

/-- KL for a composite: if `σ` is defined at `x` and `τ` at `σ x`, then `ρ = τ σ` is defined at `x`. -/
lemma rep_comp_apply (σ τ ρ : Bir k X) (e : ρ = τ * σ) (x : X) (hx : x ∈ (rep σ).domain)
    (hx' : (rep σ).hom ⟨x, hx⟩ ∈ (rep τ).domain) :
    ∃ h : x ∈ (rep ρ).domain, (rep ρ).hom ⟨x, h⟩ = (rep τ).hom ⟨(rep σ).hom ⟨x, hx⟩, hx'⟩ := by
  haveI := comp_isOver (k := k) (rep σ) (rep τ)
  have h1 : x ∈ ((rep σ).comp (rep τ)).domain := (mem_comp_domain _ _).2 ⟨hx, hx'⟩
  obtain ⟨h, hv⟩ := rep_of_rep ((rep σ).comp (rep τ)) ρ (by rw [comp_rep_toRationalMap, e]) x h1
  exact ⟨h, hv.trans (comp_hom_apply _ _ ⟨x, h1⟩ hx hx')⟩

lemma rep_eq_one (ρ : Bir k X) (e : ρ = 1) (x : X) :
    ∃ h : x ∈ (rep ρ).domain, (rep ρ).hom ⟨x, h⟩ = x := by
  obtain ⟨h, hv⟩ := rep_of_rep (Scheme.PartialMap.id X) ρ (by rw [e]; rfl) x trivial
  exact ⟨h, hv.trans (id_hom_apply x _)⟩

/-- The open where `σ` is defined and `σ⁻¹` is defined at the image. -/
noncomputable def W (σ : Bir k X) : X.Opens := ((rep σ).comp (rep σ⁻¹)).domain

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
lemma mem_W {σ : Bir k X} {x : X} :
    x ∈ W σ ↔ ∃ hx : x ∈ (rep σ).domain, (rep σ).hom ⟨x, hx⟩ ∈ (rep σ⁻¹).domain :=
  mem_comp_domain _ _

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
lemma W_le (σ : Bir k X) : W σ ≤ (rep σ).domain := fun _ hx => (mem_W.1 hx).1

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
lemma dense_W (σ : Bir k X) : Dense ((W σ : X.Opens) : Set X) := ((rep σ).comp (rep σ⁻¹)).dense_domain

lemma inv_apply_apply (σ : Bir k X) (x : X) (hx : x ∈ (rep σ).domain)
    (hx' : (rep σ).hom ⟨x, hx⟩ ∈ (rep σ⁻¹).domain) : (rep σ⁻¹).hom ⟨(rep σ).hom ⟨x, hx⟩, hx'⟩ = x := by
  obtain ⟨h, hv⟩ := rep_comp_apply σ σ⁻¹ 1 (inv_mul_cancel σ).symm x hx hx'
  obtain ⟨h', hv'⟩ := rep_eq_one (1 : Bir k X) rfl x
  exact hv.symm.trans hv'

lemma mem_W_one (x : X) : x ∈ W (1 : Bir k X) := by
  obtain ⟨h, hv⟩ := rep_eq_one (1 : Bir k X) rfl x
  obtain ⟨h', -⟩ := rep_eq_one ((1 : Bir k X)⁻¹) inv_one x
  exact mem_W.2 ⟨h, by rw [hv]; exact h'⟩

/-- Cocycle, domain part: for `ρ = τ σ` and `x ∈ W σ ∩ W ρ`, `σ x ∈ W τ`. -/
lemma mem_W_cocycle (σ τ ρ : Bir k X) (e : ρ = τ * σ) (x : X) (hσ : x ∈ W σ) (hρ : x ∈ W ρ)
    (hx : x ∈ (rep σ).domain) : (rep σ).hom ⟨x, hx⟩ ∈ W τ := by
  obtain ⟨hx0, hy1⟩ := mem_W.1 hσ
  obtain ⟨hxρ, hz1⟩ := mem_W.1 hρ
  have hv1 := inv_apply_apply σ x hx hy1
  have hv2 := inv_apply_apply ρ x hxρ hz1
  obtain ⟨hyτ, hvτ⟩ := rep_comp_apply σ⁻¹ ρ τ (by rw [e, mul_inv_cancel_right]) _ hy1 (by rw [hv1]; exact hxρ)
  obtain ⟨hzτ, -⟩ := rep_comp_apply ρ⁻¹ σ τ⁻¹ (by rw [e, mul_inv_rev, mul_inv_cancel_left]) _ hz1
    (by rw [hv2]; exact hx)
  refine mem_W.2 ⟨hyτ, ?_⟩
  rw [hvτ, hom_congr (rep ρ) hv1 _ hxρ]
  exact hzτ

/-- Cocycle, value part: for `ρ = τ σ` and `x ∈ W σ ∩ W ρ`, `τ (σ x) = ρ x`. -/
lemma apply_cocycle (σ τ ρ : Bir k X) (e : ρ = τ * σ) (x : X) (hσ : x ∈ W σ) (hx : x ∈ (rep σ).domain)
    (hy : (rep σ).hom ⟨x, hx⟩ ∈ (rep τ).domain) (hxρ : x ∈ (rep ρ).domain) :
    (rep τ).hom ⟨(rep σ).hom ⟨x, hx⟩, hy⟩ = (rep ρ).hom ⟨x, hxρ⟩ := by
  obtain ⟨hx0, hy1⟩ := mem_W.1 hσ
  have hv1 := inv_apply_apply σ x hx hy1
  obtain ⟨hyτ, hvτ⟩ := rep_comp_apply σ⁻¹ ρ τ (by rw [e, mul_inv_cancel_right]) _ hy1 (by rw [hv1]; exact hxρ)
  exact hvτ.trans (hom_congr (rep ρ) hv1 _ hxρ)

/-- The transition map `W σ ⟶ W τ`, `x ↦ σ x`, for `τ = σ⁻¹`. -/
noncomputable def tW (σ τ : Bir k X) (h : τ = σ⁻¹) : (W σ).toScheme ⟶ (W τ).toScheme :=
  liftO (W τ) (X.homOfLE (W_le σ) ≫ (rep σ).hom) (fun x => by
    refine (congrArg (· ∈ W τ) (homOfLE_comp_apply (W_le σ) (rep σ).hom x)).mpr ?_
    subst h
    exact mem_W_cocycle σ σ⁻¹ 1 (inv_mul_cancel σ).symm x.1 x.2 (mem_W_one x.1) _)

lemma tW_apply (σ τ : Bir k X) (h : τ = σ⁻¹) (x : W σ) :
    (tW σ τ h x).1 = (rep σ).hom ⟨x.1, W_le σ x.2⟩ := by
  unfold tW
  refine (val_eq_of_comp_ι (ψ := X.homOfLE (W_le σ) ≫ (rep σ).hom) (liftO_ι _ _ _) x).trans ?_
  exact homOfLE_comp_apply (W_le σ) (rep σ).hom x

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkA_Glue =====
section

/-!
# Group chunk A4 (unit S4-JacChunkA): gluing copies of `X` from pointwise data

`PtGlue k X`: opens `V i j` of `X` (`V i i = ⊤`) and `k`-morphisms `t i j : V i j ⟶ V j i` with the
gluing identities checked at points. `PtGlue.toGlueData` turns it into a `Scheme.GlueData` whose charts are
all `X` (morphism identities follow from `ext_of_apply_eq`, since `X` is reduced, lft and separated over `k`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]

omit [IsReduced X] in
/-- Morphisms into `X` from a reduced lft `k`-scheme are determined by their values at closed points. -/
lemma ext_X {T : Scheme.{u}} [IsReduced T] (sT : T ⟶ Spec (.of k)) [LocallyOfFiniteType sT]
    (f g : T ⟶ X) (hf : f ≫ X ↘ Spec (.of k) = sT) (hg : g ≫ X ↘ Spec (.of k) = sT)
    (h : ∀ x, IsClosed {x} → f x = g x) : f = g := by
  have : LocallyOfFiniteType (f ≫ X ↘ Spec (.of k)) := by rw [hf]; infer_instance
  exact ext_of_apply_eq (X ↘ Spec (.of k)) Set.univ isOpen_univ.isLocallyClosed dense_univ
    (fun x _ hx => h x hx) (hf.trans hg.symm)

variable (k X) in
/-- Pointwise gluing data for copies of `X`. -/
structure PtGlue where
  J : Type u
  V : J → J → X.Opens
  V_self : ∀ i, V i i = ⊤
  t : ∀ i j, (V i j).toScheme ⟶ (V j i).toScheme
  t_over : ∀ i j, t i j ≫ (V j i).ι ≫ X ↘ Spec (.of k) = (V i j).ι ≫ X ↘ Spec (.of k)
  t_self : ∀ i (x : V i i), (t i i x).1 = x.1
  t_mem : ∀ i j l (x : X) (hij : x ∈ V i j), x ∈ V i l → (t i j ⟨x, hij⟩).1 ∈ V j l
  t_cocycle : ∀ i j l (x : X) (hij : x ∈ V i j) (hil : x ∈ V i l) (h : (t i j ⟨x, hij⟩).1 ∈ V j l),
    (t j l ⟨(t i j ⟨x, hij⟩).1, h⟩).1 = (t i l ⟨x, hil⟩).1

namespace PtGlue

variable (D : PtGlue k X)

include D in
omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
lemma P_val (i j l : D.J) (p : (pullback (D.V i j).ι (D.V i l).ι : Scheme.{u})) :
    (pullback.fst (D.V i j).ι (D.V i l).ι p).1 = (pullback.snd (D.V i j).ι (D.V i l).ι p).1 :=
  congrArg (fun φ => φ p) (pullback.condition (f := (D.V i j).ι) (g := (D.V i l).ι))

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
lemma t_cocycle_val (i j l : D.J) (a : D.V i j) (b : D.V j l) (hil : a.1 ∈ D.V i l)
    (hb : b.1 = (D.t i j a).1) : (D.t j l b).1 = (D.t i l ⟨a.1, hil⟩).1 := by
  have hm : (D.t i j a).1 ∈ D.V j l := by rw [← hb]; exact b.2
  have e : b = ⟨(D.t i j a).1, hm⟩ := Subtype.ext hb
  rw [e]
  exact D.t_cocycle i j l a.1 a.2 hil hm

/-- The triple-overlap transition map. -/
noncomputable def t' (i j l : D.J) :
    pullback (D.V i j).ι (D.V i l).ι ⟶ pullback (D.V j l).ι (D.V j i).ι :=
  pullback.lift
    (liftO (D.V j l) (pullback.fst _ _ ≫ D.t i j ≫ (D.V j i).ι) (fun p => by
      have hil : (pullback.fst (D.V i j).ι (D.V i l).ι p).1 ∈ D.V i l := by
        rw [D.P_val]; exact (pullback.snd (D.V i j).ι (D.V i l).ι p).2
      exact D.t_mem i j l _ (pullback.fst (D.V i j).ι (D.V i l).ι p).2 hil))
    (pullback.fst _ _ ≫ D.t i j)
    ((liftO_ι _ _ _).trans (Category.assoc _ _ _).symm)

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
@[reassoc]
lemma t'_fst (i j l : D.J) :
    D.t' i j l ≫ pullback.fst _ _ ≫ (D.V j l).ι = pullback.fst _ _ ≫ D.t i j ≫ (D.V j i).ι := by
  unfold t'
  rw [pullback.lift_fst_assoc]
  exact liftO_ι _ _ _

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
lemma t'_snd (i j l : D.J) : D.t' i j l ≫ pullback.snd _ _ = pullback.fst _ _ ≫ D.t i j :=
  pullback.lift_snd _ _ _

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
lemma t'_fst_val (i j l : D.J) (p : (pullback (D.V i j).ι (D.V i l).ι : Scheme.{u})) :
    (pullback.fst (D.V j l).ι (D.V j i).ι (D.t' i j l p)).1 = (D.t i j (pullback.fst (D.V i j).ι (D.V i l).ι p)).1 :=
  congrArg (fun φ => φ p) (D.t'_fst i j l)

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
@[reassoc]
lemma t'_over (i j l : D.J) :
    D.t' i j l ≫ pullback.fst _ _ ≫ (D.V j l).ι ≫ X ↘ Spec (.of k) =
      pullback.fst _ _ ≫ (D.V i j).ι ≫ X ↘ Spec (.of k) := by
  rw [D.t'_fst_assoc, D.t_over]

@[reassoc]
lemma cocycle_fst (i j l : D.J) :
    D.t' i j l ≫ D.t' j l i ≫ D.t' l i j ≫ pullback.fst _ _ = pullback.fst _ _ := by
  haveI := isReduced_of_isOpenImmersion (pullback.fst (D.V i j).ι (D.V i l).ι ≫ (D.V i j).ι)
  refine (cancel_mono (D.V i j).ι).1 ?_
  refine ext_X (pullback.fst _ _ ≫ (D.V i j).ι ≫ X ↘ Spec (.of k)) _ _ ?_ ?_ ?_
  · simp only [Category.assoc, D.t'_over]
  · simp only [Category.assoc]
  · intro p _
    change (pullback.fst (D.V i j).ι (D.V i l).ι (D.t' l i j (D.t' j l i (D.t' i j l p)))).1 =
      (pullback.fst (D.V i j).ι (D.V i l).ι p).1
    have hil : (pullback.fst (D.V i j).ι (D.V i l).ι p).1 ∈ D.V i l := by
      rw [D.P_val]; exact (pullback.snd (D.V i j).ι (D.V i l).ι p).2
    have hii : (pullback.fst (D.V i j).ι (D.V i l).ι p).1 ∈ D.V i i := by
      rw [D.V_self i]; trivial
    have e1 := D.t'_fst_val i j l p
    have e2 := D.t'_fst_val j l i (D.t' i j l p)
    have e3 := D.t'_fst_val l i j (D.t' j l i (D.t' i j l p))
    have c1 := D.t_cocycle_val i j l _ _ hil e1
    have c2 := D.t_cocycle_val i l i ⟨_, hil⟩ _ hii (e2.trans c1)
    exact e3.trans (c2.trans (D.t_self i _))

/-- The glue data. -/
noncomputable def toGlueData : Scheme.GlueData.{u} where
  J := D.J
  U _ := X
  V p := (D.V p.1 p.2).toScheme
  f i j := (D.V i j).ι
  f_id i := by
    change IsIso (D.V i i).ι
    rw [D.V_self i]
    exact ⟨X.topIso.inv, Scheme.ι_toIso_inv X, Scheme.toIso_inv_ι X⟩
  t := D.t
  t_id i := by
    change D.t i i = 𝟙 _
    refine (cancel_mono (D.V i i).ι).1 ?_
    refine ext_X ((D.V i i).ι ≫ X ↘ Spec (.of k)) _ _ ?_ ?_ ?_
    · rw [Category.assoc, D.t_over]
    · rw [Category.id_comp]
    · intro x _
      exact D.t_self i x
  t' := D.t'
  t_fac i j l := D.t'_snd i j l
  cocycle i j l := by
    change D.t' i j l ≫ D.t' j l i ≫ D.t' l i j = 𝟙 _
    refine pullback.hom_ext ?_ ?_
    · rw [Category.id_comp, Category.assoc, Category.assoc]
      exact D.cocycle_fst i j l
    · refine (cancel_mono (D.V i l).ι).1 ?_
      simp only [Category.assoc, Category.id_comp]
      rw [← pullback.condition, D.cocycle_fst_assoc]
  f_open i j := inferInstance

end PtGlue

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkA_G =====
section

/-!
# Group chunk A5 (unit S4-JacChunkA): the glued scheme `G`

For a subgroup `H` of `Bir k X`: charts `X` indexed by `H`, overlaps `V σ τ := W (τ⁻¹ σ)` and transitions
`x ↦ (τ⁻¹ σ) x` form pointwise gluing data `gD H`. `G H` is the glued scheme, `ι H σ : X ⟶ G H` the charts
(open immersions), `sG H` the structure morphism to `Spec k` (lft), `G H` is reduced and irreducible, and
`L H h` (chart `σ ↦ h σ`) is the left action of `H`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

lemma tW_ι (σ τ : Bir k X) (h : τ = σ⁻¹) :
    tW σ τ h ≫ (W τ).ι = X.homOfLE (W_le σ) ≫ (rep σ).hom := liftO_ι _ _ _

lemma tW_over (σ τ : Bir k X) (h : τ = σ⁻¹) :
    tW σ τ h ≫ (W τ).ι ≫ X ↘ Spec (.of k) = (W σ).ι ≫ X ↘ Spec (.of k) := by
  rw [← Category.assoc, tW_ι, Category.assoc]
  refine (congrArg (X.homOfLE (W_le σ) ≫ ·)
    (HomIsOver.comp_over (f := (rep σ).hom) (S := Spec (.of k)))).trans ?_
  change X.homOfLE (W_le σ) ≫ (rep σ).domain.ι ≫ X ↘ Spec (.of k) = _
  rw [← Category.assoc, Scheme.homOfLE_ι]

lemma W_one_eq : W (1 : Bir k X) = ⊤ := top_unique fun x _ => mem_W_one x

lemma inv_mul_eq_inv (a b : Bir k X) : a⁻¹ * b = (b⁻¹ * a)⁻¹ := by rw [mul_inv_rev, inv_inv]

/-- The transition `W (b⁻¹ a) ⟶ W (a⁻¹ b)`, `x ↦ (b⁻¹ a) x`. -/
noncomputable def tH (a b : Bir k X) : (W (b⁻¹ * a)).toScheme ⟶ (W (a⁻¹ * b)).toScheme :=
  tW _ _ (inv_mul_eq_inv a b)

lemma tH_apply (a b : Bir k X) (x : W (b⁻¹ * a)) :
    (tH a b x).1 = (rep (b⁻¹ * a)).hom ⟨x.1, W_le _ x.2⟩ := tW_apply _ _ _ x

lemma tH_self (a : Bir k X) (x : W (a⁻¹ * a)) : (tH a a x).1 = x.1 := by
  rw [tH_apply]
  obtain ⟨_, hv⟩ := rep_eq_one (a⁻¹ * a) (inv_mul_cancel a) x.1
  exact hv

lemma tH_mem (a b c : Bir k X) (x : X) (h1 : x ∈ W (b⁻¹ * a)) (h2 : x ∈ W (c⁻¹ * a)) :
    (tH a b ⟨x, h1⟩).1 ∈ W (c⁻¹ * b) := by
  rw [tH_apply]
  exact mem_W_cocycle (b⁻¹ * a) (c⁻¹ * b) (c⁻¹ * a) (by rw [mul_assoc, mul_inv_cancel_left]) x h1 h2 _

lemma tH_cocycle (a b c : Bir k X) (x : X) (h1 : x ∈ W (b⁻¹ * a)) (h2 : x ∈ W (c⁻¹ * a))
    (h : (tH a b ⟨x, h1⟩).1 ∈ W (c⁻¹ * b)) :
    (tH b c ⟨(tH a b ⟨x, h1⟩).1, h⟩).1 = (tH a c ⟨x, h2⟩).1 := by
  have hy : (rep (b⁻¹ * a)).hom ⟨x, W_le _ h1⟩ ∈ (rep (c⁻¹ * b)).domain :=
    (congrArg (· ∈ (rep (c⁻¹ * b)).domain) (tH_apply a b ⟨x, h1⟩)).mp (W_le _ h)
  calc (tH b c ⟨(tH a b ⟨x, h1⟩).1, h⟩).1
      = (rep (c⁻¹ * b)).hom ⟨(tH a b ⟨x, h1⟩).1, W_le _ h⟩ := tH_apply b c _
    _ = (rep (c⁻¹ * b)).hom ⟨(rep (b⁻¹ * a)).hom ⟨x, W_le _ h1⟩, hy⟩ :=
        hom_congr _ (tH_apply a b _) _ _
    _ = (rep (c⁻¹ * a)).hom ⟨x, W_le _ h2⟩ :=
        apply_cocycle (b⁻¹ * a) (c⁻¹ * b) (c⁻¹ * a) (by rw [mul_assoc, mul_inv_cancel_left]) x h1
          (W_le _ h1) hy (W_le _ h2)
    _ = (tH a c ⟨x, h2⟩).1 := (tH_apply a c ⟨x, h2⟩).symm

variable (H : Subgroup (Bir k X))

/-- Overlaps: `V σ τ := W (τ⁻¹ σ)`. -/
noncomputable def VH (σ τ : H) : X.Opens := W ((τ : Bir k X)⁻¹ * (σ : Bir k X))

/-- Transitions `V σ τ ⟶ V τ σ`. -/
noncomputable def tHH (σ τ : H) : (VH H σ τ).toScheme ⟶ (VH H τ σ).toScheme := tH (σ : Bir k X) τ

lemma VH_self (σ : H) : VH H σ σ = ⊤ := (congrArg W (inv_mul_cancel (σ : Bir k X))).trans W_one_eq

lemma tHH_over (σ τ : H) :
    tHH H σ τ ≫ (VH H τ σ).ι ≫ X ↘ Spec (.of k) = (VH H σ τ).ι ≫ X ↘ Spec (.of k) :=
  tW_over ((τ : Bir k X)⁻¹ * (σ : Bir k X)) ((σ : Bir k X)⁻¹ * (τ : Bir k X)) (inv_mul_eq_inv _ _)

lemma tHH_self (σ : H) (x : VH H σ σ) : (tHH H σ σ x).1 = x.1 := tH_self (σ : Bir k X) x

lemma tHH_mem (σ τ ρ : H) (x : X) (h1 : x ∈ VH H σ τ) (h2 : x ∈ VH H σ ρ) :
    (tHH H σ τ ⟨x, h1⟩).1 ∈ VH H τ ρ := tH_mem (σ : Bir k X) τ ρ x h1 h2

lemma tHH_cocycle (σ τ ρ : H) (x : X) (h1 : x ∈ VH H σ τ) (h2 : x ∈ VH H σ ρ)
    (h : (tHH H σ τ ⟨x, h1⟩).1 ∈ VH H τ ρ) :
    (tHH H τ ρ ⟨(tHH H σ τ ⟨x, h1⟩).1, h⟩).1 = (tHH H σ ρ ⟨x, h2⟩).1 :=
  tH_cocycle (σ : Bir k X) τ ρ x h1 h2 h

/-- The pointwise gluing data of the charts indexed by `H`. -/
noncomputable def gD : PtGlue k X where
  J := H
  V := VH H
  V_self := VH_self H
  t := tHH H
  t_over := tHH_over H
  t_self := tHH_self H
  t_mem := tHH_mem H
  t_cocycle := tHH_cocycle H

/-- The glued scheme. -/
noncomputable abbrev G : Scheme.{u} := (gD H).toGlueData.glued

/-- The chart of index `σ`. -/
noncomputable abbrev ι (σ : H) : X ⟶ G H := (gD H).toGlueData.ι σ

lemma ι_glue (σ τ : H) : tHH H σ τ ≫ (VH H τ σ).ι ≫ ι H τ = (VH H σ τ).ι ≫ ι H σ :=
  (gD H).toGlueData.glue_condition σ τ

/-- The structure morphism of `G H`. -/
noncomputable def sG : G H ⟶ Spec (.of k) :=
  Multicoequalizer.desc _ _ (fun _ => X ↘ Spec (.of k)) (by
    rintro ⟨σ, τ⟩
    exact ((Category.assoc _ _ _).trans (tHH_over H σ τ)).symm)

lemma ι_sG (σ : H) : ι H σ ≫ sG H = X ↘ Spec (.of k) := Multicoequalizer.π_desc _ _ _ _ _

noncomputable instance : (G H).Over (Spec (.of k)) where
  hom := sG H

instance (σ : H) : (ι H σ).IsOver (Spec (.of k)) := ⟨ι_sG H σ⟩

instance (σ : H) : IsOpenImmersion (ι H σ) := Scheme.GlueData.ι_isOpenImmersion (gD H).toGlueData σ

instance : LocallyOfFiniteType (G H ↘ Spec (.of k)) := by
  have hP : ∀ σ : H, LocallyOfFiniteType (ι H σ ≫ sG H) := fun σ => by
    rw [ι_sG]
    all_goals infer_instance
  first
  | exact IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) (gD H).toGlueData.openCover hP
  | exact (set_option backward.isDefEq.respectTransparency.types false in
      IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) (gD H).toGlueData.openCover hP)

instance : IsReduced (G H) := by
  have : ∀ σ, IsReduced ((gD H).toGlueData.openCover.X σ) := fun _ => (inferInstance : IsReduced X)
  exact IsReduced.of_openCover _ (gD H).toGlueData.openCover

lemma ι_meet (σ τ : H) : ∃ x y, ι H σ x = ι H τ y := by
  obtain ⟨x, hx⟩ := (dense_W ((τ : Bir k X)⁻¹ * (σ : Bir k X))).nonempty
  refine ⟨x, (tHH H σ τ ⟨x, hx⟩).1, ?_⟩
  exact (congrArg (fun φ => φ ⟨x, hx⟩) (ι_glue H σ τ)).symm

instance : IrreducibleSpace (G H) := by
  rw [irreducibleSpace_def]
  have hirr : ∀ σ : H, IsIrreducible (Set.range (ι H σ)) := fun σ => by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ X).image _ (ι H σ).continuous.continuousOn
  have hcl : closure (Set.range (ι H 1)) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨σ, x, rfl⟩ := (gD H).toGlueData.ι_jointly_surjective g
    obtain ⟨y, z, hyz⟩ := ι_meet H σ 1
    have hs := subset_closure_inter_of_isPreirreducible_of_isOpen (hirr σ).isPreirreducible
      (ι H 1).isOpenEmbedding.isOpen_range ⟨_, ⟨y, rfl⟩, ⟨z, hyz.symm⟩⟩
    exact closure_mono Set.inter_subset_right (hs ⟨x, rfl⟩)
  have h1 := isIrreducible_iff_closure.2 (hirr 1)
  rw [hcl] at h1
  exact h1

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkA_RC =====
section

/-!
# Group chunk A6, part 1 (unit S4-JacChunkA): re-charting

`Takes σ x y` says that the maximal representative of `σ : Bir k X` is defined at `x` with value `y`.
For a strict chunk `C`, `σ ∈ C.H` and closed points `x y`:
* `RC_fwd`: `Takes σ x y → σ * λ_x = λ_y`;
* `RC_bwd`: `σ * λ_x = λ_y → Takes σ x y`;
* `RC_W`: `Takes σ x y → x ∈ W σ`, and `lamB_inj`: `λ_x = λ_y → x = y`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

/-- Two nonempty opens of an irreducible Jacobson space share a closed point. -/
lemma exists_closed_inter {T : Type*} [TopologicalSpace T] [JacobsonSpace T] [PreirreducibleSpace T]
    (U V : TopologicalSpace.Opens T) (hU : (U : Set T).Nonempty) (hV : (V : Set T).Nonempty) :
    ∃ z, z ∈ U ∧ z ∈ V ∧ IsClosed ({z} : Set T) := by
  obtain ⟨z, ⟨hzU, hzV⟩, hz⟩ := nonempty_inter_closedPoints
    (nonempty_preirreducible_inter U.2 V.2 hU hV) (U.2.inter V.2).isLocallyClosed
  exact ⟨z, hzU, hzV, hz⟩

lemma pi_mem_target {X : Scheme.{u}} (f : X.PartialIso X) (u : X) (hu : u ∈ f.toPartialMap.domain) :
    f.toPartialMap.hom ⟨u, hu⟩ ∈ f.symm.toPartialMap.domain :=
  (congrArg (· ∈ f.target) (val_eq_of_comp_ι (φ := f.iso.hom) (ψ := f.toPartialMap.hom) rfl ⟨u, hu⟩)).mp
    (f.iso.hom ⟨u, hu⟩).2

lemma pi_symm_apply {X : Scheme.{u}} (f : X.PartialIso X) (u : X) (hu : u ∈ f.toPartialMap.domain)
    (h : f.toPartialMap.hom ⟨u, hu⟩ ∈ f.symm.toPartialMap.domain) :
    f.symm.toPartialMap.hom ⟨f.toPartialMap.hom ⟨u, hu⟩, h⟩ = u := by
  have h' := congrArg (fun φ => (φ ⟨u, hu⟩ : f.source.toScheme)) f.iso.hom_inv_id
  exact congrArg Subtype.val h'

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

/-- The maximal representative of `σ` is defined at `x`, with value `y`. -/
def Takes (σ : Bir k X) (x y : X) : Prop := ∃ h : x ∈ (rep σ).domain, (rep σ).hom ⟨x, h⟩ = y

lemma Takes.comp {σ τ ρ : Bir k X} {x v w : X} (h1 : Takes σ x v) (h2 : Takes τ v w) (e : ρ = τ * σ) :
    Takes ρ x w := by
  obtain ⟨hx, rfl⟩ := h1
  obtain ⟨hv, rfl⟩ := h2
  exact rep_comp_apply σ τ ρ e x hx hv

lemma Takes.unique {σ : Bir k X} {x w w' : X} (h1 : Takes σ x w) (h2 : Takes σ x w') : w = w' := by
  obtain ⟨h, rfl⟩ := h1
  obtain ⟨h', rfl⟩ := h2
  rfl

lemma Takes.of_eq {σ σ' : Bir k X} {x w : X} (e : σ = σ') (h : Takes σ x w) : Takes σ' x w := by
  subst e; exact h

lemma Takes.val_eq {σ : Bir k X} {x w w' : X} (h : Takes σ x w) (e : w = w') : Takes σ x w' := by
  subst e; exact h

lemma Takes.src_eq {σ : Bir k X} {v v' w : X} (h : Takes σ v w) (e : v = v') : Takes σ v' w := by
  subst e; exact h

lemma takes_self (σ : Bir k X) (x : X) (h : x ∈ (rep σ).domain) : Takes σ x ((rep σ).hom ⟨x, h⟩) := ⟨h, rfl⟩

lemma secL_eq_secR (x : X) (hx : IsClosed {x}) (z : X) (hz : IsClosed {z}) :
    secL (sX := X ↘ Spec (.of k)) x hx z = secR z hz x :=
  closedPoint_pullback_ext (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) _ _ (secL_isClosed x hx z hz)
    (secR_isClosed z hz x hx) ((secL_apply_fst x hx z).trans (secR_apply_fst z hz x).symm)
    ((secL_apply_snd x hx z).trans (secR_apply_snd z hz x).symm)

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

lemma lam_mem_rho (x : X) (hx : IsClosed {x}) (z : X) (hz : IsClosed {z})
    (h : z ∈ (C.lam x hx).toPartialMap.domain) : x ∈ (C.rho z hz).toPartialMap.domain := by
  have h' : secL x hx z ∈ C.Ω := (Scheme.Hom.mem_preimage _).1 h
  change x ∈ secR z hz ⁻¹ᵁ C.Ω
  rw [Scheme.Hom.mem_preimage, ← secL_eq_secR x hx z hz]
  exact h'

lemma lam_eq_rho (x : X) (hx : IsClosed {x}) (z : X) (hz : IsClosed {z})
    (h : z ∈ (C.lam x hx).toPartialMap.domain) :
    (C.rho z hz).toPartialMap.hom ⟨x, C.lam_mem_rho x hx z hz h⟩ = (C.lam x hx).toPartialMap.hom ⟨z, h⟩ :=
  (C.rho_apply z hz x _).trans (Eq.trans (congrArg C.m (Subtype.ext (secL_eq_secR x hx z hz).symm))
    (C.lam_apply x hx z h).symm)

lemma lamB_takes (a : X) (ha : IsClosed {a}) (z : X) (hz : z ∈ (C.lam a ha).toPartialMap.domain) :
    Takes (C.lamB a ha) z ((C.lam a ha).toPartialMap.hom ⟨z, hz⟩) := by
  haveI := pi_isOver _ (C.lam_isOver a ha)
  exact rep_of_rep _ (C.lamB a ha) rfl z hz

lemma rhoB_takes (b : X) (hb : IsClosed {b}) (z : X) (hz : z ∈ (C.rho b hb).toPartialMap.domain) :
    Takes (C.rhoB b hb) z ((C.rho b hb).toPartialMap.hom ⟨z, hz⟩) := by
  haveI := pi_isOver _ (C.rho_isOver b hb)
  exact rep_of_rep _ (C.rhoB b hb) rfl z hz

lemma lamB_inv_takes (a : X) (ha : IsClosed {a}) (z : X) (hz : z ∈ (C.lam a ha).toPartialMap.domain) :
    Takes (C.lamB a ha)⁻¹ ((C.lam a ha).toPartialMap.hom ⟨z, hz⟩) z := by
  haveI := pi_isOver _ (C.lam_isOver a ha).symm
  obtain ⟨h, e⟩ := rep_of_rep (C.lam a ha).symm.toPartialMap (C.lamB a ha)⁻¹ rfl _ (pi_mem_target _ z hz)
  exact ⟨h, e.trans (pi_symm_apply _ z hz _)⟩

lemma rhoB_inv_takes (b : X) (hb : IsClosed {b}) (z : X) (hz : z ∈ (C.rho b hb).toPartialMap.domain) :
    Takes (C.rhoB b hb)⁻¹ ((C.rho b hb).toPartialMap.hom ⟨z, hz⟩) z := by
  haveI := pi_isOver _ (C.rho_isOver b hb).symm
  obtain ⟨h, e⟩ := rep_of_rep (C.rho b hb).symm.toPartialMap (C.rhoB b hb)⁻¹ rfl _ (pi_mem_target _ z hz)
  exact ⟨h, e.trans (pi_symm_apply _ z hz _)⟩

/-- Re-charting, forward: if `σ ∈ H` sends the closed point `x` to `y`, then `σ λ_x = λ_y`. -/
theorem RC_fwd (σ : Bir k X) (hσ : σ ∈ C.H) (x : X) (hx : IsClosed {x}) (y : X) (hy : IsClosed {y})
    (h : Takes σ x y) : σ * C.lamB x hx = C.lamB y hy := by
  haveI := pi_isDominant (C.lam x hx)
  haveI := pi_isOver _ (C.lam_isOver x hx)
  haveI := pi_isOver _ (C.lam_isOver y hy)
  haveI := comp_isOver (k := k) (C.lam x hx).toPartialMap (rep σ)
  refine Units.ext (Subtype.ext ?_)
  change (C.lam x hx).toPartialMap.toRationalMap.comp σ.1.1 = (C.lam y hy).toPartialMap.toRationalMap
  rw [← rep_toRationalMap σ, Scheme.RationalMap.toRationalMap_comp]
  refine toRationalMap_eq_of_apply (k := k) ?_
  intro z h1 h2 hz
  obtain ⟨hz1, hz2⟩ := (mem_comp_domain _ _).1 h1
  rw [comp_hom_apply _ _ ⟨z, h1⟩ hz1 hz2]
  have t1 : Takes (σ * C.rhoB z hz) x ((rep σ).hom ⟨_, hz2⟩) :=
    Takes.comp ((C.rhoB_takes z hz x (C.lam_mem_rho x hx z hz hz1)).val_eq (C.lam_eq_rho x hx z hz hz1))
      (takes_self σ _ hz2) rfl
  have t2 : Takes (C.rhoB z hz * σ) x ((C.lam y hy).toPartialMap.hom ⟨z, h2⟩) :=
    Takes.comp h ((C.rhoB_takes z hz y (C.lam_mem_rho y hy z hz h2)).val_eq (C.lam_eq_rho y hy z hz h2)) rfl
  exact Takes.unique t1 (t2.of_eq (C.H_comm_rhoB σ hσ z hz).symm)

/-- Re-charting, backward: if `σ ∈ H` and `σ λ_x = λ_y`, then `σ` sends `x` to `y`. -/
theorem RC_bwd (σ : Bir k X) (hσ : σ ∈ C.H) (x : X) (hx : IsClosed {x}) (y : X) (hy : IsClosed {y})
    (h : σ * C.lamB x hx = C.lamB y hy) : Takes σ x y := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  obtain ⟨u, hux, huy, hu⟩ := exists_closed_inter (C.lam x hx).toPartialMap.domain
    (C.lam y hy).toPartialMap.domain (C.lam_ne x hx) (C.lam_ne y hy)
  have tp : Takes σ ((C.lam x hx).toPartialMap.hom ⟨u, hux⟩) ((C.lam y hy).toPartialMap.hom ⟨u, huy⟩) :=
    Takes.comp (C.lamB_inv_takes x hx u hux) (C.lamB_takes y hy u huy) (eq_mul_inv_of_mul_eq h)
  have t1 : Takes (σ * C.rhoB u hu) x ((C.lam y hy).toPartialMap.hom ⟨u, huy⟩) :=
    Takes.comp ((C.rhoB_takes u hu x (C.lam_mem_rho x hx u hu hux)).val_eq (C.lam_eq_rho x hx u hu hux))
      tp rfl
  have t2 : Takes (C.rhoB u hu)⁻¹ ((C.lam y hy).toPartialMap.hom ⟨u, huy⟩) y :=
    (C.rhoB_inv_takes u hu y (C.lam_mem_rho y hy u hu huy)).src_eq (C.lam_eq_rho y hy u hu huy)
  refine Takes.comp t1 t2 ?_
  rw [C.H_comm_rhoB σ hσ u hu, inv_mul_cancel_left]

/-- A point sent to a closed point by `σ ∈ H` lies in `W σ`. -/
theorem RC_W (σ : Bir k X) (hσ : σ ∈ C.H) (x : X) (hx : IsClosed {x}) (y : X) (hy : IsClosed {y})
    (h : Takes σ x y) : x ∈ W σ := by
  have e := C.RC_fwd σ hσ x hx y hy h
  have e' : σ⁻¹ * C.lamB y hy = C.lamB x hx := by rw [← e, inv_mul_cancel_left]
  obtain ⟨hy', -⟩ := C.RC_bwd σ⁻¹ (inv_mem hσ) y hy x hx e'
  obtain ⟨hd, hv⟩ := h
  exact mem_W.2 ⟨hd, by rw [hv]; exact hy'⟩

end StrictChunk

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkA_Pt =====
section

/-!
# Group chunk A6, part 2 (unit S4-JacChunkA): the closed points of `G` are `H`

For a strict chunk `C` with `H := C.H` and `G := G C.H`:
* `ι_eq_iff_mul`: for closed `x y`, `ι σ x = ι τ y ↔ σ λ_x = τ λ_y`;
* `Pt C : {g : G // IsClosed {g}} → C.H`, `ι σ x ↦ σ λ_x` (`Pt_ι`), equivariant for the left action (`Pt_L`);
* `PtEquiv C : {g : G // IsClosed {g}} ≃ C.H`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

section Charts

variable (H : Subgroup (Bir k X))

lemma isClosed_ι (σ : H) (x : X) (hx : IsClosed {x}) : IsClosed {ι H σ x} :=
  isClosed_singleton_apply (X ↘ Spec (.of k)) (G H ↘ Spec (.of k)) (ι H σ) (ι_sG H σ) x hx

lemma isClosed_of_ι (σ : H) (x : X) (h : IsClosed {ι H σ x}) : IsClosed {x} := by
  have e : (ι H σ) ⁻¹' {ι H σ x} = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (ι H σ).isOpenEmbedding.injective.eq_iff
  rw [← e]
  exact h.preimage (ι H σ).continuous

lemma exists_chart (g : G H) : ∃ σ : H, ∃ x : X, ι H σ x = g :=
  (gD H).toGlueData.ι_jointly_surjective g

lemma ι_eq_rel (σ τ : H) (x y : X) (h : ι H σ x = ι H τ y) :
    ∃ hW : x ∈ VH H σ τ, (tHH H σ τ ⟨x, hW⟩).1 = y := by
  obtain ⟨⟨x', hx'⟩, hz1, hz2⟩ := ((gD H).toGlueData.ι_eq_iff σ τ x y).1 h
  have e1 : x' = x := hz1
  have e2 : (tHH H σ τ ⟨x', hx'⟩).1 = y := hz2
  subst e1
  exact ⟨hx', e2⟩

lemma ι_eq_of_rel (σ τ : H) (x : X) (hW : x ∈ VH H σ τ) : ι H τ (tHH H σ τ ⟨x, hW⟩).1 = ι H σ x :=
  congrArg (fun φ => φ ⟨x, hW⟩) (ι_glue H σ τ)

variable (k) in
include k in
lemma exists_closedPoint : ∃ x : X, IsClosed ({x} : Set X) := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  obtain ⟨x, -, -, hx⟩ := exists_closed_inter (⊤ : X.Opens) ⊤ ⟨Classical.arbitrary X, trivial⟩
    ⟨Classical.arbitrary X, trivial⟩
  exact ⟨x, hx⟩

end Charts

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- Two closed chart points agree in `G` iff the corresponding elements `σ λ_x` agree. -/
theorem ι_eq_iff_mul (σ τ : C.H) (x : X) (hx : IsClosed {x}) (y : X) (hy : IsClosed {y}) :
    ι C.H σ x = ι C.H τ y ↔ (σ : Bir k X) * C.lamB x hx = (τ : Bir k X) * C.lamB y hy := by
  have hm : (τ : Bir k X)⁻¹ * (σ : Bir k X) ∈ C.H := mul_mem (inv_mem τ.2) σ.2
  constructor
  · intro h
    obtain ⟨hW, e⟩ := ι_eq_rel C.H σ τ x y h
    have t : Takes ((τ : Bir k X)⁻¹ * (σ : Bir k X)) x y := ⟨W_le _ hW, (tH_apply (σ : Bir k X) τ ⟨x, hW⟩).symm.trans e⟩
    have h' := C.RC_fwd _ hm x hx y hy t
    rw [mul_assoc] at h'
    exact inv_mul_eq_iff_eq_mul.1 h'
  · intro h
    have h' : ((τ : Bir k X)⁻¹ * (σ : Bir k X)) * C.lamB x hx = C.lamB y hy := by rw [mul_assoc, h, inv_mul_cancel_left]
    have t := C.RC_bwd _ hm x hx y hy h'
    have hW : x ∈ VH C.H σ τ := C.RC_W _ hm x hx y hy t
    have e : (tHH C.H σ τ ⟨x, hW⟩).1 = y :=
      (tH_apply (σ : Bir k X) τ ⟨x, hW⟩).trans (Takes.unique (takes_self _ x _) t)
    rw [← ι_eq_of_rel C.H σ τ x hW, e]

/-- The chart index of a point of `G`. -/
noncomputable def chS (g : G C.H) : C.H := (exists_chart C.H g).choose

/-- The chart coordinate of a point of `G`. -/
noncomputable def chX (g : G C.H) : X := (exists_chart C.H g).choose_spec.choose

lemma ch_spec (g : G C.H) : ι C.H (C.chS g) (C.chX g) = g := (exists_chart C.H g).choose_spec.choose_spec

lemma isClosed_chX (g : G C.H) (hg : IsClosed {g}) : IsClosed {C.chX g} :=
  isClosed_of_ι C.H _ _ (by rw [C.ch_spec]; exact hg)

/-- The element of `H` named by a closed point of `G`: `ι σ x ↦ σ λ_x`. -/
noncomputable def Pt (g : {g : G C.H // IsClosed {g}}) : C.H :=
  ⟨(C.chS g.1 : Bir k X) * C.lamB (C.chX g.1) (C.isClosed_chX g.1 g.2),
    mul_mem (C.chS g.1).2 (C.lamB_mem_H _ _)⟩

lemma Pt_ι (σ : C.H) (x : X) (hx : IsClosed {x}) :
    (C.Pt ⟨ι C.H σ x, isClosed_ι C.H σ x hx⟩ : Bir k X) = (σ : Bir k X) * C.lamB x hx :=
  (C.ι_eq_iff_mul _ _ _ (C.isClosed_chX _ (isClosed_ι C.H σ x hx)) x hx).1 (C.ch_spec _)

lemma Pt_injective : Function.Injective C.Pt := by
  intro g g' h
  apply Subtype.ext
  rw [← C.ch_spec g.1, ← C.ch_spec g'.1]
  exact (C.ι_eq_iff_mul _ _ _ (C.isClosed_chX g.1 g.2) _ (C.isClosed_chX g'.1 g'.2)).2
    (congrArg Subtype.val h)

lemma Pt_surjective : Function.Surjective C.Pt := by
  intro h
  obtain ⟨x, hx⟩ := exists_closedPoint k (X := X)
  let σ : C.H := ⟨(h : Bir k X) * (C.lamB x hx)⁻¹, mul_mem h.2 (inv_mem (C.lamB_mem_H x hx))⟩
  refine ⟨⟨ι C.H σ x, isClosed_ι C.H σ x hx⟩, Subtype.ext ?_⟩
  rw [C.Pt_ι σ x hx]
  exact inv_mul_cancel_right _ _

/-- Closed points of the glued scheme `G` are the elements of `H`. -/
noncomputable def PtEquiv : {g : G C.H // IsClosed {g}} ≃ C.H :=
  Equiv.ofBijective C.Pt ⟨C.Pt_injective, C.Pt_surjective⟩

end StrictChunk

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkB_Ext =====
section

/-!
# Group chunk B0 (unit S4-JacChunkB): morphisms into `G` are determined by closed points and glue pointwise

* `G_ext`: two `k`-morphisms from a reduced `k`-scheme locally of finite type into `G H` that agree on closed
  points are equal (the charts of `G H` are separated, `G H` itself need not be known separated);
* `glueG`: morphisms into `G H` on the members of a family of open immersions covering the closed points glue,
  once they agree on closed points;
* `PtT`, `lamT`: total versions of `Pt` and `lamB` (value `1` away from closed points).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

section Ext

variable (H : Subgroup (Bir k X))

/-- `k`-morphisms into `G H` from a reduced `k`-scheme locally of finite type agree once they agree on closed
points. -/
theorem G_ext {T : Scheme.{u}} [IsReduced T] (sT : T ⟶ Spec (.of k)) [LocallyOfFiniteType sT]
    (f g : T ⟶ G H) (hf : f ≫ sG H = sT) (hg : g ≫ sG H = sT)
    (h : ∀ t, IsClosed {t} → f t = g t) : f = g := by
  haveI : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace sT
  refine Scheme.hom_ext_of_forall f g fun t => ?_
  obtain ⟨σ, x, hx⟩ := exists_chart H (f t)
  have hle : f ⁻¹ᵁ (ι H σ).opensRange ≤ g ⁻¹ᵁ (ι H σ).opensRange := by
    refine opens_le_of_closedPoints _ _ fun s hs hsc => ?_
    have e : f s = g s := h s hsc
    refine (Scheme.Hom.mem_preimage _).2 ?_
    rw [← e]
    exact (Scheme.Hom.mem_preimage _).1 hs
  let U : T.Opens := f ⁻¹ᵁ (ι H σ).opensRange
  have hfU : Set.range (U.ι ≫ f) ⊆ Set.range (ι H σ) := by
    rintro _ ⟨s, rfl⟩
    exact Scheme.Hom.mem_opensRange.1 ((Scheme.Hom.mem_preimage _).1 s.2)
  have hgU : Set.range (U.ι ≫ g) ⊆ Set.range (ι H σ) := by
    rintro _ ⟨s, rfl⟩
    exact Scheme.Hom.mem_opensRange.1 ((Scheme.Hom.mem_preimage _).1 (hle s.2))
  have efU : IsOpenImmersion.lift (ι H σ) (U.ι ≫ f) hfU ≫ ι H σ = U.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
  have egU : IsOpenImmersion.lift (ι H σ) (U.ι ≫ g) hgU ≫ ι H σ = U.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have key : IsOpenImmersion.lift (ι H σ) (U.ι ≫ f) hfU = IsOpenImmersion.lift (ι H σ) (U.ι ≫ g) hgU := by
    refine ext_X (U.ι ≫ sT) _ _ ?_ ?_ ?_
    · rw [← ι_sG H σ, ← Category.assoc, efU, Category.assoc, hf]
    · rw [← ι_sG H σ, ← Category.assoc, egU, Category.assoc, hg]
    · intro s hs
      apply (ι H σ).isOpenEmbedding.injective
      have hs' : IsClosed {s.1} := isClosed_singleton_apply (U.ι ≫ sT) sT U.ι rfl s hs
      have e1 : (ι H σ) (IsOpenImmersion.lift (ι H σ) (U.ι ≫ f) hfU s) = f s.1 :=
        congrArg (fun φ => φ s) efU
      have e2 : (ι H σ) (IsOpenImmersion.lift (ι H σ) (U.ι ≫ g) hgU s) = g s.1 :=
        congrArg (fun φ => φ s) egU
      rw [e1, e2]
      exact h s.1 hs'
  refine ⟨U, (Scheme.Hom.mem_preimage _).2 (Scheme.Hom.mem_opensRange.2 ⟨x, hx⟩), ?_⟩
  rw [← efU, ← egU, key]

end Ext

section Glue

variable (H : Subgroup (Bir k X)) {T : Scheme.{u}} [IsReduced T] (sT : T ⟶ Spec (.of k))
  [LocallyOfFiniteType sT] {J : Type u} (P : J → Scheme.{u}) (j : ∀ i, P i ⟶ T) [∀ i, IsOpenImmersion (j i)]

/-- The open cover of `T` by the `j i`, when their ranges contain every closed point. -/
noncomputable def coverOfClosed (hcov : ∀ t, IsClosed {t} → ∃ i, ∃ p : P i, j i p = t) : T.OpenCover :=
  Scheme.Cover.mkOfCovers J P j (by
    haveI : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace sT
    have htop : (⨆ i, (j i).opensRange) = ⊤ := by
      refine top_unique (opens_le_of_closedPoints _ _ fun t _ ht => ?_)
      obtain ⟨i, p, hp⟩ := hcov t ht
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, Scheme.Hom.mem_opensRange.2 ⟨p, hp⟩⟩
    intro t
    have ht : t ∈ (⨆ i, (j i).opensRange) := by rw [htop]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 ht
    obtain ⟨p, hp⟩ := Scheme.Hom.mem_opensRange.1 hi
    exact ⟨i, p, hp⟩)

variable (φ : ∀ i, P i ⟶ G H) (hcov : ∀ t, IsClosed {t} → ∃ i, ∃ p : P i, j i p = t)
  (hφ : ∀ i, φ i ≫ sG H = j i ≫ sT)
  (hcomp : ∀ i i' (p : P i) (p' : P i'), IsClosed {p} → IsClosed {p'} → j i p = j i' p' → φ i p = φ i' p')

include hφ hcomp in
lemma glueG_compat (a b : J) :
    pullback.fst (j a) (j b) ≫ φ a = pullback.snd (j a) (j b) ≫ φ b := by
  haveI : IsReduced (pullback (j a) (j b)) := isReduced_of_isOpenImmersion (pullback.fst (j a) (j b) ≫ j a)
  refine G_ext H (pullback.fst (j a) (j b) ≫ j a ≫ sT) _ _ ?_ ?_ ?_
  · rw [Category.assoc, hφ]
  · rw [Category.assoc, hφ, pullback.condition_assoc]
  · intro r hr
    have h1 : IsClosed {pullback.fst (j a) (j b) r} :=
      isClosed_singleton_apply (pullback.fst (j a) (j b) ≫ j a ≫ sT) (j a ≫ sT) _ rfl r hr
    have h2 : IsClosed {pullback.snd (j a) (j b) r} :=
      isClosed_singleton_apply (pullback.fst (j a) (j b) ≫ j a ≫ sT) (j b ≫ sT) _
        (by rw [← pullback.condition_assoc]) r hr
    have e : j a (pullback.fst (j a) (j b) r) = j b (pullback.snd (j a) (j b) r) :=
      congrArg (fun ψ => ψ r) (pullback.condition (f := j a) (g := j b))
    exact hcomp a b _ _ h1 h2 e

/-- Pointwise gluing of morphisms into `G H`. -/
noncomputable def glueG : T ⟶ G H :=
  (coverOfClosed sT P j hcov).glueMorphisms φ (glueG_compat H sT P j φ hφ hcomp)

@[reassoc]
lemma glueG_fac (i : J) : j i ≫ glueG H sT P j φ hcov hφ hcomp = φ i :=
  Scheme.Cover.ι_glueMorphisms (coverOfClosed sT P j hcov) φ _ i

lemma glueG_over : glueG H sT P j φ hcov hφ hcomp ≫ sG H = sT :=
  Scheme.Cover.hom_ext (coverOfClosed sT P j hcov) _ _ fun (i : J) =>
    (glueG_fac_assoc H sT P j φ hcov hφ hcomp i (sG H)).trans (hφ i)

lemma glueG_apply (i : J) (p : P i) : glueG H sT P j φ hcov hφ hcomp (j i p) = φ i p :=
  congrArg (fun ψ => ψ p) (glueG_fac H sT P j φ hcov hφ hcomp i)

end Glue

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

open Classical in
/-- `lamB` as a total function (value `1` away from closed points). -/
noncomputable def lamT (x : X) : Bir k X := if hx : IsClosed {x} then C.lamB x hx else 1

lemma lamT_eq (x : X) (hx : IsClosed {x}) : C.lamT x = C.lamB x hx := by rw [lamT, dif_pos hx]

open Classical in
/-- `Pt` as a total function into `Bir k X` (value `1` away from closed points). -/
noncomputable def PtT (g : G C.H) : Bir k X := if hg : IsClosed {g} then (C.Pt ⟨g, hg⟩ : Bir k X) else 1

lemma PtT_eq (g : G C.H) (hg : IsClosed {g}) : C.PtT g = (C.Pt ⟨g, hg⟩ : Bir k X) := by rw [PtT, dif_pos hg]

lemma PtT_mem (g : G C.H) : C.PtT g ∈ C.H := by
  by_cases hg : IsClosed {g}
  · rw [C.PtT_eq g hg]; exact (C.Pt ⟨g, hg⟩).2
  · rw [PtT, dif_neg hg]; exact one_mem _

lemma PtT_ι (σ : C.H) (x : X) (hx : IsClosed {x}) : C.PtT (ι C.H σ x) = (σ : Bir k X) * C.lamT x := by
  rw [C.PtT_eq _ (isClosed_ι C.H σ x hx), C.Pt_ι σ x hx, C.lamT_eq x hx]

lemma PtT_inj (g g' : G C.H) (hg : IsClosed {g}) (hg' : IsClosed {g'}) (h : C.PtT g = C.PtT g') : g = g' := by
  rw [C.PtT_eq g hg, C.PtT_eq g' hg'] at h
  exact congrArg Subtype.val (C.Pt_injective (Subtype.ext h))

/-- `G_ext` in terms of `PtT` values. -/
theorem G_ext_Pt {T : Scheme.{u}} [IsReduced T] (sT : T ⟶ Spec (.of k)) [LocallyOfFiniteType sT]
    (f g : T ⟶ G C.H) (hf : f ≫ sG C.H = sT) (hg : g ≫ sG C.H = sT)
    (h : ∀ t, IsClosed {t} → C.PtT (f t) = C.PtT (g t)) : f = g :=
  G_ext C.H sT f g hf hg fun t ht =>
    C.PtT_inj _ _ (isClosed_singleton_apply sT (G C.H ↘ Spec (.of k)) f hf t ht)
      (isClosed_singleton_apply sT (G C.H ↘ Spec (.of k)) g hg t ht) (h t ht)

end StrictChunk

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkB_Act =====
section

/-!
# Group chunk B1 (unit S4-JacChunkB): the right action `act : G ×_k X ⟶ G`

* `lamT_mul`: for a closed point `q` of `Ω`, `λ_{pr₁ q} λ_{pr₂ q} = λ_{m q}`;
* `act`: glued from the pieces `Ω ⟶ G ×_k X`, `(x, y) ↦ (ι σ x, y)` with value `ι σ (m(x, y))`;
  `PtT (act z) = PtT (pr₁ z) * lamT (pr₂ z)` at closed points.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

lemma isClosed_Ω (q : C.Ω) (hq : IsClosed {q.1}) : IsClosed ({q} : Set C.Ω) := isClosed_mk' C.Ω q.1 q.2 hq

lemma isClosed_m (q : C.Ω) (hq : IsClosed {q.1}) : IsClosed {C.m q} :=
  isClosed_singleton_apply (C.Ω.ι ≫ pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k))
    (X ↘ Spec (.of k)) C.m C.m_over q (C.isClosed_Ω q hq)

/-- `λ_a λ_b = λ_{ab}` for a closed point `(a, b)` of `Ω`. -/
lemma lamT_mul (q : C.Ω) (hq : IsClosed {q.1}) :
    C.lamT (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1) * C.lamT (pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1) = C.lamT (C.m q) := by
  have ha := isClosed_fst q.1 hq
  have hb := isClosed_snd q.1 hq
  have hm := C.isClosed_m q hq
  rw [C.lamT_eq _ ha, C.lamT_eq _ hb, C.lamT_eq _ hm]
  have hsec : secL (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1) ha (pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1) = q.1 :=
    closedPoint_pullback_ext (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) _ _
      (secL_isClosed _ ha _ hb) hq (secL_apply_fst _ ha _) (secL_apply_snd _ ha _)
  have hdom : pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1 ∈ (C.lam _ ha).toPartialMap.domain :=
    (Scheme.Hom.mem_preimage _).2 (by rw [hsec]; exact q.2)
  have hval : (C.lam _ ha).toPartialMap.hom ⟨_, hdom⟩ = C.m q :=
    (C.lam_apply _ ha _ hdom).trans (congrArg C.m (Subtype.ext hsec))
  exact C.RC_fwd _ (C.lamB_mem_H _ ha) _ hb _ hm ((C.lamB_takes _ ha _ hdom).val_eq hval)

/-- The chart map `X ×_k X ⟶ G ×_k X`, `(x, y) ↦ (ι σ x, y)`. -/
noncomputable def jA (σ : C.H) : pullback (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ⟶
    pullback (sG C.H) (X ↘ Spec (.of k)) :=
  pullback.map _ _ _ _ (ι C.H σ) (𝟙 X) (𝟙 _) (by rw [Category.comp_id, ι_sG]) (by simp)

instance (σ : C.H) : IsOpenImmersion (C.jA σ) := by unfold jA; infer_instance

@[reassoc (attr := simp)]
lemma jA_fst (σ : C.H) : C.jA σ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ι C.H σ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma jA_snd (σ : C.H) : C.jA σ ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma jA_fst_apply (σ : C.H) (z : (pullback (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) : Scheme.{u})) :
    pullback.fst (sG C.H) (X ↘ Spec (.of k)) (C.jA σ z) = ι C.H σ (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) z) := congrArg (fun φ => φ z) (C.jA_fst σ)

lemma jA_snd_apply (σ : C.H) (z : (pullback (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) : Scheme.{u})) :
    pullback.snd (sG C.H) (X ↘ Spec (.of k)) (C.jA σ z) = pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) z := congrArg (fun φ => φ z) (C.jA_snd σ)

/-- `ι_eq_iff_mul` with the total `lamT`. -/
lemma ι_eq_iff_mulT (σ τ : C.H) (x : X) (hx : IsClosed {x}) (y : X) (hy : IsClosed {y}) :
    ι C.H σ x = ι C.H τ y ↔ (σ : Bir k X) * C.lamT x = (τ : Bir k X) * C.lamT y := by
  rw [C.lamT_eq x hx, C.lamT_eq y hy]; exact C.ι_eq_iff_mul σ τ x hx y hy

lemma isClosed_Ωval (q : C.Ω) (hq : IsClosed ({q} : Set C.Ω.toScheme)) : IsClosed {q.1} :=
  isClosed_singleton_apply (C.Ω.ι ≫ pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k))
    (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k)) C.Ω.ι rfl q hq

end StrictChunk

lemma isClosed_of_inj {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (f : A → B) (hf : Continuous f)
    (hi : Function.Injective f) (a : A) (h : IsClosed ({f a} : Set B)) : IsClosed ({a} : Set A) := by
  have e : f ⁻¹' {f a} = {a} := by
    ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact hi.eq_iff
  rw [← e]; exact h.preimage hf

instance (H : Subgroup (Bir k X)) : LocallyOfFiniteType (sG H) :=
  (inferInstance : LocallyOfFiniteType (G H ↘ Spec (.of k)))

instance (H : Subgroup (Bir k X)) : IsLocallyNoetherian (G H) := LocallyOfFiniteType.isLocallyNoetherian (sG H)

variable [GeometricallyReduced (X ↘ Spec (.of k))]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- The structure map of `G ×_k X`. -/
noncomputable abbrev sGX : pullback (sG C.H) (X ↘ Spec (.of k)) ⟶ Spec (.of k) :=
  pullback.fst (sG C.H) (X ↘ Spec (.of k)) ≫ sG C.H

lemma act_over (σ : C.H) : (C.m ≫ ι C.H σ) ≫ sG C.H = (C.Ω.ι ≫ C.jA σ) ≫ C.sGX := by
  simp only [sGX, Category.assoc, ι_sG, C.jA_fst_assoc, C.m_over]

lemma act_cov (t : (pullback (sG C.H) (X ↘ Spec (.of k)) : Scheme.{u})) (ht : IsClosed {t}) :
    ∃ σ : C.H, ∃ p : C.Ω.toScheme, (C.Ω.ι ≫ C.jA σ) p = t := by
  have hg : IsClosed {pullback.fst (sG C.H) (X ↘ Spec (.of k)) t} :=
    isClosed_singleton_apply C.sGX (G C.H ↘ Spec (.of k)) _ rfl t ht
  have hy : IsClosed {pullback.snd (sG C.H) (X ↘ Spec (.of k)) t} :=
    isClosed_singleton_apply C.sGX (X ↘ Spec (.of k)) _ pullback.condition.symm t ht
  obtain ⟨σ, x, hx⟩ := exists_chart C.H (pullback.fst (sG C.H) (X ↘ Spec (.of k)) t)
  have hxc : IsClosed {x} := isClosed_of_ι C.H σ x (by rw [hx]; exact hg)
  obtain ⟨z, hzΩ, hz, hzy⟩ := C.fib_right _ hy
  have hu := isClosed_fst z hz
  let σ' : C.H := ⟨(σ : Bir k X) * C.lamB x hxc * (C.lamB _ hu)⁻¹,
    mul_mem (mul_mem σ.2 (C.lamB_mem_H x hxc)) (inv_mem (C.lamB_mem_H _ hu))⟩
  have e1 : ι C.H σ' (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) z) = ι C.H σ x :=
    (C.ι_eq_iff_mul σ' σ _ hu x hxc).2 (inv_mul_cancel_right _ _)
  refine ⟨σ', ⟨z, hzΩ⟩, ?_⟩
  have hc : IsClosed {C.jA σ' z} :=
    isClosed_singleton_apply (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k)) C.sGX
      (C.jA σ') (by simp only [sGX, C.jA_fst_assoc, ι_sG]) z hz
  exact closedPoint_pullback_ext (sG C.H) (X ↘ Spec (.of k)) (C.jA σ' z) t hc ht
    ((C.jA_fst_apply σ' z).trans (e1.trans hx)) ((C.jA_snd_apply σ' z).trans hzy)

lemma act_comp (σ τ : C.H) (p p' : C.Ω.toScheme) (hp : IsClosed {p}) (hp' : IsClosed {p'})
    (e : (C.Ω.ι ≫ C.jA σ) p = (C.Ω.ι ≫ C.jA τ) p') : (C.m ≫ ι C.H σ) p = (C.m ≫ ι C.H τ) p' := by
  have hq := C.isClosed_Ωval p hp
  have hq' := C.isClosed_Ωval p' hp'
  have e1 : ι C.H σ (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) p.1) =
      ι C.H τ (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) p'.1) :=
    (C.jA_fst_apply σ p.1).symm.trans
      ((congrArg (pullback.fst (sG C.H) (X ↘ Spec (.of k))) e).trans (C.jA_fst_apply τ p'.1))
  have e2 : pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) p.1 =
      pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) p'.1 :=
    (C.jA_snd_apply σ p.1).symm.trans
      ((congrArg (pullback.snd (sG C.H) (X ↘ Spec (.of k))) e).trans (C.jA_snd_apply τ p'.1))
  have h1 := (C.ι_eq_iff_mulT σ τ _ (isClosed_fst _ hq) _ (isClosed_fst _ hq')).1 e1
  show ι C.H σ (C.m p) = ι C.H τ (C.m p')
  rw [C.ι_eq_iff_mulT σ τ _ (C.isClosed_m p hq) _ (C.isClosed_m p' hq'), ← C.lamT_mul p hq,
    ← C.lamT_mul p' hq', e2, ← mul_assoc, ← mul_assoc, h1]

/-- The right action `G ×_k X ⟶ G`, `(ι σ x, y) ↦ ι σ (m(x, y))`. -/
noncomputable def act : pullback (sG C.H) (X ↘ Spec (.of k)) ⟶ G C.H :=
  glueG C.H C.sGX (fun _ : C.H => C.Ω.toScheme) (fun σ => C.Ω.ι ≫ C.jA σ) (fun σ => C.m ≫ ι C.H σ)
    C.act_cov C.act_over C.act_comp

lemma act_over' : C.act ≫ sG C.H = C.sGX :=
  glueG_over C.H C.sGX (fun _ : C.H => C.Ω.toScheme) (fun σ => C.Ω.ι ≫ C.jA σ) (fun σ => C.m ≫ ι C.H σ)
    C.act_cov C.act_over C.act_comp

/-- The value of `act` at a closed point: `PtT (act z) = PtT (pr₁ z) * λ_{pr₂ z}`. -/
theorem PtT_act (t : (pullback (sG C.H) (X ↘ Spec (.of k)) : Scheme.{u})) (ht : IsClosed {t}) :
    C.PtT (C.act t) = C.PtT (pullback.fst (sG C.H) (X ↘ Spec (.of k)) t) *
      C.lamT (pullback.snd (sG C.H) (X ↘ Spec (.of k)) t) := by
  obtain ⟨σ, p, rfl⟩ := C.act_cov t ht
  have hp : IsClosed {p} := isClosed_of_inj _ (C.Ω.ι ≫ C.jA σ).continuous
    (C.Ω.ι ≫ C.jA σ).isOpenEmbedding.injective p ht
  have hq := C.isClosed_Ωval p hp
  have e : C.act ((C.Ω.ι ≫ C.jA σ) p) = ι C.H σ (C.m p) :=
    glueG_apply C.H C.sGX (fun _ : C.H => C.Ω.toScheme) (fun σ => C.Ω.ι ≫ C.jA σ) (fun σ => C.m ≫ ι C.H σ)
      C.act_cov C.act_over C.act_comp σ p
  have e1 : pullback.fst (sG C.H) (X ↘ Spec (.of k)) ((C.Ω.ι ≫ C.jA σ) p) =
      ι C.H σ (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) p.1) := C.jA_fst_apply σ p.1
  have e2 : pullback.snd (sG C.H) (X ↘ Spec (.of k)) ((C.Ω.ι ≫ C.jA σ) p) =
      pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) p.1 := C.jA_snd_apply σ p.1
  rw [e, e1, e2, C.PtT_ι σ _ (C.isClosed_m p hq), C.PtT_ι σ _ (isClosed_fst _ hq), mul_assoc, C.lamT_mul p hq]

end StrictChunk

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkB_R =====
section

/-!
# Group chunk B2 (unit S4-JacChunkB): right translations of `G`

* `Rb b`: `g ↦ act (g, b)`, value `PtT g * λ_b`;
* `Rinv b`: glued from `ι σ ∘ ρ_b⁻¹` on the target of `ρ_b`, value `PtT g * λ_b⁻¹`;
* `exists_R`: for every `τ ∈ H` a `k`-endomorphism `R` of `G` with `PtT (R g) = PtT g * τ` at closed points.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

section Rinv

variable (b : X) (hb : IsClosed {b})

/-- `ρ_b⁻¹ y` is a closed point with `λ_{ρ_b⁻¹ y} = λ_y λ_b⁻¹`. -/
lemma rhoInv_spec (y : (C.rho b hb).symm.toPartialMap.domain) (hyc : IsClosed {y.1}) :
    IsClosed {(C.rho b hb).symm.toPartialMap.hom y} ∧
    C.lamT ((C.rho b hb).symm.toPartialMap.hom y) = C.lamT y.1 * (C.lamB b hb)⁻¹ := by
  haveI := pi_isOver _ (C.rho_isOver b hb).symm
  have hw : IsClosed {(C.rho b hb).symm.toPartialMap.hom y} :=
    isClosed_hom_apply (k := k) (C.rho b hb).symm.toPartialMap y.1 y.2 hyc
  refine ⟨hw, ?_⟩
  have hdom : (C.rho b hb).symm.toPartialMap.hom y ∈ (C.rho b hb).toPartialMap.domain :=
    pi_mem_target (C.rho b hb).symm y.1 y.2
  have hback : (C.rho b hb).toPartialMap.hom ⟨_, hdom⟩ = y.1 :=
    pi_symm_apply (C.rho b hb).symm y.1 y.2 hdom
  have hq : IsClosed {secR b hb ((C.rho b hb).symm.toPartialMap.hom y)} := secR_isClosed (sX := X ↘ Spec (.of k)) b hb _ hw
  have hm := C.lamT_mul ⟨secR b hb ((C.rho b hb).symm.toPartialMap.hom y), hdom⟩ hq
  have e3 : C.m ⟨secR b hb ((C.rho b hb).symm.toPartialMap.hom y), hdom⟩ = y.1 :=
    (C.rho_apply b hb _ hdom).symm.trans hback
  dsimp only at hm
  rw [secR_apply_fst, secR_apply_snd, e3, C.lamT_eq b hb] at hm
  rw [← hm, mul_inv_cancel_right]

lemma rinv_over (σ : C.H) : ((C.rho b hb).symm.toPartialMap.hom ≫ ι C.H σ) ≫ sG C.H =
    ((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ) ≫ sG C.H := by
  haveI := pi_isOver _ (C.rho_isOver b hb).symm
  simp only [Category.assoc, ι_sG]
  exact HomIsOver.comp_over (f := (C.rho b hb).symm.toPartialMap.hom) (S := Spec (.of k))

lemma rinv_cov (g : G C.H) (hg : IsClosed {g}) :
    ∃ σ : C.H, ∃ p : (C.rho b hb).symm.toPartialMap.domain.toScheme,
      ((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ) p = g := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  obtain ⟨σ, x, hx⟩ := exists_chart C.H g
  have hxc : IsClosed {x} := isClosed_of_ι C.H σ x (by rw [hx]; exact hg)
  have hne : (((C.rho b hb).symm.toPartialMap.domain : X.Opens) : Set X).Nonempty :=
    (C.rho b hb).dense_target.nonempty
  obtain ⟨y, hy, -, hyc⟩ := exists_closed_inter _ _ hne hne
  let σ' : C.H := ⟨(σ : Bir k X) * C.lamB x hxc * (C.lamB y hyc)⁻¹,
    mul_mem (mul_mem σ.2 (C.lamB_mem_H x hxc)) (inv_mem (C.lamB_mem_H y hyc))⟩
  exact ⟨σ', ⟨y, hy⟩, ((C.ι_eq_iff_mul σ' σ y hyc x hxc).2 (inv_mul_cancel_right _ _)).trans hx⟩

lemma rinv_comp (σ τ : C.H) (p p' : (C.rho b hb).symm.toPartialMap.domain.toScheme)
    (hp : IsClosed {p}) (hp' : IsClosed {p'})
    (e : ((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ) p =
      ((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H τ) p') :
    ((C.rho b hb).symm.toPartialMap.hom ≫ ι C.H σ) p = ((C.rho b hb).symm.toPartialMap.hom ≫ ι C.H τ) p' := by
  have hq : IsClosed {p.1} := isClosed_val (k := k) _ p hp
  have hq' : IsClosed {p'.1} := isClosed_val (k := k) _ p' hp'
  obtain ⟨hw, hl⟩ := C.rhoInv_spec b hb p hq
  obtain ⟨hw', hl'⟩ := C.rhoInv_spec b hb p' hq'
  have h1 := (C.ι_eq_iff_mulT σ τ _ hq _ hq').1 e
  show ι C.H σ ((C.rho b hb).symm.toPartialMap.hom p) = ι C.H τ ((C.rho b hb).symm.toPartialMap.hom p')
  rw [C.ι_eq_iff_mulT σ τ _ hw _ hw', hl, hl', ← mul_assoc, ← mul_assoc, h1]

/-- Right translation by `λ_b⁻¹`. -/
noncomputable def Rinv : G C.H ⟶ G C.H :=
  glueG C.H (sG C.H) (fun _ : C.H => (C.rho b hb).symm.toPartialMap.domain.toScheme)
    (fun σ => (C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ)
    (fun σ => (C.rho b hb).symm.toPartialMap.hom ≫ ι C.H σ) (C.rinv_cov b hb) (C.rinv_over b hb) (C.rinv_comp b hb)

lemma Rinv_over : C.Rinv b hb ≫ sG C.H = sG C.H :=
  glueG_over C.H (sG C.H) (fun _ : C.H => (C.rho b hb).symm.toPartialMap.domain.toScheme)
    (fun σ => (C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ)
    (fun σ => (C.rho b hb).symm.toPartialMap.hom ≫ ι C.H σ) (C.rinv_cov b hb) (C.rinv_over b hb) (C.rinv_comp b hb)

lemma PtT_Rinv (g : G C.H) (hg : IsClosed {g}) : C.PtT (C.Rinv b hb g) = C.PtT g * (C.lamB b hb)⁻¹ := by
  obtain ⟨σ, p, rfl⟩ := C.rinv_cov b hb g hg
  have hp : IsClosed {p} := isClosed_of_inj _ ((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ).continuous
    ((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ).isOpenEmbedding.injective p hg
  have hq : IsClosed {p.1} := isClosed_val (k := k) _ p hp
  obtain ⟨hw, hl⟩ := C.rhoInv_spec b hb p hq
  have e : C.Rinv b hb (((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ) p) =
      ι C.H σ ((C.rho b hb).symm.toPartialMap.hom p) :=
    glueG_apply C.H (sG C.H) (fun _ : C.H => (C.rho b hb).symm.toPartialMap.domain.toScheme)
      (fun σ => (C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ)
      (fun σ => (C.rho b hb).symm.toPartialMap.hom ≫ ι C.H σ) (C.rinv_cov b hb) (C.rinv_over b hb)
      (C.rinv_comp b hb) σ p
  rw [e]
  show C.PtT (ι C.H σ _) = C.PtT (ι C.H σ p.1) * _
  rw [C.PtT_ι σ _ hw, C.PtT_ι σ _ hq, hl, mul_assoc]

end Rinv

variable [GeometricallyReduced (X ↘ Spec (.of k))]

/-- `g ↦ (g, b)`. -/
noncomputable def liftb (b : X) (hb : IsClosed {b}) : G C.H ⟶ pullback (sG C.H) (X ↘ Spec (.of k)) :=
  pullback.lift (𝟙 _) (sG C.H ≫ pointOfClosedPoint (X ↘ Spec (.of k)) b hb) (by simp)

/-- Right translation by `λ_b`: `g ↦ act (g, b)`. -/
noncomputable def Rb (b : X) (hb : IsClosed {b}) : G C.H ⟶ G C.H := C.liftb b hb ≫ C.act

lemma liftb_fst (b : X) (hb : IsClosed {b}) :
    C.liftb b hb ≫ pullback.fst (sG C.H) (X ↘ Spec (.of k)) = 𝟙 _ := pullback.lift_fst _ _ _

lemma liftb_snd (b : X) (hb : IsClosed {b}) : C.liftb b hb ≫ pullback.snd (sG C.H) (X ↘ Spec (.of k)) =
    sG C.H ≫ pointOfClosedPoint (X ↘ Spec (.of k)) b hb := pullback.lift_snd _ _ _

lemma liftb_sGX (b : X) (hb : IsClosed {b}) : C.liftb b hb ≫ C.sGX = sG C.H := by
  show C.liftb b hb ≫ pullback.fst (sG C.H) (X ↘ Spec (.of k)) ≫ sG C.H = sG C.H
  rw [← Category.assoc, C.liftb_fst b hb, Category.id_comp]

lemma Rb_over (b : X) (hb : IsClosed {b}) : C.Rb b hb ≫ sG C.H = sG C.H := by
  rw [Rb, Category.assoc, act_over']; exact C.liftb_sGX b hb

lemma PtT_Rb (b : X) (hb : IsClosed {b}) (g : G C.H) (hg : IsClosed {g}) :
    C.PtT (C.Rb b hb g) = C.PtT g * C.lamB b hb := by
  have hl : IsClosed {C.liftb b hb g} :=
    isClosed_singleton_apply (sG C.H) C.sGX (C.liftb b hb) (C.liftb_sGX b hb) g hg
  have e1 : pullback.fst (sG C.H) (X ↘ Spec (.of k)) (C.liftb b hb g) = g := by
    have := congrArg (fun φ => φ g) (C.liftb_fst b hb)
    exact this
  have e2 : pullback.snd (sG C.H) (X ↘ Spec (.of k)) (C.liftb b hb g) = b := by
    have h1 : (C.liftb b hb ≫ pullback.snd (sG C.H) (X ↘ Spec (.of k))) g =
        (sG C.H ≫ pointOfClosedPoint (X ↘ Spec (.of k)) b hb) g := by rw [C.liftb_snd b hb]
    have h2 : (sG C.H ≫ pointOfClosedPoint (X ↘ Spec (.of k)) b hb) g = b :=
      pointOfClosedPoint_apply (X ↘ Spec (.of k)) b hb _
    exact h1.trans h2
  show C.PtT (C.act (C.liftb b hb g)) = _
  rw [C.PtT_act _ hl, e1, e2, C.lamT_eq b hb]

/-- Right translations by all elements of `H`. -/
theorem exists_R (τ : Bir k X) (hτ : τ ∈ C.H) :
    ∃ R : G C.H ⟶ G C.H, R ≫ sG C.H = sG C.H ∧ ∀ g, IsClosed {g} → C.PtT (R g) = C.PtT g * τ := by
  unfold H at hτ
  induction hτ using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hx
    exact ⟨C.Rb a ha, C.Rb_over a ha, C.PtT_Rb a ha⟩
  | inv_mem x hx =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hx
    exact ⟨C.Rinv a ha, C.Rinv_over a ha, C.PtT_Rinv a ha⟩
  | one => exact ⟨𝟙 _, Category.id_comp _, fun g _ => (mul_one _).symm⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨R1, h1, v1⟩ := ihx
    obtain ⟨R2, h2, v2⟩ := ihy
    refine ⟨R1 ≫ R2, by rw [Category.assoc, h2, h1], fun g hg => ?_⟩
    have hc := isClosed_singleton_apply (sG C.H) (sG C.H) R1 h1 g hg
    show C.PtT (R2 (R1 g)) = _
    rw [v2 _ hc, v1 g hg, mul_assoc]

end StrictChunk

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkB_Mul =====
section

/-!
# Group chunk B3 (unit S4-JacChunkB): the multiplication `μ : G ×_k G ⟶ G`

* `G` is geometrically reduced over `k` (its charts are copies of `X`);
* `Rt τ`: a chosen right translation by `τ ∈ H`;
* `mu`: glued over the charts `G ×_k X ⟶ G ×_k G`, `(g, x) ↦ (g, ι τ x)`, from `(g, x) ↦ act (R_τ g, x)`;
  `PtT (mu t) = PtT (pr₁ t) * PtT (pr₂ t)` at closed points.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

/-- `G` is geometrically reduced over `k`: base changes of its charts are base changes of `X`. -/
instance geometricallyReduced_sG (H : Subgroup (Bir k X)) : GeometricallyReduced (sG H) := by
  constructor
  intro K _ y Z fst snd h
  apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := (gD H).toGlueData.openCover.pullback₁ fst)
  intro σ
  have hl : IsPullback (pullback.fst fst (ι H σ)) (pullback.snd fst (ι H σ)) fst (ι H σ) :=
    IsPullback.of_hasPullback _ _
  have hp := (hl.paste_horiz h.flip).flip
  exact GeometricallyReduced.geometrically_isReduced (f := X ↘ Spec (.of k)) y _ _
    (by rw [← ι_sG H σ]; exact hp)

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- A chosen right translation by `τ ∈ H`. -/
noncomputable def Rt (τ : C.H) : G C.H ⟶ G C.H := Classical.choose (C.exists_R τ τ.2)

lemma Rt_over (τ : C.H) : C.Rt τ ≫ sG C.H = sG C.H := (Classical.choose_spec (C.exists_R τ τ.2)).1

lemma PtT_Rt (τ : C.H) (g : G C.H) (hg : IsClosed {g}) : C.PtT (C.Rt τ g) = C.PtT g * τ :=
  (Classical.choose_spec (C.exists_R τ τ.2)).2 g hg

/-- `(g, x) ↦ (R_τ g, x)`. -/
noncomputable def mapR (τ : C.H) : pullback (sG C.H) (X ↘ Spec (.of k)) ⟶ pullback (sG C.H) (X ↘ Spec (.of k)) :=
  pullback.map _ _ _ _ (C.Rt τ) (𝟙 X) (𝟙 _) (by rw [Category.comp_id, C.Rt_over])
    (by rw [Category.comp_id, Category.id_comp])

@[reassoc]
lemma mapR_fst (τ : C.H) : C.mapR τ ≫ pullback.fst (sG C.H) (X ↘ Spec (.of k)) =
    pullback.fst (sG C.H) (X ↘ Spec (.of k)) ≫ C.Rt τ := pullback.lift_fst _ _ _

@[reassoc]
lemma mapR_snd (τ : C.H) : C.mapR τ ≫ pullback.snd (sG C.H) (X ↘ Spec (.of k)) =
    pullback.snd (sG C.H) (X ↘ Spec (.of k)) := (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma mapR_sGX (τ : C.H) : C.mapR τ ≫ C.sGX = C.sGX := by
  show C.mapR τ ≫ pullback.fst (sG C.H) (X ↘ Spec (.of k)) ≫ sG C.H = pullback.fst _ _ ≫ sG C.H
  rw [C.mapR_fst_assoc, C.Rt_over]

lemma mapR_act_over (τ : C.H) : (C.mapR τ ≫ C.act) ≫ sG C.H = C.sGX := by
  rw [Category.assoc, C.act_over', C.mapR_sGX]

/-- The chart `(g, x) ↦ (g, ι τ x)` of `G ×_k G`. -/
noncomputable def jB (τ : C.H) : pullback (sG C.H) (X ↘ Spec (.of k)) ⟶ pullback (sG C.H) (sG C.H) :=
  pullback.map _ _ _ _ (𝟙 _) (ι C.H τ) (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ι_sG])

instance (τ : C.H) : IsOpenImmersion (C.jB τ) := by unfold jB; infer_instance

@[reassoc]
lemma jB_fst (τ : C.H) : C.jB τ ≫ pullback.fst (sG C.H) (sG C.H) = pullback.fst (sG C.H) (X ↘ Spec (.of k)) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
lemma jB_snd (τ : C.H) : C.jB τ ≫ pullback.snd (sG C.H) (sG C.H) =
    pullback.snd (sG C.H) (X ↘ Spec (.of k)) ≫ ι C.H τ := pullback.lift_snd _ _ _

/-- The structure map of `G ×_k G`. -/
noncomputable abbrev sGG : pullback (sG C.H) (sG C.H) ⟶ Spec (.of k) := pullback.fst (sG C.H) (sG C.H) ≫ sG C.H

lemma jB_sGG (τ : C.H) : C.jB τ ≫ C.sGG = C.sGX := by
  show C.jB τ ≫ pullback.fst (sG C.H) (sG C.H) ≫ sG C.H = pullback.fst _ _ ≫ sG C.H
  rw [C.jB_fst_assoc]

lemma mu_over (τ : C.H) : (C.mapR τ ≫ C.act) ≫ sG C.H = C.jB τ ≫ C.sGG :=
  (C.mapR_act_over τ).trans (C.jB_sGG τ).symm

lemma mu_cov (t : (pullback (sG C.H) (sG C.H) : Scheme.{u})) (ht : IsClosed {t}) :
    ∃ τ : C.H, ∃ p : (pullback (sG C.H) (X ↘ Spec (.of k)) : Scheme.{u}), C.jB τ p = t := by
  have h1 : IsClosed {pullback.fst (sG C.H) (sG C.H) t} :=
    isClosed_singleton_apply C.sGG (sG C.H) _ rfl t ht
  have h2 : IsClosed {pullback.snd (sG C.H) (sG C.H) t} :=
    isClosed_singleton_apply C.sGG (sG C.H) _ pullback.condition.symm t ht
  obtain ⟨τ, x, hx⟩ := exists_chart C.H (pullback.snd (sG C.H) (sG C.H) t)
  have hxc : IsClosed {x} := isClosed_of_ι C.H τ x (by rw [hx]; exact h2)
  obtain ⟨p, hp, hp1, hp2⟩ := exists_closedPoint_pullback (sG C.H) (X ↘ Spec (.of k)) _ h1 x hxc
  refine ⟨τ, p, ?_⟩
  have hc : IsClosed {C.jB τ p} := isClosed_singleton_apply C.sGX C.sGG (C.jB τ) (C.jB_sGG τ) p hp
  have f1 : pullback.fst (sG C.H) (sG C.H) (C.jB τ p) = pullback.fst (sG C.H) (X ↘ Spec (.of k)) p :=
    congrArg (fun φ => φ p) (C.jB_fst τ)
  have f2 : pullback.snd (sG C.H) (sG C.H) (C.jB τ p) = ι C.H τ (pullback.snd (sG C.H) (X ↘ Spec (.of k)) p) :=
    congrArg (fun φ => φ p) (C.jB_snd τ)
  exact closedPoint_pullback_ext (sG C.H) (sG C.H) _ t hc ht (f1.trans hp1)
    (f2.trans ((congrArg (ι C.H τ) hp2).trans hx))

lemma PtT_mapR_act (τ : C.H) (p : (pullback (sG C.H) (X ↘ Spec (.of k)) : Scheme.{u})) (hp : IsClosed {p}) :
    IsClosed {C.act (C.mapR τ p)} ∧ C.PtT (C.act (C.mapR τ p)) =
      C.PtT (pullback.fst (sG C.H) (X ↘ Spec (.of k)) p) *
        ((τ : Bir k X) * C.lamT (pullback.snd (sG C.H) (X ↘ Spec (.of k)) p)) := by
  have hg := isClosed_singleton_apply C.sGX (sG C.H) _ rfl p hp
  have hm := isClosed_singleton_apply C.sGX C.sGX (C.mapR τ) (C.mapR_sGX τ) p hp
  refine ⟨isClosed_singleton_apply C.sGX (sG C.H) (C.mapR τ ≫ C.act) (C.mapR_act_over τ) p hp, ?_⟩
  have f1 : pullback.fst (sG C.H) (X ↘ Spec (.of k)) (C.mapR τ p) = C.Rt τ (pullback.fst (sG C.H) (X ↘ Spec (.of k)) p) :=
    congrArg (fun φ => φ p) (C.mapR_fst τ)
  have f2 : pullback.snd (sG C.H) (X ↘ Spec (.of k)) (C.mapR τ p) = pullback.snd (sG C.H) (X ↘ Spec (.of k)) p :=
    congrArg (fun φ => φ p) (C.mapR_snd τ)
  rw [C.PtT_act _ hm, f1, f2, C.PtT_Rt τ _ hg, mul_assoc]

lemma mu_comp (τ τ' : C.H) (p p' : (pullback (sG C.H) (X ↘ Spec (.of k)) : Scheme.{u}))
    (hp : IsClosed {p}) (hp' : IsClosed {p'}) (e : C.jB τ p = C.jB τ' p') :
    (C.mapR τ ≫ C.act) p = (C.mapR τ' ≫ C.act) p' := by
  have e1 : pullback.fst (sG C.H) (X ↘ Spec (.of k)) p = pullback.fst (sG C.H) (X ↘ Spec (.of k)) p' :=
    (congrArg (fun φ => φ p) (C.jB_fst τ)).symm.trans
      ((congrArg (pullback.fst (sG C.H) (sG C.H)) e).trans (congrArg (fun φ => φ p') (C.jB_fst τ')))
  have e2 : ι C.H τ (pullback.snd (sG C.H) (X ↘ Spec (.of k)) p) =
      ι C.H τ' (pullback.snd (sG C.H) (X ↘ Spec (.of k)) p') :=
    (congrArg (fun φ => φ p) (C.jB_snd τ)).symm.trans
      ((congrArg (pullback.snd (sG C.H) (sG C.H)) e).trans (congrArg (fun φ => φ p') (C.jB_snd τ')))
  have hx := isClosed_singleton_apply C.sGX (X ↘ Spec (.of k)) _ pullback.condition.symm p hp
  have hx' := isClosed_singleton_apply C.sGX (X ↘ Spec (.of k)) _ pullback.condition.symm p' hp'
  have h3 := (C.ι_eq_iff_mulT τ τ' _ hx _ hx').1 e2
  obtain ⟨c, v⟩ := C.PtT_mapR_act τ p hp
  obtain ⟨c', v'⟩ := C.PtT_mapR_act τ' p' hp'
  refine C.PtT_inj _ _ c c' ?_
  show C.PtT (C.act (C.mapR τ p)) = C.PtT (C.act (C.mapR τ' p'))
  rw [v, v', e1, h3]

/-- The multiplication `G ×_k G ⟶ G`. -/
noncomputable def mu : pullback (sG C.H) (sG C.H) ⟶ G C.H :=
  glueG C.H C.sGG (fun _ : C.H => pullback (sG C.H) (X ↘ Spec (.of k))) C.jB (fun τ => C.mapR τ ≫ C.act)
    C.mu_cov C.mu_over C.mu_comp

lemma mu_over' : C.mu ≫ sG C.H = C.sGG :=
  glueG_over C.H C.sGG (fun _ : C.H => pullback (sG C.H) (X ↘ Spec (.of k))) C.jB (fun τ => C.mapR τ ≫ C.act)
    C.mu_cov C.mu_over C.mu_comp

/-- The value of `μ` at a closed point: `PtT (μ t) = PtT (pr₁ t) * PtT (pr₂ t)`. -/
theorem PtT_mu (t : (pullback (sG C.H) (sG C.H) : Scheme.{u})) (ht : IsClosed {t}) :
    C.PtT (C.mu t) = C.PtT (pullback.fst (sG C.H) (sG C.H) t) * C.PtT (pullback.snd (sG C.H) (sG C.H) t) := by
  obtain ⟨τ, p, rfl⟩ := C.mu_cov t ht
  have hp : IsClosed {p} := isClosed_of_inj _ (C.jB τ).continuous (C.jB τ).isOpenEmbedding.injective p ht
  have hx := isClosed_singleton_apply C.sGX (X ↘ Spec (.of k)) _ pullback.condition.symm p hp
  have e : C.mu (C.jB τ p) = C.act (C.mapR τ p) :=
    glueG_apply C.H C.sGG (fun _ : C.H => pullback (sG C.H) (X ↘ Spec (.of k))) C.jB
      (fun τ => C.mapR τ ≫ C.act) C.mu_cov C.mu_over C.mu_comp τ p
  have f1 : pullback.fst (sG C.H) (sG C.H) (C.jB τ p) = pullback.fst (sG C.H) (X ↘ Spec (.of k)) p :=
    congrArg (fun φ => φ p) (C.jB_fst τ)
  have f2 : pullback.snd (sG C.H) (sG C.H) (C.jB τ p) = ι C.H τ (pullback.snd (sG C.H) (X ↘ Spec (.of k)) p) :=
    congrArg (fun φ => φ p) (C.jB_snd τ)
  rw [e, (C.PtT_mapR_act τ p hp).2, f1, f2, C.PtT_ι τ _ hx]

end StrictChunk

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkB_Inv =====
section

/-!
# Group chunk B3, part 2 (unit S4-JacChunkB): the inverse `G ⟶ G` and the unit point

* `Uv v`: the open `{x | (v, x) ∈ range Ψ}` of `X`; on it `sv v := trS (secL v) Ψ` picks `z ∈ Ω` with
  `m z = v`, `pr₂ z = x`, so `λ_{pr₁ z} = λ_v λ_x⁻¹`;
* `ginv`: glued over the charts `ι σ` restricted to `Uv v`, from `x ↦ R_{σ⁻¹} (ι λ_v⁻¹ (pr₁ z))`;
  `PtT (ginv g) = (PtT g)⁻¹` at closed points;
* `ptH h`: the closed point of `G` named by `h ∈ H`; `eta`: the `k`-point at `ptH 1`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- The open of the `x` with `(v, x)` in the range of `Ψ`. -/
noncomputable abbrev Uv (v : X) (hv : IsClosed {v}) : X.Opens :=
  secL (sX := X ↘ Spec (.of k)) v hv ⁻¹ᵁ C.Ψ.opensRange

/-- `x ↦ z ∈ Ω` with `Ψ z = (v, x)`. -/
noncomputable abbrev sv (v : X) (hv : IsClosed {v}) : (C.Uv v hv).toScheme ⟶ C.Ω.toScheme :=
  trS (secL (sX := X ↘ Spec (.of k)) v hv) C.Ψ

lemma sv_over (v : X) (hv : IsClosed {v}) :
    C.sv v hv ≫ C.Ω.ι ≫ pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k) =
      (C.Uv v hv).ι ≫ X ↘ Spec (.of k) := by
  rw [pullback.condition (f := X ↘ Spec (.of k)) (g := X ↘ Spec (.of k)), ← C.Ψ_snd_assoc, trS_Φ_assoc,
    secL_snd_assoc]

/-- At a closed point `p` of `Uv v`, `z := sv v p` is closed and `λ_{pr₁ z} = λ_v λ_p⁻¹`. -/
lemma sv_spec (v : X) (hv : IsClosed {v}) (p : (C.Uv v hv).toScheme) (hp : IsClosed {p}) :
    IsClosed {(C.sv v hv p).1} ∧
    C.lamT (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.sv v hv p).1) =
      C.lamB v hv * (C.lamT p.1)⁻¹ := by
  have hz : IsClosed {C.sv v hv p} :=
    isClosed_singleton_apply ((C.Uv v hv).ι ≫ X ↘ Spec (.of k))
      (C.Ω.ι ≫ pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k)) (C.sv v hv)
      (C.sv_over v hv) p hp
  have hz1 := C.isClosed_Ωval _ hz
  refine ⟨hz1, ?_⟩
  have hΨ : C.Ψ (C.sv v hv p) = secL (sX := X ↘ Spec (.of k)) v hv p.1 :=
    congrArg (fun φ => φ p) (trS_Φ (secL (sX := X ↘ Spec (.of k)) v hv) C.Ψ)
  have e1 : C.m (C.sv v hv p) = pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.Ψ (C.sv v hv p)) :=
    (congrArg (fun φ => φ (C.sv v hv p)) C.Ψ_fst).symm
  have hm : C.m (C.sv v hv p) = v := by rw [e1, hΨ, secL_apply_fst]
  have e2 : pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.sv v hv p).1 =
      pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.Ψ (C.sv v hv p)) :=
    (congrArg (fun φ => φ (C.sv v hv p)) C.Ψ_snd).symm
  have hs : pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.sv v hv p).1 = p.1 := by
    rw [e2, hΨ, secL_apply_snd]
  have hl := C.lamT_mul (C.sv v hv p) hz1
  rw [hs, hm, C.lamT_eq v hv] at hl
  exact eq_mul_inv_of_mul_eq hl

/-- The charts of the inverse: `Uv v` for `v` closed, inside the chart `ι σ`. -/
noncomputable abbrev invP (i : C.H × {v : X // IsClosed ({v} : Set X)}) : Scheme.{u} :=
  (C.Uv i.2.1 i.2.2).toScheme

/-- `x ↦ ι σ x` on `Uv v`. -/
noncomputable def invj (i : C.H × {v : X // IsClosed ({v} : Set X)}) : C.invP i ⟶ G C.H :=
  (C.Uv i.2.1 i.2.2).ι ≫ ι C.H i.1

instance (i : C.H × {v : X // IsClosed ({v} : Set X)}) : IsOpenImmersion (C.invj i) := by
  unfold invj; infer_instance

/-- `x ↦ R_{σ⁻¹} (ι λ_v⁻¹ (pr₁ (sv v x)))`, of value `λ_x⁻¹ σ⁻¹`. -/
noncomputable def invφ (i : C.H × {v : X // IsClosed ({v} : Set X)}) : C.invP i ⟶ G C.H :=
  C.sv i.2.1 i.2.2 ≫ C.Ω.ι ≫ pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫
    ι C.H ⟨(C.lamB i.2.1 i.2.2)⁻¹, inv_mem (C.lamB_mem_H _ _)⟩ ≫ C.Rt i.1⁻¹

lemma ginv_over (i : C.H × {v : X // IsClosed ({v} : Set X)}) :
    C.invφ i ≫ sG C.H = C.invj i ≫ sG C.H := by
  simp only [invφ, invj, Category.assoc, C.Rt_over, ι_sG]
  exact C.sv_over i.2.1 i.2.2

lemma ginv_cov (g : G C.H) (hg : IsClosed {g}) :
    ∃ i : C.H × {v : X // IsClosed ({v} : Set X)}, ∃ p : C.invP i, C.invj i p = g := by
  obtain ⟨σ, x, hx⟩ := exists_chart C.H g
  have hxc : IsClosed {x} := isClosed_of_ι C.H σ x (by rw [hx]; exact hg)
  obtain ⟨z, hzΩ, hzc, hz2⟩ := C.fib_right x hxc
  have hq : IsClosed {C.m ⟨z, hzΩ⟩} := C.isClosed_m ⟨z, hzΩ⟩ hzc
  have hΨc : IsClosed {C.Ψ ⟨z, hzΩ⟩} :=
    isClosed_singleton_apply (C.Ω.ι ≫ pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k))
      (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k)) C.Ψ
      (by rw [C.Ψ_fst_assoc, C.m_over]) ⟨z, hzΩ⟩ (C.isClosed_Ω ⟨z, hzΩ⟩ hzc)
  have f1 : pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.Ψ ⟨z, hzΩ⟩) = C.m ⟨z, hzΩ⟩ :=
    congrArg (fun φ => φ ⟨z, hzΩ⟩) C.Ψ_fst
  have f2 : pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.Ψ ⟨z, hzΩ⟩) =
      pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) z :=
    congrArg (fun φ => φ ⟨z, hzΩ⟩) C.Ψ_snd
  have hsec : secL (sX := X ↘ Spec (.of k)) (C.m ⟨z, hzΩ⟩) hq x = C.Ψ ⟨z, hzΩ⟩ :=
    closedPoint_pullback_ext (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) _ _ (secL_isClosed _ hq x hxc) hΨc
      ((secL_apply_fst _ hq x).trans f1.symm) ((secL_apply_snd _ hq x).trans (hz2.symm.trans f2.symm))
  have hmem : x ∈ C.Uv (C.m ⟨z, hzΩ⟩) hq :=
    (Scheme.Hom.mem_preimage _).2 (Scheme.Hom.mem_opensRange.2 ⟨⟨z, hzΩ⟩, hsec.symm⟩)
  exact ⟨(σ, ⟨_, hq⟩), ⟨x, hmem⟩, hx⟩

/-- The value of a chart of the inverse: `PtT (invφ i p) = (PtT (invj i p))⁻¹`. -/
lemma ginv_val (i : C.H × {v : X // IsClosed ({v} : Set X)}) (p : C.invP i) (hp : IsClosed {p}) :
    IsClosed {C.invφ i p} ∧ C.PtT (C.invφ i p) = (C.PtT (C.invj i p))⁻¹ := by
  obtain ⟨σ, v, hv⟩ := i
  have hq : IsClosed {p.1} := isClosed_val (k := k) _ p hp
  obtain ⟨hz, hl⟩ := C.sv_spec v hv p hp
  have hw := isClosed_fst _ hz
  let τ : C.H := ⟨(C.lamB v hv)⁻¹, inv_mem (C.lamB_mem_H v hv)⟩
  have hι := isClosed_ι C.H τ _ hw
  refine ⟨?_, ?_⟩
  · show IsClosed {C.Rt σ⁻¹ (ι C.H τ (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.sv v hv p).1))}
    exact isClosed_singleton_apply (sG C.H) (sG C.H) _ (C.Rt_over _) _ hι
  · show C.PtT (C.Rt σ⁻¹ (ι C.H τ (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.sv v hv p).1))) =
      (C.PtT (ι C.H σ p.1))⁻¹
    rw [C.PtT_Rt _ _ hι, C.PtT_ι τ _ hw, C.PtT_ι σ _ hq, hl, Subgroup.coe_inv, mul_inv_rev]
    show (C.lamB v hv)⁻¹ * (C.lamB v hv * (C.lamT p.1)⁻¹) * (σ : Bir k X)⁻¹ = (C.lamT p.1)⁻¹ * (σ : Bir k X)⁻¹
    rw [inv_mul_cancel_left]

lemma ginv_comp (i i' : C.H × {v : X // IsClosed ({v} : Set X)}) (p : C.invP i) (p' : C.invP i')
    (hp : IsClosed {p}) (hp' : IsClosed {p'}) (e : C.invj i p = C.invj i' p') : C.invφ i p = C.invφ i' p' := by
  obtain ⟨c, v⟩ := C.ginv_val i p hp
  obtain ⟨c', v'⟩ := C.ginv_val i' p' hp'
  exact C.PtT_inj _ _ c c' (by rw [v, v', e])

/-- The inverse `G ⟶ G`. -/
noncomputable def ginv : G C.H ⟶ G C.H :=
  glueG C.H (sG C.H) C.invP C.invj C.invφ C.ginv_cov C.ginv_over C.ginv_comp

lemma ginv_over' : C.ginv ≫ sG C.H = sG C.H :=
  glueG_over C.H (sG C.H) C.invP C.invj C.invφ C.ginv_cov C.ginv_over C.ginv_comp

/-- The value of the inverse at a closed point: `PtT (ginv g) = (PtT g)⁻¹`. -/
theorem PtT_ginv (g : G C.H) (hg : IsClosed {g}) : C.PtT (C.ginv g) = (C.PtT g)⁻¹ := by
  obtain ⟨i, p, rfl⟩ := C.ginv_cov g hg
  have hp : IsClosed {p} := isClosed_of_inj _ (C.invj i).continuous (C.invj i).isOpenEmbedding.injective p hg
  have e : C.ginv (C.invj i p) = C.invφ i p :=
    glueG_apply C.H (sG C.H) C.invP C.invj C.invφ C.ginv_cov C.ginv_over C.ginv_comp i p
  rw [e]
  exact (C.ginv_val i p hp).2

/-- The closed point of `G` named by `h ∈ H`. -/
noncomputable def ptH (h : C.H) : G C.H := (C.PtEquiv.symm h).1

lemma isClosed_ptH (h : C.H) : IsClosed {C.ptH h} := (C.PtEquiv.symm h).2

lemma PtT_ptH (h : C.H) : C.PtT (C.ptH h) = h := by
  rw [C.PtT_eq _ (C.isClosed_ptH h)]
  exact congrArg Subtype.val (C.PtEquiv.apply_symm_apply h)

/-- The unit `k`-point of `G`. -/
noncomputable def eta : Spec (.of k) ⟶ G C.H := pointOfClosedPoint (sG C.H) (C.ptH 1) (C.isClosed_ptH 1)

lemma eta_over : C.eta ≫ sG C.H = 𝟙 _ := pointOfClosedPoint_comp (sG C.H) (C.ptH 1) (C.isClosed_ptH 1)

lemma eta_apply (s : Spec (.of k)) : C.eta s = C.ptH 1 :=
  pointOfClosedPoint_apply (sG C.H) (C.ptH 1) (C.isClosed_ptH 1) s

lemma PtT_eta (s : Spec (.of k)) : C.PtT (C.eta s) = 1 := by
  rw [C.eta_apply, C.PtT_ptH, Subgroup.coe_one]

end StrictChunk

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkB_Grp =====
section

/-!
# Group chunk B4 (unit S4-JacChunkB): `G` is a group object over `Spec k`

* `GO := Over.mk (sG H)`; `kval a := PtT (a (closed point))` for a `k`-point `a : 𝟙_ ⟶ GO`;
* `hom_ext_kpt`: maps `B ⟶ GO` out of a reduced `B` locally of finite type agree once they agree on `k`-points;
* `kval_mul`, `kval_inv`, `kval_one'`: the values of `μ`, `ginv`, `η` on `k`-points;
* `grpObj`: `GrpObj GO` with `one := η`, `mul := μ`, `inv := ginv`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology MonoidalCategory CartesianMonoidalCategory

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

lemma isClosed_specPt (s : Spec (.of k)) : IsClosed ({s} : Set (Spec (.of k))) := by
  rw [show ({s} : Set (Spec (.of k))) = Set.univ from Set.eq_univ_of_forall fun x => Subsingleton.elim x s]
  exact isClosed_univ

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- `G` as an object over `Spec k`. -/
noncomputable abbrev GO : Over (Spec (.of k)) := Over.mk (sG C.H)

/-- The value in `H` of a `k`-point of `G`. -/
noncomputable def kval (a : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO) : Bir k X :=
  C.PtT (a.left (IsLocalRing.closedPoint k))

lemma isClosed_kpt (a : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO) : IsClosed {a.left (IsLocalRing.closedPoint k)} :=
  isClosed_singleton_apply (𝟙 (Spec (.of k))) (sG C.H) a.left (Over.w a) _ (isClosed_specPt _)

lemma kpt_ext (a b : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO) (h : C.kval a = C.kval b) : a = b :=
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq (sG C.H) (Over.w a) (Over.w b)
    (C.PtT_inj _ _ (C.isClosed_kpt a) (C.isClosed_kpt b) h))

/-- Maps out of a reduced `B` locally of finite type over `k` are determined on `k`-points. -/
lemma hom_ext_kpt {B : Over (Spec (.of k))} (hB : IsReduced B.left) (hB' : LocallyOfFiniteType B.hom)
    (f g : B ⟶ C.GO) (h : ∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ B, C.kval (p ≫ f) = C.kval (p ≫ g)) : f = g := by
  refine Over.OverMorphism.ext (C.G_ext_Pt B.hom f.left g.left (Over.w f) (Over.w g) fun t ht => ?_)
  have e := h (Over.homMk (U := 𝟙_ (Over (Spec (.of k)))) (V := B) (pointOfClosedPoint B.hom t ht)
    (pointOfClosedPoint_comp B.hom t ht))
  have e2 : ∀ φ : B ⟶ C.GO, C.kval (Over.homMk (U := 𝟙_ (Over (Spec (.of k)))) (V := B)
      (pointOfClosedPoint B.hom t ht) (pointOfClosedPoint_comp B.hom t ht) ≫ φ) = C.PtT (φ.left t) := by
    intro φ
    exact congrArg (fun x => C.PtT (φ.left x)) (pointOfClosedPoint_apply B.hom t ht _)
  rwa [e2 f, e2 g] at e

/-- The unit of `GO`. -/
noncomputable def oneO : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO := Over.homMk C.eta C.eta_over

/-- The multiplication of `GO`. -/
noncomputable def mulO : C.GO ⊗ C.GO ⟶ C.GO := Over.homMk C.mu C.mu_over'

/-- The inverse of `GO`. -/
noncomputable def invO : C.GO ⟶ C.GO := Over.homMk C.ginv C.ginv_over'

lemma kval_one' (q : 𝟙_ (Over (Spec (.of k))) ⟶ 𝟙_ (Over (Spec (.of k)))) : C.kval (q ≫ C.oneO) = 1 :=
  C.PtT_eta _

lemma kval_inv (a : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO) : C.kval (a ≫ C.invO) = (C.kval a)⁻¹ :=
  C.PtT_ginv _ (C.isClosed_kpt a)

lemma kval_mul (p : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO ⊗ C.GO) :
    C.kval (p ≫ C.mulO) = C.kval (p ≫ fst _ _) * C.kval (p ≫ snd _ _) := by
  have hs : IsClosed {p.left (IsLocalRing.closedPoint k)} :=
    isClosed_singleton_apply (𝟙 (Spec (.of k))) C.sGG p.left (Over.w p) _ (isClosed_specPt _)
  exact C.PtT_mu _ hs

lemma oneO_mul : C.oneO ▷ C.GO ≫ C.mulO = (λ_ C.GO).hom := by
  refine C.hom_ext_kpt (by show IsReduced (pullback (𝟙 _) (sG C.H)); infer_instance)
    (by show LocallyOfFiniteType (pullback.fst (𝟙 _) (sG C.H) ≫ 𝟙 _); infer_instance) _ _ fun p => ?_
  have h1 := C.kval_mul (p ≫ C.oneO ▷ C.GO)
  have h2 := C.kval_one' (p ≫ fst _ _)
  simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd] at h1 h2
  rw [h1, h2, _root_.one_mul, leftUnitor_hom]

lemma mul_oneO : C.GO ◁ C.oneO ≫ C.mulO = (ρ_ C.GO).hom := by
  refine C.hom_ext_kpt (by show IsReduced (pullback (sG C.H) (𝟙 _)); infer_instance)
    (by show LocallyOfFiniteType (pullback.fst (sG C.H) (𝟙 _) ≫ sG C.H); infer_instance) _ _ fun p => ?_
  have h1 := C.kval_mul (p ≫ C.GO ◁ C.oneO)
  have h2 := C.kval_one' (p ≫ snd _ _)
  simp only [Category.assoc, whiskerLeft_fst, whiskerLeft_snd] at h1 h2
  rw [h1, h2, _root_.mul_one, rightUnitor_hom]

lemma mulO_assoc : C.mulO ▷ C.GO ≫ C.mulO = (α_ C.GO C.GO C.GO).hom ≫ C.GO ◁ C.mulO ≫ C.mulO := by
  refine C.hom_ext_kpt
    (by show IsReduced (pullback (pullback.fst (sG C.H) (sG C.H) ≫ sG C.H) (sG C.H)); infer_instance)
    (by show LocallyOfFiniteType (pullback.fst (pullback.fst (sG C.H) (sG C.H) ≫ sG C.H) (sG C.H) ≫
      pullback.fst (sG C.H) (sG C.H) ≫ sG C.H); infer_instance) _ _ fun p => ?_
  have h1 := C.kval_mul (p ≫ C.mulO ▷ C.GO)
  have h2 := C.kval_mul (p ≫ fst _ _)
  have h3 := C.kval_mul (p ≫ (α_ C.GO C.GO C.GO).hom ≫ C.GO ◁ C.mulO)
  have h4 := C.kval_mul (p ≫ (α_ C.GO C.GO C.GO).hom ≫ snd _ _)
  simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd, whiskerLeft_fst, whiskerLeft_snd,
    associator_hom_fst, associator_hom_snd_fst, associator_hom_snd_snd] at h1 h2 h3 h4
  rw [h1, h2, h3, h4, _root_.mul_assoc]

lemma invO_left : lift C.invO (𝟙 C.GO) ≫ C.mulO = toUnit _ ≫ C.oneO := by
  refine C.hom_ext_kpt (by show IsReduced (G C.H); infer_instance)
    (by show LocallyOfFiniteType (sG C.H); infer_instance) _ _ fun p => ?_
  have h1 := C.kval_mul (p ≫ lift C.invO (𝟙 C.GO))
  have h2 := C.kval_one' (p ≫ toUnit _)
  simp only [Category.assoc, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd,
    Category.comp_id] at h1 h2
  rw [h1, h2, C.kval_inv, inv_mul_cancel]

lemma invO_right : lift (𝟙 C.GO) C.invO ≫ C.mulO = toUnit _ ≫ C.oneO := by
  refine C.hom_ext_kpt (by show IsReduced (G C.H); infer_instance)
    (by show LocallyOfFiniteType (sG C.H); infer_instance) _ _ fun p => ?_
  have h1 := C.kval_mul (p ≫ lift (𝟙 C.GO) C.invO)
  have h2 := C.kval_one' (p ≫ toUnit _)
  simp only [Category.assoc, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd,
    Category.comp_id] at h1 h2
  rw [h1, h2, C.kval_inv, mul_inv_cancel]

/-- `G` is a group scheme over `k`: `GrpObj (Over.mk (sG H))`. -/
noncomputable instance grpObj : GrpObj C.GO where
  one := C.oneO
  mul := C.mulO
  inv := C.invO
  one_mul := C.oneO_mul
  mul_one := C.mul_oneO
  mul_assoc := C.mulO_assoc
  left_inv := C.invO_left
  right_inv := C.invO_right

end StrictChunk

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkB_Smooth =====
section

/-!
# Group chunk B5, part 1 (unit S4-JacChunkB): smoothness, transitivity, the dense open `X`

* `smooth_sG`: `G` is smooth over `k` (Mathlib `smooth_of_grpObj`);
* `kptH h`: the `k`-point named by `h ∈ H`; `transitive`: right translations act transitively on `G(k)`;
* `denseRange_ι1`: the chart `ι 1 : X ⟶ G` is an open immersion with dense range;
* `mu_ι1`: on `Ω`, `μ ∘ (ι 1 × ι 1) = ι 1 ∘ m` (the group law extends the chunk law).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology MonoidalCategory CartesianMonoidalCategory

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- `G` is smooth over `k`. -/
theorem smooth_sG : Smooth (sG C.H) := by
  haveI := C.grpObj
  exact smooth_of_grpObj (sG C.H)

/-- The `k`-point of `G` named by `h ∈ H`. -/
noncomputable def kptH (h : C.H) : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO :=
  Over.homMk (pointOfClosedPoint (sG C.H) (C.ptH h) (C.isClosed_ptH h)) (pointOfClosedPoint_comp _ _ _)

lemma kval_kptH (h : C.H) : C.kval (C.kptH h) = h :=
  (congrArg C.PtT (pointOfClosedPoint_apply (sG C.H) (C.ptH h) (C.isClosed_ptH h) _)).trans (C.PtT_ptH h)

lemma kval_mem (a : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO) : C.kval a ∈ C.H := C.PtT_mem _

end StrictChunk

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkB_Sep =====
section

/-!
# Group chunk B5, part 2 (unit S4-JacChunkB): `G` is separated

* `grpDiv G : G ⊗ G ⟶ G`, `(a, b) ↦ a b⁻¹`, for a group object `G` of a cartesian monoidal category;
* `isPullback_diag_grp`: the diagonal of `G` is the pullback of the unit `η` along `grpDiv`;
* `isSeparated_sG`: `G → Spec k` is separated (its diagonal is a base change of the closed immersion `η`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

universe u

section General

variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] (G : 𝒞) [GrpObj G]

/-- `(a, b) ↦ a b⁻¹` on a group object. -/
noncomputable def grpDiv : G ⊗ G ⟶ G := lift (fst G G) (snd G G ≫ GrpObj.inv) ≫ MonObj.mul

lemma lift_grpDiv {T : 𝒞} (a b : T ⟶ G) : lift a b ≫ grpDiv G = a * b⁻¹ := by
  rw [grpDiv, ← Category.assoc, comp_lift, lift_fst, lift_snd_assoc]
  rfl

/-- The diagonal of a group object is the pullback of the unit along `grpDiv`. -/
lemma isPullback_diag_grp :
    IsPullback (lift (𝟙 G) (𝟙 G)) (toUnit G) (grpDiv G) MonObj.one := by
  have key : ∀ {T : 𝒞} (s : T ⟶ G ⊗ G) (t : T ⟶ 𝟙_ 𝒞), s ≫ grpDiv G = t ≫ MonObj.one →
      s ≫ fst G G = s ≫ snd G G := by
    intro T s t h
    have h1 : (s ≫ fst G G) * (s ≫ snd G G)⁻¹ = 1 := by
      rw [← lift_grpDiv, lift_comp_fst_snd, h, toUnit_unique t (toUnit T)]
      rfl
    exact mul_inv_eq_one.mp h1
  have w : lift (𝟙 G) (𝟙 G) ≫ grpDiv G = toUnit G ≫ MonObj.one := by
    rw [lift_grpDiv]
    exact mul_inv_cancel (𝟙 G)
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w (fun s => s.fst ≫ fst G G) (fun s => ?_)
    (fun s => toUnit_unique _ _) (fun s m h₁ _ => ?_)⟩⟩
  · refine hom_ext _ _ (by simp) ?_
    simpa using key s.fst s.snd s.condition
  · rw [← h₁]
    simp

end General

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- `G` is separated over `k`: its diagonal is the base change of the unit section (a closed immersion) along
`(a, b) ↦ a b⁻¹`. -/
theorem isSeparated_sG : IsSeparated (sG C.H) := by
  letI := C.grpObj
  have hP := (isPullback_diag_grp C.GO).map (Over.forget (Spec (.of k)))
  have hη : IsClosedImmersion ((Over.forget (Spec (.of k))).map (MonObj.one : 𝟙_ _ ⟶ C.GO)) :=
    inferInstanceAs (IsClosedImmersion (MonObj.one : 𝟙_ _ ⟶ C.GO).left)
  have hΔ : IsClosedImmersion ((Over.forget (Spec (.of k))).map (lift (𝟙 C.GO) (𝟙 C.GO))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) hP.flip hη
  exact ⟨hΔ⟩

end StrictChunk

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkB_Uniq =====
section

/-!
# Group chunk B6, part 1 (unit S4-JacChunkB): uniqueness of maps out of `G`

* `Y_ext`: `k`-maps from a reduced lft `k`-scheme to a separated lft `k`-scheme agreeing on closed points agree;
* `glueY`: pointwise gluing of `k`-maps into a separated lft `k`-scheme `Y` (the `glueG` of B0 for any target);
* `hom_ext_ι1`: `k`-maps from `G` to a separated lft `k`-scheme are determined on the dense open `ι 1 : X ⟶ G`;
* `iso_ext_ι1`, `eq_id_of_ι1`: an isomorphism out of `G` is unique given its restriction to `X`, and a `k`-endomorphism
  of `G` fixing `X` is the identity ("unique up to unique isomorphism").
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

section GlueY

variable {T Y : Scheme.{u}} [IsReduced T] (sT : T ⟶ Spec (.of k)) [LocallyOfFiniteType sT]
  (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY]

/-- `k`-maps from a reduced lft `k`-scheme to a separated lft `k`-scheme agreeing on closed points agree. -/
lemma Y_ext (f g : T ⟶ Y) (hf : f ≫ sY = sT) (hg : g ≫ sY = sT) (h : ∀ t, IsClosed {t} → f t = g t) :
    f = g := by
  haveI : LocallyOfFiniteType (f ≫ sY) := by rw [hf]; infer_instance
  exact ext_of_apply_eq sY Set.univ isOpen_univ.isLocallyClosed dense_univ (fun t _ ht => h t ht)
    (hf.trans hg.symm)

variable {J : Type u} (P : J → Scheme.{u}) (j : ∀ i, P i ⟶ T) [∀ i, IsOpenImmersion (j i)]
  (φ : ∀ i, P i ⟶ Y) (hcov : ∀ t, IsClosed {t} → ∃ i, ∃ p : P i, j i p = t)
  (hφ : ∀ i, φ i ≫ sY = j i ≫ sT)
  (hcomp : ∀ i i' (p : P i) (p' : P i'), IsClosed {p} → IsClosed {p'} → j i p = j i' p' → φ i p = φ i' p')

include hφ hcomp in
lemma glueY_compat (a b : J) :
    pullback.fst (j a) (j b) ≫ φ a = pullback.snd (j a) (j b) ≫ φ b := by
  haveI : IsReduced (pullback (j a) (j b)) := isReduced_of_isOpenImmersion (pullback.fst (j a) (j b) ≫ j a)
  refine Y_ext (pullback.fst (j a) (j b) ≫ j a ≫ sT) sY _ _ ?_ ?_ ?_
  · rw [Category.assoc, hφ]
  · rw [Category.assoc, hφ, pullback.condition_assoc]
  · intro r hr
    have h1 : IsClosed {pullback.fst (j a) (j b) r} :=
      isClosed_singleton_apply (pullback.fst (j a) (j b) ≫ j a ≫ sT) (j a ≫ sT) _ rfl r hr
    have h2 : IsClosed {pullback.snd (j a) (j b) r} :=
      isClosed_singleton_apply (pullback.fst (j a) (j b) ≫ j a ≫ sT) (j b ≫ sT) _
        (by rw [← pullback.condition_assoc]) r hr
    have e : j a (pullback.fst (j a) (j b) r) = j b (pullback.snd (j a) (j b) r) :=
      congrArg (fun ψ => ψ r) (pullback.condition (f := j a) (g := j b))
    exact hcomp a b _ _ h1 h2 e

/-- Pointwise gluing of `k`-morphisms into a separated lft `k`-scheme `Y`. -/
noncomputable def glueY : T ⟶ Y :=
  (coverOfClosed sT P j hcov).glueMorphisms φ (glueY_compat sT sY P j φ hφ hcomp)

@[reassoc]
lemma glueY_fac (i : J) : j i ≫ glueY sT sY P j φ hcov hφ hcomp = φ i :=
  Scheme.Cover.ι_glueMorphisms (coverOfClosed sT P j hcov) φ _ i

lemma glueY_over : glueY sT sY P j φ hcov hφ hcomp ≫ sY = sT :=
  Scheme.Cover.hom_ext (coverOfClosed sT P j hcov) _ _ fun (i : J) =>
    (glueY_fac_assoc sT sY P j φ hcov hφ hcomp i sY).trans (hφ i)

lemma glueY_apply (i : J) (p : P i) : glueY sT sY P j φ hcov hφ hcomp (j i p) = φ i p :=
  congrArg (fun ψ => ψ p) (glueY_fac sT sY P j φ hcov hφ hcomp i)

end GlueY

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

end StrictChunk

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacChunkB_GPt =====
section

/-!
# Group chunk B6, part 2a (unit S4-JacChunkB): `k`-points and translations of a group scheme `G'` over `k`

For `G' : Over (Spec k)` locally of finite type (`k` algebraically closed), `k`-points `𝟙_ ⟶ G'` form a group when
`G'` is a group object (`open MonObj`). This file gives:
* `ev a`: the closed point named by a `k`-point; `ev_inj`, `kp` (the `k`-point at a closed point), `ev_kp`, `kp_ev`;
* `ev_mul`: the product of `k`-points is `μ` at the closed point of `G' ×_k G'` with the two coordinates;
* `tr θ = (toUnit ≫ θ) * 𝟙 : G' ⟶ G'` (left translation), `kp_tr : a ≫ tr θ = θ * a`, `tr_tr`, `tr_one`, `trIso`,
  `tr_ev : (tr θ).left (ev a) = ev (θ * a)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology MonoidalCategory CartesianMonoidalCategory MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace GrpPt

variable (G' : Over (Spec (.of k))) [LocallyOfFiniteType G'.hom]

/-- The closed point named by a `k`-point. -/
noncomputable def ev (a : 𝟙_ (Over (Spec (.of k))) ⟶ G') : G'.left := a.left (IsLocalRing.closedPoint k)

lemma isClosed_ev (a : 𝟙_ (Over (Spec (.of k))) ⟶ G') : IsClosed {ev G' a} :=
  isClosed_singleton_apply (𝟙 (Spec (.of k))) G'.hom a.left (Over.w a) _ (isClosed_specPt _)

lemma ev_inj {a b : 𝟙_ (Over (Spec (.of k))) ⟶ G'} (h : ev G' a = ev G' b) : a = b :=
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq G'.hom (Over.w a) (Over.w b) h)

lemma ev_comp {B : Over (Spec (.of k))} (a : 𝟙_ (Over (Spec (.of k))) ⟶ B) (f : B ⟶ G') :
    ev G' (a ≫ f) = f.left (a.left (IsLocalRing.closedPoint k)) := rfl

variable [GrpObj G']

end GrpPt

end RamanujanPetersson.JacChunk


end

-- ===== S4.Def_RP_JacComplete_Comm =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Comm` (L22, abstract half)

`isCommMonObj_of_comm`: for any strict group chunk `C` on a geometrically reduced, integral, separated, lft `k`-scheme
(`k` algebraically closed), if the group `H` of the chunk is commutative then the group scheme `G C.H` is commutative.
`isCommMonObj_Jac_of_comm`: the same for `Jac K F`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Abstract

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- A strict group chunk with commutative `H` gives a commutative group scheme. -/
theorem isCommMonObj_of_comm (hc : ∀ a b : C.H, a * b = b * a) :
    letI := C.grpObj; IsCommMonObj C.GO := by
  letI := C.grpObj
  refine ⟨?_⟩
  refine C.hom_ext_kpt
    (by show IsReduced (pullback (sG C.H) (sG C.H)); infer_instance)
    (by show LocallyOfFiniteType (pullback.fst (sG C.H) (sG C.H) ≫ sG C.H); infer_instance) _ _ fun p => ?_
  have h1 := C.kval_mul (p ≫ (β_ C.GO C.GO).hom)
  have h2 := C.kval_mul p
  have e := congrArg Subtype.val (hc ⟨C.kval (p ≫ snd _ _), C.kval_mem _⟩ ⟨C.kval (p ≫ fst _ _), C.kval_mem _⟩)
  simp only [Subgroup.coe_mul] at e
  change C.kval ((p ≫ (β_ C.GO C.GO).hom) ≫ C.mulO) = C.kval (p ≫ C.mulO)
  rw [h1, h2, ← e, Category.assoc, Category.assoc, CartesianMonoidalCategory.braiding_hom_fst,
    CartesianMonoidalCategory.braiding_hom_snd]

end Abstract

section Jac

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

end Jac

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_CommH =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `CommH` (L22: the chunk group is commutative)

* `ChunkComm C`: the law of a strict group chunk is commutative at closed points, `m(a,b) = m(b,a)`.
* `lamB_eq_rhoB`, `H_comm_of_chunkComm`: then `λ_a = ρ_a` for every closed `a`, so the generators of `H` are central
  (every element of `H` commutes with every right translation, `H_comm_rhoB`) and `H` is commutative.
* `AffComm`, `chunkComm_toStrict`: commutativity of algebraic chunk data (`AffChunk`) at `K`-points passes to the
  strict chunk `toStrict`; `PreComm`, `affComm_toAff`: and from a `PreChunk` to its shrunken `toAff`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Strict

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The law of a strict group chunk is commutative at closed points: `m(a,b) = m(b,a)`. -/
def ChunkComm {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (C : StrictChunk sX) : Prop :=
  ∀ z z' : C.Ω, IsClosed {z.1} → IsClosed {z'.1} →
    pullback.fst sX sX z'.1 = pullback.snd sX sX z.1 → pullback.snd sX sX z'.1 = pullback.fst sX sX z.1 →
    C.m z = C.m z'

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IrreducibleSpace X]

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- For a commutative law, the left and right translations by a closed point agree. -/
theorem lamB_eq_rhoB (hc : ChunkComm C) (a : X) (ha : IsClosed {a}) : C.lamB a ha = C.rhoB a ha := by
  have := pi_isOver _ (C.lam_isOver a ha)
  have := pi_isOver _ (C.rho_isOver a ha)
  refine Units.ext (Subtype.ext ?_)
  change (C.lam a ha).toPartialMap.toRationalMap = (C.rho a ha).toPartialMap.toRationalMap
  refine toRationalMap_eq_of_apply (k := k) fun x hf hg hx => ?_
  rw [C.lam_apply a ha x hf, C.rho_apply a ha x hg]
  exact hc ⟨secL a ha x, hf⟩ ⟨secR a ha x, hg⟩ (secL_isClosed a ha x hx) (secR_isClosed a ha x hx)
    ((secR_apply_fst (sX := X ↘ Spec (.of k)) a ha x).trans (secL_apply_snd a ha x).symm)
    ((secR_apply_snd (sX := X ↘ Spec (.of k)) a ha x).trans (secL_apply_fst a ha x).symm)

/-- **The chunk group of a commutative law is commutative.** -/
theorem H_comm_of_chunkComm (hc : ChunkComm C) (σ τ : C.H) : σ * τ = τ * σ := by
  have hle : C.H ≤ Subgroup.centralizer (C.H : Set (Bir k X)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun σ hσ => ?_
    show σ * C.lamB a.1 a.2 = C.lamB a.1 a.2 * σ
    rw [lamB_eq_rhoB C hc a.1 a.2]
    exact C.H_comm_rhoB σ hσ a.1 a.2
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hle τ.2)) σ σ.2)

end Strict

section Aff

variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R]

/-- Commutativity of algebraic chunk data at `K`-points. -/
def AffComm (C : AffChunk K R) : Prop :=
  ∀ x x' : Localization.Away C.ω →ₐ[K] K, pL x' = pR x → pR x' = pL x → x.comp C.μ = x'.comp C.μ

variable [IsAlgClosed K] [IsDomain R] [Algebra.FiniteType K R]

theorem chunkComm_toStrict (C : AffChunk K R) (hc : AffComm C) : ChunkComm C.toStrict := by
  show ∀ z z' : (jAway C.ω).opensRange, IsClosed {z.1} → IsClosed {z'.1} →
    pullback.fst (sR K R) (sR K R) z'.1 = pullback.snd (sR K R) (sR K R) z.1 →
    pullback.snd (sR K R) (sR K R) z'.1 = pullback.fst (sR K R) (sR K R) z.1 →
    ((jAway C.ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (C.μ : R →+* _))) z =
      ((jAway C.ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (C.μ : R →+* _))) z'
  intro z z' h h' e1 e2
  obtain ⟨x, hz, hi⟩ := exists_pt_jAway C.ω z h
  obtain ⟨x', hz', hi'⟩ := exists_pt_jAway C.ω z' h'
  rw [hz', hz, fst_jAway, snd_jAway] at e1
  rw [hz', hz, snd_jAway, fst_jAway] at e2
  exact (mS_apply C.ω C.μ z x hi).trans ((congrArg kpt (hc x x' (kpt_injective e1) (kpt_injective e2))).trans
    (mS_apply C.ω C.μ z' x' hi').symm)

end Aff

section Pre

variable {K : Type u} [Field K] {S : Type u} [CommRing S] [Algebra K S]

/-- Commutativity of a `PreChunk` law at `K`-points. -/
def PreComm (P : PreChunk K S) : Prop :=
  ∀ x x' : Localization.Away P.ω →ₐ[K] K, pL x' = pR x → pR x' = pL x → x.comp P.μ = x'.comp P.μ

variable [IsAlgClosed K] [Algebra.FiniteType K S] [IsDomain S]

theorem affComm_toAff (P : PreChunk K S) (hc : PreComm P) : AffComm P.toAff := by
  show ∀ x x' : Localization.Away (extW P.u0 (P.t1 * P.t2) P.μ) →ₐ[K] K, pL x' = pR x → pR x' = pL x →
    x.comp (extN P.u0 (P.t1 * P.t2) P.μ) = x'.comp (extN P.u0 (P.t1 * P.t2) P.μ)
  intro x x' e1 e2
  refine away_algHom_ext ?_
  rw [← extK_nu P.u0 (P.t1 * P.t2) P.μ x, ← extK_nu P.u0 (P.t1 * P.t2) P.μ x']
  refine hc (x.comp (extK P.u0 (P.t1 * P.t2) P.μ)) (x'.comp (extK P.u0 (P.t1 * P.t2) P.μ)) ?_ ?_
  · rw [extK_pL, extK_pR, e1]
  · rw [extK_pR, extK_pL, e2]

end Pre

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_PicH =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicH` (L20, abstract half)

For a strict group chunk `C` with commutative group `H` and a function `ψ : X → A` to an additive group that is
additive for the chunk law at closed points (`ChunkAdd C ψ`):
* `lam_add`: `ψ (λ_a z) = ψ a + ψ z`; `add_eq_of_lamB`: `λ_a λ_b = λ_c λ_d → ψ a + ψ b = ψ c + ψ d`;
* `Phi ψ σ = ψ y - ψ x` for any closed `x`, `y` with `σ x = y` (`Phi_spec`); `Phi_mul`, `Phi_lamB`;
* `PhiHom : C.H →* Multiplicative A`; `PhiHom_injective` when `ψ` is rigid at the outputs of the law.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section PicH

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

/-- `ψ` is additive for the law of the chunk at closed points: `ψ (m(a,b)) = ψ a + ψ b`. -/
def ChunkAdd (C : StrictChunk (X ↘ Spec (.of k))) {A : Type*} [AddCommGroup A] (ψ : X → A) : Prop :=
  ∀ z : C.Ω, IsClosed {z.1} → ψ (C.m z) =
    ψ (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) z.1) +
      ψ (pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) z.1)

lemma exists_closed_in (k : Type u) [Field k] [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (U : X.Opens) (hU : (U : Set X).Nonempty) : ∃ x, x ∈ U ∧ IsClosed ({x} : Set X) := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  obtain ⟨x, hx, -, hc⟩ := exists_closed_inter U U hU hU
  exact ⟨x, hx, hc⟩

lemma exists_takes (σ : Bir k X) : ∃ x y : X, IsClosed {x} ∧ IsClosed {y} ∧ Takes σ x y := by
  obtain ⟨x, hx, hc⟩ := exists_closed_in k (rep σ).domain (rep σ).dense_domain.nonempty
  exact ⟨x, _, hc, isClosed_hom_apply (k := k) (rep σ) x hx hc, takes_self σ x hx⟩

/-- The class of `σ`: `ψ (σ x) - ψ x` at a chosen closed point. -/
noncomputable def Phi {A : Type*} [AddCommGroup A] (ψ : X → A) (σ : Bir k X) : A :=
  ψ (exists_takes σ).choose_spec.choose - ψ (exists_takes σ).choose

variable {C : StrictChunk (X ↘ Spec (.of k))} {A : Type*} [AddCommGroup A] {ψ : X → A}

lemma lam_add (hψ : ChunkAdd C ψ) (a : X) (ha : IsClosed {a}) (z : X)
    (hz : z ∈ (C.lam a ha).toPartialMap.domain) (hzc : IsClosed {z}) :
    ψ ((C.lam a ha).toPartialMap.hom ⟨z, hz⟩) = ψ a + ψ z := by
  rw [C.lam_apply a ha z hz, hψ ⟨secL a ha z, hz⟩ (secL_isClosed a ha z hzc),
    secL_apply_fst (sX := X ↘ Spec (.of k)) a ha z, secL_apply_snd (sX := X ↘ Spec (.of k)) a ha z]

lemma add_eq_of_lamB (hψ : ChunkAdd C ψ) (a : X) (ha : IsClosed {a}) (b : X) (hb : IsClosed {b})
    (c : X) (hc : IsClosed {c}) (d : X) (hd : IsClosed {d})
    (h : C.lamB a ha * C.lamB b hb = C.lamB c hc * C.lamB d hd) : ψ a + ψ b = ψ c + ψ d := by
  haveI := pi_isDominant (C.lam b hb)
  haveI := pi_isDominant (C.lam d hd)
  haveI := pi_isOver _ (C.lam_isOver b hb)
  haveI := pi_isOver _ (C.lam_isOver d hd)
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  obtain ⟨z, h1, h2, hz⟩ := exists_closed_inter
    ((C.lam b hb).toPartialMap.comp (C.lam a ha).toPartialMap).domain
    ((C.lam d hd).toPartialMap.comp (C.lam c hc).toPartialMap).domain
    ((C.lam b hb).toPartialMap.comp (C.lam a ha).toPartialMap).dense_domain.nonempty
    ((C.lam d hd).toPartialMap.comp (C.lam c hc).toPartialMap).dense_domain.nonempty
  obtain ⟨hz1, hz2⟩ := (mem_comp_domain _ _).1 h1
  obtain ⟨hz3, hz4⟩ := (mem_comp_domain _ _).1 h2
  have hu := isClosed_hom_apply (k := k) (C.lam b hb).toPartialMap z hz1 hz
  have hv := isClosed_hom_apply (k := k) (C.lam d hd).toPartialMap z hz3 hz
  have t1 := Takes.comp (C.lamB_takes b hb z hz1) (C.lamB_takes a ha _ hz2) rfl
  have t2 := Takes.comp (C.lamB_takes d hd z hz3) (C.lamB_takes c hc _ hz4) rfl
  have e2 := congrArg ψ (Takes.unique t1 (t2.of_eq h.symm))
  rw [lam_add hψ a ha _ hz2 hu, lam_add hψ b hb z hz1 hz, lam_add hψ c hc _ hz4 hv,
    lam_add hψ d hd z hz3 hz, ← add_assoc, ← add_assoc] at e2
  exact add_right_cancel e2

lemma takes_sub_eq (hψ : ChunkAdd C ψ) (hcomm : ∀ σ τ : C.H, σ * τ = τ * σ) (σ : Bir k X) (hσ : σ ∈ C.H)
    {x y x' y' : X} (hx : IsClosed {x}) (hy : IsClosed {y}) (hx' : IsClosed {x'}) (hy' : IsClosed {y'})
    (h : Takes σ x y) (h' : Takes σ x' y') : ψ y - ψ x = ψ y' - ψ x' := by
  have e := C.RC_fwd σ hσ x hx y hy h
  have e' := C.RC_fwd σ hσ x' hx' y' hy' h'
  have hc : C.lamB x hx * C.lamB x' hx' = C.lamB x' hx' * C.lamB x hx :=
    congrArg Subtype.val (hcomm ⟨_, C.lamB_mem_H x hx⟩ ⟨_, C.lamB_mem_H x' hx'⟩)
  have key : C.lamB y hy * C.lamB x' hx' = C.lamB y' hy' * C.lamB x hx := by
    rw [← e, ← e', mul_assoc, mul_assoc, hc]
  rw [sub_eq_sub_iff_add_eq_add]
  exact add_eq_of_lamB hψ y hy x' hx' y' hy' x hx key

lemma Phi_spec (hψ : ChunkAdd C ψ) (hcomm : ∀ σ τ : C.H, σ * τ = τ * σ) (σ : Bir k X) (hσ : σ ∈ C.H)
    {x y : X} (hx : IsClosed {x}) (hy : IsClosed {y}) (h : Takes σ x y) : Phi ψ σ = ψ y - ψ x := by
  obtain ⟨h1, h2, h3⟩ := (exists_takes σ).choose_spec.choose_spec
  exact takes_sub_eq hψ hcomm σ hσ h1 h2 hx hy h3 h

lemma Phi_mul (hψ : ChunkAdd C ψ) (hcomm : ∀ σ τ : C.H, σ * τ = τ * σ) (σ τ : Bir k X) (hσ : σ ∈ C.H)
    (hτ : τ ∈ C.H) : Phi ψ (σ * τ) = Phi ψ σ + Phi ψ τ := by
  obtain ⟨x, hx, hxc⟩ := exists_closed_in k ((rep τ).comp (rep σ)).domain
    ((rep τ).comp (rep σ)).dense_domain.nonempty
  obtain ⟨h1, h2⟩ := (mem_comp_domain _ _).1 hx
  have hv := isClosed_hom_apply (k := k) (rep τ) x h1 hxc
  have hw := isClosed_hom_apply (k := k) (rep σ) _ h2 hv
  have t1 := takes_self τ x h1
  have t2 := takes_self σ _ h2
  rw [Phi_spec hψ hcomm (σ * τ) (mul_mem hσ hτ) hxc hw (Takes.comp t1 t2 rfl),
    Phi_spec hψ hcomm σ hσ hv hw t2, Phi_spec hψ hcomm τ hτ hxc hv t1]
  abel

lemma Phi_lamB (hψ : ChunkAdd C ψ) (hcomm : ∀ σ τ : C.H, σ * τ = τ * σ) (a : X) (ha : IsClosed {a}) :
    Phi ψ (C.lamB a ha) = ψ a := by
  haveI := pi_isOver _ (C.lam_isOver a ha)
  obtain ⟨z, hz, hzc⟩ := exists_closed_in k (C.lam a ha).toPartialMap.domain (C.lam_ne a ha)
  have hw := isClosed_hom_apply (k := k) (C.lam a ha).toPartialMap z hz hzc
  rw [Phi_spec hψ hcomm _ (C.lamB_mem_H a ha) hzc hw (C.lamB_takes a ha z hz), lam_add hψ a ha z hz hzc,
    add_sub_cancel_right]

/-- `ψ` is rigid at the outputs of the law: a closed point with the same value is that output. -/
def ChunkRigid (C : StrictChunk (X ↘ Spec (.of k))) (ψ : X → A) : Prop :=
  ∀ (a : X) (ha : IsClosed {a}) (z : X) (hz : z ∈ (C.lam a ha).toPartialMap.domain), IsClosed {z} →
    ∀ y : X, IsClosed {y} → ψ y = ψ ((C.lam a ha).toPartialMap.hom ⟨z, hz⟩) →
      y = (C.lam a ha).toPartialMap.hom ⟨z, hz⟩

lemma lamB_congr (C : StrictChunk (X ↘ Spec (.of k))) {u v : X} (hu : IsClosed {u}) (hv : IsClosed {v})
    (e : u = v) : C.lamB u hu = C.lamB v hv := by
  subst e; rfl

lemma eq_one_of_Phi (hψ : ChunkAdd C ψ) (hcomm : ∀ σ τ : C.H, σ * τ = τ * σ) (hrig : ChunkRigid C ψ)
    (σ : Bir k X) (hσ : σ ∈ C.H) (h0 : Phi ψ σ = 0) : σ = 1 := by
  obtain ⟨a, ha⟩ := exists_closedPoint (X := X) k
  haveI := pi_isDominant (C.lam a ha)
  haveI := pi_isOver _ (C.lam_isOver a ha)
  obtain ⟨z, hz, hzc⟩ := exists_closed_in k ((C.lam a ha).toPartialMap.comp (rep σ)).domain
    ((C.lam a ha).toPartialMap.comp (rep σ)).dense_domain.nonempty
  obtain ⟨h1, h2⟩ := (mem_comp_domain _ _).1 hz
  have hx := isClosed_hom_apply (k := k) (C.lam a ha).toPartialMap z h1 hzc
  have hy := isClosed_hom_apply (k := k) (rep σ) _ h2 hx
  have t := takes_self σ _ h2
  rw [Phi_spec hψ hcomm σ hσ hx hy t, sub_eq_zero] at h0
  have e := hrig a ha z h1 hzc _ hy h0
  have e1 := C.RC_fwd σ hσ _ hx _ hy t
  exact mul_right_cancel (e1.trans ((lamB_congr C hy hx e).trans (one_mul _).symm))

/-- **The class homomorphism** `H → A`, `σ ↦ ψ (σ x) - ψ x`. -/
noncomputable def PhiHom (hψ : ChunkAdd C ψ) (hcomm : ∀ σ τ : C.H, σ * τ = τ * σ) : C.H →* Multiplicative A :=
  MonoidHom.mk' (fun σ => Multiplicative.ofAdd (Phi ψ σ.1)) fun σ τ => by
    show Multiplicative.ofAdd (Phi ψ (σ.1 * τ.1)) = Multiplicative.ofAdd (Phi ψ σ.1) * Multiplicative.ofAdd (Phi ψ τ.1)
    rw [Phi_mul hψ hcomm _ _ σ.2 τ.2, ofAdd_add]

lemma PhiHom_apply (hψ : ChunkAdd C ψ) (hcomm : ∀ σ τ : C.H, σ * τ = τ * σ) (σ : C.H) :
    PhiHom hψ hcomm σ = Multiplicative.ofAdd (Phi ψ σ.1) := rfl

theorem PhiHom_injective (hψ : ChunkAdd C ψ) (hcomm : ∀ σ τ : C.H, σ * τ = τ * σ) (hrig : ChunkRigid C ψ) :
    Function.Injective (PhiHom hψ hcomm) := by
  refine (injective_iff_map_eq_one _).2 fun σ h => Subtype.ext (eq_one_of_Phi hψ hcomm hrig σ.1 σ.2 ?_)
  rw [PhiHom_apply] at h
  exact ofAdd_eq_one.1 h

end PicH

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_PicT =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicT` (L20: transports of additivity and rigidity)

* `chunkRigid_of_m`; `psiS ψ` reads a function on `K`-points of `R` on `Spec R` (`psiS_kpt`);
* `AffAdd`, `AffRigid` pass to `toStrict` (`chunkAdd_toStrict`, `rigid_toStrict`); `PreAdd`, `PreRigid` pass to
  the shrunken `toAff` (`affAdd_toAff`, `affRigid_toAff`, with `psiA`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Strict

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

/-- Rigidity at the outputs of the law gives `ChunkRigid`. -/
theorem chunkRigid_of_m (C : StrictChunk (X ↘ Spec (.of k))) {A : Type*} [AddCommGroup A] {ψ : X → A}
    (h : ∀ w : C.Ω, IsClosed {w.1} → ∀ y : X, IsClosed {y} → ψ y = ψ (C.m w) → y = C.m w) :
    ChunkRigid C ψ := by
  intro a ha z hz hzc y hy e
  rw [C.lam_apply a ha z hz] at e ⊢
  exact h ⟨secL a ha z, hz⟩ (secL_isClosed a ha z hzc) y hy e

end Strict

section Aff

variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R] {A : Type*} [AddCommGroup A]

/-- Additivity of a function on `K`-points for algebraic chunk data. -/
def AffAdd (C : AffChunk K R) (ψ : (R →ₐ[K] K) → A) : Prop :=
  ∀ x : Localization.Away C.ω →ₐ[K] K, ψ (x.comp C.μ) = ψ (pL x) + ψ (pR x)

/-- Rigidity of a function on `K`-points at the outputs of the law. -/
def AffRigid (C : AffChunk K R) (ψ : (R →ₐ[K] K) → A) : Prop :=
  ∀ (x : Localization.Away C.ω →ₐ[K] K) (y : R →ₐ[K] K), ψ y = ψ (x.comp C.μ) → y = x.comp C.μ

variable [IsAlgClosed K] [Algebra.FiniteType K R] [IsDomain R]

open Classical in
/-- A function on `K`-points read on `Spec R` (closed points are `kpt`s; `0` elsewhere). -/
noncomputable def psiS (ψ : (R →ₐ[K] K) → A) (p : Spec (.of R)) : A :=
  if h : IsClosed ({p} : Set (Spec (.of R))) then ψ (exists_kpt (K := K) p h).choose else 0

theorem psiS_kpt (ψ : (R →ₐ[K] K) → A) (y : R →ₐ[K] K) : psiS ψ (kpt y) = ψ y := by
  rw [psiS, dif_pos (isClosed_kpt y)]
  exact congrArg ψ (kpt_injective (exists_kpt (K := K) (kpt y) (isClosed_kpt y)).choose_spec)

theorem chunkAdd_toStrict (C : AffChunk K R) {ψ : (R →ₐ[K] K) → A} (hψ : AffAdd C ψ) :
    ∀ z : C.toStrict.Ω, IsClosed {z.1} → psiS ψ (C.toStrict.m z) =
      psiS ψ (pullback.fst (sR K R) (sR K R) z.1) + psiS ψ (pullback.snd (sR K R) (sR K R) z.1) := by
  show ∀ z : (jAway C.ω).opensRange, IsClosed {z.1} →
    psiS ψ (((jAway C.ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (C.μ : R →+* _))) z) =
      psiS ψ (pullback.fst (sR K R) (sR K R) z.1) + psiS ψ (pullback.snd (sR K R) (sR K R) z.1)
  intro z hz
  obtain ⟨x, hz1, hi⟩ := exists_pt_jAway C.ω z hz
  rw [mS_apply C.ω C.μ z x hi, hz1, fst_jAway, snd_jAway, psiS_kpt, psiS_kpt, psiS_kpt]
  exact hψ x

theorem rigid_toStrict (C : AffChunk K R) {ψ : (R →ₐ[K] K) → A} (hψ : AffRigid C ψ) :
    ∀ w : C.toStrict.Ω, IsClosed {w.1} → ∀ y : Spec (.of R), IsClosed {y} →
      psiS ψ y = psiS ψ (C.toStrict.m w) → y = C.toStrict.m w := by
  show ∀ w : (jAway C.ω).opensRange, IsClosed {w.1} → ∀ y : Spec (.of R), IsClosed {y} →
    psiS ψ y = psiS ψ (((jAway C.ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (C.μ : R →+* _))) w) →
      y = ((jAway C.ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (C.μ : R →+* _))) w
  intro w hw y hy e
  obtain ⟨x, -, hi⟩ := exists_pt_jAway C.ω w hw
  obtain ⟨y', rfl⟩ := exists_kpt (K := K) y hy
  rw [mS_apply C.ω C.μ w x hi, psiS_kpt, psiS_kpt] at e
  rw [mS_apply C.ω C.μ w x hi]
  exact congrArg kpt (hψ x y' e)

end Aff

section Pre

variable {K : Type u} [Field K] {S : Type u} [CommRing S] [Algebra K S] {A : Type*} [AddCommGroup A]

/-- Additivity of a function on `K`-points for a `PreChunk` law. -/
def PreAdd (P : PreChunk K S) (ψ : (S →ₐ[K] K) → A) : Prop :=
  ∀ x : Localization.Away P.ω →ₐ[K] K, ψ (x.comp P.μ) = ψ (pL x) + ψ (pR x)

/-- Rigidity at the outputs of a `PreChunk` law. -/
def PreRigid (P : PreChunk K S) (ψ : (S →ₐ[K] K) → A) : Prop :=
  ∀ (x : Localization.Away P.ω →ₐ[K] K) (y : S →ₐ[K] K), ψ y = ψ (x.comp P.μ) → y = x.comp P.μ

/-- `ψ` on `K`-points of `S[1/u0]`. -/
noncomputable def psiA (P : PreChunk K S) (ψ : (S →ₐ[K] K) → A) (y : Localization.Away P.u0 →ₐ[K] K) : A :=
  ψ (y.comp (awayι P.u0))

variable [IsAlgClosed K] [Algebra.FiniteType K S] [IsDomain S]

theorem affAdd_toAff (P : PreChunk K S) {ψ : (S →ₐ[K] K) → A} (hψ : PreAdd P ψ) :
    AffAdd P.toAff (psiA P ψ) := by
  show ∀ x : Localization.Away (extW P.u0 (P.t1 * P.t2) P.μ) →ₐ[K] K,
    ψ ((x.comp (extN P.u0 (P.t1 * P.t2) P.μ)).comp (awayι P.u0)) =
      ψ ((pL x).comp (awayι P.u0)) + ψ ((pR x).comp (awayι P.u0))
  intro x
  rw [← extK_nu P.u0 (P.t1 * P.t2) P.μ x, ← extK_pL P.u0 (P.t1 * P.t2) P.μ x,
    ← extK_pR P.u0 (P.t1 * P.t2) P.μ x]
  exact hψ _

theorem affRigid_toAff (P : PreChunk K S) {ψ : (S →ₐ[K] K) → A} (hψ : PreRigid P ψ) :
    AffRigid P.toAff (psiA P ψ) := by
  show ∀ (x : Localization.Away (extW P.u0 (P.t1 * P.t2) P.μ) →ₐ[K] K) (y : Localization.Away P.u0 →ₐ[K] K),
    ψ (y.comp (awayι P.u0)) = ψ ((x.comp (extN P.u0 (P.t1 * P.t2) P.μ)).comp (awayι P.u0)) →
      y = x.comp (extN P.u0 (P.t1 * P.t2) P.μ)
  intro x y e
  refine away_algHom_ext ?_
  rw [← extK_nu P.u0 (P.t1 * P.t2) P.μ x] at e ⊢
  exact hψ _ _ e

end Pre

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_PicK =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicK`: divisor classes over an arbitrary constant field

For a function field `F / K(x)` over an arbitrary field `K` (S4-JacRRFam's Fintype-free divisors):
* `PrincK K F`: the principal divisors; `PicK K F = Divisor ⧸ PrincK`; `clsK`; `degPicK`; `Pic0K K F := ker degPicK`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.JacComplete

section PicK

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem divK_one : (PlacesK.div (1 : F) : Places.Divisor K F) = 0 :=
  (PlacesK.div_eq_zero_iff (K := K) (F := F) one_ne_zero).2 (one_mem _)

variable {F} in
theorem divK_inv {f : F} (hf : f ≠ 0) : (PlacesK.div f⁻¹ : Places.Divisor K F) = -PlacesK.div f := by
  rw [← one_div, PlacesK.div_div one_ne_zero hf, divK_one, zero_sub]

/-- The principal divisors of `F / K`. -/
noncomputable def PrincK : AddSubgroup (Places.Divisor K F) where
  carrier := {D | ∃ f : F, f ≠ 0 ∧ (PlacesK.div f : Places.Divisor K F) = D}
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, mul_ne_zero hf hg, PlacesK.div_mul hf hg⟩
  zero_mem' := ⟨1, one_ne_zero, divK_one K F⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨f⁻¹, inv_ne_zero hf, divK_inv K hf⟩

theorem mem_PrincK {D : Places.Divisor K F} :
    D ∈ PrincK K F ↔ ∃ f : F, f ≠ 0 ∧ (PlacesK.div f : Places.Divisor K F) = D := Iff.rfl

theorem div_mem_PrincK {f : F} (hf : f ≠ 0) : (PlacesK.div f : Places.Divisor K F) ∈ PrincK K F :=
  ⟨f, hf, rfl⟩

/-- The divisor class group of `F / K`. -/
noncomputable abbrev PicK : Type _ := Places.Divisor K F ⧸ PrincK K F

/-- The class of a divisor. -/
noncomputable abbrev clsK (D : Places.Divisor K F) : PicK K F := QuotientAddGroup.mk D

theorem clsK_eq_iff {D E : Places.Divisor K F} : clsK K F D = clsK K F E ↔ -D + E ∈ PrincK K F :=
  QuotientAddGroup.eq

/-- The degree as an additive map. -/
noncomputable def degHomK : Places.Divisor K F →+ ℤ where
  toFun := Places.Divisor.deg
  map_zero' := Finsupp.sum_zero_index
  map_add' := PlacesK.Divisor.deg_add

@[simp] theorem degHomK_apply (D : Places.Divisor K F) : degHomK K F D = D.deg := rfl

/-- The degree of a divisor class. -/
noncomputable def degPicK : PicK K F →+ ℤ :=
  QuotientAddGroup.lift (PrincK K F) (degHomK K F) (by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := hx
    simpa using PlacesK.deg_div hf)

theorem degPicK_clsK (D : Places.Divisor K F) : degPicK K F (clsK K F D) = D.deg := rfl

/-- **`Pic⁰(F / K)`**: the divisor classes of degree `0`. -/
noncomputable def Pic0K : AddSubgroup (PicK K F) := (degPicK K F).ker

theorem mem_Pic0K {x : PicK K F} : x ∈ Pic0K K F ↔ degPicK K F x = 0 := AddMonoidHom.mem_ker

theorem clsK_mem_Pic0K {D : Places.Divisor K F} (h : D.deg = 0) : clsK K F D ∈ Pic0K K F :=
  (mem_Pic0K K F).2 h

end PicK

end RamanujanPetersson.JacComplete


end

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

theorem clsK_add (D E : Places.Divisor K F) : clsK K F (D + E) = clsK K F D + clsK K F E :=
  QuotientAddGroup.mk_add _ D E

theorem clsK_sub (D E : Places.Divisor K F) : clsK K F (D - E) = clsK K F D - clsK K F E :=
  QuotientAddGroup.mk_sub _ D E

variable {T : Type*} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]
  {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3)) (D2 : NuData K F (genusFK K F + r2))
  (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))

/-- The divisor `Θ = Hn3 - Hn2 - c0 + c1` of the law data. -/
noncomputable def ThetaD : Places.Divisor K F :=
  D3.Hn - D2.Hn - Zdiv (Finset.univ.image c0) + Zdiv (Finset.univ.image c1)

end Pt

section Law

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (L : LawData K F)

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

theorem placeDeg_one (v : Places.Place K F) : v.deg = 1 := by
  rcases v with P | P
  · exact deg_eq_one (K := K) P
  · exact deg_eq_one (K := K) P

theorem deg_single_one (v : Places.Place K F) :
    Places.Divisor.deg (Finsupp.single v (1 : ℤ) : Places.Divisor K F) = 1 := by
  rw [PlacesK.Divisor.deg_single, placeDeg_one]; norm_num

theorem deg_single' (v : Places.Place K F) (n : ℤ) :
    Places.Divisor.deg (Finsupp.single v n : Places.Divisor K F) = n := by
  rw [PlacesK.Divisor.deg_single, placeDeg_one]; norm_num

end PicMv

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

/-- The coordinate `1 / (x - c)`. -/
noncomputable def uc (x : F) (c : k) : F := (x - algebraMap k F c)⁻¹

theorem sub_ne_zero_of_tr {x : F} (hx : Transcendental k x) (c : k) : x - algebraMap k F c ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  exact hx (by rw [h]; exact isAlgebraic_algebraMap c)

end Chart

end RamanujanPetersson.JacSym


end


