-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:30:33.358713+00:00
-- url     : https://prove2.me/theorems/9e2c9a37-7fe6-4136-bd3b-08dd9872b02f
-- title:
--   Residue Selection
-- statement:
--   Definitions and structural lemmas for Residue Selection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueSelection.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.IsAdjoinRoot
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_residueExponent_ne_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_sourceYPolynomial_natDegree

set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Polynomial IntermediateField
namespace ResidueSelection
variable (F L : Type*) [Field F] [Field L] [Fintype F] [Fintype L]
  [Algebra F L] [FiniteDimensional F L]
noncomputable def elementDegree (a : L) : Nat :=
  (minpoly F a).natDegree
def elementsOfDegree (m : Nat) : Set L :=
  {a | elementDegree F L a = m}
omit [Fintype F] [FiniteDimensional F L] in
/-- The degree of an element is positive. -/
theorem elementDegree_pos (a : L) :
    0 < elementDegree F L a := by
  exact minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral a)
omit [Fintype F] [FiniteDimensional F L] in
/-- The degree of an element divides the degree of the ambient finite
extension. -/
theorem elementDegree_dvd_finrank (a : L) :
    elementDegree F L a ∣ Module.finrank F L := by
  exact minpoly.degree_dvd (Algebra.IsIntegral.isIntegral a)
omit [Fintype F] [Fintype L] in
/-- An element is a field generator exactly when its degree is the full
extension degree. -/
theorem adjoin_eq_top_iff_elementDegree_eq (a : L) :
    F⟮a⟯ = ⊤ ↔ elementDegree F L a = Module.finrank F L := by
  exact Field.primitive_element_iff_minpoly_natDegree_eq F a
omit [FiniteDimensional F L] in
/-- An element of degree `m` is fixed by the `m`-fold arithmetic Frobenius.
This is proved inside its actually generated intermediate field. -/
theorem pow_card_pow_elementDegree (a : L) :
    a ^ Fintype.card F ^ elementDegree F L a = a := by
  let E : IntermediateField F L := F⟮a⟯
  let aE : E := ⟨a, IntermediateField.mem_adjoin_simple_self F a⟩
  letI : Fintype E := Fintype.ofFinite E
  have hpow : aE ^ Fintype.card E = aE := FiniteField.pow_card aE
  have hcard : Fintype.card E =
      Fintype.card F ^ Module.finrank F E :=
    Module.card_eq_pow_finrank
  have hrank : Module.finrank F E = elementDegree F L a := by
    exact IntermediateField.adjoin.finrank
      (Algebra.IsIntegral.isIntegral a)
  have hpowValue := congrArg Subtype.val hpow
  simpa [aE, hcard, hrank] using hpowValue
omit [FiniteDimensional F L] in
/-- There are at most `|F|^m` elements of degree `m`. -/
theorem ncard_elementsOfDegree_le_pow (m : Nat) :
    Set.ncard (elementsOfDegree F L m) ≤ Fintype.card F ^ m := by
  by_cases hm : m = 0
  · subst m
    have hempty : elementsOfDegree F L 0 = ∅ := by
      ext a
      simp only [elementsOfDegree, Set.mem_setOf_eq, Set.mem_empty_iff_false]
      exact iff_false_intro (Nat.ne_of_gt (elementDegree_pos F L a))
    simp [hempty]
  · let p : Polynomial F := X ^ Fintype.card F ^ m - X
    have hp : p ≠ 0 := by
      exact FiniteField.X_pow_card_pow_sub_X_ne_zero F hm Fintype.one_lt_card
    have hsubset : elementsOfDegree F L m ⊆ p.rootSet L := by
      intro a ha
      have hdegree : elementDegree F L a = m := ha
      have hpow := pow_card_pow_elementDegree F L a
      rw [hdegree] at hpow
      rw [Polynomial.mem_rootSet_of_ne hp]
      rw [aeval_def, eval₂_sub, eval₂_pow, eval₂_X, sub_eq_zero]
      exact hpow
    calc
      Set.ncard (elementsOfDegree F L m) ≤ Set.ncard (p.rootSet L) :=
        Set.ncard_le_ncard hsubset (Set.toFinite _)
      _ ≤ p.natDegree := Polynomial.ncard_rootSet_le p L
      _ = Fintype.card F ^ m :=
        by simpa [p] using
          (FiniteField.X_pow_card_pow_sub_X_natDegree_eq
            F hm Fintype.one_lt_card)
theorem proper_divisor_le_half {m e : Nat}
    (hepos : 0 < e) (hmdvd : m ∣ e) (hmne : m ≠ e) : m ≤ e / 2 := by
  obtain ⟨k, rfl⟩ := hmdvd
  have hk : 2 ≤ k := by
    have hkpos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hkzero
      subst k
      simp at hepos
    have hkne : k ≠ 1 := by
      intro h
      subst k
      simp at hmne
    omega
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
  nlinarith
omit [Fintype F] in
/-- Every non-generator lies in one of the degree strata indexed by
`0, ..., e / 2`. -/
theorem nonGenerator_subset_degreeUnion :
    {a : L | F⟮a⟯ ≠ ⊤} ⊆
      ⋃ m ∈ (Finset.range (Module.finrank F L / 2 + 1) : Set Nat),
        elementsOfDegree F L m := by
  intro a ha
  have hne : elementDegree F L a ≠ Module.finrank F L := by
    exact fun h => ha ((adjoin_eq_top_iff_elementDegree_eq F L a).2 h)
  have hhalf : elementDegree F L a ≤ Module.finrank F L / 2 :=
    proper_divisor_le_half Module.finrank_pos
      (elementDegree_dvd_finrank F L a) hne
  simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_range,
    elementsOfDegree, Set.mem_setOf_eq]
  exact ⟨elementDegree F L a, Nat.lt_succ_of_le hhalf, rfl⟩
theorem ncard_nonGenerators_lt :
    Set.ncard {a : L | F⟮a⟯ ≠ ⊤} <
      Fintype.card F ^ (Module.finrank F L / 2 + 1) := by
  let degrees := Finset.range (Module.finrank F L / 2 + 1)
  calc
    Set.ncard {a : L | F⟮a⟯ ≠ ⊤} ≤
        Set.ncard (⋃ m ∈ (degrees : Set Nat), elementsOfDegree F L m) :=
      Set.ncard_le_ncard (nonGenerator_subset_degreeUnion F L) (Set.toFinite _)
    _ ≤ ∑ m ∈ degrees, Set.ncard (elementsOfDegree F L m) :=
      degrees.set_ncard_biUnion_le (elementsOfDegree F L)
    _ ≤ ∑ m ∈ degrees, Fintype.card F ^ m := by
      gcongr with m hm
      exact ncard_elementsOfDegree_le_pow F L m
    _ < Fintype.card F ^ (Module.finrank F L / 2 + 1) := by
      have hcard : 2 ≤ Fintype.card F := by
        exact Fintype.one_lt_card
      apply Nat.geomSum_lt hcard
      intro m hm
      simpa [degrees] using hm
theorem exists_eval_adjoin_eq_top (p : Polynomial L) (d e : Nat)
    (hdegree : p.natDegree = d) (hdpos : 0 < d)
    (hde : d < Fintype.card F)
    (hfinrank : Module.finrank F L = e) (he : 3 ≤ e) :
    ∃ a : L, F⟮p.eval a⟯ = ⊤ := by
  classical
  let bad : Set L := {a | F⟮a⟯ ≠ ⊤}
  let image : Finset L := Finset.univ.image fun a : L => p.eval a
  have hbad : Set.ncard bad <
      Fintype.card F ^ (e / 2 + 1) := by
    simpa [bad, hfinrank] using ncard_nonGenerators_lt F L
  have hhalf : e / 2 + 2 ≤ e := by omega
  have hpowpos : 0 < Fintype.card F ^ (e / 2 + 1) :=
    pow_pos Fintype.card_pos _
  have hbad_scaled : d * Set.ncard bad < Fintype.card L := by
    calc
      d * Set.ncard bad < d * Fintype.card F ^ (e / 2 + 1) :=
        (Nat.mul_lt_mul_left hdpos).2 hbad
      _ < Fintype.card F * Fintype.card F ^ (e / 2 + 1) :=
        (Nat.mul_lt_mul_right hpowpos).2 hde
      _ = Fintype.card F ^ (e / 2 + 2) := by
        rw [show e / 2 + 2 = (e / 2 + 1) + 1 by omega, pow_succ]
        exact mul_comm _ _
      _ ≤ Fintype.card F ^ e :=
        pow_le_pow_right' (by omega : 1 ≤ Fintype.card F) hhalf
      _ = Fintype.card L := by
        rw [← hfinrank, ← Module.card_eq_pow_finrank]
  have hpdegree : 0 < p.degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    simpa [hdegree] using hdpos
  have himage_lower : Fintype.card L ≤ d * image.card := by
    simpa [image, hdegree] using
      (FiniteField.card_image_polynomial_eval hpdegree)
  have hbad_lt_image : Set.ncard bad < image.card := by
    apply (Nat.mul_lt_mul_left hdpos).mp
    exact hbad_scaled.trans_le himage_lower
  by_contra hnone
  have hsubset : (image : Set L) ⊆ bad := by
    intro gamma hgamma
    show F⟮gamma⟯ ≠ ⊤
    intro htop
    apply hnone
    obtain ⟨alpha, _halpha, halpha⟩ := Finset.mem_image.mp hgamma
    exact ⟨alpha, halpha ▸ htop⟩
  have hcard_le : image.card ≤ Set.ncard bad := by
    simpa using Set.ncard_le_ncard hsubset (Set.toFinite bad)
  exact (Nat.not_le_of_lt hbad_lt_image) hcard_le
end ResidueSelection
open ResidueSelection
noncomputable def residueYPolynomial (P : BasePrime) (r : Rank) (level : Nat) :
    Polynomial (ResidueField P r level) :=
  (sourceYPolynomial P r).map
    (algebraMap (BaseField P) (ResidueField P r level))
theorem residueYPolynomial_natDegree (P : BasePrime) (r : Rank) (level : Nat) :
    (residueYPolynomial P r level).natDegree = r.matrixRank := by
  rw [residueYPolynomial, Polynomial.natDegree_map,
    sourceYPolynomial_natDegree]
theorem exists_residueAlpha (P : BasePrime) (r : Rank) (level : Nat) :
    ∃ alpha : ResidueField P r level,
      (BaseField P)⟮(residueYPolynomial P r level).eval alpha⟯ = ⊤ := by
  apply exists_eval_adjoin_eq_top
    (BaseField P) (ResidueField P r level)
    (residueYPolynomial P r level) r.matrixRank
    (r.residueExponent level)
  · exact residueYPolynomial_natDegree P r level
  · exact lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r)
  · rw [ZMod.card]
    exact lt_of_lt_of_le (by cases r <;> simp [Rank.matrixRank]) P.five_le
  · exact GaloisField.finrank P.q (Rank.residueExponent_ne_zero r level)
  · cases r <;> simp [Rank.residueExponent, Rank.matrixRank] <;> omega
noncomputable def residueAlpha (P : BasePrime) (r : Rank) (level : Nat) :
    ResidueField P r level :=
  Classical.choose (exists_residueAlpha P r level)
noncomputable def residueGamma (P : BasePrime) (r : Rank) (level : Nat) :
    ResidueField P r level :=
  (residueYPolynomial P r level).eval (residueAlpha P r level)
theorem residueGamma_adjoin_eq_top (P : BasePrime) (r : Rank) (level : Nat) :
    (BaseField P)⟮residueGamma P r level⟯ = ⊤ := by
  exact Classical.choose_spec (exists_residueAlpha P r level)
theorem residueAlpha_adjoin_eq_top (P : BasePrime) (r : Rank) (level : Nat) :
    (BaseField P)⟮residueAlpha P r level⟯ = ⊤ := by
  apply top_unique
  rw [← residueGamma_adjoin_eq_top P r level]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst x
  rw [residueGamma, residueYPolynomial, Polynomial.eval_map]
  have hle : Algebra.adjoin (BaseField P) {residueAlpha P r level} ≤
      ((BaseField P)⟮residueAlpha P r level⟯).toSubalgebra := by
    apply Algebra.adjoin_le
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact IntermediateField.mem_adjoin_simple_self
      (BaseField P) (residueAlpha P r level)
  apply hle
  simpa [Polynomial.aeval_def] using
    (Polynomial.aeval_mem_adjoin_singleton
      (p := sourceYPolynomial P r) (BaseField P) (residueAlpha P r level))
noncomputable def residueYMinpoly (P : BasePrime) (r : Rank) (level : Nat) :
    PolynomialRing P :=
  minpoly (BaseField P) (residueGamma P r level)
noncomputable def residueXMinpoly (P : BasePrime) (r : Rank) (level : Nat) :
    PolynomialRing P :=
  minpoly (BaseField P) (residueAlpha P r level)
theorem residueY_algebraAdjoin_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Algebra.adjoin (BaseField P) {residueGamma P r level} = ⊤ :=
  Algebra.adjoin_eq_top_of_primitive_element
    (Algebra.IsAlgebraic.isAlgebraic (residueGamma P r level))
    (residueGamma_adjoin_eq_top P r level)
theorem residueX_algebraAdjoin_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Algebra.adjoin (BaseField P) {residueAlpha P r level} = ⊤ :=
  Algebra.adjoin_eq_top_of_primitive_element
    (Algebra.IsAlgebraic.isAlgebraic (residueAlpha P r level))
    (residueAlpha_adjoin_eq_top P r level)
noncomputable def residueYAdjoinRootEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    AdjoinRoot (residueYMinpoly P r level) ≃ₐ[BaseField P]
      ResidueField P r level :=
  (IsAdjoinRootMonic.mkOfAdjoinEqTop'
    (residueY_algebraAdjoin_eq_top P r level)).toIsAdjoinRoot.adjoinRootAlgEquiv
noncomputable def residueXAdjoinRootEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    AdjoinRoot (residueXMinpoly P r level) ≃ₐ[BaseField P]
      ResidueField P r level :=
  (IsAdjoinRootMonic.mkOfAdjoinEqTop'
    (residueX_algebraAdjoin_eq_top P r level)).toIsAdjoinRoot.adjoinRootAlgEquiv
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


