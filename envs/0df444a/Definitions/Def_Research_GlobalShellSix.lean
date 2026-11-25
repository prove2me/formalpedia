-- Prove2me | Definitions.Def_Research_GlobalShellSix
-- name    : Research_GlobalShellSix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:43:08.434436+00:00
-- url     : https://prove2.me/theorems/a3009c40-07be-427b-9659-ef2fbf175322
-- title:
--   Global Shell Six
-- statement:
--   Definitions and structural lemmas for Global Shell Six, from Colin Snyder / Star Fleet Math; AItoBit (AItoBit/erdos-662-proof; see pinned Apache-2.0 LICENSE and NOTICE)'s pinned Erdos 662: corrected global threshold conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean

module
public import Definitions.Def_Research_TriangularShells
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Research
set_option maxRecDepth 100000
local instance prodLexLinearOrder {α β : Type*} [LinearOrder α]
    [LinearOrder β] : LinearOrder (α × β) :=
  Prod.Lex.instLinearOrder α β
def obliqueNormNum (d : ℤ × ℤ) : ℤ :=
  305 * d.1 ^ 2 + 305 * d.2 ^ 2 + 272 * d.1 * d.2
def intWindow6 : Finset ℤ :=
  {(-6 : ℤ), -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6}
lemma mem_intWindow6_iff (z : ℤ) : z ∈ intWindow6 ↔ -6 ≤ z ∧ z ≤ 6 := by
  simp [intWindow6]
  omega
def shellSixOffsets : Finset (ℤ × ℤ) :=
  ((intWindow6.product intWindow6).filter
    (fun d => d ≠ (0, 0) ∧ obliqueNormNum d ≤ 36 * 305))
lemma obliqueNormNum_decomposition (m n : ℤ) :
    obliqueNormNum (m, n) =
      136 * (m + n) ^ 2 + 169 * m ^ 2 + 169 * n ^ 2 := by
  simp only [obliqueNormNum]
  ring
theorem oblique_norm_le_six_bounds (m n : ℤ)
    (h : obliqueNormNum (m, n) ≤ 36 * 305) :
    -6 ≤ m ∧ m ≤ 6 ∧ -6 ≤ n ∧ n ≤ 6 := by
  have hdecomp := obliqueNormNum_decomposition m n
  have hpos1 : 0 ≤ (m + n) ^ 2 := sq_nonneg (m + n)
  have hposm : 0 ≤ m ^ 2 := sq_nonneg m
  have hposn : 0 ≤ n ^ 2 := sq_nonneg n
  have hm2 : 169 * m ^ 2 ≤ 36 * 305 := by nlinarith
  have hn2 : 169 * n ^ 2 ≤ 36 * 305 := by nlinarith
  constructor
  · by_contra hm
    have : m ≤ -7 := by omega
    nlinarith [sq_nonneg (m + 7)]
  constructor
  · by_contra hm
    have : 7 ≤ m := by omega
    nlinarith [sq_nonneg (m - 7)]
  constructor
  · by_contra hn
    have : n ≤ -7 := by omega
    nlinarith [sq_nonneg (n + 7)]
  · by_contra hn
    have : 7 ≤ n := by omega
    nlinarith [sq_nonneg (n - 7)]
theorem mem_shellSixOffsets_iff (d : ℤ × ℤ) :
    d ∈ shellSixOffsets ↔ d ≠ (0, 0) ∧ obliqueNormNum d ≤ 36 * 305 := by
  rcases d with ⟨m, n⟩
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hb := oblique_norm_le_six_bounds m n h.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, h⟩
    · exact (mem_intWindow6_iff m).2 ⟨hb.1, hb.2.1⟩
    · exact (mem_intWindow6_iff n).2 ⟨hb.2.2.1, hb.2.2.2⟩
def triCoordsWithinThirtySix : Finset (ℤ × ℤ) :=
  ((intWindow6.product intWindow6).filter
    (fun d => triNormSq d ≤ 36)).erase (0, 0)
noncomputable def obliquePoint (q : Fin 365 × Fin 365) : ℝ × ℝ :=
  ((q.1.val : ℝ) + (136 / 305 : ℝ) * (q.2.val : ℝ),
    (273 / 305 : ℝ) * (q.2.val : ℝ))
lemma obliquePoint_sqDist_eq (q s : Fin 365 × Fin 365) :
    sqDist (obliquePoint q) (obliquePoint s) =
      (obliqueNormNum
        (((s.1.val : ℤ) - (q.1.val : ℤ)),
         ((s.2.val : ℤ) - (q.2.val : ℤ))) : ℝ) / 305 := by
  simp only [sqDist, obliquePoint, obliqueNormNum, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  norm_num
  ring
abbrev ShellSixOffset := {d : ℤ × ℤ // d ∈ shellSixOffsets}
lemma natAbs_le_six_of_bounds (z : ℤ) (hl : -6 ≤ z) (hu : z ≤ 6) :
    z.natAbs ≤ 6 := by
  by_cases hz : 0 ≤ z
  · have hc : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz
    omega
  · have hn : 0 ≤ -z := by omega
    have hc : (z.natAbs : ℤ) = -z := by
      calc
        (z.natAbs : ℤ) = ((-z).natAbs : ℕ) := by rw [Int.natAbs_neg]
        _ = -z := Int.natAbs_of_nonneg hn
    omega
lemma shellSixOffset_natAbs_le (d : ShellSixOffset) :
    d.val.1.natAbs ≤ 6 ∧ d.val.2.natAbs ≤ 6 := by
  have hm := (mem_shellSixOffsets_iff d.val).mp d.property
  have hb := oblique_norm_le_six_bounds d.val.1 d.val.2 hm.2
  exact ⟨natAbs_le_six_of_bounds d.val.1 hb.1 hb.2.1,
    natAbs_le_six_of_bounds d.val.2 hb.2.2.1 hb.2.2.2⟩
def signedStart (d : ℤ) (hd : d.natAbs ≤ 6)
    (k : Fin (365 - d.natAbs)) : Fin 365 :=
  if h : d < 0 then
    ⟨k.val + d.natAbs, by omega⟩
  else
    ⟨k.val, by omega⟩
def signedEnd (d : ℤ) (hd : d.natAbs ≤ 6)
    (k : Fin (365 - d.natAbs)) : Fin 365 :=
  if h : d < 0 then
    ⟨k.val, by omega⟩
  else
    ⟨k.val + d.natAbs, by omega⟩
lemma signedEnd_sub_signedStart (d : ℤ) (hd : d.natAbs ≤ 6)
    (k : Fin (365 - d.natAbs)) :
    ((signedEnd d hd k).val : ℤ) - ((signedStart d hd k).val : ℤ) = d := by
  by_cases h : d < 0
  · have hn : 0 ≤ -d := by omega
    have hc : (d.natAbs : ℤ) = -d := by
      calc
        (d.natAbs : ℤ) = ((-d).natAbs : ℕ) := by rw [Int.natAbs_neg]
        _ = -d := Int.natAbs_of_nonneg hn
    simp [signedEnd, signedStart, h, hc]
  · have hp : 0 ≤ d := by omega
    have hc : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hp
    simp [signedEnd, signedStart, h, hc]
lemma signedStart_injective (d : ℤ) (hd : d.natAbs ≤ 6) :
    Function.Injective (signedStart d hd) := by
  intro a b h
  apply Fin.ext
  by_cases hdneg : d < 0
  · simpa [signedStart, hdneg] using h
  · simpa [signedStart, hdneg] using h
abbrev ShellSixIncidence :=
  Σ d : ShellSixOffset,
    Fin (365 - d.val.1.natAbs) × Fin (365 - d.val.2.natAbs)
def shellSixIncidenceStart (z : ShellSixIncidence) : Fin 365 × Fin 365 :=
  (signedStart z.1.val.1 (shellSixOffset_natAbs_le z.1).1 z.2.1,
   signedStart z.1.val.2 (shellSixOffset_natAbs_le z.1).2 z.2.2)
def shellSixIncidenceEnd (z : ShellSixIncidence) : Fin 365 × Fin 365 :=
  (signedEnd z.1.val.1 (shellSixOffset_natAbs_le z.1).1 z.2.1,
   signedEnd z.1.val.2 (shellSixOffset_natAbs_le z.1).2 z.2.2)
lemma shellSixIncidence_difference (z : ShellSixIncidence) :
    (((shellSixIncidenceEnd z).1.val : ℤ) -
        ((shellSixIncidenceStart z).1.val : ℤ),
      ((shellSixIncidenceEnd z).2.val : ℤ) -
        ((shellSixIncidenceStart z).2.val : ℤ)) = z.1.val := by
  apply Prod.ext
  · exact signedEnd_sub_signedStart z.1.val.1
      (shellSixOffset_natAbs_le z.1).1 z.2.1
  · exact signedEnd_sub_signedStart z.1.val.2
      (shellSixOffset_natAbs_le z.1).2 z.2.2
def shellSixIncidencePair (z : ShellSixIncidence) :
    (Fin 365 × Fin 365) × (Fin 365 × Fin 365) :=
  (shellSixIncidenceStart z, shellSixIncidenceEnd z)
lemma shellSixIncidencePair_injective :
    Function.Injective shellSixIncidencePair := by
  rintro ⟨d, k⟩ ⟨e, l⟩ hpair
  have hsx := congrArg (fun q => q.1.1.val) hpair
  have hsy := congrArg (fun q => q.1.2.val) hpair
  have hex := congrArg (fun q => q.2.1.val) hpair
  have hey := congrArg (fun q => q.2.2.val) hpair
  have hdval : d.val = e.val := by
    apply Prod.ext
    · calc
        d.val.1 =
            ((shellSixIncidenceEnd ⟨d, k⟩).1.val : ℤ) -
              ((shellSixIncidenceStart ⟨d, k⟩).1.val : ℤ) :=
          (congrArg Prod.fst (shellSixIncidence_difference ⟨d, k⟩)).symm
        _ = ((shellSixIncidenceEnd ⟨e, l⟩).1.val : ℤ) -
              ((shellSixIncidenceStart ⟨e, l⟩).1.val : ℤ) := by
          exact congrArg₂ (fun a b : ℕ => (a : ℤ) - (b : ℤ)) hex hsx
        _ = e.val.1 :=
          congrArg Prod.fst (shellSixIncidence_difference ⟨e, l⟩)
    · calc
        d.val.2 =
            ((shellSixIncidenceEnd ⟨d, k⟩).2.val : ℤ) -
              ((shellSixIncidenceStart ⟨d, k⟩).2.val : ℤ) :=
          (congrArg Prod.snd (shellSixIncidence_difference ⟨d, k⟩)).symm
        _ = ((shellSixIncidenceEnd ⟨e, l⟩).2.val : ℤ) -
              ((shellSixIncidenceStart ⟨e, l⟩).2.val : ℤ) := by
          exact congrArg₂ (fun a b : ℕ => (a : ℤ) - (b : ℤ)) hey hsy
        _ = e.val.2 :=
          congrArg Prod.snd (shellSixIncidence_difference ⟨e, l⟩)
  have hde : d = e := Subtype.ext hdval
  subst e
  have hstart : shellSixIncidenceStart ⟨d, k⟩ =
      shellSixIncidenceStart ⟨d, l⟩ := congrArg Prod.fst hpair
  have hkx : k.1 = l.1 :=
    signedStart_injective d.val.1 (shellSixOffset_natAbs_le d).1
      (congrArg Prod.fst hstart)
  have hky : k.2 = l.2 :=
    signedStart_injective d.val.2 (shellSixOffset_natAbs_le d).2
      (congrArg Prod.snd hstart)
  have hkl : k = l := Prod.ext hkx hky
  subst l
  rfl
def shellSixIncidenceEmbedding :
    ShellSixIncidence ↪
      ((Fin 365 × Fin 365) × (Fin 365 × Fin 365)) :=
  ⟨shellSixIncidencePair, shellSixIncidencePair_injective⟩
noncomputable def radiusSixDirectedPairs {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) : Finset (α × α) :=
  (Finset.univ.product Finset.univ).filter fun q =>
    q.1 ≠ q.2 ∧ sqDist (p q.1) (p q.2) ≤ 36
noncomputable def radiusSixOrdinaryDirectedPairs {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) : Finset (α × α) :=
  (Finset.univ.product Finset.univ).filter fun q =>
    q.1 ≠ q.2 ∧ Real.sqrt (sqDist (p q.1) (p q.2)) ≤ 6
def RadiusSixPairType {α : Type*} (p : α → ℝ × ℝ) :=
  {q : α × α // q.1 ≠ q.2 ∧ sqDist (p q.1) (p q.2) ≤ 36}
noncomputable instance RadiusSixPairType.instFintype {α : Type*} [Fintype α]
    (p : α → ℝ × ℝ) : Fintype (RadiusSixPairType p) := by
  letI : Finite (RadiusSixPairType p) :=
    Finite.of_injective (fun q : RadiusSixPairType p => q.val)
      Subtype.val_injective
  exact Fintype.ofFinite (RadiusSixPairType p)
noncomputable def radiusSixOrderedPairs {α : Type*} [Fintype α]
    [LinearOrder α] (p : α → ℝ × ℝ) : Finset (α × α) :=
  (Finset.univ.product Finset.univ).filter fun q =>
    q.1 < q.2 ∧ sqDist (p q.1) (p q.2) ≤ 36
noncomputable def radiusSixOrdinaryOrderedPairs {α : Type*} [Fintype α]
    [LinearOrder α] (p : α → ℝ × ℝ) : Finset (α × α) :=
  (Finset.univ.product Finset.univ).filter fun q =>
    q.1 < q.2 ∧ Real.sqrt (sqDist (p q.1) (p q.2)) ≤ 6
lemma shellSixIncidencePair_valid (z : ShellSixIncidence) :
    let q := shellSixIncidencePair z
    q.1 ≠ q.2 ∧ sqDist (obliquePoint q.1) (obliquePoint q.2) ≤ 36 := by
  have hoff := (mem_shellSixOffsets_iff z.1.val).mp z.1.property
  change shellSixIncidenceStart z ≠ shellSixIncidenceEnd z ∧
    sqDist (obliquePoint (shellSixIncidenceStart z))
      (obliquePoint (shellSixIncidenceEnd z)) ≤ 36
  constructor
  · intro heq
    apply hoff.1
    rw [← shellSixIncidence_difference z, heq]
    simp
  · rw [obliquePoint_sqDist_eq, shellSixIncidence_difference]
    have hzR : (obliqueNormNum z.1.val : ℝ) ≤ (36 * 305 : ℝ) := by
      exact_mod_cast hoff.2
    norm_num at hzR ⊢
    linarith
def shellSixIncidenceToDirected :
    ShellSixIncidence ↪ RadiusSixPairType obliquePoint where
  toFun z := ⟨shellSixIncidencePair z, shellSixIncidencePair_valid z⟩
  inj' := by
    intro z w h
    apply shellSixIncidencePair_injective
    exact congrArg Subtype.val h
noncomputable def obliqueBlocks (m : ℕ)
    (q : Fin m × (Fin 365 × Fin 365)) : ℝ × ℝ :=
  (2000 * (q.1.val : ℝ) + (obliquePoint q.2).1,
    (obliquePoint q.2).2)
abbrev ShellSixBlockIncidence (m : ℕ) := Fin m × ShellSixIncidence
def shellSixBlockIncidencePair (m : ℕ) (z : ShellSixBlockIncidence m) :
    (Fin m × (Fin 365 × Fin 365)) ×
      (Fin m × (Fin 365 × Fin 365)) :=
  ((z.1, shellSixIncidenceStart z.2),
    (z.1, shellSixIncidenceEnd z.2))
lemma shellSixBlockIncidencePair_injective (m : ℕ) :
    Function.Injective (shellSixBlockIncidencePair m) := by
  rintro ⟨b, z⟩ ⟨c, w⟩ h
  have hbc : b = c := congrArg (fun q => q.1.1) h
  have hstart : shellSixIncidenceStart z = shellSixIncidenceStart w :=
    congrArg (fun q => q.1.2) h
  have hend : shellSixIncidenceEnd z = shellSixIncidenceEnd w :=
    congrArg (fun q => q.2.2) h
  have hzw : z = w := shellSixIncidencePair_injective (Prod.ext hstart hend)
  exact Prod.ext hbc hzw
lemma shellSixBlockIncidencePair_valid (m : ℕ)
    (z : ShellSixBlockIncidence m) :
    let q := shellSixBlockIncidencePair m z
    q.1 ≠ q.2 ∧ sqDist (obliqueBlocks m q.1) (obliqueBlocks m q.2) ≤ 36 := by
  have hv := shellSixIncidencePair_valid z.2
  change shellSixIncidenceStart z.2 ≠ shellSixIncidenceEnd z.2 ∧
    sqDist (obliquePoint (shellSixIncidenceStart z.2))
      (obliquePoint (shellSixIncidenceEnd z.2)) ≤ 36 at hv
  change (z.1, shellSixIncidenceStart z.2) ≠
      (z.1, shellSixIncidenceEnd z.2) ∧
    sqDist (obliqueBlocks m (z.1, shellSixIncidenceStart z.2))
      (obliqueBlocks m (z.1, shellSixIncidenceEnd z.2)) ≤ 36
  constructor
  · intro h
    exact hv.1 (congrArg Prod.snd h)
  · have heq :
        sqDist (obliqueBlocks m (z.1, shellSixIncidenceStart z.2))
          (obliqueBlocks m (z.1, shellSixIncidenceEnd z.2)) =
        sqDist (obliquePoint (shellSixIncidenceStart z.2))
          (obliquePoint (shellSixIncidenceEnd z.2)) := by
        simp only [obliqueBlocks, sqDist]
        ring
    rw [heq]
    exact hv.2
def shellSixBlockIncidenceToDirected (m : ℕ) :
    ShellSixBlockIncidence m ↪ RadiusSixPairType (obliqueBlocks m) where
  toFun z := ⟨shellSixBlockIncidencePair m z,
    shellSixBlockIncidencePair_valid m z⟩
  inj' := by
    intro z w h
    apply shellSixBlockIncidencePair_injective m
    exact congrArg Subtype.val h
def OrdinaryOneSeparatedOn {α : Type*} (p : α → ℝ × ℝ) : Prop :=
  ∀ i j, i ≠ j → 1 ≤ Real.sqrt (sqDist (p i) (p j))
def EventualShellSixDirectedAverageBound : Prop :=
  ∃ N : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α],
    N ≤ Fintype.card α → ∀ p : α → ℝ × ℝ,
      OrdinaryOneSeparatedOn p →
        (radiusSixOrdinaryDirectedPairs p).card ≤ 126 * Fintype.card α
def EventualShellSixUnorderedBound : Prop :=
  ∃ N : ℕ, ∀ (α : Type) [Fintype α] [LinearOrder α],
    N ≤ Fintype.card α → ∀ p : α → ℝ × ℝ,
      OrdinaryOneSeparatedOn p →
        (radiusSixOrdinaryOrderedPairs p).card ≤ 63 * Fintype.card α
end Research


