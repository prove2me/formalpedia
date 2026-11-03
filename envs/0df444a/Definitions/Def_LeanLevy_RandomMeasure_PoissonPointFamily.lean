-- Prove2me | Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
-- name    : LeanLevy_RandomMeasure_PoissonPointFamily
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T22:23:27.382556+00:00
-- url     : https://prove2.me/theorems/680ec9f9-5656-4249-bb9f-0960a7957dec
-- title:
--   LeanLevy source module: RandomMeasure.PoissonPointFamily
-- statement:
--   Pinned source-faithful definition and helper bundle for `LeanLevy.RandomMeasure.PoissonPointFamily`. Only empty lines and standalone line comments were removed to meet the platform size limit; all retained Lean lines are byte-identical to the previously compiled generated original. Remote compilation pending.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Disjointed
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.Floor
import Definitions.Def_LeanLevy_Probability_Poisson
/-!
# Partitioning a σ-finite measure into finite pieces with normalized laws
The Poisson random measure attached to a σ-finite intensity `m` on a measurable space `E` is built
by cutting `E` into countably many disjoint measurable pieces of finite `m`-mass and running an
independent Poisson family on each. This file provides that partition and, on each piece, the
*normalized piece law* — the probability measure obtained by rescaling `m` restricted to the piece.
The partition is the classical `disjointed (spanningSets m)`: mathlib's generic σ-finite exhaustion,
disjointified so the pieces are pairwise disjoint while still covering `E`. Each piece has finite
`m`-mass, so it can be normalized to a probability measure. On a piece of zero mass the normalization
is degenerate, so we substitute a Dirac point mass at an arbitrary junk point; such a piece
contributes nothing downstream (its Poisson count is `Poisson 0 = δ₀`).
## Main definitions
* `ProbabilityTheory.prmPiece` — the `k`-th disjoint finite-mass piece of a σ-finite measure.
* `ProbabilityTheory.prmPieceLaw` — the normalized probability law of `m` on the `k`-th piece.
* `ProbabilityTheory.pointFamilyIndexType`, `ProbabilityTheory.pointFamilyCombined` — the combined
  index type `ℕ ⊕ ℕ × ℕ ↦ Type` and the single family gathering the piece counts and all points into
  one function, the data whose joint independence the whole random measure rests on.
* `ProbabilityTheory.IsPoissonPointFamily` — the driver predicate for the counts-and-points data.
* `ProbabilityTheory.pieceSum` — the sum of a test function over the points of a single piece.
## Main results
* `ProbabilityTheory.pairwise_disjoint_prmPiece`, `ProbabilityTheory.iUnion_prmPiece`,
  `ProbabilityTheory.measure_prmPiece_lt_top` — the pieces form a disjoint measurable partition of
  `E` into sets of finite `m`-mass.
* `ProbabilityTheory.isProbabilityMeasure_prmPieceLaw` — each piece law is a probability measure.
* `ProbabilityTheory.lintegral_prmPieceLaw`, `ProbabilityTheory.integral_smul_prmPieceLaw` — the
  scaling bridges turning integrals against the piece law into (rescaled) integrals against `m`
  restricted to the piece, for the lower Lebesgue and the Bochner integral respectively.
* `ProbabilityTheory.exists_isPoissonPointFamily` — the existence of the Poisson point family on a
  canonical probability space, built in one `exists_hasLaw_indepFun` call over the combined index so
  that mutual independence of every count and every point is free by construction.
* `ProbabilityTheory.IsPoissonPointFamily.iIndepFun_count`,
  `ProbabilityTheory.IsPoissonPointFamily.iIndepFun_point_piece` — the disjoint-block extractors that
  read independence of a sub-family off the one combined `indep` field.
* `ProbabilityTheory.IsPoissonPointFamily.indepFun_pointFamily_split` — the general engine reading
  independence of any two disjoint sub-families off the combined `indep` field; the
  count-versus-marks, piece-versus-piece (`indepFun_piece_piece`), and prefix-versus-next-block
  (`indepFun_pieceBlocks`) independences are its instances.
* `ProbabilityTheory.integral_pieceSum` — **Campbell's formula**: the mean of a piece sum is the
  `m`-integral of the test function over the piece.
* `ProbabilityTheory.integral_sq_pieceSum`, `ProbabilityTheory.integrable_sq_pieceSum` — the
  **second-moment identity** `E[(pieceSum)²] = ∫ f² dm + (∫ f dm)²` over the piece, and the square's
  integrability.
* `ProbabilityTheory.indepFun_pieceSum_pieceSum` — piece sums of distinct pieces are independent.
* `ProbabilityTheory.integral_pieceProd_eq_exp` — the piece **probability-generating identity**
  `E[∏_{n < K} w (X n)] = exp (m(piece) · (∫ w − 1))` for bounded measurable `w`.
* `ProbabilityTheory.map_thinnedCount` — **thinning**: the number of points of a piece landing in a
  measurable set `A` (`thinnedCount`) is Poisson with mean `m (piece ∩ A)`.
* `ProbabilityTheory.indepFun_thinnedCount_thinnedCount` — within a piece, the thinned counts of two
  disjoint sets are (pairwise) independent.
* `ProbabilityTheory.integral_prod_pow_thinnedCount`,
  `ProbabilityTheory.charFunDual_pi_thinnedCount` — the joint probability-generating and
  characteristic functions of a finite family of thinned counts over a pairwise disjoint family
  factorize across the pieces.
* `ProbabilityTheory.iIndepFun_thinnedCount` — within a piece, the thinned counts of a pairwise
  disjoint finite family of sets are mutually independent.
This file opens the `LeanLevy/RandomMeasure/` directory; the Poisson point family, the random measure
itself, and the compensated `L²` integral are built on top of this partition.
Because the combined family mixes `ℕ`-valued counts with `E`-valued points, `exists_hasLaw_indepFun`
forces all coordinate codomains into a single universe; `E` is therefore taken in `Type` here (which
covers the intended intensities on `ℝ` and `ℝ ^ d`).
-/
open MeasureTheory
open scoped ENNReal
namespace ProbabilityTheory
variable {E : Type*} [MeasurableSpace E]
/-! ### The partition -/
/-- The `k`-th piece of the canonical partition of a σ-finite measure `m`: the disjointification of
mathlib's σ-finite exhaustion `spanningSets m`. The pieces are pairwise disjoint, measurable, cover
`E`, and each has finite `m`-mass. -/
noncomputable def prmPiece (m : Measure E) [SigmaFinite m] (k : ℕ) : Set E :=
  disjointed (spanningSets m) k
/-- The normalized law of `m` on the `k`-th partition piece: `m` restricted to the piece and rescaled
to total mass one. When the piece has zero `m`-mass the rescaling is degenerate, so we fall back to a
Dirac mass at an arbitrary junk point; either way the result is a probability measure. -/
noncomputable def prmPieceLaw (m : Measure E) [SigmaFinite m] [Nonempty E] (k : ℕ) : Measure E :=
  if m (prmPiece m k) = 0 then Measure.dirac (Classical.arbitrary E)
  else (m (prmPiece m k))⁻¹ • m.restrict (prmPiece m k)
variable {m : Measure E} [SigmaFinite m] {k : ℕ}
/-- Each partition piece is measurable. -/
theorem measurableSet_prmPiece : MeasurableSet (prmPiece m k) :=
  MeasurableSet.disjointed (measurableSet_spanningSets m) k
/-- The partition pieces are pairwise disjoint. -/
theorem pairwise_disjoint_prmPiece : Pairwise (Function.onFun Disjoint (prmPiece m)) :=
  disjoint_disjointed (spanningSets m)
/-- The partition pieces cover `E`. -/
theorem iUnion_prmPiece : ⋃ k, prmPiece m k = Set.univ := by
  simp only [prmPiece]
  rw [iUnion_disjointed]
  exact iUnion_spanningSets m
/-- Each partition piece has finite `m`-mass, since it is contained in a spanning set. -/
theorem measure_prmPiece_lt_top : m (prmPiece m k) < ⊤ :=
  lt_of_le_of_lt (measure_mono (disjointed_subset (spanningSets m) k))
    (measure_spanningSets_lt_top m k)
/-! ### The normalized piece law -/
/-- On a piece of positive `m`-mass, `prmPieceLaw` is the explicit rescaled restriction. -/
private theorem prmPieceLaw_of_ne_zero [Nonempty E] (hk : m (prmPiece m k) ≠ 0) :
    prmPieceLaw m k = (m (prmPiece m k))⁻¹ • m.restrict (prmPiece m k) := by
  unfold prmPieceLaw
  rw [if_neg hk]
/-- Each normalized piece law is a probability measure: on a zero-mass piece it is a Dirac mass, and
on a positive-mass piece the rescaling factor `(m (prmPiece m k))⁻¹` cancels the finite total mass. -/
instance isProbabilityMeasure_prmPieceLaw [Nonempty E] :
    IsProbabilityMeasure (prmPieceLaw m k) := by
  unfold prmPieceLaw
  split_ifs with h
  · infer_instance
  · refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel h (measure_prmPiece_lt_top).ne
/-- Bochner scaling bridge: on a positive-mass piece, the `m`-mass of the piece times the Bochner
integral against the normalized piece law recovers the set integral against `m`. This is the form
Tasks 3–4 consume, with `f` integrable on the piece. -/
theorem integral_smul_prmPieceLaw [Nonempty E] (hk : m (prmPiece m k) ≠ 0) (f : E → ℝ) :
    (m (prmPiece m k)).toReal • ∫ x, f x ∂(prmPieceLaw m k)
      = ∫ x in prmPiece m k, f x ∂m := by
  have ht : (m (prmPiece m k)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hk, (measure_prmPiece_lt_top).ne⟩
  rw [prmPieceLaw_of_ne_zero hk, integral_smul_measure, smul_smul, ENNReal.toReal_inv,
    mul_inv_cancel₀ ht, one_smul]
/-! ### The Poisson point family
The Poisson random measure is generated by, for each partition piece `k`, a Poisson-distributed count
`K k` and an i.i.d. sequence of points `X k n` drawn from the normalized piece law — with all counts
and all points jointly independent. mathlib has no block-grouping lemma delivering joint independence
of a countable family of blocks after the fact, so the entire data is built in a single
`exists_hasLaw_indepFun` call over the combined index `ℕ ⊕ ℕ × ℕ` (counts on `Sum.inl`, points on
`Sum.inr`); mutual independence is then free by construction and every disjoint-block independence
statement downstream is a `precomp` away.
Since that one call mixes `ℕ`-valued and `E`-valued coordinates, it forces every codomain into a
single universe, so this section works with `E : Type`. -/
/-- The codomain type family of the combined Poisson point family over the index `ℕ ⊕ ℕ × ℕ`: the
count coordinates on `Sum.inl` are `ℕ`-valued and the point coordinates on `Sum.inr` are `E`-valued.
`Sum.elim` into `Type` packages the two heterogeneous codomains into one dependent family. -/
def pointFamilyIndexType (E : Type) : ℕ ⊕ ℕ × ℕ → Type :=
  Sum.elim (fun _ => ℕ) (fun _ => E)
/-- Each coordinate of the combined index carries the obvious measurable space: `ℕ`'s on a count
coordinate, `E`'s on a point coordinate. -/
instance instMeasurableSpacePointFamilyIndexType (E : Type) [MeasurableSpace E]
    (i : ℕ ⊕ ℕ × ℕ) : MeasurableSpace (pointFamilyIndexType E i) := by
  rcases i with k | p
  · exact (inferInstance : MeasurableSpace ℕ)
  · exact (inferInstance : MeasurableSpace E)
/-- The single combined family gathering the piece counts `K k` (on `Sum.inl k`) and every point
`X k n` (on `Sum.inr (k, n)`) into one function `∀ i, Ω → pointFamilyIndexType E i`. Independence of
any sub-family — the counts, or the points of a fixed piece — is recovered from the joint
independence of this one function by precomposing the index with the relevant injection. -/
def pointFamilyCombined {Ω E : Type} (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) :
    ∀ i, Ω → pointFamilyIndexType E i
  | Sum.inl k => K k
  | Sum.inr p => X p.1 p.2
section PointFamily
variable {Ω E : Type} [MeasurableSpace E]
/-- The coordinate law family of the combined Poisson point family: `Poisson (m (prmPiece m k))` on a
count coordinate `Sum.inl k`, the normalized piece law `prmPieceLaw m k` on a point coordinate
`Sum.inr (k, n)`. Each is a probability measure. -/
noncomputable def pointFamilyLaw (m : Measure E) [SigmaFinite m] [Nonempty E] :
    ∀ i, Measure (pointFamilyIndexType E i)
  | Sum.inl k => ((poissonMeasure (m (prmPiece m k)).toNNReal : Measure ℕ) :
      Measure (pointFamilyIndexType E (Sum.inl k)))
  | Sum.inr p => ((prmPieceLaw m p.1 : Measure E) :
      Measure (pointFamilyIndexType E (Sum.inr p)))
/-- Every coordinate law of the combined family is a probability measure, so the family is admissible
for `exists_hasLaw_indepFun`. -/
instance instIsProbabilityMeasurePointFamilyLaw (m : Measure E) [SigmaFinite m] [Nonempty E]
    (i : ℕ ⊕ ℕ × ℕ) : IsProbabilityMeasure (pointFamilyLaw m i) := by
  rcases i with k | p
  · exact (inferInstance : IsProbabilityMeasure (poissonMeasure _))
  · exact (inferInstance : IsProbabilityMeasure (prmPieceLaw m p.1))
variable [MeasurableSpace Ω]
/-- **The Poisson point family** of a σ-finite intensity `m`: for each partition piece `k` a count
`K k` distributed as `Poisson (m (prmPiece m k))`, and for each `k` a sequence of points `X k n` each
distributed as the normalized piece law `prmPieceLaw m k`, with all counts and all points jointly
independent. The single `indep` field over the combined index makes every disjoint-block
independence statement derivable by `precomp`. -/
structure IsPoissonPointFamily (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (m : Measure E) [SigmaFinite m] [Nonempty E] (μ : Measure Ω) : Prop where
  /-- Each count `K k` is measurable. -/
  measurable_count : ∀ k, Measurable (K k)
  /-- Each point `X k n` is measurable. -/
  measurable_point : ∀ k n, Measurable (X k n)
  /-- All counts and all points are jointly independent, phrased as one `iIndepFun` over the combined
  family `pointFamilyCombined K X` indexed by `ℕ ⊕ ℕ × ℕ`. -/
  indep : iIndepFun (pointFamilyCombined K X) μ
  /-- The count `K k` is Poisson-distributed with mean the `m`-mass of the `k`-th piece. -/
  law_count : ∀ k, HasLaw (K k) (poissonMeasure (m (prmPiece m k)).toNNReal) μ
  /-- Each point `X k n` is distributed as the normalized `k`-th piece law. -/
  law_point : ∀ k n, HasLaw (X k n) (prmPieceLaw m k) μ
end PointFamily
section Extractors
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω}
/-- For a fixed piece `k`, the points `X k ·` of a Poisson point family are jointly independent, read
off the combined `indep` field by precomposing the index with `n ↦ Sum.inr (k, n)`. -/
theorem IsPoissonPointFamily.iIndepFun_point_piece (hd : IsPoissonPointFamily K X m μ) (k : ℕ) :
    iIndepFun (fun n => X k n) μ := by
  have h := hd.indep.precomp (g := fun n => Sum.inr (k, n)) (fun a b hab => by simpa using hab)
  exact h
end Extractors
/-! ### Block independence of the point family
The counts and points of a piece `k` sit at combined-index positions `Sum.inl k` and
`Sum.inr (k, ·)`. Any two disjoint sets of combined-index positions carry independent sub-families,
by the joint `indep` field. The general splitting lemma below reads that independence off for two
arbitrary injections into the combined index whose images are disjoint; the count-versus-marks,
piece-versus-piece, and prefix-versus-next-block independences used by Campbell's formula, the
superposition step, and the compensated integral are all instances of it. -/
section BlockIndependence
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω}
/-- Every coordinate of the combined family is measurable: a count on `Sum.inl`, a point on
`Sum.inr`. -/
theorem IsPoissonPointFamily.measurable_pointFamilyCombined (hd : IsPoissonPointFamily K X m μ) :
    ∀ i, Measurable (pointFamilyCombined K X i)
  | Sum.inl k => hd.measurable_count k
  | Sum.inr p => hd.measurable_point p.1 p.2
/-- **Disjoint sub-families of the point family are independent.** For any two injections `φ`, `ψ`
into the combined index with disjoint images, the two processes obtained by reading the combined
family along `φ` and along `ψ` are independent. This is the single engine behind every
piece-block independence statement. -/
theorem IsPoissonPointFamily.indepFun_pointFamily_split [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {S T : Type} (φ : S → ℕ ⊕ ℕ × ℕ) (ψ : T → ℕ ⊕ ℕ × ℕ)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (hST : ∀ s t, φ s ≠ ψ t) :
    IndepFun (fun ω (i : S) => pointFamilyCombined K X (φ i) ω)
      (fun ω (j : T) => pointFamilyCombined K X (ψ j) ω) μ := by
  classical
  refine IndepFun.process_indepFun_process (fun i => hd.measurable_pointFamilyCombined (φ i))
    (fun j => hd.measurable_pointFamilyCombined (ψ j)) ?_
  intro I J
  set eφ : S ↪ ℕ ⊕ ℕ × ℕ := ⟨φ, hφ⟩ with heφ
  set eψ : T ↪ ℕ ⊕ ℕ × ℕ := ⟨ψ, hψ⟩ with heψ
  have hdisj : Disjoint (I.map eφ) (J.map eψ) := by
    rw [Finset.disjoint_left]
    rintro x hx1 hx2
    rw [Finset.mem_map] at hx1 hx2
    obtain ⟨a, -, rfl⟩ := hx1
    obtain ⟨c, -, hc⟩ := hx2
    exact hST a c hc.symm
  have key := hd.indep.indepFun_finset (I.map eφ) (J.map eψ) hdisj
    hd.measurable_pointFamilyCombined
  have hLmeas : Measurable
      (fun (g : (i : ↑(I.map eφ)) → pointFamilyIndexType E i.1) (i : I) =>
        g ⟨φ i, Finset.mem_map_of_mem eφ i.2⟩) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hRmeas : Measurable
      (fun (g : (j : ↑(J.map eψ)) → pointFamilyIndexType E j.1) (j : J) =>
        g ⟨ψ j, Finset.mem_map_of_mem eψ j.2⟩) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  exact key.comp hLmeas hRmeas
/-- **Count-versus-marks independence within a piece.** For a fixed piece `k`, the count `K k` is
independent of the whole sequence of points `X k ·` of that piece. -/
theorem IsPoissonPointFamily.indepFun_count_marks [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (k : ℕ) :
    IndepFun (K k) (fun ω n => X k n ω) μ := by
  have h := hd.indepFun_pointFamily_split (S := Unit) (T := ℕ)
    (fun _ => Sum.inl k) (fun n => Sum.inr (k, n)) (fun _ _ _ => rfl)
    (fun a b hab => by simpa using hab) (fun _ _ => by simp)
  exact h.comp (φ := fun g : Unit → ℕ => g ()) (ψ := id)
    (measurable_pi_apply _) measurable_id
/-- **Piece-versus-piece independence.** For distinct pieces `j ≠ k`, the count-and-marks block
`(K j, X j ·)` is independent of the block `(K k, X k ·)`. Composing with a measurable functional of
each block yields, in particular, independence of the piece sums; see `indepFun_pieceSum_pieceSum`. -/
theorem IsPoissonPointFamily.indepFun_piece_piece [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {j k : ℕ} (hjk : j ≠ k) :
    IndepFun (fun ω => (K j ω, fun n => X j n ω)) (fun ω => (K k ω, fun n => X k n ω)) μ := by
  have hφinj : Function.Injective (Sum.elim (fun _ : Unit => Sum.inl j)
      (fun n : ℕ => Sum.inr (j, n)) : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ) := by
    rintro (a | a) (b | b) hab <;> simp_all
  have hψinj : Function.Injective (Sum.elim (fun _ : Unit => Sum.inl k)
      (fun n : ℕ => Sum.inr (k, n)) : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ) := by
    rintro (a | a) (b | b) hab <;> simp_all
  have hST : ∀ (s t : Unit ⊕ ℕ),
      (Sum.elim (fun _ : Unit => Sum.inl j) (fun n : ℕ => Sum.inr (j, n)) s)
        ≠ (Sum.elim (fun _ : Unit => Sum.inl k) (fun n : ℕ => Sum.inr (k, n)) t) := by
    rintro (s | s) (t | t) <;> simp [hjk]
  have h := hd.indepFun_pointFamily_split (S := Unit ⊕ ℕ) (T := Unit ⊕ ℕ)
    (Sum.elim (fun _ => Sum.inl j) (fun n => Sum.inr (j, n)))
    (Sum.elim (fun _ => Sum.inl k) (fun n => Sum.inr (k, n))) hφinj hψinj hST
  have hextrL : Measurable
      (fun g : (i : Unit ⊕ ℕ) → pointFamilyIndexType E
          (Sum.elim (fun _ => Sum.inl j) (fun n => Sum.inr (j, n)) i) =>
        (g (Sum.inl ()), fun n => g (Sum.inr n))) :=
    (measurable_pi_apply (Sum.inl ())).prodMk
      (measurable_pi_lambda _ fun n => measurable_pi_apply (Sum.inr n))
  have hextrR : Measurable
      (fun g : (i : Unit ⊕ ℕ) → pointFamilyIndexType E
          (Sum.elim (fun _ => Sum.inl k) (fun n => Sum.inr (k, n)) i) =>
        (g (Sum.inl ()), fun n => g (Sum.inr n))) :=
    (measurable_pi_apply (Sum.inl ())).prodMk
      (measurable_pi_lambda _ fun n => measurable_pi_apply (Sum.inr n))
  exact h.comp hextrL hextrR
/-- The block index of a combined-index position: the piece it belongs to. -/
private def pointFamilyBlock : ℕ ⊕ ℕ × ℕ → ℕ := Sum.elim id Prod.fst
end BlockIndependence
/-! ### Piece sums, Campbell's formula, and the second-moment identity
For a fixed piece `k` and a test function `f`, the *piece sum* `pieceSum K X f k ω` is the sum of `f`
over the `K k ω` points of that piece. Campbell's formula computes its mean as the `m`-integral of
`f` over the piece; the second-moment identity computes `E[(pieceSum)²]` as
`∫ f² dm + (∫ f dm)²` over the piece. Both are proved by conditioning on the piece count `K k`: on
`{K k = j}` the piece sum is a fixed sum of `j` i.i.d. marks, and the count is independent of the
marks, so each conditional expectation factors; summing over `j` against the Poisson mean and second
factorial moment gives the result. -/
section PieceSum
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {k : ℕ}
/-- The **piece sum**: the sum of the test function `f` over the `K k ω` points of piece `k`. -/
noncomputable def pieceSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (f : E → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ n ∈ Finset.range (K k ω), f (X k n ω)
omit [Nonempty E] in
/-- The piece sum is measurable, since it is a countable-index composition of the measurable count
and the measurable points. -/
theorem measurable_pieceSum {f : E → ℝ} (hK : Measurable (K k))
    (hX : ∀ n, Measurable (X k n))
    (hf : Measurable f) : Measurable (pieceSum K X f k) := by
  have hP : Measurable (fun p : Ω × ℕ => ∑ n ∈ Finset.range p.2, f (X k n p.1)) :=
    measurable_from_prod_countable_left fun j =>
      Finset.measurable_sum (Finset.range j) fun n _ => hf.comp (hX n)
  exact hP.comp (measurable_id.prodMk hK)
/-- A test function integrable on a piece is integrable against that piece's normalized law: on a
positive-mass piece the law is a finite rescaling of the restriction, and on a zero-mass piece it is
a Dirac mass. -/
private theorem integrable_prmPieceLaw {g : E → ℝ} (hg : Measurable g)
    (hgi : Integrable g (m.restrict (prmPiece m k))) : Integrable g (prmPieceLaw m k) := by
  unfold prmPieceLaw
  split_ifs with h
  · exact integrable_dirac' hg.stronglyMeasurable (by finiteness)
  · exact (integrable_smul_measure (ENNReal.inv_ne_zero.2 (measure_prmPiece_lt_top).ne)
      (ENNReal.inv_ne_top.2 h)).mpr hgi
/-- Unconditional scaling bridge: the `m`-mass of the piece times the Bochner integral against the
normalized law is the set integral against `m`, including the zero-mass piece where both sides
vanish. -/
private theorem toReal_mul_integral_prmPieceLaw (g : E → ℝ) :
    (m (prmPiece m k)).toReal * ∫ x, g x ∂(prmPieceLaw m k) = ∫ x in prmPiece m k, g x ∂m := by
  by_cases h : m (prmPiece m k) = 0
  · rw [h, ENNReal.toReal_zero, zero_mul,
      show (∫ x in prmPiece m k, g x ∂m) = ∫ x, g x ∂(m.restrict (prmPiece m k)) from rfl,
      Measure.restrict_eq_zero.mpr h, integral_zero_measure]
  · rw [← integral_smul_prmPieceLaw h, smul_eq_mul]
/-- Each mark `X k n` integrates `g` to the piece-law integral, and the sum of the first `j` marks
therefore integrates to `j` times that value. -/
private theorem integral_marksSum_eq [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {g : E → ℝ} (hg : Measurable g) (hgi : Integrable g (m.restrict (prmPiece m k))) (j : ℕ) :
    ∫ ω, ∑ n ∈ Finset.range j, g (X k n ω) ∂μ = (j : ℝ) * ∫ x, g x ∂(prmPieceLaw m k) := by
  have hterm : ∀ n, Integrable (fun ω => g (X k n ω)) μ := by
    intro n
    have hI : Integrable g (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]; exact integrable_prmPieceLaw hg hgi
    exact hI.comp_measurable (hd.measurable_point k n)
  have heach : ∀ n, ∫ ω, g (X k n ω) ∂μ = ∫ x, g x ∂(prmPieceLaw m k) := by
    intro n
    rw [← (hd.law_point k n).map_eq,
      integral_map (hd.measurable_point k n).aemeasurable hg.aestronglyMeasurable]
  rw [integral_finsetSum _ (fun n _ => hterm n)]
  simp_rw [heach]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
/-- **Conditional Campbell factorization.** On the event `{K k = j}` the integral of the sum of the
first `j` marks factors as the probability of the event times `j` times the piece-law integral, by
independence of the count from the marks. -/
private theorem setIntegral_count_rangeSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {g : E → ℝ} (hg : Measurable g)
    (hgi : Integrable g (m.restrict (prmPiece m k))) (j : ℕ) :
    ∫ ω in {ω | K k ω = j}, ∑ n ∈ Finset.range j, g (X k n ω) ∂μ
      = μ.real {ω | K k ω = j} * ((j : ℝ) * ∫ x, g x ∂(prmPieceLaw m k)) := by
  have hmeas : MeasurableSet {ω | K k ω = j} :=
    hd.measurable_count k (measurableSet_singleton j)
  set Xk : Ω → (ℕ → E) := fun ω n => X k n ω with hXk
  have hXk_meas : Measurable Xk := measurable_pi_lambda _ fun n => hd.measurable_point k n
  set ψ : (ℕ → E) → ℝ := fun y => ∑ n ∈ Finset.range j, g (y n) with hψ
  have hψ_meas : Measurable ψ :=
    Finset.measurable_sum _ fun n _ => hg.comp (measurable_pi_apply n)
  have hcongr : ({ω | K k ω = j}).indicator (fun ω => ψ (Xk ω))
      = fun ω => (if K k ω = j then (1 : ℝ) else 0) * ψ (Xk ω) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : K k ω = j <;> simp [h]
  rw [← integral_indicator hmeas, hcongr,
    (hd.indepFun_count_marks k).integral_fun_comp_mul_comp
      (f := fun c : ℕ => if c = j then (1 : ℝ) else 0) (g := ψ)
      (hd.measurable_count k).aemeasurable hXk_meas.aemeasurable
      (measurable_of_countable _).aestronglyMeasurable hψ_meas.aestronglyMeasurable]
  have hfirst : ∫ ω, (if K k ω = j then (1 : ℝ) else 0) ∂μ = μ.real {ω | K k ω = j} := by
    have hrw : (fun ω => if K k ω = j then (1 : ℝ) else 0)
        = ({ω | K k ω = j}).indicator (fun _ => 1) := by
      funext ω; by_cases h : K k ω = j <;> simp [Set.mem_setOf_eq, h]
    rw [hrw, integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one]
  rw [hfirst]
  congr 1
  exact integral_marksSum_eq hd hg hgi j
/-- The probability of the piece-count event `{K k = j}` is the Poisson pmf at `j`. -/
private theorem measureReal_count_eq (hd : IsPoissonPointFamily K X m μ) (j : ℕ) :
    μ.real {ω | K k ω = j} = (poissonMeasure (m (prmPiece m k)).toNNReal).real {j} := by
  have h1 : μ {ω | K k ω = j} = poissonMeasure (m (prmPiece m k)).toNNReal {j} := by
    rw [show {ω | K k ω = j} = K k ⁻¹' {j} from rfl,
      ← Measure.map_apply (hd.measurable_count k) (measurableSet_singleton j), (hd.law_count k).map_eq]
  rw [measureReal_def, h1, ← measureReal_def]
/-- **Campbell's formula for a piece sum.** The mean of the piece sum is the `m`-integral of the test
function over the piece:
`E[∑_{n < K k} f(X k n)] = ∫_{piece k} f dm`. The zero-mass piece is handled inside: the count is
`0` almost surely and both sides vanish. -/
theorem integral_pieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {f : E → ℝ}
    (hf : Measurable f) (hfi : Integrable f (m.restrict (prmPiece m k))) :
    ∫ ω, pieceSum K X f k ω ∂μ = ∫ x in prmPiece m k, f x ∂m := by
  classical
  have habs : Measurable fun x => |f x| := continuous_abs.measurable.comp hf
  set rate := (m (prmPiece m k)).toNNReal with hrate
  set s : ℕ → Set Ω := fun j => {ω | K k ω = j} with hs
  have hs_meas : ∀ j, MeasurableSet (s j) := fun j =>
    hd.measurable_count k (measurableSet_singleton j)
  have hs_disj : Pairwise fun i j => Disjoint (s i) (s j) := by
    intro a b hab
    simp only [Set.disjoint_left, hs, Set.mem_setOf_eq]
    intro ω h1 h2; exact hab (h1 ▸ h2)
  have hunion : (⋃ j, s j) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨K k ω, rfl⟩
  have heqcell : ∀ j, Set.EqOn (pieceSum K X f k)
      (fun ω => ∑ n ∈ Finset.range j, f (X k n ω)) (s j) := by
    intro j ω hω
    show pieceSum K X f k ω = _
    rw [pieceSum, show K k ω = j from hω]
  have hGint : ∀ (g : E → ℝ), Measurable g → Integrable g (m.restrict (prmPiece m k)) → ∀ j,
      Integrable (fun ω => ∑ n ∈ Finset.range j, g (X k n ω)) μ := by
    intro g hg hgi j
    refine integrable_finsetSum _ fun n _ => ?_
    have hI : Integrable g (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]; exact integrable_prmPieceLaw hg hgi
    exact hI.comp_measurable (hd.measurable_point k n)
  have hi : ∀ j, IntegrableOn (pieceSum K X f k) (s j) μ := fun j =>
    ((hGint f hf hfi j).integrableOn).congr_fun (heqcell j).symm (hs_meas j)
  have hbound : ∀ j, ∫ x in s j, ‖pieceSum K X f k x‖ ∂μ
      ≤ (poissonMeasure rate).real {j} * ((j : ℝ) * ∫ x, |f x| ∂(prmPieceLaw m k)) := by
    intro j
    have hmono : ∫ x in s j, ‖pieceSum K X f k x‖ ∂μ
        ≤ ∫ x in s j, ∑ n ∈ Finset.range j, |f (X k n x)| ∂μ := by
      refine setIntegral_mono_on ((hi j).norm)
        ((hGint (fun x => |f x|) habs hfi.abs j).integrableOn) (hs_meas j) fun ω hω => ?_
      rw [Real.norm_eq_abs, show pieceSum K X f k ω = ∑ n ∈ Finset.range j, f (X k n ω) from
        heqcell j hω]
      exact Finset.abs_sum_le_sum_abs _ _
    calc ∫ x in s j, ‖pieceSum K X f k x‖ ∂μ
        ≤ ∫ x in s j, ∑ n ∈ Finset.range j, |f (X k n x)| ∂μ := hmono
      _ = (poissonMeasure rate).real {j} * ((j : ℝ) * ∫ x, |f x| ∂(prmPieceLaw m k)) := by
          rw [setIntegral_count_rangeSum hd habs hfi.abs j, measureReal_count_eq hd j]
  have hsummable : Summable fun j => ∫ x in s j, ‖pieceSum K X f k x‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _) hbound ?_
    have hexp : Summable fun (j : ℕ) => (∫ x, |f x| ∂(prmPieceLaw m k)) * ((j : ℝ) * (poissonMeasure rate).real {j}) :=
      ((poissonExpectation_hasSum rate).summable).mul_left _
    refine hexp.congr fun j => ?_
    ring
  have hInt : Integrable (pieceSum K X f k) μ := by
    have h := integrableOn_iUnion_of_summable_integral_norm hi hsummable
    rwa [hunion, integrableOn_univ] at h
  have hval := integral_iUnion hs_meas hs_disj (by rw [hunion]; exact hInt.integrableOn)
  rw [hunion, setIntegral_univ] at hval
  rw [hval]
  have hcellf : ∀ j, ∫ x in s j, pieceSum K X f k x ∂μ
      = (poissonMeasure rate).real {j} * ((j : ℝ) * ∫ x, f x ∂(prmPieceLaw m k)) := by
    intro j
    rw [setIntegral_congr_fun (hs_meas j) (heqcell j),
      setIntegral_count_rangeSum hd hf hfi j, measureReal_count_eq hd j]
  simp_rw [hcellf]
  have hfun : (fun j => (poissonMeasure rate).real {j} * ((j : ℝ) * ∫ x, f x ∂(prmPieceLaw m k)))
      = fun (j : ℕ) => (∫ x, f x ∂(prmPieceLaw m k)) * ((j : ℝ) * (poissonMeasure rate).real {j}) := by
    funext j; ring
  have hr : (rate : ℝ) = (m (prmPiece m k)).toReal := rfl
  rw [hfun, ((poissonExpectation_hasSum rate).mul_left (∫ x, f x ∂(prmPieceLaw m k))).tsum_eq, hr,
    mul_comm, toReal_mul_integral_prmPieceLaw (k := k) f]
/-- **General conditional factorization.** On `{K k = j}`, the integral of any measurable functional
of the marks of piece `k` factors as the probability of the event times the functional's integral,
by independence of the count from the marks. -/
private theorem setIntegral_count_marksFun [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (j : ℕ) {ψ : (ℕ → E) → ℝ} (hψ : Measurable ψ) :
    ∫ ω in {ω | K k ω = j}, ψ (fun n => X k n ω) ∂μ
      = μ.real {ω | K k ω = j} * ∫ ω, ψ (fun n => X k n ω) ∂μ := by
  have hmeas : MeasurableSet {ω | K k ω = j} :=
    hd.measurable_count k (measurableSet_singleton j)
  set Xk : Ω → (ℕ → E) := fun ω n => X k n ω with hXk
  have hXk_meas : Measurable Xk := measurable_pi_lambda _ fun n => hd.measurable_point k n
  have hcongr : ({ω | K k ω = j}).indicator (fun ω => ψ (Xk ω))
      = fun ω => (if K k ω = j then (1 : ℝ) else 0) * ψ (Xk ω) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : K k ω = j <;> simp [h]
  rw [← integral_indicator hmeas, hcongr,
    (hd.indepFun_count_marks k).integral_fun_comp_mul_comp
      (f := fun c : ℕ => if c = j then (1 : ℝ) else 0) (g := ψ)
      (hd.measurable_count k).aemeasurable hXk_meas.aemeasurable
      (measurable_of_countable _).aestronglyMeasurable hψ.aestronglyMeasurable]
  have hfirst : ∫ ω, (if K k ω = j then (1 : ℝ) else 0) ∂μ = μ.real {ω | K k ω = j} := by
    have hrw : (fun ω => if K k ω = j then (1 : ℝ) else 0)
        = ({ω | K k ω = j}).indicator (fun _ => 1) := by
      funext ω; by_cases h : K k ω = j <;> simp [Set.mem_setOf_eq, h]
    rw [hrw, integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one]
  rw [hfirst]
/-- The square of the sum of the first `j` marks is integrable: expanding the square gives a finite
sum of products of marks, each integrable (a squared mark on the diagonal, a product of independent
marks off it). -/
private theorem integrable_marksSum_sq [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {f : E → ℝ} (hf : Measurable f) (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k))) (j : ℕ) :
    Integrable (fun ω => (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2) μ := by
  classical
  have hInt_f : ∀ n, Integrable (fun ω => f (X k n ω)) μ := by
    intro n
    have hI : Integrable f (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]; exact integrable_prmPieceLaw hf hfi
    exact hI.comp_measurable (hd.measurable_point k n)
  have hInt_f2 : ∀ n, Integrable (fun ω => f (X k n ω) ^ 2) μ := by
    intro n
    have hI : Integrable (fun x => f x ^ 2) (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]; exact integrable_prmPieceLaw (hf.pow_const 2) hfi2
    exact hI.comp_measurable (hd.measurable_point k n)
  have hprod : ∀ n n', Integrable (fun ω => f (X k n ω) * f (X k n' ω)) μ := by
    intro n n'
    by_cases h : n = n'
    · subst h; simpa [pow_two] using hInt_f2 n
    · exact (((hd.iIndepFun_point_piece k).indepFun h).comp hf hf).integrable_mul
        (hInt_f n) (hInt_f n')
  have hexp : (fun ω => (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2)
      = fun ω => ∑ n ∈ Finset.range j, ∑ n' ∈ Finset.range j, f (X k n ω) * f (X k n' ω) := by
    funext ω; rw [pow_two, Finset.sum_mul_sum]
  rw [hexp]
  exact integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun n' _ => hprod n n'
/-- **Second moment of a fixed-length mark sum.** The mean square of the sum of the first `j` i.i.d.
marks is `j * E[f^2] + j (j-1) * E[f]^2`, against the piece law. Expanding the square, diagonal terms
give `E[f^2]` and off-diagonal terms factor as `E[f]^2` by independence. -/
private theorem integral_marksSum_sq_eq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {f : E → ℝ} (hf : Measurable f)
    (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k))) (j : ℕ) :
    ∫ ω, (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2 ∂μ
      = (j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k))
        + (j : ℝ) * ((j : ℝ) - 1) * (∫ x, f x ∂(prmPieceLaw m k)) ^ 2 := by
  classical
  set A := ∫ x, f x ^ 2 ∂(prmPieceLaw m k) with hA
  set B := ∫ x, f x ∂(prmPieceLaw m k) with hB
  have hf2m : Measurable (fun x => f x ^ 2) := hf.pow_const 2
  have hInt_f : ∀ n, Integrable (fun ω => f (X k n ω)) μ := by
    intro n
    have hI : Integrable f (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]; exact integrable_prmPieceLaw hf hfi
    exact hI.comp_measurable (hd.measurable_point k n)
  have hInt_f2 : ∀ n, Integrable (fun ω => f (X k n ω) ^ 2) μ := by
    intro n
    have hI : Integrable (fun x => f x ^ 2) (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]; exact integrable_prmPieceLaw hf2m hfi2
    exact hI.comp_measurable (hd.measurable_point k n)
  have heach_f : ∀ n, ∫ ω, f (X k n ω) ∂μ = B := by
    intro n
    rw [hB, ← (hd.law_point k n).map_eq,
      integral_map (hd.measurable_point k n).aemeasurable hf.aestronglyMeasurable]
  have heach_f2 : ∀ n, ∫ ω, f (X k n ω) ^ 2 ∂μ = A := by
    intro n
    rw [hA, ← (hd.law_point k n).map_eq,
      integral_map (hd.measurable_point k n).aemeasurable hf2m.aestronglyMeasurable]
  have hindep : ∀ n n', n ≠ n' →
      IndepFun (fun ω => f (X k n ω)) (fun ω => f (X k n' ω)) μ :=
    fun n n' h => ((hd.iIndepFun_point_piece k).indepFun h).comp hf hf
  have hprod : ∀ n n', Integrable (fun ω => f (X k n ω) * f (X k n' ω)) μ := by
    intro n n'
    by_cases h : n = n'
    · subst h; simpa [pow_two] using hInt_f2 n
    · exact (hindep n n' h).integrable_mul (hInt_f n) (hInt_f n')
  have hprod_val : ∀ n n', ∫ ω, f (X k n ω) * f (X k n' ω) ∂μ
      = if n = n' then A else B ^ 2 := by
    intro n n'
    by_cases h : n = n'
    · subst h; rw [if_pos rfl]; simp_rw [← pow_two]; exact heach_f2 n
    · rw [if_neg h, (hindep n n' h).integral_fun_mul_eq_mul_integral
        (hInt_f n).aestronglyMeasurable (hInt_f n').aestronglyMeasurable, heach_f n, heach_f n',
        ← pow_two]
  have hexp : (fun ω => (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2)
      = fun ω => ∑ n ∈ Finset.range j, ∑ n' ∈ Finset.range j, f (X k n ω) * f (X k n' ω) := by
    funext ω; rw [pow_two, Finset.sum_mul_sum]
  rw [hexp, integral_finsetSum _ fun n _ =>
    integrable_finsetSum _ fun n' _ => hprod n n']
  have hinner : ∀ n, ∫ ω, ∑ n' ∈ Finset.range j, f (X k n ω) * f (X k n' ω) ∂μ
      = ∑ n' ∈ Finset.range j, (if n = n' then A else B ^ 2) := by
    intro n
    rw [integral_finsetSum _ fun n' _ => hprod n n']
    exact Finset.sum_congr rfl fun n' _ => hprod_val n n'
  simp_rw [hinner]
  have hin : ∀ n ∈ Finset.range j,
      (∑ n' ∈ Finset.range j, (if n = n' then A else B ^ 2)) = A + ((j : ℝ) - 1) * B ^ 2 := by
    intro n hn
    have hrw : ∀ n', (if n = n' then A else B ^ 2)
        = B ^ 2 + (if n = n' then (A - B ^ 2) else 0) := by
      intro n'; split_ifs <;> ring
    simp_rw [hrw]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.sum_ite_eq (Finset.range j) n (fun _ => A - B ^ 2), if_pos hn]
    ring
  rw [Finset.sum_congr rfl hin, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring
/-- Per-cell second moment: on `{K k = j}` the mean square of the piece sum is the Poisson pmf at `j`
times the fixed-length second moment `j * E[f^2] + j (j-1) * E[f]^2`. -/
private theorem setIntegral_sq_pieceSum_eq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {f : E → ℝ} (hf : Measurable f)
    (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k))) (j : ℕ) :
    ∫ x in {ω | K k ω = j}, (pieceSum K X f k x) ^ 2 ∂μ
      = (poissonMeasure (m (prmPiece m k)).toNNReal).real {j}
        * ((j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k))
          + (j : ℝ) * ((j : ℝ) - 1) * (∫ x, f x ∂(prmPieceLaw m k)) ^ 2) := by
  have hψmeas : Measurable (fun y : ℕ → E => (∑ n ∈ Finset.range j, f (y n)) ^ 2) :=
    (Finset.measurable_sum _ fun n _ => hf.comp (measurable_pi_apply n)).pow_const 2
  calc ∫ x in {ω | K k ω = j}, (pieceSum K X f k x) ^ 2 ∂μ
      = ∫ x in {ω | K k ω = j},
          (fun y : ℕ → E => (∑ n ∈ Finset.range j, f (y n)) ^ 2) (fun n => X k n x) ∂μ := by
        refine setIntegral_congr_fun (hd.measurable_count k (measurableSet_singleton j)) ?_
        intro ω hω; show (pieceSum K X f k ω) ^ 2 = _
        rw [pieceSum, show K k ω = j from hω]
    _ = μ.real {ω | K k ω = j}
          * ∫ x, (fun y : ℕ → E => (∑ n ∈ Finset.range j, f (y n)) ^ 2) (fun n => X k n x) ∂μ :=
        setIntegral_count_marksFun hd j hψmeas
    _ = (poissonMeasure (m (prmPiece m k)).toNNReal).real {j}
          * ((j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k))
            + (j : ℝ) * ((j : ℝ) - 1) * (∫ x, f x ∂(prmPieceLaw m k)) ^ 2) := by
        rw [measureReal_count_eq hd j]
        congr 1
        exact integral_marksSum_sq_eq hd hf hfi hfi2 j
/-- The square of a piece sum is integrable: its cell integrals are dominated by the Poisson first
and second factorial moments of the count, which are summable. -/
theorem integrable_sq_pieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {f : E → ℝ} (hf : Measurable f) (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k))) :
    Integrable (fun ω => (pieceSum K X f k ω) ^ 2) μ := by
  classical
  set rate := (m (prmPiece m k)).toNNReal with hrate
  set s : ℕ → Set Ω := fun j => {ω | K k ω = j} with hs
  have hs_meas : ∀ j, MeasurableSet (s j) := fun j =>
    hd.measurable_count k (measurableSet_singleton j)
  have hunion : (⋃ j, s j) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨K k ω, rfl⟩
  have heqcell : ∀ j, Set.EqOn (fun ω => (pieceSum K X f k ω) ^ 2)
      (fun ω => (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2) (s j) := by
    intro j ω hω; show (pieceSum K X f k ω) ^ 2 = _; rw [pieceSum, show K k ω = j from hω]
  have hi : ∀ j, IntegrableOn (fun ω => (pieceSum K X f k ω) ^ 2) (s j) μ := fun j =>
    ((integrable_marksSum_sq hd hf hfi hfi2 j).integrableOn).congr_fun (heqcell j).symm (hs_meas j)
  have hsummable : Summable fun j => ∫ x in s j, ‖(pieceSum K X f k x) ^ 2‖ ∂μ := by
    have heqnorm : (fun j => ∫ x in s j, ‖(pieceSum K X f k x) ^ 2‖ ∂μ)
        = fun j => (poissonMeasure rate).real {j}
          * ((j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k))
            + (j : ℝ) * ((j : ℝ) - 1) * (∫ x, f x ∂(prmPieceLaw m k)) ^ 2) := by
      funext j
      rw [← setIntegral_sq_pieceSum_eq hd hf hfi hfi2 j]
      exact setIntegral_congr_fun (hs_meas j) fun ω _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [heqnorm]
    have h1 : Summable fun (j : ℕ) =>
        (∫ x, f x ^ 2 ∂(prmPieceLaw m k)) * ((j : ℝ) * (poissonMeasure rate).real {j}) :=
      ((poissonExpectation_hasSum rate).summable).mul_left _
    have h2 : Summable fun (j : ℕ) => (∫ x, f x ∂(prmPieceLaw m k)) ^ 2
        * (((j : ℝ) * ((j : ℝ) - 1)) * (poissonMeasure rate).real {j}) :=
      ((poissonFactorialMoment2_hasSum rate).summable).mul_left _
    exact (h1.add h2).congr fun j => by ring
  have h := integrableOn_iUnion_of_summable_integral_norm hi hsummable
  rwa [hunion, integrableOn_univ] at h
/-- **Second-moment identity for a piece sum.** The mean square of the piece sum is
`∫_{piece k} f^2 dm + (∫_{piece k} f dm)^2`; the zero-mass piece is handled inside. -/
theorem integral_sq_pieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {f : E → ℝ} (hf : Measurable f) (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k))) :
    ∫ ω, (pieceSum K X f k ω) ^ 2 ∂μ
      = (∫ x in prmPiece m k, f x ^ 2 ∂m) + (∫ x in prmPiece m k, f x ∂m) ^ 2 := by
  classical
  set rate := (m (prmPiece m k)).toNNReal with hrate
  set s : ℕ → Set Ω := fun j => {ω | K k ω = j} with hs
  have hs_meas : ∀ j, MeasurableSet (s j) := fun j =>
    hd.measurable_count k (measurableSet_singleton j)
  have hs_disj : Pairwise fun i j => Disjoint (s i) (s j) := by
    intro a b hab
    simp only [Set.disjoint_left, hs, Set.mem_setOf_eq]
    intro ω h1 h2; exact hab (h1 ▸ h2)
  have hunion : (⋃ j, s j) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨K k ω, rfl⟩
  have hInt := integrable_sq_pieceSum hd hf hfi hfi2
  have hval := integral_iUnion hs_meas hs_disj (by rw [hunion]; exact hInt.integrableOn)
  rw [hunion, setIntegral_univ] at hval
  rw [hval]
  have hcell : ∀ j, ∫ x in s j, (pieceSum K X f k x) ^ 2 ∂μ
      = (poissonMeasure rate).real {j}
        * ((j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k))
          + (j : ℝ) * ((j : ℝ) - 1) * (∫ x, f x ∂(prmPieceLaw m k)) ^ 2) :=
    fun j => setIntegral_sq_pieceSum_eq hd hf hfi hfi2 j
  simp_rw [hcell]
  set A := ∫ x, f x ^ 2 ∂(prmPieceLaw m k) with hA
  set B := ∫ x, f x ∂(prmPieceLaw m k) with hB
  have hHS : HasSum
      (fun j => (poissonMeasure rate).real {j} * ((j : ℝ) * A + (j : ℝ) * ((j : ℝ) - 1) * B ^ 2))
      (A * (rate : ℝ) + B ^ 2 * (rate : ℝ) ^ 2) := by
    have h1 := (poissonExpectation_hasSum rate).mul_left A
    have h2 := (poissonFactorialMoment2_hasSum rate).mul_left (B ^ 2)
    have hfun : (fun j => (poissonMeasure rate).real {j} * ((j : ℝ) * A + (j : ℝ) * ((j : ℝ) - 1) * B ^ 2))
        = fun (j : ℕ) => A * ((j : ℝ) * (poissonMeasure rate).real {j})
          + B ^ 2 * (((j : ℝ) * ((j : ℝ) - 1)) * (poissonMeasure rate).real {j}) := by
      funext j; ring
    rw [hfun]; exact h1.add h2
  rw [hHS.tsum_eq]
  have hr : (rate : ℝ) = (m (prmPiece m k)).toReal := rfl
  have hAeq : (rate : ℝ) * A = ∫ x in prmPiece m k, f x ^ 2 ∂m := by
    rw [hr, hA]; exact toReal_mul_integral_prmPieceLaw (fun x => f x ^ 2)
  have hBeq : (rate : ℝ) * B = ∫ x in prmPiece m k, f x ∂m := by
    rw [hr, hB]; exact toReal_mul_integral_prmPieceLaw f
  rw [mul_comm A (rate : ℝ), hAeq, show B ^ 2 * (rate : ℝ) ^ 2 = ((rate : ℝ) * B) ^ 2 from by ring,
    hBeq]
/-- **Independence of piece sums of distinct pieces.** For `j ≠ k`, the piece sum over piece `j` is
independent of the piece sum over piece `k`: each is a measurable functional of its own block, and
the blocks are independent. -/
theorem indepFun_pieceSum_pieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g) {j k : ℕ} (hjk : j ≠ k) :
    IndepFun (pieceSum K X f j) (pieceSum K X g k) μ := by
  have hmapf : Measurable fun p : ℕ × (ℕ → E) => ∑ n ∈ Finset.range p.1, f (p.2 n) := by
    have h : Measurable fun p : (ℕ → E) × ℕ => ∑ n ∈ Finset.range p.2, f (p.1 n) :=
      measurable_from_prod_countable_left fun y =>
        Finset.measurable_sum (Finset.range y) fun n _ => hf.comp (measurable_pi_apply n)
    exact h.comp measurable_swap
  have hmapg : Measurable fun p : ℕ × (ℕ → E) => ∑ n ∈ Finset.range p.1, g (p.2 n) := by
    have h : Measurable fun p : (ℕ → E) × ℕ => ∑ n ∈ Finset.range p.2, g (p.1 n) :=
      measurable_from_prod_countable_left fun y =>
        Finset.measurable_sum (Finset.range y) fun n _ => hg.comp (measurable_pi_apply n)
    exact h.comp measurable_swap
  exact (hd.indepFun_piece_piece hjk).comp hmapf hmapg
end PieceSum
/-! ### Thinning and within-piece factorization
The number of piece-`k` points that land in a set `A` is the *thinned count* `thinnedCount K X A k`.
The engine behind its distribution is the **probability-generating-function identity**
`E[∏_{n < K k} w (X k n)] = exp (m (piece k) · (∫ w d(pieceLaw k) − 1))` for any bounded measurable
`w : E → ℂ` (`integral_pieceProd_eq_exp`), proved by the same cell-partition over `{K k = j}` used
for Campbell's formula, this time with a bounded integrand. Feeding in the indicator-shaped weights
`w x = z ^ 1_A(x)` and reading the resulting characteristic function against
`charFun_poissonMeasure_eq` yields both Poisson **thinning** (`map_thinnedCount`) and the
**within-piece independence** of thinned counts on disjoint sets
(`indepFun_thinnedCount_thinnedCount`). -/
section Thinning
open Complex
open scoped NNReal
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {k : ℕ} {A B : Set E}
/-- **Poisson probability-generating series (complex form).** `∑ⱼ P(N = j) · wʲ = exp(λ(w − 1))` for
any complex `w`; the analytic identity behind the piece pgf identity. Re-derived here rather than
imported from the compound-Poisson development. -/
private lemma tsum_poissonMeasure_real_mul_cpow (lam : ℝ≥0) (w : ℂ) :
    ∑' j : ℕ, ((poissonMeasure lam).real {j} : ℂ) * w ^ j = Complex.exp ((lam : ℝ) * (w - 1)) := by
  have hterm : ∀ j : ℕ, ((poissonMeasure lam).real {j} : ℂ) * w ^ j
      = (Real.exp (-(lam : ℝ)) : ℂ) * (((lam : ℝ) * w) ^ j / (Nat.factorial j : ℂ)) := by
    intro j
    simp only [poissonMeasure_real_singleton]
    push_cast
    rw [mul_pow]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hsum := NormedSpace.expSeries_div_hasSum_exp (((lam : ℝ) : ℂ) * w)
  rw [hsum.tsum_eq, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring
/-- Constant-branch product of a two-valued `if`: `∏ᵢ (if p i then z else 1) = z ^ #{i : p i}`. -/
private lemma prod_ite_const {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] (z : ℂ) :
    ∏ i ∈ s, (if p i then z else 1) = z ^ (s.filter p).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
/-- Integral of a complex-constant indicator, stated as a plain product to avoid the noncanonical
`ℝ`-on-`ℂ` scalar action that `integral_indicator_const` exposes: since `Complex.real_smul` is
`rfl`, the residual `μ.real s • c` closes by definitional unfolding via `exact`. -/
private lemma integral_indicator_const_complex {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {s : Set α} (c : ℂ) (hs : MeasurableSet s) :
    ∫ x, s.indicator (fun _ => c) x ∂ν = (ν.real s : ℂ) * c := by
  rw [integral_indicator_const c hs]; exact Complex.real_smul
open Classical in
/-- The **thinned count**: the number of the `K k ω` points of piece `k` that land in `A`. -/
noncomputable def thinnedCount (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (A : Set E) (k : ℕ) (ω : Ω) :
    ℕ := ((Finset.range (K k ω)).filter fun n => X k n ω ∈ A).card
omit [Nonempty E] in
/-- The thinned count is measurable: it is a countable-index sum of the measurable point-membership
indicators, capped by the measurable count. -/
theorem measurable_thinnedCount (hK : Measurable (K k)) (hX : ∀ n, Measurable (X k n))
    (hA : MeasurableSet A) : Measurable (thinnedCount K X A k) := by
  classical
  have hcard : thinnedCount K X A k
      = fun ω => ∑ n ∈ Finset.range (K k ω), (if X k n ω ∈ A then (1 : ℕ) else 0) := by
    funext ω; rw [thinnedCount, Finset.card_filter]
  rw [hcard]
  have hp : Measurable
      fun p : Ω × ℕ => ∑ n ∈ Finset.range p.2, (if X k n p.1 ∈ A then (1 : ℕ) else 0) :=
    measurable_from_prod_countable_left fun j =>
      Finset.measurable_sum (Finset.range j) fun n _ =>
        Measurable.ite (hX n hA) measurable_const measurable_const
  exact hp.comp (measurable_id.prodMk hK)
/-- Each mark contributes a factor `∫ w d(pieceLaw k)`, so the product of the first `j` marks
integrates to its `j`-th power, by within-piece i.i.d. independence. -/
private theorem integral_marksProd_eq [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {w : E → ℂ} (hw : Measurable w) (j : ℕ) :
    ∫ ω, ∏ n ∈ Finset.range j, w (X k n ω) ∂μ = (∫ x, w x ∂(prmPieceLaw m k)) ^ j := by
  have hZ : iIndepFun (fun i : Fin j => X k (i : ℕ)) μ :=
    (hd.iIndepFun_point_piece k).precomp Fin.val_injective
  have hfun : (fun ω => ∏ n ∈ Finset.range j, w (X k n ω))
      = fun ω => ∏ i : Fin j, w (X k (i : ℕ) ω) := by
    funext ω; exact (Fin.prod_univ_eq_prod_range (fun n => w (X k n ω)) j).symm
  rw [hfun]
  rw [show (∫ ω, ∏ i : Fin j, w (X k (i : ℕ) ω) ∂μ)
        = ∏ i : Fin j, ∫ ω, w (X k (i : ℕ) ω) ∂μ from
      iIndepFun.integral_fun_prod_comp (f := fun _ : Fin j => w) hZ
        (fun i => (hd.measurable_point k (i : ℕ)).aemeasurable)
        (fun _ => hw.aestronglyMeasurable)]
  have heach : ∀ i : Fin j, ∫ ω, w (X k (i : ℕ) ω) ∂μ = ∫ x, w x ∂(prmPieceLaw m k) := by
    intro i
    rw [← (hd.law_point k (i : ℕ)).map_eq,
      integral_map (hd.measurable_point k (i : ℕ)).aemeasurable hw.aestronglyMeasurable]
  simp_rw [heach]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
/-- **Conditional pgf factorization (complex).** On `{K k = j}`, the integral of a measurable complex
functional of the marks factors as the probability of the event times its integral. -/
private theorem setIntegral_count_marksFun_complex [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (j : ℕ) {ψ : (ℕ → E) → ℂ} (hψ : Measurable ψ) :
    ∫ ω in {ω | K k ω = j}, ψ (fun n => X k n ω) ∂μ
      = (μ.real {ω | K k ω = j} : ℂ) * ∫ ω, ψ (fun n => X k n ω) ∂μ := by
  have hmeas : MeasurableSet {ω | K k ω = j} :=
    hd.measurable_count k (measurableSet_singleton j)
  have hXk_meas : Measurable (fun ω (n : ℕ) => X k n ω) :=
    measurable_pi_lambda _ fun n => hd.measurable_point k n
  have hcongr : ({ω | K k ω = j}).indicator (fun ω => ψ (fun n => X k n ω))
      = fun ω => (if K k ω = j then (1 : ℂ) else 0) * ψ (fun n => X k n ω) := by
    funext ω; simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : K k ω = j <;> simp [h]
  rw [← integral_indicator hmeas, hcongr]
  simp only []
  rw [show (∫ ω, (if K k ω = j then (1 : ℂ) else 0) * ψ (fun n => X k n ω) ∂μ)
        = (∫ ω, (if K k ω = j then (1 : ℂ) else 0) ∂μ) * ∫ ω, ψ (fun n => X k n ω) ∂μ from
      (hd.indepFun_count_marks k).integral_fun_comp_mul_comp
        (f := fun c : ℕ => if c = j then (1 : ℂ) else 0) (g := ψ)
        (hd.measurable_count k).aemeasurable hXk_meas.aemeasurable
        (measurable_of_countable _).aestronglyMeasurable hψ.aestronglyMeasurable]
  have hfirst : ∫ ω, (if K k ω = j then (1 : ℂ) else 0) ∂μ = (μ.real {ω | K k ω = j} : ℂ) := by
    have hrw : (fun ω => if K k ω = j then (1 : ℂ) else 0)
        = ({ω | K k ω = j}).indicator (fun _ => 1) := by
      funext ω; by_cases h : K k ω = j <;> simp [Set.mem_setOf_eq, h]
    rw [hrw, integral_indicator_const_complex (1 : ℂ) hmeas, mul_one]
  rw [hfirst]
/-- **The piece pgf identity.** For any bounded measurable `w : E → ℂ`,
`E[∏_{n < K k} w (X k n)] = exp (m (piece k) · (∫ w d(pieceLaw k) − 1))`. Proved by conditioning on
the count `K k`: on `{K k = j}` the product is a fixed i.i.d. product integrating to
`P(K k = j) · (∫ w)ʲ`, and summing the Poisson pgf series closes it. The zero-mass piece is handled
uniformly: both sides collapse to `1`. -/
theorem integral_pieceProd_eq_exp [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {w : E → ℂ} (hw : Measurable w) (hbdd : ∀ x, ‖w x‖ ≤ 1) :
    ∫ ω, ∏ n ∈ Finset.range (K k ω), w (X k n ω) ∂μ
      = Complex.exp ((m (prmPiece m k)).toReal * ((∫ x, w x ∂(prmPieceLaw m k)) - 1)) := by
  classical
  set s : ℕ → Set Ω := fun j => {ω | K k ω = j} with hs
  have hs_meas : ∀ j, MeasurableSet (s j) := fun j =>
    hd.measurable_count k (measurableSet_singleton j)
  have hs_disj : Pairwise fun i j => Disjoint (s i) (s j) := by
    intro a b hab
    simp only [Set.disjoint_left, hs, Set.mem_setOf_eq]
    intro ω h1 h2; exact hab (h1 ▸ h2)
  have hunion : (⋃ j, s j) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨K k ω, rfl⟩
  have hPmeas : Measurable fun ω => ∏ n ∈ Finset.range (K k ω), w (X k n ω) := by
    have hp : Measurable fun p : Ω × ℕ => ∏ n ∈ Finset.range p.2, w (X k n p.1) :=
      measurable_from_prod_countable_left fun j =>
        Finset.measurable_prod (Finset.range j) fun n _ => hw.comp (hd.measurable_point k n)
    exact hp.comp (measurable_id.prodMk (hd.measurable_count k))
  have hbound : ∀ ω, ‖∏ n ∈ Finset.range (K k ω), w (X k n ω)‖ ≤ 1 := by
    intro ω
    calc ‖∏ n ∈ Finset.range (K k ω), w (X k n ω)‖
        = ∏ n ∈ Finset.range (K k ω), ‖w (X k n ω)‖ := norm_prod _ _
      _ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hbdd _)
  have hInt : Integrable (fun ω => ∏ n ∈ Finset.range (K k ω), w (X k n ω)) μ :=
    (integrable_const (1 : ℝ)).mono' hPmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hval := integral_iUnion (f := fun ω => ∏ n ∈ Finset.range (K k ω), w (X k n ω))
    hs_meas hs_disj (by rw [hunion]; exact hInt.integrableOn)
  rw [hunion, setIntegral_univ] at hval
  rw [hval]
  have hcell : ∀ j, ∫ ω in s j, ∏ n ∈ Finset.range (K k ω), w (X k n ω) ∂μ
      = ((poissonMeasure (m (prmPiece m k)).toNNReal).real {j} : ℂ) * (∫ x, w x ∂(prmPieceLaw m k)) ^ j := by
    intro j
    have hψmeas : Measurable (fun y : ℕ → E => ∏ n ∈ Finset.range j, w (y n)) :=
      Finset.measurable_prod _ fun n _ => hw.comp (measurable_pi_apply n)
    have hEq : ∫ ω in s j, ∏ n ∈ Finset.range (K k ω), w (X k n ω) ∂μ
        = ∫ ω in s j, (fun y : ℕ → E => ∏ n ∈ Finset.range j, w (y n)) (fun n => X k n ω) ∂μ := by
      refine setIntegral_congr_fun (hs_meas j) fun ω hω => ?_
      show (∏ n ∈ Finset.range (K k ω), w (X k n ω)) = ∏ n ∈ Finset.range j, w (X k n ω)
      rw [show K k ω = j from hω]
    rw [hEq, setIntegral_count_marksFun_complex hd j hψmeas, measureReal_count_eq hd j]
    congr 1
    exact integral_marksProd_eq hd hw j
  simp_rw [hcell]
  exact tsum_poissonMeasure_real_mul_cpow (m (prmPiece m k)).toNNReal (∫ x, w x ∂(prmPieceLaw m k))
/-- The mass bridge for thinning: `m (piece k) · pieceLaw k (A) = m (piece k ∩ A)`. -/
private lemma toReal_mul_real_prmPieceLaw (hA : MeasurableSet A) :
    (m (prmPiece m k)).toReal * (prmPieceLaw m k).real A = (m (prmPiece m k ∩ A)).toReal := by
  by_cases h : m (prmPiece m k) = 0
  · have h2 : m (prmPiece m k ∩ A) = 0 := measure_mono_null Set.inter_subset_left h
    rw [h, ENNReal.toReal_zero, zero_mul, h2, ENNReal.toReal_zero]
  · rw [prmPieceLaw_of_ne_zero h, measureReal_def, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hA, ENNReal.toReal_mul, ENNReal.toReal_inv, ← mul_assoc,
      mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨h, measure_prmPiece_lt_top.ne⟩), one_mul,
      Set.inter_comm]
/-- The pgf identity at the indicator weight `w x = z ^ 1_A(x)`:
`E[z ^ (thinnedCount A)] = exp (m (piece k ∩ A) · (z − 1))`, for `‖z‖ ≤ 1`. -/
private lemma integral_pow_thinnedCount [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ∫ ω, z ^ (thinnedCount K X A k ω) ∂μ
      = Complex.exp ((m (prmPiece m k ∩ A)).toReal * (z - 1)) := by
  classical
  set w : E → ℂ := fun x => if x ∈ A then z else 1 with hw_def
  have hwmeas : Measurable w := Measurable.ite hA measurable_const measurable_const
  have hwbdd : ∀ x, ‖w x‖ ≤ 1 := by
    intro x; simp only [hw_def]; split_ifs with hx
    · exact hz
    · simp
  have hprod : ∀ ω, z ^ (thinnedCount K X A k ω) = ∏ n ∈ Finset.range (K k ω), w (X k n ω) := by
    intro ω
    simp only [hw_def]
    rw [prod_ite_const (Finset.range (K k ω)) (fun n => X k n ω ∈ A) z, thinnedCount]
  simp_rw [hprod]
  rw [integral_pieceProd_eq_exp hd hwmeas hwbdd]
  congr 1
  have hint : ∫ x, w x ∂(prmPieceLaw m k) = 1 + (z - 1) * ((prmPieceLaw m k).real A) := by
    have hwrw : w = fun x => (1 : ℂ) + A.indicator (fun _ => z - 1) x := by
      funext x
      by_cases hx : x ∈ A
      · simp only [hw_def, Set.indicator_of_mem hx, if_pos hx]; ring
      · simp only [hw_def, Set.indicator_of_notMem hx, if_neg hx]; ring
    have hone : ∫ _ : E, (1 : ℂ) ∂(prmPieceLaw m k) = 1 := by simp
    rw [hwrw, integral_add (integrable_const 1) ((integrable_const (z - 1)).indicator hA),
      hone, integral_indicator_const_complex (z - 1) hA]
    ring
  rw [hint]
  have halg : ((m (prmPiece m k)).toReal : ℂ) * ((1 + (z - 1) * ((prmPieceLaw m k).real A)) - 1)
      = (((m (prmPiece m k)).toReal * (prmPieceLaw m k).real A : ℝ) : ℂ) * (z - 1) := by
    push_cast; ring
  rw [halg, toReal_mul_real_prmPieceLaw hA]
/-- The `ℕ → ℝ` cast is a measurable embedding: injective on the countable discrete space `ℕ`. -/
private lemma measurableEmbedding_natCast : MeasurableEmbedding (Nat.cast : ℕ → ℝ) :=
  ⟨Nat.cast_injective, measurable_from_top, fun {t} _ => (t.to_countable.image _).measurableSet⟩
/-- The characteristic function of the `ℝ`-pushforward of the thinned count, from the pgf identity. -/
private lemma charFun_natCast_thinnedCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (ξ : ℝ) :
    charFun ((μ.map (thinnedCount K X A k)).map (Nat.cast : ℕ → ℝ)) ξ
      = Complex.exp ((m (prmPiece m k ∩ A)).toReal * (Complex.exp (↑ξ * I) - 1)) := by
  have hTA : Measurable (thinnedCount K X A k) :=
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hA
  rw [charFun_apply_real,
    integral_map (φ := (Nat.cast : ℕ → ℝ)) measurable_from_top.aemeasurable (by fun_prop),
    integral_map (φ := thinnedCount K X A k) hTA.aemeasurable (by fun_prop)]
  have hpow : ∀ ω, Complex.exp (↑ξ * ↑((thinnedCount K X A k ω : ℝ)) * I)
      = (Complex.exp (↑ξ * I)) ^ (thinnedCount K X A k ω) := by
    intro ω
    rw [show (↑ξ : ℂ) * ↑((thinnedCount K X A k ω : ℝ)) * I
        = ↑(thinnedCount K X A k ω) * (↑ξ * I) from by push_cast; ring, Complex.exp_nat_mul]
  simp_rw [hpow]
  exact integral_pow_thinnedCount hd hA (Complex.exp (↑ξ * I))
    (le_of_eq (Complex.norm_exp_ofReal_mul_I ξ))
/-- **Poisson thinning within a piece.** The count of piece-`k` points landing in a measurable set
`A` is Poisson-distributed with mean `m (piece k ∩ A)`. Read off the pgf identity by matching the
characteristic function of the `ℝ`-pushforward against `charFun_poissonMeasure_eq` and descending
along the injective `ℕ → ℝ` cast. -/
theorem map_thinnedCount [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) :
    μ.map (thinnedCount K X A k) = poissonMeasure (m (prmPiece m k ∩ A)).toNNReal := by
  have hTA : Measurable (thinnedCount K X A k) :=
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hA
  haveI : IsProbabilityMeasure (μ.map (thinnedCount K X A k)) :=
    Measure.isProbabilityMeasure_map hTA.aemeasurable
  have hcast : (μ.map (thinnedCount K X A k)).map (Nat.cast : ℕ → ℝ)
      = (poissonMeasure (m (prmPiece m k ∩ A)).toNNReal).map (Nat.cast : ℕ → ℝ) := by
    haveI : IsProbabilityMeasure ((μ.map (thinnedCount K X A k)).map (Nat.cast : ℕ → ℝ)) :=
      Measure.isProbabilityMeasure_map measurable_from_top.aemeasurable
    haveI : IsProbabilityMeasure ((poissonMeasure (m (prmPiece m k ∩ A)).toNNReal).map
        (Nat.cast : ℕ → ℝ)) := Measure.isProbabilityMeasure_map measurable_from_top.aemeasurable
    apply Measure.ext_of_charFun
    funext ξ
    rw [charFun_natCast_thinnedCount hd hA ξ, charFun_poissonMeasure_eq,
      ENNReal.coe_toNNReal_eq_toReal]
  exact measurableEmbedding_natCast.map_injective hcast
end Thinning
end ProbabilityTheory


