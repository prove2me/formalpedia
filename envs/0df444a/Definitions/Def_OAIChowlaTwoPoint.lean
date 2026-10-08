-- Prove2me | Definitions.Def_OAIChowlaTwoPoint
-- name    : OAIChowlaTwoPoint
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T00:41:30.005053+00:00
-- url     : https://prove2.me/theorems/4391a13d-e1a6-438f-ab49-262b7c85ba31
-- title:
--   OpenAI's ordinary two-point correlations — the definitions of the formalization
-- statement:
--   The definitions behind OpenAI's proof of ordinary (non-logarithmic) two-point cancellation for the Liouville function and for nonpretentious multiplicative functions, as they appear in OpenAI's Lean development `lean/OAI/NumberTheory/TwoPoint` (github.com/openai/math, Apache License 2.0), together with the definitions it uses from the libraries math-inc/strongpnt and PrimeNumberTheoremAnd. They are carved out of that development, with comments removed and line-level edits for this Lean and Mathlib version, and published so that the intermediate results of the proof can be stated and proved one at a time. The bundle imports the published comparator bundle `OrdinaryTwoPointCorrelations` and takes its nine definitions from there (`liouville`, `correlationSum`, `affineSum`, `Multiplicative`, `OneBounded`, `primesUpTo`, `squaredDistance`, `characterTwist`, `UniformlyNonpretentious`).
--
--   The main groups of definitions:
--
--   - **The analytic inputs**, stated as propositions: `ModFiveThetaInput` (the prime number theorem with error $Cx\,e^{-c\sqrt{\log x}}$ for the primes $\equiv1$ and $\not\equiv1\pmod5$), `PrimeReciprocalInput` ($|\sum_{p\le y}1/p-\log\log y|\le C$), `BravermanDepth22Input` (Braverman's theorem that polylogarithmically $t$-wise uniform densities fool depth-22 AC⁰ circuits), `MRTShortExponentialInput` and `MRTLiouvilleShortInput` (Matomäki–Radziwiłł–Tao short exponential-sum bounds), `HalaszPrimeSparseInput`, `HalaszHighPrimeInput` and `MRTWeakHurwitzGrowthInput`; and the three conclusions `LiouvilleLogSaving`, `BinaryCorrectedElliott`, `AffineCorrectedElliott` in the form of the comparator theorems.
--   - **Halász and Matomäki–Radziwiłł machinery**: smooth-supported restrictions, Dirichlet and dyadic polynomials, prime bands $(\mathrm{lo}_j,\mathrm{up}_j]$ (`mrtBandLower`, `mrtBandUpper`), typical-number restrictions (`mrtTypicalCoefficient`), cofactor polynomials, short exponential sums and integrals, Vinogradov mean-value counts and polynomials, and the explicit constants these estimates use.
--   - **The prohibited-prime probabilistic model**: finite probability laws (`FiniteLaw`), prohibited prime families (`ProhibitedPrimeFamily`), their residue laws and deleted events, padding supplies and weights, column prime assignments, signed walk words and their shift matrices, AC⁰ circuits and Walsh–Fourier expansions on the Boolean cube.
--   - **L-functions and the zeta function**: normalized Dirichlet L-functions modulo 5 and modulo $q$, zero sets in discs, and, from strongpnt and PrimeNumberTheoremAnd, the smoothed Chebyshev function, its contour pieces `I₁`, …, `I₉`, Mellin transforms, rectangle and vertical integrals, and the constant `I` (an abbreviation for the imaginary unit `Complex.I`).
--
--   Each published statement of the split says in its own description which of these objects it uses and what they unfold to.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); the definitions are OpenAI's Lean definitions (with those of the vendored math-inc/strongpnt and PrimeNumberTheoremAnd libraries it uses), carved from the development

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OrdinaryTwoPointCorrelations

/-!
# Ordinary two-point correlations of multiplicative functions: definitions

OpenAI, *Ordinary two-point correlations of multiplicative functions*, OpenAI Math Release,
September 24, 2026, https://github.com/openai/math (paper:
`preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf`).

The definitions below are taken from OpenAI's Lean development `lean/OAI/NumberTheory/TwoPoint`
in that repository (Apache License, Version 2.0), and from the libraries math-inc/strongpnt and
PrimeNumberTheoremAnd that it uses, with comments removed and line-level edits for this Lean and
Mathlib version. They are the declarations needed to state the published lemmas of the proof.
The nine comparator definitions (`liouville`, `correlationSum`, `affineSum`, `Multiplicative`,
`OneBounded`, `primesUpTo`, `squaredDistance`, `characterTwist`, `UniformlyNonpretentious`) come
from the imported bundle `OrdinaryTwoPointCorrelations`.
-/

section

namespace OAI

noncomputable section
open scoped _root_.BigOperators
open _root_.Finset

namespace Problem337.SelbergError

def divisorTupleCount (k n : ℕ) : ℕ :=
  (ArithmeticFunction.zeta ^ k) n

end Problem337.SelbergError

end

end OAI

end

section

namespace OAI

noncomputable section

open scoped _root_.BigOperators

namespace Problem337

def GoldbachSieveRoot (u d : ℕ) :=
  {x : ZMod d // x * ((u : ZMod d) - x) = 0}

def goldbachSieveRootCount (u d : ℕ) : ℕ :=
  Nat.card (GoldbachSieveRoot u d)

def goldbachSieveRootEquiv (u a b : ℕ) (hab : a.Coprime b) :
    GoldbachSieveRoot u (a * b) ≃
      GoldbachSieveRoot u a × GoldbachSieveRoot u b := by
  let e := ZMod.chineseRemainder hab
  apply (Equiv.subtypeEquiv e.toEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  change x * ((u : ZMod (a * b)) - x) = 0 ↔
    (e x).1 * ((u : ZMod a) - (e x).1) = 0 ∧
      (e x).2 * ((u : ZMod b) - (e x).2) = 0
  have h := e.injective.eq_iff (a := x * ((u : ZMod (a * b)) - x)) (b := 0)
  simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.mk_zero_zero,
    Prod.mul_def, Prod.sub_def, Prod.fst_natCast, Prod.snd_natCast,
    Prod.mk.injEq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] using h.symm

theorem goldbachSieveRootCount_mul (u a b : ℕ) (hab : a.Coprime b) :
    goldbachSieveRootCount u (a * b) =
      goldbachSieveRootCount u a * goldbachSieveRootCount u b := by
  unfold goldbachSieveRootCount
  rw [Nat.card_congr (goldbachSieveRootEquiv u a b hab), Nat.card_prod]

@[simp] theorem goldbachSieveRootCount_one (u : ℕ) :
    goldbachSieveRootCount u 1 = 1 := by
  unfold goldbachSieveRootCount GoldbachSieveRoot
  have e : {x : ZMod 1 // x * ((u : ZMod 1) - x) = 0} ≃ ZMod 1 :=
    Equiv.subtypeUnivEquiv (fun x => Subsingleton.elim _ _)
  rw [Nat.card_congr e, Nat.card_zmod]

theorem goldbachSieveRootCount_prime (u p : ℕ) (hp : p.Prime) :
    goldbachSieveRootCount u p = if p ∣ u then 1 else 2 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hroots : (Finset.univ.filter
      (fun x : ZMod p => x * ((u : ZMod p) - x) = 0)) = {0, (u : ZMod p)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mul_eq_zero, sub_eq_zero, Finset.mem_insert, Finset.mem_singleton]
    tauto
  unfold goldbachSieveRootCount GoldbachSieveRoot
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hroots]
  by_cases h : p ∣ u
  · simp [h, (ZMod.natCast_eq_zero_iff u p).mpr h]
  · have hne : (u : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff u p).not.mpr h
    simp [h, Ne.symm hne]

def goldbachSieveDensity (u : ℕ) : ArithmeticFunction ℝ where
  toFun d := (goldbachSieveRootCount u d : ℝ) / (d : ℝ)
  map_zero' := by simp

@[simp] theorem goldbachSieveDensity_apply (u d : ℕ) :
    goldbachSieveDensity u d = (goldbachSieveRootCount u d : ℝ) / (d : ℝ) := rfl

theorem goldbachSieveDensity_isMultiplicative (u : ℕ) :
    (goldbachSieveDensity u).IsMultiplicative := by
  constructor
  · simp
  · intro a b hab
    simp only [goldbachSieveDensity_apply, goldbachSieveRootCount_mul u a b hab,
      Nat.cast_mul, mul_div_mul_comm]

theorem goldbachSieveDensity_prime (u p : ℕ) (hp : p.Prime) :
    goldbachSieveDensity u p = if p ∣ u then 1 / (p : ℝ) else 2 / (p : ℝ) := by
  rw [goldbachSieveDensity_apply, goldbachSieveRootCount_prime u p hp]
  split_ifs <;> norm_num

theorem goldbachSieveDensity_prime_pos (u p : ℕ) (hp : p.Prime) :
    0 < goldbachSieveDensity u p := by
  rw [goldbachSieveDensity_prime u p hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  split_ifs <;> positivity

theorem goldbachSieveDensity_prime_lt_one (u p : ℕ) (hp : p.Prime)
    (hparity : p = 2 → 2 ∣ u) : goldbachSieveDensity u p < 1 := by
  rw [goldbachSieveDensity_prime u p hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  split_ifs with h
  · rw [div_lt_one hpR]
    exact_mod_cast hp.one_lt
  · have hp2 : 2 < p := by
      have := hp.two_le
      by_contra hnot
      have heq : p = 2 := by omega
      exact h (heq ▸ hparity heq)
    rw [div_lt_one hpR]
    exact_mod_cast hp2

end Problem337

end

end OAI

end

section

namespace OAI
noncomputable section

open scoped _root_.BigOperators

namespace Problem337

instance goldbachSieveRootFintype (u d : ℕ) [NeZero d] :
    Fintype (GoldbachSieveRoot u d) :=
  inferInstanceAs (Fintype {x : ZMod d // x * ((u : ZMod d) - x) = 0})

def goldbachSieveRootLCMEmbedding (u a b : ℕ) :
    GoldbachSieveRoot u (a.lcm b) ↪
      GoldbachSieveRoot u a × GoldbachSieveRoot u b := by
  let e : ZMod (a.lcm b) →+* ZMod a × ZMod b :=
    ZMod.castHom (dvd_refl (a.lcm b)) _
  have einj : Function.Injective e := ZMod.castHom_injective _
  have he (x : GoldbachSieveRoot u (a.lcm b)) :
      (e x.val).1 * ((u : ZMod a) - (e x.val).1) = 0 ∧
        (e x.val).2 * ((u : ZMod b) - (e x.val).2) = 0 := by
    have h := congrArg e x.property
    simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.mul_def,
      Prod.sub_def, Prod.ext_iff, Prod.fst_natCast, Prod.snd_natCast,
      Prod.fst_zero, Prod.snd_zero] using h
  refine ⟨fun x => (⟨(e x.val).1, (he x).1⟩, ⟨(e x.val).2, (he x).2⟩), ?_⟩
  intro x y hxy
  apply Subtype.ext
  apply einj
  apply Prod.ext
  · exact congrArg (fun z : GoldbachSieveRoot u a × GoldbachSieveRoot u b => z.1.val) hxy
  · exact congrArg (fun z : GoldbachSieveRoot u a × GoldbachSieveRoot u b => z.2.val) hxy

end Problem337

end

end OAI

end

section

namespace OAI
noncomputable section
open scoped _root_.BigOperators

namespace Problem337.PrimePairSieve

def fiberWeight (A : Finset ℕ) (f : ℕ → ℕ) (y : ℕ) : ℝ :=
  ((A.filter (fun x => f x = y)).card : ℝ)

lemma fiberWeight_nonneg (A : Finset ℕ) (f : ℕ → ℕ) (y : ℕ) :
    0 ≤ fiberWeight A f y := by
  exact Nat.cast_nonneg _

def imageSieve (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) : BoundingSieve where
  support := A.image f
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fiberWeight A f
  weights_nonneg := fiberWeight_nonneg A f
  totalMass := A.card
  nu := ν
  nu_mult := hν
  nu_pos_of_prime := hνpos
  nu_lt_one_of_prime := hνlt

def primePairs (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun x => x.Prime ∧ (N - x).Prime)

def siftedPairs (N P : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun x => P.Coprime (x * (N - x)))

end Problem337.PrimePairSieve

end

end OAI

end

section

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SievePartition

open scoped _root_.BigOperators

variable {α ι : Type*} [DecidableEq α] [LinearOrder ι]

noncomputable def survivors (C : Finset α) (P : Finset ι)
    (bad : ι → α → Prop) : Finset α := by
  classical
  exact C.filter fun x => ∀ p ∈ P, ¬ bad p x

def residueBad (a : ℕ → ℕ) (p n : ℕ) : Prop := n % p = a p % p

end NumberTheoryLean.SievePartition

end

section

namespace NumberTheoryLean.SieveTree

open scoped _root_.BigOperators

variable {V : Type*} [DecidableEq V]

end NumberTheoryLean.SieveTree

end

section

namespace NumberTheoryLean.ResidueSieveTree

open scoped _root_.BigOperators
open _root_.OAI.Erdos970.NumberTheoryLean.SievePartition

end NumberTheoryLean.ResidueSieveTree

end

section

namespace ErdosInverseCounts
open _root_.OAI.Erdos970.NumberTheoryLean _root_.OAI.Erdos970.NumberTheoryLean.SievePartition

end ErdosInverseCounts

end

section

namespace ErdosAlignedProgression

end ErdosAlignedProgression

end

end Erdos970

end OAI

end

section

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LargePrimeDeletion

open scoped _root_.BigOperators

def cutoffPrimes (z : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter Nat.Prime

@[simp] theorem mem_cutoffPrimes {p z : ℕ} :
    p ∈ cutoffPrimes z ↔ p.Prime ∧ p ≤ z := by
  simp only [cutoffPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, and_comm]

noncomputable def deletionCell (C : Finset ℕ) (a : ℤ) (q : ℕ) : Finset ℕ := by
  classical
  exact C.filter fun i => (q : ℤ) ∣ a + i

def divisibilityResidue (a : ℤ) (q : ℕ) : ℕ := ((-a) % q).toNat

noncomputable def cutoffSurvivors (Y z : ℕ) (residue : ℕ → ℕ) : Finset ℕ :=
  SievePartition.survivors (Finset.range Y) (cutoffPrimes z)
    (SievePartition.residueBad residue)

noncomputable def coprimeOffsets (Y n : ℕ) (a : ℤ) : Finset ℕ := by
  classical
  exact (Finset.range Y).filter fun i => (a + i).natAbs.Coprime n

end NumberTheoryLean.LargePrimeDeletion

end

end Erdos970

end OAI

end

section

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.IntervalBoundingSieve

open scoped _root_.BigOperators

noncomputable def reciprocalDensity : ArithmeticFunction ℝ where
  toFun := fun d => (d : ℝ)⁻¹
  map_zero' := by simp

@[simp] theorem reciprocalDensity_apply (d : ℕ) :
    reciprocalDensity d = (d : ℝ)⁻¹ := rfl

theorem reciprocalDensity_multiplicative : reciprocalDensity.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n _
  simp only [reciprocalDensity_apply, Nat.cast_mul, mul_inv_rev, mul_comm]

noncomputable def intervalSieve (A J P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := (Finset.range J).image fun i => A + i
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 1
  weights_nonneg := by intro n; norm_num
  totalMass := J
  nu := reciprocalDensity
  nu_mult := reciprocalDensity_multiplicative
  nu_pos_of_prime := by
    intro p hp _
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

noncomputable def residueAvoidingOffsets (J P : ℕ) (residue : ℕ → ℕ) : Finset ℕ := by
  classical
  exact (Finset.range J).filter fun i => ∀ p ∈ P.primeFactors,
    i % p ≠ residue p % p

theorem squarefree_primeSet_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hpprime : p.Prime := hs p (Finset.mem_insert_self p s)
      have hsprime : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hp]
      apply Nat.squarefree_mul_iff.mpr
      refine ⟨?_, hpprime.squarefree, ih hsprime⟩
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hpprime (hsprime q hq)).mpr (by
        intro heq
        exact hp (heq ▸ hq))

def cutoffProduct (z : ℕ) : ℕ := ∏ p ∈ LargePrimeDeletion.cutoffPrimes z, p

theorem cutoffProduct_squarefree (z : ℕ) : Squarefree (cutoffProduct z) := by
  apply squarefree_primeSet_product
  intro p hp
  exact (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1

end NumberTheoryLean.IntervalBoundingSieve

end

end Erdos970

end OAI

end

section

namespace OAI

open scoped _root_.BigOperators

namespace TwoPointCorrelations

def progressionSum (f g : ℕ → ℂ) (h l b N : ℕ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % l = b % l), f n * g (n + h)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

open scoped _root_.BigOperators

namespace TwoPointCorrelations

def residuePrefix (u : ℕ → ℂ) (l b N : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc 0 N, if m % l = b % l then u m else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def centerMagnitude (θ : ℝ) (lit : Bool) : ℝ :=
  |(if lit then 1 else 0) - θ|

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.BinaryTree

variable {V : Type*}

def forestNodes : BinaryTree V → List V
  | .nil => []
  | .node v children siblings => v :: (forestNodes children ++ forestNodes siblings)

def forestRoots : BinaryTree V → List V
  | .nil => []
  | .node v _ siblings => v :: forestRoots siblings

def forestAdjacent : BinaryTree V → V → V → Prop
  | .nil, _, _ => False
  | .node v children siblings, x, y =>
      (x = v ∧ y ∈ forestRoots children) ∨ (y = v ∧ x ∈ forestRoots children) ∨
        forestAdjacent children x y ∨ forestAdjacent siblings x y

@[simp] lemma forestNodes_length (t : BinaryTree V) : (forestNodes t).length = t.numNodes := by
  induction t with
  | nil => rfl
  | node v l r hl hr => simp [forestNodes, hl, hr]

def attachForestLeaf [DecidableEq V] (parent leaf : V) : BinaryTree V → BinaryTree V
  | .nil => .nil
  | .node v children siblings =>
      if v = parent then .node v (.node leaf .nil children) siblings
      else .node v (attachForestLeaf parent leaf children) (attachForestLeaf parent leaf siblings)

@[simp] lemma forestNodes_map {W : Type*} (f : V → W) (t : BinaryTree V) :
    forestNodes (t.map f) = (forestNodes t).map f := by
  induction t <;> simp [BinaryTree.map, forestNodes, *]

@[simp] lemma forestRoots_map {W : Type*} (f : V → W) (t : BinaryTree V) :
    forestRoots (t.map f) = (forestRoots t).map f := by
  induction t <;> simp [BinaryTree.map, forestRoots, *]

lemma forestAdjacent_map {W : Type*} (f : V → W) (hf : Function.Injective f)
    (t : BinaryTree V) (x y : V) :
    forestAdjacent (t.map f) (f x) (f y) ↔ forestAdjacent t x y := by
  induction t <;> simp [BinaryTree.map, forestAdjacent, hf.eq_iff, *]

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def fromPrimePowers (F : ℕ → ℕ → ℂ) (n : ℕ) : ℂ :=
  n.factorization.prod F

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def matrixOperator (A : ι → ι → ℂ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def halfPair (u v : E) (z : ℂ) : E := (2 : ℂ)⁻¹ • (u + z • v)

end Hilbert

noncomputable def halfPairFunction {α : Type*} (f g : α → ℂ) (z : ℂ) : α → ℂ :=
  fun x => (f x + z * g x) / 2

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

variable {α : Type*} {N : ℕ}

def paddedListCode (l : List α) (h : l.length ≤ N) (default : α) : Fin N → α :=
  fun i => (l ++ List.replicate (N - l.length) default)[i.val]'(by
    simp only [List.length_append, List.length_replicate]
    omega)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

open scoped _root_.BigOperators

namespace TwoPointCorrelations

def paddingMass (Q : Finset ℕ) (weight : ℕ → ℤ → ℕ → ℝ)
    (next : ℕ → ℤ → ℕ → ℤ) : ℕ → ℕ → ℤ → ℝ
  | 0, _, _ => 1
  | m + 1, i, n => ∑ q ∈ Q, weight i n q * paddingMass Q weight next m (i + 1) (next i n q)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.BinaryTree

variable {V W : Type*}

lemma forest_map_congr (t : BinaryTree V) (f g : V → W)
    (h : ∀ x ∈ forestNodes t, f x = g x) : t.map f = t.map g := by
  induction t with
  | nil => rfl
  | node v l r hl hr =>
      simp only [BinaryTree.map]
      congr 1
      · exact h v (by simp [forestNodes])
      · exact hl (fun x hx => h x (by simp [forestNodes, hx]))
      · exact hr (fun x hx => h x (by simp [forestNodes, hx]))

@[simp] lemma forest_numNodes_map (f : V → W) (t : BinaryTree V) :
    (t.map f).numNodes = t.numNodes := by
  induction t <;> simp [BinaryTree.map, *]

def numberForest : BinaryTree V → ℕ → BinaryTree ℕ
  | .nil, _ => .nil
  | .node _ l r, start =>
      .node start (numberForest l (start + 1)) (numberForest r (start + 1 + l.numNodes))

@[simp] lemma numberForest_map (f : V → W) (t : BinaryTree V) (start : ℕ) :
    numberForest (t.map f) start = numberForest t start := by
  induction t generalizing start <;> simp [BinaryTree.map, numberForest, *]

lemma numberForest_eq_map_idxOf [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (start : ℕ) :
    numberForest t start = t.map (fun v => start + (forestNodes t).idxOf v) := by
  induction t generalizing start with
  | nil => rfl
  | node v l r hl hr =>
      have hn := List.nodup_cons.mp ht
      have hp := List.nodup_append.mp hn.2
      simp only [numberForest, BinaryTree.map]
      congr 1
      · simp [forestNodes]
      · rw [hl hp.1 (start + 1)]
        apply forest_map_congr
        intro x hx
        have hv : v ≠ x := by intro heq; subst x; exact hn.1 (List.mem_append_left _ hx)
        simp only [forestNodes, List.idxOf_cons_ne _ hv, List.idxOf_append_of_mem hx]
        omega
      · rw [hr hp.2.1 (start + 1 + l.numNodes)]
        apply forest_map_congr
        intro x hx
        have hv : v ≠ x := by intro heq; subst x; exact hn.1 (List.mem_append_right _ hx)
        have hxl : x ∉ forestNodes l := by
          intro hxl
          exact hp.2.2 x hxl x hx rfl
        simp only [forestNodes, List.idxOf_cons_ne _ hv, List.idxOf_append_of_notMem hxl,
          forestNodes_length]
        omega

theorem numberForest_eq_of_same_shape (t : BinaryTree V) (s : BinaryTree W)
    (hts : t.map (fun _ => ()) = s.map (fun _ => ())) (start : ℕ) :
    numberForest t start = numberForest s start := by
  have h := congrArg (fun a => numberForest a start) hts
  simpa only [numberForest_map] using h

lemma preorder_index_injective [DecidableEq V] (t : BinaryTree V)
    (hcover : ∀ v, v ∈ forestNodes t) :
    Function.Injective (fun v => (forestNodes t).idxOf v) := by
  intro x y hxy
  exact (List.idxOf_inj (hcover x)).mp hxy

theorem numberForest_adjacent [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hcover : ∀ v, v ∈ forestNodes t) (x y : V) :
    forestAdjacent (numberForest t 0) ((forestNodes t).idxOf x) ((forestNodes t).idxOf y) ↔
      forestAdjacent t x y := by
  rw [numberForest_eq_map_idxOf t ht 0]
  simpa only [zero_add] using forestAdjacent_map
    (fun v => (forestNodes t).idxOf v) (preorder_index_injective t hcover) t x y

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Submodule

variable {K κ V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype κ] [DecidableEq κ]

def pairFamily (v : κ → Fin 2 → V) (S : Finset κ) : S × Fin 2 → V :=
  fun z => v z.1 z.2

noncomputable def insertPairEquiv (S : Finset κ) (k : κ) (hk : k ∉ S) :
    (S × Fin 2) ⊕ Fin 2 ≃ ↥(insert k S) × Fin 2 :=
  Equiv.ofBijective
    (Sum.elim (fun z => (⟨z.1, mem_insert_of_mem z.1.property⟩, z.2))
      (fun b => (⟨k, mem_insert_self k S⟩, b))) (by
    constructor
    · intro z w heq
      cases z with
      | inl z =>
        cases w with
        | inl w =>
          apply congrArg Sum.inl
          apply Prod.ext
          · apply Subtype.ext
            exact congrArg (fun a : ↥(insert k S) × Fin 2 => (a.1 : κ)) heq
          · exact congrArg (fun a : ↥(insert k S) × Fin 2 => a.2) heq
        | inr b =>
          have hz : (z.1 : κ) = k :=
            congrArg (fun a : ↥(insert k S) × Fin 2 => (a.1 : κ)) heq
          exact (hk (hz ▸ z.1.property)).elim
      | inr b =>
        cases w with
        | inl w =>
          have hw : k = (w.1 : κ) :=
            congrArg (fun a : ↥(insert k S) × Fin 2 => (a.1 : κ)) heq
          exact (hk (hw ▸ w.1.property)).elim
        | inr c => exact congrArg Sum.inr (congrArg Prod.snd heq)
    · rintro ⟨⟨j, hj⟩, b⟩
      rcases mem_insert.mp hj with rfl | hj
      · exact ⟨.inr b, rfl⟩
      · exact ⟨.inl (⟨j, hj⟩, b), rfl⟩)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

def residueCount {D : ℕ} [NeZero D] (A : ZMod D) (N : ℕ) (r : ZMod D) : ℕ :=
  ∑ j ∈ Finset.range N, if A + (j : ZMod D) = r then 1 else 0

noncomputable def residueProbability {D : ℕ} [NeZero D] (A : ZMod D)
    (N : ℕ) (r : ZMod D) : ℝ := (residueCount A N r : ℝ) / N

lemma residueCount_sum {D : ℕ} [NeZero D] (A : ZMod D) (N : ℕ) :
    ∑ r : ZMod D, residueCount A N r = N := by
  unfold residueCount
  rw [Finset.sum_comm]
  simp

lemma residueProbability_sum {D : ℕ} [NeZero D] (A : ZMod D) (N : ℕ) (hN : 0 < N) :
    ∑ r : ZMod D, residueProbability A N r = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp only [residueProbability, ← Finset.sum_div, ← Nat.cast_sum, residueCount_sum]
  exact div_self hN'

noncomputable def residueTotalVariation {D : ℕ} [NeZero D] (A : ZMod D) (N : ℕ) : ℝ :=
  (∑ r : ZMod D, |residueProbability A N r - 1 / (D : ℝ)|) / 2

end TwoPointCorrelations

end OAI

end

section

namespace OAI

open _root_.Finset

namespace TwoPointCorrelations

noncomputable def finiteTotalVariation {α : Type*} [Fintype α] (f g : α → ℝ) : ℝ :=
  (∑ x, |f x - g x|) / 2

noncomputable def kernelTransport {α β : Type*} [Fintype α]
    (K : α → β → ℝ) (f : α → ℝ) (y : β) : ℝ :=
  ∑ x, f x * K x y

noncomputable def finiteRandomKernel {α β J : Type*} [DecidableEq β] [Fintype J]
    (F : α → J → β) (x : α) (y : β) : ℝ :=
  (∑ j, if F x j = y then (1 : ℝ) else 0) / Fintype.card J

instance modulusProduct_neZero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] : NeZero (∏ i, s i) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (s i))⟩

noncomputable def crtJointProbability {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    [∀ i, NeZero (s i)] (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (r : ∀ i, ZMod (s i)) : ℝ :=
  residueProbability A N ((ZMod.prodEquivPi s hcop).symm r)

noncomputable def crtUniform {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    (_r : ∀ i, ZMod (s i)) : ℝ := 1 / (∏ i, s i : ℕ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

theorem exists_common_integer_residue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ∀ i, ZMod (p i)) :
    ∃ n : ℤ, ∀ i, (n : ZMod (p i)) = r i := by
  let y : ZMod (∏ i, p i) := (ZMod.prodEquivPi p hcop).symm r
  refine ⟨(y.val : ℤ), ?_⟩
  intro i
  calc
    ((y.val : ℤ) : ZMod (p i)) =
        ZMod.prodEquivPi p hcop ((y.val : ℕ) : ZMod (∏ i, p i)) i := by
      simp only [Int.cast_natCast, ZMod.prodEquivPi_apply, map_natCast]
    _ = ZMod.prodEquivPi p hcop y i := by rw [ZMod.natCast_zmod_val]
    _ = r i := congrFun ((ZMod.prodEquivPi p hcop).apply_symm_apply r) i

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def shiftedDivisorCount (p a Y : ℕ) : ℕ :=
  ∑ v ∈ range Y, if p ∣ a + v then 1 else 0

def coprimeExceptionCount (u d Y : ℕ) : ℕ :=
  ∑ v ∈ range Y, if ¬u.Coprime ((v + 1) * (v + 1 + d)) then 1 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def uniformAverage {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.BigOperators

def positivePrefix (u : ℕ → ℂ) (Y : ℕ) : ℂ :=
  ∑ v ∈ Finset.range Y, u (v + 1)

noncomputable def translatedPrefixAverage (u : ℕ → ℂ) (Y D : ℕ) : ℂ :=
  (D : ℂ)⁻¹ * ∑ m ∈ Finset.range D, positivePrefix (fun n => u (n + (m + 1))) Y

def weightedShiftProfile {ι : Type*} (Z : Finset ι) (w : ι → ℂ) (shift : ι → ℕ)
    (f g : ℕ → ℂ) (l b n : ℕ) : ℂ :=
  ∑ z ∈ Z, w z * (if n % l = b % l then f n * g (n + shift z) else 0)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def multiplicativeExtractionGap (f g : ℕ → ℂ) (u d n : ℕ) : ℂ :=
  f (u * n) * g (u * (n + d)) - f u * g u * f n * g (n + d)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def edgeBlockSum {E : Type*} (edges : Finset E) (r : E → ℕ)
    (c : E → ℕ → ℂ) (M t : ℕ) : ℂ :=
  ∑ i ∈ range M, ∑ e ∈ edges, if i + 1 + r e ≤ M then c e (t + i + 2) else 0

noncomputable def fullBlockSum {E : Type*} (edges : Finset E)
    (c : E → ℕ → ℂ) (M t : ℕ) : ℂ :=
  ∑ i ∈ range M, ∑ e ∈ edges, c e (t + i + 2)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

variable {α : Type*}

def partitionColumnRuns (omitted : α → Bool) : List α → List (List α ⊕ α)
  | [] => []
  | a :: rest =>
      if omitted a then .inr a :: partitionColumnRuns omitted rest
      else match partitionColumnRuns omitted rest with
        | .inl segment :: tail => .inl (a :: segment) :: tail
        | tail => .inl [a] :: tail

def regularPieceCount (pieces : List (List α ⊕ α)) : ℕ :=
  (pieces.filterMap (Sum.elim some (fun _ => none))).length

def omittedPieceCount (pieces : List (List α ⊕ α)) : ℕ :=
  (pieces.filterMap (Sum.elim (fun _ => none) some)).length

def startsWithRegularPiece (pieces : List (List α ⊕ α)) : Bool :=
  (pieces.head?.map (Sum.elim (fun _ => true) (fun _ => false))).getD false

end TwoPointCorrelations

end OAI

end

section

namespace OAI

open _root_.Filter

namespace TwoPointCorrelations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Nontrivial E]

noncomputable def leastRayleigh (T : E →L[ℂ] E) : ℝ :=
  ⨅ x : {x : E // x ≠ 0}, T.rayleighQuotient x

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open _root_.OAI.Problem337 hiding goldbachSieveRootFintype goldbachSieveRootLCMEmbedding
open scoped _root_.Classical

noncomputable def sieveGoldbachWeight (N p : ℕ) : ℝ :=
  goldbachSieveDensity N p / (1 - goldbachSieveDensity N p)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def primeSmoothPart (P : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (fun p => p ∈ P)).prod

noncomputable def primeRoughPart (P : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (fun p => p ∉ P)).prod

noncomputable def coprimeRestriction (q : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if q.Coprime n then f n else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def smoothReciprocalProduct (P : Finset ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ P, (1 - (p : ℝ) ^ (-s))⁻¹

noncomputable def natNegativePower (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    push_cast
    exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

abbrev BooleanCube (n : ℕ) := Fin n → Bool

noncomputable def cubeAverage {n : ℕ} (f : BooleanCube n → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card (BooleanCube n)

lemma cubeAverage_add {n : ℕ} (f g : BooleanCube n → ℝ) :
    cubeAverage (fun x => f x + g x) = cubeAverage f + cubeAverage g := by
  simp [cubeAverage, Finset.sum_add_distrib, add_div]

lemma cubeAverage_mul_const {n : ℕ} (f : BooleanCube n → ℝ) (c : ℝ) :
    cubeAverage (fun x => c * f x) = c * cubeAverage f := by
  simp only [cubeAverage, ← Finset.mul_sum, mul_div_assoc]

@[simp] lemma cubeAverage_const {n : ℕ} (c : ℝ) :
    cubeAverage (fun _ : BooleanCube n => c) = c := by
  simp [cubeAverage, Finset.sum_const]

def booleanSign (b : Bool) : ℝ := if b then -1 else 1

def walsh {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) : ℝ :=
  ∏ i ∈ S, booleanSign (x i)

@[simp] lemma walsh_empty {n : ℕ} (x : BooleanCube n) : walsh ∅ x = 1 := by
  simp [walsh]

def flipBit {n : ℕ} (i : Fin n) : BooleanCube n ≃ BooleanCube n where
  toFun x := Function.update x i (!x i)
  invFun x := Function.update x i (!x i)
  left_inv x := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  right_inv x := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]

def lowWalshSets (n t : ℕ) : Finset (Finset (Fin n)) :=
  univ.filter (fun S => S.Nonempty ∧ S.card ≤ t)

noncomputable def walshCoefficient {n : ℕ} (f : BooleanCube n → ℝ)
    (S : Finset (Fin n)) : ℝ := cubeAverage (fun x => f x * walsh S x)

noncomputable def lowWalshCorrection {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (x : BooleanCube n) : ℝ :=
  ∑ S ∈ lowWalshSets n t, walshCoefficient f S * walsh S x

noncomputable def lowWalshMass {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) : ℝ :=
  ∑ S ∈ lowWalshSets n t, |walshCoefficient f S|

noncomputable def correctedCubeDensity {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (a : ℝ) (x : BooleanCube n) : ℝ :=
  (f x - lowWalshCorrection f t x + a) / (1 + a)

noncomputable def cubePattern {n : ℕ} (S : Finset (Fin n))
    (z x : BooleanCube n) : ℝ := if ∀ i ∈ S, x i = z i then 1 else 0

def TWiseUniformDensity {n : ℕ} (g : BooleanCube n → ℝ) (t : ℕ) : Prop :=
  ∀ (S : Finset (Fin n)), S.card ≤ t → ∀ z : BooleanCube n,
    cubeAverage (fun x => g x * cubePattern S z x) = 1 / (2 : ℝ) ^ S.card

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def sampleDensity {α : Type*} [Fintype α] {n : ℕ}
    (sample : α → BooleanCube n) (x : BooleanCube n) : ℝ :=
  (Fintype.card (BooleanCube n) : ℝ) / Fintype.card α *
    ∑ a, if sample a = x then 1 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

open _root_.Finset

namespace TwoPointCorrelations

def jitterPermutation (s Q : ℕ) : Fin s × Fin Q ≃ Fin Q × Fin s :=
  finProdFinEquiv.trans ((finCongr (Nat.mul_comm s Q)).trans finProdFinEquiv.symm)

def jitterCode {s Q : ℕ} (r : Fin s) (j : Fin Q) : Fin Q :=
  (jitterPermutation s Q (r, j)).1

def jitterDecode {s Q : ℕ} (hs : 0 < s) (hQ : 0 < Q) (k : Fin Q) : Fin s :=
  ⟨s * k.val / Q, (Nat.div_lt_iff_lt_mul hQ).mpr
    (Nat.mul_lt_mul_of_pos_left k.isLt hs)⟩

noncomputable def binaryCellEquiv (B : ℕ) : Fin (2 ^ B) ≃ BooleanCube B :=
  Fintype.equivOfCardEq (by simp [BooleanCube])

noncomputable def jitterBits {s B : ℕ} (r : Fin s) (j : Fin (2 ^ B)) : BooleanCube B :=
  binaryCellEquiv B (jitterCode r j)

noncomputable def decodeBits {s B : ℕ} (hs : 0 < s) (x : BooleanCube B) : Fin s :=
  jitterDecode hs (by positivity) ((binaryCellEquiv B).symm x)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

def coordinatePairEquiv {ι : Type*} (α β : ι → Type*) :
    (∀ i, α i × β i) ≃ (∀ i, α i) × (∀ i, β i) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x i := (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

def jointJitterPermutation {ι : Type*} (s : ι → ℕ) (Q : ℕ) :
    ((∀ i, Fin (s i)) × (ι → Fin Q)) ≃ ((ι → Fin Q) × (∀ i, Fin (s i))) :=
  (coordinatePairEquiv (fun i => Fin (s i)) (fun _ => Fin Q)).symm.trans
    ((Equiv.piCongrRight (fun i => jitterPermutation (s i) Q)).trans
      (coordinatePairEquiv (fun _ => Fin Q) (fun i => Fin (s i))))

def jointJitterCode {ι : Type*} {s : ι → ℕ} {Q : ℕ}
    (r : ∀ i, Fin (s i)) (j : ι → Fin Q) : ι → Fin Q :=
  fun i => jitterCode (r i) (j i)

noncomputable def crtJitterCode {ι : Type*} (s : ι → ℕ) [∀ i, NeZero (s i)] {Q : ℕ}
    (r : ∀ i, ZMod (s i)) (j : ι → Fin Q) : ι → Fin Q :=
  jointJitterCode (fun i => (ZMod.finEquiv (s i)).symm (r i)) j

noncomputable def jointBitEquiv (ι : Type*) (B : ℕ) :
    (ι → Fin (2 ^ B)) ≃ (ι → BooleanCube B) :=
  Equiv.piCongrRight (fun _ => binaryCellEquiv B)

noncomputable def crtJitterBits {ι : Type*} (s : ι → ℕ) [∀ i, NeZero (s i)] (B : ℕ)
    (r : ∀ i, ZMod (s i)) (j : ι → Fin (2 ^ B)) : ι → BooleanCube B :=
  jointBitEquiv ι B (crtJitterCode s r j)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def minorArcValueCount {α : Type*} (S : Finset α) (f : α → ℤ) (n : ℤ) : ℕ :=
  (S.filter (fun a => f a = n)).card

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology

noncomputable def halaszHurwitzDifference (a : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (((n+1:ℕ):ℝ)+a:ℂ)^(-s)-((n+1:ℕ):ℂ)^(-s)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def halaszHyperbola (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N).product (Icc 1 N)).filter (fun p => p.1 * p.2 ≤ N)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszPrimePowerWeight (n : ℕ) : ℝ :=
  if n.Prime then 0 else ArithmeticFunction.vonMangoldt n

noncomputable def halaszPrimePowerConstant : ℝ :=
  ∑' n : ℕ, halaszPrimePowerWeight n / (n : ℝ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszPrimeConvolution (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ p ∈ (Icc 1 N).filter Nat.Prime,
    (Real.log (p : ℝ) : ℂ) * f p * (∑ m ∈ Icc 1 (N / p), f m)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def halaszInnerErrorConstant : ℝ :=
  halaszPrimePowerConstant + 1 + Real.log 2

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MvPolynomial

noncomputable def halaszVinogradovFiber {s N : ℕ} (x : Fin s → Fin N) (k : ℕ) :
    Finset (Fin s → Fin N) := by
  classical
  exact univ.filter (fun y => ∀ j ∈ Icc 1 k,
    (∑ i, ((x i).val+1)^j) = ∑ i, ((y i).val+1)^j)

noncomputable def halaszVinogradovCount (s k N : ℕ) : ℕ :=
  ∑ x : Fin s → Fin N, (halaszVinogradovFiber x k).card

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def halaszPrimePowerReduction (p r : ℕ) :
    ZMod (p^(r+1)) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega : r+1≠0)) (ZMod p)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate

local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

noncomputable def halaszVinogradovHaar (k : ℕ) : Measure (Fin k → AddCircle (1:ℝ)) :=
  Measure.pi (fun _ => AddCircle.haarAddCircle)

instance (k : ℕ) : IsProbabilityMeasure (halaszVinogradovHaar k) := by
  unfold halaszVinogradovHaar
  infer_instance

noncomputable def halaszVinogradovCharacter {k : ℕ} (m : Fin k → ℤ)
    (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  ∏ j, fourier (m j) (α j)

lemma halasz_vinogradov_character_continuous {k : ℕ} (m : Fin k → ℤ) :
    Continuous (halaszVinogradovCharacter m) := by
  unfold halaszVinogradovCharacter
  fun_prop

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate

noncomputable def halaszVinogradovPolynomial (k N : ℕ)
    (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  ∑ n : Fin N, halaszVinogradovCharacter
    (fun j => (((n.val+1)^(j.val+1):ℕ):ℤ)) α

def halaszVinogradovFrequency {s N : ℕ} (k : ℕ) (x : Fin s → Fin N) : Fin k → ℤ :=
  fun j => ∑ i, (((x i).val+1)^(j.val+1):ℕ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def halaszDyadicCutoffDegree (L : ℝ) : ℕ := ⌈2*L/Real.log 2⌉₊+1

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate

noncomputable def halaszRepresentationCount {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (w : Fin k → ℤ) : ℕ := by
  classical
  exact (univ.filter (fun xy : ι × ι => f xy.1-f xy.2=w)).card

noncomputable def halaszRepresentationSum {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  ∑ x, halaszVinogradovCharacter (f x) α

noncomputable def halaszRepresentationWeight {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (w : Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  halaszRepresentationSum f α * conj (halaszRepresentationSum f α) *
    halaszVinogradovCharacter (-w) α

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszFiberEnergy {α β : Type*} (F : Finset α) (f : α → β) : ℕ := by
  exact ∑ t ∈ F.image f, (F.filter (fun x => f x=t)).card^2

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical _root_.ComplexConjugate

noncomputable def halaszFinitePhase {ι : Type*} {k : ℕ} (F : Finset ι)
    (f : ι → Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  ∑ x∈F, halaszVinogradovCharacter (f x) α

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Polynomial
open scoped _root_.Classical

def halaszNatPowerFrequency {s N : ℕ} (k : ℕ) (x : Fin s → Fin N) : Fin k → ℕ :=
  fun j => ∑ i, ((x i).val+1)^(j.val+1)

def halaszLongResidues {s k N Q : ℕ} (p r : ℕ)
    (x : (Fin k → Fin N) × (Fin s → Fin Q)) : Fin k → ZMod (p^(r+1)) :=
  fun i => ((x.1 i).val+1:ℕ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def halaszScaledPolynomial (k N : ℕ) (m : ℤ)
    (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  halaszFinitePhase (univ : Finset (Fin N))
    (fun x j => m*((x.val+1)^(j.val+1):ℕ)) α

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.MeasureTheory

noncomputable def halaszCollisionMoment (s k N : ℕ) : ℝ :=
  ∫ α, ‖halaszVinogradovPolynomial k N α‖^(2*(s+k)-2) *
    ‖halaszScaledPolynomial k N 2 α‖ ∂halaszVinogradovHaar k

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical _root_.ComplexConjugate

noncomputable def halaszCrossCount {ι κ : Type*} {k : ℕ}
    (F : Finset ι) (G : Finset κ) (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) : ℕ :=
  ((F×ˢG).filter (fun x => f x.1=g x.2)).card

def halaszRepeatedFrequency (n k N : ℕ) (x : Fin N × (Fin n → Fin N)) : Fin k → ℤ :=
  fun j => 2*((x.1.val+1)^(j.val+1):ℕ)+halaszVinogradovFrequency k x.2 j

noncomputable def halaszRepeatedCount (n k N : ℕ) : ℕ :=
  halaszCrossCount univ univ (halaszRepeatedFrequency n k N)
    (halaszVinogradovFrequency (s := n+2) (N := N) k)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def halaszRepeatTuple {n N : ℕ} (a : Fin N) (x : Fin n → Fin N) :
    Fin (n+2) → Fin N := Fin.cons a (Fin.cons a x)

noncomputable def halaszPairCollision (n k N : ℕ) (i j : Fin (n+2)) :
    Finset ((Fin (n+2) → Fin N) × (Fin (n+2) → Fin N)) :=
  univ.filter (fun xy => xy.1 i=xy.1 j ∧
    halaszVinogradovFrequency k xy.1=halaszVinogradovFrequency k xy.2)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Polynomial
open scoped _root_.Classical

def halaszShiftedLongShortFrequency {s k N Q : ℕ} (p a : ℕ)
    (x : (Fin k → Fin N) × (Fin s → Fin Q)) : Fin k → ℕ :=
  fun j => (∑ i, ((x.1 i).val+1+a)^(j.val+1)) +
    p^(j.val+1)*halaszNatPowerFrequency k x.2 j

def halaszCommonResidueFrequency {s k N Q : ℕ} (p a : ℕ)
    (x : (Fin k → Fin N) × (Fin s → Fin Q)) : Fin k → ℕ :=
  fun j => halaszNatPowerFrequency k x.1 j +
    ∑ i, (p*((x.2 i).val+1)-a)^(j.val+1)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def halaszResidueQuotient {M : ℕ} (p : ℕ) (x : Fin M) : Fin (M/p+1) :=
  ⟨x.val/p,lt_of_le_of_lt (Nat.div_le_div_right (Nat.le_of_lt x.isLt)) (Nat.lt_succ_self _)⟩

def halaszResidueIndex {M p : ℕ} (hp : 0< p) (x : Fin M) : Fin p :=
  ⟨x.val%p,Nat.mod_lt _ hp⟩

def halaszResidueTupleQuotient {s k N M : ℕ} (p : ℕ)
    (x : (Fin k → Fin N) × (Fin s → Fin M)) :
    (Fin k → Fin N) × (Fin s → Fin (M/p+1)) :=
  (x.1,fun i => halaszResidueQuotient p (x.2 i))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def halaszTupleJoin (a b N : ℕ) :
    ((Fin a → Fin N) × (Fin b → Fin N)) ≃ (Fin (a+b) → Fin N) where
  toFun x := Fin.append x.1 x.2
  invFun y := (fun i => y (i.castAdd b),fun i => y (i.natAdd a))
  left_inv x := by
    apply Prod.ext <;> funext i <;> simp
  right_inv y := Fin.append_castAdd_natAdd

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszGoodLongTuples {n N ℓ : ℕ} (L : Fin ℓ → Fin n) :
    Finset (Fin n → Fin N) := univ.filter (fun x => Function.Injective (x ∘ L))

noncomputable def halaszBadLongCount {n k N ℓ : ℕ} (L : Fin ℓ → Fin (n+2)) : ℕ :=
  (univ.filter (fun xy : (Fin (n+2) → Fin N) × (Fin (n+2) → Fin N) =>
    ¬Function.Injective (xy.1 ∘ L) ∧
    halaszVinogradovFrequency k xy.1=halaszVinogradovFrequency k xy.2)).card

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszResidueGoodTuples {n N ℓ : ℕ}
    (L : Fin ℓ → Fin n) (p : ℕ) : Finset (Fin n → Fin N) :=
  univ.filter (fun x => Function.Injective (fun i => (((x (L i)).val+1:ℕ):ZMod p)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology

def halaszPrimeSupply (R : ℕ) : Finset ℕ := Nat.primesLE (16*R)\Nat.primesLE R

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def halaszRootScale (N k : ℕ) : ℕ := ⌊(N:ℝ)^(1/(k:ℝ))⌋₊+1

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

def halaszIterationRootThreshold (R₀ k : ℕ) : ℕ := R₀+(2*(k^2*k)+1)^2+k+2

def halaszIterationThreshold (R₀ k : ℕ) : ℕ :=
  (halaszIterationRootThreshold R₀ k)^k+(4*k^2)^2+2^k+1

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

def halaszIterationBase (R₀ k : ℕ) : ℕ :=
  k.factorial+(halaszIterationThreshold R₀ k)^(k+k*(k-1)/2)+
    2*(2*(k^2*k)+1)*k^k*32^(k*(k-1)/2)+1

def halaszIterationConstant (R₀ k n : ℕ) : ℕ :=
  (halaszIterationBase R₀ k)^(n+1)*32^(k*n*(n+1))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

def halaszStepExponent (s k : ℕ) : ℕ := 2*s+k*(k-1)/2

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

def halaszTriangularDegree (k : ℕ) : ℕ := k*(k-1)/2

def halaszTotalDegree (k : ℕ) : ℕ := k+halaszTriangularDegree k

noncomputable def halaszClassicalDefect (k n : ℕ) : ℝ :=
  (halaszTriangularDegree k:ℝ)*(1-1/(k:ℝ))^n

noncomputable def halaszClassicalExponent (k n : ℕ) : ℝ :=
  2*(((n+1)*k:ℕ):ℝ)-(halaszTotalDegree k:ℝ)+halaszClassicalDefect k n

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate
open _root_.Filter

noncomputable def productCharacters {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q * r) :=
  χ.changeLevel (Nat.dvd_mul_right q r) * ψ.changeLevel (Nat.dvd_mul_left r q)

def conjugateCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) : DirichletCharacter ℂ q :=
  χ.ringHomComp (starRingEnd ℂ)

noncomputable def twistByCharacter {q : ℕ} (f : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ := f n * χ (n : ZMod q)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

open scoped _root_.BigOperators

namespace TwoPointCorrelations

noncomputable def localComponent (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P E : Finset ℕ) : ℕ → ℂ :=
  fromPrimePowers (fun p k => if p ∈ P then if p ∈ E then C p k else B p k else f (p ^ k))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

open scoped _root_.BigOperators

namespace TwoPointCorrelations

noncomputable def dilate (a : ℕ) (f : ℕ → ℂ) (m : ℕ) : ℂ :=
  if a ∣ m then f (m / a) else 0

noncomputable def dilationLocal (a : ℕ) (f : ℕ → ℂ) (p k : ℕ) : ℂ :=
  if k < a.factorization p then 0 else f (p ^ (k - a.factorization p))

noncomputable def dilationB (a : ℕ) (f : ℕ → ℂ) (p k : ℕ) : ℂ :=
  if k = 0 then 1 else dilationLocal a f p k

noncomputable def dilationC (_a : ℕ) (_f : ℕ → ℂ) (_p k : ℕ) : ℂ :=
  if k = 0 then 1 else 0

noncomputable def dilationComponent (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) : ℕ → ℂ :=
  localComponent f (dilationB a f) (dilationC a f) a.primeFactors E

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def primeDefectLocal (f : ℕ → ℂ) (p n : ℕ) : ℝ :=
  if p ∣ n ∧ ¬p ^ 2 ∣ n then ‖f p‖ else 1

noncomputable def primeDefectMajorant (f : ℕ → ℂ) (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∏ p ∈ P, primeDefectLocal f p n

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def primeModulusDefect (f : ℕ → ℂ) (p : ℕ) : ℝ :=
  if p.Prime then (1 - ‖f p‖) / (p : ℝ) else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

open scoped _root_.BigOperators _root_.ComplexConjugate

namespace TwoPointCorrelations

noncomputable def naturalCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n : ZMod q)

noncomputable def residueComponent {q : ℕ} (f : ℕ → ℂ) (d : ℕ)
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) (n : ℕ) : ℂ :=
  f n * dilationComponent d (naturalCharacter χ) E n

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.BigOperators
open _root_.MeasureTheory

noncomputable def additiveCharacter (α : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I)

noncomputable def shortExponentialSum (b : ℕ → ℂ) (H : ℕ) (α y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (Nat.floor y + 1) (Nat.floor (y + (H : ℝ))),
    b n * additiveCharacter α n

noncomputable def shortExponentialIntegral (b : ℕ → ℂ) (X H : ℕ) (α : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..(X : ℝ), ‖shortExponentialSum b H α y‖

noncomputable def mrtModulusCutoff (X H : ℕ) : ℝ :=
  min ((Real.log (X : ℝ)) ^ (1 / (125 : ℝ))) ((Real.log (H : ℝ)) ^ (5 : ℕ))

noncomputable def mrtShortError (X H : ℕ) : ℝ :=
  Real.log (Real.log (H : ℝ)) / Real.log (H : ℝ) +
    (Real.log (X : ℝ)) ^ (-1 / (700 : ℝ))

def MRTDistanceLowerBound (b : ℕ → ℂ) (X H : ℕ) (M : ℝ) : Prop :=
  ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ mrtModulusCutoff X H →
    ∀ (χ : DirichletCharacter ℂ q) (t : ℝ), |t| ≤ (X : ℝ) →
      M ≤ squaredDistance b (characterTwist χ t) X

def MRTShortExponentialInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (X H : ℕ), 10 ≤ H → H ≤ X →
    ∀ (b : ℕ → ℂ), Multiplicative b → OneBounded b →
      ∀ M : ℝ, MRTDistanceLowerBound b X H M → ∀ α : ℝ,
        shortExponentialIntegral b X H α ≤
          C * (H : ℝ) * (X : ℝ) * (Real.exp (-M / 20) + mrtShortError X H)

def MRTLiouvilleShortInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (X H : ℕ), 10 ≤ H → H ≤ X → ∀ α : ℝ,
    shortExponentialIntegral liouville X H α ≤
      C * (H : ℝ) * (X : ℝ) * mrtShortError X H

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.BigOperators _root_.ComplexConjugate
open _root_.MeasureTheory

noncomputable def fourierPolynomial {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) (θ : AddCircle (1 : ℝ)) : ℂ :=
  ∑ i ∈ S, coefficient i * fourier (frequency i) θ

noncomputable def roughFourierPolynomial (Z : Finset ℕ) (h : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  fourierPolynomial Z (fun z => (h : ℤ) * z) (fun z => (z : ℂ)⁻¹)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def shortWindowSum (b : ℕ → ℂ) (D : ℕ) (α : ℝ) (v : ℕ) : ℂ :=
  ∑ m ∈ range D, b (v + m + 1) * additiveCharacter α (m + 1)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def finitePrimeDivisorCount (P : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ p ∈ P, if p ∣ n then 1 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def forwardWindowPolynomial (f : ℕ → ℂ) (D v : ℕ) :
    AddCircle (1 : ℝ) → ℂ :=
  fourierPolynomial (Icc 1 D) (fun m => (m : ℤ)) (fun m => f (v + m))

noncomputable def backwardWindowPolynomial (g : ℕ → ℂ) (Q v : ℕ) :
    AddCircle (1 : ℝ) → ℂ :=
  fourierPolynomial (Icc 1 Q) (fun a => -(a : ℤ)) (fun a => g (v + a))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical _root_.ComplexConjugate

noncomputable def progressionSequence (f : ℕ → ℂ) (l : ℕ) [NeZero l]
    (a : ZMod l) (n : ℕ) : ℂ := if (n : ZMod l) = a then f n else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def roughShiftProfile (f g : ℕ → ℂ) (Z : Finset ℕ) (h n : ℕ) : ℂ :=
  ∑ z ∈ Z, (z : ℂ)⁻¹ * (f n * g (n + h * z))

noncomputable def roughShiftAverage (f g : ℕ → ℂ) (Z : Finset ℕ) (h Y : ℕ) : ℂ :=
  positivePrefix (roughShiftProfile f g Z h) Y / (Y : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex

noncomputable def minorArcGeometricBound (L α : ℝ) : ℝ :=
  if additiveCharacter α 1 = 1 then L
  else min L (2 / ‖additiveCharacter α 1 - 1‖)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

def minorArcWindowInterval (M A k H : ℕ) : Finset ℕ :=
  Ico (k / A + 1) (min M ((k + H) / A + 1))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.ComplexConjugate

noncomputable def minorArcWindowTerm (M A k H : ℕ) (z : ℂ) (β : ℝ) (m : ℕ) : ℂ :=
  if m ∈ minorArcWindowInterval M A k H then z * additiveCharacter β m else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def minorArcBilinearWindow (P : Finset ℕ) (M H d : ℕ)
    (a c : ℕ → ℂ) (α : ℝ) (k : ℕ) : ℂ :=
  ∑ m ∈ range M, a m * ∑ p ∈ P,
    minorArcWindowTerm M (d * p) k H (c p) (α * p) m

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.ComplexConjugate

noncomputable def mrtCharacterFourierCoefficient {q : ℕ} [NeZero q]
    (A : ZMod q → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ b : ZMod q, A b * conj (χ b)

noncomputable def mrtAdditiveCharacterCoefficient (q : ℕ) [NeZero q] (r : ℤ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  mrtCharacterFourierCoefficient (fun b : ZMod q => additiveCharacter ((r : ℝ) / q) b.val) χ

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.ComplexConjugate

noncomputable def mrtArchimedeanTwist (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)

noncomputable def mrtPrimeEulerTerm (b : ℕ → ℂ) (t : ℝ) (p : ℕ) : ℂ :=
  (b p * conj (mrtArchimedeanTwist t p)) / (p : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Set

noncomputable def mrtMeanSquareKernel (T ω t : ℝ) : ℂ :=
  (Real.exp (-|t| / T) : ℂ) * Complex.exp ((ω * t : ℝ) * Complex.I)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.BigOperators _root_.ComplexConjugate

noncomputable def mrtExponentialPolynomial {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, a i * Complex.exp ((freq i * t : ℝ) * Complex.I)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical

noncomputable def halaszFrequencyShell {ι : Type*} (S : Finset ι)
    (freq : ι → ℝ) (T u : ℝ) (k : ℕ) : Finset ι :=
  S.filter (fun i => Nat.floor (T * |freq i - u|) = k)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset
open scoped _root_.BigOperators

noncomputable def mrtDyadicPolynomial (b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  mrtExponentialPolynomial (Ioc N (2 * N))
    (fun n => b n / (n : ℂ)) (fun n => -Real.log (n : ℝ)) t

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory

noncomputable def mrtBoundarySet (N : ℕ) (δ : ℝ) : Finset ℕ :=
  Ioc N ⌊δ * (N : ℝ)⌋₊ ∪ Ioc (2 * N) ⌊δ * (2 * N : ℕ)⌋₊

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def mrtCompletePart (f : ℕ → ℂ) : ℕ → ℂ :=
  fromPrimePowers (fun p k => f p ^ k)

noncomputable def mrtCorrectionLocal (f : ℕ → ℂ) (p k : ℕ) : ℂ :=
  if k = 0 then 1 else f (p ^ k) - f p * f (p ^ (k - 1))

noncomputable def mrtCorrection (f : ℕ → ℂ) : ℕ → ℂ :=
  fromPrimePowers (mrtCorrectionLocal f)

noncomputable def mrtArithmetic (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else f n, by simp⟩

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszUnitCorrectionLocal (F : ℕ → ℂ) (p k : ℕ) : ℂ :=
  if k = 0 then 1 else F (p ^ k) - F (p ^ (k - 1))

noncomputable def halaszUnitCorrection (F : ℕ → ℂ) : ℕ → ℂ :=
  fromPrimePowers (halaszUnitCorrectionLocal F)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszPrimePowerLog (n : ℕ) : ℝ :=
  if IsPrimePow n then 2 * Real.log n else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators

noncomputable def mrtCorrectionWeight (f : ℕ → ℂ) (n : ℕ) : ℝ :=
  ‖mrtArithmetic (mrtCorrection f) n‖ * (n : ℝ) ^ (-(3 / 4 : ℝ))

noncomputable def mrtCorrectionEulerConstant : ℝ :=
  2 / (1 - (2 : ℝ) ^ (-(3 / 4 : ℝ)))

noncomputable def mrtCorrectionBound : ℝ :=
  Real.exp (mrtCorrectionEulerConstant * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical

noncomputable def mrtPrimePowerCoefficient (P : Finset ℕ) (a : ℕ → ℂ)
    (r n : ℕ) : ℂ :=
  ∑ v ∈ (Fintype.piFinset fun _ : Fin r => P).filter
    (fun v => (∏ i, v i) = n), ∏ i, a (v i)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate _root_.Classical

noncomputable def halaszCharacterL2 {k : ℕ} (m : Fin k → ℤ) :
    Lp ℂ 2 (halaszVinogradovHaar k) :=
  ContinuousMap.toLp 2 (halaszVinogradovHaar k) ℂ
    ⟨halaszVinogradovCharacter m,halasz_vinogradov_character_continuous m⟩

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Metric _root_.Set
open scoped _root_.ComplexConjugate

noncomputable def halaszCircleWindow (δ : ℝ) (x : AddCircle (1:ℝ)) : ℂ :=
  (closedBall 0 δ).indicator (fun _ => 1) x

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex

noncomputable def halaszLogTaylor (k : ℕ) (z h : ℝ) : ℝ :=
  ∑ i∈range k,(-1:ℝ)^i*(h/z)^(i+1)/(i+1)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set _root_.Metric
open scoped _root_.Classical _root_.ComplexConjugate

noncomputable def halaszTorusWindow {k : ℕ} (δ : Fin k → ℝ)
    (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  (Set.univ.pi (fun j => closedBall 0 (δ j))).indicator (fun _ => 1) α

lemma halasz_torus_window_measurable_set {k : ℕ} (δ : Fin k → ℝ) :
    MeasurableSet (Set.univ.pi (fun j => closedBall (0:AddCircle (1:ℝ)) (δ j))) := by
  exact MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_closedBall)

lemma halasz_torus_window_memLp {k : ℕ} (δ : Fin k → ℝ) :
    MemLp (halaszTorusWindow δ) 2 (halaszVinogradovHaar k) :=
  (memLp_const (1:ℂ)).indicator (halasz_torus_window_measurable_set δ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set _root_.Metric
open scoped _root_.Classical _root_.ComplexConjugate

def HalaszWindowNear {k : ℕ} (δ : Fin k → ℝ)
    (β γ : Fin k → AddCircle (1:ℝ)) : Prop := ∀ j, ‖β j-γ j‖≤2*δ j

lemma halasz_window_translate_memLp {k : ℕ} (δ : Fin k → ℝ)
    (β : Fin k → AddCircle (1:ℝ)) :
    MemLp (fun α => halaszTorusWindow δ (α+β)) 2 (halaszVinogradovHaar k) := by
  have : (halaszVinogradovHaar k).IsAddRightInvariant := by
    unfold halaszVinogradovHaar
    infer_instance
  exact (halasz_torus_window_memLp δ).comp_measurePreserving
    (measurePreserving_add_right (halaszVinogradovHaar k) β)

noncomputable def halaszWindowL2 {k : ℕ} (δ : Fin k → ℝ)
    (β : Fin k → AddCircle (1:ℝ)) : Lp ℂ 2 (halaszVinogradovHaar k) :=
  (halasz_window_translate_memLp δ β).toLp (fun α => halaszTorusWindow δ (α+β))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.ComplexConjugate

noncomputable def halaszScaledFrequency {k : ℕ} (γ : Fin k → ℝ)
    (m : Fin k → ℤ) : Fin k → AddCircle (1:ℝ) :=
  fun j => ((γ j*(m j:ℝ):ℝ):AddCircle (1:ℝ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex

noncomputable def halaszLogCoefficient {k : ℕ} (t z : ℝ) (j : Fin k) : ℝ :=
  t*(-1:ℝ)^j.val/(2*Real.pi*(j.val+1)*z^(j.val+1))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszIntegerWindow (L : ℕ) (γ δ : ℝ) : Finset ℤ :=
  (Icc (-(L:ℤ)) L).filter (fun d => ‖((γ*(d:ℝ):ℝ):AddCircle (1:ℝ))‖≤δ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def halaszDoubleWindow {k : ℕ} (r M : ℕ) (j : Fin k) : ℝ :=
  1/(16*(r:ℝ)*(M:ℝ)^(j.val+1))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def halaszDoubleWeight {k : ℕ} (r s M₁ M₂ : ℕ)
    (γ : Fin k → ℝ) (j : Fin k) : ℝ :=
  min (2*((s*M₂^(j.val+1):ℕ):ℝ)+1)
    (8*((s*M₂^(j.val+1):ℕ):ℝ)*halaszDoubleWindow r M₁ j+
      2*((s*M₂^(j.val+1):ℕ):ℝ)* |γ j| +8*halaszDoubleWindow r M₁ j/ |γ j| +2)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def halaszNormalizedWeight {k : ℕ} (r M : ℕ)
    (γ : Fin k → ℝ) (j : Fin k) : ℝ :=
  min (2*(r:ℝ)+1) ((5/2:ℝ)/(M:ℝ)^(j.val+1)+2*r*|γ j|+
    1/(2*r*((M:ℝ)^(j.val+1))^2*|γ j|))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def halaszLogWeightCost (k r : ℕ) : ℝ :=
  (8:ℝ)^(k+2)*(r+k+1)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

def halaszSelectedMoment (k : ℕ) : ℕ := (10*k+1)*k

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszMediumDegree (lam : ℝ) : ℕ := 3*⌈lam⌉₊+3
noncomputable def halaszMediumActive (lam : ℝ) : ℕ := ⌈3*lam/2⌉₊

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def halaszLargeDegreeMap (m : ℕ) (hm : 1≤ m) (i : Fin (2*m+1)) : Fin (12*m) :=
  ⟨8*m-1+i.val,by omega⟩

def halaszLargeDegrees (m : ℕ) (hm : 1≤ m) : Finset (Fin (12*m)) :=
  univ.image (halaszLargeDegreeMap m hm)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def halaszShortScale (N α : ℝ) : ℕ := ⌊N^α⌋₊

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtIntervalSum (S : Finset ℕ) (a : ℕ → ℂ) (x h : ℝ) : ℂ :=
  ∑ n ∈ S, if x < (n : ℝ) ∧ (n : ℝ) ≤ x + h then a n else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.FourierTransform _root_.Set
open scoped _root_.ENNReal

noncomputable def mrtLogWindowAtom (b a y : ℝ) : ℂ :=
  (Ico (b - a) b).indicator (fun y => (Real.exp (-y) : ℂ)) y

noncomputable def mrtWindowMultiplier (a t : ℝ) : ℂ :=
  (Complex.exp (((1 : ℂ) + (t : ℂ) * I) * a) - 1) / ((1 : ℂ) + (t : ℂ) * I)

noncomputable def mrtLogWindow (S : Finset ℕ) (a : ℕ → ℂ) (v y : ℝ) : ℂ :=
  ∑ n ∈ S, a n * mrtLogWindowAtom (Real.log (n : ℝ)) v y

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.FourierTransform _root_.Finset

noncomputable def mrtLogDirichlet (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n * Complex.exp (-((1 : ℂ) + (t : ℂ) * I) * Real.log (n : ℝ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.Classical

noncomputable def mrtWindowKernel (r t : ℝ) : ℝ :=
  min (16 * r^2) (25 / (1+t^2))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.Classical

noncomputable def mrtShortKernel (T t : ℝ) : ℝ :=
  min 1 (T^2/(1+t^2))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

open _root_.Filter

namespace TwoPointCorrelations

def LiouvilleLogSaving : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ a₁ a₂ b₁ b₂ : ℕ,
    0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      ‖affineSum liouville liouville a₁ a₂ b₁ b₂ ⌊X⌋₊‖ ≤
        C * X / Real.rpow (Real.log X) c

def BinaryCorrectedElliott : Prop :=
  ∀ f₁ f₂ : ℕ → ℂ, Multiplicative f₁ → Multiplicative f₂ →
    OneBounded f₁ → OneBounded f₂ →
    (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
    ∀ h₁ h₂ : ℕ, h₁ ≠ h₂ →
      Tendsto (fun N : ℕ => correlationSum f₁ f₂ h₁ h₂ N / (N : ℂ)) atTop (nhds 0)

def AffineCorrectedElliott : Prop :=
  ∀ f₁ f₂ : ℕ → ℂ, Multiplicative f₁ → Multiplicative f₂ →
    OneBounded f₁ → OneBounded f₂ →
    (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
    ∀ a₁ a₂ b₁ b₂ : ℕ, 0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
      Tendsto (fun N : ℕ => affineSum f₁ f₂ a₁ a₂ b₁ b₂ N / (N : ℂ)) atTop (nhds 0)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

open _root_.Filter
open scoped _root_.BigOperators

namespace TwoPointCorrelations

def ProgressionCorrectedElliott : Prop :=
  ∀ f g : ℕ → ℂ, Multiplicative f → Multiplicative g →
    OneBounded f → OneBounded g →
    (UniformlyNonpretentious f ∨ UniformlyNonpretentious g) →
    ∀ h l b : ℕ, 0 < h → 0 < l →
      Tendsto (fun N : ℕ => residuePrefix (fun n => f n * g (n + h)) l b N / (N : ℂ))
        atTop (nhds 0)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

open _root_.Filter

namespace TwoPointCorrelations

def UnshiftedCorrectedElliott : Prop :=
  ∀ f g : ℕ → ℂ, Multiplicative f → Multiplicative g →
    OneBounded f → OneBounded g →
    (UniformlyNonpretentious f ∨ UniformlyNonpretentious g) →
    ∀ h : ℕ, 0 < h →
      Tendsto (fun N : ℕ => correlationSum f g 0 h N / (N : ℂ)) atTop (nhds 0)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def positiveNormalization (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else f n

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α] {N : ℕ}

def columnRepresentativeCandidates (label : Fin N → α) (perfect : Finset (Fin N))
    (i : Fin N) : Finset (Fin N) :=
  let p := perfect.filter (fun j => label j = label i)
  if p.Nonempty then p else univ.filter (fun j => label j = label i)

lemma columnRepresentativeCandidates_nonempty (label : Fin N → α)
    (perfect : Finset (Fin N)) (i : Fin N) :
    (columnRepresentativeCandidates label perfect i).Nonempty := by
  dsimp only [columnRepresentativeCandidates]
  split_ifs with h
  · exact h
  · exact ⟨i, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩

def columnRepresentative (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N) : Fin N :=
  (columnRepresentativeCandidates label perfect i).min'
    (columnRepresentativeCandidates_nonempty label perfect i)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

def intervalColor (D x : ℤ) : ℤ := (x / D) % 5

def forwardColorPair (D x y : ℤ) : Prop :=
  (intervalColor D y - intervalColor D x) % 5 = 1 ∨
    (intervalColor D y - intervalColor D x) % 5 = 2

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

abbrev ForwardColorCode := Fin 5 × Fin 2

abbrev sourceColor (D : ℤ) (c : ForwardColorCode) (x : ℤ) : Prop :=
  intervalColor D x = c.1.val

abbrev targetColor (D : ℤ) (c : ForwardColorCode) (y : ℤ) : Prop :=
  intervalColor D y = ((c.1.val : ℤ) + c.2.val + 1) % 5

noncomputable def sourceColorFunction {V : Type*} (D : ℤ) (site : V → ℤ)
    (c : ForwardColorCode) (F : V → ℂ) : V → ℂ :=
  fun i => if sourceColor D c (site i) then F i else 0

noncomputable def targetColorFunction {V : Type*} (D : ℤ) (site : V → ℤ)
    (c : ForwardColorCode) (G : V → ℂ) : V → ℂ :=
  fun i => if targetColor D c (site i) then G i else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.BinaryTree

def forestBits : BinaryTree Bool → List Bool
  | .nil => [false]
  | .node b l r => true :: b :: (forestBits l ++ forestBits r)

@[simp] theorem forestBits_length (t : BinaryTree Bool) :
    (forestBits t).length = 3 * t.numNodes + 1 := by
  induction t with
  | nil => rfl
  | node b l r hl hr => simp only [forestBits, List.length_cons, List.length_append,
      hl, hr, numNodes]; omega

def parseForestBits : ℕ → List Bool → Option (BinaryTree Bool × List Bool)
  | 0, _ => none
  | _ + 1, false :: rest => some (.nil, rest)
  | fuel + 1, true :: b :: rest => do
      let (l, rest') ← parseForestBits fuel rest
      let (r, rest'') ← parseForestBits fuel rest'
      some (.node b l r, rest'')
  | _ + 1, _ => none

theorem parseForestBits_encode (t : BinaryTree Bool) (fuel : ℕ)
    (hf : t.numNodes < fuel) (rest : List Bool) :
    parseForestBits fuel (forestBits t ++ rest) = some (t, rest) := by
  induction t generalizing fuel rest with
  | nil =>
      cases fuel with
      | zero => simp only [numNodes] at hf; omega
      | succ fuel => rfl
  | node b l r hl hr =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hlf : l.numNodes < fuel := by simp only [numNodes] at hf; omega
          have hrf : r.numNodes < fuel := by simp only [numNodes] at hf; omega
          simp [forestBits, List.append_assoc, parseForestBits, hl fuel hlf, hr fuel hrf]

def paddedForestBits (N : ℕ) (t : BinaryTree Bool) : List Bool :=
  forestBits t ++ List.replicate (3 * (N - t.numNodes)) false

lemma paddedForestBits_length (N : ℕ) (t : BinaryTree Bool) (ht : t.numNodes ≤ N) :
    (paddedForestBits N t).length = 3 * N + 1 := by
  simp only [paddedForestBits, List.length_append, forestBits_length, List.length_replicate]
  omega

theorem paddedForestBits_injective (N : ℕ) :
    Function.Injective (fun t : {t : BinaryTree Bool // t.numNodes ≤ N} =>
      paddedForestBits N t.val) := by
  intro t u heq
  apply Subtype.ext
  have hp := congrArg (parseForestBits (N + 1)) heq
  simp only [paddedForestBits] at hp
  rw [parseForestBits_encode _ _ (by omega),
    parseForestBits_encode _ _ (by omega)] at hp
  exact congrArg Prod.fst (Option.some.inj hp)

def boundedForestCode (N : ℕ) (t : {t : BinaryTree Bool // t.numNodes ≤ N}) :
    Fin (3 * N + 1) → Bool :=
  fun i => (paddedForestBits N t.val).get
    ⟨i, by rw [paddedForestBits_length N t.val t.property]; exact i.isLt⟩

theorem boundedForestCode_injective (N : ℕ) : Function.Injective (boundedForestCode N) := by
  intro t u heq
  apply paddedForestBits_injective N
  apply List.ext_get
  · rw [paddedForestBits_length N t.val t.property,
      paddedForestBits_length N u.val u.property]
  · intro i ht hu
    have hi : i < 3 * N + 1 := by simpa only [paddedForestBits_length N t.val t.property] using ht
    exact congrFun heq ⟨i, hi⟩

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

instance boundedForestFinite (N : ℕ) : Finite {t : BinaryTree Bool // t.numNodes ≤ N} :=
  Finite.of_injective (boundedForestCode N) (boundedForestCode_injective N)

noncomputable instance boundedForestFintype (N : ℕ) :
    Fintype {t : BinaryTree Bool // t.numNodes ≤ N} := Fintype.ofFinite _

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.SimpleGraph _root_.BinaryTree

universe u

lemma forest_representation_numNodes {V : Type*} [Fintype V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hcover : ∀ v, v ∈ forestNodes t) :
    t.numNodes = Fintype.card V := by
  rw [← forestNodes_length]
  apply le_antisymm ht.length_le_card
  have hsurj : Function.Surjective (fun i : Fin (forestNodes t).length => (forestNodes t).get i) := by
    intro v
    exact List.mem_iff_get.mp (hcover v)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective _ hsurj

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.SimpleGraph _root_.BinaryTree

variable {V W : Type*}

def forestIndexEquiv [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t) :
    V ≃ Fin (forestNodes t).length :=
  (List.Nodup.getEquivOfForallMemList (forestNodes t) ht hc).symm

lemma forest_shape_length (t : BinaryTree V) (s : BinaryTree W)
    (h : t.map (fun _ => ()) = s.map (fun _ => ())) :
    (forestNodes t).length = (forestNodes s).length := by
  simpa only [forestNodes_length, forest_numNodes_map] using congrArg numNodes h

def forestShapeEquiv [DecidableEq V] [DecidableEq W]
    (t : BinaryTree V) (s : BinaryTree W)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (hs : (forestNodes s).Nodup) (hd : ∀ w, w ∈ forestNodes s)
    (hshape : t.map (fun _ => ()) = s.map (fun _ => ())) : V ≃ W :=
  (forestIndexEquiv t ht hc).trans
    ((finCongr (forest_shape_length t s hshape)).trans (forestIndexEquiv s hs hd).symm)

@[simp] theorem forestShapeEquiv_index [DecidableEq V] [DecidableEq W]
    (t : BinaryTree V) (s : BinaryTree W)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (hs : (forestNodes s).Nodup) (hd : ∀ w, w ∈ forestNodes s)
    (hshape : t.map (fun _ => ()) = s.map (fun _ => ())) (v : V) :
    (forestNodes s).idxOf (forestShapeEquiv t s ht hc hs hd hshape v) =
      (forestNodes t).idxOf v := by
  change (forestIndexEquiv s hs hd (forestShapeEquiv t s ht hc hs hd hshape v)).val = _
  simp only [forestShapeEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem forestShapeEquiv_adjacent [DecidableEq V] [DecidableEq W]
    (t : BinaryTree V) (s : BinaryTree W)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (hs : (forestNodes s).Nodup) (hd : ∀ w, w ∈ forestNodes s)
    (hshape : t.map (fun _ => ()) = s.map (fun _ => ())) (a b : V) :
    forestAdjacent s (forestShapeEquiv t s ht hc hs hd hshape a)
      (forestShapeEquiv t s ht hc hs hd hshape b) ↔ forestAdjacent t a b := by
  rw [← numberForest_adjacent s hs hd, forestShapeEquiv_index, forestShapeEquiv_index,
    ← numberForest_eq_of_same_shape t s hshape 0, numberForest_adjacent t ht hc]

def representedGraphIso [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (t : BinaryTree V) (s : BinaryTree W)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (hs : (forestNodes s).Nodup) (hd : ∀ w, w ∈ forestNodes s)
    (hG : ∀ a b, forestAdjacent t a b ↔ G.Adj a b)
    (hH : ∀ a b, forestAdjacent s a b ↔ H.Adj a b)
    (hshape : t.map (fun _ => ()) = s.map (fun _ => ())) : G ≃g H where
  toEquiv := forestShapeEquiv t s ht hc hs hd hshape
  map_rel_iff' := by
    intro a b
    rw [← hH, forestShapeEquiv_adjacent t s ht hc hs hd hshape, hG]

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.SimpleGraph

variable {K ι V : Type*} [Field K] [AddCommGroup V] [Module K V]

def affineIncidenceGraph (anchor d : ι → V) : SimpleGraph (ι ⊕ V) where
  Adj
    | .inl i, .inr x => ∃ t : K, x = anchor i + t • d i
    | .inr x, .inl i => ∃ t : K, x = anchor i + t • d i
    | _, _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> exact h⟩
  loopless := ⟨by intro x; cases x <;> exact id⟩

def edgeSide (anchor : ι → V) (φ : V →ₗ[K] K) (i : ι) (x : V) :
    (ι ⊕ V) → Prop
  | .inl j => j ≠ i ∧ φ (anchor j) = φ x
  | .inr y => φ y = φ x

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Submodule

variable {K α ι : Type*} [Field K] [Fintype α] [Fintype ι]
  [DecidableEq α] [DecidableEq ι]

def EqualLabelPairs (label : ι → α) :=
  {p : α × ι × ι // label p.2.1 = p.1 ∧ label p.2.2 = p.1}

instance equalLabelPairsFintype (label : ι → α) : Fintype (EqualLabelPairs label) :=
  inferInstanceAs (Fintype {p : α × ι × ι // label p.2.1 = p.1 ∧ label p.2.2 = p.1})

instance equalLabelPairsDecidableEq (label : ι → α) : DecidableEq (EqualLabelPairs label) :=
  inferInstanceAs (DecidableEq {p : α × ι × ι // label p.2.1 = p.1 ∧ label p.2.2 = p.1})

noncomputable def labelPairVectors (label : ι → α) (offset : ι → α → K)
    (p : EqualLabelPairs label) : Fin 2 → (α → K) :=
  ![offset p.val.2.1 - offset p.val.2.2, Pi.basisFun K α p.val.1]

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {K α V : Type*} [Field K] [Fintype α]
  [AddCommGroup V] [Module K V]

noncomputable def formalDeparture (label : ℕ → α) (coefficient : ℕ → K) (n : ℕ) : α → K :=
  ∑ i ∈ range n, coefficient i • Pi.basisFun K α (label i)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Submodule _root_.Matrix

variable {K α ρ : Type*} [Field K] [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ]

noncomputable def controlCoordinates (control : ρ → α) : Finset α := univ.image control

noncomputable def deleteControlCoordinates (control : ρ → α) :
    (α → K) →ₗ[K] ({j : α // j ∉ controlCoordinates control} → K) :=
  LinearMap.pi (fun i => LinearMap.proj (i : α))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.SimpleGraph

variable {V : Type*}

def NoImmediateReturn : List V → Prop
  | a :: b :: c :: rest => a ≠ c ∧ NoImmediateReturn (b :: c :: rest)
  | _ => True

variable {K ι : Type*} [Field K] [AddCommGroup V] [Module K V]

def incidenceVertices (i : ι) : List (V × ι) → List (ι ⊕ V)
  | [] => [.inl i]
  | (x, j) :: rest => .inl i :: .inr x :: incidenceVertices j rest

def IncidenceChain (anchor d : ι → V) (i : ι) : List (V × ι) → Prop
  | [] => True
  | (x, j) :: rest =>
      (∃ t : K, x = anchor i + t • d i) ∧
      (∃ t : K, x = anchor j + t • d j) ∧ IncidenceChain anchor d j rest

def IncidenceReduced (i : ι) : List (V × ι) → Prop
  | [] => True
  | (x, j) :: rest => i ≠ j ∧
      (∀ y k, rest.head? = some (y, k) → x ≠ y) ∧ IncidenceReduced j rest

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def retainedPrimeDivisors (S : Finset ℕ) : Finset ℕ :=
  S.powerset.image (fun U => ∏ p ∈ U, p)

lemma retainedPrimeDivisor_factors (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {u : ℕ} (hu : u ∈ retainedPrimeDivisors S) : u.primeFactors ⊆ S := by
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hu
  have hUS : U ⊆ S := mem_powerset.mp hU
  rw [Nat.primeFactors_prod (fun p hp => hS p (hUS hp))]
  exact hUS

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def natDivisibilityIndicator (d n : ℕ) : ℂ := if d ∣ n then 1 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def smoothDilationTerm (q : ℕ) (f : ℕ → ℂ) (a n : ℕ) : ℂ :=
  if a.primeFactors ⊆ q.primeFactors ∧ a ∣ n then
    f (q * a) * coprimeRestriction q f (n / a) else 0

noncomputable def truncatedDilation (q : ℕ) (f : ℕ → ℂ) (K n : ℕ) : ℂ :=
  if primeSmoothPart q.primeFactors n ≤ K then f (q * n) else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def dilationSequence (a : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if a ∣ n then f (n / a) else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtPrimeSquareCount (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, if p ^ 2 ∣ n then 1 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def mrtGcdTriple (v : ℕ × ℕ) : ℕ × (ℕ × ℕ) :=
  (Nat.gcd v.1 v.2, (v.1 / Nat.gcd v.1 v.2, v.2 / Nat.gcd v.1 v.2))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def mrtFactoredUpTo (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => n ∈ Nat.factoredNumbers P)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def mrtMixedPrimeFiber (P M : Finset ℕ) (r n : ℕ) :
    Finset ((Fin r → ℕ) × ℕ) :=
  ((Fintype.piFinset (fun _ : Fin r => P)) ×ˢ M).filter
    (fun v => (∏ i, v.1 i) * v.2 = n)

noncomputable def mrtMixedPrimeCoefficient (P M : Finset ℕ)
    (a b : ℕ → ℂ) (r n : ℕ) : ℂ :=
  ∑ v ∈ mrtMixedPrimeFiber P M r n, (∏ i, a (v.1 i)) * b v.2

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtRamareCorrection (P : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) : ℂ :=
  (if finitePrimeDivisorCount P n = 0 then 0 else F n) -
    ∑ p ∈ P, if p ∣ n then
      F n / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def mrtRamareWeight (P : Finset ℕ) (n p : ℕ) : ℝ :=
  if p ∣ n then 1 / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℝ) else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def mrtCoarseRamareWeight (P : Finset ℕ) (L : ℕ → ℝ)
    (N n : ℕ) : ℝ :=
  ∑ p ∈ P, mrtRamareWeight P n p *
    if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then 1 else 0

noncomputable def mrtCoarseBoundaryCoefficient (P : Finset ℕ) (L : ℕ → ℝ)
    (N n : ℕ) : ℝ :=
  (if N < n ∧ n ≤ 2 * N then ∑ p ∈ P, mrtRamareWeight P n p else 0) -
    mrtCoarseRamareWeight P L N n

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtWeightedRamareCoefficient (P : Finset ℕ) (F : ℕ → ℂ)
    (n : ℕ) : ℂ := F n * ((∑ p ∈ P, mrtRamareWeight P n p : ℝ) : ℂ)

noncomputable def mrtCoarsePolynomial (P : Finset ℕ) (L : ℕ → ℝ)
    (N : ℕ) (F : ℕ → ℂ) (t : ℝ) : ℂ :=
  mrtExponentialPolynomial (Ioc 0 (4 * N))
    (fun n => F n * (mrtCoarseRamareWeight P L N n : ℂ) / (n : ℂ))
    (fun n => -Real.log (n : ℝ)) t

noncomputable def mrtCoarseBoundaryPolynomial (P : Finset ℕ) (L : ℕ → ℝ)
    (N : ℕ) (δ : ℝ) (F : ℕ → ℂ) (t : ℝ) : ℂ :=
  mrtExponentialPolynomial (mrtBoundarySet N δ)
    (fun n => F n * (mrtCoarseBoundaryCoefficient P L N n : ℂ) / (n : ℂ))
    (fun n => -Real.log (n : ℝ)) t

noncomputable def mrtSupportedCoefficient (P : Finset ℕ) (F : ℕ → ℂ)
    (n : ℕ) : ℂ := if finitePrimeDivisorCount P n = 0 then 0 else F n

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def mrtDirichletAtom (F : ℕ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  F n / (n : ℂ) * Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I)

noncomputable def mrtCofactorPolynomial (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) (a t : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 (4 * N),
    if (N : ℝ) < a * m ∧ a * m ≤ 2 * N then
      mrtDirichletAtom F m t / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)
    else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators

def mrtPrimeAvoids (P : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ P, ¬ p ∣ n

noncomputable def mrtPrimeMask (P : Finset ℕ) (n : ℕ) : ℝ :=
  if mrtPrimeAvoids P n then 1 else 0

def mrtTypical {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ) (n : ℕ) : Prop :=
  ∀ j ∈ J, ∃ p ∈ P j, p ∣ n

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtCountMask (P : Finset ℕ) (u : ℝ) (n : ℕ) : ℝ :=
  u ^ finitePrimeDivisorCount P n

noncomputable def mrtCountMaskedCoefficient (F : ℕ → ℂ) (P : Finset ℕ)
    (u : ℝ) (n : ℕ) : ℂ := F n * (mrtCountMask P u n : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical

noncomputable def mrtMaskedCoefficient (F : ℕ → ℂ) (P : Finset ℕ) (n : ℕ) : ℂ :=
  F n * (mrtPrimeMask P n : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtTypicalCoefficient {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (n : ℕ) : ℂ :=
  if mrtTypical J P n then F n else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma major_arc_divisor_quotient_pos {q : ℕ} (hq : 0 < q)
    (d : {d : ℕ // d ∈ q.divisors}) : 0 < q/d.val := by
  have hdq := (Nat.mem_divisors.mp d.property).1
  exact Nat.div_pos (Nat.le_of_dvd hq hdq) (Nat.pos_of_dvd_of_pos hdq hq)

noncomputable def majorArcDivisorTerm {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (q : ℕ) (hq : 0 < q) (r : ℤ)
    (d : {d : ℕ // d ∈ q.divisors}) (n : ℕ) : ℂ := by
  letI : NeZero (q/d.val) := ⟨(major_arc_divisor_quotient_pos hq d).ne'⟩
  exact F d.val * ∑ χ : DirichletCharacter ℂ (q/d.val),
    mrtAdditiveCharacterCoefficient (q/d.val) r χ *
      dilationSequence d.val (mrtTypicalCoefficient J P (twistByCharacter F χ)) n

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def majorArcDivisorWindow {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (q : ℕ) (hq : 0 < q) (r : ℤ)
    (d : {d : ℕ // d ∈ q.divisors}) (v H : ℕ) : ℂ := by
  letI : NeZero (q/d.val) := ⟨(major_arc_divisor_quotient_pos hq d).ne'⟩
  exact F d.val * ∑ χ : DirichletCharacter ℂ (q/d.val),
    mrtAdditiveCharacterCoefficient (q/d.val) r χ *
      shortExponentialSum (dilationSequence d.val (mrtTypicalCoefficient J P (twistByCharacter F χ))) H 0 v

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def mrtCorrectionMaskedCofactor {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (d n : ℕ) : ℂ :=
  if mrtTypical J P (d*n) then mrtCompletePart F n else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

noncomputable def mrtCorrectionCutoff (W : ℝ) : ℕ := ⌊W ^ (5 : ℕ)⌋₊

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def mrtArcSubdivisionLength (H : ℕ) (W : ℝ) : ℕ := ⌊(H : ℝ) / W⌋₊

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Filter

noncomputable def majorArcParameter (L H M : ℝ) : ℝ :=
  min ((Real.log H)^5) (min (L^(1/125:ℝ)) (Real.exp (M/3)))

noncomputable def majorArcWorkingError (W : ℝ) : ℝ :=
  (1+Real.log W)*W^(-1/5:ℝ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtPrimeProductError (P : Finset ℕ)
    (active : ℕ → ℕ → Prop) (C A B : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ P, if p ∣ n ∧ active p n then
    (C n - A p * B (n / p)) / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
  else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def minorArcRamareApprox (P : Finset ℕ) (A B : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ P, if p ∣ n then
    A p * B (n / p) / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def minorArcRamareCofactor (P : Finset ℕ) (B : ℕ → ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else B m / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def minorArcDyadicPrimes (P : Finset ℕ) (j : ℕ) : Finset ℕ :=
  P.filter (fun p => Nat.log 2 p = j)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtPrimeExtractionError (P : Finset ℕ) (L : ℕ → ℝ)
    (N : ℕ) (C A B : ℕ → ℂ) : ℕ → ℂ :=
  mrtPrimeProductError P
    (fun p n => (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N)
    C A B

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Filter

noncomputable def mrtWorkingCap (W : ℝ) : ℕ :=
  ⌊Real.exp (Real.sqrt W / 2)⌋₊

noncomputable def mrtWorkingLength (H : ℕ) (W : ℝ) : ℕ :=
  if (H : ℝ) ≤ Real.exp (Real.sqrt W) then H else mrtWorkingCap W

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Filter

noncomputable def majorArcWorkingLength (H : ℕ) (W : ℝ) : ℕ :=
  mrtWorkingLength H (W^(2/5:ℝ))

end TwoPointCorrelations

end OAI

end

section

namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

end Erdos970

end

section

namespace Erdos970

open scoped _root_.ContDiff

open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory _root_.Set _root_.Function

variable {𝕂 : Type*} [RCLike 𝕂]

local notation (name := mellintransform) "𝓜" => mellin

noncomputable def MellinConvolution (f g : ℝ → 𝕂) (x : ℝ) : 𝕂 :=
  ∫ y in Ioi 0, f y * g (x / y) / y

noncomputable def DeltaSpike (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ν (x ^ (1 / ε)) / ε

noncomputable def Smooth1 (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) (DeltaSpike ν ε)

end Erdos970

end

section

namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle

end Rectangle

def RectangleBorder (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

end Erdos970

end

section

namespace OAI

namespace TwoPointCorrelations

structure SignedStep where
  forward : Bool
  tuple : ℕ
  padding : ℕ
  deriving DecidableEq

namespace SignedStep

def flip (a : SignedStep) : SignedStep := ⟨!a.forward, a.tuple, a.padding⟩

def displacement (h : ℕ) (a : SignedStep) : ℤ :=
  (if a.forward then 1 else -1) * (h : ℤ) * a.padding * a.tuple

def divisor (a : SignedStep) : ℤ := (a.padding : ℤ) * a.tuple

end SignedStep

def wordDisplacement (h : ℕ) (w : List SignedStep) : ℤ :=
  (w.map (SignedStep.displacement h)).sum

def reverseWord (w : List SignedStep) : List SignedStep := w.reverse.map SignedStep.flip

def PositiveWord (h : ℕ) (x : ℤ) : List SignedStep → Prop
  | [] => True
  | a :: w => a.divisor ∣ x ∧ PositiveWord h (x + a.displacement h) w

def WordVertex (h : ℕ) (x : ℤ) (w : List SignedStep) (y : ℤ) : Prop :=
  ∃ u v, w = u ++ v ∧ y = x + wordDisplacement h u

def OrientedInfix (u w : List SignedStep) : Prop := u <:+: w ∨ u <:+: reverseWord w

def MinimalWord (P : List SignedStep → Prop) (w : List SignedStep) : Prop :=
  P w ∧ ∀ u, OrientedInfix u w → u.length < w.length → ¬P u

def TuplePrimeAt (w : List SignedStep) (p i : ℕ) : Prop :=
  p.Prime ∧ ∃ a, w[i]? = some a ∧ p ∣ a.tuple

def TuplePrimeIntervals (w : List SignedStep) : Prop :=
  ∀ p i j k, i ≤ j → j ≤ k → k < w.length →
    TuplePrimeAt w p i → TuplePrimeAt w p k → TuplePrimeAt w p j

def ForwardProhibited (h s : ℕ) (supply : ℕ → ℕ → Prop) (w : List SignedStep) : Prop :=
  3 ≤ w.length ∧ w.length ≤ s ∧
  (∀ a ∈ w, supply a.tuple a.padding) ∧
  w.IsChain (fun a b => a.tuple ≠ b.tuple) ∧ TuplePrimeIntervals w ∧
  ∃ p, TuplePrimeAt w p 0 ∧ ¬TuplePrimeAt w p (w.length - 1) ∧
    ∃ a, 0 < a ∧ a + 1 < w.length ∧ (p : ℤ) ∣ wordDisplacement h (w.drop a)

def ProhibitedWitness (h s : ℕ) (supply : ℕ → ℕ → Prop) (x : ℤ)
    (w : List SignedStep) : Prop :=
  PositiveWord h x w ∧ MinimalWord (ForwardProhibited h s supply) w

def ProhibitedSite (h s : ℕ) (supply : ℕ → ℕ → Prop) (x : ℤ) : Prop :=
  ∃ w, ProhibitedWitness h s supply x w

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

def OccurrenceIntervals {α : Type*} (P : α → ℕ → Prop) (a b : ℕ) : Prop :=
  ∀ p i j k, a ≤ i → i ≤ j → j ≤ k → k < b → P p i → P p k → P p j

def OccurrenceHole {α : Type*} (P : α → ℕ → Prop) (n : ℕ) (p : α) (i j : ℕ) : Prop :=
  i < j ∧ j < n ∧ P p i ∧ P p j ∧ ∃ k, i < k ∧ k < j ∧ ¬P p k

def intervalDisplacement (D : ℕ → ℤ) (a b : ℕ) : ℤ := ∑ i ∈ Ico a b, D i

def ProhibitedInterval {α : Type*} (P : α → ℕ → Prop) (D : ℕ → ℤ)
    (prime : α → ℕ) (a b : ℕ) : Prop :=
  a + 2 < b ∧ OccurrenceIntervals P a b ∧
  ∃ p, P p a ∧ ¬P p (b - 1) ∧ ∃ c, a < c ∧ c + 1 < b ∧
    (prime p : ℤ) ∣ intervalDisplacement D c b

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

def wordStepDisplacement (h : ℕ) (w : List SignedStep) (i : ℕ) : ℤ :=
  ((w[i]?).map (SignedStep.displacement h)).getD 0

def wordSlice (w : List SignedStep) (a b : ℕ) : List SignedStep := (w.drop a).take (b - a)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def wordPrimeContribution (h : ℕ) (w : List SignedStep) (p a b : ℕ) : ℤ := by
  classical
  exact ∑ i ∈ Ico a b, if TuplePrimeAt w p i then wordStepDisplacement h w i else 0

def ActivePrime (h : ℕ) (w : List SignedStep) (p : ℕ) : Prop :=
  ∃ c a b, a ≤ b ∧ b ≤ w.length ∧ (∃ i, TuplePrimeAt w c i) ∧
    (c : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) a b ∧
    ¬(c : ℤ) ∣ wordPrimeContribution h w p a b

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.SimpleGraph

structure ForestPathData (N segments : ℕ) where
  vertices : ℕ
  vertex_bound : vertices ≤ N
  graph : SimpleGraph (Fin vertices)
  acyclic : graph.IsAcyclic
  tree : BinaryTree (Fin vertices)
  nodup : (forestNodes tree).Nodup
  cover : ∀ v, v ∈ forestNodes tree
  adjacent : ∀ a b, forestAdjacent tree a b ↔ graph.Adj a b
  color : Fin vertices → Bool
  start : Fin segments → Fin vertices
  finish : Fin segments → Fin vertices
  walk : ∀ i, graph.Walk (start i) (finish i)
  reduced : ∀ i, List.IsChain (· ≠ ·) (walk i).edges

namespace ForestPathData

variable {N segments : ℕ}

def pattern (d : ForestPathData N segments) : Fin segments → List ℕ :=
  fun i => (d.walk i).support.map (fun v => (forestNodes d.tree).idxOf v)

def shape (d : ForestPathData N segments) : {t : BinaryTree Bool // t.numNodes ≤ N} :=
  ⟨d.tree.map d.color, by
    rw [forest_numNodes_map, forest_representation_numNodes d.tree d.nodup d.cover]
    simpa only [Fintype.card_fin] using d.vertex_bound⟩

def index (d : ForestPathData N segments) (v : Fin d.vertices) : Fin N :=
  ⟨(forestNodes d.tree).idxOf v, by
    have hlt := List.idxOf_lt_length_iff.mpr (d.cover v)
    rw [forestNodes_length, forest_representation_numNodes d.tree d.nodup d.cover,
      Fintype.card_fin] at hlt
    exact hlt.trans_le d.vertex_bound⟩

abbrev Code (N segments : ℕ) :=
  {t : BinaryTree Bool // t.numNodes ≤ N} × (Fin segments → Fin N × Fin N)

def code (d : ForestPathData N segments) : Code N segments :=
  (d.shape, fun i => (d.index (d.start i), d.index (d.finish i)))

end ForestPathData

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def decodeForestPaths {N segments : ℕ}
    (code : ForestPathData.Code N segments) : Fin segments → List ℕ := by
  classical
  exact if h : ∃ d : ForestPathData N segments, d.code = code then h.choose.pattern else fun _ => []

inductive CanonicalColumnLabel
  | regular : ℕ → CanonicalColumnLabel
  | omitted : ℕ → CanonicalColumnLabel
  | freshImperfect : ℕ → CanonicalColumnLabel
  deriving DecidableEq

def evenEntries {α : Type*} : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: rest => a :: evenEntries rest

def mergeColumnRuns {α : Type*} : List Bool → List (List α) → List α → List α
  | [], _, _ => []
  | true :: mask, regular, omitted =>
      regular.headD [] ++ mergeColumnRuns mask regular.tail omitted
  | false :: mask, regular, omitted =>
      omitted.head?.toList ++ mergeColumnRuns mask regular omitted.tail

def expandColumnRuns : List (Bool × Bool) → List CanonicalColumnLabel →
    Option CanonicalColumnLabel → List (Option CanonicalColumnLabel)
  | [], _, _ => []
  | (true, _) :: flags, runs, _ => none :: expandColumnRuns flags runs none
  | (false, true) :: flags, runs, _ =>
      runs.head? :: expandColumnRuns flags runs.tail runs.head?
  | (false, false) :: flags, runs, previous =>
      previous :: expandColumnRuns flags runs previous

def attachImperfectLabels (full : List (Option CanonicalColumnLabel)) :
    List (Option CanonicalColumnLabel) → List ℕ → List CanonicalColumnLabel
  | [], _ => []
  | some a :: rest, refs => a :: attachImperfectLabels full rest refs
  | none :: rest, refs =>
      let j := refs.headD 0
      ((full[j]?.join).getD (.freshImperfect j)) ::
        attachImperfectLabels full rest refs.tail

abbrev ColumnDecoderCode (N segments omitted imperfect : ℕ) :=
  ForestPathData.Code N segments ×
    (Fin N → Bool) × (Fin N → Bool × Bool) ×
    (Fin omitted → Fin N) × (Fin imperfect → Fin N)

noncomputable def decodeColumnLabels {N segments omitted imperfect : ℕ}
    (code : ColumnDecoderCode N segments omitted imperfect) : List CanonicalColumnLabel :=
  let paths := List.ofFn (fun i => (evenEntries (decodeForestPaths code.1 i)).map
    CanonicalColumnLabel.regular)
  let omittedLabels := List.ofFn (fun i => CanonicalColumnLabel.omitted (code.2.2.2.1 i).val)
  let runs := mergeColumnRuns (List.ofFn code.2.1) paths omittedLabels
  let full := expandColumnRuns (List.ofFn code.2.2.1) runs none
  attachImperfectLabels full full (List.ofFn (fun i => (code.2.2.2.2 i).val))

noncomputable def decodeColumnPattern {N segments omitted imperfect : ℕ}
    (code : ColumnDecoderCode N segments omitted imperfect) : Fin N → Fin N → Bool :=
  fun i j => decide ((decodeColumnLabels code).getD i (.freshImperfect 0) =
    (decodeColumnLabels code).getD j (.freshImperfect 0))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

abbrev BoundedColumnDecoderCode (N segments omitted imperfect : ℕ) :=
  Σ s : Fin (segments + 1), Σ o : Fin (omitted + 1), Σ i : Fin (imperfect + 1),
    ColumnDecoderCode N s.val o.val i.val

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def decodeColumnPrefixPattern {n N S O I : ℕ} (hn : n ≤ N)
    (code : ColumnDecoderCode N S O I) : Fin n → Fin n → Bool :=
  fun i j => decodeColumnPattern code (Fin.castLE hn i) (Fin.castLE hn j)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Filter

noncomputable def columnBudgetCap (N : ℕ) (L : ℝ) : ℕ :=
  min N ⌊66 * L ^ (0.92 : ℝ)⌋₊

noncomputable abbrev BudgetColumnCode (N : ℕ) (L : ℝ) :=
  BoundedColumnDecoderCode N (columnBudgetCap N L) (columnBudgetCap N L) (columnBudgetCap N L)

noncomputable def decodeBudgetColumnPattern {n N : ℕ} {L : ℝ} (hn : n ≤ N)
    (code : BudgetColumnCode N L) : Fin n → Fin n → Bool :=
  decodeColumnPrefixPattern hn code.2.2.2

noncomputable abbrev BudgetColumnArrayCode (J N : ℕ) (L : ℝ) :=
  Fin J → BudgetColumnCode N L

noncomputable instance budgetColumnArrayFintype (J N : ℕ) (L : ℝ) :
    Fintype (BudgetColumnArrayCode J N L) := by
  classical
  letI : Fintype (BudgetColumnCode N L) := inferInstance
  exact Pi.instFintype

noncomputable def decodeBudgetColumnArray {n J N : ℕ} {L : ℝ} (hn : n ≤ N)
    (code : BudgetColumnArrayCode J N L) : Fin J → Fin n → Fin n → Bool :=
  fun j => decodeBudgetColumnPattern hn (code j)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

def columnFlags : List (Option α) → Option α → List (Bool × Bool)
  | [], _ => []
  | none :: rest, _ => (true, false) :: columnFlags rest none
  | some a :: rest, previous =>
      (false, decide (previous ≠ some a)) :: columnFlags rest (some a)

def columnRunHeads : List (Option α) → Option α → List α
  | [], _ => []
  | none :: rest, _ => columnRunHeads rest none
  | some a :: rest, previous =>
      if previous = some a then columnRunHeads rest (some a)
      else a :: columnRunHeads rest (some a)

def markedColumn (label : α → CanonicalColumnLabel) (entries : List (α × Bool)) :
    List (Option CanonicalColumnLabel) :=
  entries.map (fun a => if a.2 then some (label a.1) else none)

def imperfectColumnReferences (reference : α → ℕ) (entries : List (α × Bool)) : List ℕ :=
  entries.filterMap (fun a => if a.2 then none else some (reference a.1))

def resolveColumnReference (full : List (Option CanonicalColumnLabel)) (j : ℕ) :
    CanonicalColumnLabel := (full[j]?.join).getD (.freshImperfect j)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α] {N : ℕ}

def perfectColumnName : ℕ ⊕ ℕ → CanonicalColumnLabel
  | .inl a => .regular a
  | .inr a => .omitted a

def canonicalColumnName (label : Fin N → α) (perfect : Finset (Fin N))
    (name : Fin N → ℕ ⊕ ℕ) (i : Fin N) : CanonicalColumnLabel :=
  let j := columnRepresentative label perfect i
  if j ∈ perfect then perfectColumnName (name j) else .freshImperfect j.val

noncomputable def canonicalPerfectEntries (label : Fin N → α) (perfect : Finset (Fin N))
    (name : Fin N → ℕ ⊕ ℕ) : List (Option CanonicalColumnLabel) :=
  List.ofFn (fun i => if i ∈ perfect then some (canonicalColumnName label perfect name i) else none)

def columnPositionEntries (perfect : Finset (Fin N)) : List (Fin N × Bool) :=
  List.ofFn (fun i => (i, decide (i ∈ perfect)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α] {n : ℕ}

def forestPerfectName (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (i : Fin n) : ℕ ⊕ ℕ :=
  if hi : label i ∈ regular then .inl (number ⟨label i, hi⟩)
  else .inr (columnRepresentative label perfect i).val

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α] {n : ℕ}

noncomputable def observedColumnName (label : Fin n → α) (perfect : Finset (Fin n))
    (name : Fin n → ℕ ⊕ ℕ) (a : α) : CanonicalColumnLabel := by
  classical
  exact if h : ∃ i, label i = a then canonicalColumnName label perfect name h.choose
    else .freshImperfect 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

def columnFlagsWithCuts : List (Option α × Bool) → Option α → List (Bool × Bool)
  | [], _ => []
  | (none, _) :: rest, _ => (true, false) :: columnFlagsWithCuts rest none
  | (some a, cut) :: rest, previous =>
      (false, cut || decide (previous ≠ some a)) :: columnFlagsWithCuts rest (some a)

def columnRunHeadsWithCuts : List (Option α × Bool) → Option α → List α
  | [], _ => []
  | (none, _) :: rest, _ => columnRunHeadsWithCuts rest none
  | (some a, cut) :: rest, previous =>
      if cut = false ∧ previous = some a then columnRunHeadsWithCuts rest (some a)
      else a :: columnRunHeadsWithCuts rest (some a)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

def columnFinalState : List (Option α × Bool) → Option α → Option α
  | [], previous => previous
  | (a, _) :: rest, _ => columnFinalState rest a

def perfectBlockCuts : List α → List (Option α × Bool)
  | [] => []
  | a :: rest => (some a, true) :: rest.map (fun b => (some b, false))

def columnChunkCuts (chunks : List (List α ⊕ α)) : List (Option α × Bool) :=
  chunks.flatMap (Sum.elim perfectBlockCuts (fun _ => [(none, false)]))

def columnChunkEntries (chunks : List (List α ⊕ α)) : List (α × Bool) :=
  chunks.flatMap (Sum.elim (fun l => l.map (fun a => (a, true))) (fun a => [(a, false)]))

def columnChunkRuns (chunks : List (List α ⊕ α)) : List α :=
  chunks.flatMap (Sum.elim (fun l => columnRunHeads (l.map some) none) (fun _ => []))

def columnChunkPieces (omitted : α → Bool) (chunks : List (List α ⊕ α)) :
    List (List α ⊕ α) :=
  chunks.flatMap (Sum.elim
    (fun l => partitionColumnRuns omitted (columnRunHeads (l.map some) none)) (fun _ => []))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α]

def perfectChunkCount (chunks : List (List α ⊕ α)) : ℕ :=
  (chunks.filterMap (Sum.elim some (fun _ => none))).length

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

variable {α : Type*}

def shortBlockLengths (n s : ℕ) : List ℕ := List.replicate (n / s) s ++ [n % s]

def shortBlocks (s : ℕ) (l : List α) : List (List α) :=
  (shortBlockLengths l.length s).splitLengths l

def subdivideColumnChunks (s : ℕ) (chunks : List (List α ⊕ α)) : List (List α ⊕ α) :=
  chunks.flatMap (Sum.elim (fun l => (shortBlocks s l).map Sum.inl) (fun a => [Sum.inr a]))

def perfectChunkLength (chunks : List (List α ⊕ α)) : ℕ :=
  (chunks.map (Sum.elim List.length (fun _ => 0))).sum

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

variable {α β : Type*}

def initialColumnChunks (entries : List (α × Bool)) : List (List α ⊕ α) :=
  (partitionColumnRuns (fun a => !a.2) entries).map (Sum.map (List.map Prod.fst) Prod.fst)

def shortPerfectColumnChunks (s : ℕ) (entries : List (α × Bool)) : List (List α ⊕ α) :=
  subdivideColumnChunks s (initialColumnChunks entries)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

def columnPieceMask (pieces : List (List CanonicalColumnLabel ⊕ CanonicalColumnLabel)) :
    List Bool := pieces.map (Sum.elim (fun _ => true) (fun _ => false))

def columnPieceRegular (pieces : List (List CanonicalColumnLabel ⊕ CanonicalColumnLabel)) :
    List (List CanonicalColumnLabel) :=
  pieces.filterMap (Sum.elim some (fun _ => none))

def columnPieceOmitted (pieces : List (List CanonicalColumnLabel ⊕ CanonicalColumnLabel)) :
    List CanonicalColumnLabel :=
  pieces.filterMap (Sum.elim (fun _ => none) some)

def columnPieceFlatten (pieces : List (List CanonicalColumnLabel ⊕ CanonicalColumnLabel)) :
    List CanonicalColumnLabel :=
  pieces.flatMap (Sum.elim id List.singleton)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {N segments : ℕ}

noncomputable def forestPathDataOfRepresentation
    (G : SimpleGraph V) (hG : G.IsAcyclic) (hN : Fintype.card V ≤ N)
    (t : BinaryTree V) (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (ha : ∀ a b, forestAdjacent t a b ↔ G.Adj a b) (color : V → Bool)
    (start finish : Fin segments → V) (p : ∀ i, G.Walk (start i) (finish i))
    (hp : ∀ i, List.IsChain (· ≠ ·) (p i).edges) : ForestPathData N segments := by
  let e := Fintype.equivFin V
  let H := G.comap e.symm
  have hH : H.IsAcyclic := hG.of_comap e.symm.toEmbedding
  let f : G →g H := ⟨e, by
    intro a b hab
    change G.Adj (e.symm (e a)) (e.symm (e b))
    simpa only [Equiv.symm_apply_apply] using hab⟩
  refine {
    vertices := Fintype.card V
    vertex_bound := hN
    graph := H
    acyclic := hH
    tree := t.map e
    nodup := by rw [forestNodes_map]; exact ht.map e.injective
    cover := ?_
    adjacent := ?_
    color := color ∘ e.symm
    start := e ∘ start
    finish := e ∘ finish
    walk := fun i => (p i).map f
    reduced := ?_ }
  · intro v
    rw [forestNodes_map]
    exact List.mem_map.mpr ⟨e.symm v, hc _, e.apply_symm_apply v⟩
  · intro a b
    have h := forestAdjacent_map e e.injective t (e.symm a) (e.symm b)
    change _ ↔ G.Adj (e.symm a) (e.symm b)
    simpa only [Equiv.apply_symm_apply] using h.trans (ha _ _)
  · intro i
    apply (hH.isPath_iff_isChain _).mp
    exact ((hG.isPath_iff_isChain _).mpr (hp i)).map e.injective

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {segments N : ℕ}
  (start finish : Fin segments → V) (p : ∀ i, G.Walk (start i) (finish i))

def walkFamilySupport : Finset V :=
  univ.biUnion (fun i => (p i).support.toFinset)

lemma mem_walkFamilySupport (i : Fin segments) (v : V) (hv : v ∈ (p i).support) :
    v ∈ walkFamilySupport start finish p :=
  mem_biUnion.mpr ⟨i, mem_univ _, List.mem_toFinset.mpr hv⟩

abbrev walkFamilyGraph := G.induce (walkFamilySupport start finish p : Set V)

def walkFamilyStart (i : Fin segments) : (walkFamilySupport start finish p) :=
  ⟨start i, mem_walkFamilySupport start finish p i _ (p i).start_mem_support⟩

def walkFamilyFinish (i : Fin segments) : (walkFamilySupport start finish p) :=
  ⟨finish i, mem_walkFamilySupport start finish p i _ (p i).end_mem_support⟩

def restrictedFamilyWalk (i : Fin segments) :
    (walkFamilyGraph start finish p).Walk
      (walkFamilyStart start finish p i) (walkFamilyFinish start finish p i) :=
  (p i).induce _ (mem_walkFamilySupport start finish p i)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.SimpleGraph

variable {K α ι : Type*} [Field K] [Fintype α]

def QuotientRunData (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α)
    (label : ℕ → α) (coefficient : ℕ → K) (a : ℕ) (i : ι) :
    List (ℕ × ι) → Prop
  | [] => True
  | (b, j) :: rest =>
      a ≤ b ∧ (∀ t ∈ Ico a b, label t = regularLabel i) ∧
      (∑ t ∈ Ico a b, coefficient t) ≠ 0 ∧ i ≠ j ∧
      (∃ c : K, D.mkQ (formalDeparture label coefficient b) = anchor j +
        c • D.mkQ (Pi.basisFun K α (regularLabel j))) ∧
      QuotientRunData D anchor regularLabel label coefficient b j rest

noncomputable def quotientRunSteps (D : Submodule K (α → K)) (label : ℕ → α)
    (coefficient : ℕ → K) (steps : List (ℕ × ι)) : List (((α → K) ⧸ D) × ι) :=
  steps.map (fun p => (D.mkQ (formalDeparture label coefficient p.1), p.2))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {K α ι : Type*} [Field K] [Fintype α] [DecidableEq ι]

def scanRunTransitions (runLabel : ℕ → ι) : ℕ → ℕ → ι → List (ℕ × ι)
  | _, 0, _ => []
  | n, len + 1, previous =>
      if runLabel n = previous then scanRunTransitions runLabel (n + 1) len previous
      else (n, runLabel n) :: scanRunTransitions runLabel (n + 1) len (runLabel n)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α]

def IndexedRunStep (label : ℕ → α) (a b : ℕ × α) : Prop :=
  a.1 < b.1 ∧ label a.1 = a.2 ∧ label b.1 = b.2 ∧ a.2 ≠ b.2 ∧
    ∀ t ∈ Ico a.1 b.1, label t = a.2

def indexedBlockRuns (label : ℕ → α) (start len : ℕ) : List (ℕ × α) :=
  match len with
  | 0 => []
  | len + 1 => (start, label start) :: scanRunTransitions label (start + 1) len (label start)

def blockLabelList (label : ℕ → α) (start len : ℕ) : List α :=
  (List.range len).map (fun j => label (start + j))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

def intervalPositions (b : ℕ × ℕ) : List ℕ :=
  (List.range b.2).map (fun j => b.1 + j)

variable {α : Type*}

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

variable {α : Type*} {n : ℕ}

def columnNatLabel (label : Fin n → α) (hn : 0 < n) (t : ℕ) : α :=
  if ht : t < n then label ⟨t, ht⟩ else label ⟨0, hn⟩

def columnNatPerfect (perfect : Finset (Fin n)) (t : ℕ) : Bool :=
  if ht : t < n then decide ((⟨t, ht⟩ : Fin n) ∈ perfect) else false

def shortColumnChunks (label : Fin n → α) (hn : 0 < n) (perfect : Finset (Fin n)) (s : ℕ) :
    List (List α ⊕ α) :=
  (shortPerfectColumnChunks s ((List.range n).map (fun t => (t, columnNatPerfect perfect t)))).map
    (Sum.map (List.map (columnNatLabel label hn)) (columnNatLabel label hn))

end TwoPointCorrelations

end OAI

end

section

namespace Erdos970

def ballDR (R : ℝ) : Set ℂ := Metric.ball (0 : ℂ) R

lemma lem_ballDR (R : ℝ) (hR : R > 0) : closure (ballDR R) = Metric.closedBall (0 : ℂ) R := by
  unfold ballDR
  exact closure_ball 0 (ne_of_gt hR)

lemma lem_DRcompact (R : ℝ) (hR : R > 0) : IsCompact (closure (ballDR R)) := by
  rw [lem_ballDR R hR]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact Metric.isClosed_closedBall
  · exact Metric.isBounded_closedBall

noncomputable def f_M (R M : ℝ) (_hR : R > 0) (_hM : M > 0)
    (f : ℂ → ℂ)
    (_h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (_h_zero : f 0 = 0)
    (_h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
ℂ → ℂ := fun z ↦ (if z = 0 then (fderiv ℂ f 0) 1 else f z / z) / (2 * M - f z)

abbrev I := Complex.I

open _root_.Complex _root_.MeasureTheory _root_.intervalIntegral
open scoped _root_.Interval

noncomputable def If_taxicab
    {r1 R R0: ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (_hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
    (Metric.closedBall (0 : ℂ) r1) → ℂ :=
  fun z =>
    (∫ t in (0 : ℝ)..z.1.re, f (t : ℂ))
    + Complex.I * (∫ τ in (0 : ℝ)..z.1.im, f ((z.1.re : ℂ) + Complex.I * τ))

noncomputable def Err
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (_hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (z h : ℂ) : ℂ :=
  (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
  + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))

noncomputable def S_horiz (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ t ∈ Set.uIcc z.re (z + h).re,
        r = ‖f (t + Complex.I * z.im) - f z‖}

noncomputable def S_vert (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ τ ∈ Set.uIcc z.im (z + h).im,
        r = ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖}

noncomputable def S_max (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  max (S_horiz z h f) (S_vert z h f)

open _root_.Filter _root_.Topology

open _root_.Classical
                                                                                      
noncomputable def If_ext
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) : ℂ → ℂ :=
  fun w =>
    if h : w ∈ Metric.closedBall (0 : ℂ) r1 then
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, h⟩
    else
      0

open scoped _root_.Topology

noncomputable def H_auxiliary
    {r1 R' R : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R' : r1 < R') (_hR'_lt_R : R' < R) (_hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (_hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (_hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    (J : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp (J z) / B z

end Erdos970

end

section

namespace Erdos970

open _root_.Complex _root_.BigOperators _root_.Nat _root_.Classical _root_.Real _root_.Topology _root_.Filter
open _root_.Set _root_.MeasureTheory _root_.intervalIntegral _root_.Asymptotics

open scoped _root_.Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)

noncomputable def HIntegral' (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    (1 / (2 * π * I)) • HIntegral f x₁ x₂ y

noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w

noncomputable def VerticalIntegral (f : ℂ → E) (σ : ℝ) : E :=
    I • ∫ t : ℝ, f (σ + t * I)

noncomputable abbrev VerticalIntegral' (f : ℂ → E) (σ : ℝ) : E :=
    (1 / (2 * π * I)) • VerticalIntegral f σ

abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s

def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

end Erdos970

end

section

namespace Erdos970

lemma DRinD1 (R : ℝ) (_hR : 0 < R) (hR' : R < 1) :
    Metric.closedBall (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) 1 := by
  exact Metric.closedBall_subset_ball hR'
def zerosetKfR (R : ℝ) (_hR : 0 < R) (f : ℂ → ℂ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ f ρ = 0}
lemma lemKinDR (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) :
    zerosetKfR R hR f ⊆ Metric.closedBall (0 : ℂ) R := by
  intro ρ hρ

  rw [zerosetKfR] at hρ
                                                                     
  exact hρ.1
lemma lemKRinK1 (R : ℝ) (hR : 0 < R) (hR' : R < 1) (f : ℂ → ℂ) :
    zerosetKfR R hR f ⊆ {ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0} := by
  intro ρ hρ
  simp only [zerosetKfR, Set.mem_ofPred_eq] at hρ ⊢
  constructor
  · exact DRinD1 R hR hR' hρ.1
  · exact hρ.2

lemma lem_bolzano_weierstrass {D : Set ℂ} (hD : IsCompact D) {Z : Set ℂ} (hZ_inf : Z.Infinite) (hZ_sub_D : Z ⊆ D) :
    ∃ ρ₀ ∈ D, AccPt ρ₀ (Filter.principal Z) :=
  Set.Infinite.exists_accPt_of_subset_isCompact hZ_inf hD hZ_sub_D
lemma lem_zeros_have_limit_point (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (h_Kf_inf : Set.Infinite (zerosetKfR R hR f)) :
    ∃ ρ₀ ∈ Metric.closedBall (0 : ℂ) R, AccPt ρ₀ (Filter.principal (zerosetKfR R hR f)) := by
  apply lem_bolzano_weierstrass
  ·                                                
    rw [← lem_ballDR R hR]
    exact lem_DRcompact R hR
  · exact h_Kf_inf
  · exact lemKinDR R hR f

open _root_.Filter _root_.Metric _root_.Set _root_.Bornology _root_.Function

lemma lem_identity_theorem (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (ρ₀ : ℂ) (hρ₀_in_D1 : ρ₀ ∈ Metric.ball (0 : ℂ) 1)
    (h_acc : AccPt ρ₀ (Filter.principal ({ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0}))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
                                                 
  have h_subset : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall
                                                        
  have hf_open : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := AnalyticOnNhd.mono hf h_subset
                                                         
  have h_conn : IsConnected (Metric.ball (0 : ℂ) 1) := Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1)
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) := h_conn.isPreconnected
                                                     
  have h_zeros_subset : {ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0} ⊆ {z | f z = 0} := by
    intro z hz
    exact hz.2
                                                                                           
  have h_acc_zero : AccPt ρ₀ (Filter.principal ({z | f z = 0})) := by
    exact AccPt.mono h_acc (principal_mono.2 h_zeros_subset)
                                                                                                  
  have h_closure : ρ₀ ∈ closure ({z | f z = 0} \ {ρ₀}) := by
                                                                                
    have h_cluster : ClusterPt ρ₀ (Filter.principal ({z | f z = 0} \ {ρ₀})) :=
      (accPt_principal_iff_clusterPt).mp h_acc_zero
    exact (mem_closure_iff_clusterPt).2 h_cluster
                               
  exact AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hf_open h_preconn hρ₀_in_D1 h_closure
lemma lem_identity_theoremR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (ρ₀ : ℂ) (hρ₀_in_DR : ρ₀ ∈ Metric.closedBall (0 : ℂ) R)
    (h_acc : AccPt ρ₀ (Filter.principal ({ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0}))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  have hρ₀_in_D1 : ρ₀ ∈ Metric.ball (0 : ℂ) 1 := DRinD1 R hR hR' hρ₀_in_DR
  exact lem_identity_theorem f hf ρ₀ hρ₀_in_D1 h_acc
lemma lem_identity_theoremKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_exists_rho0 : ∃ ρ₀ ∈ Metric.closedBall (0 : ℂ) R, AccPt ρ₀ (Filter.principal (zerosetKfR R hR f))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
                                
  obtain ⟨ρ₀, hρ₀_in_R, h_acc⟩ := h_exists_rho0
                                
  apply lem_identity_theoremR R hR hR' f hf ρ₀ hρ₀_in_R
                                                                    
  exact AccPt.mono h_acc (principal_mono.2 (lemKRinK1 R hR hR' f))
lemma lem_identity_infiniteKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_Kf_inf : Set.Infinite (zerosetKfR R hR f)) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  have h_exists_rho0 := lem_zeros_have_limit_point R hR f h_Kf_inf
  exact lem_identity_theoremKR R hR hR' f hf h_exists_rho0
lemma lem_Contra_finiteKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_exists_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0) :
    Set.Finite (zerosetKfR R hR f) := by
                                                  
  by_contra h_not_finite

  have h_Kf_inf : Set.Infinite (zerosetKfR R hR f) := h_not_finite
                                  
  have h_eq_zero := lem_identity_infiniteKR R hR hR' f hf h_Kf_inf

  obtain ⟨z, hz_in_ball, hz_nonzero⟩ := h_exists_nonzero
  have h_f_z_zero : f z = 0 := h_eq_zero hz_in_ball
  exact hz_nonzero h_f_z_zero

open _root_.Classical

noncomputable def Cf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (_hR1_lt_R : R1 < R)
    (_hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))                                                        
    (z : ℂ) : ℂ :=
  if hz : z ∈ zerosetKfR R1 (by linarith) f then
    h_σ z z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase z), (z - ρ) ^ (analyticOrderAt f ρ).toNat
  else
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat

noncomputable def Bf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (z : ℂ) : ℂ :=
  Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z *
  ∏ ρ ∈ h_finite_zeros.toFinset,
    ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat

variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)
variable (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
variable (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)

end Erdos970

end

section

namespace Erdos970

open scoped _root_.BigOperators _root_.Topology
abbrev ℙ := Nat.Primes

local notation "ι" => fun (z : ℂˣ) ↦ (z : ℂ)

open _root_.Real _root_.Set _root_.Filter _root_.Topology _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Topology

noncomputable def zetaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-s)

open _root_.Metric _root_.Set _root_.Filter _root_.Asymptotics _root_.BigOperators

noncomputable def logDerivZeta (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s

def zerosetKfRc (R : ℝ) (c : ℂ) (f : ℂ → ℂ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ Metric.closedBall c R ∧ f ρ = 0}

end Erdos970

end

section

namespace Erdos970

namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics

end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology

end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

attribute [fun_prop] measurable_from_top

section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg

noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

end LogZetaInteg
end

section
open _root_.MeasureTheory _root_.Set

end

noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

noncomputable def E₃ (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, log (1 - (1:ℝ) / p) + log (log x) + eulerMascheroniConstant

noncomputable abbrev M_eq_summand (p : ℕ) := if p.Prime then log (1 - 1 / p) + 1 / p else 0

end Mertens

end Erdos970

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

inductive AC0Circuit (n : ℕ) where
  | literal (i : Fin n) (positive : Bool)
  | andGate {k : ℕ} (children : Fin k → AC0Circuit n)
  | orGate {k : ℕ} (children : Fin k → AC0Circuit n)

namespace AC0Circuit

def eval {n : ℕ} : AC0Circuit n → BooleanCube n → Bool
  | .literal i positive, x => if positive then x i else !(x i)
  | .andGate children, x => decide (∀ i, eval (children i) x = true)
  | .orGate children, x => decide (∃ i, eval (children i) x = true)

def depth {n : ℕ} : AC0Circuit n → ℕ
  | .literal _ _ => 0
  | .andGate children => 1 + Finset.univ.sup (fun i => depth (children i))
  | .orGate children => 1 + Finset.univ.sup (fun i => depth (children i))

def size {n : ℕ} : AC0Circuit n → ℕ
  | .literal _ _ => 1
  | .andGate children => 1 + ∑ i, size (children i)
  | .orGate children => 1 + ∑ i, size (children i)

noncomputable def indicator {n : ℕ} (c : AC0Circuit n) (x : BooleanCube n) : ℝ :=
  if c.eval x then 1 else 0

end AC0Circuit

def BravermanDepth22Input : Prop :=
  ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ (n : ℕ) (c : AC0Circuit n), c.depth ≤ 22 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
      (K : ℝ) * (Real.log ((c.size : ℝ) / ε)) ^ C ≤ (t : ℝ) →
      ∀ g : BooleanCube n → ℝ, (∀ x, 0 ≤ g x) → cubeAverage g = 1 →
        TWiseUniformDensity g t →
        |cubeAverage (fun x => g x * c.indicator x) - cubeAverage c.indicator| ≤ ε

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

def flattenBitBlocks (m B : ℕ) : (Fin m → BooleanCube B) ≃ BooleanCube (m * B) :=
  (Equiv.curry (Fin m) (Fin B) Bool).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool))

def bitSources {m B : ℕ} (S : Finset (Fin (m * B))) : Finset (Fin m) :=
  S.image (fun k => k.divNat)

def extendBitBlocks {m B : ℕ} (C : Finset (Fin m)) (z : C → BooleanCube B) : Fin m → BooleanCube B :=
  fun i => if h : i ∈ C then z ⟨i, h⟩ else fun _ => false

noncomputable def selectedWalsh {m B : ℕ} (S : Finset (Fin (m * B)))
    (z : bitSources S → BooleanCube B) : ℝ :=
  walsh S (flattenBitBlocks m B (extendBitBlocks (bitSources S) z))

noncomputable def integerBitSample {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (B a : ℕ) {N : ℕ} (x : Fin N × (Fin m → Fin (2 ^ B))) : BooleanCube (m * B) :=
  flattenBitBlocks m B (crtJitterBits s B (fun i => (a + x.1.val : ZMod (s i))) x.2)

noncomputable def integerBitDensity {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (B a N : ℕ) : BooleanCube (m * B) → ℝ :=
  sampleDensity (@integerBitSample m s _ B a N)

noncomputable def selectedWalshMean {m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (S : Finset (Fin (m * B)))
    (r : ∀ i : bitSources S, ZMod (s i)) : ℝ :=
  uniformAverage (fun j : bitSources S → Fin (2 ^ B) =>
    selectedWalsh S (crtJitterBits (fun i : bitSources S => s i) B r j))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations.AC0Circuit

open _root_.Finset

def substitute {n m : ℕ} (σ : Fin n → Bool → AC0Circuit m) : AC0Circuit n → AC0Circuit m
  | .literal i positive => σ i positive
  | .andGate children => .andGate (fun i => substitute σ (children i))
  | .orGate children => .orGate (fun i => substitute σ (children i))

def assignmentTerm {n B : ℕ} (v : Fin B → Fin n) (z : BooleanCube B) : AC0Circuit n :=
  .andGate (fun i => .literal (v i) (z i))

def falseCircuit (n : ℕ) : AC0Circuit n := .orGate (fun i : Fin 0 => Fin.elim0 i)

@[simp] lemma falseCircuit_eval (n : ℕ) (x : BooleanCube n) :
    (falseCircuit n).eval x = false := by simp [falseCircuit, eval]

noncomputable def truthTable {n B : ℕ} (v : Fin B → Fin n)
    (F : BooleanCube B → Bool) : AC0Circuit n :=
  .orGate (fun k : Fin (2 ^ B) =>
    if F (binaryCellEquiv B k) then assignmentTerm v (binaryCellEquiv B k)
    else falseCircuit n)

noncomputable def encodeInputs {n m B : ℕ} (v : Fin n → Fin B → Fin m)
    (F : Fin n → BooleanCube B → Bool) (c : AC0Circuit n) : AC0Circuit m :=
  substitute (fun i positive => truthTable (v i)
    (fun z => if positive then F i z else !(F i z))) c

end TwoPointCorrelations.AC0Circuit

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def decodedResidues {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (B : ℕ) (x : Fin m → BooleanCube B) : ∀ i, ZMod (s i) :=
  fun i => ZMod.finEquiv (s i) (decodeBits (NeZero.pos (s i)) (x i))

noncomputable def eventIndicator {α : Type*} (E : α → Bool) (x : α) : ℝ := if E x then 1 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

def residueCircuitInputs {n m : ℕ} (s : Fin m → ℕ) (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (r : ∀ j, ZMod (s j)) : BooleanCube n :=
  fun i => test i (r (coord i))

def residueCircuitEvent {n m : ℕ} (s : Fin m → ℕ) (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n)
    (r : ∀ j, ZMod (s j)) : Bool := c.eval (residueCircuitInputs s coord test r)

noncomputable def encodeResidueCircuit {n m : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (B : ℕ) (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n) : AC0Circuit (m * B) :=
  AC0Circuit.encodeInputs (fun i j => finProdFinEquiv (coord i, j))
    (fun i z => test i (ZMod.finEquiv (s (coord i))
      (decodeBits (NeZero.pos (s (coord i))) z))) c

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def primeResidueModuli (P : Finset ℕ) : Fin (Fintype.card P) → ℕ :=
  fun i => ((Fintype.equivFin P).symm i).val

noncomputable def primeLiteralCoordinate (P : Finset ℕ) {n : ℕ}
    (literal : Fin n → P × ℤ) : Fin n → Fin (Fintype.card P) :=
  fun i => (Fintype.equivFin P) (literal i).1

noncomputable def primeLiteralTest (P : Finset ℕ) {n : ℕ}
    (literal : Fin n → P × ℤ) (i : Fin n)
    (z : ZMod (primeResidueModuli P (primeLiteralCoordinate P literal i))) : Bool :=
  decide (z = -((literal i).2 : ZMod (primeResidueModuli P (primeLiteralCoordinate P literal i))))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def activeState {n : ℕ} (x : BooleanCube n) : Finset (Fin n) :=
  univ.filter (fun i => x i = true)

def boundedActiveStates (n M : ℕ) : Finset (Finset (Fin n)) :=
  univ.powerset.filter (fun S => S.card ≤ M)

def activeStateCircuit {n : ℕ} (S : Finset (Fin n)) : AC0Circuit n :=
  .andGate (fun i : Fin n => .literal i (decide (i ∈ S)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def activeStateVectorCircuit {R n m : ℕ} (index : Fin R → Fin n → Fin m)
    (S : Fin R → Finset (Fin n)) : AC0Circuit m :=
  .andGate (fun r => .andGate (fun i => .literal (index r i) (decide (i ∈ S r))))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {n : ℕ}

def cubeRestrict (S : Finset (Fin n)) (x : BooleanCube n) : S → Bool := fun i => x i

noncomputable def cubeExtend (S : Finset (Fin n)) (z : S → Bool) : BooleanCube n :=
  fun i => if hi : i ∈ S then z ⟨i, hi⟩ else false

def WalshDegreeLE (F : BooleanCube n → ℝ) (t : ℕ) : Prop :=
  ∃ a : Finset (Fin n) → ℝ, ∀ x,
    F x = ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ t),
      a S * walsh S x

end TwoPointCorrelations

end OAI

end

section

namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

section lemmas

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [one_add_one_eq_two, Circle.norm_coe])⟩

end lemmas

end Erdos970

end

section

namespace Erdos970

open _root_.Complex _root_.Topology _root_.Filter _root_.Interval _root_.Set _root_.Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))

open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
                                                              

end Erdos970

end

section

namespace Erdos970

def zeroZ : Set ℂ := {s : ℂ | riemannZeta s = 0}

def ZetaZerosNearPoint (t : ℝ) : Set ℂ := { ρ : ℂ | ρ ∈ zeroZ ∧ ‖ρ - ((3/2 : ℂ) + t * Complex.I)‖ ≤ (5/6 : ℝ) }

open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

end Erdos970

end

section

namespace Erdos970

open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)

noncomputable abbrev MellinTransform : (ℝ → ℂ) → ℂ → ℂ := mellin

noncomputable def MellinInverseTransform (F : ℂ → ℂ) (σ : ℝ) (x : ℝ) : ℂ :=
  VerticalIntegral' (fun s ↦ x ^ (-s) * F s) σ

local notation (name := mellintransform2) "𝓜" => MellinTransform

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "I" => Complex.I

noncomputable def ChebyshevPsi (x : ℝ) : ℝ :=
  (Finset.range ⌊x + 1⌋₊).sum Λ

local notation "ψ" => ChebyshevPsi

noncomputable abbrev SmoothedChebyshevIntegrand (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    𝓜 ((Smooth1 SmoothingF ε) ·) s * (X : ℂ) ^ s

noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)

open _root_.ComplexConjugate

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

@[inline] noncomputable def sigma1Of (A T : ℝ) : ℝ := 1 - A / Real.log T

noncomputable def I₁ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₂ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)))

noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₈ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + T * I)))

noncomputable def I₉ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₃ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₄ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)))

noncomputable def I₆ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + 3 * I)))

noncomputable def I₅ (SmoothingF : ℝ → ℝ) (ε X σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-3)..3,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)))

def LogDerivZetaHasBound (A C : ℝ) : Prop := ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t|)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
    C * Real.log |t| ^ 9

def LogDerivZetaIsHoloSmall (σ₂ : ℝ) : Prop :=
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (((uIcc σ₂ 2)  ×ℂ (uIcc (-3) 3)) \ {1})

open _root_.Filter _root_.Topology

end Erdos970

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.symmDiff

variable {n : ℕ}

lemma WalshDegreeLE.of_walsh (S : Finset (Fin n)) {t : ℕ} (hS : S.card ≤ t) :
    WalshDegreeLE (walsh S) t := by
  refine ⟨fun T => if T = S then 1 else 0, ?_⟩
  intro x
  simp [hS]

lemma WalshDegreeLE.const (c : ℝ) (t : ℕ) :
    WalshDegreeLE (fun _ : BooleanCube n => c) t := by
  refine ⟨fun S => if S = ∅ then c else 0, ?_⟩
  intro x
  simp

lemma WalshDegreeLE.smul {F : BooleanCube n → ℝ} {t : ℕ}
    (hF : WalshDegreeLE F t) (c : ℝ) : WalshDegreeLE (fun x => c * F x) t := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨fun S => c * a S, ?_⟩
  intro x
  dsimp only
  rw [ha, mul_sum]
  apply sum_congr rfl
  intro S _
  ring

lemma WalshDegreeLE.sub {F G : BooleanCube n → ℝ} {t : ℕ}
    (hF : WalshDegreeLE F t) (hG : WalshDegreeLE G t) :
    WalshDegreeLE (fun x => F x - G x) t := by
  obtain ⟨a, ha⟩ := hF
  obtain ⟨b, hb⟩ := hG
  refine ⟨fun S => a S - b S, ?_⟩
  intro x
  dsimp only
  rw [ha, hb, ← sum_sub_distrib]
  apply sum_congr rfl
  intro S _
  ring

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

variable {n : ℕ}

noncomputable def semiExactMinorant (P : BooleanCube n → ℝ) (x : BooleanCube n) : ℝ :=
  1 - (1 - P x) ^ 2

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

noncomputable def exceptionalExtension {n : ℕ} (F : BooleanCube n → ℝ)
    (E : BooleanCube n → Bool) (x : BooleanCube n) : ℝ :=
  if E x then 1 else F x

noncomputable def errorCutoffPolynomial {n : ℕ} (P T : BooleanCube n → ℝ)
    (x : BooleanCube n) : ℝ := P x * (1 - T x)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def walshTruncation {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ)
    (x : BooleanCube n) : ℝ :=
  ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ t),
    walshCoefficient f S * walsh S x

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def restrictCube {n : ℕ} (L : Finset (Fin n))
    (y x : BooleanCube n) : BooleanCube n := fun i => if i ∈ L then x i else y i

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

abbrev PartialAssignment (n : ℕ) := Fin n → Option Bool

namespace PartialAssignment

def apply {n : ℕ} (ρ : PartialAssignment n) (x : BooleanCube n) : BooleanCube n :=
  fun i => (ρ i).getD (x i)

def Extends {n : ℕ} (ρ τ : PartialAssignment n) : Prop :=
  ∀ i b, ρ i = some b → τ i = some b

def assign {n : ℕ} (ρ : PartialAssignment n) (S : Finset (Fin n))
    (x : BooleanCube n) : PartialAssignment n := fun i => if i ∈ S then some (x i) else ρ i

def free {n : ℕ} (ρ : PartialAssignment n) : Finset (Fin n) :=
  univ.filter (fun i => ρ i = none)

end PartialAssignment

structure CubeTerm (n : ℕ) where
  support : Finset (Fin n)
  value : BooleanCube n

namespace CubeTerm

def eval {n : ℕ} (C : CubeTerm n) (x : BooleanCube n) : Bool :=
  decide (∀ i ∈ C.support, x i = C.value i)

def Compatible {n : ℕ} (C : CubeTerm n) (ρ : PartialAssignment n) : Prop :=
  ∀ i ∈ C.support, ρ i = none ∨ ρ i = some (C.value i)

def Satisfied {n : ℕ} (C : CubeTerm n) (ρ : PartialAssignment n) : Prop :=
  ∀ i ∈ C.support, ρ i = some (C.value i)

def live {n : ℕ} (C : CubeTerm n) (ρ : PartialAssignment n) : Finset (Fin n) :=
  C.support.filter (fun i => ρ i = none)

end CubeTerm

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

structure DNFQueryBlock (n : ℕ) where
  term : CubeTerm n
  queried : Finset (Fin n)
  answer : BooleanCube n

namespace DNFQueryBlock

def support {n : ℕ} : List (DNFQueryBlock n) → Finset (Fin n)
  | [] => ∅
  | b :: bs => b.queried ∪ support bs

def length {n : ℕ} : List (DNFQueryBlock n) → ℕ
  | [] => 0
  | b :: bs => b.queried.card + length bs

def image {n : ℕ} : PartialAssignment n → List (DNFQueryBlock n) → PartialAssignment n
  | ρ, [] => ρ
  | ρ, b :: bs => image (ρ.assign b.queried b.term.value) bs

end DNFQueryBlock

inductive CanonicalDNFWalk {n : ℕ} :
    List (CubeTerm n) → PartialAssignment n → List (DNFQueryBlock n) → Prop
  | nil (F ρ) : CanonicalDNFWalk F ρ []
  | skip {C F ρ bs} (hC : ¬ C.Compatible ρ) (h : CanonicalDNFWalk F ρ bs) :
      CanonicalDNFWalk (C :: F) ρ bs
  | step {C F ρ bs} (x : BooleanCube n) (hC : C.Compatible ρ)
      (hne : (C.live ρ).Nonempty) (h : CanonicalDNFWalk F (ρ.assign (C.live ρ) x) bs) :
      CanonicalDNFWalk (C :: F) ρ (⟨C, C.live ρ, x⟩ :: bs)

namespace CanonicalDNFWalk

end CanonicalDNFWalk

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def CubeTerm.slot {n : ℕ} (C : CubeTerm n) (i : Fin n) : ℕ :=
  if hi : i ∈ C.support then (C.support.equivFin ⟨i, hi⟩).val
  else C.support.card

namespace DNFQueryBlock

noncomputable def literalCode {n : ℕ} (b : DNFQueryBlock n) : List (ℕ × Bool) :=
  (b.queried.sort (· ≤ ·)).map (fun i => (b.term.slot i, b.answer i))

noncomputable def code {n : ℕ} (b : DNFQueryBlock n) : List (Option (ℕ × Bool)) :=
  b.literalCode.map some ++ [none]

noncomputable def codes {n : ℕ} (bs : List (DNFQueryBlock n)) : List (Option (ℕ × Bool)) :=
  bs.flatMap code

end DNFQueryBlock

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

abbrev BoundedRestrictionCode (w k : ℕ) :=
  Σ l : Fin (k + 1), Fin l.val → Option (Fin (w + 1) × Bool)

def readRestrictionCode {w k : ℕ} (c : BoundedRestrictionCode w k) :
    List (Option (ℕ × Bool)) :=
  List.ofFn (fun i => (c.2 i).map (fun z => (z.1.val, z.2)))

noncomputable def packRestrictionSymbol (w : ℕ) (z : Option (ℕ × Bool))
    (hz : ∀ a b, z = some (a, b) → a ≤ w) : Option (Fin (w + 1) × Bool) :=
  match z with
  | none => none
  | some (a, b) => some (⟨a, Nat.lt_succ_of_le (hz a b rfl)⟩, b)

noncomputable def packRestrictionCode (w k : ℕ) (l : List (Option (ℕ × Bool)))
    (hl : l.length ≤ k)
    (hw : ∀ z ∈ l, ∀ a b, z = some (a, b) → a ≤ w) : BoundedRestrictionCode w k :=
  ⟨⟨l.length, Nat.lt_succ_of_le hl⟩, fun i => packRestrictionSymbol w (l.get i)
    (hw (l.get i) (List.get_mem l i))⟩

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

structure FiniteLaw (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

noncomputable def average (μ : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

noncomputable def probability (μ : FiniteLaw α) (E : α → Prop) : ℝ := by
  classical
  exact μ.average (fun x => if E x then 1 else 0)

@[simp] lemma average_const (μ : FiniteLaw α) (c : ℝ) : μ.average (fun _ => c) = c := by
  simp [average, ← sum_mul, μ.total]

noncomputable def product (μ : FiniteLaw α) (ν : FiniteLaw β) : FiniteLaw (α × β) where
  weight x := μ.weight x.1 * ν.weight x.2
  nonneg x := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by simp [Fintype.sum_prod_type, ← mul_sum, μ.total, ν.total]

noncomputable def independent [DecidableEq ι] (μ : ι → FiniteLaw α) : FiniteLaw (ι → α) where
  weight x := ∏ i, (μ i).weight (x i)
  nonneg x := prod_nonneg (fun i _ => (μ i).nonneg _)
  total := by
    rw [← Fintype.prod_sum (fun i x => (μ i).weight x)]
    simp only [FiniteLaw.total, prod_const_one]

end FiniteLaw

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def avoidsEvents {ι α : Type*} (P : Finset ι) (E : ι → α → Prop) (x : α) : Prop :=
  ∀ i ∈ P, ¬E i x

def eventIntersection {ι α : Type*} (E : ι → α → Prop) (S : Finset ι) (x : α) : Prop :=
  ∀ i ∈ S, E i x

noncomputable def eventIntersectionCount {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (j : ℕ) (x : α) : ℝ :=
  ∑ S ∈ P.powersetCard j, if eventIntersection E S x then 1 else 0

noncomputable def truncatedEventCount {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) : ℝ :=
  ∑ j ∈ range (r + 1), (-1 : ℝ) ^ j * eventIntersectionCount P E j x

noncomputable def eventIntersectionMass {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (j : ℕ) : ℝ :=
  ∑ S ∈ P.powersetCard j, μ.probability (eventIntersection E S)

noncomputable def truncatedEventMass {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (r : ℕ) : ℝ :=
  ∑ j ∈ range (r + 1), (-1 : ℝ) ^ j * eventIntersectionMass μ P E j

noncomputable def sieveIntersectionError {ι : Type*}
    (P : Finset ι) (err : Finset ι → ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ range (r + 1), ∑ S ∈ P.powersetCard j, err S

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

abbrev CrudeWordCode (R N D : ℕ) :=
  (Fin R → Bool) × (Fin N → Fin N) × (Fin N → Fin D) × (Fin N → Bool)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]

def joinCoordinates (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A) : ι → A :=
  fun i => if h : i ∈ S then x ⟨i, h⟩ else y ⟨i, h⟩

namespace FiniteLaw

variable [Fintype A]

end FiniteLaw

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations.FiniteLaw

open _root_.Finset
open scoped _root_.Classical

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

noncomputable def dependentProduct (μ : FiniteLaw α) (ν : α → FiniteLaw β) :
    FiniteLaw (α × β) where
  weight x := μ.weight x.1 * (ν x.1).weight x.2
  nonneg x := mul_nonneg (μ.nonneg _) ((ν _).nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← mul_sum, total, mul_one]

end TwoPointCorrelations.FiniteLaw

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

section Paths

variable {V : Type*} [Fintype V] [DecidableEq V]

def matrixFrobeniusSq (A : Matrix V V ℝ) : ℝ := ∑ x, ∑ y, (A x y) ^ 2

end Paths

section Nonbacktracking

variable {D V : Type*} [DecidableEq D]

def blockNonbacktrackingMatrix (A : D → Matrix V V ℝ) : Matrix (D × V) (D × V) ℝ :=
  fun x y => if x.1 ≠ y.1 then A y.1 x.2 y.2 else 0

variable [DecidableEq V]

end Nonbacktracking

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

def forceCoordinates (S : Finset ι) (a x : ι → A) : ι → A := S.piecewise a x

noncomputable def mixedDifference (a : ι → A) (F : (ι → A) → ℝ) (x : ι → A) : ℝ :=
  ∑ S : Finset ι, (-1 : ℝ) ^ Sᶜ.card * F (forceCoordinates S a x)

namespace FiniteLaw

end FiniteLaw

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

noncomputable def selectedMixedDifference (S : Finset ι) (a : ι → A)
    (F : (ι → A) → ℝ) (x : ι → A) : ℝ :=
  mixedDifference (fun i : S => a i)
    (fun z : S → A => F (joinCoordinates S z (fun i : {i // i ∉ S} => x i)))
    (fun i : S => x i)

namespace FiniteLaw

end FiniteLaw

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def primeHarmonicMass (P : Finset ℕ) : ℝ :=
  ∑ p : P, (p.val : ℝ)⁻¹

noncomputable def primeReciprocalLaw (P : Finset ℕ) (hV : 0 < primeHarmonicMass P) : FiniteLaw P where
  weight p := (p.val : ℝ)⁻¹ / primeHarmonicMass P
  nonneg p := div_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hV.le
  total := by
    rw [← sum_div]
    exact div_self hV.ne'

variable {α : Type*} [Fintype α] [DecidableEq α]

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def crudePaddingWeight (q : ℕ) : ℝ := 4 ^ q.primeFactors.card

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def crudeTraceWeight (R S : ℕ) (q : Fin R → ℕ) (L external : ℝ) : ℝ :=
  external * 2 ^ S * ∏ i, L * crudePaddingWeight (q i)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

def litReciprocalExponent (lit unlit : ℕ) : ℕ :=
  unlit + if lit = 0 then 0 else 1

def extraReciprocalExponent (lit unlit : ℕ) : ℕ :=
  litReciprocalExponent lit unlit - 1

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]

def labelOccurrences (label : τ → ι) (i : ι) : Finset τ :=
  univ.filter (fun t => label t = i)

def litOccurrences (label : τ → ι) (lit : τ → Bool) (i : ι) : Finset τ :=
  (labelOccurrences label i).filter (fun t => lit t = true)

def unlitOccurrences (label : τ → ι) (lit : τ → Bool) (i : ι) : Finset τ :=
  (labelOccurrences label i).filter (fun t => lit t = false)

def singletonLabels (label : τ → ι) : Finset ι :=
  univ.filter (fun i => (labelOccurrences label i).card = 1)

def nonsingletonLabels (label : τ → ι) : Finset ι :=
  univ.filter (fun i => 2 ≤ (labelOccurrences label i).card)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {ι τ A : Type*} [DecidableEq ι] [DecidableEq A]

def LitConsistent (L : Finset τ) (label : τ → ι) (target : τ → A) : Prop :=
  ∀ t ∈ L, ∀ u ∈ L, label t = label u → target t = target u

noncomputable def litForcedTarget (L : Finset τ) (label : τ → ι) (target : τ → A)
    (base : ι → A) (i : ι) : A := by
  classical
  exact if hi : ∃ t ∈ L, label t = i then target (Classical.choose hi) else base i

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {τ P : Type*} [Fintype τ] [DecidableEq P]

def patternClasses (template : τ → P) : Finset P := univ.image template

def patternCoordinate (template : τ → P) (t : τ) : patternClasses template :=
  ⟨template t, mem_image.mpr ⟨t, mem_univ _, rfl⟩⟩

noncomputable def patternRepresentative (template : τ → P) (c : patternClasses template) : τ :=
  Classical.choose (mem_image.mp c.property)

noncomputable def patternEncode (template w : τ → P) (c : patternClasses template) : P :=
  w (patternRepresentative template c)

def patternResample (template : τ → P) (a : patternClasses template → P) (t : τ) : P :=
  a (patternCoordinate template t)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def uniformZModLaw (D : ℕ) [NeZero D] : FiniteLaw (ZMod D) where
  weight _ := 1 / D
  nonneg _ := by positivity
  total := by simp [ZMod.card, nsmul_eq_mul, NeZero.ne D]

noncomputable def intervalResidueLaw {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) : FiniteLaw (ZMod D) where
  weight := residueProbability A N
  nonneg _ := by unfold residueProbability; positivity
  total := residueProbability_sum A N hN

noncomputable def residueCubeLaw {D : ℕ} [NeZero D]
    (A : ZMod D × ZMod D × ZMod D) (N : ℕ) (hN : 0 < N) :
    FiniteLaw (ZMod D × ZMod D × ZMod D) :=
  (intervalResidueLaw A.1 N hN).product
    ((intervalResidueLaw A.2.1 N hN).product (intervalResidueLaw A.2.2 N hN))

noncomputable def uniformResidueCubeLaw (D : ℕ) [NeZero D] :
    FiniteLaw (ZMod D × ZMod D × ZMod D) :=
  (uniformZModLaw D).product ((uniformZModLaw D).product (uniformZModLaw D))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def zeroResidueIndicator {D : ℕ} [NeZero D] (x : ZMod D) : ℝ :=
  if x = 0 then 1 else 0

def fourFormBad {D : ℕ} [NeZero D] (x : ZMod D × ZMod D × ZMod D) : Prop :=
  x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0 ∨ x.1 + x.2.1 - x.2.2 = 0

noncomputable def fourFormBadDensity (D : ℕ) [NeZero D] : ℝ :=
  (uniformResidueCubeLaw D).probability fourFormBad

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {V E S : Type*} [Fintype V] [DecidableEq V] [Fintype E]

noncomputable def shiftMatrix (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) : Matrix V V ℝ := by
  classical
  exact fun i j => ∑ e, if next e (embed i) = embed j then weight e (embed i) else 0

noncomputable def retainedShiftWeight (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) (e : E) (x : S) : ℝ := by
  classical
  exact if next e x ∈ Set.range embed then weight e x else 0

def shiftWordEnd (next : E → S → S) : {k : ℕ} → S → (Fin k → E) → S
  | 0, x, _ => x
  | _k + 1, x, w => shiftWordEnd next (next (w 0) x) (Fin.tail w)

noncomputable def shiftWordWeight (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) : {k : ℕ} → S → (Fin k → E) → ℝ
  | 0, _, _ => 1
  | _k + 1, x, w => retainedShiftWeight embed next weight (w 0) x *
      shiftWordWeight embed next weight (next (w 0) x) (Fin.tail w)

noncomputable def shiftWordTerm (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) {k : ℕ} (x y : S) (w : Fin k → E) : ℝ := by
  classical
  exact if shiftWordEnd next x w = y then shiftWordWeight embed next weight x w else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {V E S Ω Ω' : Type*} [Fintype V] [DecidableEq V] [Fintype E]
  [Fintype Ω] [Fintype Ω']

noncomputable def shiftClosedWeight (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) (k : ℕ) (i : V) (u v : Fin k → E) : ℝ := by
  classical
  exact if shiftWordEnd next (embed i) u = shiftWordEnd next (embed i) v then
    shiftWordWeight embed next weight (embed i) u *
      shiftWordWeight embed next weight (embed i) v else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

noncomputable def dependentIndependent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i)) :
    FiniteLaw (∀ i, A i) where
  weight x := ∏ i, (μ i).weight (x i)
  nonneg x := prod_nonneg (fun i _ => (μ i).nonneg (x i))
  total := by
    rw [← Fintype.prod_sum (fun i x => (μ i).weight x)]
    simp only [FiniteLaw.total, prod_const_one]

end FiniteLaw

noncomputable def elementarySymmetric {ι : Type*} (P : Finset ι) (a : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ S ∈ P.powersetCard j, ∏ i ∈ S, a i

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def sieveCubeCRT {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j))) :
    (ZMod (∏ i, s i) × ZMod (∏ i, s i) × ZMod (∏ i, s i)) ≃
      (∀ i, ZMod (s i) × ZMod (s i) × ZMod (s i)) where
  toFun x i := (ZMod.prodEquivPi s hcop x.1 i,
    ZMod.prodEquivPi s hcop x.2.1 i, ZMod.prodEquivPi s hcop x.2.2 i)
  invFun y := ((ZMod.prodEquivPi s hcop).symm (fun i => (y i).1),
    (ZMod.prodEquivPi s hcop).symm (fun i => (y i).2.1),
    (ZMod.prodEquivPi s hcop).symm (fun i => (y i).2.2))
  left_inv x := by
    apply Prod.ext
    · exact (ZMod.prodEquivPi s hcop).symm_apply_apply x.1
    · apply Prod.ext
      · exact (ZMod.prodEquivPi s hcop).symm_apply_apply x.2.1
      · exact (ZMod.prodEquivPi s hcop).symm_apply_apply x.2.2
  right_inv y := by
    funext i
    apply Prod.ext
    · exact congrFun ((ZMod.prodEquivPi s hcop).apply_symm_apply (fun i => (y i).1)) i
    · apply Prod.ext
      · exact congrFun ((ZMod.prodEquivPi s hcop).apply_symm_apply (fun i => (y i).2.1)) i
      · exact congrFun ((ZMod.prodEquivPi s hcop).apply_symm_apply (fun i => (y i).2.2)) i

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def uniformFiniteLaw (α : Type*) [Fintype α] [Nonempty α] : FiniteLaw α where
  weight _ := 1 / Fintype.card α
  nonneg _ := by positivity
  total := by simp [Fintype.card_ne_zero]

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def sievePrimesUpTo (y : ℝ) : Finset ℕ := (Iic ⌊y⌋₊).filter Nat.Prime

def PrimeReciprocalInput : Prop :=
  ∃ C : ℝ, ∀ y : ℝ, 2 ≤ y →
    |(∑ p ∈ sievePrimesUpTo y, 1 / (p : ℝ)) - Real.log (Real.log y)| ≤ C

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def paddingCharacteristicFactor (p : ℕ) (t : ℝ) : ℝ :=
  1 - 8 * (1 - Real.cos (t * Real.log p)) / (5 * ((p : ℝ) + 4))

noncomputable def paddingCharacteristic (Q : Finset ℕ) (t : ℝ) : ℝ :=
  ∏ p ∈ Q, paddingCharacteristicFactor p t

noncomputable def paddingOscillation (Q : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ Q, (1 - Real.cos (t * Real.log p)) / p

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def paddingDifferenceAtom (p : ℕ) (e : Fin 3) : ℝ :=
  if e = 0 then 1 - 8 / (5 * ((p : ℝ) + 4)) else 4 / (5 * ((p : ℝ) + 4))

noncomputable def paddingDifferenceStep (p : ℕ) (e : Fin 3) : ℝ :=
  if e = 0 then 0 else if e = 1 then Real.log p else -Real.log p

lemma paddingDifferenceAtom_zero (p : ℕ) :
    paddingDifferenceAtom p 0 = 1 - 8 / (5 * ((p : ℝ) + 4)) := by
  unfold paddingDifferenceAtom; rw [if_pos rfl]
lemma paddingDifferenceAtom_one (p : ℕ) :
    paddingDifferenceAtom p 1 = 4 / (5 * ((p : ℝ) + 4)) := by
  unfold paddingDifferenceAtom; rw [if_neg (by decide)]
lemma paddingDifferenceAtom_two (p : ℕ) :
    paddingDifferenceAtom p 2 = 4 / (5 * ((p : ℝ) + 4)) := by
  unfold paddingDifferenceAtom; rw [if_neg (by decide)]

noncomputable def paddingStepLaw (p : ℕ) (hp : 2 ≤ p) : FiniteLaw (Fin 3) where
  weight := paddingDifferenceAtom p
  nonneg e := by
    have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
    have hd : 0 < 5 * ((p : ℝ) + 4) := by positivity
    unfold paddingDifferenceAtom
    split_ifs
    · have hh : 8 / (5 * ((p : ℝ) + 4)) ≤ 1 := (div_le_one hd).mpr (by linarith)
      linarith
    · positivity
  total := by
    rw [Fin.sum_univ_three]
    norm_num [paddingDifferenceAtom_zero, paddingDifferenceAtom_one, paddingDifferenceAtom_two]
    ring

noncomputable def paddingDifferenceLaw (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    FiniteLaw (Q → Fin 3) :=
  FiniteLaw.independent (fun p : Q => paddingStepLaw p (hQ p p.property))

noncomputable def paddingDifferenceValue (Q : Finset ℕ) (x : Q → Fin 3) : ℝ :=
  ∑ p : Q, paddingDifferenceStep p (x p)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def booleanLaw (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : FiniteLaw Bool where
  weight b := if b then q else 1 - q
  nonneg b := by cases b <;> simp [hq0, sub_nonneg.mpr hq1]
  total := by simp

noncomputable def paddingAvailabilityLaw (p : ℕ) (hp : 2 ≤ p) : FiniteLaw Bool :=
  booleanLaw (5 / ((p : ℝ) + 4)) (by positivity)
    (by
      apply (div_le_one (by positivity)).mpr
      have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith)

noncomputable def paddingSelectionLaw (a : Bool) : FiniteLaw Bool :=
  booleanLaw (if a then 4 / 5 else 0) (by cases a <;> norm_num)
    (by cases a <;> norm_num)

noncomputable def paddingPairLocal (p : ℕ) (hp : 2 ≤ p) : FiniteLaw (Bool × (Bool × Bool)) :=
  (paddingAvailabilityLaw p hp).dependentProduct
    (fun a => (paddingSelectionLaw a).product (paddingSelectionLaw a))

def paddingPairDifference (x : Bool × (Bool × Bool)) : Fin 3 :=
  if x.2.1 = x.2.2 then 0 else if x.2.1 then 1 else 2

noncomputable def paddingPairLaw (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    FiniteLaw (Q → Bool × (Bool × Bool)) :=
  FiniteLaw.independent (fun p : Q => paddingPairLocal p (hQ p p.property))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def booleanCount {ι : Type*} [Fintype ι] (a : ι → Bool) : ℝ :=
  ∑ i, if a i then 1 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def paddingAvailableLaw (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    FiniteLaw (Q → Bool) :=
  FiniteLaw.independent (fun p : Q => paddingAvailabilityLaw p (hQ p p.property))

noncomputable def paddingDivisorLaw (Q : Finset ℕ) (a : Q → Bool) :
    FiniteLaw (Q → Bool) := FiniteLaw.independent (fun p => paddingSelectionLaw (a p))

noncomputable def paddingLog (Q : Finset ℕ) (b : Q → Bool) : ℝ :=
  ∑ p : Q, if b p then Real.log p else 0

def paddingTripleEquiv (Q : Finset ℕ) :
    (Q → Bool × (Bool × Bool)) ≃ ((Q → Bool) × ((Q → Bool) × (Q → Bool))) where
  toFun x := (fun p => (x p).1, fun p => (x p).2.1, fun p => (x p).2.2)
  invFun y p := (y.1 p, y.2.1 p, y.2.2 p)
  left_inv x := by funext p; rfl
  right_inv y := by rfl

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def paddingOriginalPrimeLaw (p : ℕ) (hp : 2 ≤ p) : FiniteLaw Bool :=
  booleanLaw (1 / (p : ℝ)) (by positivity) (by
    apply (div_le_one (by exact_mod_cast (by omega : 0 < p))).mpr
    exact_mod_cast (by omega : 1 ≤ p))

noncomputable def paddingOriginalLaw (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    FiniteLaw (Q → Bool) :=
  FiniteLaw.independent (fun p : Q => paddingOriginalPrimeLaw p (hQ p p.property))

noncomputable def paddingTiltWeight (Q : Finset ℕ) (a : Q → Bool) : ℝ :=
  ∏ p : Q, if a p then 5 else 1

noncomputable def paddingTiltNormalizer (Q : Finset ℕ) : ℝ :=
  ∏ p : Q, (1 + 4 / (p : ℝ))

noncomputable def paddingDivisorCoefficient (Q : Finset ℕ) (b : Q → Bool) : ℝ :=
  ∏ p : Q, if b p then 4 else 1

def PaddingSelectionSupported (Q : Finset ℕ) (a b : Q → Bool) : Prop :=
  ∀ p, b p = true → a p = true

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def positiveCenterWeight (q : ι → ℝ) (S : Finset ι)
    (a : ι → Bool) : ℝ :=
  ∏ i, if i ∈ S then (if a i then 1 else 0) + q i else 1

noncomputable def positiveCenterNormalizer (q : ι → ℝ) (S : Finset ι) : ℝ :=
  ∏ i, if i ∈ S then 2 * q i else 1

noncomputable def positiveCenterParameter (q : ι → ℝ) (S : Finset ι) (i : ι) : ℝ :=
  if i ∈ S then (1 + q i) / 2 else q i

omit [Fintype ι] in
lemma positiveCenterParameter_nonneg (q : ι → ℝ) (S : Finset ι)
    (hq : ∀ i, 0 ≤ q i) (i : ι) : 0 ≤ positiveCenterParameter q S i := by
  unfold positiveCenterParameter
  split_ifs
  · exact div_nonneg (add_nonneg zero_le_one (hq i)) (by norm_num)
  · exact hq i

omit [Fintype ι] in
lemma positiveCenterParameter_le_one (q : ι → ℝ) (S : Finset ι)
    (hq : ∀ i, q i ≤ 1) (i : ι) : positiveCenterParameter q S i ≤ 1 := by
  unfold positiveCenterParameter
  split_ifs
  · linarith [hq i]
  · exact hq i

noncomputable def positiveCenterLaw (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) : FiniteLaw (ι → Bool) :=
  FiniteLaw.independent (fun i => booleanLaw (positiveCenterParameter q S i)
    (positiveCenterParameter_nonneg q S hq0 i) (positiveCenterParameter_le_one q S hq1 i))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def avoidsPrimeSet (P : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ P, ¬p ∣ n

def fourFormsAvoidPrimeSet (P : Finset ℕ) (x : ℕ × ℕ × ℕ) : Prop :=
  avoidsPrimeSet P x.1 ∧ avoidsPrimeSet P x.2.1 ∧ avoidsPrimeSet P x.2.2 ∧
    ∀ p ∈ P, ¬(p : ℤ) ∣ (x.1 : ℤ) + x.2.1 - x.2.2

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def roughIntervalSamples (P : Finset ℕ) (A N : ℕ) : Finset (Fin N) :=
  univ.filter (fun j => avoidsPrimeSet P (A + j.val))

noncomputable def roughCubeSamples (P : Finset ℕ) (A : ℕ × ℕ × ℕ) (N : ℕ) :
    Finset (Fin N × Fin N × Fin N) :=
  univ.filter (fun j => fourFormsAvoidPrimeSet P
    (A.1 + j.1.val, A.2.1 + j.2.1.val, A.2.2 + j.2.2.val))

noncomputable def additiveQuadruples (Z : Finset ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Z ×ˢ Z) ×ˢ (Z ×ˢ Z)).filter (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def sieveEulerFactor (p : ℕ) : ℝ := (1 - 1 / (p : ℝ))⁻¹

noncomputable def sieveSingularFactor (N : ℕ) : ℝ :=
  ∏ p ∈ N.primeFactors, sieveEulerFactor p

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Filter

noncomputable def qualitativeSieveHalfOrder (B : ℝ) : ℕ := ⌈500 * Real.log B⌉₊

noncomputable def qualitativeSieveLogCutoff (B : ℝ) : ℝ :=
  B ^ (9999 / 10000 : ℝ) / (100 * (2 * qualitativeSieveHalfOrder B + 1 : ℕ))

structure QualitativeSieveParameters (B : ℝ) : Prop where
  log_one : 1 ≤ Real.log B
  nextOrder_large : 220 * Real.log B ≤ (2 * qualitativeSieveHalfOrder B + 1 : ℕ)
  order_small : (2 * qualitativeSieveHalfOrder B : ℕ) ≤ 1002 * Real.log B
  cutoff_one : 1 ≤ qualitativeSieveLogCutoff B
  cutoff_le : qualitativeSieveLogCutoff B ≤ B
  cutoff_cost : qualitativeSieveLogCutoff B * Real.log B ≤
    B ^ (9999 / 10000 : ℝ) / 100000
  inverse_cutoff : 1 / qualitativeSieveLogCutoff B ≤
    100300 * Real.log B / B ^ (9999 / 10000 : ℝ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def qualitativeSievePrimes (B : ℝ) : Finset ℕ :=
  sievePrimesUpTo (Real.exp (qualitativeSieveLogCutoff B))

def HasNoPrimeFactorBelow (R : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → (p : ℝ) < R → ¬p ∣ n

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def dilationCutoff (B : ℝ) : ℕ :=
  ⌊Real.exp (B ^ (9999 / 10000 : ℝ) / 4)⌋₊

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

structure DilationWindowParameters (B C₀ : ℝ) (D : ℕ) : Prop where
  cutoff_pos : 0 < dilationCutoff B
  cutoff_le : dilationCutoff B ≤ D
  quotient_ten : ∀ a ∈ Icc 1 (dilationCutoff B), 10 ≤ D / a + 1
  quotient_error : ∀ a ∈ Icc 1 (dilationCutoff B),
    Real.log (Real.log (D / a + 1 : ℕ)) / Real.log (D / a + 1 : ℕ) ≤
      (2 * (Real.log (C₀ + 1) + 2)) *
        (Real.log B / B ^ (9999 / 10000 : ℝ))
  cutoff_relative : (dilationCutoff B : ℝ) / D ≤
    2 * (Real.log B / B ^ (9999 / 10000 : ℝ))
  cutoff_tail : (dilationCutoff B : ℝ) ^ (-(1 / 2) : ℝ) ≤
    2 * (Real.log B / B ^ (9999 / 10000 : ℝ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]

def nonsingletonLitSlots (label : τ → ι) (lit : τ → Bool) : Finset τ :=
  univ.filter (fun t => label t ∈ nonsingletonLabels label ∧ lit t = true)

def nonsingletonUnlitSlots (label : τ → ι) (lit : τ → Bool) : Finset τ :=
  univ.filter (fun t => label t ∈ nonsingletonLabels label ∧ lit t = false)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def triangleKernel (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - t) * Real.cos (t * x)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

def restoreCoordinate (i : ι) (a : A) (y : {j : ι // j ≠ i} → A) (j : ι) : A :=
  if h : j = i then a else y ⟨j, h⟩

namespace FiniteLaw

end FiniteLaw

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def uniformResidueLaw (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B) :
    FiniteLaw (Fin B) where
  weight x := if x.val < p then (p : ℝ)⁻¹ else 0
  nonneg x := by split_ifs <;> positivity
  total := by
    rw [← sum_filter]
    simp [Fin.card_filter_val_lt, min_eq_right hpB, ne_of_gt hp]

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in

noncomputable def designatedReciprocal (p : ι → ℕ) (S : Finset ι)
    (L U : Finset τ) (label : τ → ι) : ℝ :=
  (∏ t ∈ U, (p (label t) : ℝ)⁻¹) *
    (∏ i ∈ L.image label, (p i : ℝ)⁻¹) * (∏ i ∈ S, (p i : ℝ)⁻¹)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {ι τ A : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]

def singletonSlots (label : τ → ι) : Finset τ :=
  univ.filter (fun t => label t ∈ singletonLabels label)

def nonsingletonSlots (label : τ → ι) : Finset τ :=
  univ.filter (fun t => label t ∈ nonsingletonLabels label)

lemma singleton_occurrence_exists (label : τ → ι) (i : singletonLabels label) :
    ∃ t, label t = i.val := by
  have hc := (mem_filter.mp i.property).2
  have hn : (labelOccurrences label i.val).Nonempty := card_pos.mp (by omega)
  obtain ⟨t, ht⟩ := hn
  exact ⟨t, (mem_filter.mp ht).2⟩

noncomputable def singletonRepresentative (label : τ → ι) (i : singletonLabels label) : τ :=
  Classical.choose (singleton_occurrence_exists label i)

noncomputable def singletonTarget (label : τ → ι) (target : τ → A) (base : ι → A) : ι → A :=
  fun i => if hi : i ∈ singletonLabels label
    then target (singletonRepresentative label ⟨i, hi⟩) else base i

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]

noncomputable def designationLit (U : Finset τ) (t : τ) : Bool := decide (t ∉ U)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate _root_.Classical

noncomputable def weightedRoughFourier (Z : Finset ℕ) (c : ℕ → ℂ) (h : ℕ) :
    AddCircle (1 : ℝ) → ℂ :=
  fourierPolynomial Z (fun z => (h : ℤ) * z) (fun z => c z / (z : ℂ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def centeredTuple (P : Finset ℕ) (n : ℤ) : ℝ :=
  ∏ p ∈ P, ((if (p : ℤ) ∣ n then 1 else 0) - (p : ℝ)⁻¹)

noncomputable def paddingDensity (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (n : ℤ) : ℝ := by
  classical
  exact (∑ q ∈ Q, if eligible q ∧ (q : ℤ) ∣ n then u q else 0) / (g n) ^ 2

noncomputable def integerEdgeKeep (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (n : ℤ) : Prop :=
  paddingDensity Q u eligible g n ≤ K / L ∧ extra n

noncomputable def directedIntegerEdge (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h d q : ℕ) (n m : ℤ) : ℝ := by
  classical
  exact if q ∈ Q ∧ m = n + (h * q * d : ℕ) ∧ eligible q ∧ (q : ℤ) ∣ n ∧
      integerEdgeKeep Q u eligible g L K extra n ∧
      integerEdgeKeep Q u eligible g L K extra m
    then L * u q * center n / (g n * g m) else 0

noncomputable def integerEdgeMatrix {ι : Type*} [Fintype ι]
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h d : ℕ) (i j : ι) : ℝ :=
  ∑ q ∈ Q, (directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j) +
    directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i))

noncomputable def retainedPaddingAtom (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (n : ℤ) (q : ℕ) : ℝ := by
  classical
  exact if eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n
    then L * u q / (g n) ^ 2 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

noncomputable def integerLiouville (n : ℤ) : ℂ := liouville n.toNat

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def signedIntegerWeight (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h : ℕ) (a : SignedStep) (n : ℤ) : ℝ :=
  if a.forward then
    directedIntegerEdge Q u eligible g center L K extra h a.tuple a.padding n
      (n + a.displacement h)
  else
    directedIntegerEdge Q u eligible g center L K extra h a.tuple a.padding
      (n + a.displacement h) n

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

def integerShiftNext (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ)
    (e : D × (Q × Bool)) (x : D × ℤ) : D × ℤ :=
  (e.1, x.2 + (SignedStep.mk e.2.2 (tuple e.1) e.2.1).displacement h)

noncomputable def integerShiftWeight (Q : Finset ℕ) (tuple : D → ℕ)
    (u : ℕ → ℝ) (eligible : D → ℕ → Prop) (g : ℤ → ℝ) (center : D → ℤ → ℝ)
    (L K : ℝ) (extra : D → ℤ → Prop) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (e : D × (Q × Bool)) (x : D × ℤ) : ℝ := by
  classical
  exact if x.1 ≠ e.1 ∧ gate e.1 x.2 (integerShiftNext Q tuple h e x).2 then
    signedIntegerWeight Q u (eligible e.1) g (center e.1) L K (extra e.1) h
      ⟨e.2.2, tuple e.1, e.2.1⟩ x.2 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {ι : Type*} [Fintype ι]

noncomputable def maskMatrix (gate : ι → ι → Prop) (A : ι → ι → ℂ) (i j : ι) : ℂ := by
  classical
  exact if gate i j then A i j else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {ι : Type*} [Fintype ι]

noncomputable def maskedIntegerEdgeMatrix
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : ι → ι → Prop) : ι → ι → ℂ :=
  maskMatrix gate (fun i j => (integerEdgeMatrix site Q u eligible g center L K extra h d i j : ℂ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def complexifyMatrix (A : Matrix V V ℝ) : Matrix V V ℂ := A.map Complex.ofReal

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

variable {D V : Type*}

def integerStepWord (Q : Finset ℕ) (tuple : D → ℕ) {k : ℕ}
    (w : Fin k → D × (Q × Bool)) : List SignedStep :=
  (List.ofFn w).map (fun e => ⟨e.2.2, tuple e.1, e.2.1⟩)

variable [DecidableEq D]

variable [Fintype V]

variable [Fintype D] [DecidableEq V]

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

variable {D : Type*}

def integerClosedWordCode (Q : Finset ℕ) (tuple : D → ℕ) {k : ℕ}
    (a : (Fin k → D × (Q × Bool)) × (Fin k → D × (Q × Bool))) : List SignedStep :=
  integerStepWord Q tuple a.1 ++ reverseWord (integerStepWord Q tuple a.2)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [Fintype α] [DecidableEq α]
  {P : α → Type*} [∀ i, Fintype (P i)]

noncomputable def familyCenter (value : (i : α) → P i → ℕ)
    (offset : (i : α) → P i → ℤ) (x : (i : α) → P i) (n : ℤ) : ℝ :=
  ∏ i, ((if (value i (x i) : ℤ) ∣ offset i (x i) + n then 1 else 0) - (value i (x i) : ℝ)⁻¹)

noncomputable def familyTuple (value : (i : α) → P i → ℕ) (x : (i : α) → P i) : ℕ :=
  ∏ i, value i (x i)

omit [DecidableEq α] [∀ i, Fintype (P i)] in
lemma familyTuple_primeFactors (value : (i : α) → P i → ℕ)
    (hprime : ∀ i p, (value i p).Prime) (x : (i : α) → P i)
    (hinj : Function.Injective (fun i => value i (x i))) :
    (familyTuple value x).primeFactors = univ.image (fun i => value i (x i)) := by
  classical
  have hprod : (∏ p ∈ univ.image (fun i => value i (x i)), p) = familyTuple value x := by
    rw [prod_image]
    · rfl
    · exact fun i _ j _ hij => hinj hij
  rw [← hprod]
  apply Nat.primeFactors_prod
  intro p hp
  obtain ⟨i, _, rfl⟩ := mem_image.mp hp
  exact hprime i (x i)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  {P : α → Type*} [∀ i, Fintype (P i)]

noncomputable def primeFamilyGraphOperator
    (value : (i : α) → P i → ℕ) (offset : (i : α) → P i → ℤ)
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ι → ι → Prop) (x : (i : α) → P i) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  matrixOperator (maskedIntegerEdgeMatrix site Q u (eligible (familyTuple value x))
    g (familyCenter value offset x) L K (extra (familyTuple value x)) h
    (familyTuple value x) (gate (familyTuple value x)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

def progressionEdgeGate (h l b d : ℕ) (n m : ℤ) : Prop :=
  ∃ q : ℕ,
    (m = n + (h * q * d : ℕ) ∧ Int.ModEq (l : ℤ) n (b * q * d : ℕ)) ∨
    (n = m + (h * q * d : ℕ) ∧ Int.ModEq (l : ℤ) m (b * q * d : ℕ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def weightedRoughShiftProfile (f g : ℕ → ℂ) (Z : Finset ℕ) (c : ℕ → ℂ) (h n : ℕ) : ℂ :=
  ∑ z ∈ Z, (c z / (z : ℂ)) * (f n * g (n + h * z))

noncomputable def weightedRoughShiftAverage (f g : ℕ → ℂ) (Z : Finset ℕ) (c : ℕ → ℂ) (h Y : ℕ) : ℂ :=
  positivePrefix (weightedRoughShiftProfile f g Z c h) Y / (Y : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def residueScaledRoughProfile (l : ℕ) [NeZero l] (b : ZMod l)
    (Z : Finset ℕ) (h n : ℕ) : ℂ :=
  ∑ z ∈ Z, (z : ℂ)⁻¹ *
    (progressionSequence liouville l (b * (z : ZMod l)) n * liouville (n + h * z))

noncomputable def residueScaledRoughAverage (l : ℕ) [NeZero l] (b : ZMod l)
    (Z : Finset ℕ) (h Y : ℕ) : ℂ :=
  positivePrefix (residueScaledRoughProfile l b Z h) Y / (Y : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def partialLiouvilleProfile (l : ℕ) [NeZero l] (b : ZMod l)
    (u : ℕ) (Z : Finset ℕ) (h n : ℕ) : ℂ :=
  natDivisibilityIndicator u n * ∑ z ∈ Z, (z : ℂ)⁻¹ *
    (progressionSequence liouville l (b * ((u * z : ℕ) : ZMod l)) n *
      liouville (n + h * (u * z)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def fullLiouvilleProfile (l : ℕ) [NeZero l] (b : ZMod l)
    (u h n : ℕ) : ℂ :=
  natDivisibilityIndicator u n *
    (progressionSequence liouville l (b * (u : ZMod l)) n * liouville (n + h * u))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Matrix

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

noncomputable def rationalRows (B : Matrix ι ι ℤ) (S : Finset ι) :
    (ι → ℚ) →ₗ[ℚ] (S → ℚ) :=
  LinearMap.pi (fun i : S => (LinearMap.proj i.val).comp
    (B.map (Int.castRingHom ℚ)).mulVecLin)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def bernoulliCubeLaw (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteLaw (BooleanCube n) :=
  FiniteLaw.independent (fun _ : Fin n => booleanLaw p hp hp1)

def singleBitPattern {n : ℕ} (i : Fin n) : BooleanCube n := fun j => decide (j = i)

noncomputable def singleHitScore {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) : ℝ :=
  ∑ i ∈ S, cubePattern S (singleBitPattern i) x

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def isolatesOne {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) : Prop :=
  ∃ i ∈ S, ∀ j ∈ S, x j = singleBitPattern i j

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {n : ℕ}

noncomputable def andGateFactor {k : ℕ} (S : Finset (Fin k)) (u : Fin k → ℝ) : ℝ :=
  1 - ∑ i ∈ S, (1 - u i)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def restrictionBitLaw (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteLaw (Option Bool) where
  weight b := match b with | none => p | some _ => (1 - p) / 2
  nonneg b := by cases b <;> dsimp <;> positivity
  total := by simp [Fintype.sum_option]; ring

noncomputable def restrictionLaw (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteLaw (PartialAssignment n) :=
  FiniteLaw.independent (fun _ : Fin n => restrictionBitLaw p hp hp1)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def dyadicCubeLaw (n a : ℕ) : FiniteLaw (BooleanCube n) :=
  bernoulliCubeLaw n (1 / (2 : ℝ) ^ a) (by positivity)
    (by
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ a := one_le_pow₀ (by norm_num)
      simpa only [div_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hpow)

abbrev GateSamplingChoices (n k s : ℕ) := Fin (Nat.log 2 k + 3) → Fin s → BooleanCube n

noncomputable def gateSamplingLaw (n k s : ℕ) : FiniteLaw (GateSamplingChoices n k s) :=
  FiniteLaw.independent (fun a : Fin (Nat.log 2 k + 3) =>
    FiniteLaw.independent (fun _ : Fin s => dyadicCubeLaw n a.val))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def sampledCoordinates {k : ℕ} (x : BooleanCube k) : Finset (Fin k) :=
  univ.filter (fun i => x i = true)

def falseCoordinates {k : ℕ} (b : Fin k → Bool) : Finset (Fin k) :=
  univ.filter (fun i => b i = false)

noncomputable def sampledAndPolynomial {k s : ℕ}
    (x : GateSamplingChoices k k s) (u : Fin k → ℝ) : ℝ :=
  ∏ a, ∏ i, andGateFactor (sampledCoordinates (x a i)) u

noncomputable def boolAndValue {k : ℕ} (b : Fin k → Bool) : ℝ :=
  if ∀ i, b i = true then 1 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma literal_indicator_degree {n : ℕ} (i : Fin n) (b : Bool) :
    WalshDegreeLE (AC0Circuit.literal i b).indicator 1 := by
  have hw : WalshDegreeLE (walsh {i}) 1 := WalshDegreeLE.of_walsh {i} (by simp)
  have hp := (WalshDegreeLE.const (n := n) (1 / 2) 1).sub (hw.smul (1 / 2))
  have hn := (WalshDegreeLE.const (n := n) 1 1).sub hp
  cases b
  · convert (preTransparency := .instances) hn using 1
    funext x
    simp only [AC0Circuit.indicator, AC0Circuit.eval, Bool.false_eq_true, ite_false,
      walsh, prod_singleton]
    cases x i <;> norm_num [booleanSign]
  · convert (preTransparency := .instances) hp using 1
    funext x
    simp only [AC0Circuit.indicator, AC0Circuit.eval, ite_true, walsh, prod_singleton]
    cases x i <;> norm_num [booleanSign]

namespace AC0Circuit

def approximationDegree {n : ℕ} (s : ℕ) : AC0Circuit n → ℕ
  | .literal _ _ => 1
  | .andGate (k := k) children =>
    (univ.sup fun i => approximationDegree s (children i)) * s * (Nat.log 2 k + 3)
  | .orGate (k := k) children =>
    (univ.sup fun i => approximationDegree s (children i)) * s * (Nat.log 2 k + 3)

end AC0Circuit

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def cubeDensityLaw {n : ℕ} (g : BooleanCube n → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1) : FiniteLaw (BooleanCube n) where
  weight x := g x / Fintype.card (BooleanCube n)
  nonneg x := div_nonneg (hg x) (Nat.cast_nonneg _)
  total := by simpa only [← sum_div, cubeAverage] using hmean

lemma half_uniform_density_mean {n : ℕ} (g : BooleanCube n → ℝ)
    (hmean : cubeAverage g = 1) :
    cubeAverage (fun x => (g x + 1) / 2) = 1 := by
  have heq : (fun x => (g x + 1) / 2) = fun x => (1 / 2 : ℝ) * (g x + 1) := by
    funext x
    ring
  rw [heq, cubeAverage_mul_const, cubeAverage_add, hmean, cubeAverage_const]
  norm_num

noncomputable def mixedCubeLaw {n : ℕ} (g : BooleanCube n → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1) : FiniteLaw (BooleanCube n) :=
  cubeDensityLaw (fun x => (g x + 1) / 2) (fun x => by have hx := hg x; positivity)
    (half_uniform_density_mean g hmean)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def partialAssignmentOfMask {n : ℕ} (mask y : BooleanCube n) : PartialAssignment n :=
  fun i => if mask i then none else some (y i)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def composeRestrictionBit (r s : Option Bool) : Option Bool :=
  match r with | none => s | some b => some b

def composeRestriction {n : ℕ} (ρ τ : PartialAssignment n) : PartialAssignment n :=
  fun i => composeRestrictionBit (ρ i) (τ i)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology

def ModFivePrime (one : Bool) (p : ℕ) : Prop :=
  p.Prime ∧ if one then p % 5 = 1 else p % 5 ≠ 1

noncomputable def modFiveDensity (one : Bool) : ℝ := if one then 1 / 4 else 3 / 4

noncomputable def modFivePrimesUpTo (one : Bool) (x : ℝ) : Finset ℕ :=
  (Icc 0 ⌊x⌋₊).filter (ModFivePrime one)

noncomputable def modFiveLogWeight (one : Bool) (p : ℕ) : ℝ :=
  if ModFivePrime one p then Real.log p else 0

noncomputable def modFiveTheta (one : Bool) (x : ℝ) : ℝ :=
  ∑ p ∈ Icc 0 ⌊x⌋₊, modFiveLogWeight one p

noncomputable def deletedModFivePrimes (E : Finset ℕ) (one : Bool) (x : ℝ) : Finset ℕ :=
  modFivePrimesUpTo one x \ E

noncomputable def deletedModFiveTheta (E : Finset ℕ) (one : Bool) (x : ℝ) : ℝ :=
  ∑ p ∈ deletedModFivePrimes E one x, Real.log p

def ModFiveThetaInput : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (one : Bool) (x : ℝ), 2 ≤ x →
    |modFiveTheta one x - modFiveDensity one * x| ≤
      C * x * Real.exp (-c * Real.sqrt (Real.log x))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def partialCoefficientSum (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊, c n

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def reciprocalLog (x : ℝ) : ℝ := x⁻¹ / Real.log x

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def oscillatoryReciprocalLog (t x : ℝ) : ℝ :=
  (1 - Real.cos (t * Real.log x)) * reciprocalLog x

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.BigOperators _root_.Classical

def modFiveResidue (one : Bool) (n : ℕ) : Prop :=
  if one then n % 5 = 1 else n % 5 ≠ 1

noncomputable def modFiveMangoldtWeight (one : Bool) (n : ℕ) : ℝ :=
  if modFiveResidue one n then ArithmeticFunction.vonMangoldt n else 0

noncomputable def modFivePsi (one : Bool) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊, modFiveMangoldtWeight one n

noncomputable def modFiveTwistedPsi (χ : DirichletCharacter ℂ 5) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊,
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 5)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.HurwitzZeta
open scoped _root_.BigOperators _root_.Classical

noncomputable def modFiveMangoldtTwist (χ : DirichletCharacter ℂ 5) (n : ℕ) : ℂ :=
  χ (n : ZMod 5) * (ArithmeticFunction.vonMangoldt n : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical _root_.Topology

noncomputable def modFiveSummatory (χ : DirichletCharacter ℂ 5) (t : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊t⌋₊, χ (n : ZMod 5)

noncomputable def modFiveAbelKernel (χ : DirichletCharacter ℂ 5) (s : ℂ) (t : ℝ) : ℂ :=
  modFiveSummatory χ t * (t : ℂ) ^ (-(s + 1))

noncomputable def modFiveAbelIntegral (χ : DirichletCharacter ℂ 5) (s : ℂ) : ℂ :=
  s * ∫ t in Set.Ioi (1 : ℝ), modFiveAbelKernel χ s t

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Filter _root_.MeasureTheory _root_.Asymptotics
open scoped _root_.BigOperators _root_.Classical _root_.Topology

noncomputable def modFiveAbelInput (χ : DirichletCharacter ℂ 5) : ℝ → ℂ :=
  (Set.Ioi (1 : ℝ)).indicator (modFiveSummatory χ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction
open scoped _root_.BigOperators _root_.Classical _root_.LSeries.notation _root_.ArithmeticFunction.Moebius

noncomputable def modFiveInverseConstant : ℝ :=
  1 + ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖

noncomputable def modFiveNormalizedLFunction (χ : DirichletCharacter ℂ 5) (t : ℝ)
    (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ) + (3 / 2 : ℂ) * z) /
    DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex

noncomputable def modFivePerronKernel (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ s / (s * (s + 1))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter
open scoped _root_.BigOperators _root_.Classical _root_.Topology

noncomputable def modFiveNormalizedZeros (χ : DirichletCharacter ℂ 5) (t : ℝ) : Set ℂ :=
  Erdos970.zerosetKfR (7 / 8) (by norm_num) (modFiveNormalizedLFunction χ t)

noncomputable def modFiveLogDerivativeConstant : ℝ :=
  16 * (4 / 5 : ℝ) ^ 2 / ((4 / 5 : ℝ) - 3 / 4) ^ 3 +
    1 / (((15 / 16 : ℝ) ^ 2 / (7 / 8) - 7 / 8) * Real.log ((15 / 16 : ℝ) / (7 / 8)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Set _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def modFiveTriangle (x : ℝ) : ℂ :=
  ((max (1 - x) 0 : ℝ) : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def deletedModFiveLogWeight (E : Finset ℕ) (one : Bool) (p : ℕ) : ℝ :=
  if ModFivePrime one p ∧ p ∉ E then Real.log p else 0

noncomputable def modFivePrimeBand (E : Finset ℕ) (one : Bool) (a b : ℝ) : Finset ℕ :=
  (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p => ModFivePrime one p ∧ p ∉ E)

lemma modFivePrimeBand_mem {E : Finset ℕ} {one : Bool} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {p : ℕ} :
    p ∈ modFivePrimeBand E one a b ↔
      a < (p : ℝ) ∧ (p : ℝ) ≤ b ∧ ModFivePrime one p ∧ p ∉ E := by
  simp only [modFivePrimeBand, mem_filter, mem_Ioc]
  rw [Nat.floor_lt ha, Nat.le_floor_iff hb]
  tauto

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def primeSupplyEndpoint (A W : ℝ) (i : ℕ) : ℝ :=
  A * Real.exp (6 * W * i)

noncomputable def centeredPrimeSupply (E : Finset ℕ) (A W : ℝ) (i : ℕ) : Finset ℕ :=
  modFivePrimeBand E true (Real.exp (primeSupplyEndpoint A W i))
    (Real.exp (primeSupplyEndpoint A W (i + 1)))

noncomputable def paddingPrimeSupply (E : Finset ℕ) (L : ℝ) : Finset ℕ :=
  deletedModFivePrimes E false (Real.exp L)

lemma primeSupplyEndpoint_mono (A W : ℝ) (hA : 0 ≤ A) (hW : 0 ≤ W) :
    Monotone (primeSupplyEndpoint A W) := by
  intro i j hij
  unfold primeSupplyEndpoint
  apply mul_le_mul_of_nonneg_left _ hA
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (by positivity)

lemma centeredPrimeSupply_mem {E : Finset ℕ} {A W : ℝ} {i p : ℕ}
    (hp : p ∈ centeredPrimeSupply E A W i) :
    p.Prime ∧ p % 5 = 1 ∧ p ∉ E ∧
      primeSupplyEndpoint A W i < Real.log p ∧
      Real.log p ≤ primeSupplyEndpoint A W (i + 1) := by
  obtain ⟨hlo, hhi, hs, he⟩ := (modFivePrimeBand_mem (Real.exp_pos _).le
    (Real.exp_pos _).le).mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hs.1.pos
  refine ⟨hs.1, hs.2, he, ?_, ?_⟩
  · simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hlo
  · simpa only [Real.log_exp] using Real.log_le_log hp0 hhi

lemma centeredPrimeSupply_pairwise_disjoint (E : Finset ℕ) (A W : ℝ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) :
    Pairwise (fun i j => Disjoint (centeredPrimeSupply E A W i) (centeredPrimeSupply E A W j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro p hpi hpj
  have hi := centeredPrimeSupply_mem hpi
  have hj := centeredPrimeSupply_mem hpj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hh := primeSupplyEndpoint_mono A W hA hW (Nat.succ_le_of_lt hlt)
    linarith [hi.2.2.2.2, hj.2.2.2.1]
  · have hh := primeSupplyEndpoint_mono A W hA hW (Nat.succ_le_of_lt hgt)
    linarith [hj.2.2.2.2, hi.2.2.2.1]

lemma centered_padding_disjoint (E : Finset ℕ) (A W L : ℝ) (i : ℕ) :
    Disjoint (centeredPrimeSupply E A W i) (paddingPrimeSupply E L) := by
  apply disjoint_left.mpr
  intro p hp hq
  have hpc := (centeredPrimeSupply_mem hp).2.1
  have hqc := (mem_filter.mp (mem_sdiff.mp hq).1).2.2
  exact hqc hpc

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma paddingPrimeSupply_prime {E : Finset ℕ} {L : ℝ} {p : ℕ}
    (hp : p ∈ paddingPrimeSupply E L) : p.Prime :=
  (mem_filter.mp (mem_sdiff.mp hp).1).2.1

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

variable {α β : Type*} [Fintype α]

end FiniteLaw

noncomputable def paddingBin (η c x : ℝ) : ℤ := ⌊(x + c) / η⌋

noncomputable def paddingBinMass (Q : Finset ℕ) (a : Q → Bool) (η c : ℝ) (j : ℤ) : ℝ :=
  (paddingDivisorLaw Q a).probability (fun b => paddingBin η c (paddingLog Q b) = j)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def selectedCoordinates (Q : Finset ℕ) (b : Q → Bool) : Finset Q :=
  univ.filter (fun p => b p = true)

noncomputable def paddingSelectedDivisor (Q : Finset ℕ) (b : Q → Bool) : ℕ :=
  ∏ p ∈ selectedCoordinates Q b, p.val

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def paddingAvailablePrimes (Q : Finset ℕ) (a : Q → Bool) : Finset ℕ :=
  (selectedCoordinates Q a).image Subtype.val

lemma paddingAvailablePrimes_subset (Q : Finset ℕ) (a : Q → Bool) :
    paddingAvailablePrimes Q a ⊆ Q := by
  intro p hp
  obtain ⟨u, _, rfl⟩ := mem_image.mp hp
  exact u.property

lemma mem_paddingAvailablePrimes (Q : Finset ℕ) (a : Q → Bool) (p : Q) :
    p.val ∈ paddingAvailablePrimes Q a ↔ a p = true := by
  constructor
  · intro hp
    obtain ⟨u, hu, he⟩ := mem_image.mp hp
    have hup : u = p := Subtype.ext he
    subst u
    exact (mem_filter.mp hu).2
  · intro hp
    exact mem_image.mpr ⟨p, mem_filter.mpr ⟨mem_univ p, hp⟩, rfl⟩

lemma paddingSelectedDivisor_eq_prod (Q : Finset ℕ) (b : Q → Bool) :
    paddingSelectedDivisor Q b = ∏ p ∈ paddingAvailablePrimes Q b, p := by
  rw [paddingAvailablePrimes, prod_image]
  · rfl
  · intro p _ q _ hpq
    exact Subtype.ext hpq

lemma paddingSelectedDivisor_primeFactors (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (b : Q → Bool) : (paddingSelectedDivisor Q b).primeFactors = paddingAvailablePrimes Q b := by
  rw [paddingSelectedDivisor_eq_prod, Nat.primeFactors_prod]
  exact fun p hp => hQ p (paddingAvailablePrimes_subset Q b hp)

lemma paddingSelectedDivisor_injective (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    Function.Injective (paddingSelectedDivisor Q) := by
  intro b c hbc
  have hsets : paddingAvailablePrimes Q b = paddingAvailablePrimes Q c := by
    simpa only [paddingSelectedDivisor_primeFactors Q hQ] using congrArg Nat.primeFactors hbc
  funext p
  have he : (b p = true) ↔ (c p = true) := by
    rw [← mem_paddingAvailablePrimes Q b p, ← mem_paddingAvailablePrimes Q c p, hsets]
  cases hb : b p <;> cases hc : c p <;> simp_all

lemma paddingSelectedDivisor_mem (Q : Finset ℕ) (b : Q → Bool) :
    paddingSelectedDivisor Q b ∈ retainedPrimeDivisors Q := by
  rw [retainedPrimeDivisors, paddingSelectedDivisor_eq_prod]
  exact mem_image.mpr ⟨paddingAvailablePrimes Q b,
    mem_powerset.mpr (paddingAvailablePrimes_subset Q b), rfl⟩

lemma exists_paddingSelection (Q : Finset ℕ) (q : ℕ) (hq : q ∈ retainedPrimeDivisors Q) :
    ∃ b : Q → Bool, paddingSelectedDivisor Q b = q := by
  obtain ⟨S, hS, rfl⟩ := mem_image.mp hq
  have hSQ := mem_powerset.mp hS
  let b : Q → Bool := fun p => decide (p.val ∈ S)
  have hb : paddingAvailablePrimes Q b = S := by
    ext p
    constructor
    · intro hp
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hp
      simpa only [selectedCoordinates, mem_filter, mem_univ, true_and, b,
        decide_eq_true_eq] using hu
    · intro hp
      exact (mem_paddingAvailablePrimes Q b ⟨p, hSQ hp⟩).mpr (by simp [b, hp])
  exact ⟨b, by rw [paddingSelectedDivisor_eq_prod, hb]⟩

noncomputable def paddingDivisorEquiv (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    (Q → Bool) ≃ retainedPrimeDivisors Q :=
  Equiv.ofBijective (fun b => ⟨paddingSelectedDivisor Q b, paddingSelectedDivisor_mem Q b⟩)
    ⟨fun _ _ h => paddingSelectedDivisor_injective Q hQ (congrArg Subtype.val h), by
      intro q
      obtain ⟨b, hb⟩ := exists_paddingSelection Q q q.property
      exact ⟨b, Subtype.ext hb⟩⟩

noncomputable def literalPaddingBinMass (Q : Finset ℕ) (a : Q → Bool)
    (η c : ℝ) (j : ℤ) : ℝ :=
  (5 : ℝ) ^ (-(paddingAvailablePrimes Q a).card : ℤ) *
    ∑ q ∈ retainedPrimeDivisors Q,
      if q.primeFactors ⊆ paddingAvailablePrimes Q a ∧
          paddingBin η c (Real.log q) = j
      then (4 : ℝ) ^ q.primeFactors.card else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def integerPaddingBinMass (Q : Finset ℕ) (n : ℤ) (η c : ℝ) (j : ℤ) : ℝ :=
  (5 : ℝ) ^ (-((Q.filter (fun (p : ℕ) => (p : ℤ) ∣ n)).card : ℤ)) *
    ∑ q ∈ retainedPrimeDivisors Q,
      if (q : ℤ) ∣ n ∧ (j : ℝ) * η ≤ Real.log q + c ∧
          Real.log q + c < ((j : ℝ) + 1) * η
      then (4 : ℝ) ^ q.primeFactors.card else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def primeSupplyCount (W L : ℝ) : ℕ :=
  ⌊((1 / 200 : ℝ) * Real.log L) / (6 * W)⌋₊

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def reciprocalPaddingPrimeLaw (p : ℕ) : FiniteLaw Bool :=
  booleanLaw (4 / ((p : ℝ) + 4)) (by positivity) (by
    apply (div_le_one (by positivity)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg p))

noncomputable def reciprocalPaddingLaw (Q : Finset ℕ) : FiniteLaw (Q → Bool) :=
  FiniteLaw.independent (fun p : Q => reciprocalPaddingPrimeLaw p)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def paddingSmoothConstant : ℝ :=
  Real.exp ((4 / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))) *
    ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter
open scoped _root_.Classical _root_.Topology

noncomputable def modFiveEulerFactor (s : ℂ) : ℂ := 1 - (5 : ℂ) ^ (-s)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset
open _root_.Erdos970 hiding B1 Bf Cf ChebyshevPsi DRinD1 DeltaSpike Err H_auxiliary I If_ext If_taxicab I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform S_horiz S_max S_vert Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand ZetaZerosNearPoint ballDR e f_M lemKRinK1 lemKinDR lem_Contra_finiteKR lem_DRcompact lem_ballDR lem_bolzano_weierstrass lem_identity_infiniteKR lem_identity_theorem lem_identity_theoremKR lem_identity_theoremR lem_zeros_have_limit_point logDerivZeta riemannZeta0 sigma1Of zeroZ zerosetKfR zerosetKfRc zetaPartialSum
open scoped _root_.BigOperators _root_.Classical

noncomputable def modFiveSmoothedPsi (χ : DirichletCharacter ℂ 5) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊,
    modFiveMangoldtTwist χ n * ((1 - (n : ℝ) / x : ℝ) : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.Classical

noncomputable def modFivePhysicalPoint (t : ℝ) (z : ℂ) : ℂ :=
  (2 : ℂ) + Complex.I * (t : ℂ) + (3 / 2 : ℂ) * z

noncomputable def modFiveRealDiskPoint (σ : ℝ) : ℂ :=
  (((2 / 3 : ℝ) * (σ - 2) : ℝ) : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Set
open _root_.Erdos970 hiding ChebyshevPsi DeltaSpike I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand sigma1Of

noncomputable def modFivePerronIntegrand (χ : DirichletCharacter ℂ 5)
    (x : ℝ) (s : ℂ) : ℂ :=
  (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
    modFivePerronKernel x s

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex

noncomputable def halaszPerronWindowKernel (x δ : ℝ) (s : ℂ) : ℂ :=
  (((1 + δ : ℝ) : ℂ) * modFivePerronKernel ((1 + δ) * x) s -
    modFivePerronKernel x s) / (δ : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszPrimePowerLogConstant : ℝ :=
  2 * Real.log 4 + 32 / Real.log 2

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.MeasureTheory
open _root_.Erdos970 hiding B1 Bf Cf ChebyshevPsi DRinD1 DeltaSpike Err H_auxiliary I If_ext If_taxicab I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform S_horiz S_max S_vert Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand ZetaZerosNearPoint ballDR e f_M lemKRinK1 lemKinDR lem_Contra_finiteKR lem_DRcompact lem_ballDR lem_bolzano_weierstrass lem_identity_infiniteKR lem_identity_theorem lem_identity_theoremKR lem_identity_theoremR lem_zeros_have_limit_point logDerivZeta riemannZeta0 sigma1Of zeroZ zerosetKfR zerosetKfRc zetaPartialSum
open scoped _root_.Classical _root_.LSeries.notation

noncomputable def halaszSmoothFunction (f : ℕ → ℂ) (N n : ℕ) : ℂ :=
  if n ∈ Nat.smoothNumbers (N + 1) then f n else 0

noncomputable def halaszFiniteCoefficient (P : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ P then a n else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex

noncomputable def halaszTriangularSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((1 - (n : ℝ) / x : ℝ) : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def mrtPrimeBand (P Q : ℝ) : Finset ℕ :=
  sievePrimesUpTo Q \ sievePrimesUpTo P

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszMertensConstant : ℝ := Real.log 4 + 4

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszBandIndex (y : ℝ) : ℕ := Nat.log 2 ⌊y / Real.log 2⌋₊

noncomputable def halaszBandScale (j : ℕ) : ℝ := Real.log 2 * 2 ^ j

noncomputable def halaszPrimeBandPart (P : Finset ℕ) (X : ℝ) (j : ℕ) : Finset ℕ :=
  P.filter (fun p : ℕ => halaszBandIndex (Real.log (X / p)) = j)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def halaszPrimeWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log (n : ℝ) / n else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.MeasureTheory

noncomputable def halaszDenominatorWeight (X x : ℝ) : ℝ :=
  (Real.log X - Real.log x)⁻¹

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszPrimeTerm (f : ℕ → ℂ) (N p : ℕ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) * f p * (∑ m ∈ Icc 1 (N / p), f m)

noncomputable def halaszPrimePrefix (f : ℕ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ p ∈ sievePrimesUpTo x, halaszPrimeTerm f N p

noncomputable def halaszPrimeBandConvolution (f : ℕ → ℂ) (N : ℕ) (L U : ℝ) : ℂ :=
  ∑ p ∈ mrtPrimeBand L U, halaszPrimeTerm f N p

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszDoubleConvolution (f : ℕ → ℂ) (N : ℕ) (L : ℝ) : ℂ :=
  ∑ p ∈ mrtPrimeBand L ((N : ℝ) / 2),
    (Real.log (p : ℝ) : ℂ) * f p *
      (halaszPrimeConvolution f (N / p) / (Real.log ((N : ℝ) / p) : ℂ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def halaszDenominatorConstant : ℝ :=
  -Real.log (Real.log 2) + 2 * halaszMertensConstant / Real.log 2

noncomputable def halaszDoubleErrorConstant : ℝ :=
  4 + (Real.log 2 + 3 * halaszMertensConstant + halaszPrimePowerConstant + 1) +
    halaszInnerErrorConstant * (1 + |halaszDenominatorConstant|)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszRawPrimeTerm (B : ℕ → ℂ) (N p : ℕ) : ℂ :=
  (Real.log (p:ℝ):ℂ) * ∑ m ∈ Icc 1 (N/p), B (p*m)

noncomputable def halaszMixedPrimeConvolution (G B : ℕ → ℂ) (N : ℕ) (L U : ℝ) : ℂ :=
  ∑ p ∈ mrtPrimeBand L U,
    (Real.log (p:ℝ):ℂ)*G p*(∑ m ∈ Icc 1 (N/p), B m)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def mrtPrimePowerTail (a : ℝ) (X : ℕ) : Finset ℕ :=
  mrtPrimeBand (Real.exp ((Real.log (X:ℝ))^a)) X

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Set _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtRieszSquare (x : ℝ) : ℂ :=
  (((max (1 - x) 0) ^ 2 : ℝ) : ℂ)

noncomputable def mrtRieszKernel (x : ℝ) (s : ℂ) : ℂ :=
  2 * (x : ℂ) ^ s / (s * (s + 1) * (s + 2))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.ComplexConjugate _root_.Classical

noncomputable def mrtLiouvillePrimeTail (X : ℕ) : Finset ℕ :=
  mrtPrimePowerTail (3/4) X

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.ComplexConjugate _root_.Classical

noncomputable def mrtCharacterPrimeEuler {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (S : Finset ℕ) : ℂ :=
  ∏ p ∈ S, (1-characterTwist χ t p/(p:ℂ))⁻¹

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.ComplexConjugate

noncomputable def mrtCharacterShiftedEuler {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t δ : ℝ) (S : Finset ℕ) : ℂ :=
  ∏ p ∈ S, (1-(characterTwist χ t p/(p:ℂ))*
    (Real.exp (-δ*Real.log (p:ℝ)):ℂ))⁻¹

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical _root_.Topology

variable {q : ℕ} [NeZero q]

noncomputable def mrtCharacterSummatory (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊t⌋₊, χ (n : ZMod q)

noncomputable def mrtCharacterAbelKernel (χ : DirichletCharacter ℂ q) (s : ℂ) (t : ℝ) : ℂ :=
  mrtCharacterSummatory χ t * (t : ℂ) ^ (-(s + 1))

noncomputable def mrtCharacterAbelIntegral (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  s * ∫ t in Set.Ioi (1 : ℝ), mrtCharacterAbelKernel χ s t

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Filter _root_.MeasureTheory _root_.Asymptotics
open scoped _root_.BigOperators _root_.Classical _root_.Topology

variable {q : ℕ} [NeZero q]

noncomputable def mrtCharacterAbelInput (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Set.Ioi (1 : ℝ)).indicator (mrtCharacterSummatory χ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction
open scoped _root_.BigOperators _root_.Classical _root_.LSeries.notation _root_.ArithmeticFunction.Moebius

variable {q : ℕ} [NeZero q]

noncomputable def mrtCharacterInverseConstant : ℝ :=
  1 + ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖

noncomputable def mrtCharacterNormalizedLFunction (χ : DirichletCharacter ℂ q) (t : ℝ)
    (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ) + (3 / 2 : ℂ) * z) /
    DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ))

lemma mrtCharacterNormalizedLFunction_zero (χ : DirichletCharacter ℂ q) (t : ℝ) :
    mrtCharacterNormalizedLFunction χ t 0 = 1 := by
  simp only [mrtCharacterNormalizedLFunction, mul_zero, add_zero]
  exact div_self (χ.LFunction_ne_zero_of_one_le_re (Or.inr (by
    intro h; have := congrArg Complex.re h; norm_num at this)) (by norm_num))

lemma mrtCharacterNormalizedLFunction_differentiable (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) :
    Differentiable ℂ (mrtCharacterNormalizedLFunction χ t) := by
  unfold mrtCharacterNormalizedLFunction
  have ha : Differentiable ℂ (fun z : ℂ => (2 : ℂ) + Complex.I * (t : ℂ) + (3 / 2 : ℂ) * z) := by
    fun_prop
  exact ((DirichletCharacter.differentiable_LFunction hχ).comp ha).div_const _

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter
open scoped _root_.BigOperators _root_.Classical _root_.Topology

variable {q : ℕ} [NeZero q]

noncomputable def mrtCharacterNormalizedZeros (χ : DirichletCharacter ℂ q) (t : ℝ) : Set ℂ :=
  Erdos970.zerosetKfR (7 / 8) (by norm_num) (mrtCharacterNormalizedLFunction χ t)

lemma mrtCharacterNormalizedZeros_finite (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) : (mrtCharacterNormalizedZeros χ t).Finite := by
  apply Erdos970.lem_Contra_finiteKR (7 / 8) (by norm_num) (by norm_num)
    (mrtCharacterNormalizedLFunction χ t)
  · intro z _
    exact (mrtCharacterNormalizedLFunction_differentiable χ hχ t).analyticAt z
  · refine ⟨0, by simp, ?_⟩
    rw [mrtCharacterNormalizedLFunction_zero]
    exact one_ne_zero

noncomputable def mrtCharacterLogDerivativeConstant : ℝ :=
  16 * (4 / 5 : ℝ) ^ 2 / ((4 / 5 : ℝ) - 3 / 4) ^ 3 +
    1 / (((15 / 16 : ℝ) ^ 2 / (7 / 8) - 7 / 8) * Real.log ((15 / 16 : ℝ) / (7 / 8)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.Classical

variable {q : ℕ} [NeZero q]

noncomputable def mrtCharacterPhysicalPoint (t : ℝ) (z : ℂ) : ℂ :=
  (2 : ℂ) + Complex.I * (t : ℂ) + (3 / 2 : ℂ) * z

noncomputable def mrtCharacterRealDiskPoint (σ : ℝ) : ℂ :=
  (((2 / 3 : ℝ) * (σ - 2) : ℝ) : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def mrtCharacterHeight (q : ℕ) (t : ℝ) : ℝ :=
  Real.log ((q:ℝ)*(|t|+2))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter
open scoped _root_.BigOperators _root_.Classical _root_.Topology

noncomputable def mrtDiskZeros (f : ℂ → ℂ) : Set ℂ :=
  Erdos970.zerosetKfR (7 / 8) (by norm_num) f

lemma mrtDiskZeros_finite (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) : (mrtDiskZeros f).Finite := by
  apply Erdos970.lem_Contra_finiteKR (7 / 8) (by norm_num) (by norm_num) f hf
  exact ⟨0, by simp, by rw [h0]; exact one_ne_zero⟩

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter
open scoped _root_.BigOperators _root_.Classical _root_.Topology

variable {q : ℕ} [NeZero q]

noncomputable def mrtMovingPoint (r t : ℝ) (z : ℂ) : ℂ :=
  ((1 + 2 * r : ℝ) : ℂ) + Complex.I * (t : ℂ) + ((3 * r : ℝ) : ℂ) * z

noncomputable def mrtMovingLFunction (χ : DirichletCharacter ℂ q) (r t : ℝ)
    (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ (mrtMovingPoint r t z) /
    DirichletCharacter.LFunction χ (mrtMovingPoint r t 0)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.Classical

variable {q : ℕ} [NeZero q]

noncomputable def mrtMovingRealPoint (r σ : ℝ) : ℂ :=
  (((σ - 1 - 2 * r) / (3 * r) : ℝ) : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology

noncomputable def mrtPrincipalEulerFactor (p : ℕ) (s : ℂ) : ℂ :=
  1-(p:ℂ)^(-s)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction
open scoped _root_.BigOperators _root_.Classical _root_.LSeries.notation

variable {q : ℕ}

noncomputable def mrtCharacterMangoldtTwist (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.Set
open scoped _root_.Classical _root_.Topology

noncomputable def mrtQuadraticRemainder (u : ℝ) : ℝ :=
  u⁻¹ - (Real.exp u - 1)⁻¹

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology

noncomputable def mrtCharacterThermal {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑' n : ℕ+, χ.zetaMul n * (Real.exp (-t * n) : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def mrtBandLower (P Q : ℝ) (j : ℕ) : ℝ :=
  Real.exp ((j : ℝ) ^ (4 * j) * (Real.log Q) ^ (j - 1) * Real.log P)

noncomputable def mrtBandUpper (Q : ℝ) (j : ℕ) : ℝ :=
  Real.exp ((j : ℝ) ^ (4 * j + 2) * (Real.log Q) ^ j)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset _root_.HurwitzZeta
open scoped _root_.Classical

noncomputable def mrtVKLog (t : ℝ) : ℝ := Real.log (|t| + 3)

noncomputable def mrtVKRadius (t : ℝ) : ℝ := (mrtVKLog t) ^ (-(2 / 3 : ℝ))

noncomputable def mrtHurwitzFirstTerm (a : ℝ) (s : ℂ) : ℂ :=
  if a = 0 then 0 else (a : ℂ) ^ (-s)

def MRTWeakHurwitzGrowthInput : Prop :=
  ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ t : ℝ, T ≤ |t| →
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ s : ℂ,
      1 - mrtVKRadius t ≤ s.re → s.re ≤ 1 + 5 * mrtVKRadius t →
      |s.im - t| ≤ 3 * mrtVKRadius t →
        ‖hurwitzZeta (a : UnitAddCircle) s - mrtHurwitzFirstTerm a s‖ ≤ (mrtVKLog t) ^ C

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex
open scoped _root_.Classical

noncomputable def mrtVKWeight (q : ℕ) (t : ℝ) : ℝ :=
  1 + Real.log (q : ℝ) + Real.log (mrtVKLog t)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Metric _root_.Set _root_.Filter
open scoped _root_.Topology

noncomputable def mrtZetaPoleCorrection (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Filter

noncomputable def canonicalRoughParameter (L : ℝ) : ℝ := L ^ (9950 / 9999 : ℝ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

noncomputable def scalarWalkProduct (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (n : ℤ) : List SignedStep → ℝ
  | [] => 1
  | a :: w => weight a n * scalarWalkProduct h weight (n + a.displacement h) w

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def paddingWordWeight (Q : Finset ℕ) (weight : ℕ → ℤ → ℕ → ℝ)
    (next : ℕ → ℤ → ℕ → ℤ) : {m : ℕ} → ℕ → ℤ → (Fin m → Q) → ℝ
  | 0, _, _, _ => 1
  | _m + 1, i, n, q => weight i n (q 0).val *
      paddingWordWeight Q weight next (i + 1) (next i n (q 0).val) (Fin.tail q)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

variable {D V : Type*}

noncomputable def integerStepMask (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (e : D × (Q × Bool)) (x : D × ℤ) : ℝ :=
  if x.1 ≠ e.1 ∧ gate e.1 x.2 (integerShiftNext Q tuple h e x).2 ∧
    integerShiftNext Q tuple h e x ∈ Set.range embed then 1 else 0

noncomputable def integerPathMask (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop) :
    {k : ℕ} → D × ℤ → (Fin k → D × (Q × Bool)) → ℝ
  | 0, _, _ => 1
  | _k + 1, x, w =>
      integerStepMask embed Q tuple h gate (w 0) x *
        integerPathMask embed Q tuple h gate (integerShiftNext Q tuple h (w 0) x) (Fin.tail w)

variable [Fintype V] [DecidableEq D]

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

variable {D V : Type*}

def integerVertexGate (gate : D → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (d : D) (n m : ℤ) : Prop := gate d n m ∧ keep n ∧ keep m

noncomputable def vertexIndicator (keep : ℤ → Prop) (n : ℤ) : ℝ :=
  if keep n then 1 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

variable {D V : Type*}

noncomputable def physicalShiftWeight (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ)
    (gate : D → ℤ → ℤ → Prop) (weight : SignedStep → ℤ → ℝ)
    (e : D × (Q × Bool)) (x : D × ℤ) : ℝ :=
  if x.1 ≠ e.1 ∧ gate e.1 x.2 (integerShiftNext Q tuple h e x).2 then
    weight ⟨e.2.2, tuple e.1, e.2.1⟩ x.2 else 0

variable [Fintype V] [DecidableEq D]

noncomputable def maskedSignedIntegerWeight (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ) (center : ℕ → ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ) (keep : ℤ → Prop)
    (t : SignedStep) (n : ℤ) : ℝ :=
  vertexIndicator keep n *
    signedIntegerWeight Q u (eligible t.tuple) g (center t.tuple) L K
      (extra t.tuple) h t n * vertexIndicator keep (n + t.displacement h)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def primeDifference (P : Finset ℕ) (B : Matrix ι ι ℤ)
    (y z : ι → P) : ι → ℤ :=
  B *ᵥ ((fun j => ((y j).val : ℤ)) - (fun j => ((z j).val : ℤ)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Matrix

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

noncomputable def outsideCoordinates (control pivot : ρ → α) : Finset α :=
  (controlCoordinates control ∪ controlCoordinates pivot)ᶜ

noncomputable def splitAssignment (control pivot : ρ → α) (base : α → ℤ)
    (c y : ρ → ℤ) : α → ℤ :=
  Function.extend control c (Function.extend pivot y base)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Matrix

namespace FiniteLaw

variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A]

end FiniteLaw

variable {α ρ A : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

abbrev OutsideIndex (control pivot : ρ → α) := {z : α // z ∈ outsideCoordinates control pivot}

def coordinateIndex (control pivot : ρ → α) : ρ ⊕ (ρ ⊕ OutsideIndex control pivot) → α :=
  Sum.elim control (Sum.elim pivot Subtype.val)

omit [DecidableEq ρ] in
lemma coordinateIndex_bijective (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j) :
    Function.Bijective (coordinateIndex control pivot) := by
  classical
  have hout (z : OutsideIndex control pivot) :
      (∀ i, (z : α) ≠ control i) ∧ (∀ i, (z : α) ≠ pivot i) := by
    have hz : (z : α) ∉ controlCoordinates control ∧ (z : α) ∉ controlCoordinates pivot := by
      simpa only [outsideCoordinates, mem_compl, mem_union, not_or] using z.property
    constructor
    · intro i h
      exact hz.1 (mem_image.mpr ⟨i, mem_univ _, h.symm⟩)
    · intro i h
      exact hz.2 (mem_image.mpr ⟨i, mem_univ _, h.symm⟩)
  constructor
  · intro x y hxy
    rcases x with i | (i | z) <;> rcases y with j | (j | z')
    · exact congrArg Sum.inl (hc hxy)
    · exact False.elim (hdisjoint j i hxy.symm)
    · exact False.elim ((hout z').1 i hxy.symm)
    · exact False.elim (hdisjoint i j hxy)
    · exact congrArg (Sum.inr ∘ Sum.inl) (hp hxy)
    · exact False.elim ((hout z').2 i hxy.symm)
    · exact False.elim ((hout z).1 j hxy)
    · exact False.elim ((hout z).2 j hxy)
    · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext hxy)
  · intro z
    by_cases hz : z ∈ controlCoordinates control
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hz
      exact ⟨Sum.inl i, rfl⟩
    · by_cases hz' : z ∈ controlCoordinates pivot
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hz'
        exact ⟨Sum.inr (Sum.inl i), rfl⟩
      · exact ⟨Sum.inr (Sum.inr ⟨z, by simp [outsideCoordinates, hz, hz']⟩), rfl⟩

noncomputable def coordinateEquiv (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j) :
    ρ ⊕ (ρ ⊕ OutsideIndex control pivot) ≃ α :=
  Equiv.ofBijective (coordinateIndex control pivot) (coordinateIndex_bijective control pivot hc hp hdisjoint)

noncomputable def coordinateAssignment (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j)
    (base : OutsideIndex control pivot → A) (c y : ρ → A) : α → A :=
  fun z => Sum.elim c (Sum.elim y base) ((coordinateEquiv control pivot hc hp hdisjoint).symm z)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

noncomputable def retainedLiouvilleScalar (g : ℤ → ℝ) (keep : ℤ → Prop) (n : ℤ) : ℂ :=
  if keep n then (g n : ℂ) * integerLiouville n else 0

noncomputable def retainedLiouvilleEdge (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra keep : ℤ → Prop) (h d q : ℕ) (n m : ℤ) : ℂ :=
  if keep n ∧ keep m ∧ q ∈ Q ∧ m = n + (h * q * d : ℕ) ∧
    eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n ∧
    integerEdgeKeep Q u eligible g L K extra m then
      (u q * center n : ℝ) * integerLiouville n * integerLiouville m else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def retainedComplexScalar (g : ℤ → ℝ) (keep : ℤ → Prop)
    (f : ℤ → ℂ) (n : ℤ) : ℂ := if keep n then (g n : ℂ) * f n else 0

noncomputable def retainedRealEdge (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra keep : ℤ → Prop) (h d q : ℕ) (n m : ℤ) : ℝ :=
  if keep n ∧ keep m ∧ q ∈ Q ∧ m = n + (h * q * d : ℕ) ∧
    eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n ∧
    integerEdgeKeep Q u eligible g L K extra m then L * u q * center n else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {ι W A : Type*} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

def DependsOn (support : Finset ι) (F : (ι → A) → Bool) : Prop :=
  ∀ x y, (∀ i ∈ support, x i = y i) → F x = F y

noncomputable def witnessIntersection (I : W → (ι → A) → Bool) (S : Finset W)
    (x : ι → A) : ℝ := ∏ w ∈ S, if I w x then 1 else 0

noncomputable def witnessAvoidance (I : W → (ι → A) → Bool) (x : ι → A) : ℝ :=
  ∏ w : W, (1 - if I w x then 1 else 0)

def witnessSupport (support : W → Finset ι) (S : Finset W) : Finset ι :=
  S.biUnion support

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

def wordPrimeSupport : List SignedStep → Finset ℕ
  | [] => ∅
  | a :: w => a.tuple.primeFactors ∪ wordPrimeSupport w

def wordCoordinateSupport {ι : Type*} [Fintype ι] (prime : ι → ℕ) (w : List SignedStep) : Finset ι :=
  Finset.univ.filter (fun i => prime i ∈ wordPrimeSupport w)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def freshActiveBefore {n : ℕ} (h : ℕ) (word : Fin n → List SignedStep)
    (i : Fin n) : Prop :=
  ∃ z, ActivePrime h (word i) z ∧ ∀ j : Fin n, j < i → z ∉ wordPrimeSupport (word j)

noncomputable def freshActiveAfter {n : ℕ} (h : ℕ) (word : Fin n → List SignedStep)
    (i : Fin n) : Prop :=
  ∃ z, ActivePrime h (word i) z ∧ ∀ j : Fin n, i < j → z ∉ wordPrimeSupport (word j)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

abbrev WitnessRelationSlot (n N : ℕ) (ι : Type*) :=
  ι × ι × Fin n × Fin (N + 1) × Fin (N + 1) × Fin (N + 1) × Fin (N + 1)

structure WitnessSystemData (n N : ℕ) (ι : Type*) where
  mode : Fin 4
  chosen : Finset (Fin n)
  slot : chosen → WitnessRelationSlot n N ι

noncomputable def witnessSystemCode {n N : ℕ} {ι : Type*} (d : WitnessSystemData n N ι) :
    Fin 4 × (Fin n → Option (WitnessRelationSlot n N ι)) := by
  classical
  exact (d.mode, fun i => if hi : i ∈ d.chosen then some (d.slot ⟨i, hi⟩) else none)

lemma witnessSystemCode_injective (n N : ℕ) (ι : Type*) :
    Function.Injective (@witnessSystemCode n N ι) := by
  classical
  rintro ⟨mode, chosen, slot⟩ ⟨mode', chosen', slot'⟩ heq
  have hmode : mode = mode' := congrArg Prod.fst heq
  have hfun := congrArg Prod.snd heq
  have hchosen : chosen = chosen' := by
    ext i
    have hi := congrFun hfun i
    by_cases h : i ∈ chosen
    · by_cases h' : i ∈ chosen'
      · exact iff_of_true h h'
      · exfalso
        simp [witnessSystemCode, h, h'] at hi
    · by_cases h' : i ∈ chosen'
      · exfalso
        simp [witnessSystemCode, h, h'] at hi
      · exact iff_of_false h h'
  subst mode'
  subst chosen'
  congr 1
  funext i
  have hi := congrFun hfun i.val
  simpa [witnessSystemCode, i.property] using hi

instance (n N : ℕ) (ι : Type*) [Finite ι] : Finite (WitnessSystemData n N ι) :=
  Finite.of_injective _ (witnessSystemCode_injective n N ι)

noncomputable instance (n N : ℕ) (ι : Type*) [Fintype ι] :
    Fintype (WitnessSystemData n N ι) := Fintype.ofFinite _

end TwoPointCorrelations

end OAI

end

section

namespace OAI

open scoped _root_.BigOperators

namespace TwoPointCorrelations

section

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup E] [Module ℂ E]

def nonbacktracking (B : ι → E →ₗ[ℂ] E) : (ι → E) →ₗ[ℂ] (ι → E) where
  toFun z i := ∑ j ∈ Finset.univ.erase i, B j (z j)
  map_add' x y := by
    funext i
    simp [Finset.sum_add_distrib]
  map_smul' c x := by
    funext i
    simp [Finset.smul_sum, smul_sub]

end

end TwoPointCorrelations

end OAI

end

section

namespace OAI

open scoped _root_.BigOperators _root_.NNReal _root_.ENNReal

namespace TwoPointCorrelations

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

noncomputable def edgeResolvent (B : E →L[ℂ] E) (u : ℝ) : E →L[ℂ] E :=
  Ring.inverse (1 + u • B)

noncomputable def transferResolvent (B : ι → E →L[ℂ] E) (u : ℝ) : E →L[ℂ] E :=
  1 - ∑ i, u • (B i * edgeResolvent (B i) u)

noncomputable def nonbacktrackingContinuous (B : ι → E →L[ℂ] E) :
    (ι → E) →L[ℂ] (ι → E) :=
  (nonbacktracking (fun i => (B i).toLinearMap)).toContinuousLinearMap

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def coordinateProjection (keep : V → Prop) :
    EuclideanSpace ℂ V →L[ℂ] EuclideanSpace ℂ V :=
  matrixOperator (Matrix.diagonal (fun i => if keep i then (1 : ℂ) else 0))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def realMatrixSpectralRadius {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) : ℝ :=
  (spectralRadius ℂ (matrixOperator (fun i j => (A i j : ℂ)))).toReal

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

noncomputable def blockEuclideanEquiv :
    (D → EuclideanSpace ℂ V) ≃L[ℂ] EuclideanSpace ℂ (D × V) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun v => WithLp.toLp 2 (fun x => v x.1 x.2)
      invFun := fun v d => WithLp.toLp 2 (fun i => v (d, i))
      left_inv := by intro v; ext d i; rfl
      right_inv := by intro v; ext x; rfl
      map_add' := by intro v w; ext x; rfl
      map_smul' := by intro c v; ext x; rfl }

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

inductive BooleanDecisionTree (n : ℕ) where
  | leaf (value : Bool)
  | query (i : Fin n) (low high : BooleanDecisionTree n)

namespace BooleanDecisionTree

def eval {n : ℕ} : BooleanDecisionTree n → BooleanCube n → Bool
  | .leaf b, _ => b
  | .query i low high, x => if x i then high.eval x else low.eval x

def depth {n : ℕ} : BooleanDecisionTree n → ℕ
  | .leaf _ => 0
  | .query _ low high => max low.depth high.depth + 1

noncomputable def indicator {n : ℕ} (c : BooleanDecisionTree n) (x : BooleanCube n) : ℝ :=
  if c.eval x then 1 else 0

end BooleanDecisionTree

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace BooleanDecisionTree

def queryVariables {n : ℕ} : List (Fin n) →
    (PartialAssignment n → BooleanDecisionTree n) → PartialAssignment n → BooleanDecisionTree n
  | [], k, ρ => k ρ
  | i :: is, k, ρ => .query i
      (queryVariables is k (Function.update ρ i (some false)))
      (queryVariables is k (Function.update ρ i (some true)))

end BooleanDecisionTree

def dnfEval {n : ℕ} (F : List (CubeTerm n)) (x : BooleanCube n) : Bool :=
  F.any (fun C => C.eval x)

noncomputable def canonicalDNFTree {n : ℕ} :
    List (CubeTerm n) → PartialAssignment n → BooleanDecisionTree n
  | [], _ => .leaf false
  | C :: F, ρ =>
      if C.Compatible ρ then
        BooleanDecisionTree.queryVariables ((C.live ρ).sort (· ≤ ·))
          (fun τ => if C.Satisfied τ then .leaf true else canonicalDNFTree F τ) ρ
      else canonicalDNFTree F ρ

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace BooleanDecisionTree

def negate {n : ℕ} : BooleanDecisionTree n → BooleanDecisionTree n
  | .leaf b => .leaf (!b)
  | .query i low high => .query i low.negate high.negate

end BooleanDecisionTree

def CubeTerm.withLiteral {n : ℕ} (C : CubeTerm n) (i : Fin n) (b : Bool) : CubeTerm n :=
  ⟨insert i C.support, Function.update C.value i b⟩

def addDNFLiteral {n : ℕ} (F : List (CubeTerm n)) (i : Fin n) (b : Bool) :
    List (CubeTerm n) :=
  F.flatMap (fun C => if i ∉ C.support ∨ C.value i = b then [C.withLiteral i b] else [])

namespace BooleanDecisionTree

def toDNF {n : ℕ} : BooleanDecisionTree n → List (CubeTerm n)
  | .leaf false => []
  | .leaf true => [⟨∅, fun _ => false⟩]
  | .query i low high => addDNFLiteral low.toDNF i false ++ addDNFLiteral high.toDNF i true

end BooleanDecisionTree

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

namespace BooleanDecisionTree

def restrict {n : ℕ} (ρ : PartialAssignment n) :
    BooleanDecisionTree n → BooleanDecisionTree n
  | .leaf b => .leaf b
  | .query i low high =>
    match ρ i with
    | none => .query i (low.restrict ρ) (high.restrict ρ)
    | some false => low.restrict ρ
    | some true => high.restrict ρ

end BooleanDecisionTree

def HasSmallDecisionTree {n : ℕ} (f : BooleanCube n → Bool) (r : ℕ) : Prop :=
  ∃ T : BooleanDecisionTree n, T.depth ≤ r ∧ ∀ x, T.eval x = f x

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def decisionTreeDisjunction {n k : ℕ} (T : Fin k → BooleanDecisionTree n) :
    List (CubeTerm n) :=
  (univ : Finset (Fin k)).toList.flatMap (fun i => (T i).toDNF)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations.AC0Circuit

open _root_.Finset

def negate {n : ℕ} : AC0Circuit n → AC0Circuit n
  | .literal i b => .literal i (!b)
  | .andGate c => .orGate (fun i => negate (c i))
  | .orGate c => .andGate (fun i => negate (c i))

def relabel {n m : ℕ} (f : Fin n → Fin m) (c : AC0Circuit n) : AC0Circuit m :=
  substitute (fun i b => .literal (f i) b) c

noncomputable def conjunction {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : AC0Circuit n :=
  .andGate (fun i : Fin (Fintype.card ι) => c ((Fintype.equivFin ι).symm i))

end TwoPointCorrelations.AC0Circuit

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit

noncomputable def certificateDisjunction {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : AC0Circuit n :=
  (conjunction (fun i => (c i).negate)).negate

noncomputable def uniqueFalseTerm {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) (i : S) : AC0Circuit n :=
  conjunction (fun j : S => if j = i then (c j).negate else c j)

noncomputable def uniqueFalseCircuit {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) : AC0Circuit n :=
  certificateDisjunction (fun i : S => uniqueFalseTerm c S i)

end AC0Circuit

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit

noncomputable def gateSamplingException {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c : Fin k → AC0Circuit n) : AC0Circuit n :=
  conjunction (fun flag : Bool => if flag then
    (certificateDisjunction (fun j : Fin (Nat.log 2 k + 3) × Fin s =>
      uniqueFalseCircuit c (sampledCoordinates (sample j.1 j.2)))).negate
    else (andGate c).negate)

end AC0Circuit

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit

noncomputable def combineGateException {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c E : Fin k → AC0Circuit n) : AC0Circuit n :=
  certificateDisjunction (fun i : Option (Fin k) => match i with
    | none => gateSamplingException sample c
    | some i => E i)

end AC0Circuit

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def weightedStateCircuit {R n t m : ℕ}
    (qindex : Fin R → Fin n → Fin m) (pindex : Fin t → Fin m)
    (S : Fin R → Finset (Fin n)) (bits : BooleanCube t) (c : AC0Circuit m) :
    AC0Circuit m :=
  AC0Circuit.conjunction (fun i : Fin 3 =>
    ![activeStateVectorCircuit qindex S, AC0Circuit.assignmentTerm pindex bits, c] i)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit

noncomputable def disjunction {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : AC0Circuit n :=
  .orGate (fun i : Fin (Fintype.card ι) => c ((Fintype.equivFin ι).symm i))

end AC0Circuit

noncomputable def degreeSubsetCircuit {n : ℕ} (S : Finset (Fin n)) : AC0Circuit n :=
  AC0Circuit.conjunction (fun i : S => .literal i.val true)

noncomputable def degreeThresholdCircuit (n r : ℕ) : AC0Circuit n :=
  AC0Circuit.disjunction (fun S : (univ : Finset (Fin n)).powersetCard r =>
    degreeSubsetCircuit S.val)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit

noncomputable def sampleNormBound {n : ℕ} (s : ℕ) : AC0Circuit n → ℝ
  | .literal _ _ => 1
  | .andGate (k := k) c =>
    1 + (1 + (k : ℝ) * (2 + ∑ i, sampleNormBound s (c i))) ^ (s * (Nat.log 2 k + 3))
  | .orGate (k := k) c =>
    1 + (1 + (k : ℝ) * (2 + ∑ i, sampleNormBound s (c i))) ^ (s * (Nat.log 2 k + 3))

def exceptionSizeBound {n : ℕ} (s : ℕ) : AC0Circuit n → ℕ
  | .literal _ _ => 1
  | .andGate (k := k) c =>
    4 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
      (1 + k * (1 + ∑ i, (c i).size)) + ∑ i, exceptionSizeBound s (c i)
  | .orGate (k := k) c =>
    4 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
      (1 + k * (1 + ∑ i, (c i).size)) + ∑ i, exceptionSizeBound s (c i)

end AC0Circuit

structure CircuitCertificate {n : ℕ} (ν : FiniteLaw (BooleanCube n))
    (s : ℕ) (c : AC0Circuit n) where
  polynomial : BooleanCube n → ℝ
  error : AC0Circuit n
  degree_bound : WalshDegreeLE polynomial (c.approximationDegree s)
  error_depth : error.depth ≤ 4 * c.depth + 1
  error_size : error.size ≤ c.exceptionSizeBound s
  error_probability : ν.probability (fun x => error.eval x = true) ≤
    (c.size : ℝ) * (7 / 8 : ℝ) ^ s
  exact_off_error : ∀ x, error.eval x ≠ true → polynomial x = c.indicator x
  norm_bound : ∀ x, |polynomial x| ≤ c.sampleNormBound s

noncomputable def CircuitCertificate.literal {n : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (s : ℕ) (i : Fin n) (b : Bool) :
    CircuitCertificate ν s (.literal i b) where
  polynomial := (AC0Circuit.literal i b).indicator
  error := AC0Circuit.falseCircuit n
  degree_bound := literal_indicator_degree i b
  error_depth := by simp [AC0Circuit.falseCircuit, AC0Circuit.depth]
  error_size := by simp [AC0Circuit.falseCircuit, AC0Circuit.size, AC0Circuit.exceptionSizeBound]
  error_probability := by
    simp only [AC0Circuit.falseCircuit_eval, Bool.false_eq_true, FiniteLaw.probability,
      ite_false, FiniteLaw.average_const]
    positivity
  exact_off_error := fun _ _ => rfl
  norm_bound := by
    intro x
    unfold AC0Circuit.indicator
    split_ifs <;> norm_num [AC0Circuit.sampleNormBound]

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations.AC0Circuit

open _root_.Finset
open scoped _root_.Classical

def exceptionPolynomialBound (m s : ℕ) : ℕ :=
  5 + m + s * (Nat.log 2 m + 3) * (1 + m * (1 + m))

end TwoPointCorrelations.AC0Circuit

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

structure PrimeMonomial (ι : Type*) where
  coefficient : ℤ
  labels : Finset ι

namespace PrimeMonomial

variable {ι : Type*} [DecidableEq ι]

def eval (m : PrimeMonomial ι) (x : ι → ℤ) : ℤ :=
  m.coefficient * ∏ j ∈ m.labels, x j

def coefficientAt (m : PrimeMonomial ι) (i : ι) (x : ι → ℤ) : ℤ :=
  if i ∈ m.labels then m.coefficient * ∏ j ∈ m.labels.erase i, x j else 0

def constantAt (m : PrimeMonomial ι) (i : ι) (x : ι → ℤ) : ℤ :=
  if i ∈ m.labels then 0 else m.eval x

end PrimeMonomial

variable {ι τ : Type*} [DecidableEq ι] [Fintype τ]

def primeRelationEval (m : τ → PrimeMonomial ι) (x : ι → ℤ) : ℤ := ∑ t, (m t).eval x

def primeRelationCoefficient (m : τ → PrimeMonomial ι) (i : ι) (x : ι → ℤ) : ℤ :=
  ∑ t, (m t).coefficientAt i x

def primeRelationConstant (m : τ → PrimeMonomial ι) (i : ι) (x : ι → ℤ) : ℤ :=
  ∑ t, (m t).constantAt i x

def primeRelationContribution (m : τ → PrimeMonomial ι) (i : ι) (x : ι → ℤ) : ℤ :=
  ∑ t, if i ∈ (m t).labels then (m t).eval x else 0

def primeRelationSupport (m : τ → PrimeMonomial ι) : Finset ι := univ.biUnion (fun t => (m t).labels)

def primeRelationEvent (m : τ → PrimeMonomial ι) (selected control : ι) (x : ι → ℤ) : Prop :=
  x control ∣ primeRelationEval m x ∧ ¬x control ∣ primeRelationCoefficient m selected x

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

namespace FiniteLaw

variable {A : Type*} [Fintype A]

end FiniteLaw

variable {ι A : Type*} [DecidableEq ι]

def integerPrimeAssignment (value : A → ℕ) (x : ι → A) : ι → ℤ := fun i => value (x i)

namespace FiniteLaw

end FiniteLaw

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

structure LabeledPrimeWord (ι : Type*) where
  word : List SignedStep
  labels : Fin word.length → Finset ι

namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

def Realizes (w : LabeledPrimeWord ι) (value : ι → ℕ) : Prop :=
  ∀ i, ∏ j ∈ w.labels i, value j = (w.word[i.val]'i.isLt).tuple

def monomial (w : LabeledPrimeWord ι) (h : ℕ) (i : Fin w.word.length) : PrimeMonomial ι where
  coefficient := (if (w.word[i.val]'i.isLt).forward then 1 else -1) * (h : ℤ) * (w.word[i.val]'i.isLt).padding
  labels := w.labels i

def intervalRelation (w : LabeledPrimeWord ι) (h a b : ℕ) (i : Fin w.word.length) : PrimeMonomial ι :=
  if a ≤ i.val ∧ i.val < b then w.monomial h i else ⟨0, ∅⟩

end LabeledPrimeWord

namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

end LabeledPrimeWord

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {ι τ σ : Type*} [DecidableEq ι] [Fintype τ] [Fintype σ]

def relationAdd (m : τ → PrimeMonomial ι) (n : σ → PrimeMonomial ι) : τ ⊕ σ → PrimeMonomial ι :=
  Sum.elim m n

def relationNeg (m : τ → PrimeMonomial ι) (t : τ) : PrimeMonomial ι :=
  ⟨-(m t).coefficient, (m t).labels⟩

namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

end LabeledPrimeWord

def comparisonRelation {ι : Type*} [DecidableEq ι]
    (main wi wj : LabeledPrimeWord ι) (h aj ai ri rj : ℕ) :=
  relationAdd (main.intervalRelation h aj ai)
    (relationAdd (wi.intervalRelation h 0 ri) (relationNeg (wj.intervalRelation h 0 rj)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Matrix

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

noncomputable def integerColumnDeparture (label : ℕ → α) (t : ℕ → ℤ) (n : ℕ) (z : α) : ℤ :=
  ∑ a ∈ range n, if label a = z then t a else 0

noncomputable def columnDifference (label : ℕ → α) (t : ℕ → ℤ)
    (left right : ρ → ℕ) (i : ρ) (z : α) : ℤ :=
  integerColumnDeparture label t (left i) z - integerColumnDeparture label t (right i) z

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

structure OrderedPrimeSystem (ι : Type*) [DecidableEq ι] where
  Index : Type
  [indexFintype : Fintype Index]
  [indexOrder : LinearOrder Index]
  Term : Index → Type
  [termFintype : ∀ i, Fintype (Term i)]
  relation : (i : Index) → Term i → PrimeMonomial ι
  selected : Index → ι
  control : Index → ι
  control_ne : ∀ i, control i ≠ selected i
  triangular : ∀ i j, i < j →
    selected j ∉ primeRelationSupport (relation i) ∧ control i ≠ selected j

attribute [instance] OrderedPrimeSystem.indexFintype OrderedPrimeSystem.indexOrder
  OrderedPrimeSystem.termFintype

namespace OrderedPrimeSystem

variable {ι : Type*} [DecidableEq ι]

def size (S : OrderedPrimeSystem ι) : ℕ := Fintype.card S.Index

def Holds (S : OrderedPrimeSystem ι) (x : ι → ℤ) : Prop :=
  ∀ i, primeRelationEvent (S.relation i) (S.selected i) (S.control i) x

end OrderedPrimeSystem

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

structure PackedPrimeRelation (ι : Type*) where
  Term : Type
  [termFintype : Fintype Term]
  monomial : Term → PrimeMonomial ι

attribute [instance] PackedPrimeRelation.termFintype

namespace WitnessSystemData

variable {n N : ℕ} {ι : Type*} [DecidableEq ι]

abbrev selected (d : WitnessSystemData n N ι) (i : d.chosen) : ι := (d.slot i).1
abbrev control (d : WitnessSystemData n N ι) (i : d.chosen) : ι := (d.slot i).2.1
abbrev partner (d : WitnessSystemData n N ι) (i : d.chosen) : Fin n := (d.slot i).2.2.1
abbrev left (d : WitnessSystemData n N ι) (i : d.chosen) : Fin (N + 1) := (d.slot i).2.2.2.1
abbrev right (d : WitnessSystemData n N ι) (i : d.chosen) : Fin (N + 1) := (d.slot i).2.2.2.2.1
abbrev departure (d : WitnessSystemData n N ι) (i : d.chosen) : Fin (N + 1) := (d.slot i).2.2.2.2.2.1
abbrev partnerDeparture (d : WitnessSystemData n N ι) (i : d.chosen) : Fin (N + 1) := (d.slot i).2.2.2.2.2.2

def relation (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (i : d.chosen) : PackedPrimeRelation ι :=
  if d.mode.val < 2 then {
    Term := Fin (word i).word.length
    termFintype := inferInstance
    monomial := (word i).intervalRelation h (d.left i) (d.right i) }
  else if d.mode.val = 2 then {
    Term := Fin main.word.length ⊕ (Fin (word i).word.length ⊕ Fin (word (d.partner i)).word.length)
    termFintype := inferInstance
    monomial := comparisonRelation main (word i) (word (d.partner i)) h
      (d.left i) (d.right i) (d.departure i) (d.partnerDeparture i) }
  else {
    Term := Fin main.word.length ⊕ (Fin (word (d.partner i)).word.length ⊕ Fin (word i).word.length)
    termFintype := inferInstance
    monomial := comparisonRelation main (word (d.partner i)) (word i) h
      (d.left i) (d.right i) (d.partnerDeparture i) (d.departure i) }

@[instance_reducible] noncomputable def chosenOrder (d : WitnessSystemData n N ι) : LinearOrder d.chosen :=
  if d.mode.val % 2 = 0 then inferInstance
  else (inferInstance : LinearOrder (OrderDual d.chosen))

def Triangular (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) : Prop :=
  (∀ i, d.control i ≠ d.selected i) ∧
    ∀ i j, @LT.lt d.chosen d.chosenOrder.toLT i j →
      d.selected j ∉ primeRelationSupport (d.relation main word h i).monomial ∧
        d.control i ≠ d.selected j

def Holds (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (x : ι → ℤ) : Prop :=
  ∀ i, primeRelationEvent (d.relation main word h i).monomial (d.selected i) (d.control i) x

noncomputable def toSystem (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) :
    OrderedPrimeSystem ι where
  Index := d.chosen
  indexFintype := inferInstance
  indexOrder := d.chosenOrder
  Term i := (d.relation main word h i).Term
  termFintype i := (d.relation main word h i).termFintype
  relation i := (d.relation main word h i).monomial
  selected := d.selected
  control := d.control
  control_ne := ht.1
  triangular := ht.2

end WitnessSystemData

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

structure PatternEquiv (w v : LabeledPrimeWord ι) where
  index : Fin w.word.length ≃ Fin v.word.length
  index_val : ∀ i, (index i).val = i.val
  monomial : ∀ h i, v.monomial h (index i) = w.monomial h i

def resample (w : LabeledPrimeWord ι) (value : ι → ℕ) : LabeledPrimeWord ι where
  word := List.ofFn (fun i : Fin w.word.length =>
    ⟨(w.word[i.val]'i.isLt).forward, ∏ z ∈ w.labels i, value z,
      (w.word[i.val]'i.isLt).padding⟩)
  labels i := w.labels ⟨i.val, by simpa using i.isLt⟩

omit [DecidableEq ι] in
@[simp] lemma resample_length (w : LabeledPrimeWord ι) (value : ι → ℕ) :
    (w.resample value).word.length = w.word.length := by
  simp [resample]

def resamplePattern (w : LabeledPrimeWord ι) (value : ι → ℕ) :
    PatternEquiv w (w.resample value) where
  index := finCongr (w.resample_length value).symm
  index_val _ := rfl
  monomial h i := by
    simp only [monomial, resample, List.getElem_ofFn]
    rfl

end LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

def comparisonIndexEquiv {main wi wj main' wi' wj' : LabeledPrimeWord ι}
    (hm : LabeledPrimeWord.PatternEquiv main main')
    (hi : LabeledPrimeWord.PatternEquiv wi wi')
    (hj : LabeledPrimeWord.PatternEquiv wj wj') :
    (Fin main.word.length ⊕ (Fin wi.word.length ⊕ Fin wj.word.length)) ≃
      (Fin main'.word.length ⊕ (Fin wi'.word.length ⊕ Fin wj'.word.length)) :=
  Equiv.sumCongr hm.index (Equiv.sumCongr hi.index hj.index)

namespace WitnessSystemData

variable {n N : ℕ}

end WitnessSystemData

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def ResampledWitnessEvent {n : ℕ} {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (mark : Fin n → ι) (attachment position : Fin n → ℕ) (value : ι → ℕ) : Prop :=
  Function.Injective value ∧
  (∀ j, (value j).Prime) ∧
  (∀ i, MinimalWord (ForwardProhibited h s supply) ((word i).resample value).word) ∧
  (∀ i t, t ∈ ((word i).resample value).word → Squarefree t.tuple) ∧
  (∀ i t, t ∈ ((word i).resample value).word → t.tuple.primeFactors.card = J) ∧
  (∀ i p j, TuplePrimeAt ((word i).resample value).word p j →
    ¬p ∣ h ∧ ∀ t ∈ ((word i).resample value).word, ¬p ∣ t.padding) ∧
  (∀ i, value (mark i) ∈ wordPrimeSupport ((word i).resample value).word) ∧
  (∀ i j, j ≠ i → value (mark i) ∉ wordPrimeSupport ((word j).resample value).word) ∧
  (∀ i v, TuplePrimeAt (main.resample value).word (value (mark i)) v → v = position i) ∧
  ∃ x : ℤ, ∀ i, PositiveWord h
    (x + wordDisplacement h ((main.resample value).word.take (attachment i)))
    ((word i).resample value).word

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def HasResampledWitnesses {n : ℕ} {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (h s J : ℕ) (supply : ℕ → ℕ → Prop) (value : ι → ℕ) : Prop :=
  ∃ (mark : Fin n → ι) (attachment position : Fin n → ℕ),
    Monotone attachment ∧ (∀ i, attachment i ≤ main.word.length) ∧
      ResampledWitnessEvent main word h s J supply mark attachment position value

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

abbrev BadRelationCode (N : ℕ) (ι : Type*) := ι × ι × Fin (N + 1) × Fin (N + 1)

namespace BadRelationCode

variable {N : ℕ} {ι : Type*} [DecidableEq ι]

def Holds (d : BadRelationCode N ι) (w : LabeledPrimeWord ι) (h : ℕ) (x : ι → ℤ) : Prop :=
  d.2.1 ≠ d.1 ∧ primeRelationEvent (w.intervalRelation h d.2.2.1 d.2.2.2) d.1 d.2.1 x

def toSystem (d : BadRelationCode N ι) (w : LabeledPrimeWord ι) (h : ℕ)
    (hne : d.2.1 ≠ d.1) : OrderedPrimeSystem ι where
  Index := Fin 1
  Term _ := Fin w.word.length
  relation _ := w.intervalRelation h d.2.2.1 d.2.2.2
  selected _ := d.1
  control _ := d.2.1
  control_ne _ := hne
  triangular i j hij := by have hi := i.isLt; have hj := j.isLt; omega

end BadRelationCode

def ResampledProhibitedEvent {ι : Type*} [DecidableEq ι]
    (w : LabeledPrimeWord ι) (h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (value : ι → ℕ) : Prop :=
  Function.Injective value ∧ (∀ i, (value i).Prime) ∧
  ForwardProhibited h s supply (w.resample value).word ∧
  (∀ a ∈ (w.resample value).word, Squarefree a.tuple) ∧
  (∀ a ∈ (w.resample value).word, a.tuple.primeFactors.card = J) ∧
  (∀ p j, TuplePrimeAt (w.resample value).word p j →
    ¬p ∣ h ∧ ∀ a ∈ (w.resample value).word, ¬p ∣ a.padding)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations
namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

def segment (w : LabeledPrimeWord ι) (a n : ℕ) : LabeledPrimeWord ι where
  word := (w.word.drop a).take n
  labels i := w.labels ⟨a + i.val, by
    have hi : i.val < min n (w.word.length - a) := by
      simpa only [List.length_take, List.length_drop] using i.isLt
    have := (lt_min_iff.mp hi).2
    omega⟩

end LabeledPrimeWord
end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

structure PrimeSlotData (R N : ℕ) where
  forward : Fin R → Bool
  row : Fin N → Fin R
  isPadding : Fin N → Bool
  prime : Fin N → ℕ

namespace PrimeSlotData

variable {R N : ℕ}

def slots (a : PrimeSlotData R N) (i : Fin R) (b : Bool) : Finset (Fin N) :=
  univ.filter (fun j => a.row j = i ∧ a.isPadding j = b)

def factor (a : PrimeSlotData R N) (i : Fin R) (b : Bool) : ℕ :=
  ∏ j ∈ a.slots i b, a.prime j

def word (a : PrimeSlotData R N) : List SignedStep :=
  List.ofFn (fun i => ⟨a.forward i, a.factor i false, a.factor i true⟩)

noncomputable def code (a : PrimeSlotData R N) : CrudeWordCode R N R :=
  (a.forward, columnRepresentative a.prime ∅, a.row, a.isPadding)

end PrimeSlotData

namespace CrudeWordCode

variable {R N : ℕ}

def usedClasses (c : CrudeWordCode R N R) : Finset (Fin N) := univ.image c.2.1

def classAt (c : CrudeWordCode R N R) (i : Fin N) : c.usedClasses :=
  ⟨c.2.1 i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩

def primeData (c : CrudeWordCode R N R) (value : c.usedClasses → ℕ) : PrimeSlotData R N where
  forward := c.1
  row := c.2.2.1
  isPadding := c.2.2.2
  prime i := value (c.classAt i)

def numericalWord (c : CrudeWordCode R N R) (value : c.usedClasses → ℕ) : List SignedStep :=
  (c.primeData value).word

lemma numericalWord_length (c : CrudeWordCode R N R) (value : c.usedClasses → ℕ) :
    (c.numericalWord value).length = R := by
  simp [numericalWord, PrimeSlotData.word]

end CrudeWordCode

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {R : ℕ}

abbrev ActualPrimeSlot (w : Fin R → SignedStep) :=
  Σ i : Fin R, (w i).tuple.primeFactors ⊕ (w i).padding.primeFactors

def actualSlotPrime (w : Fin R → SignedStep) (s : ActualPrimeSlot w) : ℕ :=
  match s.2 with
  | .inl p => p.val
  | .inr p => p.val

def actualSlotKind (w : Fin R → SignedStep) (s : ActualPrimeSlot w) : Bool :=
  match s.2 with
  | .inl _ => false
  | .inr _ => true

noncomputable def actualPrimeSlotEquiv (w : Fin R → SignedStep) :
    ActualPrimeSlot w ≃ Fin (Fintype.card (ActualPrimeSlot w)) :=
  Fintype.equivFin (ActualPrimeSlot w)

noncomputable def actualPrimeSlotData (w : Fin R → SignedStep) :
    PrimeSlotData R (Fintype.card (ActualPrimeSlot w)) where
  forward i := (w i).forward
  row j := ((actualPrimeSlotEquiv w).symm j).1
  isPadding j := actualSlotKind w ((actualPrimeSlotEquiv w).symm j)
  prime j := actualSlotPrime w ((actualPrimeSlotEquiv w).symm j)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace CrudeWordCode

variable {R N : ℕ}

def recordedSlots (c : CrudeWordCode R N R) (i : Fin R) (b : Bool) : Finset (Fin N) :=
  univ.filter (fun j => c.2.2.1 j = i ∧ c.2.2.2 j = b)

def KindConsistent (c : CrudeWordCode R N R) : Prop :=
  ∀ j, c.2.2.2 (c.2.1 j) = c.2.2.2 j

def RowInjective (c : CrudeWordCode R N R) : Prop :=
  ∀ i b, Set.InjOn c.2.1 (c.recordedSlots i b)

def tupleClasses (c : CrudeWordCode R N R) : Finset c.usedClasses :=
  univ.filter (fun z => c.2.2.2 z.val = false)

def tupleLabels (c : CrudeWordCode R N R) (i : Fin R) : Finset c.tupleClasses :=
  ((c.recordedSlots i false).image c.classAt).subtype (fun z => z ∈ c.tupleClasses)

def labeledWord (c : CrudeWordCode R N R)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) : LabeledPrimeWord c.tupleClasses where
  word := c.numericalWord (joinCoordinates c.tupleClasses (fun _ => 1) b)
  labels i := c.tupleLabels ⟨i.val, by
    exact lt_of_lt_of_eq i.isLt (numericalWord_length c _)⟩

end CrudeWordCode

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

def NumericalWitnessEvent {n : ℕ} {ι : Type*}
    (main : List SignedStep) (word : Fin n → List SignedStep) (value : ι → ℕ)
    (h s J : ℕ) (supply : ℕ → ℕ → Prop) : Prop :=
  ∃ (mark : Fin n → ι) (attachment position : Fin n → ℕ),
    Monotone attachment ∧ (∀ i, attachment i ≤ main.length) ∧
    Function.Injective value ∧ (∀ j, (value j).Prime) ∧
    (∀ i, MinimalWord (ForwardProhibited h s supply) (word i)) ∧
    (∀ i t, t ∈ word i → Squarefree t.tuple) ∧
    (∀ i t, t ∈ word i → t.tuple.primeFactors.card = J) ∧
    (∀ i p j, TuplePrimeAt (word i) p j → ¬p ∣ h ∧ ∀ t ∈ word i, ¬p ∣ t.padding) ∧
    (∀ i, value (mark i) ∈ wordPrimeSupport (word i)) ∧
    (∀ i j, j ≠ i → value (mark i) ∉ wordPrimeSupport (word j)) ∧
    (∀ i v, TuplePrimeAt main (value (mark i)) v → v = position i) ∧
    ∃ x : ℤ, ∀ i, PositiveWord h
      (x + wordDisplacement h (main.take (attachment i))) (word i)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def outsideCoordinate {I : Type*} {β : I → Type*} (j : I) (w : ∀ i, β i) :
    (i : {i // i ≠ j}) → β i := fun i => w i

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

abbrev ColumnPrimeAssignment (J R : ℕ) (P : Fin J → Finset ℕ) :=
  (j : Fin J) → Fin R → P j

noncomputable def columnReciprocalWeight {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) : ℝ :=
  ∏ j, ∏ p ∈ univ.image (w j), (p.val : ℝ)⁻¹

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

def columnSingletonCount {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) : ℕ :=
  ∑ j, (singletonLabels (w j)).card

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def forcedResidue (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B) (offset : ℤ) : Fin B :=
  letI : NeZero p := ⟨hp.ne'⟩
  ⟨(- (offset : ZMod p)).val, (ZMod.val_lt _).trans_le hpB⟩

abbrev ColumnPrimeCoordinate {J : ℕ} (P : Fin J → Finset ℕ) := Σ j, P j

def tupleSlotLabel {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (t : Fin R × Fin J) : ColumnPrimeCoordinate P :=
  ⟨t.2, w t.2 t.1⟩

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def retainedColumnPaddingWeight {J k : ℕ} {P : Fin J → Finset ℕ}
    (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ)
    (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
    (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ)
    (n : ℤ) (w : ColumnPrimeAssignment J (2 * k) P) (q : Fin (2 * k) → Q) : ℝ :=
  paddingWordWeight Q
    (fun i n q => retainedPaddingAtom Q u (eligible w i) g L K (extra w i) n q)
    (next w) 0 n q

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def FiniteLaw.uniform (α : Type*) [Fintype α] [Nonempty α] : FiniteLaw α where
  weight _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by simp

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

structure ColumnWordPattern (α : Type*) where
  length : ℕ
  label : ℕ → α
  forward : ℕ → Bool
  padding : ℕ → ℕ
  otherColumns : ℕ → ℕ

namespace ColumnWordPattern

variable {α : Type*}

def step (w : ColumnWordPattern α) (value : α → ℕ) (j : ℕ) : SignedStep where
  forward := w.forward j
  tuple := value (w.label j) * w.otherColumns j
  padding := w.padding j

def word (w : ColumnWordPattern α) (value : α → ℕ) : List SignedStep :=
  List.ofFn (fun j : Fin w.length => w.step value j)

def coefficient (w : ColumnWordPattern α) (h j : ℕ) : ℤ :=
  (if w.forward j then 1 else -1) * (h : ℤ) * w.padding j * w.otherColumns j

end ColumnWordPattern

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations.ColumnWordPattern

open _root_.Finset

variable {α : Type*}

def slice (w : ColumnWordPattern α) (start len : ℕ) : ColumnWordPattern α where
  length := len
  label := fun t => w.label (start + t)
  forward := fun t => w.forward (start + t)
  padding := fun t => w.padding (start + t)
  otherColumns := fun t => w.otherColumns (start + t)

end TwoPointCorrelations.ColumnWordPattern

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α]

def indexedRegularSegments (label : ℕ → α) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ)) : List (List (ℕ × α)) :=
  blocks.flatMap (fun b =>
    (partitionColumnRuns (fun p => omitted p.2) (indexedBlockRuns label b.1 b.2)).filterMap
      (Sum.elim some (fun _ => none)))

variable {K ι : Type*} [Field K] [Fintype α] [DecidableEq ι]

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

def emptyForestPathCode (N : ℕ) : ForestPathData.Code N 0 :=
  (⟨BinaryTree.nil, by simp⟩, Fin.elim0)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

def imperfectColumnCount (perfect : Finset (Fin n)) : ℕ :=
  ((columnPositionEntries perfect).filter (fun p => !p.2)).length

def ShortColumnGeometry (label : Fin n → α) (hn : 0 < n)
    (coefficient : ℕ → ℝ) (perfect : Finset (Fin n)) (s : ℕ) : Prop :=
  ∀ start len, start + len ≤ n → len ≤ s →
      (∀ t ∈ intervalPositions (start, len), columnNatPerfect perfect t = true) →
      (∀ i j k : Fin (blockLabelList (columnNatLabel label hn) start len).length,
        i ≤ j → j ≤ k →
        (blockLabelList (columnNatLabel label hn) start len).get i =
          (blockLabelList (columnNatLabel label hn) start len).get k →
        (blockLabelList (columnNatLabel label hn) start len).get j =
          (blockLabelList (columnNatLabel label hn) start len).get i) ∧
      (∀ a b z, start ≤ a → a < b → b ≤ start + len →
        (∀ t ∈ Ico a b, columnNatLabel label hn t = z) →
        (∑ t ∈ Ico a b, coefficient t) ≠ 0)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit

noncomputable def finiteDNF {W : Type*} [Fintype W] (T : W → Type*) [∀ w, Fintype (T w)]
    {n : ℕ} (input : ∀ w, T w → Fin n) : AC0Circuit n :=
  .orGate (fun j : Fin (Fintype.card W) =>
    .andGate (fun k : Fin (Fintype.card (T ((Fintype.equivFin W).symm j))) =>
      .literal (input _ ((Fintype.equivFin _).symm k)) true))

end AC0Circuit

abbrev StepAlphabet (pairs : Finset (ℕ × ℕ)) := Bool × pairs

def decodeStep {pairs : Finset (ℕ × ℕ)} (a : StepAlphabet pairs) : SignedStep :=
  ⟨a.1, a.2.val.1, a.2.val.2⟩

abbrev BoundedStepWords (pairs : Finset (ℕ × ℕ)) (s : ℕ) :=
  (m : Fin (s + 1)) × (Fin m.val → StepAlphabet pairs)

def decodeStepWord {pairs : Finset (ℕ × ℕ)} {s : ℕ} (c : BoundedStepWords pairs s) :
    List SignedStep := List.ofFn (fun i => decodeStep (c.2 i))

abbrev ProhibitedCatalog (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :=
  {c : BoundedStepWords pairs s //
    MinimalWord (ForwardProhibited h s (fun d q => (d, q) ∈ pairs)) (decodeStepWord c)}

abbrev ProhibitedWordTests {pairs : Finset (ℕ × ℕ)} {h s : ℕ}
    (c : ProhibitedCatalog pairs h s) :=
  (i : Fin (decodeStepWord c.val).length) ×
    {p : ℕ // p ∈ (((decodeStepWord c.val).get i).padding *
      ((decodeStepWord c.val).get i).tuple).primeFactors}

abbrev ProhibitedInputs (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :=
  (c : ProhibitedCatalog pairs h s) × ProhibitedWordTests c

noncomputable def prohibitedInputIndex (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :
    ProhibitedInputs pairs h s ≃ Fin (Fintype.card (ProhibitedInputs pairs h s)) :=
  Fintype.equivFin _

noncomputable def prohibitedCircuit (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :
    AC0Circuit (Fintype.card (ProhibitedInputs pairs h s)) :=
  AC0Circuit.finiteDNF ProhibitedWordTests (fun c t => prohibitedInputIndex pairs h s ⟨c, t⟩)

noncomputable def prohibitedInputAt (pairs : Finset (ℕ × ℕ)) (h s : ℕ) (n : ℤ) :
    BooleanCube (Fintype.card (ProhibitedInputs pairs h s)) := fun j =>
  let t := (prohibitedInputIndex pairs h s).symm j
  decide ((t.2.2.val : ℤ) ∣ n + wordDisplacement h ((decodeStepWord t.1.val).take t.2.1.val))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def wordDivisorPrimeSupport (w : List SignedStep) : Finset ℕ :=
  w.toFinset.biUnion (fun a => (a.padding * a.tuple).primeFactors)

def ResiduePositiveWord {ι : Type*} (p : ι → ℕ) (h : ℕ) (w : List SignedStep)
    (r : ∀ i, ZMod (p i)) : Prop :=
  ∀ (k : Fin w.length) (i : ι),
    p i ∈ ((w.get k).padding * (w.get k).tuple).primeFactors →
      r i = -((wordDisplacement h (w.take k.val) : ℤ) : ZMod (p i))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def paddingPrimeSupport {R : ℕ} (q : Fin R → ℕ) : Finset ℕ :=
  univ.biUnion (fun i => (q i).primeFactors)

def PaddingResidueEvent {R B : ℕ} (Q : Finset ℕ) (q : Fin R → ℕ)
    (offset : Fin R → ℤ) (y : Q → Fin B) : Prop :=
  ∀ (i : Fin R) (p : Q), p.val ∈ (q i).primeFactors →
    ((y p).val : ZMod p.val) = -((offset i : ℤ) : ZMod p.val)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def paddingResidueAvailable (Q : Finset ℕ) (B : ℕ)
    (n : ℤ) (z : Q → Fin B) (p : Q) : Bool :=
  decide ((p.val : ℤ) ∣ (z p).val + n)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def paddingBinIndices (L η : ℝ) : Finset ℤ :=
  Icc 0 ⌊100 * L / η⌋

def PaddingPairEligible (L η : ℝ) (d q : ℕ) : Prop :=
  (q.primeFactors.card : ℝ) ≤ 100 * Real.log L ∧
    paddingBin η 0 (Real.log (d * q : ℕ)) ∈ paddingBinIndices L η

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def paddingPairHarmonicMass (Q : Finset ℕ) (L η : ℝ) (d : ℕ) : ℝ :=
  ∑ q ∈ retainedPrimeDivisors Q,
    if PaddingPairEligible L η d q then
      (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) else 0

noncomputable def totalPaddingBinMass (D Q : Finset ℕ) (L η : ℝ) : ℝ :=
  ∑ j ∈ paddingBinIndices L η, ∑ d ∈ D, ∑ q ∈ retainedPrimeDivisors Q,
    if (q.primeFactors.card : ℝ) ≤ 100 * Real.log L ∧
        (j : ℝ) * η ≤ Real.log (d * q : ℕ) ∧
        Real.log (d * q : ℕ) < ((j : ℝ) + 1) * η
    then (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def AttachedResiduePositiveWord {ι : Type*} (p : ι → ℕ) (h : ℕ)
    (w : List SignedStep) (attachment : ℤ) (B : ℕ) (x : ι → Fin B) : Prop :=
  ∀ (k : Fin w.length) (i : ι),
    p i ∈ ((w.get k).padding * (w.get k).tuple).primeFactors →
      ((x i).val : ZMod (p i)) =
        -((attachment + wordDisplacement h (w.take k.val) : ℤ) : ZMod (p i))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace CrudeWordCode

variable {R N : ℕ}

noncomputable def badReciprocalCost (c : CrudeWordCode R N R) (VP VQ : ℝ) : ℝ :=
  (Fintype.card c.tupleClasses ^ 2 * (R + 1) ^ 2 : ℕ) *
    VP ^ Fintype.card c.tupleClasses *
    VQ ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}

end CrudeWordCode

noncomputable def badCatalogCost (s T : ℕ) (VP VQ : ℝ) : ℝ :=
  ∑ R : Fin (s + 1), ∑ N : Fin (T + 1),
    ∑ c : CrudeWordCode R.val N.val R.val, c.badReciprocalCost VP VQ

open _root_.Filter

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

abbrev CrudeColumnPatternCode (J R : ℕ) := Fin J → Fin R → Fin R

def decodeCrudeColumnPattern {J R : ℕ} (c : CrudeColumnPatternCode J R)
    (j : Fin J) (i k : Fin R) : Bool := decide (c j i = c j k)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def freshWitnessCoordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (p : ι → ℕ) (S : Finset ι) (word : Fin n → List SignedStep) : Finset ι :=
  univ.filter (fun i => i ∉ S ∧ ∃ j, p i ∈ wordDivisorPrimeSupport (word j))

def RetainedWitnessTests {ι : Type*} {n : ℕ} [DecidableEq ι]
    (p : ι → ℕ) (S : Finset ι) (h B : ℕ) (word : Fin n → List SignedStep)
    (attachment : Fin n → ℤ) (x : ι → Fin B) : Prop :=
  ∀ i, i ∉ S → ∀ (j : Fin n) (k : Fin (word j).length),
    p i ∈ (((word j).get k).padding * ((word j).get k).tuple).primeFactors →
      ((x i).val : ZMod (p i)) =
        -((attachment j + wordDisplacement h ((word j).take k.val) : ℤ) : ZMod (p i))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def cyclicIndex (R : ℕ) (hR : 0 < R) (t : ℕ) : Fin R :=
  ⟨t % R, Nat.mod_lt _ hR⟩

def columnTuple {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R) : ℕ := ∏ j, (w j i).val

def columnTupleWord {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ) :
    List SignedStep := List.ofFn (fun i => ⟨forward i, columnTuple w i, padding i⟩)

noncomputable def tupleColumnPattern {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) : ColumnWordPattern (P j) where
  length := R
  label t := w j (cyclicIndex R hR t)
  forward t := forward (cyclicIndex R hR t)
  padding t := padding (cyclicIndex R hR t)
  otherColumns t := ∏ l ∈ univ.erase j, (w l (cyclicIndex R hR t)).val

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def retainedEdgeDeparture (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ) (t : SignedStep) (n : ℤ) : ℝ :=
  if t.padding ∈ Q ∧ eligible t t.padding ∧ (t.padding : ℤ) ∣ n ∧
      integerEdgeKeep Q u (eligible t) g L K (extra t) n ∧
      integerEdgeKeep Q u (eligible t) g L K (extra t) (n + t.displacement h)
  then L * u t.padding / (g n) ^ 2 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def ColumnLowRank {α : Type*} [Fintype α] [DecidableEq α]
    (w : ColumnWordPattern α) (hn : 0 < w.length) (h : ℕ)
    (perfect : Finset (Fin w.length)) (cut : Fin w.length) (r : ℕ) : Prop :=
  ∀ S : Finset (EqualLabelPairs (fun i : perfect.erase cut => w.label i.val.val)), S.card = r →
    ¬LinearIndependent ℝ (pairFamily (labelPairVectors
      (fun i : perfect.erase cut => w.label i.val.val)
      (fun i => formalDeparture (columnNatLabel (fun i : Fin w.length => w.label i.val) hn)
        (fun t => (w.coefficient h t : ℝ)) i.val.val)) S)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def wordPosition (R : ℕ) (hR : 0 < R) (t : ℕ) : Fin R :=
  ⟨t % R, Nat.mod_lt _ hR⟩

noncomputable def resampledTupleColumnPattern {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) :
    ColumnWordPattern (patternClasses (w j)) where
  length := R
  label t := patternCoordinate (w j) (wordPosition R hR t)
  forward t := forward (wordPosition R hR t)
  padding t := padding (wordPosition R hR t)
  otherColumns t := ∏ l ∈ univ.erase j, (w l (wordPosition R hR t)).val

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def perfectRows {ι : Type*} [Fintype ι] [DecidableEq ι] {R J : ℕ}
    (label : Fin R × Fin J → ι) (U : Finset (Fin R × Fin J)) : Finset (Fin R) :=
  ((singletonSlots label ∪ U).image Prod.fst)ᶜ

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma selectedPrimeValues_injective {J : ℕ} {P : Fin J → Finset ℕ}
    (x : (j : Fin J) → P j)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (fun j => (x j).val) := by
  intro j l he
  change (x j).val = (x l).val at he
  by_contra hne
  have hj : (x j).val ∈ P l := by rw [he]; exact (x l).property
  exact (disjoint_left.mp (hdisjoint j l (Ne.symm hne))) (x j).property hj

lemma columnTuple_squarefree {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Squarefree (columnTuple w i) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro j _ l _ hne
    change IsRelPrime (w j i).val (w l i).val
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hprime j _ (w j i).property)
      (hprime l _ (w l i).property)).mpr
      (fun he => hne (selectedPrimeValues_injective (fun j => w j i) hdisjoint he))
  · intro j _
    exact (hprime j _ (w j i).property).squarefree

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def primeTupleDivisors {J : ℕ} (P : Fin J → Finset ℕ) : Finset ℕ :=
  univ.image (fun x : (j : Fin J) → P j => ∏ j, (x j).val)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def primeTuplePool {J : ℕ} (P : Fin J → Finset ℕ) : Finset ℕ :=
  univ.biUnion P

lemma mem_primeTuplePool {J : ℕ} {P : Fin J → Finset ℕ} {p : ℕ} :
    p ∈ primeTuplePool P ↔ ∃ j, p ∈ P j := by
  simp only [primeTuplePool, mem_biUnion, mem_univ, true_and]

lemma primeTuplePool_prime {J : ℕ} {P : Fin J → Finset ℕ}
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime) {p : ℕ} (hp : p ∈ primeTuplePool P) :
    p.Prime := by
  obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hp
  exact hprime j p hj

lemma primeTupleDivisors_arithmetic {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    {d : ℕ} (hd : d ∈ primeTupleDivisors P) :
    Squarefree d ∧ d.primeFactors.card = J ∧ d.primeFactors ⊆ primeTuplePool P := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hd
  have hf : (∏ j, (x j).val).primeFactors = univ.image (fun j => (x j).val) :=
    familyTuple_primeFactors (fun j (p : P j) => p.val)
      (fun j p => hprime j _ p.property) x (selectedPrimeValues_injective x hdisjoint)
  refine ⟨?_, ?_, ?_⟩
  · exact columnTuple_squarefree (fun j (_ : Fin 1) => x j) 0 hprime hdisjoint
  · rw [hf, card_image_of_injective _ (selectedPrimeValues_injective x hdisjoint),
      card_univ, Fintype.card_fin]
  · rw [hf]
    intro p hp
    obtain ⟨j, _, rfl⟩ := mem_image.mp hp
    exact mem_primeTuplePool.mpr ⟨j, (x j).property⟩

lemma retainedPrimeDivisor_squarefree (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    {q : ℕ} (hq : q ∈ retainedPrimeDivisors Q) : Squarefree q := by
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hq
  have hprime (p : ℕ) (hp : p ∈ U) := hQ p ((mem_powerset.mp hU) hp)
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp r hr hne
    change IsRelPrime p r
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hprime p hp) (hprime r hr)).mpr hne
  · intro p hp
    exact (hprime p hp).squarefree

noncomputable def boundedPaddingDivisors (Q : Finset ℕ) (M : ℕ) : Finset ℕ :=
  (retainedPrimeDivisors Q).filter (fun q => q.primeFactors.card ≤ M)

noncomputable def primeFamilyPairs {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (M : ℕ) (eligible : ℕ → ℕ → Prop) : Finset (ℕ × ℕ) :=
  ((primeTupleDivisors P).product (boundedPaddingDivisors Q M)).filter
    (fun dq => eligible dq.1 dq.2)

lemma mem_primeFamilyPairs {J : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    {M : ℕ} {eligible : ℕ → ℕ → Prop} {dq : ℕ × ℕ} :
    dq ∈ primeFamilyPairs P Q M eligible ↔
      dq.1 ∈ primeTupleDivisors P ∧ dq.2 ∈ retainedPrimeDivisors Q ∧
        dq.2.primeFactors.card ≤ M ∧ eligible dq.1 dq.2 := by
  rcases dq with ⟨d, q⟩
  simp only [primeFamilyPairs, boundedPaddingDivisors, Finset.product_eq_sprod,
    mem_filter, Finset.mem_product]
  tauto

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def primeTupleSlice {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J)) :
    Finset ℕ := univ.image (fun x : (i : I) → P i => ∏ i, (x i).val)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def tuplePartialProfile {J : ℕ} (P : Fin J → Finset ℕ)
    (I : Finset (Fin J)) (q : ℕ) (eligible : ℕ → ℕ → Prop)
    (l : ℕ) [NeZero l] (b : ZMod l) (h n : ℕ) : ℂ :=
  ∑ x : (j : Fin J) → P j,
    if eligible (∏ j, (x j).val) q then
      ((∏ i : I, (x i).val : ℕ) : ℂ)⁻¹ *
        (natDivisibilityIndicator (q * ∏ j : {j // j ∉ I}, (x j).val) n *
          (progressionSequence liouville l (b * ((q * ∏ j, (x j).val : ℕ) : ZMod l)) n *
            liouville (n + h * (q * ∏ j, (x j).val))))
    else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def tupleCenteredProfile {J : ℕ} (P : Fin J → Finset ℕ)
    (q : ℕ) (eligible : ℕ → ℕ → Prop) (l : ℕ) [NeZero l]
    (b : ZMod l) (h n : ℕ) : ℂ :=
  ∑ x : (j : Fin J) → P j,
    if eligible (∏ j, (x j).val) q then
      natDivisibilityIndicator q n *
        (centeredTuple (∏ j, (x j).val).primeFactors (n : ℤ) : ℂ) *
        (progressionSequence liouville l (b * ((q * ∏ j, (x j).val : ℕ) : ZMod l)) n *
          liouville (n + h * (q * ∏ j, (x j).val)))
    else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def tupleComplexPartialProfile {J : ℕ} (P : Fin J → Finset ℕ)
    (I : Finset (Fin J)) (q : ℕ) (eligible : ℕ → ℕ → Prop)
    (F G : ℕ → ℂ) (h n : ℕ) : ℂ :=
  ∑ x : (j : Fin J) → P j,
    if eligible (∏ j, (x j).val) q then
      ((∏ i : I, (x i).val : ℕ) : ℂ)⁻¹ *
        (natDivisibilityIndicator (q * ∏ j : {j // j ∉ I}, (x j).val) n *
          (F n * G (n + h * (q * ∏ j, (x j).val))))
    else 0

noncomputable def tupleComplexCenteredProfile {J : ℕ} (P : Fin J → Finset ℕ)
    (q : ℕ) (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h n : ℕ) : ℂ :=
  ∑ x : (j : Fin J) → P j,
    if eligible (∏ j, (x j).val) q then
      natDivisibilityIndicator q n *
        (centeredTuple (∏ j, (x j).val).primeFactors (n : ℤ) : ℂ) *
        (F n * G (n + h * (q * ∏ j, (x j).val)))
    else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def complexRoughProfile (F G : ℕ → ℂ) (Z : Finset ℕ) (h n : ℕ) : ℂ :=
  ∑ z ∈ Z, (z : ℂ)⁻¹ * (F n * G (n + h * z))

noncomputable def complexPartialProfile (F G : ℕ → ℂ) (u : ℕ) (Z : Finset ℕ)
    (h n : ℕ) : ℂ :=
  natDivisibilityIndicator u n * ∑ z ∈ Z, (z : ℂ)⁻¹ * (F n * G (n + h * u * z))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def tuplePrimeSupport {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) : Finset ℕ :=
  univ.biUnion (fun j => (univ.image (w j)).image Subtype.val)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Filter

def witnessRecordBudget (D J M n : ℕ) : ℕ := D * (J + M) + D + n

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

abbrev PrimeWordEncoding (R T : ℕ) (P Q : Finset ℕ) :=
  (n : Fin (T + 1)) × (c : CrudeWordCode R n.val R) ×
    (c.tupleClasses → P) × ({z : c.usedClasses // z ∉ c.tupleClasses} → Q)

namespace PrimeWordEncoding

variable {R T : ℕ} {P Q : Finset ℕ}

def decode (e : PrimeWordEncoding R T P Q) : List SignedStep :=
  e.2.1.numericalWord (joinCoordinates e.2.1.tupleClasses
    (fun z => (e.2.2.1 z).val) (fun z => (e.2.2.2 z).val))

noncomputable def weight (e : PrimeWordEncoding R T P Q) : ℝ :=
  ∏ z : e.2.1.usedClasses, ((joinCoordinates e.2.1.tupleClasses
    (fun z => (e.2.2.1 z).val) (fun z => (e.2.2.2 z).val) z : ℕ) : ℝ)⁻¹

end PrimeWordEncoding

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def PrimeWordEncoding.Witnesses {R T : ℕ} {P Q : Finset ℕ}
    (e : PrimeWordEncoding R T P Q) (n mainLength : ℕ) (start len : Fin n → ℕ)
    (h s J : ℕ) (supply : ℕ → ℕ → Prop) : Prop :=
  e.2.1.KindConsistent ∧ e.2.1.RowInjective ∧
    NumericalWitnessEvent (e.decode.take mainLength)
      (fun i => (e.decode.drop (start i)).take (len i))
      (fun z => (e.2.2.1 z).val) h s J supply

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def paddingOnlyWord {R : ℕ} (q : Fin R → ℕ) : Fin R → SignedStep :=
  fun i => ⟨false, 1, q i⟩

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def largeUnlitCatalog {R J : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (F : Finset (Fin R → SignedStep))
    (label : (Fin R → SignedStep) → Fin R × Fin J → ι) (L : ℝ) :
    Finset (Σ _w : Fin R → SignedStep, Finset (Fin R × Fin J)) :=
  F.sigma (fun w => (nonsingletonSlots (label w)).powerset.filter
    (fun U => L ^ (1 / 50 : ℝ) < (U.card : ℝ)))

noncomputable def designationExtra {τ ι : Type*} [Fintype τ] [Fintype ι] [DecidableEq ι]
    (label : τ → ι) (U : Finset τ) : ℕ :=
  ∑ a ∈ nonsingletonLabels label,
    extraReciprocalExponent (litOccurrences label (designationLit U) a).card
      (unlitOccurrences label (designationLit U) a).card

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def columnNatCode {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (a : ColumnPrimeAssignment J R P × (Fin R → Q)) :
    ColumnPrimeAssignment J R P × (Fin R → ℕ) :=
  (a.1, fun i => (a.2 i).val)

def columnStepCode {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (forward : Fin R → Bool) (a : ColumnPrimeAssignment J R P × (Fin R → Q)) :
    Fin R → SignedStep :=
  fun i => ⟨forward i, columnTuple a.1 i, (a.2 i).val⟩

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def closedColumnRows {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) :
    Fin (k + k) → ((j : Fin J) → P j) × (Q × Bool) :=
  Fin.append a (fun i => ((b i.rev).1, (b i.rev).2.1, !(b i.rev).2.2))

def closedColumnAssignment {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) :
    ColumnPrimeAssignment J (k + k) P :=
  fun j i => (closedColumnRows Q a b i).1 j

def closedColumnPadding {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) : Fin (k + k) → Q :=
  fun i => (closedColumnRows Q a b i).2.1

def closedColumnForward {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) : Fin (k + k) → Bool :=
  fun i => (closedColumnRows Q a b i).2.2

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

def closedTraceEncoding {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (p : (Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool))) :
    (Fin (2 * k) → Bool) × (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :=
  let castIndex : Fin (2 * k) → Fin (k + k) := Fin.cast (by omega)
  (fun i => closedColumnForward Q p.1 p.2 (castIndex i),
    (fun j i => closedColumnAssignment Q p.1 p.2 j (castIndex i),
      fun i => closedColumnPadding Q p.1 p.2 (castIndex i)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def closedTraceFiber {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (F : Finset ((Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool)))) (forward : Fin (2 * k) → Bool) :
    Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :=
  (F.filter (fun p => (closedTraceEncoding Q p).1 = forward)).image
    (fun p => (closedTraceEncoding Q p).2)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace PrimeWordEncoding

variable {R T : ℕ} {P Q : Finset ℕ}

def Prohibited (e : PrimeWordEncoding R T P Q) (h s J : ℕ)
    (supply : ℕ → ℕ → Prop) : Prop :=
  e.2.1.KindConsistent ∧ e.2.1.RowInjective ∧
  Function.Injective (fun z => (e.2.2.1 z).val) ∧
  ForwardProhibited h s supply e.decode ∧
  (∀ a ∈ e.decode, Squarefree a.tuple) ∧
  (∀ a ∈ e.decode, a.tuple.primeFactors.card = J) ∧
  (∀ p j, TuplePrimeAt e.decode p j → ¬p ∣ h ∧ ∀ a ∈ e.decode, ¬p ∣ a.padding)

end PrimeWordEncoding

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def witnessCatalogCost (R T n M : ℕ) (VP VQ : ℝ) : ℝ :=
  ∑ t : Fin (T + 1), ∑ c : CrudeWordCode R t.val R,
    (Fintype.card (WitnessSystemData n M c.tupleClasses) : ℝ) *
      VP ^ Fintype.card c.tupleClasses *
      VQ ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

abbrev WitnessSegmentation (n R : ℕ) :=
  Fin (R + 1) × (Fin n → Fin (R + 1)) × (Fin n → Fin (R + 1))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

def recordedWitnessWord {n : ℕ} (main : List SignedStep) (word : Fin n → List SignedStep) :
    List SignedStep := main ++ (List.ofFn word).flatten

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

abbrev WitnessRecord (n R : ℕ) :=
  WitnessSegmentation n R × (Fin n → Fin (R + 1))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def WitnessRecord.Realizes {R T n : ℕ} {P Q : Finset ℕ}
    (d : WitnessRecord n R) (e : PrimeWordEncoding R T P Q) (main : List SignedStep) : Prop :=
  e.decode.take d.1.1.val = main ∧
    e.decode = recordedWitnessWord main
      (fun i => (e.decode.drop (d.1.2.1 i).val).take (d.1.2.2 i).val) ∧
    e.weight = ∏ q ∈ wordDivisorPrimeSupport e.decode, (q : ℝ)⁻¹

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def RetainedMainTests {ι : Type*} [DecidableEq ι] (p : ι → ℕ) (S : Finset ι)
    (h B : ℕ) (main : List SignedStep) (x : ι → Fin B) : Prop :=
  ∀ i, i ∉ S → ∀ k : Fin main.length,
    p i ∈ ((main.get k).padding * (main.get k).tuple).primeFactors →
      ((x i).val : ZMod (p i)) = -((wordDisplacement h (main.take k.val) : ℤ) : ZMod (p i))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def EncodedPaddingWitnessEvent {R T n : ℕ} {P Q : Finset ℕ} {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (d : WitnessRecord n R) (e : PrimeWordEncoding R T P Q)
    (main : List SignedStep) (p : ι → ℕ) (B h s J : ℕ)
    (supply : ℕ → ℕ → Prop) (x : ι → Fin B) : Prop :=
  e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
      h s J supply ∧ d.Realizes e main ∧ RetainedMainTests p S h B main x ∧
    ∃ y : ι → Fin B, (∀ i, i ∉ S → y i = x i) ∧
      ∀ j, AttachedResiduePositiveWord p h
        ((e.decode.drop (d.1.2.1 j).val).take (d.1.2.2 j).val)
        (wordDisplacement h (main.take (d.2 j).val)) B y

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def MainPaddingTests {ι : Type*} (p : ι → ℕ) (h B : ℕ)
    (main : List SignedStep) (x : ι → Fin B) : Prop :=
  ∀ (k : Fin main.length) (i : ι), p i ∈ (main.get k).padding.primeFactors →
    ((x i).val : ZMod (p i)) = -((wordDisplacement h (main.take k.val) : ℤ) : ZMod (p i))

noncomputable def paddingWeightedFunction {ι : Type*} (p : ι → ℕ)
    (h B : ℕ) (main : List SignedStep) (R : (ι → Fin B) → ℝ) (x : ι → Fin B) : ℝ :=
  if MainPaddingTests p h B main x then R x else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def centeredWordEnvelope {ι τ : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] {A : Type*} [Fintype A] [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base : ι → A)
    (R G : (ι → A) → ℝ) (x : ι → A) : ℝ :=
  ∑ U ∈ (nonsingletonSlots label).powerset,
    if LitConsistent (nonsingletonSlots label \ U) label target then
      R x * |selectedMixedDifference (singletonLabels label)
        (singletonTarget label target base)
        (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
          (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x|
    else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def WitnessStepAdmissible (P Q : Finset ℕ) (J M : ℕ) (t : SignedStep) : Prop :=
  Squarefree t.tuple ∧ Squarefree t.padding ∧
    t.tuple.primeFactors.card ≤ J ∧ t.padding.primeFactors.card ≤ M ∧
    t.tuple.primeFactors ⊆ P ∧ t.padding.primeFactors ⊆ Q

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

structure ProhibitedPrimeFamily (h J M : ℕ) where
  P : Finset ℕ
  Q : Finset ℕ
  pairs : Finset (ℕ × ℕ)
  primeP : ∀ p ∈ P, p.Prime
  primeQ : ∀ p ∈ Q, p.Prime
  disjoint : Disjoint P Q
  excluded : ∀ p ∈ P, ¬p ∣ h
  tuple_squarefree : ∀ dq ∈ pairs, Squarefree dq.1
  padding_squarefree : ∀ dq ∈ pairs, Squarefree dq.2
  tuple_card : ∀ dq ∈ pairs, dq.1.primeFactors.card = J
  padding_card : ∀ dq ∈ pairs, dq.2.primeFactors.card ≤ M
  tuple_pool : ∀ dq ∈ pairs, dq.1.primeFactors ⊆ P
  padding_pool : ∀ dq ∈ pairs, dq.2.primeFactors ⊆ Q

namespace ProhibitedPrimeFamily

variable {h J M : ℕ} (F : ProhibitedPrimeFamily h J M)

lemma prime (p : ↥(F.P ∪ F.Q)) : p.val.Prime := by
  rcases mem_union.mp p.property with hp | hp
  · exact F.primeP _ hp
  · exact F.primeQ _ hp

lemma support_subset (s : ℕ) (c : ProhibitedCatalog F.pairs h s) :
    wordDivisorPrimeSupport (decodeStepWord c.val) ⊆ F.P ∪ F.Q := by
  intro p hp
  obtain ⟨a, ha, hpa⟩ := mem_biUnion.mp hp
  have hdq := c.property.1.2.2.1 a (List.mem_toFinset.mp ha)
  rw [Nat.primeFactors_mul (F.padding_squarefree _ hdq).ne_zero
    (F.tuple_squarefree _ hdq).ne_zero, mem_union] at hpa
  rcases hpa with hpa | hpa
  · exact mem_union_right _ (F.padding_pool _ hdq hpa)
  · exact mem_union_left _ (F.tuple_pool _ hdq hpa)

noncomputable def residueLaw (B : ℕ) (hB : ∀ p ∈ F.P ∪ F.Q, p ≤ B) :
    FiniteLaw (↥(F.P ∪ F.Q) → Fin B) :=
  FiniteLaw.independent (fun p => uniformResidueLaw B p.val (F.prime p).pos (hB _ p.property))

def deletedEvent (s B : ℕ) (x : ↥(F.P ∪ F.Q) → Fin B) : Prop :=
  ∃ c : ProhibitedCatalog F.pairs h s,
    ResiduePositiveWord (fun p : ↥(F.P ∪ F.Q) => p.val) h (decodeStepWord c.val)
      (fun p => ((x p).val : ZMod p.val))

end ProhibitedPrimeFamily

open _root_.Filter

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def centeredPrimeBands (E : Finset ℕ) (A W : ℝ) (J : ℕ)
    (j : Fin J) : Finset ℕ := centeredPrimeSupply E A W j.val

noncomputable def centeredPrimePool (E : Finset ℕ) (A W : ℝ) (J : ℕ) : Finset ℕ :=
  primeTuplePool (centeredPrimeBands E A W J)

lemma centeredPrimeBands_prime (E : Finset ℕ) (A W : ℝ) (J : ℕ)
    (j : Fin J) (p : ℕ) (hp : p ∈ centeredPrimeBands E A W J j) : p.Prime :=
  (centeredPrimeSupply_mem hp).1

lemma centeredPrimeBands_disjoint (E : Finset ℕ) (A W : ℝ) (J : ℕ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) (j l : Fin J) (hne : l ≠ j) :
    Disjoint (centeredPrimeBands E A W J j) (centeredPrimeBands E A W J l) :=
  centeredPrimeSupply_pairwise_disjoint E A W hA hW
    (fun he => hne (Fin.ext he.symm))

lemma centeredPrimePool_disjoint_padding (E : Finset ℕ) (A W L : ℝ) (J : ℕ) :
    Disjoint (centeredPrimePool E A W J) (paddingPrimeSupply E L) := by
  apply disjoint_left.mpr
  intro p hp hq
  obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hp
  exact (disjoint_left.mp (centered_padding_disjoint E A W L j.val)) hj hq

noncomputable def actualProhibitedPrimeFamily (h J M : ℕ) (E : Finset ℕ)
    (A W L : ℝ) (eligible : ℕ → ℕ → Prop)
    (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) : ProhibitedPrimeFamily h J M where
  P := centeredPrimePool E A W J
  Q := paddingPrimeSupply E L
  pairs := primeFamilyPairs (centeredPrimeBands E A W J) (paddingPrimeSupply E L) M eligible
  primeP p hp := primeTuplePool_prime (centeredPrimeBands_prime E A W J) hp
  primeQ _ hp := paddingPrimeSupply_prime hp
  disjoint := centeredPrimePool_disjoint_padding E A W L J
  excluded p hp := by
    obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hp
    intro hph
    have hs := centeredPrimeSupply_mem hj
    exact hs.2.2.1 (hE p hs.1 hph)
  tuple_squarefree dq hdq :=
    (primeTupleDivisors_arithmetic _ (centeredPrimeBands_prime E A W J)
      (centeredPrimeBands_disjoint E A W J hA hW) (mem_primeFamilyPairs.mp hdq).1).1
  padding_squarefree dq hdq :=
    retainedPrimeDivisor_squarefree _ (fun _ hp => paddingPrimeSupply_prime hp)
      (mem_primeFamilyPairs.mp hdq).2.1
  tuple_card dq hdq :=
    (primeTupleDivisors_arithmetic _ (centeredPrimeBands_prime E A W J)
      (centeredPrimeBands_disjoint E A W J hA hW) (mem_primeFamilyPairs.mp hdq).1).2.1
  padding_card dq hdq := (mem_primeFamilyPairs.mp hdq).2.2.1
  tuple_pool dq hdq :=
    (primeTupleDivisors_arithmetic _ (centeredPrimeBands_prime E A W J)
      (centeredPrimeBands_disjoint E A W J hA hW) (mem_primeFamilyPairs.mp hdq).1).2.2
  padding_pool dq hdq :=
    retainedPrimeDivisor_factors _ (fun _ hp => paddingPrimeSupply_prime hp)
      (mem_primeFamilyPairs.mp hdq).2.1

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BonferroniBlocks

open scoped _root_.BigOperators

noncomputable def alternatingChoose (m n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (m + 1), (-1 : ℝ) ^ r * n.choose r

noncomputable def hitSet (P : Finset ℕ) (hit : ℕ → Prop) : Finset ℕ := by
  classical
  exact P.filter hit

noncomputable def intersectionValue (T : Finset ℕ) (hit : ℕ → Prop) : ℝ := by
  classical
  exact if ∀ p ∈ T, hit p then 1 else 0

noncomputable def coefficientPolynomial (m : ℕ) (P : Finset ℕ) (hit : ℕ → Prop) : ℝ :=
  ∑ r ∈ Finset.range (m + 1), (-1 : ℝ) ^ r *
    ∑ T ∈ P.powersetCard r, intersectionValue T hit

noncomputable def survives (P : Finset ℕ) (hit : ℕ → Prop) : ℝ := by
  classical
  exact if ∀ p ∈ P, ¬ hit p then 1 else 0

noncomputable def blockUpper (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (hit : ℕ → Prop) : ℝ :=
  ∏ j ∈ B, coefficientPolynomial (2 * orders j) (blocks j) hit

noncomputable def blockCorrection (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (hit : ℕ → Prop) : ℝ :=
  ∑ j ∈ B,
    (coefficientPolynomial (2 * orders j) (blocks j) hit -
      coefficientPolynomial (2 * orders j + 1) (blocks j) hit) *
      ∏ i ∈ B.erase j, coefficientPolynomial (2 * orders i) (blocks i) hit

noncomputable def blockLower (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (hit : ℕ → Prop) : ℝ :=
  blockUpper B blocks orders hit - blockCorrection B blocks orders hit

noncomputable def intersectionMass {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hit : ℕ → α → Prop) (T : Finset ℕ) : ℝ :=
  ∑ x ∈ C, weight x * intersectionValue T (fun p => hit p x)

noncomputable def momentPolynomial (m : ℕ) (P : Finset ℕ) (M : Finset ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m + 1), (-1 : ℝ) ^ r * ∑ T ∈ P.powersetCard r, M T

noncomputable def intersectionRemainder {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hit : ℕ → α → Prop) (X : ℝ) (g : ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  intersectionMass C weight hit T - X * ∏ p ∈ T, g p

end NumberTheoryLean.BonferroniBlocks

end

end Erdos970

end OAI

end

section

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BonferroniDensity

open scoped _root_.BigOperators

noncomputable def elementarySum (P : Finset ℕ) (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ P.powersetCard k, ∏ p ∈ T, g p

noncomputable def densityPolynomial (m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m + 1), (-1 : ℝ) ^ r * elementarySum P g r

end NumberTheoryLean.BonferroniDensity

end

end Erdos970

end OAI

end

section

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DisjointBlockExpansion

open scoped _root_.BigOperators

noncomputable def blockChoices (B : Finset ℕ) (blocks : ℕ → Finset ℕ) :
    Finset (∀ j ∈ B, Finset ℕ) := by
  classical
  exact B.pi fun j => (blocks j).powerset

noncomputable def selectedUnion (B : Finset ℕ) (choice : ∀ j ∈ B, Finset ℕ) : Finset ℕ := by
  classical
  exact B.attach.biUnion fun j => choice j.1 j.2

def intersectionChoices (B : Finset ℕ) (blocks : ℕ → Finset ℕ) (T : Finset ℕ) :
    ∀ j ∈ B, Finset ℕ := fun j _ => T ∩ blocks j

def truncatedCoefficient (m : ℕ) (T : Finset ℕ) : ℝ :=
  if T.card ≤ m then (-1 : ℝ) ^ T.card else 0

def layerCoefficient (m : ℕ) (T : Finset ℕ) : ℝ :=
  if T.card = m then 1 else 0

noncomputable def globalCoefficient (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (localCoeff : ℕ → Finset ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  ∏ j ∈ B, localCoeff j (T ∩ blocks j)

noncomputable def upperCoefficient (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (T : Finset ℕ) : ℝ :=
  globalCoefficient B blocks (fun j => truncatedCoefficient (2 * orders j)) T

noncomputable def correctionCoefficient (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (j : ℕ) (T : Finset ℕ) : ℝ :=
  globalCoefficient B blocks
    (fun i => if i = j then layerCoefficient (2 * orders i + 1)
      else truncatedCoefficient (2 * orders i)) T

noncomputable def lowerCoefficient (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (T : Finset ℕ) : ℝ :=
  upperCoefficient B blocks orders T - ∑ j ∈ B, correctionCoefficient B blocks orders j T

end NumberTheoryLean.DisjointBlockExpansion

end

end Erdos970

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations.ProhibitedPrimeFamily

open _root_.Finset
open scoped _root_.Classical

theorem exists_residue_origin {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    ∃ n : ℤ, ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = ((x p).val : ZMod p.val) := by
  let (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩
  apply exists_common_integer_residue (fun p : ↥(data.P ∪ data.Q) => p.val)
  intro p q hpq
  exact (Nat.coprime_primes (data.prime p) (data.prime q)).mpr
    (fun he => hpq (Subtype.ext he))

noncomputable def residueOrigin {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (x : ↥(data.P ∪ data.Q) → Fin B) : ℤ :=
  (data.exists_residue_origin x).choose

noncomputable def residueValue {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (f : ℤ → ℝ) (x : ↥(data.P ∪ data.Q) → Fin B) : ℝ := f (data.residueOrigin x)

end TwoPointCorrelations.ProhibitedPrimeFamily

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

end FiniteLaw

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

def paddingCoordinate (p : data.Q) : ↥(data.P ∪ data.Q) :=
  ⟨p.val, mem_union_right _ p.property⟩

def paddingRestriction (x : ↥(data.P ∪ data.Q) → Fin B) : data.Q → Fin B :=
  fun p => x (data.paddingCoordinate p)

noncomputable def paddingResidueLaw (B : ℕ)
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) : FiniteLaw (data.Q → Fin B) :=
  FiniteLaw.independent (fun p : data.Q =>
    uniformResidueLaw B p.val (data.primeQ _ p.property).pos
      (hB _ (mem_union_right _ p.property)))

lemma exists_padding_residue_origin (x : data.Q → Fin B) :
    ∃ n : ℤ, ∀ p : data.Q, (n : ZMod p.val) = ((x p).val : ZMod p.val) := by
  let (p : data.Q) : NeZero p.val := ⟨(data.primeQ _ p.property).ne_zero⟩
  apply exists_common_integer_residue (fun p : data.Q => p.val)
  intro p q hpq
  exact (Nat.coprime_primes (data.primeQ _ p.property) (data.primeQ _ q.property)).mpr
    (fun he => hpq (Subtype.ext he))

noncomputable def paddingResidueOrigin (x : data.Q → Fin B) : ℤ :=
  (data.exists_padding_residue_origin x).choose

end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def translateResidue (B p : ℕ) [NeZero p] (hpB : p ≤ B)
    (c : ℤ) (x : Fin B) : Fin B :=
  ⟨((x.val : ZMod p) + (c : ZMod p)).val, (ZMod.val_lt _).trans_le hpB⟩

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def attachedCatalogAvoidance {h J M : ℕ}
    (F : ProhibitedPrimeFamily h J M) (s B D : ℕ) (main : List SignedStep)
    (x : ↥(F.P ∪ F.Q) → Fin B) : ℝ :=
  witnessAvoidance
    (fun a : Fin (D + 1) × ProhibitedCatalog F.pairs h s => fun z => decide
      (AttachedResiduePositiveWord (fun p : ↥(F.P ∪ F.Q) => p.val) h
        (decodeStepWord a.2.val) (wordDisplacement h (main.take (min a.1.val main.length))) B z)) x

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def tupleForcedTarget {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (t : Fin R × Fin J) : Fin B :=
  forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
    (wordDisplacement h (word.take t.1.val))

noncomputable def prohibitedWordDifference {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B) (U : Finset (Fin R × Fin J))
    (x : ↥(data.P ∪ data.Q) → Fin B) : ℝ :=
  selectedMixedDifference (singletonLabels label)
    (singletonTarget label (tupleForcedTarget data hB word label) base)
    (fun y => attachedCatalogAvoidance data s B D word
      (forceCoordinates ((nonsingletonSlots label \ U).image label)
        (litForcedTarget (nonsingletonSlots label \ U) label
          (tupleForcedTarget data hB word label) base) y)) x

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def prohibitedCenteredAverage {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (weight : (↥(data.P ∪ data.Q) → Fin B) → ℝ) : ℝ :=
  (data.residueLaw B hB).average (fun x => weight x * (∏ t,
    ((if ((label t).val : ℤ) ∣ (x (label t)).val + wordDisplacement h (word.take t.1.val)
      then (1 : ℝ) else 0) - ((label t).val : ℝ)⁻¹)) *
        attachedCatalogAvoidance data s B D word x)

noncomputable def prohibitedDesignatedTerm {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (↥(data.P ∪ data.Q) → Fin B) → ℝ) (U : Finset (Fin R × Fin J)) : ℝ :=
  if LitConsistent (nonsingletonSlots label \ U) label (tupleForcedTarget data hB word label) then
    designatedReciprocal (fun p : ↥(data.P ∪ data.Q) => p.val)
      (singletonLabels label) (nonsingletonSlots label \ U) U label *
        (data.residueLaw B hB).average
          (fun x => weight x * |prohibitedWordDifference data hB s D word label base U x|)
  else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def highRankTraceSlice {J R : ℕ} {P : Fin J → Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
    (label : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → Fin R × Fin J → ι)
    (forward : Fin R → Bool) (hR : 0 < R) (h r : ℕ) (cut : Fin R)
    (U : Finset (Fin R × Fin J)) (perfect : Finset (Fin R)) (j : Fin J) :=
  F.filter (fun a => U ⊆ nonsingletonSlots (label a) ∧ perfectRows (label a) U = perfect ∧
    ¬ColumnLowRank (tupleColumnPattern a.1 hR forward a.2 j) hR h perfect cut r)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def prohibitedWordKeepCircuit (pairs : Finset (ℕ × ℕ)) (h s : ℕ)
    {R n : ℕ} (index : Fin R → Fin (Fintype.card (ProhibitedInputs pairs h s)) → Fin n) :
    AC0Circuit n :=
  AC0Circuit.conjunction (fun r => ((prohibitedCircuit pairs h s).negate).relabel (index r))

lemma ProhibitedPrimeFamily.prohibited_input_mem {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ)
    (i : ProhibitedInputs data.pairs h s) : i.2.2.val ∈ data.P ∪ data.Q := by
  apply data.support_subset s i.1
  apply mem_biUnion.mpr
  refine ⟨(decodeStepWord i.1.val).get i.2.1, ?_, i.2.2.property⟩
  exact List.mem_toFinset.mpr (List.get_mem _ _)

noncomputable def ProhibitedPrimeFamily.prohibitedLiteral {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ)
    (i : Fin (Fintype.card (ProhibitedInputs data.pairs h s))) :
    ↥(data.P ∪ data.Q) × ℤ :=
  let v := (prohibitedInputIndex data.pairs h s).symm i
  (⟨v.2.2.val, data.prohibited_input_mem s v⟩,
    wordDisplacement h ((decodeStepWord v.1.val).take v.2.1.val))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def columnTupleAtNat {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : ℕ) : ℕ :=
  if hi : i < R then columnTuple w ⟨i, hi⟩ else 1

def columnForwardAtNat {R : ℕ} (forward : Fin R → Bool) (i : ℕ) : Bool :=
  if hi : i < R then forward ⟨i, hi⟩ else false

def actualColumnNext {J R : ℕ} {P : Fin J → Finset ℕ}
    (h : ℕ) (forward : Fin R → Bool) (w : ColumnPrimeAssignment J R P)
    (i : ℕ) (n : ℤ) (q : ℕ) : ℤ :=
  n + (SignedStep.mk (columnForwardAtNat forward i) (columnTupleAtNat w i) q).displacement h

noncomputable def columnCrudeCap {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (L : ℝ) (a : ColumnPrimeAssignment J R P × (Fin R → Q)) : ℝ :=
  ∏ i, L * crudePaddingWeight (a.2 i).val

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def actualPaddingDegree (Q : Finset ℕ) (n : ℤ) : ℕ :=
  (Q.filter (fun p : ℕ => (p : ℤ) ∣ n)).card

noncomputable def actualPaddingWeight (Q : Finset ℕ) (n : ℤ) : ℝ :=
  (5 : ℝ) ^ actualPaddingDegree Q n

noncomputable def actualPaddingVertex (Q : Finset ℕ) (n : ℤ) : ℝ :=
  Real.sqrt (actualPaddingWeight Q n)

noncomputable def actualPaddingCoefficient (q : ℕ) : ℝ :=
  (4 : ℝ) ^ q.primeFactors.card

noncomputable def actualPaddingDegreeCut (Q : Finset ℕ) (L : ℝ) (n : ℤ) : Prop :=
  (actualPaddingDegree Q n : ℝ) ≤ 400 * Real.log L

def actualPaddingBin (η c : ℝ) (j : ℤ) (q : ℕ) : Prop :=
  (j : ℝ) * η ≤ Real.log q + c ∧ Real.log q + c < ((j : ℝ) + 1) * η

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def numericalBinEligible (L η : ℝ) (j : ℤ) (d q : ℕ) : Prop :=
  0 < d ∧ 0 < q ∧ (q.primeFactors.card : ℝ) ≤ 100 * Real.log L ∧
    actualPaddingBin η (Real.log d) j q

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def numericalBinPairs (D R : Finset ℕ) (L η : ℝ) (j : ℤ) : Finset (ℕ × ℕ) :=
  (D ×ˢ R).filter (fun e => numericalBinEligible L η j e.1 e.2)

noncomputable def numericalBinHarmonicMass (D R : Finset ℕ) (L η : ℝ) (j : ℤ) : ℝ :=
  ∑ e ∈ numericalBinPairs D R L η j, actualPaddingCoefficient e.2 / (e.1 * e.2 : ℕ)

noncomputable def fullNumericalBin (D R : Finset ℕ) (L η : ℝ) (j : ℤ)
    (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ) (T : ℝ) : ℂ :=
  ∑ e ∈ numericalBinPairs D R L η j, (actualPaddingCoefficient e.2 : ℂ) *
    (positivePrefix (fullLiouvilleProfile l b (e.2 * e.1) h) ⌊T⌋₊ / (T : ℂ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def paddingActiveState {m : ℕ} (Q : Finset ℕ) (e : Fin m ≃ Q)
    (n : ℤ) : Finset (Fin m) :=
  activeState (fun i => decide (((e i).val : ℤ) ∣ n))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def primeStateTruncatedWeight {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (M : ℕ) (site : ℤ) (z : ∀ i, ZMod (s i)) : ℝ :=
  let S := activeState (fun i => decide (z i + (site : ZMod (s i)) = 0))
  if S.card ≤ M then (5 : ℝ) ^ S.card else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def paddingStateDensity {m : ℕ} (Qp Q : Finset ℕ) (e : Fin m ≃ Qp)
    (eligible : ℕ → Prop) (S : Finset (Fin m)) : ℝ :=
  (∑ q ∈ Q, if eligible q ∧ q.primeFactors ⊆ S.image (fun i => (e i).val)
    then actualPaddingCoefficient q else 0) / (5 : ℝ) ^ S.card

noncomputable def paddingStateKeep {m : ℕ} (Qp Q : Finset ℕ) (e : Fin m ≃ Qp)
    (eligible : ℕ → Prop) (L K : ℝ) (S : Finset (Fin m)) : Prop :=
  paddingStateDensity Qp Q e eligible S ≤ K / L ∧ (S.card : ℝ) ≤ 400 * Real.log L

noncomputable def paddingStateDeparture {m : ℕ} (Qp Q : Finset ℕ) (e : Fin m ≃ Qp)
    (eligible : SignedStep → ℕ → Prop) (L K : ℝ) (t : SignedStep)
    (S T : Finset (Fin m)) : ℝ :=
  if t.padding ∈ Q ∧ eligible t t.padding ∧
      t.padding.primeFactors ⊆ S.image (fun i => (e i).val) ∧
      paddingStateKeep Qp Q e (eligible t) L K S ∧
      paddingStateKeep Qp Q e (eligible t) L K T
    then L * actualPaddingCoefficient t.padding / (5 : ℝ) ^ S.card else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def primeSubsetIndex (U S : Finset ℕ) (hS : S ⊆ U) :
    Fin (Fintype.card S) → Fin (Fintype.card U) :=
  fun i => (Fintype.equivFin U)
    ⟨((Fintype.equivFin S).symm i).val, hS ((Fintype.equivFin S).symm i).property⟩

noncomputable def primeSiteBits (U : Finset ℕ) (n : ℤ) :
    BooleanCube (Fintype.card U) :=
  fun i => decide ((((Fintype.equivFin U).symm i).val : ℤ) ∣ n)

noncomputable def degreeDivisorCircuit {m n t : ℕ}
    (pindex : Fin n → Fin m) (qindex : Fin t → Fin m) (r : ℕ) : AC0Circuit m :=
  AC0Circuit.conjunction (fun b : Bool => if b then
    AC0Circuit.relabel pindex (degreeThresholdCircuit n r) else
    AC0Circuit.relabel qindex (degreeSubsetCircuit univ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def activePredicateCircuit (n M : ℕ) (E : Finset (Fin n) → Prop) :
    AC0Circuit n :=
  AC0Circuit.disjunction (fun S : (boundedActiveStates n M).filter E =>
    activeStateCircuit S.val)

noncomputable def stateDivisorCircuit {m n t : ℕ}
    (qindex : Fin n → Fin m) (dindex : Fin t → Fin m) (M : ℕ)
    (E : Finset (Fin n) → Prop) : AC0Circuit m :=
  AC0Circuit.conjunction (fun b : Bool => if b then
    AC0Circuit.relabel qindex (activePredicateCircuit n M E) else
    AC0Circuit.relabel dindex (degreeSubsetCircuit univ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def primeSelection (P S : Finset ℕ) (hSP : S ⊆ P) : Finset P :=
  S.attach.image (fun p => (⟨p.val, hSP p.property⟩ : P))

noncomputable def positivePrimeWeight (S : Finset ℕ) (n : ℤ) : ℝ :=
  ∏ p ∈ S, ((if (p : ℤ) ∣ n then 1 else 0) + 1 / (p : ℝ))

noncomputable def positivePrimeNormalizer (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, 2 / (p : ℝ)

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.NNReal _root_.ENNReal

noncomputable def primeRealEdgeMatrix {J : ℕ} {V : Type*} [Fintype V]
    (P : Fin J → Finset ℕ) (site : V → ℤ) (Q : Finset ℕ)
    (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (d : (j : Fin J) → P j) : Matrix V V ℝ :=
  fun i j => if gate (∏ k, (d k).val) i j then
    integerEdgeMatrix site Q u (eligible (∏ k, (d k).val)) g
      (centeredTuple (∏ k, (d k).val).primeFactors) L K
      (extra (∏ k, (d k).val)) h (∏ k, (d k).val) i j else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def positivePrimeTable {t : ℕ} (p : Fin t → ℕ) (r : ℕ)
    (bits : BooleanCube t) : ℝ :=
  (4 : ℝ) ^ r * ∏ i, ((if bits i then 1 else 0) + 1 / (p i : ℝ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

end FiniteLaw

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

def tupleRestriction (x : ↥(data.P ∪ data.Q) → Fin B) : data.P → Fin B :=
  fun p => x ⟨p.val, mem_union_left _ p.property⟩

noncomputable def tupleResidueLaw (B : ℕ)
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) : FiniteLaw (data.P → Fin B) :=
  FiniteLaw.independent (fun p : data.P =>
    uniformResidueLaw B p.val (data.primeP _ p.property).pos
      (hB _ (mem_union_left _ p.property)))

end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def paddingRejectedMass (Q D : Finset ℕ) (bins : Finset ℤ)
    (η c L K : ℝ) (n : ℤ) : ℝ :=
  (actualPaddingVertex Q n) ^ 2 *
    ∑ j ∈ bins, if ¬integerEdgeKeep D actualPaddingCoefficient (actualPaddingBin η c j)
      (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n then
        paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
          (actualPaddingVertex Q) n else 0

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def paddingRejectionAtom (Q S D : Finset ℕ) (eligible : ℕ → Prop)
    (L K : ℝ) (q : ℕ) (n : ℤ) : ℝ :=
  if eligible q then
    actualPaddingCoefficient q * positivePrimeWeight S n *
      if (q : ℤ) ∣ n ∧ ¬integerEdgeKeep D actualPaddingCoefficient eligible
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n then 1 else 0
  else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def positiveDegreeCost (P S : Finset ℕ) (W : ℝ) (q : ℕ) (n : ℤ) : ℝ :=
  actualPaddingCoefficient q * positivePrimeWeight S n *
    if (q : ℤ) ∣ n ∧ 6 * W * S.card < (actualPaddingDegree P n : ℝ) then 1 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI
noncomputable section

open scoped _root_.BigOperators _root_.ArithmeticFunction.Moebius
open _root_.Finset _root_.ArithmeticFunction

namespace Problem337.SelbergOptimal

def upperInverse (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ x ∈ (P / d).divisorsAntidiagonal, (μ x.1 : ℝ) * y (P / x.2)

def normalizer (s : BoundingSieve) (z : ℕ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, if d ≤ z then s.selbergTerms d else 0

def optimalDiagonal (s : BoundingSieve) (z d : ℕ) : ℝ :=
  if d ≤ z then (μ d : ℝ) * s.selbergTerms d / normalizer s z else 0

def optimalWeight (s : BoundingSieve) (z d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then
    upperInverse s.prodPrimes (optimalDiagonal s z) d / s.nu d else 0

def complementNormalizer (s : BoundingSieve) (z d : ℕ) : ℝ :=
  ∑ t ∈ (s.prodPrimes / d).divisors, if t ≤ z / d then s.selbergTerms t else 0

end Problem337.SelbergOptimal

end

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

end FiniteLaw

noncomputable def primeRowMajorant {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (n : ℤ) : ℝ :=
  actualPaddingWeight Q n *
    ∏ j : Fin J, ((actualPaddingDegree (P j) n : ℝ) + primeHarmonicMass (P j))

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {D V : Type*} [DecidableEq D] [Fintype D] [Fintype V]

def closedPairNumericalTest (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ)
    (h : ℕ) (gate : D → ℤ → ℤ → Prop) {k : ℕ} (x : D × ℤ)
    (p : (Fin k → D × (Q × Bool)) × (Fin k → D × (Q × Bool))) : Prop :=
  shiftWordEnd (integerShiftNext Q tuple h) x p.1 =
      shiftWordEnd (integerShiftNext Q tuple h) x p.2 ∧
    integerPathMask embed Q tuple h gate x p.1 ≠ 0 ∧
    integerPathMask embed Q tuple h gate x p.2 ≠ 0

noncomputable def actualClosedPairCatalog (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop) (pairs : Finset (ℕ × ℕ))
    (k : ℕ) (x : D × ℤ) :
    Finset ((Fin k → D × (Q × Bool)) × (Fin k → D × (Q × Bool))) :=
  univ.filter (fun p => closedPairNumericalTest embed Q tuple h gate x p ∧
    ∀ t ∈ integerClosedWordCode Q tuple p, (t.tuple, t.padding) ∈ pairs)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

def switchingDenominator (r : ℕ) : ℕ := 24 * (2 * r + 3) ^ 2

def switchingDegree (d r : ℕ) : ℕ := 8 * (r + 1) * switchingDenominator r ^ d

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open scoped _root_.Classical

def bravermanSamples (j : ℕ) : ℕ := 40 * (j + 1)
def bravermanBase (j : ℕ) : ℕ := bravermanSamples j * (j + 3)
def bravermanNormExponent (j : ℕ) : ℕ :=
  (2 * j + 3) * (2 * bravermanBase j + 2) ^ 22
def bravermanErrorExponent (j : ℕ) : ℕ := 20 * (j + 3)
def bravermanSwitches (j : ℕ) : ℕ :=
  2 * bravermanNormExponent j + bravermanErrorExponent j + j + 10
def bravermanDegree (j : ℕ) : ℕ :=
  2 * (bravermanBase j ^ 22 + switchingDegree 89 (bravermanSwitches j))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

def NatPolynomialGrowth (f : ℕ → ℕ) : Prop :=
  ∃ K C : ℕ, ∀ j, f j ≤ K * (j + 1) ^ C

namespace NatPolynomialGrowth

end NatPolynomialGrowth

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def paddingTestVector {V : Type*} (Q : Finset ℕ) (L : ℝ)
    (site : V → ℤ) (f : ℤ → ℂ) : EuclideanSpace ℂ V :=
  WithLp.toLp 2 (fun i => if actualPaddingDegreeCut Q L (site i) then
    (actualPaddingVertex Q (site i) : ℂ) * f (site i) else 0)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def enlargedBinStart (η : ℝ) (j : ℤ) (u : ℕ) : ℝ :=
  Real.exp (((j : ℝ) - 1) * η) / (u : ℝ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def tupleNonrawBin {J : ℕ} (P : Fin J → Finset ℕ)
    (R : Finset ℕ) (weight : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ) (T : ℝ) : ℂ :=
  ∑ q ∈ R, (weight q : ℂ) *
    ((positivePrefix (tupleCenteredProfile P q eligible l b h) ⌊T⌋₊ -
      positivePrefix (tuplePartialProfile P ∅ q eligible l b h) ⌊T⌋₊) / (T : ℂ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def actualColumnLabel {h J M R : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hP : ∀ j, P j ⊆ data.P)
    (w : ColumnPrimeAssignment J R P) (t : Fin R × Fin J) : ↥(data.P ∪ data.Q) :=
  ⟨(w t.2 t.1).val, mem_union_left _ (hP t.2 (w t.2 t.1).property)⟩

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def actualColumnWeight {h J M R B : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (forward : Fin R → Bool)
    (a : ColumnPrimeAssignment J R P × (Fin R → Q))
    (x : ↥(data.P ∪ data.Q) → Fin B) : ℝ :=
  data.residueValue (fun n => scalarWalkProduct h
    (retainedEdgeDeparture Q u (fun t => eligible t.tuple) g L K (fun t => extra t.tuple) h)
    n (columnTupleWord a.1 forward (fun i => (a.2 i).val))) x

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def canonicalTraceFamily (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) :
    ProhibitedPrimeFamily h (primeSupplyCount W L) ⌊100 * Real.log L⌋₊ :=
  actualProhibitedPrimeFamily h (primeSupplyCount W L) ⌊100 * Real.log L⌋₊ E
    (L ^ (199 / 200 : ℝ)) W L eligible
    (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hW) hE

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

def primeBlockEmbedding {J : ℕ} {P : Fin J → Finset ℕ} (N : ℕ) :
    (((j : Fin J) → P j) × Fin N) → (((j : Fin J) → P j) × ℤ) :=
  fun x => (x.1, (x.2.val : ℤ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def prohibitedCostCircuit {n m t : ℕ} (c : AC0Circuit n)
    (index : Fin n → Fin m) (qindex : Fin t → Fin m) : AC0Circuit m :=
  AC0Circuit.conjunction (fun b : Bool => if b then c.relabel index else
    (degreeSubsetCircuit univ).relabel qindex)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def prohibitedPositiveRow {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ) (D : Finset ℕ)
    (padding : ℕ → Finset ℕ) (n : ℤ) : ℝ :=
  ∑ d ∈ D, ∑ q ∈ padding d,
    actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
      if (q : ℤ) ∣ n ∧ ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then 1 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def positiveDeletionAtom (P Q R : Finset ℕ)
    (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ) (eligible : ℤ → ℕ → ℕ → Prop)
    (bad : ℤ → ℤ → Prop) (j : ℤ) (d q : ℕ) (n : ℤ) : ℝ :=
  if eligible j d q then
    actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
      if (q : ℤ) ∣ n ∧
        (¬integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
          (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∨
        6 * W * d.primeFactors.card < (actualPaddingDegree P n : ℝ) ∨ bad j n)
        then 1 else 0
  else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def shiftedProhibitedRow {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s : ℕ) (D : Finset ℕ) (padding : ℕ → Finset ℕ) (site : ℕ → ℕ → ℤ) (n : ℤ) : ℝ :=
  ∑ d ∈ D, ∑ q ∈ padding d, actualPaddingCoefficient q *
    positivePrimeWeight d.primeFactors (n + site d q) *
      if (q : ℤ) ∣ n + site d q ∧
        ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (n + site d q) then 1 else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def canonicalPairPadding (Q : Finset ℕ) (M : ℕ)
    (eligible : ℕ → ℕ → Prop) (d : ℕ) : Finset ℕ :=
  (boundedPaddingDivisors Q M).filter (eligible d)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def retainedDirectedMatrix {V : Type*} (site : V → ℤ)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop) (h d : ℕ)
    (gate : V → V → Prop) : Matrix V V ℂ := fun i j =>
  if gate i j then ∑ q ∈ Q,
    (retainedRealEdge Q u eligible g center L K extra keep h d q (site i) (site j) : ℂ)
  else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def retainedPrimeMatrix {J : ℕ} {V : Type*} [Fintype V]
    (P : Fin J → Finset ℕ) (site : V → ℤ) (Q : Finset ℕ)
    (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (keep : ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) : Matrix V V ℂ :=
  ∑ d : (j : Fin J) → P j, retainedDirectedMatrix site Q u
    (eligible (∏ j, (d j).val)) g (centeredTuple (∏ j, (d j).val).primeFactors)
    L K (extra (∏ j, (d j).val)) keep h (∏ j, (d j).val) (gate (∏ j, (d j).val))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def canonicalShiftedSourceDeletion (h : ℕ) (E : Finset ℕ) (W L η K : ℝ)
    (hL : 1 ≤ L) (hW : 1 ≤ W) (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (bins : Finset ℤ) (c : ℕ → ℝ) (eligible : ℤ → ℕ → ℕ → Prop)
    (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ) : ℝ :=
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  let bad := fun j n => ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ (canonicalTraceFamily h E W L (eligible j) hL hW hE).pairs) n
  ∑ j ∈ bins, ∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
    uniformAverage (fun x : Fin (N j) => positiveDeletionAtom (primeTuplePool P) Q R
      η c L K W eligible bad j d q ((a j + x.val : ℤ) + site j d q))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def centeredWordBits {R J : ℕ} (p : Fin R → Fin J → ℕ)
    (bits : BooleanCube (R * J)) : ℝ :=
  ∏ i : Fin R, ∏ j : Fin J,
    ((if bits (finProdFinEquiv (i, j)) then 1 else 0) - (p i j : ℝ)⁻¹)

noncomputable def actualWordCoefficient {R J m : ℕ}
    (Qp Q : Finset ℕ) (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop)
    (L K : ℝ) (step : Fin R → SignedStep) (p : Fin R → Fin J → ℕ)
    (S : Fin (R + 1) → Finset (Fin m)) (bits : BooleanCube (R * J)) : ℝ :=
  (∏ i : Fin R, paddingStateDeparture Qp Q e eligible L K (step i)
    (S i.castSucc) (S i.succ)) * centeredWordBits p bits

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

def wordVertexSite {R : ℕ} (h : ℕ) (step : Fin R → SignedStep) (n : ℤ)
    (i : Fin (R + 1)) : ℤ :=
  n + wordDisplacement h ((List.ofFn step).take i.val)

noncomputable def wordCenteredBits {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (h : ℕ) (step : Fin R → SignedStep) (n : ℤ) :
    BooleanCube (R * J) := fun k =>
  let ij := finProdFinEquiv.symm k
  decide (((w ij.2 ij.1).val : ℤ) ∣ wordVertexSite h step n ij.1.castSucc)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

abbrev ActualWordInput {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s R m : ℕ) :=
  (Fin (R + 1) × Fin m) ⊕
    ((Fin R × Fin J) ⊕ (Fin (R + 1) × Fin (Fintype.card (ProhibitedInputs data.pairs h s))))

noncomputable def actualWordInputEquiv {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s R m : ℕ) : ActualWordInput data s R m ≃ Fin (Fintype.card (ActualWordInput data s R m)) :=
  Fintype.equivFin _

noncomputable def actualWordLiterals {h J M R m : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s : ℕ) (e : Fin m ≃ data.Q) (step : Fin R → SignedStep)
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q)) :
    Fin (Fintype.card (ActualWordInput data s R m)) → ↥(data.P ∪ data.Q) × ℤ := fun i =>
  match (actualWordInputEquiv data s R m).symm i with
  | .inl (r, j) => (⟨(e j).val, mem_union_right _ (e j).property⟩, wordVertexSite h step 0 r)
  | .inr (.inl (r, j)) => (label (r, j), wordVertexSite h step 0 r.castSucc)
  | .inr (.inr (r, j)) =>
      ((data.prohibitedLiteral s j).1, wordVertexSite h step 0 r + (data.prohibitedLiteral s j).2)

noncomputable def actualWordQIndex {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s R m : ℕ) (r : Fin (R + 1)) (j : Fin m) :
    Fin (Fintype.card (ActualWordInput data s R m)) :=
  actualWordInputEquiv data s R m (.inl (r, j))

noncomputable def actualWordPIndex {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s R m : ℕ) (k : Fin (R * J)) : Fin (Fintype.card (ActualWordInput data s R m)) :=
  actualWordInputEquiv data s R m (.inr (.inl (finProdFinEquiv.symm k)))

noncomputable def actualWordBadIndex {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s R m : ℕ) (r : Fin (R + 1)) (j : Fin (Fintype.card (ProhibitedInputs data.pairs h s))) :
    Fin (Fintype.card (ActualWordInput data s R m)) :=
  actualWordInputEquiv data s R m (.inr (.inr (r, j)))

noncomputable def actualWordIntegerBits {h J M R m : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s : ℕ) (e : Fin m ≃ data.Q) (step : Fin R → SignedStep)
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q)) (n : ℤ) :
    BooleanCube (Fintype.card (ActualWordInput data s R m)) :=
  residueCircuitInputs (primeResidueModuli (data.P ∪ data.Q))
    (primeLiteralCoordinate (data.P ∪ data.Q) (actualWordLiterals data s e step label))
    (primeLiteralTest (data.P ∪ data.Q) (actualWordLiterals data s e step label))
    (fun j => (n : ZMod (primeResidueModuli (data.P ∪ data.Q) j)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def actualWordBoolean {h J M R m : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s : ℕ) (Q : Finset ℕ) (e : Fin m ≃ data.Q) (step : Fin R → SignedStep)
    (p : Fin R → Fin J → ℕ) (eligible : ℕ → ℕ → Prop) (L K : ℝ)
    (x : BooleanCube (Fintype.card (ActualWordInput data s R m))) : ℝ :=
  let S := fun r => activeState (fun i => x (actualWordQIndex data s R m r i))
  if (∀ r, (S r).card ≤ ⌊400 * Real.log L⌋₊) ∧
      (prohibitedWordKeepCircuit data.pairs h s (actualWordBadIndex data s R m)).eval x = true
    then actualWordCoefficient data.Q Q e (fun t => eligible t.tuple) L K step p S
      (fun k => x (actualWordPIndex data s R m k))
    else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def primeBlockCompression {J : ℕ} (P : Fin J → Finset ℕ)
    (M : ℕ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (c : ℤ) :
    EuclideanSpace ℂ (Fin M) →L[ℂ] EuclideanSpace ℂ (Fin M) :=
  let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
    (fun i : Fin M => (i.val : ℤ) + c) Q u eligible g L K extra h
    (fun d i j => gate d i.val j.val ∧ keep ((i.val : ℤ) + c) ∧ keep ((j.val : ℤ) + c))
  let proj := coordinateProjection (fun i : Fin M =>
    (actualPaddingDegree (univ.biUnion P) ((i.val : ℤ) + c) : ℝ) ≤ 6 * W * J)
  proj * (∑ d, B d) * proj

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def retainedPrimeEdge {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ) : ℂ :=
  if gate (∏ j, (e.1 j).val) n m ∧ keep n ∧ keep m then
    retainedLiouvilleEdge Q u (eligible (∏ j, (e.1 j).val)) (actualPaddingVertex Qp)
      (centeredTuple (∏ j, (e.1 j).val).primeFactors) L K (extra (∏ j, (e.1 j).val))
      (fun z => (actualPaddingDegree (univ.biUnion P) z : ℝ) ≤ 6 * W * J ∧
        actualPaddingDegreeCut Qp L z) h (∏ j, (e.1 j).val) e.2.val n m
  else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def ambientLiouvilleBlockForm {J : ℕ} (P : Fin J → Finset ℕ)
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (t : ℕ) : ℂ :=
  let c : ℤ := (t + 2 : ℕ)
  let v := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + c) integerLiouville
  inner ℂ v (primeBlockCompression P M Q u eligible (actualPaddingVertex Qp)
    L K W extra h (fun d n m => gate d (n + c) (m + c)) keep c v)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def retainedPrimeStep {J : ℕ} {P : Fin J → Finset ℕ}
    {Q : Finset ℕ} (eligible : ℕ → ℕ → Prop) (h : ℕ)
    (e : ((j : Fin J) → P j) × Q) : ℕ :=
  if eligible (∏ j, (e.1 j).val) e.2.val then h * e.2.val * ∏ j, (e.1 j).val else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def retainedPrimePrefix {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (N : ℕ) : ℂ :=
  positivePrefix (fun n => ∑ e : ((j : Fin J) → P j) × Q,
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
      ((n : ℤ) + (h * e.2.val * ∏ j, (e.1 j).val : ℕ))) N / (N : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def canonicalRetainedPrefix (h l b : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (N : ℕ) : ℂ :=
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ data.pairs) z
  retainedPrimePrefix P Q Qp actualPaddingCoefficient (fun d q => (d, q) ∈ data.pairs)
    L (Real.exp (4 * J)) W (fun _ => actualPaddingDegreeCut Qp L)
    h (progressionEdgeGate h l b) keep N

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def retainedComplexPrimeEdge {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ) : ℂ :=
  if gate (∏ j, (e.1 j).val) n m ∧ keep n ∧ keep m then
    F n * G m * (retainedRealEdge Q u (eligible (∏ j, (e.1 j).val))
      (actualPaddingVertex Qp) (centeredTuple (∏ j, (e.1 j).val).primeFactors)
      L K (extra (∏ j, (e.1 j).val))
      (fun z => (actualPaddingDegree (univ.biUnion P) z : ℝ) ≤ 6 * W * J ∧
        actualPaddingDegreeCut Qp L z) h (∏ j, (e.1 j).val) e.2.val n m : ℂ)
  else 0

noncomputable def retainedComplexBlock {J : ℕ} (P : Fin J → Finset ℕ)
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ) (t : ℕ) : ℂ :=
  let site := fun i : Fin M => (i.val : ℤ) + (t + 2 : ℕ)
  let A := retainedPrimeMatrix P site Q u eligible (actualPaddingVertex Qp) L K extra
    (fun z => (actualPaddingDegree (univ.biUnion P) z : ℝ) ≤ 6 * W * J ∧
      actualPaddingDegreeCut Qp L z) h
    (fun d i j => gate d (site i) (site j) ∧ keep (site i) ∧ keep (site j))
  ∑ i, ∑ j, F (site i) * G (site j) * A i j

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def ambientComplexBlockTest {J : ℕ} (P : Fin J → Finset ℕ)
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ) (t : ℕ) : ℂ :=
  let c : ℤ := (t + 2 : ℕ)
  let vf := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + c) (fun n => star (F n))
  let vg := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + c) G
  inner ℂ vf (primeBlockCompression P M Q u eligible (actualPaddingVertex Qp)
    L K W extra h (fun d n m => gate d (n + c) (m + c)) keep c vg)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def retainedComplexPrefix {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ) (N : ℕ) : ℂ :=
  (positivePrefix (fun n => ∑ e : ((j : Fin J) → P j) × Q,
    retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n
      ((n : ℤ) + (h * e.2.val * ∏ j, (e.1 j).val : ℕ))) N / (N : ℂ)) / (L : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

namespace ErdosPrimeInputs.StrongChebyshev

open _root_.Filter _root_.Asymptotics
open scoped _root_.Topology

noncomputable def errorScale (c x : ℝ) : ℝ :=
  x * Real.exp (-c * Real.sqrt (Real.log x))

end ErdosPrimeInputs.StrongChebyshev

namespace ErdosPrimeInputs.PrimeAbel

open _root_.Set _root_.Finset _root_.MeasureTheory
open scoped _root_.Topology

noncomputable def primeLogWeight (n : ℕ) : ℝ := if n.Prime then Real.log n else 0
noncomputable def reciprocalPrimes (a b : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (n : ℝ)⁻¹
noncomputable def invLogWeight (t : ℝ) : ℝ := 1 / (t * Real.log t)
noncomputable def errorKernel (t : ℝ) : ℝ := (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)

end ErdosPrimeInputs.PrimeAbel

namespace ErdosPrimeInputs.PrimeEndpoints

open _root_.Finset
open _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeAbel

end ErdosPrimeInputs.PrimeEndpoints

namespace ErdosPrimeInputs.PrimeErrorDecay

open _root_.Set _root_.MeasureTheory _root_.Filter _root_.Asymptotics
open scoped _root_.Topology
open _root_.OAI.Erdos970.ErdosPrimeInputs.StrongChebyshev _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeAbel

noncomputable def decay (c t : ℝ) : ℝ := Real.exp (-c * Real.sqrt (Real.log t))
noncomputable def tailKernel (c t : ℝ) : ℝ := decay c t / (t * Real.sqrt (Real.log t))

end ErdosPrimeInputs.PrimeErrorDecay

namespace ErdosPrimeInputs.HarmonicPrimeMeasure

open _root_.Filter _root_.Asymptotics
open scoped _root_.Topology
open _root_.OAI.Erdos970.ErdosPrimeInputs.StrongChebyshev _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeAbel _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay

end ErdosPrimeInputs.HarmonicPrimeMeasure

namespace ErdosPrimeInputs.MertensStrong

open _root_.Filter _root_.Asymptotics _root_.Finset
open scoped _root_.Topology
open _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeAbel _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay

noncomputable def primeProduct (x : ℝ) : ℝ :=
  ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1:ℝ) / p)

end ErdosPrimeInputs.MertensStrong

namespace ErdosInversePrimeBin
open _root_.Filter _root_.Asymptotics
open scoped _root_.Topology
open _root_.OAI.Erdos970.ErdosPrimeInputs.StrongChebyshev _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay

end ErdosInversePrimeBin

namespace ErdosPrimeInputs.PrimePrefixMass

open _root_.Finset
open _root_.OAI.Erdos970.ErdosPrimeInputs.StrongChebyshev _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeAbel _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay

end ErdosPrimeInputs.PrimePrefixMass

namespace ErdosPrimeInputs.PrimePrefixTail

open _root_.Finset

end ErdosPrimeInputs.PrimePrefixTail

namespace ErdosPrimeInputs.LongPrimePaths

open _root_.Filter _root_.Asymptotics
open scoped _root_.Topology
open _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeAbel _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay

end ErdosPrimeInputs.LongPrimePaths

namespace ErdosPrimeInputs.HighPrimeGeometry

open _root_.Finset

end ErdosPrimeInputs.HighPrimeGeometry

namespace ErdosPrimeInputs.HighPrimeMass

open _root_.Finset

end ErdosPrimeInputs.HighPrimeMass

namespace ErdosPrimeInputs.HighPrimeRemoval

open _root_.Filter _root_.Asymptotics
open scoped _root_.Topology

end ErdosPrimeInputs.HighPrimeRemoval

end Erdos970

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def logBinStep (h : ℕ) (η : ℝ) (j : ℤ) : ℤ :=
  ⌈(h : ℝ) * Real.exp ((j : ℝ) * η)⌉

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def canonicalComplexPrefix (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (F G : ℤ → ℂ) (N : ℕ) : ℂ :=
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let active := fun d q => (d, q) ∈ data.pairs
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ active z
  retainedComplexPrefix P Q Qp actualPaddingCoefficient active L (Real.exp (4 * J)) W
    (fun _ => actualPaddingDegreeCut Qp L) h (fun _ _ _ => True) keep F G N

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def retainedNumericalEdge {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (d q : ℕ) (n m : ℤ) : ℂ :=
  if gate d n m ∧ keep n ∧ keep m then
    retainedLiouvilleEdge Q u (eligible d) (actualPaddingVertex Qp)
      (centeredTuple d.primeFactors) L K (extra d)
      (fun z => (actualPaddingDegree (univ.biUnion P) z : ℝ) ≤ 6 * W * J ∧
        actualPaddingDegreeCut Qp L z) h d q n m
  else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def uncutNumericalEdge (R : Finset ℕ) (eligible : ℕ → ℕ → Prop)
    (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop) (d q : ℕ) (n m : ℤ) : ℂ :=
  if gate d n m ∧ q ∈ R ∧ eligible d q ∧ (q : ℤ) ∣ n ∧
      m = n + (h * q * d : ℕ) then
    (actualPaddingCoefficient q * centeredTuple d.primeFactors n : ℝ) *
      integerLiouville n * integerLiouville m
  else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def liouvilleUntwist (F G : ℤ → ℂ) (n m : ℤ) : ℂ :=
  (F n * integerLiouville n) * (G m * integerLiouville m)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def uncutPrimePrefix {J : ℕ} (P : Fin J → Finset ℕ)
    (R : Finset ℕ) (eligible : ℕ → ℕ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (N : ℕ) : ℂ :=
  positivePrefix (fun n => ∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
    uncutNumericalEdge R eligible h gate d q n ((n : ℤ) + (h * q * d : ℕ))) N / (N : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def untwistedRetainedPrefix {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ) (N : ℕ) : ℂ :=
  positivePrefix (fun n => ∑ d ∈ primeTupleDivisors P, ∑ q ∈ Q,
    liouvilleUntwist F G n ((n : ℤ) + (h * q * d : ℕ)) *
      retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep d q n
        ((n : ℤ) + (h * q * d : ℕ))) N / (N : ℂ)

noncomputable def untwistedUncutPrefix {J : ℕ} (P : Fin J → Finset ℕ)
    (Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (F G : ℤ → ℂ) (N : ℕ) : ℂ :=
  positivePrefix (fun n => ∑ d ∈ primeTupleDivisors P, ∑ q ∈ Q,
    liouvilleUntwist F G n ((n : ℤ) + (h * q * d : ℕ)) *
      uncutNumericalEdge Q eligible h gate d q n ((n : ℤ) + (h * q * d : ℕ))) N / (N : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def canonicalUncutPrefix (h l b : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (N : ℕ) : ℂ :=
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let R := boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊
  uncutPrimePrefix P R eligible h (progressionEdgeGate h l b) N

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def canonicalComplexUncutPrefix (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (F G : ℤ → ℂ) (N : ℕ) : ℂ :=
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let R := boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊
  untwistedUncutPrefix P R eligible h (fun _ _ _ => True) F G N

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SelbergOptimization

open scoped _root_.BigOperators _root_.ArithmeticFunction.Moebius

noncomputable def lowerMobius (F : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ t ∈ m.divisorsAntidiagonal, (μ t.1 : ℝ) * F t.2

noncomputable def inverseMultiples (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  lowerMobius (fun t => y (P / t)) (P / d)

noncomputable def normalization (s : BoundingSieve) (R : ℕ) : ℝ :=
  ∑ l ∈ s.prodPrimes.divisors, if l ≤ R then s.selbergTerms l else 0

noncomputable def diagonalTarget (s : BoundingSieve) (R l : ℕ) : ℝ :=
  if l ≤ R then (μ l : ℝ) * s.selbergTerms l / normalization s R else 0

noncomputable def optimizedWeight (s : BoundingSieve) (R d : ℕ) : ℝ :=
  inverseMultiples s.prodPrimes (diagonalTarget s R) d / s.nu d

noncomputable def cutoffNormalization (z R : ℕ) : ℝ :=
  normalization (IntervalBoundingSieve.intervalSieve 0 0
    (IntervalBoundingSieve.cutoffProduct z) (IntervalBoundingSieve.cutoffProduct_squarefree z)) R

end NumberTheoryLean.SelbergOptimization

end

section

namespace NumberTheoryLean.SquarefreeHarmonic

open scoped _root_.BigOperators

noncomputable def squarefreeUpTo (R : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 R).filter Squarefree

noncomputable def squarefreeHarmonic (R : ℕ) : ℝ :=
  ∑ d ∈ squarefreeUpTo R, (d : ℝ)⁻¹

end NumberTheoryLean.SquarefreeHarmonic

end

end Erdos970

end OAI

end

section

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PrimeDensityBlocks

open scoped _root_.BigOperators

def dyadicPrimes (n : ℕ) : Finset ℕ := (Finset.Ico n (2 * n)).filter Nat.Prime

def geometricPrimes (j : ℕ) : Finset ℕ :=
  (Finset.Ico (2 ^ (2 ^ j)) (2 ^ (2 ^ (j + 1)))).filter Nat.Prime

def lastBlock (V : ℕ) : ℕ := Nat.log 2 (Nat.log 2 V)

def blockIndices (V : ℕ) : Finset ℕ := Finset.range (lastBlock V + 1)

def primeBlock (P : Finset ℕ) (j : ℕ) : Finset ℕ := P ∩ geometricPrimes j

def reverseOrder (m J j : ℕ) : ℕ := m + (J - j)

def supportCost (m J : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (J + 1), 2 ^ (j + 1) * (2 * reverseOrder m J j + 1)

noncomputable def actualLowerCoefficient (V m : ℕ) (P : Finset ℕ) (T : Finset ℕ) : ℝ :=
  DisjointBlockExpansion.lowerCoefficient (blockIndices V) (primeBlock P)
    (reverseOrder m (lastBlock V)) T

end NumberTheoryLean.PrimeDensityBlocks

end

end Erdos970

end OAI

end

section

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FundamentalBlockEstimate

open scoped _root_.BigOperators

noncomputable def baseError (m : ℕ) : ℝ := Real.exp (5 * 1532) / (2 : ℝ) ^ (2 * m + 1)

noncomputable def blockEuler (P : Finset ℕ) (g : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∏ p ∈ PrimeDensityBlocks.primeBlock P j, (1 - g p)

noncomputable def blockUpperDensity (V m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) (j : ℕ) : ℝ :=
  BonferroniDensity.densityPolynomial (2 * PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V) j)
    (PrimeDensityBlocks.primeBlock P j) g

noncomputable def blockOverflowDensity (V m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) (j : ℕ) : ℝ :=
  BonferroniDensity.elementarySum (PrimeDensityBlocks.primeBlock P j) g
    (2 * PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V) j + 1)

noncomputable def actualUpperDensity (V m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ T ∈ P.powerset,
    DisjointBlockExpansion.upperCoefficient (PrimeDensityBlocks.blockIndices V) (PrimeDensityBlocks.primeBlock P)
      (PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V)) T * ∏ p ∈ T, g p

noncomputable def actualLowerDensity (V m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ T ∈ P.powerset, PrimeDensityBlocks.actualLowerCoefficient V m P T * ∏ p ∈ T, g p

noncomputable def actualUpperCoefficient (V m : ℕ) (P : Finset ℕ) (T : Finset ℕ) : ℝ :=
  DisjointBlockExpansion.upperCoefficient (PrimeDensityBlocks.blockIndices V) (PrimeDensityBlocks.primeBlock P)
    (PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V)) T

def levelSubsets (P : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter fun T => (∏ p ∈ T, p) ≤ L

def levelDivisors (P : Finset ℕ) (L : ℕ) : Finset ℕ :=
  (∏ p ∈ P, p).divisors.filter fun d => d ≤ L

noncomputable def integerRemainder {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hit : ℕ → α → Prop) (X : ℝ) (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  BonferroniBlocks.intersectionRemainder C weight hit X g d.primeFactors

end NumberTheoryLean.FundamentalBlockEstimate

end

end Erdos970

end OAI

end

section

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

end ErdosVarianceMoments

end

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

end ErdosVarianceMoments

end

section

namespace NumberTheoryLean.RealFundamentalSieve

open scoped _root_.BigOperators

noncomputable def levelDivisors (P : Finset ℕ) (v s : ℝ) : Finset ℕ := by
  classical
  exact (∏ p ∈ P, p).divisors.filter fun d => (d : ℝ) ≤ v ^ s

end NumberTheoryLean.RealFundamentalSieve

end

section

namespace ErdosVarianceMoments
open _root_.OAI.Erdos970.NumberTheoryLean
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

end ErdosVarianceMoments

end

section

namespace NumberTheoryLean.SmallSieveFinite

open scoped _root_.BigOperators

end NumberTheoryLean.SmallSieveFinite

end

section

namespace NumberTheoryLean.EulerProductRatio

open scoped _root_.BigOperators

end NumberTheoryLean.EulerProductRatio

end

end Erdos970

end OAI

end

section

namespace OAI

namespace Erdos970

namespace NumberTheoryLean.ProgressionSieve

open scoped _root_.BigOperators

end NumberTheoryLean.ProgressionSieve

namespace NumberTheoryLean.SmallSieveRelative

open scoped _root_.BigOperators

end NumberTheoryLean.SmallSieveRelative

namespace NumberTheoryLean.ProgressionSmallSieve

end NumberTheoryLean.ProgressionSmallSieve

namespace ErdosModulusRelative
open _root_.OAI.Erdos970.NumberTheoryLean
attribute [local instance] Classical.propDecidable

end ErdosModulusRelative

namespace NumberTheoryLean.SmallSieveUpper

end NumberTheoryLean.SmallSieveUpper

namespace ErdosPrimeInputs.SubsetPrimeSieve

open _root_.Finset
open _root_.OAI.Erdos970.NumberTheoryLean
open SmallSieveFinite IntervalBoundingSieve

noncomputable def euler (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)

end ErdosPrimeInputs.SubsetPrimeSieve

namespace ErdosModulusRelative
open _root_.OAI.Erdos970.NumberTheoryLean

end ErdosModulusRelative

namespace ErdosInverseTail
open _root_.OAI.Erdos970.NumberTheoryLean

end ErdosInverseTail

namespace ErdosInverseTail
open _root_.OAI.Erdos970.NumberTheoryLean

end ErdosInverseTail

namespace ErdosInverseTail
open _root_.OAI.Erdos970.NumberTheoryLean

end ErdosInverseTail

end Erdos970

end OAI

end

section

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.PrimeProductOmissions

open _root_.Finset
open _root_.OAI.Erdos970.NumberTheoryLean.LargePrimeDeletion _root_.OAI.Erdos970.ErdosPrimeInputs.SubsetPrimeSieve _root_.OAI.Erdos970.ErdosPrimeInputs.MertensStrong

noncomputable def reducedPrimes (z q : ℕ) : Finset ℕ := cutoffPrimes z \ q.primeFactors

end ErdosPrimeInputs.PrimeProductOmissions

end

end Erdos970

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def fullComplexBin {J : ℕ} (P : Fin J → Finset ℕ)
    (Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h : ℕ) (T : ℝ) : ℂ :=
  ∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
    (positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) ⌊T⌋₊ / (T : ℂ))

noncomputable def nonrawComplexBin {J : ℕ} (P : Fin J → Finset ℕ)
    (Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h : ℕ) (T : ℝ) : ℂ :=
  ∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
    ((positivePrefix (tupleComplexCenteredProfile P q eligible F G h) ⌊T⌋₊ -
      positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) ⌊T⌋₊) / (T : ℂ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def eligibleComplexPairs (D Q : Finset ℕ)
    (eligible : ℕ → ℕ → Prop) : Finset (ℕ × ℕ) :=
  (D ×ˢ retainedPrimeDivisors Q).filter (fun dq => eligible dq.1 dq.2)

noncomputable def complexPairWeight (dq : ℕ × ℕ) : ℝ :=
  (4 : ℝ) ^ dq.2.primeFactors.card / (dq.1 * dq.2 : ℕ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def progressionLiouvilleMean (h l b : ℕ) [NeZero l] (X : ℝ) : ℂ :=
  positivePrefix (fun n => progressionSequence liouville l (b : ZMod l) n * liouville (n + h))
    ⌊X⌋₊ / (X : ℂ)

noncomputable def canonicalRawBin (h l b : ℕ) (E : Finset ℕ) (W L η X : ℝ) (j : ℤ) : ℂ :=
  let T := X * Real.exp ((j : ℝ) * η)
  ((⌊T⌋₊ : ℂ) / (T : ℂ)) *
    canonicalUncutPrefix h l b E W L (numericalBinEligible L η j) ⌊T⌋₊

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def selectedPairBin (η : ℝ) (A : Finset (ℕ × ℕ))
    (j : ℤ) (d q : ℕ) : Prop :=
  (d, q) ∈ A ∧ paddingBin η 0 (Real.log (d * q : ℕ)) = j

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def selectedRawMean (A : Finset (ℕ × ℕ)) (T : ℕ × ℕ → ℝ)
    (f g : ℕ → ℂ) (h : ℕ) : ℂ :=
  ∑ dq ∈ A, (actualPaddingCoefficient dq.2 : ℂ) *
    (positivePrefix (fun n => f ((dq.1 * dq.2) * n) *
      g ((dq.1 * dq.2) * (n + h))) (⌊T dq⌋₊ / (dq.1 * dq.2)) / (T dq : ℂ))

noncomputable def selectedRawCoefficient (A : Finset (ℕ × ℕ)) (f g : ℕ → ℂ) : ℂ :=
  ∑ dq ∈ A, (complexPairWeight dq : ℂ) * (f (dq.1 * dq.2) * g (dq.1 * dq.2))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.AffinePrimeSieve

open _root_.Finset
open _root_.OAI.Erdos970.NumberTheoryLean IntervalBoundingSieve _root_.OAI.Erdos970.ErdosPrimeInputs.SubsetPrimeSieve _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeProductOmissions

noncomputable def value (a : ℤ) (q i : ℕ) : ℤ := a + (q:ℤ)*i
noncomputable def survivors (N : ℕ) (a : ℤ) (q : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (range N).filter (fun i => ∀ p ∈ P, ¬Int.ModEq (p:ℤ) (value a q i) 0)
noncomputable def primeIndices (N : ℕ) (a : ℤ) (q : ℕ) : Finset ℕ :=
  (range N).filter (fun i => (value a q i).natAbs.Prime ∧ 0 ≤ value a q i)
noncomputable def smallPrimeIndices (N : ℕ) (a : ℤ) (q : ℕ) (u : ℝ) : Finset ℕ :=
  (primeIndices N a q).filter (fun i => ((value a q i).natAbs : ℝ) ≤ u)

end ErdosPrimeInputs.AffinePrimeSieve

end

section

namespace ErdosPrimeInputs.SieveScale

open _root_.Filter
open scoped _root_.Topology

noncomputable def level : ℝ := 480024
noncomputable def exponent : ℝ := 1 / (2*level)
noncomputable def cutoff (J : ℝ) : ℝ := J ^ exponent

end ErdosPrimeInputs.SieveScale

end

end Erdos970

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical

noncomputable def halaszPrimePolynomial (P : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  mrtExponentialPolynomial P
    (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ)) (fun p => -Real.log (p : ℝ)) t

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical

noncomputable def halaszGroupedDouble (f : ℕ → ℂ) (N : ℕ) (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, (Real.log (p : ℝ) : ℂ) * f p *
    (halaszPrimeConvolution f (N / p) / (Real.log ((N : ℝ) / p) : ℂ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical

noncomputable def halaszMixedGrouped (G B : ℕ → ℂ) (N : ℕ) (L : ℝ)
    (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, (Real.log (p:ℝ):ℂ)*G p*
    (halaszMixedPrimeConvolution G B (N/p) L ((N/p:ℕ):ℝ)/(Real.log ((N:ℝ)/p):ℂ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszMixedDouble (G B : ℕ → ℂ) (N : ℕ) (R : ℝ) : ℂ :=
  halaszMixedGrouped G B N R (mrtPrimeBand R ((N:ℝ)/2))

noncomputable def halaszMixedErrorConstant (R : ℝ) : ℝ :=
  halaszPrimePowerConstant+Real.log R+halaszMertensConstant+1+Real.log 2

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def halaszMixedNumericConstant : ℝ :=
  (halaszPrimePowerConstant+3*halaszMertensConstant+1+Real.log 2+1)+
    (halaszPrimePowerConstant+halaszMertensConstant+1+Real.log 2+1)*
      (1+|halaszDenominatorConstant|)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.ComplexConjugate

noncomputable def halaszTwistedFunction (f : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  f n * conj (mrtArchimedeanTwist t n)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.ComplexConjugate _root_.Classical

noncomputable def mrtMissingCoefficient (F : ℕ → ℂ) (Q : Finset ℕ)
    (n : ℕ) : ℂ := F n * (mrtPrimeMask Q n : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset

noncomputable def halaszPowerPhase (t x : ℝ) : ℂ :=
  Complex.exp (((-t * Real.log x : ℝ) : ℂ) * Complex.I)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.MeasureTheory

noncomputable def halaszLogPhase (u v x : ℝ) : ℂ :=
  Complex.exp (((u*Real.log x-v*x : ℝ):ℂ)*Complex.I)

noncomputable def halaszLogSlope (u v x : ℝ) : ℝ := u/x-v

noncomputable def halaszLogReciprocalDeriv (u v x : ℝ) : ℝ :=
  u/(x^2*(halaszLogSlope u v x)^2)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszPrimeLogWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log n else 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.ComplexConjugate _root_.Classical

noncomputable def halaszPrimeDiscrepancy (F : ℕ → ℂ) (t : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N, ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / p

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.MeasureTheory

noncomputable def halaszLogAmplitude0 (u v m c x : ℝ) : ℝ :=
  (m*x+c) / halaszLogSlope u v x

noncomputable def halaszLogAmplitude2 (u v m c x : ℝ) : ℝ :=
  m/(halaszLogSlope u v x)^2 +
    (m*x+c)*u/(x^2*(halaszLogSlope u v x)^3)

noncomputable def halaszLogAmplitude2Deriv (u v m c x : ℝ) : ℝ :=
  3*m*u/(x^2*(halaszLogSlope u v x)^3) -
    2*(m*x+c)*u/(x^3*(halaszLogSlope u v x)^3) +
    3*(m*x+c)*u^2/(x^4*(halaszLogSlope u v x)^4)

noncomputable def halaszLogDoublePrimitive (u v m c x : ℝ) : ℂ :=
  halaszLogPhase u v x * ((halaszLogAmplitude2 u v m c x:ℂ) -
    Complex.I*(halaszLogAmplitude0 u v m c x:ℂ))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.MeasureTheory

noncomputable def halaszTriangleIntegral (N u v : ℝ) : ℂ :=
  (∫ x in N/2..3*N/2, ((2/N*x-1:ℝ):ℂ)*halaszLogPhase u v x) +
  (∫ x in 3*N/2..5*N/2, ((-(2/N)*x+5:ℝ):ℂ)*halaszLogPhase u v x)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.MeasureTheory

noncomputable def halaszTriangleWeight (N x : ℝ) : ℝ :=
  max 0 (min (2/N*x-1) (5-2/N*x))

noncomputable def halaszTriangleFunction (N u v x : ℝ) : ℂ :=
  (halaszTriangleWeight N x:ℂ)*halaszLogPhase u v x

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszNearModes (R : ℝ) : Finset ℤ :=
  (Icc (-⌊R⌋) ⌊R⌋).erase 0

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def halaszIntegerSquareMass : ℝ := ∑' k : ℤ, 1/(k:ℝ)^2

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszTriangleSupport (N : ℝ) : Finset ℕ :=
  range (⌈5*N/2⌉₊+1)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszUnitReciprocal (F : ℕ → ℂ) (n : ℕ) : ℝ :=
  ‖mrtArithmetic (halaszUnitCorrection F) n‖ / (n : ℝ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def halaszPhaseMean (F : ℕ → ℂ) (t : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 N, F n * halaszPowerPhase t n

noncomputable def halaszUnitMain (F : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ) * ∑ d ∈ Icc 1 N, halaszUnitCorrection F d / (d : ℂ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

def HalaszPrimeSparseInput : Prop :=
  ∃ C L₀ : ℝ, 0 < C ∧ ∀ L Y : ℝ, L₀ ≤ L → 1 ≤ L → 2 ≤ Y →
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y) →
    ∀ (a : ℕ → ℂ) (S : Finset ℝ),
    (∀ t ∈ S, |t| ≤ Real.exp L) →
    (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a (fun p => -Real.log (p:ℝ)) t‖^2) ≤
      C*(Y+(S.card:ℝ)*Y*Real.exp (-Real.log Y/L^(3/4:ℝ))*L^2)*
        ∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

noncomputable def mrtRieszPrimeWeight (Y : ℝ) (n : ℕ) : ℝ :=
  4 * (max (1 - (n : ℝ) / (4 * Y)) 0) ^ 2

noncomputable def mrtRieszPrimeSupport (Y : ℝ) : Finset ℕ := Icc 1 ⌊4 * Y⌋₊

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Erdos970 _root_.OAI.Erdos970 _root_.Finset _root_.ArithmeticFunction
open scoped _root_.Classical

noncomputable def mrtMangoldtTwist (u : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((u : ℂ) * Complex.I))

noncomputable def mrtZetaRieszIntegrand (x u : ℝ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta (s + (u : ℂ) * Complex.I) /
    riemannZeta (s + (u : ℂ) * Complex.I)) * mrtRieszKernel x s

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def halaszSparseKernelError (M T : ℝ) : ℝ :=
  (440/Real.pi)*Real.sqrt (2*T) +
    (512/(M*(2*Real.pi)^2))*halaszIntegerSquareMass

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtAmplificationOrder (Y u : ℝ) : ℕ :=
  ⌈Real.log u / Real.log Y⌉₊

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def mrtFrequencyExponent (η : ℝ) (j : ℕ) : ℝ :=
  1 / 4 - η * (1 + 1 / (2 * ((j : ℝ) + 1)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtSmallFrequencyBand {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) (j : ℕ) : Set ℝ :=
  {t | ∀ k ∈ K j, ‖Q j k t‖ ≤ A j k}

noncomputable def mrtFirstSmallBand {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) (j : ℕ) : Set ℝ :=
  mrtSmallFrequencyBand K Q A j \ ⋃ i ∈ range j, mrtSmallFrequencyBand K Q A i

noncomputable def mrtNoSmallBand {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) (J : ℕ) : Set ℝ :=
  (⋃ j ∈ range J, mrtSmallFrequencyBand K Q A j)ᶜ

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def mrtPrimeLogBin (H : ℝ) (p : ℕ) : ℕ :=
  ⌊H * Real.log (p : ℝ)⌋₊

noncomputable def mrtPrimeLogLower (H : ℝ) (k : ℕ) : ℝ :=
  Real.exp ((k : ℝ) / H)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def mrtAmplificationCost (r : ℕ) (y a : ℝ) : ℝ :=
  ((r : ℝ) + 1) * Real.log 2 + y +
    2 * (r : ℝ) * Real.log (max 1 (r : ℝ)) + 2 * a * y

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def mrtMixedBinCost (η : ℝ) (j : ℕ) (τ Y u : ℝ) : ℝ :=
  Real.exp (-mrtFrequencyExponent η (j + 1) * Real.log u) ^ 2 *
    ((16 * Real.exp 10 *
      (τ + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
        ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2) /
      Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
        (2 * mrtAmplificationOrder ⌈Y⌉₊ u))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def mrtLogBins (H P Q : ℝ) : Finset ℕ :=
  Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset

noncomputable def mrtBaseResolution (P Q η : ℝ) : ℝ :=
  Real.exp ((1 / 6 - η) * Real.log P - (1 / 3) * Real.log (Real.log Q))

noncomputable def mrtResolution (P Q η : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) ^ 2 * mrtBaseResolution P Q η

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

noncomputable def halaszSparseErrorConstant : ℝ :=
  (440/Real.pi)*Real.sqrt 2 + (512/(2*Real.pi)^2)*halaszIntegerSquareMass

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

def HalaszHighPrimeInput : Prop :=
  ∀ᶠ X : ℕ in atTop, ∀ u : ℝ, (Real.log X)^20 ≤ |u| → |u| ≤ 2*X →
    (1/10:ℝ)*Real.log (Real.log X) ≤
      ∑ p ∈ primesUpTo X, (1-|Real.cos (u*Real.log (p:ℝ)/2)|)/(p:ℝ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.Classical

noncomputable def mrtLogPrimePolynomial (S : Finset ℕ) (F : ℕ → ℂ)
    (H : ℝ) (k : ℕ) : ℝ → ℂ :=
  mrtExponentialPolynomial (S.filter (fun p => mrtPrimeLogBin H p = k))
    (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ))

noncomputable def mrtLogSmallSet (S : Finset ℕ) (F : ℕ → ℂ)
    (H : ℝ) (K : Finset ℕ) (a : ℝ) : Set ℝ :=
  {t | ∀ k ∈ K, ‖mrtLogPrimePolynomial S F H k t‖ ≤
    Real.exp (-a*Real.log (mrtPrimeLogLower H k))}

noncomputable def mrtLogLargeSet (S : Finset ℕ) (F : ℕ → ℂ)
    (H : ℝ) (K : Finset ℕ) (a : ℝ) : Set ℝ :=
  {t | ∃ k ∈ K, Real.exp (-a*Real.log (mrtPrimeLogLower H k)) <
    ‖mrtLogPrimePolynomial S F H k t‖}

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.Classical

noncomputable def mrtLaterLogClass (S₀ S₁ : Finset ℕ) (F : ℕ → ℂ)
    (P Q η : ℝ) (j : ℕ) (T : ℝ) : Set ℝ :=
  Ioc (-T) T ∩
    (mrtLogSmallSet S₁ F (mrtResolution P Q η (j+2))
      (mrtLogBins (mrtResolution P Q η (j+2))
        (mrtBandLower P Q (j+2)) (mrtBandUpper Q (j+2)))
      (mrtFrequencyExponent η (j+1)) ∩
    mrtLogLargeSet S₀ F (mrtResolution P Q η (j+1))
      (mrtLogBins (mrtResolution P Q η (j+1))
        (mrtBandLower P Q (j+1)) (mrtBandUpper Q (j+1)))
      (mrtFrequencyExponent η j))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.Classical

noncomputable def mrtLogFamilyBins (P Q η : ℝ) (r : ℕ) : Finset ℕ :=
  mrtLogBins (mrtResolution P Q η (r+1))
    (mrtBandLower P Q (r+1)) (mrtBandUpper Q (r+1))

noncomputable def mrtLogFamilyPolynomial (V : ℕ → Finset ℕ) (F : ℕ → ℂ)
    (P Q η : ℝ) (r k : ℕ) : ℝ → ℂ :=
  mrtLogPrimePolynomial (V (r+1)) F (mrtResolution P Q η (r+1)) k

noncomputable def mrtLogFamilyThreshold (P Q η : ℝ) (r k : ℕ) : ℝ :=
  Real.exp (-mrtFrequencyExponent η r *
    Real.log (mrtPrimeLogLower (mrtResolution P Q η (r+1)) k))

noncomputable def mrtFirstLogClass (V : ℕ → Finset ℕ) (F : ℕ → ℂ)
    (P Q η : ℝ) (r : ℕ) (T : ℝ) : Set ℝ :=
  Ioc (-T) T ∩ mrtFirstSmallBand (mrtLogFamilyBins P Q η)
    (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) r

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.Classical

noncomputable def mrtLogExtractionError (V : ℕ → Finset ℕ)
    (P Q η : ℝ) (j : ℕ) : ℝ :=
  (∑ p ∈ V j, 1/(p:ℝ)^2) + (∑ p ∈ V j, 1/(p:ℝ)^2)^2 +
    2/mrtResolution P Q η j

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical

noncomputable def mrtShortPrimeSampleCost (Y V T : ℝ) (r : ℕ) : ℝ :=
  (8*Real.exp 1*(T+1+((2*⌈Y⌉₊)^r:ℕ)) *
    (2+(Real.log ((2*⌈Y⌉₊)^r:ℕ))^2) * (r.factorial:ℝ)*(2/Y)^r)/V^(2*r)

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.Classical

noncomputable def mrtExtraPrimeLower (L : ℝ) : ℝ :=
  Real.exp (2*L^(79/80:ℝ))

noncomputable def mrtExtraPrimeUpper (L : ℝ) : ℝ :=
  Real.exp (L/Real.log L)

noncomputable def mrtExtraPrimeResolution (L : ℝ) : ℝ := L^(1/80:ℝ)

end TwoPointCorrelations

end OAI

end

section

namespace OAI
noncomputable section
open scoped _root_.BigOperators
open _root_.Finset

namespace Problem337.GoldbachSelberg

def sieve (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) : BoundingSieve :=
  PrimePairSieve.imageSieve (Icc 1 (N - 1)) (fun x => x * (N - x)) P hP
    (goldbachSieveDensity N) (goldbachSieveDensity_isMultiplicative N)
    (fun p hp _ => goldbachSieveDensity_prime_pos N p hp)
    (fun p hp _ => goldbachSieveDensity_prime_lt_one N p hp (fun _ => hN))

def denominator (N P z : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, if d ≤ z then
    goldbachSieveDensity N d *
      ∏ p ∈ d.primeFactors, (1 - goldbachSieveDensity N p)⁻¹ else 0

end Problem337.GoldbachSelberg

end

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def sieveSingularMeanConstant : ℝ :=
  (4 : ℝ) ^ 36 * (∑' d : ℕ, (d : ℝ) ^ (-(3 / 2 : ℝ)))

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtExtraCoarsePolynomial {ι : Type*} (L : ℝ)
    (J : Finset ι) (P : ι → Finset ℕ) (F : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  let A := mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let H := mrtExtraPrimeResolution L
  ∑ k ∈ mrtLogBins H (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L),
    mrtLogPrimePolynomial A F H k t *
      mrtCofactorPolynomial A (mrtTypicalCoefficient J P F) N (mrtPrimeLogLower H k) t

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtNoSmallOffCenter (P Q : ℝ) (J N : ℕ) (F : ℕ → ℂ) (τ : ℝ) : Set ℝ :=
  (Set.Ioc (-(N:ℝ)) N ∩ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
    (mrtLogFamilyPolynomial
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F P Q (1/100))
    (mrtLogFamilyThreshold P Q (1/100)) J) ∩
    {t | (Real.log N)^(1/16:ℝ) ≤ |t-τ|}

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

noncomputable def mrtActualNoSmall (P Q : ℝ) (J N : ℕ) (F : ℕ → ℂ) : Set ℝ :=
  Set.Ioc (-(N:ℝ)) N ∩ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
    (mrtLogFamilyPolynomial
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F P Q (1/100))
    (mrtLogFamilyThreshold P Q (1/100)) J

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

noncomputable def majorArcEnergyConstant (C : ℝ) : ℝ :=
  (139968/(2*Real.pi))*(12*(C+33792*Real.exp 1+2+2048*Real.exp 2)+2048*Real.exp 1)+1

end TwoPointCorrelations

end OAI

end

section

namespace OAI

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.LSeries.notation

noncomputable def mrtPrimePowerCutoff (a : ℝ) (X : ℕ) : ℕ :=
  ⌊Real.exp ((Real.log (X:ℝ))^a)⌋₊

end TwoPointCorrelations

end OAI

end


