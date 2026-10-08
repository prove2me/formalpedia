-- Prove2me | Definitions.Def_CoordinateSweeps
-- name    : CoordinateSweeps
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:05.420574+00:00
-- url     : https://prove2.me/theorems/3045a0f4-5515-422b-b9b3-393fc745aa0a
-- statement:
--   A finite law assigns nonnegative real masses summing to one; uniform laws and their pushforwards are provided, and laws agreeing pointwise are equal. On the Boolean cube {0,1}ᵈ, a binary layer independently swaps or preserves each pair differing only in a chosen coordinate. A binary sweep applies these layers in coordinate order, starting at zero, and its law B is induced by uniformly choosing all swap bits. A grid has a positive number b of coordinates, with side j equal to a Boolean cube of dimension dⱼ and length nⱼ=2^{dⱼ}; its total size is s=∏ⱼnⱼ. A choice assigns a permutation to every coordinate line, each stage applies all permutations for one coordinate, and the boundary at time t is the composition of the first t stages. The grid is allowed at scale r when r≤dⱼ≤2r for every j, so all side lengths lie between 2ʳ and 2^{2r}. A family of h holes specifies h paths through the b+1 boundaries, distinct at every boundary and changing only coordinate j at stage j. Compatibility means a choice realizes all these paths; feasibility means some compatible choice exists. If mⱼ,L paths traverse line L at stage j, their cost is C=∑ⱼ,L log(nⱼ^{mⱼ,L}/(nⱼ)_{mⱼ,L}), where (n)ₘ is the falling factorial. The stabilizer consists of permutations fixing every marked input. Choosing any compatible reference sweep identifies each compatible sweep with a residual permutation in this stabilizer by composing it with the inverse reference sweep. For real z, a choice has the product weight obtained by assigning each line the mixture (1−z)U+zB, where U is uniform on all permutations of that line; these are probability weights when 0≤z≤1. The probability of the hole trajectories is the sum of compatible weights. For an event E, eventDistance is the sum over E of absolute differences between the normalized z-weights and normalized zero-weights, without the factor one-half. A unitary irreducible representation is specified by a positive dimension D and a group homomorphism into complex D-by-D matrices, assumed unitary and having no invariant complex subspaces other than zero and the whole space. Its conditional average K is the weighted average of the residual representation matrices over compatible choices, divided by the trajectory probability. The unnormalized Schatten moment is M_q(K)=Re tr((K* K)^q), with no division by D; logMoment equals log M when M≠0 and −∞ when M=0. Set a=1/100, c₀=e₀=1/10000, c(s)=c₀+1/√log s, and e(s)=e₀−1/√log s. ConditionalMain is the defined proposition that there exist integers r,q≥1 and 0<z*≤1/2 such that, for every allowed grid, every feasible family of any number h of holes, every z∈[0,z*], and every such representation of its stabilizer, logMoment(M_q(K))≤−c(s)log D+e(s)h log s−C. MomentBound defines the corresponding exponential inequality M_q(K)≤exp(−c(s)log D+e(s)h log s−C) for fixed grid, q, and z, universally over feasible holes and representations. Further definitions package numerical hypotheses for scalar estimates: ScaleLarge requires r≥1 and r log 2≥max((2/e₀)²,4/e₀); baseWidth is (2^{2r})! and baseZeta is 1/(4 baseWidth²). MainSizeReady(q,s) assumes log s≥1, 100004s^{1−a/4}≤s^{1−1/1600}, [4(2q+1)+82c₀]2s^{4/5+2a}log(s+1)≤s^{9/10}, and s^{9/10}+s^{1−a/2}log s≤s^{1−a/4}/(20√log s). The sparse estimates fix θ=1/1600, K₀=100000, B₀=12800, ξ=1/2048000000, ρ=1/32768000000, q=65536000000, and U₀=log 2+B₀[K₀+1+log 4+log(16 exp(2))+log(1+16 exp(2))]. Their SizeReady(s) assumes s≥2, log s≤s^{θ/4}, 2≤s^{θ/4}, B₀+1≤s^{θ/2}, 4/s^{1/(4B₀)}≤θ/(64B₀), log(1+2B₀)+log 2≤ξ log s, s^{−ξ}≤1/8, U₀≤ξ log s/16, and log 2≤ξ log s/8. ScaleReady(r) assumes r≥2, r log 2≥1, 3 log 2+2(K₀+1+log 4)≤θr log 2/8, and SizeReady(s) for every real s≥2ʳ. Finally, slack(s)=s^{−2ρs}(s^ρ−1) for s>1 and equals one otherwise; SparsePerturb(r,z*) is the proposition that 0<z*≤baseZeta(r) and every allowed grid with b≤B₀, every z∈[0,z*], and every nonempty event E satisfy eventDistance(E,z)<slack(s). These readiness conditions and main bounds are definitions of propositions, not assertions that they hold.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoordinateSweeps.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CoordinateSweeps.lean; bytes 16..10918
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
Conditional moments for one ordered coordinate sweep on power-of-two rectangular
grids. The line law mixes uniform permutations with a binary coordinate sweep.
The trace is unnormalized, and the trajectory cost uses falling factorials.
-/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ComplexConjugate MatrixOrder ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps

structure FiniteLaw (Ω : Type*) where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ᶠ x, mass x = 1

namespace FiniteLaw

variable {Ω X Y : Type*}

instance : CoeFun (FiniteLaw Ω) (fun _ => Ω → ℝ) := ⟨FiniteLaw.mass⟩

@[ext] theorem ext {μ ν : FiniteLaw Ω} (h : ∀ x, μ x = ν x) : μ = ν := by
  cases μ
  cases ν
  congr
  exact funext h

variable [Fintype Ω] [Fintype X] [Fintype Y]

@[simp] theorem sum_mass (μ : FiniteLaw Ω) : ∑ x, μ x = 1 := by
  simpa only [finsum_eq_sum_of_fintype] using μ.total

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  mass _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    rw [finsum_eq_sum_of_fintype]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

def map (μ : FiniteLaw Ω) (f : Ω → X) : FiniteLaw X where
  mass y := ∑ x, if f x = y then μ x else 0
  nonneg y := Finset.sum_nonneg (fun x _ => by split_ifs; exact μ.nonneg x; exact le_rfl)
  total := by
    rw [finsum_eq_sum_of_fintype]
    classical
    rw [Finset.sum_comm]
    simp [μ.sum_mass]

end FiniteLaw

abbrev Cube (d : ℕ) := Fin d → Bool

def pairSwitch {L : Type*} (bits : L → Bool) : Equiv.Perm (Bool × L) where
  toFun x := (Bool.xor x.1 (bits x.2), x.2)
  invFun x := (Bool.xor x.1 (bits x.2), x.2)
  left_inv point := by
    rcases point with ⟨bit, label⟩
    change ((bit ^^ bits label) ^^ bits label, label) = (bit, label)
    cases bit <;> cases bits label <;> simp
  right_inv point := by
    rcases point with ⟨bit, label⟩
    change ((bit ^^ bits label) ^^ bits label, label) = (bit, label)
    cases bit <;> cases bits label <;> simp

def binaryLayer {d : ℕ} (j : Fin d) (bits : ({k : Fin d // k ≠ j} → Bool) → Bool) :
    Equiv.Perm (Cube d) :=
  (Equiv.funSplitAt j Bool).trans ((pairSwitch bits).trans (Equiv.funSplitAt j Bool).symm)

/-- Coordinate zero acts first. -/
def orderedProduct {G : Type*} [Monoid G] {d : ℕ} (g : Fin d → G) : G :=
  (List.ofFn g).reverse.prod

abbrev BinaryChoices (d : ℕ) := ∀ j : Fin d, ({k : Fin d // k ≠ j} → Bool) → Bool

instance (d : ℕ) : Nonempty (BinaryChoices d) := ⟨fun _ _ => false⟩

def binarySweep (d : ℕ) (bits : BinaryChoices d) : Equiv.Perm (Cube d) :=
  orderedProduct (fun j => binaryLayer j (bits j))

def binaryLaw (d : ℕ) : FiniteLaw (Equiv.Perm (Cube d)) :=
  (FiniteLaw.uniform (BinaryChoices d)).map (binarySweep d)

structure Grid where
  b : ℕ
  positive : 0 < b
  bits : Fin b → ℕ

namespace Grid

def size (G : Grid) : ℕ := ∏ j, 2 ^ G.bits j

abbrev Slot (G : Grid) := ∀ j, Cube (G.bits j)

abbrev Line (G : Grid) (j : Fin G.b) := ∀ k : {k : Fin G.b // k ≠ j}, Cube (G.bits k)

abbrev Choices (G : Grid) := ∀ j, G.Line j → Equiv.Perm (Cube (G.bits j))

def fiberPerm {A B : Type*} (p : B → Equiv.Perm A) : Equiv.Perm (A × B) where
  toFun x := (p x.2 x.1, x.2)
  invFun x := ((p x.2).symm x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp

def stage (G : Grid) (ω : G.Choices) (j : Fin G.b) : Equiv.Perm G.Slot :=
  (Equiv.piSplitAt j (fun k => Cube (G.bits k))).trans
    ((fiberPerm (ω j)).trans (Equiv.piSplitAt j (fun k => Cube (G.bits k))).symm)

def boundary (G : Grid) (ω : G.Choices) (t : ℕ) : Equiv.Perm G.Slot :=
  ((List.ofFn (G.stage ω)).take t).reverse.prod

def sweep (G : Grid) (ω : G.Choices) : Equiv.Perm G.Slot := G.boundary ω G.b

/-- The side lengths are in `[R, R²]`, where the single global scale is `R = 2^r`. -/
def Allowed (G : Grid) (r : ℕ) : Prop := ∀ j, r ≤ G.bits j ∧ G.bits j ≤ 2 * r

/-- Full disjoint paths, including every boundary of the ordered sweep. -/
structure Holes (G : Grid) (h : ℕ) where
  path : Fin h → Fin (G.b + 1) → G.Slot
  disjoint : ∀ t, Function.Injective (fun i => path i t)
  coordinate_step : ∀ i (j : Fin G.b) (k : Fin G.b), k ≠ j →
    path i j.succ k = path i j.castSucc k

namespace Holes

variable {G : Grid} {h : ℕ}

def Compatible (H : G.Holes h) (ω : G.Choices) : Prop :=
  ∀ i (t : Fin (G.b + 1)), G.boundary ω t (H.path i 0) = H.path i t

def Feasible (H : G.Holes h) : Prop := ∃ ω, H.Compatible ω

def lineCount (H : G.Holes h) (j : Fin G.b) (L : G.Line j) : ℕ :=
  (Finset.univ.filter (fun i : Fin h =>
    (fun k : {k : Fin G.b // k ≠ j} => H.path i j.castSucc k) = L)).card

def cost (H : G.Holes h) : ℝ :=
  ∑ j, ∑ L : G.Line j,
    Real.log (((2 ^ G.bits j : ℕ) : ℝ) ^ H.lineCount j L /
      ((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℝ))

/-- The symmetric group on the unmarked input sites. -/
def stabilizer (H : G.Holes h) : Subgroup (Equiv.Perm G.Slot) where
  carrier g := ∀ i, g (H.path i 0) = H.path i 0
  one_mem' _ := rfl
  mul_mem' := by
    intro g g' hg hg' i
    change g (g' (H.path i 0)) = H.path i 0
    rw [hg' i, hg i]
  inv_mem' hg i := (Equiv.symm_apply_eq _).mpr (hg i).symm

def reference (H : G.Holes h) (hf : H.Feasible) : G.Choices := hf.choose

theorem reference_compatible (H : G.Holes h) (hf : H.Feasible) :
    H.Compatible (H.reference hf) := hf.choose_spec

/-- A reference completion identifies the free input and output sites. -/
def residual (H : G.Holes h) (hf : H.Feasible) (ω : {ω : G.Choices // H.Compatible ω}) :
    H.stabilizer :=
  ⟨(G.sweep (H.reference hf))⁻¹ * G.sweep ω.val, by
    intro i
    change (G.sweep (H.reference hf)).symm (G.sweep ω.val (H.path i 0)) = H.path i 0
    apply (Equiv.symm_apply_eq _).mpr
    exact (ω.property i (Fin.last _)).trans ((H.reference_compatible hf i (Fin.last _)).symm)⟩

end Holes

/-- Independent line permutations with law `(1-z) U + z B`. -/
def choiceWeight (G : Grid) (z : ℝ) (ω : G.Choices) : ℝ :=
  ∏ j, ∏ L : G.Line j,
    ((1-z) * (Fintype.card (Equiv.Perm (Cube (G.bits j))) : ℝ)⁻¹ +
      z * binaryLaw (G.bits j) (ω j L))

namespace Holes

variable {G : Grid} {h : ℕ}

def probability (H : G.Holes h) (z : ℝ) : ℝ :=
  ∑ ω : {ω : G.Choices // H.Compatible ω}, G.choiceWeight z ω.val

end Holes

def eventDistance (G : Grid) (E : Finset G.Choices) (z : ℝ) : ℝ :=
  ∑ ω ∈ E, |G.choiceWeight z ω/(∑ v ∈ E, G.choiceWeight z v)-
    G.choiceWeight 0 ω/(∑ v ∈ E, G.choiceWeight 0 v)|

end Grid

structure UnitaryIrrep (Γ : Type*) [Group Γ] where
  dimension : ℕ
  positive : 0 < dimension
  matrix : Γ →* Matrix (Fin dimension) (Fin dimension) ℂ
  unitary : ∀ g, (matrix g).conjTranspose * matrix g = 1
  irreducible : ∀ S : Submodule ℂ (Fin dimension → ℂ),
    (∀ g v, v ∈ S → (matrix g).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤

/-- Unnormalized Schatten `2q` moment, without division by the dimension. -/
def schattenMoment {D : ℕ} (q : ℕ) (K : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  (Matrix.trace ((K.conjTranspose * K) ^ q)).re

namespace Grid.Holes

variable {G : Grid} {h : ℕ}

def conditionalAverage (H : G.Holes h) (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ :=
  (H.probability z : ℂ)⁻¹ •
    ∑ ω : {ω : G.Choices // H.Compatible ω},
      (G.choiceWeight z ω.val : ℂ) • ρ.matrix (H.residual hf ω)

end Grid.Holes

def a : ℝ := 1 / 100
def c0 : ℝ := a / 100
def e0 : ℝ := a / 100
def c (s : ℕ) : ℝ := c0 + 1 / Real.sqrt (Real.log s)
def e (s : ℕ) : ℝ := e0 - 1 / Real.sqrt (Real.log s)

/-- The logarithm of a zero moment is minus infinity. -/
def logMoment (t : ℝ) : EReal := if t = 0 then ⊥ else (Real.log t : EReal)

def ConditionalMain : Prop :=
  ∃ (r q : ℕ) (zStar : ℝ), 1 ≤ r ∧ 1 ≤ q ∧ 0 < zStar ∧ zStar ≤ 1 / ((2 : ℕ) : ℝ) ∧
    ∀ (G : Grid), G.Allowed r → ∀ (h : ℕ) (H : G.Holes h) (hf : H.Feasible),
    ∀ z ∈ Set.Icc 0 zStar, ∀ ρ : UnitaryIrrep H.stabilizer,
      logMoment (schattenMoment q (H.conditionalAverage hf z ρ)) ≤
        ((-c G.size * Real.log ρ.dimension + e G.size * h * Real.log G.size - H.cost : ℝ) : EReal)

def MomentBound (G : Grid) (q : ℕ) (z : ℝ) : Prop :=
  ∀ (h : ℕ) (H : G.Holes h) (hf : H.Feasible) (σ : UnitaryIrrep H.stabilizer),
    schattenMoment q (H.conditionalAverage hf z σ) ≤
      Real.exp (-c G.size*Real.log σ.dimension+e G.size*h*Real.log G.size-H.cost)

def ScaleLarge (r : ℕ) : Prop :=
  1 ≤ r ∧ (2/e0)^2 ≤ (r : ℝ)*Real.log 2 ∧ 4/e0 ≤ (r : ℝ)*Real.log 2

def baseWidth (r : ℕ) : ℝ := ((2^(2*r)).factorial : ℕ)
def baseZeta (r : ℕ) : ℝ := 1/(4*(baseWidth r)^2)

namespace ScalarInduction

structure MainSizeReady (q : ℕ) (s : ℝ) : Prop where
  one : 1 ≤ Real.log s
  sparse : (100004:ℝ)*s^(1-a/4) ≤ s^(1-(1:ℝ)/1600)
  hook : (((2*q+1:ℕ):ℝ)*4+82*c0)*2*s^((4:ℝ)/5+2*a)*Real.log (s+1) ≤ s^((9:ℝ)/10)
  removed : s^((9:ℝ)/10)+s^(1-a/2)*Real.log s ≤ s^(1-a/4)/(20*Real.sqrt (Real.log s))

end ScalarInduction

namespace SparseScalar

def theta : ℝ := 1/1600
def K0 : ℝ := 100000
def B0 : ℕ := 12800
def xi : ℝ := 1/2048000000
def rho : ℝ := 1/32768000000
def q : ℕ := 65536000000

def uniformRate : ℝ := Real.log ((2 : ℕ) : ℝ) + (B0 : ℝ) *
  (K0 + 1 + Real.log ((4 : ℕ) : ℝ) +
    Real.log (((16 : ℕ) : ℝ) * Real.exp ((2 : ℕ) : ℝ)) +
    Real.log (1 + ((16 : ℕ) : ℝ) * Real.exp ((2 : ℕ) : ℝ)))

structure SizeReady (s : ℝ) : Prop where
  two : 2 ≤ s
  logpow : Real.log s ≤ s^(theta/4)
  powtwo : 2 ≤ s^(theta/4)
  powB : (B0+1:ℝ) ≤ s^(theta/2)
  count : 4/s^(1/(4*(B0:ℝ))) ≤ theta/(64*B0)
  absorb : Real.log (1+2*(B0:ℝ))+Real.log 2 ≤ xi*Real.log s
  eta : s^(-xi) ≤ 1/8
  prefactor : uniformRate ≤ xi*Real.log s/16
  logtwo : Real.log 2 ≤ xi*Real.log s/8

structure ScaleReady (r : ℕ) : Prop where
  two : 2 ≤ r
  logone : 1 ≤ (r:ℝ)*Real.log 2
  absorb : 3*Real.log 2+2*(K0+1+Real.log 4) ≤ theta*((r:ℝ)*Real.log 2)/8
  size : ∀ s : ℝ, (2:ℝ)^r ≤ s → SizeReady s

def slack (s : ℝ) : ℝ :=
  if 1 < s then s ^ (-((2 : ℕ) : ℝ) * rho * s) * (s ^ rho - 1) else 1

end SparseScalar

def SparsePerturb (r : ℕ) (zStar : ℝ) : Prop :=
  0 < zStar ∧ zStar ≤ baseZeta r ∧ ∀ G : Grid, G.b ≤ SparseScalar.B0 → G.Allowed r →
    ∀ z ∈ Set.Icc 0 zStar, ∀ E : Finset G.Choices, E.Nonempty →
      G.eventDistance E z < SparseScalar.slack G.size



end CoordinateSweeps
end
end OAI


