-- Prove2me | Definitions.Def_OAIB3Kr008
-- name    : OAIB3Kr008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T16:58:36.633985+00:00
-- url     : https://prove2.me/theorems/a3d13ab0-e631-4abe-bed2-43098aa4f0e1
-- title:
--   Definitions bundle OAIB3Kr008 of the split of OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 223 declarations of OpenAI's Lean: 107 definitions, 4 inductive types or structures, 15 instances and 97 theorems. The definitions and types are `OAI.KirchbergRordam.ContinuousSectionLocality.Square`, `OAI.KirchbergRordam.ContinuousSectionLocality.firstCoord`, `OAI.KirchbergRordam.ContinuousSectionLocality.scalarMap`, `OAI.KirchbergRordam.ContinuousSectionLocality.secondCoord`, `OAI.KirchbergRordam.ContinuousSectionLocality.weight`, `OAI.KirchbergRordam.DiagonalIteration.System`, `OAI.KirchbergRordam.DiagonalIteration.System.flat`, `OAI.KirchbergRordam.DiagonalIteration.System.full`, `OAI.KirchbergRordam.DiagonalIteration.System.unitaryPath`, `OAI.KirchbergRordam.DiagonalIteration.conj`, `OAI.KirchbergRordam.DiagonalIteration.piUnitary`, `OAI.KirchbergRordam.DropChannels.conjugated`, `OAI.KirchbergRordam.DropChannels.leftScalar`, `OAI.KirchbergRordam.DropChannels.rightScalar`, `OAI.KirchbergRordam.EndpointMultiplicity.constHom`, `OAI.KirchbergRordam.EndpointMultiplicity.prodUnitary`, `OAI.KirchbergRordam.FiniteHalfFlipSequence.conj`, `OAI.KirchbergRordam.FourLegSymmetries.Index`, `OAI.KirchbergRordam.FourLegSymmetries.hflip`, `OAI.KirchbergRordam.FourLegSymmetries.kflip`, `OAI.KirchbergRordam.GeneralEndpointMultiplicity.leftExpand`, `OAI.KirchbergRordam.GeneralEndpointMultiplicity.rightExpand`, `OAI.KirchbergRordam.GenericRW.CentralCalculus.center`, `OAI.KirchbergRordam.GenericRW.CentralCalculus.family`, `OAI.KirchbergRordam.GenericRW.CentralCalculus.hom`, `OAI.KirchbergRordam.GenericRW.CentralCalculus.inclusion`, `OAI.KirchbergRordam.GenericRW.ClosedRightRange.embed`, `OAI.KirchbergRordam.GenericRW.ClosedRightRange.hereditary`, `OAI.KirchbergRordam.GenericRW.ClosedRightRange.space`, `OAI.KirchbergRordam.GenericRW.ClosedRightRange.transport`, `OAI.KirchbergRordam.GenericRW.ConeCube.Cube`, `OAI.KirchbergRordam.GenericRW.ConeCube.Fiber`, `OAI.KirchbergRordam.GenericRW.ConeCube.Label`, `OAI.KirchbergRordam.GenericRW.ConeCube.matLeg`, `OAI.KirchbergRordam.GenericRW.ConeModel.Cone`, `OAI.KirchbergRordam.GenericRW.ConeModel.ConeMatrix`, `OAI.KirchbergRordam.GenericRW.ConeModel.M2`, `OAI.KirchbergRordam.GenericRW.ConeModel.coefficients`, `OAI.KirchbergRordam.GenericRW.ConeModel.coneSubalgebra`, `OAI.KirchbergRordam.GenericRW.ConeModel.eval` and 71 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CharacterCriterion_BalancedLimit`, `CharacterCriterion_BalancedSystem`, `CharacterCriterion_ConeCube`, `CharacterCriterion_ConeModel`, `CharacterCriterion_ConePauli`, `CharacterCriterion_CubeCalculus`, `CharacterCriterion_DiagonalIteration`, `CharacterCriterion_EndpointMultiplicity`, `CharacterCriterion_FieldCalculus`, `CharacterCriterion_FlipPath`, `CharacterCriterion_FourLegSymmetries`, `CharacterCriterion_GeneralSystem`, `CharacterCriterion_HereditaryTransport`, `CharacterCriterion_InductiveLimit`, `CharacterCriterion_MatrixPaths`, `CharacterCriterion_MatrixSimplex`, `CharacterCriterion_MultiplicativeChannels`, `CharacterCriterion_NormUltrapower`, `CharacterCriterion_OrderZero`, `CharacterCriterion_Pauli`, `CharacterCriterion_Reindexing`, `CharacterCriterion_SquareZeroCone`, `CharacterCriterion_TensorSections`.
--
--   **Imports.** It imports the published bundle `Def_CharacterCriterion`; the bundle `OAIB3Kr001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIB3Kr010`, `OAIB3Kr011` and `OAIB3Kr012`; the proof of `OAI_KirchbergRordam_PrimeSquareUnitary_exists_half_flip_control`.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr001

section
-- module Solutions.OAIB3_Krc.Compat
attribute [-instance] _root_.OAI.KirchbergRordam.NormUltrapower.quotientNormedRing _root_.OAI.KirchbergRordam.StarCompletion.completionNormedAlgebra _root_.OAI.KirchbergRordam.StarCompletion.completionStar _root_.OAI.KirchbergRordam.StarCompletion.completionStarRing
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Pauli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace KirchbergRordam.Pauli
open scoped Matrix BigOperators Kronecker
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

def e : Fin 4 → M2 := ![1,!![0,1;1,0],!![0,-Complex.I;Complex.I,0],!![1,0;0,-1]]

lemma e_zero : e 0=1 := rfl
lemma e_star (i : Fin 4) : star (e i)=e i := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;> simp [e]
lemma e_square (i : Fin 4) : e i*e i=1 := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [e,Matrix.mul_apply,Fin.sum_univ_two]

lemma trace_mul (i j : Fin 4) : Matrix.trace (e i*e j)=if i=j then 2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [e,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two]

end KirchbergRordam.Pauli

namespace KirchbergRordam.PauliPower
open scoped Matrix BigOperators Kronecker

def Row : ℕ→Type
  | 0 => Fin 2
  | n+1 => Fin 2 × Row n

def Label : ℕ→Type
  | 0 => Fin 4
  | n+1 => Fin 4 × Label n

instance rowFintype : (n : ℕ) → Fintype (Row n)
  | 0 => inferInstanceAs (Fintype (Fin 2))
  | n+1 => letI := rowFintype n; inferInstanceAs (Fintype (Fin 2 × Row n))
instance rowDecidableEq : (n : ℕ) → DecidableEq (Row n)
  | 0 => inferInstanceAs (DecidableEq (Fin 2))
  | n+1 => letI := rowDecidableEq n; inferInstanceAs (DecidableEq (Fin 2 × Row n))
instance labelFintype : (n : ℕ) → Fintype (Label n)
  | 0 => inferInstanceAs (Fintype (Fin 4))
  | n+1 => letI := labelFintype n; inferInstanceAs (Fintype (Fin 4 × Label n))
instance labelDecidableEq : (n : ℕ) → DecidableEq (Label n)
  | 0 => inferInstanceAs (DecidableEq (Fin 4))
  | n+1 => letI := labelDecidableEq n; inferInstanceAs (DecidableEq (Fin 4 × Label n))

abbrev Mat (n : ℕ) := Matrix (Row n) (Row n) ℂ

def e : (n : ℕ) → Label n → Mat n
  | 0,a => Pauli.e a
  | n+1,a => Matrix.kronecker (Pauli.e a.1) (e n a.2)

lemma row_card (n : ℕ) : Fintype.card (Row n)=2^(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Fin 2 × Row n)=_
    simp only [Fintype.card_prod,Fintype.card_fin,ih,pow_succ]
    omega
lemma label_card (n : ℕ) : Fintype.card (Label n)=4^(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Fin 4 × Label n)=_
    simp only [Fintype.card_prod,Fintype.card_fin,ih,pow_succ]
    omega

lemma e_star (n : ℕ) (a : Label n) : star (e n a)=e n a := by
  induction n with
  | zero => exact Pauli.e_star a
  | succ n ih =>
    change (Matrix.kronecker (Pauli.e a.1) (e n a.2)).conjTranspose=_
    dsimp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker]
    change Matrix.kronecker (star (Pauli.e a.1)) (star (e n a.2))=_
    rw [Pauli.e_star,ih]
    rfl

lemma e_square (n : ℕ) (a : Label n) : e n a*e n a=1 := by
  induction n with
  | zero => exact Pauli.e_square a
  | succ n ih =>
    change Matrix.kronecker (Pauli.e a.1) (e n a.2)*Matrix.kronecker (Pauli.e a.1) (e n a.2)=
      (1 : Matrix (Fin 2 × Row n) (Fin 2 × Row n) ℂ)
    dsimp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul,Pauli.e_square,ih,Matrix.one_kronecker_one]

lemma trace_mul (n : ℕ) (a b : Label n) :
    Matrix.trace (e n a*e n b)=if a=b then (2:ℂ)^(n+1) else 0 := by
  induction n with
  | zero =>
    change Matrix.trace (Pauli.e a * Pauli.e b) = if a = b then (2 : ℂ)^1 else 0
    rw [pow_one]
    exact Pauli.trace_mul a b
  | succ n ih =>
    change Matrix.trace (Matrix.kronecker (Pauli.e a.1) (e n a.2)*
      Matrix.kronecker (Pauli.e b.1) (e n b.2))=_
    dsimp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul,Matrix.trace_kronecker,Pauli.trace_mul,ih]
    have hab : a=b ↔ a.1=b.1 ∧ a.2=b.2 := Prod.ext_iff
    by_cases h1 : a.1=b.1 <;> by_cases h2 : a.2=b.2 <;>
      simp [h1,h2,hab,pow_succ,mul_comm]

end KirchbergRordam.PauliPower

namespace KirchbergRordam.PauliSupport
open scoped Matrix Kronecker BigOperators
open PauliPower

def partner (a : Fin 4) : Fin 4 := if a=1 then 2 else 1
lemma anti (a : Fin 4) (ha : a≠0) : Pauli.e (partner a)*Pauli.e a= -(Pauli.e a*Pauli.e (partner a)) := by
  fin_cases a
  · exact (ha rfl).elim
  all_goals
    dsimp [partner,Pauli.e]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Pauli.e,Matrix.mul_apply,Fin.sum_univ_two]

def coord : (n : ℕ)→Label n→Fin (n+1)→Fin 4
  | 0,a,_ => a
  | n+1,a,i => Fin.cases a.1 (fun j=>coord n a.2 j) i

def leg : (n : ℕ)→Fin (n+1)→Pauli.M2→⋆ₐ[ℂ] Mat n
  | 0,_ => StarAlgHom.id ℂ Pauli.M2
  | n+1,i => Fin.cases MatrixTensor.leftMatrixAlgebra
      (fun j=>MatrixTensor.rightMatrixAlgebra.comp (leg n j)) i

lemma anti_leg (n : ℕ) (a : Label n) (j : Fin (n+1)) (hj : coord n a j≠0) :
    leg n j (Pauli.e (partner (coord n a j)))*e n a=
      -(e n a*leg n j (Pauli.e (partner (coord n a j)))) := by
  induction n with
  | zero => exact anti a hj
  | succ n ih =>
    induction j using Fin.cases with
    | zero =>
      change @Eq (Matrix (Fin 2 × Row n) (Fin 2 × Row n) ℂ)
        (Matrix.kronecker (Pauli.e (partner a.1)) 1*Matrix.kronecker (Pauli.e a.1) (e n a.2))
        (-(Matrix.kronecker (Pauli.e a.1) (e n a.2)*Matrix.kronecker (Pauli.e (partner a.1)) 1))
      dsimp only [Matrix.kronecker]
      erw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,anti a.1 hj,one_mul,mul_one ]
      ext r s
      simp [Matrix.kroneckerMap_apply]
      rfl
    | succ j =>
      change @Eq (Matrix (Fin 2 × Row n) (Fin 2 × Row n) ℂ)
        (Matrix.kronecker 1 (leg n j (Pauli.e (partner (coord n a.2 j))))*Matrix.kronecker (Pauli.e a.1) (e n a.2))
        (-(Matrix.kronecker (Pauli.e a.1) (e n a.2)*Matrix.kronecker 1 (leg n j (Pauli.e (partner (coord n a.2 j))))))
      dsimp only [Matrix.kronecker]
      erw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,one_mul,mul_one,ih a.2 j hj ]
      ext r s
      simp [Matrix.kroneckerMap_apply]
      rfl

lemma trace_zero_of_anti {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b e x : Matrix ι ι ℂ) (hb : b*b=1) (he : b*e= -(e*b)) (hx : Commute b x) :
    Matrix.trace (e*x)=0 := by
  have hneg : b*(e*x)*b= -(e*x) := by
    calc
      _ = (b*e)*x*b := by noncomm_ring
      _ = -(e*(b*x)*b) := by rw [he]; noncomm_ring
      _ = -(e*x*(b*b)) := by rw [hx.eq]; noncomm_ring
      _ = -(e*x) := by rw [hb,mul_one]
  have ht : Matrix.trace (b*(e*x)*b)=Matrix.trace (e*x) := by
    rw [mul_assoc,Matrix.trace_mul_comm b,mul_assoc (e*x),hb,mul_one]
  rw [hneg,Matrix.trace_neg] at ht
  linear_combination -ht / 2

end KirchbergRordam.PauliSupport

namespace KirchbergRordam.PauliPower

def zeroLabel : (n : ℕ) → Label n
  | 0 => (0 : Fin 4)
  | n+1 => (0, zeroLabel n)

lemma e_zeroLabel (n : ℕ) : e n (zeroLabel n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Matrix.kronecker (Pauli.e 0) (e n (zeroLabel n)) = _
    rw [Pauli.e_zero, ih]
    exact Matrix.one_kronecker_one

lemma coord_zero_iff (n : ℕ) (a : Label n) :
    (∀ j, PauliSupport.coord n a j = 0) ↔ a = zeroLabel n := by
  induction n with
  | zero =>
    constructor
    · intro h; exact h 0
    · intro h j; exact h
  | succ n ih =>
    constructor
    · intro h
      have h0 := h 0
      have ht : ∀ j, PauliSupport.coord n a.2 j = 0 := fun j => h j.succ
      exact Prod.ext h0 ((ih a.2).mp ht)
    · intro h
      subst a
      intro j
      induction j using Fin.cases with
      | zero => rfl
      | succ j => exact (ih (zeroLabel n)).mpr rfl j

lemma exists_anti (n : ℕ) (a : Label n) (ha : a ≠ zeroLabel n) :
    ∃ b : Mat n, b*b=1 ∧ b*e n a = -(e n a*b) := by
  have h : ¬ ∀ j, PauliSupport.coord n a j = 0 :=
    fun h => ha ((coord_zero_iff n a).mp h)
  obtain ⟨j,hj⟩ := not_forall.mp h
  refine ⟨PauliSupport.leg n j (Pauli.e (PauliSupport.partner (PauliSupport.coord n a j))), ?_,
    PauliSupport.anti_leg n a j hj⟩
  rw [← map_mul, Pauli.e_square, map_one]

end KirchbergRordam.PauliPower

namespace KirchbergRordam.GenericRW
class Size where
  n : ℕ
  positive : 0 < n

section
open scoped Matrix BigOperators
variable [Size]
local notation "N" => Size.n


class PauliData where
  Label : Type
  [finite : Fintype Label]
  [decidable : DecidableEq Label]
  zero : Label
  e : Label → Matrix (Fin N) (Fin N) ℂ
  e_zero : e zero = 1
  e_star : ∀ a, star (e a) = e a
  e_square : ∀ a, e a * e a = 1
  trace_mul : ∀ a b, Matrix.trace (e a * e b) = if a=b then (N:ℂ) else 0
  card : Fintype.card Label = N*N
  anti : ∀ a, a ≠ zero → ∃ b : Matrix (Fin N) (Fin N) ℂ,
    b*b=1 ∧ b*e a= -(e a*b)
  two_le : 2 ≤ N
attribute [instance_reducible] PauliData.finite PauliData.decidable
attribute [instance] PauliData.finite PauliData.decidable
instance instZeroLabel [PauliData] : Zero PauliData.Label := ⟨PauliData.zero⟩

omit [Size] in
abbrev powerSize (k : ℕ) : Size := ⟨2^(k+1), by positivity⟩

omit [Size] in
def rowEquiv (k : ℕ) : _root_.OAI.KirchbergRordam.PauliPower.Row k ≃ Fin (2^(k+1)) :=
  (Fintype.equivFin _).trans (finCongr (PauliPower.row_card k))

omit [Size] in
def rowReindex (k : ℕ) : _root_.OAI.KirchbergRordam.PauliPower.Mat k ≃⋆ₐ[ℂ]
    Matrix (Fin (2^(k+1))) (Fin (2^(k+1))) ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ (rowEquiv k) with
    map_smul' := fun c x => rfl
    map_star' := fun x => by
      exact (Matrix.conjTranspose_reindex (rowEquiv k) (rowEquiv k) x).symm }

omit [Size] in
lemma reindex_trace (k : ℕ) (x : _root_.OAI.KirchbergRordam.PauliPower.Mat k) :
    Matrix.trace (rowReindex k x) = Matrix.trace x := by
  change (∑ i, x ((rowEquiv k).symm i) ((rowEquiv k).symm i)) = ∑ i, x i i
  exact (rowEquiv k).symm.sum_comp (fun i => x i i)

end
open scoped Matrix BigOperators

@[instance_reducible] def powerPauliData (k : ℕ) : @PauliData (powerSize k) := by
  letI : Size := powerSize k
  exact {
    Label := _root_.OAI.KirchbergRordam.PauliPower.Label k
    zero := PauliPower.zeroLabel k
    e := fun a => rowReindex k (_root_.OAI.KirchbergRordam.PauliPower.e k a)
    e_zero := by rw [PauliPower.e_zeroLabel, map_one]
    e_star a := by rw [← map_star, PauliPower.e_star]
    e_square a := by rw [← map_mul, PauliPower.e_square, map_one]
    trace_mul a b := by
      change Matrix.trace (rowReindex k (_root_.OAI.KirchbergRordam.PauliPower.e k a) * rowReindex k (_root_.OAI.KirchbergRordam.PauliPower.e k b)) =
        if a=b then ((2^(k+1):ℕ):ℂ) else 0
      rw [← map_mul, reindex_trace, PauliPower.trace_mul, Nat.cast_pow, Nat.cast_ofNat]
    card := by
      rw [PauliPower.label_card]
      change 4^(k+1) = 2^(k+1)*2^(k+1)
      rw [← mul_pow]
      norm_num
    anti a ha := by
      obtain ⟨b,hb,he⟩ := PauliPower.exists_anti k a ha
      refine ⟨rowReindex k b, ?_, ?_⟩
      · rw [← map_mul, hb, map_one]
      · rw [← map_mul, he, map_neg, map_mul]
    two_le := by
      change 2 ≤ 2^(k+1)
      calc
        2 = 2^1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  }
end KirchbergRordam.GenericRW

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SquareZeroCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace


variable [instSize : KirchbergRordam.GenericRW.Size]

namespace KirchbergRordam.GenericRW

namespace IntervalCalculus
open scoped ComplexOrder


def coord : C(unitInterval, ℂ) := ⟨fun t => (t : ℝ), by fun_prop⟩
omit instSize in
@[simp] lemma coord_apply
    [KirchbergRordam.GenericRW.Size]
    (t : unitInterval) : coord t = (t : ℝ) := rfl

end IntervalCalculus
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.IntervalCalculus
open scoped ContinuousMapZero
def coordMul : C(unitInterval, ℂ) →ₗ[ℂ] C(unitInterval, ℂ)₀ where
  toFun f := ⟨coord * f, by simp [coord]⟩
  map_add' f g := by ext t; simp [mul_add]
  map_smul' c f := by ext t; simp [mul_comm, mul_left_comm]

omit instSize in
@[simp] lemma coordMul_apply
    [KirchbergRordam.GenericRW.Size]
    (f : C(unitInterval, ℂ)) (t : unitInterval) :
    coordMul f t = coord t * f t := rfl

end KirchbergRordam.GenericRW.IntervalCalculus

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_HereditaryTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW
namespace ConeModel
open scoped ContinuousMapZero BigOperators ComplexOrder
abbrev M2 := CStarMatrix (Fin rankNum) (Fin rankNum) ℂ
abbrev ConeMatrix := Matrix (Fin rankNum) (Fin rankNum) C(unitInterval, ℂ)₀

def eval (t : unitInterval) : C(unitInterval, M2) →⋆ₐ[ℂ] M2 where
  toFun f := f t
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl


def coneSubalgebra : StarSubalgebra ℂ C(unitInterval, M2) :=
  (⊥ : StarSubalgebra ℂ M2).comap (eval 0)

abbrev Cone := coneSubalgebra

instance instFiniteDimensionalComplexM2 : FiniteDimensional ℂ M2 :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix (Fin rankNum) (Fin rankNum) ℂ))

instance coneClosed : IsClosed (coneSubalgebra : Set C(unitInterval, M2)) :=
  ((⊥ : StarSubalgebra ℂ M2).toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (0 : unitInterval))


def coefficients : ConeMatrix →⋆ₙₐ[ℂ] C(unitInterval, M2) where
  toFun m := ⟨fun t => CStarMatrix.ofMatrix (fun i j => m i j t), by
    apply CStarMatrix.ofMatrixL.continuous.comp
    fun_prop⟩
  map_zero' := by ext t i j; rfl
  map_add' _ _ := by ext t i j; rfl
  map_smul' _ _ := by ext t i j; rfl
  map_mul' m n := by
    ext t i j
    change (∑ k, m i k * n k j) t = ∑ k, m i k t * n k j t
    simp
  map_star' _ := by ext t i j; rfl

@[simp] lemma coefficients_apply (m : ConeMatrix) (t : unitInterval) (i j : Fin rankNum) :
    coefficients m t i j = m i j t := rfl

end ConeModel

open scoped ContinuousMapZero BigOperators ComplexOrder
end KirchbergRordam.GenericRW


namespace KirchbergRordam.GenericRW
namespace ClosedRightRange
variable {A : Type*} [CStarAlgebra A]


def space (a : A) : Submodule ℂ A :=
  (LinearMap.range (LinearMap.mulLeft ℂ a)).topologicalClosure

omit instSize in
lemma mem_space.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    (a x : A) : a * x ∈ space a :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)

omit instSize in
lemma closed.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    (a : A) : IsClosed (space a : Set A) :=
  Submodule.isClosed_topologicalClosure _

def embed (a : A) : A →ₗ[ℂ] space a :=
  (LinearMap.mulLeft ℂ a).codRestrict _ (mem_space a)

@[simp] lemma embed_val (a x : A) : (embed a x : A) = a * x := rfl

lemma dense (a : A) : DenseRange (embed a) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro x
  rw [closure_subtype]
  change (x : A) ∈ closure (Subtype.val '' Set.range (embed a))
  have h : Subtype.val '' Set.range (embed a) = Set.range (fun z : A => a * z) := by
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨embed a z, ⟨z, rfl⟩, rfl⟩
  rw [h]
  exact x.property

omit instSize in
lemma norm_mul_eq.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a b : A} (h : star a * a = star b * b) (x : A) :
    ‖a * x‖ = ‖b * x‖ := by
  have hh : ‖a * x‖ ^ 2 = ‖b * x‖ ^ 2 := by
    simp only [pow_two, ← CStarRing.norm_star_mul_self, star_mul]
    congr 1
    calc
      _ = star x * (star a * a) * x := by noncomm_ring
      _ = star x * (star b * b) * x := by rw [h]
      _ = _ := by noncomm_ring
  nlinarith [norm_nonneg (a*x), norm_nonneg (b*x)]


def transport (a b : A) : space a →L[ℂ] A :=
  (LinearMap.mulLeft ℂ b).extendOfNorm (embed a)

lemma transport_embed {a b : A} (h : star a * a = star b * b) (x : A) :
    transport a b (embed a x) = b * x := by
  exact LinearMap.extendOfNorm_eq (dense a)
    ⟨1, fun x => by change ‖b * x‖ ≤ 1 * ‖a * x‖; simpa only [one_mul] using (norm_mul_eq h x).ge⟩ x

lemma transport_inner {a b : A} (h : star a * a = star b * b)
    (x y : space a) : star (transport a b x) * transport a b y = star (x : A) * y := by
  refine (dense a).induction_on₂ (p := fun x y =>
    star (transport a b x) * transport a b y = star (x : A) * y)
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro x y
  rw [transport_embed h, transport_embed h]
  simp only [embed_val, star_mul]
  calc
    _ = star x * (star b * b) * y := by noncomm_ring
    _ = star x * (star a * a) * y := by rw [h]
    _ = _ := by noncomm_ring

lemma transport_mem {a b : A} (h : star a * a = star b * b) (x : space a) :
    transport a b x ∈ space b := by
  refine (dense a).induction_on x ((closed b).preimage (by fun_prop)) ?_
  intro y
  rw [transport_embed h]
  exact mem_space b y

lemma mul_right_mem {a z : A} (hz : z ∈ space a) (x : A) : z * x ∈ space a := by
  have hh (z : space a) : (z : A) * x ∈ space a := by
    refine (dense a).induction_on z ((closed a).preimage (by fun_prop)) ?_
    intro y
    change (a * y) * x ∈ space a
    rw [mul_assoc]
    exact mem_space a (y*x)
  exact hh ⟨z, hz⟩

lemma space_le {a b : A} (ha : a ∈ space b) : space a ≤ space b := by
  apply Submodule.topologicalClosure_minimal _ ?_ (closed b)
  rintro z ⟨x, rfl⟩
  exact mul_right_mem ha x

lemma space_mul_le (a b : A) : space (a*b) ≤ space a := space_le (mem_space a b)


def hereditary (b : A) : Set A := closure (Set.range (fun x : A => b * x * b))

lemma self_mul_star_mem_hereditary {b z : A} (hb : IsSelfAdjoint b) (hz : z ∈ space b) :
    z * star z ∈ hereditary b := by
  have hh (z : space b) : (z : A) * star (z : A) ∈ hereditary b := by
    refine (dense b).induction_on z (isClosed_closure.preimage (by fun_prop)) ?_
    intro x
    apply subset_closure
    refine ⟨x * star x, ?_⟩
    change b * (x * star x) * b = b * x * star (b*x)
    rw [star_mul, hb.star_eq]
    noncomm_ring
  exact hh ⟨z, hz⟩

end ClosedRightRange
end KirchbergRordam.GenericRW
namespace KirchbergRordam.GenericRW.HereditaryTransport
open ClosedRightRange
variable {A : Type*} [CStarAlgebra A]


def raw (a : A) (ha : IsSelfAdjoint a) : NonUnitalStarSubalgebra ℂ A where
  carrier := Set.range (fun x : A => a*x*a)
  zero_mem' := ⟨0,by simp⟩
  add_mem' := by rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩; exact ⟨x+y,by noncomm_ring⟩
  mul_mem' := by rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩; exact ⟨x*a*a*y,by noncomm_ring⟩
  smul_mem' := by rintro c _ ⟨x,rfl⟩; exact ⟨c • x,by simp only [mul_smul_comm,smul_mul_assoc]⟩
  star_mem' := by rintro _ ⟨x,rfl⟩; exact ⟨star x,by simp only [star_mul,ha.star_eq]; noncomm_ring⟩

abbrev corner (a : A) (ha : IsSelfAdjoint a) := (raw a ha).topologicalClosure

lemma in_space {a : A} {ha : IsSelfAdjoint a} {x : A} (hx : x ∈ corner a ha) : x ∈ space a := by
  apply closure_minimal (s := Set.range (fun y : A => a*y*a)) ?_ (closed a) hx
  rintro _ ⟨y,rfl⟩
  change a*y*a ∈ space a
  rw [mul_assoc]
  exact mem_space a (y*a)

variable {a v : A} (ha : IsSelfAdjoint a) (hv : star a*a=star v*v)


def left (x : corner a ha) : A := transport a v ⟨x,in_space x.property⟩

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW
namespace Vanish
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]


def algebra (S : Set X) : NonUnitalStarSubalgebra ℂ C(X,ℂ) where
  carrier := {f | ∀ t ∈ S, f t = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg t ht; simp [hf t ht,hg t ht]
  mul_mem' := by intro f g hf hg t ht; simp [hf t ht,hg t ht]
  smul_mem' := by intro z f hf t ht; simp [hf t ht]
  star_mem' := by intro f hf t ht; simp [hf t ht]

abbrev Functions (S : Set X) := algebra S


def multiplier (p : C(X,ℂ)) : C(X,ℂ) →ₗ[ℂ] Functions {t | p t = 0} where
  toFun f := ⟨p*f, by intro t ht; simp [show p t=0 from ht]⟩
  map_add' f g := by ext t; simp [mul_add]
  map_smul' z f := by ext t; simp

omit [CompactSpace X] [T2Space X] in
omit instSize in
@[simp] lemma multiplier_apply.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {X : Type contextLevel1}
    [TopologicalSpace X]
    (p f : C(X,ℂ)) (t : X) : (multiplier p f : C(X,ℂ)) t = p t*f t := rfl


end Vanish
end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_ConeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]


namespace KirchbergRordam.GenericRW.ConeModel
open scoped ComplexOrder ContinuousMapZero BigOperators
open IntervalCalculus HereditaryTransport

instance coneSubringClass : SubringClass
    (StarSubalgebra ℂ C(unitInterval,M2)) C(unitInterval,M2) :=
  StarSubalgebra.subringClass (R := ℂ) (A := C(unitInterval,M2))

instance instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone : CStarAlgebra Cone := StarSubalgebra.cstarAlgebra coneSubalgebra

def scalar : C(unitInterval,ℂ) →⋆ₐ[ℂ] Cone where
  toFun f := ⟨⟨fun t => algebraMap ℂ M2 (f t),by fun_prop⟩,by
    change algebraMap ℂ M2 (f 0) ∈ (⊥ : StarSubalgebra ℂ M2)
    exact StarSubalgebra.algebraMap_mem _ (f 0)⟩
  map_zero' := by apply Subtype.ext; apply ContinuousMap.ext; intro t; exact map_zero (algebraMap ℂ M2)
  map_one' := by apply Subtype.ext; apply ContinuousMap.ext; intro t; exact map_one (algebraMap ℂ M2)
  map_add' f g := by apply Subtype.ext; apply ContinuousMap.ext; intro t; exact map_add (algebraMap ℂ M2) (f t) (g t)
  map_mul' f g := by apply Subtype.ext; apply ContinuousMap.ext; intro t; exact map_mul (algebraMap ℂ M2) (f t) (g t)
  commutes' c := by ext t; rfl
  map_star' f := by apply Subtype.ext; apply ContinuousMap.ext; intro t; exact map_star (StarAlgHom.ofId ℂ M2) (f t)

@[simp] lemma scalar_apply (f : C(unitInterval,ℂ)) (t : unitInterval) :
    (scalar f : C(unitInterval,M2)) t=algebraMap ℂ M2 (f t) := rfl

end KirchbergRordam.GenericRW.ConeModel

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FlipPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]

namespace KirchbergRordam.GenericRW.RWFunctions

def realG : C(unitInterval,ℝ) := ⟨fun t => min 1 (3*(1-(t:ℝ))),by fun_prop⟩
def g : C(unitInterval,ℂ) := ⟨fun t => (realG t : ℂ),by fun_prop⟩
def q : C(unitInterval,ℂ) := ⟨fun t => (Real.sqrt (realG t) : ℂ),by fun_prop⟩

def realJ : C(unitInterval,ℝ) := ⟨fun t => (max (t:ℝ) (2/3))⁻¹,
  Continuous.inv₀ (by fun_prop) (fun _ => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<2/3) (le_max_right _ _)))⟩
def j : C(unitInterval,ℂ) := ⟨fun t => (realJ t : ℂ),by fun_prop⟩

omit instSize in
@[simp] lemma g_zero
    [KirchbergRordam.GenericRW.Size]
    : g 0=1 := by norm_num [g,realG]
omit instSize in
@[simp] lemma g_one
    [KirchbergRordam.GenericRW.Size]
    : g 1=0 := by norm_num [g,realG]
omit instSize in
@[simp] lemma q_one
    [KirchbergRordam.GenericRW.Size]
    : q 1=0 := by norm_num [q,realG]
omit instSize in
@[simp] lemma j_one
    [KirchbergRordam.GenericRW.Size]
    : j 1=1 := by norm_num [j,realJ]

end KirchbergRordam.GenericRW.RWFunctions
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_OrderZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW.OrderZero
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


structure WeightedUnits (ι A : Type*) [Fintype ι] [DecidableEq ι]
    [CStarAlgebra A] [PartialOrder A] where
  h : A
  x : ι → ι → A
  nonneg : 0 ≤ h
  norm_le : ‖h‖ ≤ 1
  star_x : ∀ i j, star (x i j) = x j i
  mul_x : ∀ i j k l, x i j * x k l = if j = k then h * x i l else 0
  diagonal : ∑ i, x i i = h

namespace WeightedUnits
variable (W : WeightedUnits ι A)


def linear : Matrix ι ι ℂ →ₗ[ℂ] A where
  toFun m := ∑ i, ∑ j, m i j • W.x i j
  map_add' m n := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c m := by simp [Finset.smul_sum, smul_smul]

omit [StarOrderedRing A] in
omit instSize in
@[simp] lemma linear_single.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    (W : KirchbergRordam.GenericRW.OrderZero.WeightedUnits ι A)
    (i j : ι) (z : ℂ) :
    W.linear (Matrix.single i j z) = z • W.x i j := by
  simp [linear, Matrix.single, ite_and]

end WeightedUnits
end KirchbergRordam.GenericRW.OrderZero

namespace KirchbergRordam.GenericRW.ClosedRightRange
variable {A : Type*} [CStarAlgebra A]
lemma transport_right {a b : A} (h : star a*a=star b*b) (x : space a) (y : A) :
    transport a b ⟨(x:A)*y,mul_right_mem x.property y⟩=transport a b x*y := by
  refine (dense a).induction_on x (isClosed_eq
    ((transport a b).continuous.comp ((continuous_subtype_val.mul continuous_const).subtype_mk _))
    ((transport a b).continuous.mul continuous_const)) ?_
  intro x
  have he : (⟨(embed a x:A)*y,mul_right_mem (embed a x).property y⟩ : space a)=embed a (x*y) :=
    Subtype.ext (mul_assoc a x y)
  rw [he,transport_embed h,transport_embed h,mul_assoc]
end KirchbergRordam.GenericRW.ClosedRightRange

namespace KirchbergRordam.GenericRW.HereditaryTransport
open scoped BigOperators CStarAlgebra
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {a : A} (ha : IsSelfAdjoint a) (s : ι → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)


def frame (K : Matrix ι ι (corner a ha)) (i : ι) : A :=
  ∑ j,left (v := s j) ha (K j i)

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW.HereditaryTransport
open scoped BigOperators CStarAlgebra
variable {A : Type*} [CStarAlgebra A]
variable {a : A} (ha : IsSelfAdjoint a) (s : Fin rankNum → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)
variable (hz : ∀ i,a*s i=0)
variable (K : Matrix (Fin rankNum) (Fin rankNum) (corner a ha))
variable (h q : corner a ha) (hq : star q=q) (hqq : q*q=h)
variable (hK : star K*K=Matrix.diagonal (fun _ => h))
variable (hK' : K*star K=Matrix.diagonal (fun _ => h))

def triple : Fin (rankNum+1) → A := Fin.lastCases (q:A) (fun i => star (frame ha s K i))

@[simp] lemma triple_last : triple ha s K q (Fin.last rankNum) = (q:A) := by simp [triple]
@[simp] lemma triple_castSucc (i : Fin rankNum) : triple ha s K q i.castSucc = star (frame ha s K i) := by simp [triple]

end KirchbergRordam.GenericRW.HereditaryTransport
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FieldCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n



namespace KirchbergRordam.GenericRW

open scoped Matrix Kronecker ComplexOrder

abbrev M2 := CStarMatrix (Fin rankNum) (Fin rankNum) ℂ
abbrev M3 := CStarMatrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ
abbrev M6 := CStarMatrix (Fin rankNum × Fin (rankNum+1)) (Fin rankNum × Fin (rankNum+1)) ℂ


def leftMatrixAlgebra : Matrix (Fin rankNum) (Fin rankNum) ℂ →⋆ₐ[ℂ]
    Matrix (Fin rankNum × Fin (rankNum+1)) (Fin rankNum × Fin (rankNum+1)) ℂ where
  toFun a := a ⊗ₖ (1 : Matrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.add_kronecker _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul a b
      (1 : Matrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ) (1 : Matrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ)
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  map_star' a := by
    change aᴴ ⊗ₖ (1 : Matrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ) = (a ⊗ₖ 1)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]


def rightMatrixAlgebra : Matrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ →⋆ₐ[ℂ]
    Matrix (Fin rankNum × Fin (rankNum+1)) (Fin rankNum × Fin (rankNum+1)) ℂ where
  toFun a := (1 : Matrix (Fin rankNum) (Fin rankNum) ℂ) ⊗ₖ a
  map_zero' := Matrix.kronecker_zero _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.kronecker_add _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul
      (1 : Matrix (Fin rankNum) (Fin rankNum) ℂ) (1 : Matrix (Fin rankNum) (Fin rankNum) ℂ) a b
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]
  map_star' a := by
    change (1 : Matrix (Fin rankNum) (Fin rankNum) ℂ) ⊗ₖ aᴴ = (1 ⊗ₖ a)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]


def leftMatrix : M2 →⋆ₐ[ℂ] M6 :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (leftMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)


def rightMatrix : M3 →⋆ₐ[ℂ] M6 :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (rightMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)


def matrixEval (t : unitInterval) : C(unitInterval, M6) →⋆ₐ[ℂ] M6 where
  toFun f := f t
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl


def dimensionDropSubalgebra : StarSubalgebra ℂ C(unitInterval, M6) :=
  leftMatrix.range.comap (matrixEval 0) ⊓ rightMatrix.range.comap (matrixEval 1)


abbrev DimensionDrop23 := dimensionDropSubalgebra

@[ext]
theorem drop_ext {f g : DimensionDrop23}
    (h : ∀ t, (f : C(unitInterval, M6)) t = (g : C(unitInterval, M6)) t) : f = g := by
  apply Subtype.ext
  exact ContinuousMap.ext h

end KirchbergRordam.GenericRW

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_ConePauli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


variable [instPauliData : KirchbergRordam.GenericRW.PauliData]
namespace KirchbergRordam.GenericRW.Pauli
open scoped Matrix BigOperators Kronecker
abbrev Label := PauliData.Label
abbrev M2 := Matrix (Fin rankNum) (Fin rankNum) ℂ
abbrev e : Label → M2 := PauliData.e
lemma e_zero : e (0:Label)=1 := PauliData.e_zero
end KirchbergRordam.GenericRW.Pauli

namespace KirchbergRordam.GenericRW.PauliPower
open scoped Matrix BigOperators Kronecker

def Row : ℕ→Type
  | 0 => Fin rankNum
  | n+1 => Fin rankNum × Row n

def Label : ℕ→Type
  | 0 => Pauli.Label
  | n+1 => Pauli.Label × Label n

instance rowFintype : (n : ℕ) → Fintype (Row n)
  | 0 => inferInstanceAs (Fintype (Fin rankNum))
  | n+1 => letI := rowFintype n; inferInstanceAs (Fintype (Fin rankNum × Row n))
instance rowDecidableEq : (n : ℕ) → DecidableEq (Row n)
  | 0 => inferInstanceAs (DecidableEq (Fin rankNum))
  | n+1 => letI := rowDecidableEq n; inferInstanceAs (DecidableEq (Fin rankNum × Row n))

abbrev Mat (n : ℕ) := Matrix (Row n) (Row n) ℂ

def e : (n : ℕ) → Label n → Mat n
  | 0,a => Pauli.e a
  | n+1,a => Matrix.kronecker (Pauli.e a.1) (e n a.2)

def coeff (n : ℕ) (a : Label n) : Mat n →ₗ[ℂ] ℂ :=
  ((rankNum:ℂ)^(n+1))⁻¹ • (Matrix.traceLinearMap (Row n) ℂ ℂ).comp (LinearMap.mulLeft ℂ (e n a))
lemma coeff_apply (n : ℕ) (a : Label n) (x : Mat n) :
    coeff n a x=((rankNum:ℂ)^(n+1))⁻¹*Matrix.trace (e n a*x) := rfl

abbrev CMat (n : ℕ) := CStarMatrix (Row n) (Row n) ℂ
instance instFiniteDimensionalComplexCMat (n : ℕ) : FiniteDimensional ℂ (CMat n) :=
  inferInstanceAs (FiniteDimensional ℂ (Mat n))
def ccoeff (n : ℕ) (a : Label n) : CMat n →L[ℂ] ℂ :=
  ((coeff n a).comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toAlgEquiv.toLinearMap).toContinuousLinearMap
end KirchbergRordam.GenericRW.PauliPower

namespace KirchbergRordam.GenericRW.MatrixTensor
open scoped Matrix Kronecker
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
abbrev Mat (ι : Type*) := CStarMatrix ι ι ℂ

def leftMatrixAlgebra : Matrix ι ι ℂ →⋆ₐ[ℂ]
    Matrix (ι × κ) (ι × κ) ℂ where
  toFun a := a ⊗ₖ (1 : Matrix κ κ ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.add_kronecker _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul a b
      (1 : Matrix κ κ ℂ) (1 : Matrix κ κ ℂ)
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  map_star' a := by
    change aᴴ ⊗ₖ (1 : Matrix κ κ ℂ) = (a ⊗ₖ 1)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]


def rightMatrixAlgebra : Matrix κ κ ℂ →⋆ₐ[ℂ]
    Matrix (ι × κ) (ι × κ) ℂ where
  toFun a := (1 : Matrix ι ι ℂ) ⊗ₖ a
  map_zero' := Matrix.kronecker_zero _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.kronecker_add _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul
      (1 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) a b
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]
  map_star' a := by
    change (1 : Matrix ι ι ℂ) ⊗ₖ aᴴ = (1 ⊗ₖ a)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]


def leftMatrix : Mat ι →⋆ₐ[ℂ] Mat (ι×κ) :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (leftMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)


def rightMatrix : Mat κ →⋆ₐ[ℂ] Mat (ι×κ) :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (rightMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)


end KirchbergRordam.GenericRW.MatrixTensor
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_CubeCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW.JointCalculus
open WeakDual
variable {S : Type*} [CommCStarAlgebra S]
variable {I X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable (φ : I → C(X,ℂ) →⋆ₐ[ℂ] S)

def coordinates : C(characterSpace ℂ S,I→X) where
  toFun χ i := (CharacterSpace.homeoEval X ℂ).symm (CharacterSpace.compContinuousMap (φ i) χ)
  continuous_toFun := continuous_pi fun i => (CharacterSpace.homeoEval X ℂ).symm.continuous.comp
    (CharacterSpace.compContinuousMap (φ i)).continuous

def hom : C(I→X,ℂ) →⋆ₐ[ℂ] S :=
  (gelfandStarTransform S).symm.toStarAlgHom.comp ((coordinates φ).compStarAlgHom' ℂ ℂ)

def coordinate (i : I) (f : C(X,ℂ)) : C(I→X,ℂ) := f.comp ⟨fun t => t i,continuous_apply i⟩

omit instSize instPauliData in
lemma hom_coordinate.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {S : Type contextLevel1}
    [CommCStarAlgebra S]
    {I : Type contextLevel2}
    {X : Type contextLevel3}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    (φ : I → C(X, ℂ) →⋆ₐ[ℂ] S)
    (i : I) (f : C(X,ℂ)) : hom φ (coordinate i f)=φ i f := by
  apply (gelfandStarTransform S).injective
  change gelfandStarTransform S ((gelfandStarTransform S).symm _) = _
  rw [StarAlgEquiv.apply_symm_apply]
  ext χ
  change f ((CharacterSpace.homeoEval X ℂ).symm (CharacterSpace.compContinuousMap (φ i) χ)) = χ (φ i f)
  have h := congrArg (fun ψ : characterSpace ℂ C(X,ℂ) => ψ f)
    ((CharacterSpace.homeoEval X ℂ).apply_symm_apply (CharacterSpace.compContinuousMap (φ i) χ))
  exact h

end KirchbergRordam.GenericRW.JointCalculus

namespace KirchbergRordam.GenericRW.CentralCalculus
variable (A : Type*) [CStarAlgebra A]
def center : StarSubalgebra ℂ A := StarSubalgebra.centralizer ℂ Set.univ
instance centerClosed : IsClosed (center A : Set A) := by
  change IsClosed (Set.univ ∪ star Set.univ).centralizer
  exact Set.isClosed_centralizer _
instance centerComm : CommCStarAlgebra (center A) where
  mul_comm a b := Subtype.ext (((StarSubalgebra.mem_centralizer_iff ℂ).mp b.property) a.1 (Set.mem_univ _)).1

def inclusion : center A →⋆ₐ[ℂ] A := (center A).subtype
variable {A}
omit instSize instPauliData in
lemma mem_center.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a : A} (ha : ∀ b,Commute a b) : a∈center A := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro b _
  exact ⟨(ha b).eq.symm,(ha (star b)).eq.symm⟩
omit instSize instPauliData in
lemma commute.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    (a : center A) (b : A) : Commute (a:A) b :=
  (((StarSubalgebra.mem_centralizer_iff ℂ).mp a.property) b (Set.mem_univ _)).1.symm

variable {I X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable (φ : I→C(X,ℂ)→⋆ₐ[ℂ] A) (hc : ∀ i f a,Commute (φ i f) a)
def family (i : I) : C(X,ℂ) →⋆ₐ[ℂ] center A :=
  (φ i).codRestrict (center A) fun f => mem_center (hc i f)
def hom : C(I→X,ℂ) →⋆ₐ[ℂ] A :=
  (inclusion A).comp (JointCalculus.hom (family φ hc))
lemma hom_coordinate (i : I) (f : C(X,ℂ)) :
    hom φ hc (JointCalculus.coordinate i f)=φ i f := by
  change ((JointCalculus.hom (family φ hc) _ : center A):A)=_
  rw [JointCalculus.hom_coordinate]
  rfl
lemma hom_commute (f : C(I→X,ℂ)) (a : A) : Commute (hom φ hc f) a := commute _ _
end KirchbergRordam.GenericRW.CentralCalculus

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_ConeCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW.ConeCube
open scoped CStarAlgebra BigOperators ComplexOrder
open ConeModel
abbrev Cube (n : ℕ) := Fin (n+1)→unitInterval
abbrev Fiber (n : ℕ) := PauliPower.CMat n
abbrev Label (n : ℕ) := PauliPower.Label n

def matLeg : (n : ℕ)→Fin (n+1)→M2→⋆ₐ[ℂ] Fiber n
  | 0,_ => StarAlgHom.id ℂ M2
  | n+1,i => Fin.cases MatrixTensor.leftMatrix
      (fun j=>MatrixTensor.rightMatrix.comp (matLeg n j)) i

end KirchbergRordam.GenericRW.ConeCube


namespace KirchbergRordam.GenericRW.PauliSupport
open scoped Matrix Kronecker BigOperators
open KirchbergRordam.GenericRW.PauliPower

def coord : (n : ℕ)→Label n→Fin (n+1)→Pauli.Label
  | 0,a,_ => a
  | n+1,a,i => Fin.cases a.1 (fun j=>coord n a.2 j) i

def leg : (n : ℕ)→Fin (n+1)→Pauli.M2→⋆ₐ[ℂ] Mat n
  | 0,_ => StarAlgHom.id ℂ Pauli.M2
  | n+1,i => Fin.cases MatrixTensor.leftMatrixAlgebra
      (fun j=>MatrixTensor.rightMatrixAlgebra.comp (leg n j)) i

lemma anti_leg (n : ℕ) (a : Label n) (j : Fin (n+1)) (b : Pauli.M2)
    (he : b*Pauli.e (coord n a j) = -(Pauli.e (coord n a j)*b)) :
    leg n j b*e n a = -(e n a*leg n j b) := by
  induction n with
  | zero => exact he
  | succ n ih =>
    induction j using Fin.cases with
    | zero =>
      change b*Pauli.e a.1 = -(Pauli.e a.1*b) at he
      have result : (Matrix.kronecker b 1*Matrix.kronecker (Pauli.e a.1) (e n a.2) :
        Matrix (Fin rankNum × Row n) (Fin rankNum × Row n) ℂ) =
        -(Matrix.kronecker (Pauli.e a.1) (e n a.2)*Matrix.kronecker b 1) := by
        dsimp only [Matrix.kronecker]
        rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,he,one_mul,mul_one]
        ext row col
        simp [Matrix.kroneckerMap_apply]
      exact result
    | succ j =>
      have result : (Matrix.kronecker 1 (leg n j b)*Matrix.kronecker (Pauli.e a.1) (e n a.2) :
        Matrix (Fin rankNum × Row n) (Fin rankNum × Row n) ℂ) =
        -(Matrix.kronecker (Pauli.e a.1) (e n a.2)*Matrix.kronecker 1 (leg n j b)) := by
        dsimp only [Matrix.kronecker]
        rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,one_mul,mul_one,ih a.2 j he]
        ext row col
        simp [Matrix.kroneckerMap_apply]
      exact result

lemma coeff_zero (n : ℕ) (a : Label n) (j : Fin (n+1)) (hj : coord n a j≠0)
    (x : Mat n) (hx : ∀ b,Commute (leg n j b) x) : coeff n a x=0 := by
  obtain ⟨b,hb,he⟩ := PauliData.anti (coord n a j) hj
  rw [coeff_apply, KirchbergRordam.PauliSupport.trace_zero_of_anti _ _ _ ?_
    (anti_leg n a j b he) (hx b), mul_zero]
  rw [← map_mul,hb,map_one]
end KirchbergRordam.GenericRW.PauliSupport

namespace KirchbergRordam.GenericRW.ConeCube
open scoped CStarAlgebra ComplexOrder BigOperators
open ConeModel

omit instSize instPauliData in
lemma matLeg_plain
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (n : ℕ) (j : Fin (n+1)) (b : Pauli.M2) :
    matLeg n j (CStarMatrix.ofMatrix b)=CStarMatrix.ofMatrix (PauliSupport.leg n j b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      change MatrixTensor.rightMatrix (matLeg n j (CStarMatrix.ofMatrix b))=_
      rw [ih]
      rfl

lemma ccoeff_zero (n : ℕ) (a : Label n) (j : Fin (n+1)) (hj : PauliSupport.coord n a j≠0)
    (x : Fiber n) (hx : ∀ b,Commute (matLeg n j b) x) : PauliPower.ccoeff n a x=0 := by
  apply PauliSupport.coeff_zero n a j hj (CStarMatrix.ofMatrix.symm x)
  intro b
  have h := (hx (CStarMatrix.ofMatrix b)).map CStarMatrix.ofMatrixStarAlgEquiv.symm
  rw [matLeg_plain] at h
  exact h


end KirchbergRordam.GenericRW.ConeCube
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MatrixSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW

def CoordinateSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

namespace CoordinateSimplex

variable {ι : Type*} [Fintype ι]

instance instFunLikeElemForallReal : FunLike (CoordinateSimplex ι) ι ℝ where
  coe weights := weights.val
  coe_injective := Subtype.val_injective

omit instSize instPauliData in
@[ext] lemma ext.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    {weights other : CoordinateSimplex ι}
    (heq : ∀ index, weights index = other index) : weights = other :=
  Subtype.ext (funext heq)

omit instSize instPauliData in
@[simp] lemma zero_le.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    (weights : CoordinateSimplex ι) (index : ι) :
    0 ≤ weights index := weights.2.1 index

omit instSize instPauliData in
@[simp] lemma sum_eq_one.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    (weights : CoordinateSimplex ι) :
    ∑ index, weights index = 1 := weights.2.2

abbrev vertex [DecidableEq ι] (index : ι) : CoordinateSimplex ι :=
  ⟨Pi.single index 1, by
    constructor
    · intro entry
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · simp⟩

omit instSize instPauliData in
@[simp] lemma vertex_coe.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    [DecidableEq ι] (index : ι) :
    ⇑(vertex index) = Pi.single index 1 := rfl

end CoordinateSimplex
end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_NormUltrapower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]


open Filter Topology BoundedContinuousFunction

universe uQuot

namespace KirchbergRordam
namespace NormUltrapower

variable {A : Type*} [CStarAlgebra A]


theorem exists_norm_limit (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
  obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
    (Ultrafilter.map (fun n => ‖x n‖) ω) (by
      change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
      exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
  exact ⟨r, hr, h⟩


theorem tendsto_norm (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 (normLimit ω x)) :=
  (exists_norm_limit ω x).choose_spec.2

@[simp]
theorem normLimit_zero (ω : Ultrafilter ℕ) : normLimit ω (0 : BoundedSeq A) = 0 := by
  apply tendsto_nhds_unique (tendsto_norm ω 0)
  simp

@[simp]
theorem normLimit_neg (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    normLimit ω (-x) = normLimit ω x := by
  apply tendsto_nhds_unique (tendsto_norm ω (-x))
  simpa using tendsto_norm ω x

@[simp]
theorem normLimit_star (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    normLimit ω (star x) = normLimit ω x := by
  apply tendsto_nhds_unique (tendsto_norm ω (star x))
  simpa using tendsto_norm ω x


@[simp]
theorem mem_nullIdeal (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    x ∈ nullIdeal ω ↔ Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 0) := by
  change normLimit ω x = 0 ↔ _
  constructor
  · intro h
    simpa only [h] using tendsto_norm ω x
  · exact fun h => tendsto_nhds_unique (tendsto_norm ω x) h


@[simp]
theorem star_mk (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    star (Ideal.Quotient.mk (nullIdeal ω) x) = Ideal.Quotient.mk (nullIdeal ω) (star x) := rfl


end NormUltrapower
end KirchbergRordam
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Reindexing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction

open Filter Topology

namespace KirchbergRordam.NormUltrapower
open Filter Topology TopologicalSpace
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A]
lemma quotient_eq_iff (ω : Ultrafilter ℕ) (x y : BoundedSeq A) :
    quotientMap ω x = quotientMap ω y ↔
      Tendsto (fun n => ‖x n - y n‖) (ω : Filter ℕ) (𝓝 0) := by
  change Ideal.Quotient.mk (nullIdeal ω) x = Ideal.Quotient.mk (nullIdeal ω) y ↔ _
  rw [Ideal.Quotient.eq, mem_nullIdeal]
  rfl

def reindexed (k : ℕ → ℕ) (x : BoundedSeq A) : BoundedSeq A :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => x (k n)) ‖x‖
    (fun n => x.norm_coe_le_norm (k n))
@[simp] lemma reindexed_apply (k : ℕ → ℕ) (x : BoundedSeq A) (n : ℕ) :
    reindexed k x n = x (k n) := rfl

end KirchbergRordam.NormUltrapower
open Topology
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_InductiveLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology


open scoped TensorProduct CStarAlgebra


namespace KirchbergRordam.CStarInductiveLimit
section
universe u


attribute [instance] System.cstar


end

universe u


attribute [instance] Chain.cstar


@[simp] lemma Chain.map_self (S : Chain) (i : ℕ) :
    S.map i i le_rfl = StarAlgHom.id ℂ _ := by simp [Chain.map, Nat.leRecOn_self]

@[simp] lemma Chain.map_succ (S : Chain) (i j : ℕ) (h : i ≤ j) :
    S.map i (j+1) (h.trans (Nat.le_succ j)) = (S.step j).comp (S.map i j h) := by
  exact Nat.leRecOn_succ (C := fun n => S.obj i →⋆ₐ[ℂ] S.obj n)
    (next := fun {n} φ => (S.step n).comp φ) h (StarAlgHom.id ℂ (S.obj i))


end KirchbergRordam.CStarInductiveLimit


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MatrixPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra


open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.MatrixPermutationPath
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


@[simp] lemma perm_one : perm (1 : Equiv.Perm ι) = 1 := by
  apply Subtype.ext
  change (1⁻¹ : Equiv.Perm ι).permMatrix ℂ = 1
  simp
lemma perm_mul (σ τ : Equiv.Perm ι) : perm (σ*τ) = perm σ * perm τ := by
  apply Subtype.ext
  change ((σ*τ)⁻¹).permMatrix ℂ = σ⁻¹.permMatrix ℂ * τ⁻¹.permMatrix ℂ
  simp


end KirchbergRordam.MatrixPermutationPath

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder


namespace KirchbergRordam.BalancedDropSystem
open MatrixDiagonalPath
open MatrixTensor (leftMatrix rightMatrix)
open MatrixBlockReindex
open scoped ComplexOrder CStarAlgebra Matrix

@[simp] lemma lower_zero : lowerPath 0 = 0 := by
  apply Subtype.ext
  change (0 : ℝ) / 2 = 0
  norm_num
@[simp] lemma lower_one : lowerPath 1 = half := by
  apply Subtype.ext
  change (1 : ℝ) / 2 = (1 : ℝ) / 2
  rfl
@[simp] lemma upper_zero : upperPath 0 = half := by
  apply Subtype.ext
  change ((0 : ℝ) + 1) / 2 = (1 : ℝ) / 2
  rw [zero_add]
@[simp] lemma upper_one : upperPath 1 = 1 := by
  apply Subtype.ext
  change ((1 : ℝ) + 1) / 2 = 1
  norm_num

end KirchbergRordam.BalancedDropSystem


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder


namespace KirchbergRordam

open scoped Matrix Kronecker ComplexOrder

abbrev M3 := CStarMatrix (Fin 3) (Fin 3) ℂ


def leftMatrixAlgebra : Matrix (Fin 2) (Fin 2) ℂ →⋆ₐ[ℂ]
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ where
  toFun a := a ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.add_kronecker _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul a b
      (1 : Matrix (Fin 3) (Fin 3) ℂ) (1 : Matrix (Fin 3) (Fin 3) ℂ)
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  map_star' a := by
    change aᴴ ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) = (a ⊗ₖ 1)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]


def rightMatrixAlgebra : Matrix (Fin 3) (Fin 3) ℂ →⋆ₐ[ℂ]
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ where
  toFun a := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ a
  map_zero' := Matrix.kronecker_zero _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.kronecker_add _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul
      (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ) a b
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]
  map_star' a := by
    change (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ aᴴ = (1 ⊗ₖ a)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]


end KirchbergRordam


namespace KirchbergRordam.CStarInductiveLimit
open Filter Topology
open scoped CStarAlgebra
variable {B : Type*} [CStarAlgebra B]

lemma quotient_eq_of_eventuallyEq (ω : Ultrafilter ℕ)
    {x y : NormUltrapower.BoundedSeq B}
    (h : ∀ᶠ m in (ω : Filter ℕ), x m=y m) :
    NormUltrapower.quotientMap ω x=NormUltrapower.quotientMap ω y := by
  apply (NormUltrapower.quotient_eq_iff ω x y).mpr
  apply tendsto_const_nhds.congr'
  filter_upwards [h] with m hm
  simp only [hm,sub_self,norm_zero]

end KirchbergRordam.CStarInductiveLimit


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_TensorSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam.ContinuousSectionLocality
section
variable {X E : Type*} [TopologicalSpace X] [instCompactSpaceX : CompactSpace X] [instT2SpaceX : T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
def weight (f : C(X,ℝ)) (g : C(X,E)) : C(X,E) :=
  ⟨fun x => f x • g x,f.continuous.smul g.continuous⟩
omit instCompactSpaceX instT2SpaceX in
@[simp] lemma weight_apply.{contextLevel1, contextLevel2}
    {X : Type contextLevel1}
    {E : Type contextLevel2}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (f : C(X,ℝ)) (g : C(X,E)) (x : X) :
    weight f g x=f x • g x := rfl


end
open scoped CStarAlgebra ComplexOrder
variable {X E : Type*} [TopologicalSpace X] [instCompactSpaceX : CompactSpace X] [instT2SpaceX : T2Space X] [CStarAlgebra E]
def scalarMap : C(X,ℂ) →⋆ₐ[ℂ] C(X,E) where
  toFun f := ⟨fun x => f x • 1,f.continuous.smul continuous_const⟩
  map_zero' := by apply ContinuousMap.ext; intro x; simp
  map_one' := by apply ContinuousMap.ext; intro x; simp
  map_add' f g := by apply ContinuousMap.ext; intro x; exact add_smul _ _ _
  map_mul' f g := by apply ContinuousMap.ext; intro x; change (f x * g x) • (1:E)=(f x • (1:E))*(g x • (1:E)); simp [smul_smul,mul_comm]
  commutes' z := by apply ContinuousMap.ext; intro x; exact (_root_.Algebra.algebraMap_eq_smul_one z).symm
  map_star' f := by apply ContinuousMap.ext; intro x; change star (f x) • (1:E)=star (f x • (1:E)); simp
omit instCompactSpaceX instT2SpaceX in
@[simp] lemma scalarMap_apply.{contextLevel1, contextLevel2}
    {X : Type contextLevel1}
    {E : Type contextLevel2}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    [CStarAlgebra E]
    (f : C(X,ℂ)) (x : X) : scalarMap (E:=E) f x=f x • 1 := rfl

abbrev Square := unitInterval×unitInterval
def firstCoord : C(Square,ℂ) := ⟨fun x => ((x.1:ℝ):ℂ),by fun_prop⟩
def secondCoord : C(Square,ℂ) := ⟨fun x => ((x.2:ℝ):ℂ),by fun_prop⟩


end KirchbergRordam.ContinuousSectionLocality
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FourLegSymmetries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam.FourLegSymmetries
open scoped CStarAlgebra ComplexOrder Matrix Kronecker
open MatrixTensor MatrixPermutationPath
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
abbrev Index (P Q : Type*) := (P×Q)×(P×Q)
def hflip : Equiv.Perm (Index P Q) where
  toFun x := ((x.2.1,x.1.2),(x.1.1,x.2.2))
  invFun x := ((x.2.1,x.1.2),(x.1.1,x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
def kflip : Equiv.Perm (Index P Q) where
  toFun x := ((x.1.1,x.2.2),(x.2.1,x.1.2))
  invFun x := ((x.1.1,x.2.2),(x.2.1,x.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

end KirchbergRordam.FourLegSymmetries


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_DiagonalIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.DiagonalIteration
open scoped CStarAlgebra ComplexOrder
open Filter Topology
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
abbrev conj (v : unitary A) := Unitary.conjStarAlgAut ℂ A v
lemma conj_one (a : A) : conj (1:unitary A) a=a := by simp [conj]

def piUnitary {ι : Type*} (v : ι → unitary A) : unitary (ι→A) :=
  ⟨fun i => v i,⟨by funext i; exact (v i).property.1,by funext i; exact (v i).property.2⟩⟩
lemma piUnitary_continuous {X ι : Type*} [TopologicalSpace X]
    (v : X → ι → unitary A) (hv : ∀ i, Continuous (fun x => v x i)) :
    Continuous (fun x => piUnitary (v x)) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => continuous_subtype_val.comp (hv i))
lemma mapUnitary_continuous (φ : A →⋆ₐ[ℂ] B) : Continuous (Unitary.map (StarMonoidHom.ofClass φ)) :=
  ((map_continuous φ).comp continuous_subtype_val).subtype_mk _

structure System where
  obj : ℕ → Type*
  [cstar : ∀ n, CStarAlgebra (obj n)]
  slot : ℕ → Type*
  [finite : ∀ n, Fintype (slot n)]
  diagonal : ∀ n, (slot n → obj n) →⋆ₐ[ℂ] obj (n+1)
  eigen : ∀ n, slot n → C(unitInterval,unitInterval)
  twist : ∀ n, C(unitInterval,unitary (obj (n+1)))
attribute [instance] System.cstar System.finite
namespace System
variable (S : System)

def flat (n : ℕ) : (k : ℕ) → (unitInterval → S.obj n) → unitInterval → S.obj (n+k)
  | 0, f, t => f t
  | k+1, f, t => S.diagonal (n+k) (fun i => flat n k f (S.eigen (n+k) i t))
def full (n : ℕ) : (k : ℕ) → (unitInterval → S.obj n) → unitInterval → S.obj (n+k)
  | 0, f, t => f t
  | k+1, f, t => conj (S.twist (n+k) t)
      (S.diagonal (n+k) (fun i => full n k f (S.eigen (n+k) i t)))
def unitaryPath (n : ℕ) : (k : ℕ) → unitInterval → unitary (S.obj (n+k))
  | 0, _ => 1
  | k+1, t => S.twist (n+k) t * Unitary.map (StarMonoidHom.ofClass (S.diagonal (n+k)))
      (piUnitary (fun i => unitaryPath n k (S.eigen (n+k) i t)))

lemma unitaryPath_continuous (n k : ℕ) : Continuous (S.unitaryPath n k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    exact (S.twist (n+k)).continuous.mul ((mapUnitary_continuous _).comp
      (piUnitary_continuous _ (fun i => ih.comp (S.eigen (n+k) i).continuous)))

end System
end KirchbergRordam.DiagonalIteration


namespace KirchbergRordam.FiniteHalfFlipSequence
open scoped CStarAlgebra ComplexOrder
open Filter Topology
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
abbrev conj (u : unitary B) := Unitary.conjStarAlgAut ℂ B u

end KirchbergRordam.FiniteHalfFlipSequence
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_EndpointMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.DropMatrixRepresentations
open MatrixDiagonalPath MatrixBlockReindex
open scoped CStarAlgebra ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable (p q : ℕ) [instNeZerop : NeZero p] [instNeZeroq : NeZero q]
lemma two_three (r : ℕ) (hr : 2≤r) : ∃ a b : ℕ, 2*a+3*b=r := by
  by_cases h : r%2=0
  · exact ⟨r/2,0,by omega⟩
  · have hr3 : 3≤r := by omega
    exact ⟨(r-3)/2,1,by omega⟩
end KirchbergRordam.DropMatrixRepresentations
namespace KirchbergRordam.EndpointMultiplicity
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration
open scoped ComplexOrder CStarAlgebra
variable {P Q R : Type*} [Fintype P] [Fintype Q] [Fintype R]
  [DecidableEq P] [DecidableEq Q] [DecidableEq R]
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
def constHom (ι : Type*) : A →⋆ₐ[ℂ] (ι→A) where
  toFun a _ := a
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
def prodUnitary (u : unitary A) (v : unitary B) : unitary (A×B) :=
  ⟨(u,v),⟨Prod.ext u.property.1 v.property.1,Prod.ext u.property.2 v.property.2⟩⟩
end KirchbergRordam.EndpointMultiplicity
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MultiplicativeChannels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.MultiplicativeChannel
open scoped CStarAlgebra ComplexOrder
variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


variable {A B}
@[simp] lemma map_zero (φ : Channel A B) : φ 0=0 := φ.linear.map_zero
@[simp] lemma map_add (φ : Channel A B) (a b : A) : φ (a+b)=φ a+φ b := φ.linear.map_add a b
@[simp] lemma map_smul (φ : Channel A B) (z : ℂ) (a : A) : φ (z • a)=z • φ a := φ.linear.map_smul z a
variable {C : Type*} [CStarAlgebra C]

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
def weighted (h : C(X,ℂ)) (hh : ∀ x, ‖h x‖≤1)
    (φ : A →⋆ₐ[ℂ] C(X,B)) : Channel A C(X,B) where
  linear := {
    toFun a := ⟨fun x => h x • φ a x,h.continuous.smul (φ a).continuous⟩
    map_add' a b := by ext x; simp [smul_add]
    map_smul' z a := by ext x; simp [smul_smul,mul_comm] }
  norm_le a := by
    apply (ContinuousMap.norm_le _ (norm_nonneg a)).mpr
    intro x
    change ‖h x • φ a x‖≤‖a‖
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hh x)).trans
      ((ContinuousMap.norm_coe_le_norm (φ a) x).trans (NonUnitalStarAlgHom.norm_apply_le φ a))
  mul_eq a b := by
    ext x
    change (h x • φ a x)*(h x • φ b x)=(h x • φ 1 x)*(h x • φ (a*b) x)
    simp only [map_one,ContinuousMap.one_apply,map_mul,ContinuousMap.mul_apply,
      smul_mul_assoc,mul_smul_comm,smul_smul,one_mul]

end KirchbergRordam.MultiplicativeChannel
namespace KirchbergRordam.DropChannels
open MatrixDiagonalPath DiagonalIteration
open MultiplicativeChannel (Channel weighted )
open scoped CStarAlgebra ComplexOrder
variable {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
def conjugated (w : X→unitary B) (hw : Continuous w) (ρ : D →⋆ₐ[ℂ] B) :
    D →⋆ₐ[ℂ] C(X,B) where
  toFun d := ⟨fun t => conj (w t) (ρ d),by
    change Continuous (fun t => (w t:B)*ρ d*star (w t:B))
    exact ((continuous_subtype_val.comp hw).mul continuous_const).mul
      (continuous_subtype_val.comp hw).star⟩
  map_zero' := by ext t; change conj (w t) (ρ 0)=0; rw [map_zero,map_zero]
  map_one' := by ext t; change conj (w t) (ρ 1)=1; rw [map_one,map_one]
  map_add' a b := by ext t; change conj (w t) (ρ (a+b))=_; rw [map_add,map_add]; rfl
  map_mul' a b := by ext t; change conj (w t) (ρ (a*b))=_; rw [map_mul,map_mul]; rfl
  commutes' z := by ext t; change conj (w t) (ρ (algebraMap ℂ D z))=_; rw [AlgHomClass.commutes,AlgHomClass.commutes]; rfl
  map_star' a := by ext t; change conj (w t) (ρ (star a))=_; rw [map_star,map_star]; rfl

def leftScalar : C(unitInterval,ℂ) :=
  ⟨fun t => ((1-(t:ℝ):ℝ):ℂ), Complex.continuous_ofReal.comp (continuous_const.sub continuous_subtype_val)⟩
def rightScalar : C(unitInterval,ℂ) :=
  ⟨fun t => ((t:ℝ):ℂ),Complex.continuous_ofReal.comp continuous_subtype_val⟩
@[simp] lemma leftScalar_zero : leftScalar 0=1 := by norm_num [leftScalar]
@[simp] lemma leftScalar_one : leftScalar 1=0 := by norm_num [leftScalar]
@[simp] lemma rightScalar_zero : rightScalar 0=0 := rfl
@[simp] lemma rightScalar_one : rightScalar 1=1 := rfl
lemma leftScalar_norm (t : unitInterval) : ‖leftScalar t‖≤1 := by
  change ‖((1-(t:ℝ):ℝ):ℂ)‖≤1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr t.property.2)]
  linarith [t.property.1]
lemma rightScalar_norm (t : unitInterval) : ‖rightScalar t‖≤1 := by
  change ‖((t:ℝ):ℂ)‖≤1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg t.property.1]
  exact t.property.2
end KirchbergRordam.DropChannels
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_GeneralSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.GeneralBlockReindex
open MatrixBlockReindex MatrixDiagonalPath

open scoped CStarAlgebra Matrix
variable {P Q L R S T U : Type*}
  [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T] [instFintypeU : Fintype U]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R]
  [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T] [instDecidableEqU : DecidableEq U]
omit instFintypeP instFintypeQ instFintypeL instFintypeR instFintypeS instFintypeT instFintypeU instDecidableEqP instDecidableEqQ instDecidableEqL instDecidableEqR instDecidableEqS instDecidableEqT instDecidableEqU in
@[simp] lemma left_low.{contextLevel1, contextLevel2, contextLevel3, contextLevel4, contextLevel5, contextLevel6, contextLevel7}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    {L : Type contextLevel3}
    {R : Type contextLevel4}
    {S : Type contextLevel5}
    {T : Type contextLevel6}
    {U : Type contextLevel7}
    [Fintype P]
    [Fintype Q]
    [Fintype L]
    [Fintype R]
    [Fintype S]
    [Fintype T]
    [Fintype U]
    [DecidableEq P]
    [DecidableEq Q]
    [DecidableEq L]
    [DecidableEq R]
    [DecidableEq S]
    [DecidableEq T]
    [DecidableEq U]
    (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
    (i : P) (j : Q) (l : L) :
    repackLeft hL hR ((i,j),.inl l) = (.inl (i,(hL (j,l)).1),(hL (j,l)).2) := rfl
omit instFintypeP instFintypeQ instFintypeL instFintypeR instFintypeS instFintypeT instFintypeU instDecidableEqP instDecidableEqQ instDecidableEqL instDecidableEqR instDecidableEqS instDecidableEqT instDecidableEqU in
@[simp] lemma left_full.{contextLevel1, contextLevel2, contextLevel3, contextLevel4, contextLevel5, contextLevel6, contextLevel7}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    {L : Type contextLevel3}
    {R : Type contextLevel4}
    {S : Type contextLevel5}
    {T : Type contextLevel6}
    {U : Type contextLevel7}
    [Fintype P]
    [Fintype Q]
    [Fintype L]
    [Fintype R]
    [Fintype S]
    [Fintype T]
    [Fintype U]
    [DecidableEq P]
    [DecidableEq Q]
    [DecidableEq L]
    [DecidableEq R]
    [DecidableEq S]
    [DecidableEq T]
    [DecidableEq U]
    (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
    (i : P) (j : Q) (r : R) :
    repackLeft hL hR ((i,j),.inr r) = (.inr ((i,j),(hR r).1),(hR r).2) := rfl
omit instFintypeP instFintypeQ instFintypeL instFintypeR instFintypeS instFintypeT instFintypeU instDecidableEqP instDecidableEqQ instDecidableEqL instDecidableEqR instDecidableEqS instDecidableEqT instDecidableEqU in
@[simp] lemma right_low.{contextLevel1, contextLevel2, contextLevel3, contextLevel4, contextLevel5, contextLevel6, contextLevel7}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    {L : Type contextLevel3}
    {R : Type contextLevel4}
    {S : Type contextLevel5}
    {T : Type contextLevel6}
    {U : Type contextLevel7}
    [Fintype P]
    [Fintype Q]
    [Fintype L]
    [Fintype R]
    [Fintype S]
    [Fintype T]
    [Fintype U]
    [DecidableEq P]
    [DecidableEq Q]
    [DecidableEq L]
    [DecidableEq R]
    [DecidableEq S]
    [DecidableEq T]
    [DecidableEq U]
    (hL : P × L ≃ T × U) (hR : R ≃ T × S)
    (i : P) (j : Q) (l : L) :
    repackRight hL hR ((i,j),.inl l) = ((hL (i,l)).1,.inl (j,(hL (i,l)).2)) := rfl
omit instFintypeP instFintypeQ instFintypeL instFintypeR instFintypeS instFintypeT instFintypeU instDecidableEqP instDecidableEqQ instDecidableEqL instDecidableEqR instDecidableEqS instDecidableEqT instDecidableEqU in
@[simp] lemma right_full.{contextLevel1, contextLevel2, contextLevel3, contextLevel4, contextLevel5, contextLevel6, contextLevel7}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    {L : Type contextLevel3}
    {R : Type contextLevel4}
    {S : Type contextLevel5}
    {T : Type contextLevel6}
    {U : Type contextLevel7}
    [Fintype P]
    [Fintype Q]
    [Fintype L]
    [Fintype R]
    [Fintype S]
    [Fintype T]
    [Fintype U]
    [DecidableEq P]
    [DecidableEq Q]
    [DecidableEq L]
    [DecidableEq R]
    [DecidableEq S]
    [DecidableEq T]
    [DecidableEq U]
    (hL : P × L ≃ T × U) (hR : R ≃ T × S)
    (i : P) (j : Q) (r : R) :
    repackRight hL hR ((i,j),.inr r) = ((hR r).1,.inr ((i,j),(hR r).2)) := rfl
end KirchbergRordam.GeneralBlockReindex
namespace KirchbergRordam.GeneralEndpointMultiplicity
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration EndpointMultiplicity
open scoped ComplexOrder CStarAlgebra
variable {P Q R E : Type*} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeR : Fintype R] [Fintype E]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqR : DecidableEq R] [DecidableEq E]
def leftExpand : (P×E) ⊕ ((P×Q)×R) ≃ P × (E ⊕ (Q×R)) where
  toFun x := match x with
    | .inl (a,e) => (a,.inl e)
    | .inr ((a,b),r) => (a,.inr (b,r))
  invFun x := match x.2 with
    | .inl e => .inl (x.1,e)
    | .inr (b,r) => .inr ((x.1,b),r)
  left_inv x := by rcases x with ⟨a,e⟩|⟨⟨a,b⟩,r⟩ <;> rfl
  right_inv x := by rcases x with ⟨a,e|⟨b,r⟩⟩ <;> rfl
def rightExpand : (Q×E) ⊕ ((P×Q)×R) ≃ Q × (E ⊕ (P×R)) where
  toFun x := match x with
    | .inl (b,e) => (b,.inl e)
    | .inr ((a,b),r) => (b,.inr (a,r))
  invFun x := match x.2 with
    | .inl e => .inl (x.1,e)
    | .inr (a,r) => .inr ((a,x.1),r)
  left_inv x := by rcases x with ⟨b,e⟩|⟨⟨a,b⟩,r⟩ <;> rfl
  right_inv x := by rcases x with ⟨b,e|⟨a,r⟩⟩ <;> rfl
end KirchbergRordam.GeneralEndpointMultiplicity
end

end OAI
end


