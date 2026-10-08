-- Prove2me | Definitions.Def_OAIErdos3B001
-- name    : OAIErdos3B001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T07:17:36.706974+00:00
-- url     : https://prove2.me/theorems/c6a07da5-82da-4a2e-b290-e61e5be072e7
-- title:
--   OpenAI Erdős-3 split, definitions bundle 2 of 132
-- statement:
--   Definitions bundle 2 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B000`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 2 available.
--
--   Modules: `Polynomial.PolynomialPatchProductBudget`, `Sampling.NormalizedRealBoxHalfGrid`, `Lattices.ResidueSliceNormalizedCell`, `Linear.FiniteSpanRounding`, `Dynamics.CandidateFrontSourceLossBudget`, `Fourier.PrimePowerCharacterScaling`, `Lattices.ResidueRefinedPeriod`, `Lattices.IntegerCokernelExponent`, `Fourier.CharacterCoordinateScale`, `Estimates.WeightedSummandCorrelation`, `Estimates.BufferedSiteExpansion`, `Lattices.RectangularLatticeCells`, `Geometry.CompactBoxIntegral`, `Probability.FiniteProbabilityLipschitz`, `Estimates.CorrelationDerivative`, `Estimates.UnitExpansionCorrelation`, `Estimates.FiniteFiberTest`, `Probability.FiniteConditionedMass`, `Probability.LargeCokernelProbability`, `Lattices.IntegerColumnMinor`, `Estimates.RationalRowReduction`, `Dynamics.RationalHeightBudget`, `Geometry.LinearMapCoordinateHeight`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B000

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateFrontSourceLossBudget
namespace OAI

section

namespace Erdos3

theorem le_power_budget {p : ℝ} (hp : 0 ≤ p) {a : ℕ} (ha : 1 ≤ a) :
    p ≤ (p + 2) ^ a := by
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith
  calc
    p ≤ p + 2 := by linarith
    _ ≤ (p + 2) ^ a := by simpa only [pow_one] using pow_le_pow_right₀ hbase ha

theorem shifted_power_budget_le {p : ℝ} (hp : 0 ≤ p) (a b : ℕ) :
    ((p + 2) ^ a + 2) ^ b ≤ (p + 2) ^ ((a + 2) * b) := by
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith
  have hpow : (1 : ℝ) ≤ (p + 2) ^ a := one_le_pow₀ hbase
  have hsq : (4 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
  have hstep : (p + 2) ^ a + 2 ≤ (p + 2) ^ (a + 2) := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (p + 2) ^ a)]
  calc
    _ ≤ ((p + 2) ^ (a + 2)) ^ b := pow_le_pow_left₀ (by positivity) hstep b
    _ = _ := (pow_mul _ _ _).symm

theorem polynomial_budget_comp {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (a b : ℕ) (hpq : q ≤ (p + 2) ^ a) (hqr : r ≤ (q + 2) ^ b) :
    r ≤ (p + 2) ^ ((a + 2) * b) := by
  calc
    r ≤ (q + 2) ^ b := hqr
    _ ≤ ((p + 2) ^ a + 2) ^ b := by gcongr
    _ ≤ _ := shifted_power_budget_le hp a b

def budgetDepthExponent (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => (budgetDepthExponent a d + 2) * a

theorem bounded_depth_budget {p : ℝ} (hp : 0 ≤ p) (a : ℕ) (q : ℕ → ℝ)
    (hq : ∀ d, 0 ≤ q d) (hzero : q 0 ≤ p)
    (hstep : ∀ d, q (d + 1) ≤ (q d + 2) ^ a) (d : ℕ) :
    q d ≤ (p + 2) ^ budgetDepthExponent a d := by
  induction d with
  | zero => simpa only [budgetDepthExponent, pow_one] using hzero.trans (by linarith : p ≤ p + 2)
  | succ d ih => exact polynomial_budget_comp hp (hq d) _ a ih (hstep d)

theorem exponential_budget_comp {p q h : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (a b : ℕ) (hpq : q ≤ (p + 2) ^ a) (hh : h ≤ Real.exp ((q + 2) ^ b)) :
    h ≤ Real.exp ((p + 2) ^ ((a + 2) * b)) := by
  exact hh.trans (Real.exp_le_exp.mpr (polynomial_budget_comp hp hq a b hpq le_rfl))

theorem product_exponential_budget {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {p : ℝ} (hp : 0 ≤ p) (a c : ℕ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf : ∀ i ∈ s, f i ≤ Real.exp ((p + 2) ^ a))
    (hcard : (s.card : ℝ) ≤ (p + 2) ^ c) :
    (∏ i ∈ s, f i) ≤ Real.exp ((p + 2) ^ (a + c)) := by
  calc
    _ ≤ ∏ _i ∈ s, Real.exp ((p + 2) ^ a) := Finset.prod_le_prod hf0 hf
    _ = Real.exp ((s.card : ℝ) * (p + 2) ^ a) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]
    _ ≤ Real.exp ((p + 2) ^ (a + c)) := by
      apply Real.exp_le_exp.mpr
      rw [pow_add]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcard
        (by positivity : 0 ≤ (p + 2) ^ a)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

def candidateFrontFamilyParameter (cap : ℝ) : ℝ := (cap + 3) ^ 4

theorem candidateFrontFamilyBounds (cap native : ℝ) (layers variableCount : ℕ)
    (hcap : 0 ≤ cap) (hnative : native ≤ cap)
    (hlayers : (layers : ℝ) ≤ cap) (hvariableCount : (variableCount : ℝ) ≤ cap) :
    0 ≤ candidateFrontFamilyParameter cap ∧
    cap ≤ candidateFrontFamilyParameter cap ∧
    2 * max native 3 ≤ candidateFrontFamilyParameter cap ∧
    Real.exp (max native 3) *
      (1 + (layers : ℝ) * (((layers + 1 : ℕ) : ℝ) *
        ((variableCount + 1 : ℕ) : ℝ) ^ layers)) ≤ Real.exp (candidateFrontFamilyParameter cap) := by
  have hbase : 1 ≤ cap + 3 := by linarith
  have hsq : (cap + 3) ^ 2 ≤ candidateFrontFamilyParameter cap :=
    pow_le_pow_right₀ hbase (by decide)
  have hcapFamily : cap ≤ candidateFrontFamilyParameter cap :=
    (by nlinarith [sq_nonneg cap] : cap ≤ (cap + 3) ^ 2).trans hsq
  have hmax : max native 3 ≤ cap + 3 := max_le (by linarith) (by linarith)
  have hperiod : 2 * max native 3 ≤ candidateFrontFamilyParameter cap :=
    (by nlinarith [sq_nonneg cap] : 2 * max native 3 ≤ (cap + 3) ^ 2).trans hsq
  have hplus : cap + 1 ≤ Real.exp cap := Real.add_one_le_exp cap
  have hLayerExp : (layers : ℝ) ≤ Real.exp cap := hlayers.trans (by linarith)
  have hLayerOneExp : ((layers + 1 : ℕ) : ℝ) ≤ Real.exp cap := by
    push_cast
    linarith
  have hVariableExp : ((variableCount + 1 : ℕ) : ℝ) ≤ Real.exp cap := by
    push_cast
    linarith
  have hpower : ((variableCount + 1 : ℕ) : ℝ) ^ layers ≤ Real.exp (cap ^ 2) := by
    calc
      _ ≤ (Real.exp cap) ^ layers := pow_le_pow_left₀ (Nat.cast_nonneg _) hVariableExp layers
      _ = Real.exp ((layers : ℝ) * cap) := (Real.exp_nat_mul cap layers).symm
      _ ≤ Real.exp (cap ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  have hproduct : (layers : ℝ) * (((layers + 1 : ℕ) : ℝ) *
      ((variableCount + 1 : ℕ) : ℝ) ^ layers) ≤ Real.exp (2 * cap + cap ^ 2) := by
    calc
      _ ≤ Real.exp cap * (Real.exp cap * Real.exp (cap ^ 2)) := by
        gcongr
      _ = Real.exp (2 * cap + cap ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hone : 1 ≤ Real.exp (2 * cap + cap ^ 2) := Real.one_le_exp (by positivity)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum : 1 + (layers : ℝ) * (((layers + 1 : ℕ) : ℝ) *
      ((variableCount + 1 : ℕ) : ℝ) ^ layers) ≤ Real.exp (2 * cap + cap ^ 2 + 1) := by
    calc
      _ ≤ 2 * Real.exp (2 * cap + cap ^ 2) := by linarith
      _ ≤ Real.exp 1 * Real.exp (2 * cap + cap ^ 2) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (2 * cap + cap ^ 2 + 1) := by
        rw [← Real.exp_add]
        congr 1
        ring
  refine ⟨by unfold candidateFrontFamilyParameter; positivity, hcapFamily, hperiod, ?_⟩
  calc
    _ ≤ Real.exp (max native 3) * Real.exp (2 * cap + cap ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)
    _ = Real.exp (max native 3 + (2 * cap + cap ^ 2 + 1)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((cap + 3) ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ Real.exp (candidateFrontFamilyParameter cap) := Real.exp_le_exp.mpr hsq

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

noncomputable def iteratedPowerBudget (a : ℕ) (p : ℝ) : ℕ → ℝ
  | 0 => p
  | n + 1 => (iteratedPowerBudget a p n + 2) ^ a

@[simp] theorem iteratedPowerBudget_zero (a : ℕ) (p : ℝ) : iteratedPowerBudget a p 0 = p := rfl

@[simp] theorem iteratedPowerBudget_succ (a : ℕ) (p : ℝ) (n : ℕ) :
    iteratedPowerBudget a p (n + 1) = (iteratedPowerBudget a p n + 2) ^ a := rfl

theorem iteratedPowerBudget_nonneg (a : ℕ) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    0 ≤ iteratedPowerBudget a p n := by
  induction n with
  | zero => exact hp
  | succ n ih => exact pow_nonneg (by linarith) _

theorem iteratedPowerBudget_monotone {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 0 ≤ p) :
    Monotone (iteratedPowerBudget a p) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_power_budget (iteratedPowerBudget_nonneg a hp n) ha

theorem iteratedPowerBudget_ge {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    p ≤ iteratedPowerBudget a p n :=
  iteratedPowerBudget_monotone ha hp (Nat.zero_le n)

theorem iteratedPowerBudget_le_power (a : ℕ) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    iteratedPowerBudget a p n ≤ (p + 2) ^ budgetDepthExponent a n :=
  bounded_depth_budget hp a (iteratedPowerBudget a p)
    (iteratedPowerBudget_nonneg a hp) le_rfl (fun _ => le_rfl) n

end Erdos3

end

section

namespace Erdos3

theorem powerCover_index_allowance_le_exp (l m d : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) (hd : (d : ℝ) ≤ p) :
    (((l * m) ^ d : ℕ) : ℝ) ≤ Real.exp (2 * p ^ 2) := by
  have hprod : (l : ℝ) * m ≤ Real.exp (2 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hl hm (by positivity) (by positivity)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
  rw [Nat.cast_pow, Nat.cast_mul]
  calc
    _ ≤ (Real.exp (2 * p)) ^ d := pow_le_pow_left₀ (by positivity) hprod d
    _ = Real.exp ((d : ℝ) * (2 * p)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (2 * p ^ 2) := Real.exp_le_exp.mpr (by nlinarith)

theorem powerCover_grid_allowance_le_exp (l m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) :
    (((l * m) * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp p * Real.exp p :=
      mul_le_mul (mul_le_mul hl hm (by positivity) (by positivity)) hl
        (by positivity) (by positivity)
    _ = Real.exp (3 * p) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem candidateFrontSourceLossBounds (cap p q u pModel native bin : ℝ)
    (hcap : 3 ≤ cap)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hu : 0 ≤ u) (hmodel : 0 ≤ pModel)
    (hnative : 0 ≤ native) (hbin : 0 ≤ bin)
    (hpCap : p ≤ cap) (hqCap : q ≤ cap) (huCap : u ≤ cap)
    (hmodelCap : pModel ≤ cap) (hnativeCap : native ≤ cap) (hbinU : bin ≤ u) :
    let Q := max (max native 3) (2 * u + 4 * pModel + 20)
    let r := q + bin + Q + 6
    let M := 2 * p + q + p * (bin + (2 * Q + 2 * u + 4 * pModel + 34)) + 2
    0 ≤ Q ∧ Q ≤ 6 * cap + 20 ∧
      0 ≤ r ∧ r ≤ (cap + 3) ^ 4 ∧
      0 ≤ M ∧ M ≤ (cap + 3) ^ 4 := by
  let Q := max (max native 3) (2 * u + 4 * pModel + 20)
  have hc0 : 0 ≤ cap := le_trans (by norm_num) hcap
  have hQ0 : 0 ≤ Q := (hnative.trans (le_max_left _ _)).trans (le_max_left _ _)
  have hQcap : Q ≤ 6 * cap + 20 := by
    apply max_le
    · exact max_le (by linarith only [hnativeCap, hc0]) (by linarith only [hcap])
    · linarith only [huCap, hmodelCap]
  have hbinCap : bin ≤ cap := hbinU.trans huCap
  have hterm0 : 0 ≤ bin + (2 * Q + 2 * u + 4 * pModel + 34) := by positivity
  have hterm : bin + (2 * Q + 2 * u + 4 * pModel + 34) ≤ 19 * cap + 74 := by
    linarith only [hbinCap, hQcap, huCap, hmodelCap]
  have hproduct := mul_le_mul hpCap hterm hterm0 hc0
  have hmass : 2 * p + q + p * (bin + (2 * Q + 2 * u + 4 * pModel + 34)) + 2 ≤
      19 * cap ^ 2 + 77 * cap + 2 := by
    nlinarith only [hpCap, hqCap, hproduct]
  have hresidual : q + bin + Q + 6 ≤ 8 * cap + 26 := by
    linarith only [hqCap, hbinCap, hQcap]
  have hquartic : (cap + 3) ^ 4 = cap ^ 4 + 12 * cap ^ 3 + 54 * cap ^ 2 +
      108 * cap + 81 := by ring
  have hc2 : 0 ≤ cap ^ 2 := pow_nonneg hc0 _
  have hc3 : 0 ≤ cap ^ 3 := pow_nonneg hc0 _
  have hc4 : 0 ≤ cap ^ 4 := pow_nonneg hc0 _
  have hresidualQuartic : 8 * cap + 26 ≤ (cap + 3) ^ 4 := by
    rw [hquartic]
    linarith only [hc0, hc2, hc3, hc4]
  have hmassQuartic : 19 * cap ^ 2 + 77 * cap + 2 ≤ (cap + 3) ^ 4 := by
    rw [hquartic]
    linarith only [hc0, hc2, hc3, hc4]
  exact ⟨hQ0, hQcap, by positivity, hresidual.trans hresidualQuartic,
    by positivity, hmass.trans hmassQuartic⟩

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PrimePowerCharacterScaling
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

def characterPullback {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) : AddChar H ℂ →* AddChar G ℂ where
  toFun χ := χ.compAddMonoidHom f
  map_one' := rfl
  map_mul' _ _ := rfl

theorem characterPullback_order {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (hf : Function.Surjective f) (χ : AddChar H ℂ) :
    orderOf (characterPullback f χ) = orderOf χ :=
  orderOf_injective (characterPullback f) (AddChar.compAddMonoidHom_injective_left f hf) χ

end Erdos3

end

section

namespace Erdos3

def zmodPiReduction {I : Type*} {n m : ℕ} (h : m ∣ n) :
    (I → ZMod n) →+ (I → ZMod m) :=
  AddMonoidHom.piMap fun _ => (ZMod.castHom h (ZMod m)).toAddMonoidHom

@[simp] theorem zmodPiReduction_apply {I : Type*} {n m : ℕ} (h : m ∣ n)
    (x : I → ZMod n) (i : I) :
    zmodPiReduction h x i = ZMod.castHom h (ZMod m) (x i) := rfl

theorem zmodPiReduction_surjective {I : Type*} {n m : ℕ} (h : m ∣ n) :
    Function.Surjective (zmodPiReduction (I := I) h) := by
  intro y
  choose x hx using fun i => ZMod.castHom_surjective h (y i)
  exact ⟨x, funext hx⟩

theorem zmodPiReduction_kernel_nsmul {I : Type*} {n m : ℕ} [NeZero n]
    (h : m ∣ n) (x : I → ZMod n) (hx : zmodPiReduction h x = 0) :
    ∃ y : I → ZMod n, m • y = x := by
  have hdvd (i : I) : m ∣ (x i).val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    have hi := congrFun hx i
    simpa only [zmodPiReduction_apply, ZMod.castHom_apply, ZMod.cast_eq_val,
      Pi.zero_apply] using hi
  choose w hw using hdvd
  refine ⟨fun i => (w i : ZMod n), ?_⟩
  funext i
  change m • (w i : ZMod n) = x i
  rw [nsmul_eq_mul, ← Nat.cast_mul, ← hw i, ZMod.natCast_zmod_val]

theorem zmodPiReduction_kernel_character {I : Type*} {n m : ℕ} [NeZero n]
    (h : m ∣ n) (χ : AddChar (I → ZMod n) ℂ) (hχ : χ ^ m = 1)
    (x : I → ZMod n) (hx : zmodPiReduction h x = 0) : χ x = 1 := by
  obtain ⟨y, hy⟩ := zmodPiReduction_kernel_nsmul h x hx
  rw [← hy, AddChar.map_nsmul_eq_pow]
  exact congrArg (fun ψ : AddChar (I → ZMod n) ℂ => ψ y) hχ

theorem exists_zmodPiReduction_character {I : Type*} {n m : ℕ} [NeZero n]
    (h : m ∣ n) (χ : AddChar (I → ZMod n) ℂ) (hχ : χ ^ m = 1) :
    ∃ ψ : AddChar (I → ZMod m) ℂ,
      characterPullback (zmodPiReduction h) ψ = χ ∧ orderOf ψ = orderOf χ := by
  let q := zmodPiReduction (I := I) h
  let f := q.toMultiplicative
  have hf : Function.Surjective f := zmodPiReduction_surjective h
  let g := χ.toMonoidHom.toHomUnits
  have hker : f.ker ≤ g.ker := by
    intro x hx
    apply Units.ext
    change χ x.toAdd = 1
    exact zmodPiReduction_kernel_character h χ hχ x.toAdd hx
  let lifted := f.liftOfSurjective hf ⟨g, hker⟩
  let ψ : AddChar (I → ZMod m) ℂ :=
    AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp lifted)
  have heq : characterPullback q ψ = χ := by
    apply AddChar.ext
    intro x
    change (lifted (f (Multiplicative.ofAdd x)) : ℂ) = χ x
    simp only [lifted, MonoidHom.liftOfSurjective,
      MonoidHom.liftOfRightInverse_comp_apply]
    rfl
  refine ⟨ψ, heq, ?_⟩
  rw [← characterPullback_order q (zmodPiReduction_surjective h) ψ, heq]

end Erdos3

end

section

namespace Erdos3

theorem zmod_character_order_dvd {I : Type*} {N : ℕ}
    (χ : AddChar (I → ZMod N) ℂ) : orderOf χ ∣ N := by
  apply orderOf_dvd_of_pow_eq_one
  ext x
  rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow]
  have hx : N • x = 0 := by
    funext i
    simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  rw [hx, AddChar.map_zero_eq_one, AddChar.one_apply]

theorem zmod_character_order_pos {I : Type*} {N : ℕ} [NeZero N]
    (χ : AddChar (I → ZMod N) ℂ) : 0 < orderOf χ := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hdvd := zmod_character_order_dvd χ
  rw [hz, zero_dvd_iff] at hdvd
  exact NeZero.ne N hdvd

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem integerMatrixImage_index {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) :
    A.mulVecLin.range.toAddSubgroup.index = A.det.natAbs := by
  let e := LinearEquiv.ofInjective A.mulVecLin (Matrix.mulVec_injective_of_det_ne_zero hA)
  have h := Submodule.natAbs_det_equiv A.mulVecLin.range e
  have he : A.mulVecLin.range.subtype.comp e.toLinearMap = A.mulVecLin := by
    ext x i
    rfl
  change (LinearMap.det (A.mulVecLin.range.subtype.comp e.toLinearMap)).natAbs = _ at h
  rw [he] at h
  rw [← Matrix.toLin'_apply', LinearMap.det_toLin'] at h
  exact h.symm

theorem integerMatrixImage_det_smul {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (y : I → ℤ) : A.det • y ∈ A.mulVecLin.range := by
  refine ⟨A.adjugate *ᵥ y, ?_⟩
  change A *ᵥ (A.adjugate *ᵥ y) = A.det • y
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem integerMatrixImage_multiple_smul {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) {m : ℤ} (hm : A.det ∣ m) (y : I → ℤ) :
    m • y ∈ A.mulVecLin.range := by
  obtain ⟨r, rfl⟩ := hm
  simpa only [smul_smul, mul_comm] using
    A.mulVecLin.range.smul_mem r (integerMatrixImage_det_smul A y)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

def pivotFreeLattice {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) : Submodule ℤ (J → ℤ) :=
  A.mulVecLin.range.comap B.mulVecLin

def pivotFullImage {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) : Submodule ℤ (I → ℤ) :=
  A.mulVecLin.range ⊔ B.mulVecLin.range

def pivotFreeAdmissible {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ) (y : J → ℤ) : Prop :=
  v - B *ᵥ y ∈ A.mulVecLin.range

theorem pivotFreeAdmissible_iff {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ) (y : J → ℤ) :
    pivotFreeAdmissible A B v y ↔ ∃ x : I → ℤ, A *ᵥ x + B *ᵥ y = v := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (eq_sub_iff_add_eq).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (eq_sub_iff_add_eq).mpr hx⟩

theorem pivotFreeAdmissible_coset {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ)
    {y₀ : J → ℤ} (hy₀ : pivotFreeAdmissible A B v y₀) (y : J → ℤ) :
    pivotFreeAdmissible A B v y ↔ y - y₀ ∈ pivotFreeLattice A B := by
  change v - B *ᵥ y ∈ A.mulVecLin.range ↔ B *ᵥ (y - y₀) ∈ A.mulVecLin.range
  rw [Matrix.mulVec_sub]
  constructor
  · intro hy
    convert A.mulVecLin.range.sub_mem hy₀ hy using 1
    abel
  · intro hy
    convert A.mulVecLin.range.sub_mem hy₀ hy using 1
    abel

noncomputable def pivotIntegerFiberEquiv {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (v : I → ℤ) :
    {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} ≃
      {y : J → ℤ // pivotFreeAdmissible A B v y} where
  toFun p := ⟨p.val.2, (pivotFreeAdmissible_iff A B v p.val.2).mpr ⟨p.val.1, p.property⟩⟩
  invFun y := ⟨⟨(pivotFreeAdmissible_iff A B v y.val).mp y.property |>.choose, y.val⟩,
    (pivotFreeAdmissible_iff A B v y.val).mp y.property |>.choose_spec⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Matrix.mulVec_injective_of_det_ne_zero hA
      have h := (pivotFreeAdmissible_iff A B v p.val.2).mp
        ((pivotFreeAdmissible_iff A B v p.val.2).mpr ⟨p.val.1, p.property⟩) |>.choose_spec
      exact add_right_cancel (h.trans p.property.symm)
    · rfl
  right_inv _ := rfl

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

def integerScalarLattice (J : Type*) [Fintype J] (m : ℤ) : Submodule ℤ (J → ℤ) :=
  (m • (LinearMap.id : (J → ℤ) →ₗ[ℤ] (J → ℤ))).range

theorem integerScalarLattice_mem {J : Type*} [Fintype J] (m : ℤ) (y : J → ℤ) :
    y ∈ integerScalarLattice J m ↔ ∃ z : J → ℤ, m • z = y := Iff.rfl

theorem integerScalarLattice_index {J : Type*} [Fintype J] [DecidableEq J]
    {m : ℤ} (hm : m ≠ 0) :
    (integerScalarLattice J m).toAddSubgroup.index = m.natAbs ^ Fintype.card J := by
  have hM : (m • (1 : Matrix J J ℤ)).det ≠ 0 := by
    simp only [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hm
  have hi := integerMatrixImage_index (m • (1 : Matrix J J ℤ)) hM
  have he : (m • (1 : Matrix J J ℤ)).mulVecLin = m • LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (m • (1 : Matrix J J ℤ)) *ᵥ x = m • x
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [he, Matrix.det_smul, Matrix.det_one, mul_one, Int.natAbs_pow] at hi
  exact hi

theorem integerScalarLattice_le_pivotFreeLattice {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) {m : ℤ} (hm : A.det ∣ m) :
    integerScalarLattice J m ≤ pivotFreeLattice A B := by
  rintro y ⟨z, rfl⟩
  change B *ᵥ (m • z) ∈ A.mulVecLin.range
  rw [Matrix.mulVec_smul]
  exact integerMatrixImage_multiple_smul A hm (B *ᵥ z)

end Erdos3

end

section

namespace Erdos3

def integerLatticeResidue {J : Type*} [Fintype J]
    (L : Submodule ℤ (J → ℤ)) (m : ℤ) :=
  L.toAddSubgroup ⧸ (integerScalarLattice J m).toAddSubgroup.addSubgroupOf L.toAddSubgroup

@[instance_reducible] noncomputable def integerLatticeResidueFintype {J : Type*}
    [Fintype J] [DecidableEq J]
    (L : Submodule ℤ (J → ℤ)) {m : ℤ} (hm : m ≠ 0) :
    Fintype (integerLatticeResidue L m) := by
  let : (integerScalarLattice J m).toAddSubgroup.FiniteIndex :=
    ⟨by rw [integerScalarLattice_index hm]; exact pow_ne_zero _ (Int.natAbs_ne_zero.mpr hm)⟩
  unfold integerLatticeResidue
  exact Fintype.ofFinite _

noncomputable def integerScalarPeriodEquiv {J : Type*} [Fintype J]
    (L : Submodule ℤ (J → ℤ)) {m : ℤ} (hm : m ≠ 0)
    (hL : integerScalarLattice J m ≤ L) :
    (J → ℤ) ≃ (integerScalarLattice J m).toAddSubgroup.addSubgroupOf L.toAddSubgroup where
  toFun z := ⟨⟨m • z, hL ⟨z, rfl⟩⟩, ⟨z, rfl⟩⟩
  invFun z := z.property.choose
  left_inv z := by
    funext j
    apply mul_left_cancel₀ hm
    exact congrFun (Exists.choose_spec (show ∃ w : J → ℤ, m • w = m • z from ⟨z, rfl⟩)) j
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact z.property.choose_spec

noncomputable def additiveResidueEquiv {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) : G ≃ (G ⧸ H) × H where
  toFun x := ⟨(x : G ⧸ H), ⟨x - Quotient.out (x : G ⧸ H),
    QuotientAddGroup.eq_iff_sub_mem.mp (Quotient.out_eq' _).symm⟩⟩
  invFun p := p.1.out + p.2.val
  left_inv x := by simp
  right_inv := by
    rintro ⟨r, n⟩
    have h : ((r.out + n.val : G) : G ⧸ H) = r := by
      calc
        _ = (r.out : G ⧸ H) := QuotientAddGroup.eq_iff_sub_mem.mpr (by simp)
        _ = r := Quotient.out_eq' r
    apply Prod.ext
    · exact h
    · apply Subtype.ext
      change r.out + n.val - Quotient.out ((r.out + n.val : G) : G ⧸ H) = n.val
      rw [h]
      simp

noncomputable def integerLatticeResidueEquiv {J : Type*} [Fintype J]
    (L : Submodule ℤ (J → ℤ)) {m : ℤ} (hm : m ≠ 0)
    (hL : integerScalarLattice J m ≤ L) :
    L ≃ integerLatticeResidue L m × (J → ℤ) :=
  (additiveResidueEquiv _).trans
    (Equiv.prodCongr (Equiv.refl _) (integerScalarPeriodEquiv L hm hL).symm)

end Erdos3

end

section

namespace Erdos3

def integerResidueMap (I : Type*) (m : ℕ) : (I → ℤ) →ₗ[ℤ] (I → ZMod m) where
  toFun v i := v i
  map_add' v w := by ext i; simp
  map_smul' r v := by ext i; simp

theorem integerResidueMap_surjective (I : Type*) (m : ℕ) :
    Function.Surjective (integerResidueMap I m) := by
  intro v
  choose z hz using fun i => ZMod.intCast_surjective (v i)
  exact ⟨z, funext hz⟩

theorem integerResidueMap_ker (I : Type*) [Fintype I] (m : ℕ) :
    LinearMap.ker (integerResidueMap I m) = integerScalarLattice I (m : ℤ) := by
  ext v
  rw [LinearMap.mem_ker, integerScalarLattice_mem]
  constructor
  · intro hv
    have hd : ∀ i, (m : ℤ) ∣ v i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) m).mp (congrFun hv i)
    choose z hz using hd
    exact ⟨z, funext fun i => (hz i).symm⟩
  · rintro ⟨z, rfl⟩
    ext i
    change (((m : ℤ) * z i : ℤ) : ZMod m) = 0
    simp

end Erdos3

end

section

namespace Erdos3

open scoped Matrix ENNReal

def pivotAdmissibleLatticeEquiv {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ)
    (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀) :
    {y : J → ℤ // pivotFreeAdmissible A B v y} ≃ pivotFreeLattice A B where
  toFun y := ⟨y.val - y₀, (pivotFreeAdmissible_coset A B v hy₀ y.val).mp y.property⟩
  invFun z := ⟨y₀ + z.val, (pivotFreeAdmissible_coset A B v hy₀ _).mpr (by
    simpa only [add_sub_cancel_left] using z.property)⟩
  left_inv y := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp

noncomputable def pivotFiberGridEquiv {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (v : I → ℤ)
    (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m) :
    {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} ≃
      integerLatticeResidue (pivotFreeLattice A B) m × (J → ℤ) :=
  (pivotIntegerFiberEquiv A hA B v).trans ((pivotAdmissibleLatticeEquiv A B v y₀ hy₀).trans
    (integerLatticeResidueEquiv (pivotFreeLattice A B) hm
      (integerScalarLattice_le_pivotFreeLattice A B hdiv)))

end Erdos3

end

section

namespace Erdos3

def residueLatticeImage {I : Type*} (L : Submodule ℤ (I → ℤ)) (m : ℕ) :
    Submodule ℤ (I → ZMod m) := L.map (integerResidueMap I m)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

def integerResidueMatrix {I J : Type*} (A : Matrix I J ℤ) (m : ℕ) : Matrix I J (ZMod m) :=
  A.map (Int.castRingHom (ZMod m))

theorem integerResidueMap_mulVec {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) (x : J → ℤ) :
    integerResidueMap I m (A *ᵥ x) = integerResidueMatrix A m *ᵥ integerResidueMap J m x := by
  funext i
  exact (Int.castRingHom (ZMod m)).map_mulVec A x i

theorem integerResidueMatrix_eq_of_mod {I J : Type*} (A B : Matrix I J ℤ) (m : ℕ)
    (hAB : ∀ i j, A i j % (m : ℤ) = B i j % (m : ℤ)) :
    integerResidueMatrix A m = integerResidueMatrix B m := by
  ext i j
  exact (ZMod.intCast_eq_intCast_iff' (A i j) (B i j) m).mpr (hAB i j)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

def reducedIntegerMatrix {I J : Type*} (A : Matrix I J ℤ) (M : ℕ) : Matrix I J ℤ :=
  fun i j => A i j % (M : ℤ)

theorem reducedIntegerMatrix_bounds {I J : Type*} (A : Matrix I J ℤ)
    (M : ℕ) [NeZero M] (i : I) (j : J) :
    0 ≤ reducedIntegerMatrix A M i j ∧ reducedIntegerMatrix A M i j < M := by
  have hM : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  exact ⟨Int.emod_nonneg _ hM.ne', Int.emod_lt_of_pos _ hM⟩

theorem integerResidueMatrix_reduced {I J : Type*} (A : Matrix I J ℤ) (M : ℕ) :
    integerResidueMatrix (reducedIntegerMatrix A M) M = integerResidueMatrix A M := by
  apply integerResidueMatrix_eq_of_mod
  intro i j
  exact Int.emod_emod _ _

theorem reducedIntegerMatrix_residue {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (M : ℕ) (x : J → ℤ) :
    integerResidueMap I M (A *ᵥ x) =
      integerResidueMatrix (reducedIntegerMatrix A M) M *ᵥ integerResidueMap J M x := by
  rw [integerResidueMatrix_reduced]
  exact integerResidueMap_mulVec A M x

theorem exists_bounded_integerMap_residue_matrix {I J : Type*} [Fintype J] [DecidableEq J]
    (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (M : ℕ) [NeZero M] :
    ∃ A : Matrix I J ℤ,
      (∀ i j, 0 ≤ A i j ∧ A i j < M) ∧
      ∀ x, integerResidueMap I M (f x) = integerResidueMatrix A M *ᵥ integerResidueMap J M x := by
  refine ⟨reducedIntegerMatrix (LinearMap.toMatrix' f) M, reducedIntegerMatrix_bounds _ M, ?_⟩
  intro x
  rw [← LinearMap.toMatrix'_mulVec f x]
  exact reducedIntegerMatrix_residue _ M x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

def residueMatrixShift {I J : Type*} [Fintype J]
    (C D : Matrix I J ℤ) (q : ℕ) (r : J → ℤ) : I → ℤ :=
  fun i => ((C - D) *ᵥ r) i / (q : ℤ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def residueRefinedPeriod {X : Type*} [Fintype X] (m : ℕ) (q : X → ℕ) : ℕ :=
  m * ∏ d, q d

theorem residueRefinedPeriod_pos {X : Type*} [Fintype X]
    {m : ℕ} (hm : 0 < m) (q : X → ℕ) (hq : ∀ d, 0 < q d) :
    0 < residueRefinedPeriod m q :=
  Nat.mul_pos hm (Finset.prod_pos (fun d _ => hq d))

theorem stride_mul_dvd_residueRefinedPeriod {X : Type*} [Fintype X]
    (m : ℕ) (q : X → ℕ) (d : X) : q d * m ∣ residueRefinedPeriod m q := by
  classical
  obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem q (Finset.mem_univ d)
  refine ⟨a, ?_⟩
  unfold residueRefinedPeriod
  rw [ha]
  ring

theorem residueRefinedPeriod_exp_bound {X : Type*} [Fintype X]
    (m : ℕ) (q : X → ℕ) {P R : ℝ}
    (hm : (m : ℝ) ≤ Real.exp P) (hq : ∀ d, (q d : ℝ) ≤ Real.exp R) :
    (residueRefinedPeriod m q : ℝ) ≤ Real.exp (P + Fintype.card X * R) := by
  have hprod : (∏ d, (q d : ℝ)) ≤ Real.exp R ^ Fintype.card X := by
    calc
      _ ≤ ∏ _d : X, Real.exp R :=
        Finset.prod_le_prod (fun direction _ => Nat.cast_nonneg (q direction))
          (fun direction _ => hq direction)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ]
  have h := mul_le_mul hm hprod (Finset.prod_nonneg (fun d _ => Nat.cast_nonneg (q d))) (Real.exp_pos P).le
  simpa only [residueRefinedPeriod, Nat.cast_mul, Nat.cast_prod, Real.exp_add, Real.exp_nat_mul] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerCokernelExponent
namespace OAI

section

namespace Erdos3

noncomputable def integerCokernelExponent {I : Type*} (L : Submodule ℤ (I → ℤ)) : ℕ :=
  AddMonoid.exponent ((I → ℤ) ⧸ L.toAddSubgroup)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CharacterCoordinateScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def latticeCharacterCoordinates {I : Type*} [DecidableEq I] (χ : AddChar (I → ℤ) ℂ) (i : I) : ℂ :=
  χ (Pi.single i 1)

theorem integerVector_sum_single {I : Type*} [Fintype I] [DecidableEq I] (v : I → ℤ) :
    v = ∑ i, v i • (Pi.single i 1 : I → ℤ) := by
  ext i
  simp [Pi.single_apply]

theorem latticeCharacter_eval {I : Type*} [Fintype I] [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (v : I → ℤ) :
    χ v = ∏ i, latticeCharacterCoordinates χ i ^ (v i : ℤ) := by
  have hsum (s : Finset I) : χ (∑ i ∈ s, v i • (Pi.single i 1 : I → ℤ)) =
      ∏ i ∈ s, latticeCharacterCoordinates χ i ^ (v i : ℤ) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, χ.map_add_eq_mul, ih]
      rw [χ.map_zsmul_eq_zpow]
      rfl
  rw [integerVector_sum_single v]
  convert hsum Finset.univ using 1
  apply Finset.prod_congr rfl
  intro i _
  simp [Pi.single_apply]

theorem latticeCharacterCoordinates_injective {I : Type*} [Fintype I] [DecidableEq I] :
    Function.Injective (latticeCharacterCoordinates (I := I)) := by
  intro χ ψ h
  ext v
  rw [latticeCharacter_eval, latticeCharacter_eval, h]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

abbrev TorsionLatticeCharacter (I : Type*) (a : ℕ) :=
  {χ : AddChar (I → ℤ) ℂ // χ ^ a = 1}

noncomputable def torsionCharacterCoordinates {I : Type*} [DecidableEq I] {a : ℕ} [NeZero a]
    (χ : TorsionLatticeCharacter I a) (i : I) : rootsOfUnity a ℂ :=
  rootsOfUnity.mkOfPowEq (latticeCharacterCoordinates χ.val i)
    (congrArg (fun ψ : AddChar (I → ℤ) ℂ => ψ (Pi.single i 1)) χ.property)

theorem torsionCharacterCoordinates_injective {I : Type*} [Fintype I] [DecidableEq I]
    {a : ℕ} [NeZero a] :
    Function.Injective (torsionCharacterCoordinates (I := I) (a := a)) := by
  intro χ ψ h
  apply Subtype.ext
  apply latticeCharacterCoordinates_injective
  funext i
  exact congrArg (fun z : rootsOfUnity a ℂ => (z.val : ℂ)) (congrFun h i)

noncomputable instance torsionLatticeCharacterFintype (I : Type*) [Fintype I] (a : ℕ) [NeZero a] :
    Fintype (TorsionLatticeCharacter I a) := by
  classical
  let _ : Fintype (rootsOfUnity a ℂ) := Fintype.ofFinite _
  exact Fintype.ofInjective torsionCharacterCoordinates torsionCharacterCoordinates_injective

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedSummandCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

noncomputable def finiteCorrelation {Ω : Type*} (Q : Finset Ω) (f u : Ω → ℂ) : ℂ :=
  𝔼 x ∈ Q, f x * star (u x)

theorem finiteCorrelation_sub_right {Ω : Type*} (Q : Finset Ω) (f u v : Ω → ℂ) :
    finiteCorrelation Q f (fun x => u x - v x) =
      finiteCorrelation Q f u - finiteCorrelation Q f v := by
  simp only [finiteCorrelation, star_sub, mul_sub, Finset.expect_sub_distrib]

theorem finiteCorrelation_sum_right {Ω J : Type*} [Fintype J]
    (Q : Finset Ω) (f : Ω → ℂ) (u : J → Ω → ℂ) :
    finiteCorrelation Q f (fun x => ∑ j, u j x) = ∑ j, finiteCorrelation Q f (u j) := by
  simp only [finiteCorrelation, star_sum, Finset.mul_sum, Finset.expect_sum_comm]

theorem norm_finiteCorrelation_le {Ω : Type*} {Q : Finset Ω} (hQ : Q.Nonempty)
    (f u : Ω → ℂ) {B : ℝ} (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hu : ∀ x ∈ Q, ‖u x‖ ≤ B) :
    ‖finiteCorrelation Q f u‖ ≤ B := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply (Finset.expect_le_expect _).trans_eq (Finset.expect_const hQ B)
  intro x hx
  simpa only [norm_mul, norm_star, one_mul] using
    mul_le_mul (hf x hx) (hu x hx) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem norm_finiteCorrelation_sub_le {Ω : Type*} {Q : Finset Ω} (hQ : Q.Nonempty)
    (f u v : Ω → ℂ) {δ : ℝ} (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (huv : ∀ x ∈ Q, ‖u x - v x‖ ≤ δ) :
    ‖finiteCorrelation Q f u - finiteCorrelation Q f v‖ ≤ δ := by
  rw [← finiteCorrelation_sub_right]
  exact norm_finiteCorrelation_le hQ f _ hf huv

theorem exists_correlating_summand {Ω J : Type*} [Fintype J]
    {Q : Finset Ω} (hQ : Q.Nonempty) (f u : Ω → ℂ) (v : J → Ω → ℂ)
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M) (hcard : (Fintype.card J : ℝ) ≤ M)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (happrox : ∀ x ∈ Q, ‖(∑ j, v j x) - u x‖ ≤ ρ / 2)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f u‖) :
    ∃ j, ρ / (2 * M) ≤ ‖finiteCorrelation Q f (v j)‖ := by
  classical
  have herr := norm_finiteCorrelation_sub_le hQ f (fun x => ∑ j, v j x) u hf happrox
  rw [finiteCorrelation_sum_right] at herr
  have htriangle := norm_le_norm_add_norm_sub
    (∑ j, finiteCorrelation Q f (v j)) (finiteCorrelation Q f u)
  have hsum : ρ / 2 ≤ ∑ j, ‖finiteCorrelation Q f (v j)‖ := by
    have hn := norm_sum_le (Finset.univ : Finset J) (fun j => finiteCorrelation Q f (v j))
    linarith
  have hJ : (Finset.univ : Finset J).Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty] at hsum
    linarith
  have hthreshold : 0 ≤ ρ / (2 * M) := le_of_lt (div_pos hρ (by positivity))
  have hconstants : (∑ _j : J, ρ / (2 * M)) ≤ ρ / 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ ≤ M * (ρ / (2 * M)) := mul_le_mul_of_nonneg_right hcard hthreshold
      _ = ρ / 2 := by field_simp
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le hJ (hconstants.trans hsum)
  exact ⟨j, hj⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteSiteExtension {T X : Type*} [Nonempty T]
    (e : T → X) (f : T → ℂ) : X → ℂ := fun x => f (Function.invFun e x)

theorem finiteSiteExtension_apply {T X : Type*} [Nonempty T]
    (e : T → X) (he : Function.Injective e) (f : T → ℂ) (t : T) :
    finiteSiteExtension e f (e t) = f t := by
  rw [finiteSiteExtension, Function.leftInverse_invFun he t]

theorem finiteSiteExtension_norm_le {T X : Type*} [Nonempty T]
    (e : T → X) (f : T → ℂ) {B : ℝ} (hf : ∀ t, ‖f t‖ ≤ B) (x : X) :
    ‖finiteSiteExtension e f x‖ ≤ B := hf _

theorem finiteSiteExtension_test_mean {T X : Type*} [Nonempty T] [DecidableEq X]
    (e : T → X) (he : Function.Injective e) (A : Finset T)
    (f w : T → ℂ) (ψ : X → ℂ) (hw : ∀ t ∈ A, w t = star (ψ (e t))) :
    (𝔼 t ∈ A, f t * w t) = finiteCorrelation (A.image e) (finiteSiteExtension e f) ψ := by
  unfold finiteCorrelation
  rw [Finset.expect_image he.injOn]
  apply Finset.expect_congr rfl
  intro t ht
  rw [finiteSiteExtension_apply e he, hw t ht]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_correlating_weighted_summand {Ω J : Type*} [Fintype J]
    {Q : Finset Ω} (hQ : Q.Nonempty) (f u : Ω → ℂ) (v : J → Ω → ℂ) (c : J → ℂ)
    {ρ M B : ℝ} (hρ : 0 < ρ) (hM : 0 < M) (hB : 0 < B)
    (hcard : (Fintype.card J : ℝ) ≤ M) (hc : ∀ j, ‖c j‖ ≤ B)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (happrox : ∀ x ∈ Q, ‖(∑ j, c j * v j x) - u x‖ ≤ ρ / 2)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f u‖) :
    ∃ j, ρ / (2 * M * B) ≤ ‖finiteCorrelation Q f (v j)‖ := by
  obtain ⟨j, hj⟩ := exists_correlating_summand hQ f u (fun j x => c j * v j x)
    hρ hM hcard hf happrox hcorr
  have heq : finiteCorrelation Q f (fun x => c j * v j x) =
      star (c j) * finiteCorrelation Q f (v j) := by
    unfold finiteCorrelation
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    simp only [star_mul]
    ring
  rw [heq, norm_mul, norm_star] at hj
  refine ⟨j, ?_⟩
  rw [← div_div]
  apply (div_le_iff₀ hB).mpr
  simpa only [mul_comm] using hj.trans
    (mul_le_mul_of_nonneg_right (hc j) (norm_nonneg _))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitz_mul_star_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℂ) {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) :
    LipschitzWith (Bf * Kg + Bg * Kf) (fun x => f x * star (g x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have he : f x * star (g x) - f y * star (g y) =
      f x * star (g x - g y) + (f x - f y) * star (g y) := by
    rw [star_sub]
    ring
  rw [he]
  calc
    _ ≤ ‖f x * star (g x - g y)‖ + ‖(f x - f y) * star (g y)‖ := norm_add_le _ _
    _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by rw [norm_mul, norm_mul, norm_star, norm_star]
    _ ≤ Bf * (Kg * dist x y) + (Kf * dist x y) * Bg := by
      apply add_le_add
      · exact mul_le_mul (hBf x) (by simpa only [dist_eq_norm] using hg.dist_le_mul x y)
          (norm_nonneg _) Bf.coe_nonneg
      · exact mul_le_mul (by simpa only [dist_eq_norm] using hf.dist_le_mul x y) (hBg y)
          (norm_nonneg _) (mul_nonneg Kf.coe_nonneg dist_nonneg)
    _ = _ := by push_cast; ring

end Erdos3

end

section

open scoped NNReal BigOperators

namespace Erdos3

theorem lipschitz_mul_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℂ) {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) :
    LipschitzWith (Bf * Kg + Bg * Kf) (fun x => f x * g x) := by
  have hstar : LipschitzWith Kg (fun x => star (g x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← star_sub, norm_star] using hg.dist_le_mul x y
  simpa only [star_star] using lipschitz_mul_star_of_bounds f (fun x => star (g x)) hf hstar
    hBf (fun x => by simpa only [norm_star] using hBg x)

theorem bounded_lipschitz_finset_prod {ι X : Type*} [PseudoMetricSpace X]
    (s : Finset ι) (f : ι → X → ℂ) {B K : ℝ≥0} (hB : 1 ≤ B)
    (hf : ∀ i ∈ s, LipschitzWith K (f i)) (hn : ∀ i ∈ s, ∀ x, ‖f i x‖ ≤ B) :
    (∀ x, ‖∏ i ∈ s, f i x‖ ≤ (B : ℝ) ^ s.card) ∧
      LipschitzWith (s.card * K * B ^ s.card) (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    constructor
    · intro x
      simp
    · simpa only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero, zero_mul] using
        (LipschitzWith.const (α := X) (1 : ℂ))
  | @insert a s ha ih =>
    obtain ⟨hns, hls⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hn i (Finset.mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    constructor
    · intro x
      rw [norm_mul, pow_succ']
      exact mul_le_mul (hn a (Finset.mem_insert_self _ _) x) (hns x) (norm_nonneg _) B.coe_nonneg
    · have hm := lipschitz_mul_of_bounds (f a) (fun x => ∏ i ∈ s, f i x)
        (hf a (Finset.mem_insert_self _ _)) hls (hn a (Finset.mem_insert_self _ _))
        (Bg := B ^ s.card) (fun x => by simpa only [NNReal.coe_pow] using hns x)
      apply hm.weaken
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      have hh := mul_le_mul_of_nonneg_left hB (show 0 ≤ K * B ^ s.card from zero_le)
      nlinarith

theorem bounded_lipschitz_fintype_prod {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    (f : ι → X → ℂ) {B K : ℝ≥0} (hB : 1 ≤ B)
    (hf : ∀ i, LipschitzWith K (f i)) (hn : ∀ i x, ‖f i x‖ ≤ B) :
    (∀ x, ‖∏ i, f i x‖ ≤ (B : ℝ) ^ Fintype.card ι) ∧
      LipschitzWith (Fintype.card ι * K * B ^ Fintype.card ι) (fun x => ∏ i, f i x) := by
  simpa only [Finset.card_univ] using
    bounded_lipschitz_finset_prod Finset.univ f hB (fun i _ => hf i) (fun i _ => hn i)

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators NNReal

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem lipschitz_real_mul_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℝ) {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, |f x| ≤ Bf) (hBg : ∀ x, |g x| ≤ Bg) :
    LipschitzWith (Bf * Kg + Bg * Kf) (fun x => f x * g x) := by
  have hfc : LipschitzWith Kf (fun x => (f x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hf.dist_le_mul x y
  have hgc : LipschitzWith Kg (fun x => (g x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hg.dist_le_mul x y
  have h := lipschitz_mul_of_bounds _ _ hfc hgc
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hBf x)
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hBg x)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [← Complex.ofReal_mul, Complex.isometry_ofReal.dist_eq] using h.dist_le_mul x y

theorem bounded_lipschitz_real_prod {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    (f : ι → X → ℝ) {B K : ℝ≥0} (hB : 1 ≤ B)
    (hf : ∀ i, LipschitzWith K (f i)) (hn : ∀ i x, |f i x| ≤ B) :
    (∀ x, |∏ i, f i x| ≤ (B : ℝ)^Fintype.card ι) ∧
      LipschitzWith (Fintype.card ι * K * B^Fintype.card ι) (fun x => ∏ i, f i x) := by
  have hfc (i : ι) : LipschitzWith K (fun x => (f i x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact (hf i).dist_le_mul x y
  obtain ⟨hb, hl⟩ := bounded_lipschitz_fintype_prod (fun i x => (f i x : ℂ)) hB hfc
    (fun i x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hn i x)
  constructor
  · intro x
    simpa only [← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs] using hb x
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [← Complex.ofReal_prod, Complex.isometry_ofReal.dist_eq] using hl.dist_le_mul x y

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem siteFactorTensor_factor_bound {D U : Type*} [Fintype D] (f : D → U → ℂ)
    (hf : ∀ d x, ‖f d x‖ ≤ 1) (x : D → U) : ‖∏ d, f d (x d)‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun d _ => hf d (x d))

theorem siteFactorTensor_factor_lipschitz {D U : Type*} [Fintype D] [PseudoMetricSpace U]
    (f : D → U → ℂ) {K : ℝ≥0} (hf : ∀ d, LipschitzWith K (f d))
    (hn : ∀ d x, ‖f d x‖ ≤ 1) :
    LipschitzWith (Fintype.card D * K) (fun x : D → U => ∏ d, f d (x d)) := by
  have hcoord (d : D) : LipschitzWith K (fun x : D → U => f d (x d)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hf d).dist_le_mul _ _ |>.trans (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y d) K.coe_nonneg)
  simpa only [one_pow, mul_one] using
    (bounded_lipschitz_fintype_prod (fun d (x : D → U) => f d (x d))
      (B := 1) le_rfl hcoord (fun d x => hn d (x d))).2

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {S T U D : Type*} [Fintype S] [Fintype T]

def bufferedSiteFactor (y : S → U → D → ℝ) (χ : S → U → ℂ)
    (f : T → S → (D → ℝ) → ℂ) (k : T) (s : S) (u : U) : ℂ :=
  χ s u*f k s (y s u)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RectangularLatticeCells
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def latticeSample (a S x : ℝ) : ℝ := (⌊a + S * x⌋ - a) / S

def latticeSamplingCell (a S : ℝ) (k : ℤ) : Set ℝ :=
  Set.Ico (((k : ℝ) - a) / S) (((k : ℝ) + 1 - a) / S)

theorem latticeSamplingCell_measurable (a S : ℝ) (k : ℤ) :
    MeasurableSet (latticeSamplingCell a S k) := measurableSet_Ico

theorem latticeSamplingCell_iff {a S x : ℝ} (hS : 0 < S) (k : ℤ) :
    x ∈ latticeSamplingCell a S k ↔ ⌊a + S * x⌋ = k := by
  rw [Int.floor_eq_iff]
  change (((k : ℝ) - a) / S ≤ x ∧ x < ((k : ℝ) + 1 - a) / S) ↔ _
  rw [div_le_iff₀ hS, lt_div_iff₀ hS]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

theorem latticeSamplingCell_volume {a S : ℝ} (hS : 0 < S) (k : ℤ) :
    volume.real (latticeSamplingCell a S k) = 1 / S := by
  rw [measureReal_def, latticeSamplingCell, Real.volume_Ico]
  have he : (((k : ℝ) + 1 - a) / S - ((k : ℝ) - a) / S) = 1 / S := by ring
  rw [he, ENNReal.toReal_ofReal (div_nonneg zero_le_one hS.le)]

theorem latticeSample_error {a S : ℝ} (hS : 0 < S) (x : ℝ) :
    |latticeSample a S x - x| ≤ 1 / S := by
  have hlo := Int.floor_le (a + S * x)
  have hhi := Int.lt_floor_add_one (a + S * x)
  have he : latticeSample a S x - x =
      (((⌊a + S * x⌋ : ℤ) : ℝ) - (a + S * x)) / S := by
    unfold latticeSample
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hS]
  apply div_le_div_of_nonneg_right _ hS.le
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def finiteLatticeHistogram (s : Finset ℤ) (w : ℤ → ℝ) (a S x : ℝ) : ℝ :=
  ∑ k ∈ s, (latticeSamplingCell a S k).indicator (fun _ => w k) x

theorem latticeSamplingCell_indicator_integrable (a S : ℝ) (k : ℤ) (v : ℝ) :
    Integrable ((latticeSamplingCell a S k).indicator (fun _ => v)) := by
  apply (integrable_indicator_iff (latticeSamplingCell_measurable a S k)).mpr
  exact integrableOn_const (by simp [latticeSamplingCell, Real.volume_Ico])

theorem finiteLatticeHistogram_integrable (s : Finset ℤ) (w : ℤ → ℝ) (a S : ℝ) :
    Integrable (finiteLatticeHistogram s w a S) := by
  apply integrable_finsetSum
  intro k _
  exact latticeSamplingCell_indicator_integrable a S k (w k)

theorem finiteLatticeHistogram_integral (s : Finset ℤ) (w : ℤ → ℝ) (a : ℝ)
    {S : ℝ} (hS : 0 < S) :
    (∫ x, finiteLatticeHistogram s w a S x) = (∑ k ∈ s, w k) / S := by
  unfold finiteLatticeHistogram
  rw [integral_finsetSum]
  · simp only [integral_indicator_const _ (latticeSamplingCell_measurable a S _),
      latticeSamplingCell_volume hS, smul_eq_mul, one_div]
    rw [← Finset.mul_sum]
    ring
  · intro k _
    exact latticeSamplingCell_indicator_integrable a S k (w k)

theorem finiteLatticeHistogram_eq_floor (s : Finset ℤ) (w : ℤ → ℝ)
    (hw : ∀ k, k ∉ s → w k = 0) (a : ℝ) {S : ℝ} (hS : 0 < S) (x : ℝ) :
    finiteLatticeHistogram s w a S x = w ⌊a + S * x⌋ := by
  classical
  unfold finiteLatticeHistogram
  rw [Finset.sum_eq_single ⌊a + S * x⌋]
  · exact Set.indicator_of_mem ((latticeSamplingCell_iff hS _).mpr rfl) _
  · intro k _ hne
    apply Set.indicator_of_notMem
    intro hk
    exact hne ((latticeSamplingCell_iff hS k).mp hk).symm
  · intro hn
    rw [hw _ hn]
    simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def rectangularLatticePoint (a S : J → ℝ) (k : J → ℤ) : J → ℝ :=
  fun j => ((k j : ℝ) - a j) / S j

noncomputable def rectangularLatticeRound (a S x : J → ℝ) : J → ℤ :=
  fun j => ⌊a j + S j * x j⌋

noncomputable def rectangularLatticeSample (a S x : J → ℝ) : J → ℝ :=
  rectangularLatticePoint a S (rectangularLatticeRound a S x)

def rectangularLatticeCell (a S : J → ℝ) (k : J → ℤ) : Set (J → ℝ) :=
  Set.univ.pi fun j => latticeSamplingCell (a j) (S j) (k j)

theorem rectangularLatticeCell_measurable (a S : J → ℝ) (k : J → ℤ) :
    MeasurableSet (rectangularLatticeCell a S k) :=
  MeasurableSet.univ_pi fun j => latticeSamplingCell_measurable (a j) (S j) (k j)

omit [Fintype J] in
theorem rectangularLatticeCell_iff (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (x : J → ℝ) (k : J → ℤ) :
    x ∈ rectangularLatticeCell a S k ↔ rectangularLatticeRound a S x = k := by
  simp only [rectangularLatticeCell, Set.mem_univ_pi, rectangularLatticeRound,
    funext_iff, latticeSamplingCell_iff (hS _)]

theorem rectangularLatticeCell_volume (a S : J → ℝ) (hS : ∀ j, 0 < S j) (k : J → ℤ) :
    volume.real (rectangularLatticeCell a S k) = (∏ j, S j)⁻¹ := by
  rw [measureReal_def, rectangularLatticeCell, volume_pi_pi, ENNReal.toReal_prod]
  change (∏ j, volume.real (latticeSamplingCell (a j) (S j) (k j))) = _
  simp only [latticeSamplingCell_volume (hS _), one_div, Finset.prod_inv_distrib]

theorem rectangularLatticeCell_volume_ne_top (a S : J → ℝ) (k : J → ℤ) :
    volume (rectangularLatticeCell a S k) ≠ ⊤ := by
  rw [rectangularLatticeCell, volume_pi_pi]
  apply ENNReal.prod_ne_top
  intro j _
  simp only [latticeSamplingCell, Real.volume_Ico, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]

theorem rectangularLatticeSample_error (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {δ : ℝ} (hδ : 0 ≤ δ) (hmesh : ∀ j, 1 / S j ≤ δ) (x : J → ℝ) :
    ‖rectangularLatticeSample a S x - x‖ ≤ δ := by
  apply (pi_norm_le_iff_of_nonneg hδ).mpr
  intro j
  exact (latticeSample_error (hS j) (x j)).trans (hmesh j)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CompactBoxIntegral
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {J : Type*} [Fintype J]

theorem compactBox_integrable (f : (J → ℝ) → ℝ) (hf : Continuous f) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) : Integrable f := by
  apply hf.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : J → ℝ) R)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  exact hx (hsupport x h)

theorem integral_norm_le_box (f : (J → ℝ) → ℝ) {R C : ℝ} (hR : 0 ≤ R)
    (hzero : ∀ x, R < ‖x‖ → f x = 0) (hbound : ∀ x, ‖x‖ ≤ R → ‖f x‖ ≤ C) :
    (∫ x, ‖f x‖) ≤ C * (2 * R) ^ Fintype.card J := by
  let s := Metric.closedBall (0 : J → ℝ) R
  have hs : MeasurableSet s := measurableSet_closedBall
  have hi : Integrable (s.indicator (fun _ : J → ℝ => C)) :=
    (integrableOn_const ((isCompact_closedBall (0 : J → ℝ) R).measure_lt_top.ne)).integrable_indicator hs
  have hb : ∀ x, ‖f x‖ ≤ s.indicator (fun _ : J → ℝ => C) x := by
    intro x
    by_cases hx : x ∈ s
    · have hx' : ‖x‖ ≤ R := by simpa only [s, Metric.mem_closedBall, dist_zero_right] using hx
      simpa only [Set.indicator_of_mem hx] using hbound x hx'
    · have hx' : R < ‖x‖ := by simpa only [s, Metric.mem_closedBall, dist_zero_right, not_le] using hx
      simp only [hzero x hx', norm_zero, Set.indicator_of_notMem hx, le_refl]
  have hv : volume.real s = (2 * R) ^ Fintype.card J := by
    rw [measureReal_def, Real.volume_pi_closedBall 0 hR, ENNReal.toReal_ofReal (by positivity)]
  calc
    _ ≤ ∫ x, s.indicator (fun _ : J → ℝ => C) x :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg (f x))) hi
        (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_indicator_const C hs, hv, smul_eq_mul]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz
namespace OAI

section

namespace Erdos3

open scoped BigOperators

structure FiniteProbabilityWeights (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

namespace FiniteProbabilityWeights

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

noncomputable def mean (f : Ω → ℝ) : ℝ := ∑ x, p.weight x * f x

noncomputable def correlation (v w : Ω → ℂ) : ℂ :=
  ∑ x, (p.weight x : ℂ) * (v x * star (w x))

theorem mean_nonneg {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ p.mean f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (hf x))

theorem mean_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : p.mean f ≤ p.mean g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x))

theorem mean_const (c : ℝ) : p.mean (fun _ => c) = c := by
  rw [mean, ← Finset.sum_mul, p.total, one_mul]

theorem mean_mul_sq_le (f g : Ω → ℝ) :
    (p.mean (fun x => f x * g x)) ^ 2 ≤
      p.mean (fun x => f x ^ 2) * p.mean (fun x => g x ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun x _ => mul_nonneg (p.nonneg x) (sq_nonneg (f x)))
    (fun x _ => mul_nonneg (p.nonneg x) (sq_nonneg (g x)))
  intro x _
  exact le_of_eq (by ring)

theorem mean_square_le (f : Ω → ℝ) : (p.mean f) ^ 2 ≤ p.mean (fun x => f x ^ 2) := by
  have h := p.mean_mul_sq_le f (fun _ => 1)
  simpa only [mul_one, one_pow, p.mean_const] using h

theorem norm_correlation_sq_le (v w : Ω → ℂ) :
    ‖p.correlation v w‖ ^ 2 ≤
      p.mean (fun x => ‖v x‖ ^ 2) * p.mean (fun x => ‖w x‖ ^ 2) := by
  have hnorm : ‖p.correlation v w‖ ≤ p.mean (fun x => ‖v x‖ * ‖w x‖) := by
    unfold correlation mean
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro x _
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (p.nonneg x)]
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (p.mean_mul_sq_le (fun x => ‖v x‖) (fun x => ‖w x‖))

theorem correlation_self (v : Ω → ℂ) :
    p.correlation v v = (p.mean (fun x => ‖v x‖ ^ 2) : ℂ) := by
  unfold correlation mean
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  change v x * (starRingEnd ℂ) (v x) = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem norm_correlation_symm (v w : Ω → ℂ) :
    ‖p.correlation v w‖ = ‖p.correlation w v‖ := by
  have h : star (p.correlation v w) = p.correlation w v := by
    unfold correlation
    simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [← h, norm_star]

theorem mean_single_norm [DecidableEq Ω] (x : Ω) :
    p.mean (fun y => ‖(Pi.single x (1 : ℂ) : Ω → ℂ) y‖) = p.weight x := by
  unfold mean
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (law : C → FiniteProbabilityWeights Ω)

noncomputable def centeredFiniteWeightDensity (z : C × Ω) : ℝ :=
  (law z.1).weight z.2

theorem centeredFiniteWeightDensity_measurable
    (hweight : ∀ x, Measurable (fun c => (law c).weight x)) :
    Measurable (centeredFiniteWeightDensity law) :=
  measurable_from_prod_countable_left hweight

omit [MeasurableSpace C] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFiniteWeightDensity_nonneg (z : C × Ω) :
    0 ≤ centeredFiniteWeightDensity law z := (law z.1).nonneg z.2

omit [MeasurableSpace C] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFiniteWeightDensity_le_one (z : C × Ω) :
    centeredFiniteWeightDensity law z ≤ 1 := by
  change (law z.1).weight z.2 ≤ 1
  rw [← (law z.1).total]
  exact Finset.single_le_sum (fun x _ => (law z.1).nonneg x) (Finset.mem_univ z.2)

theorem centeredFiniteWeightDensity_integrable
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (μ : Measure C) [IsProbabilityMeasure μ] :
    Integrable (centeredFiniteWeightDensity law) (μ.prod Measure.count) := by
  apply (integrable_const (1 : ℝ)).mono'
    (centeredFiniteWeightDensity_measurable law hweight).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_of_nonneg (centeredFiniteWeightDensity_nonneg law z)]
    exact centeredFiniteWeightDensity_le_one law z)

theorem centeredFiniteWeightDensity_integral
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (μ : Measure C) [IsProbabilityMeasure μ] :
    (∫ z, centeredFiniteWeightDensity law z ∂μ.prod Measure.count) = 1 := by
  rw [integral_prod _ (centeredFiniteWeightDensity_integrable law hweight μ)]
  simp only [centeredFiniteWeightDensity, integral_count, (law _).total]
  simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped Classical BigOperators NNReal

theorem mean_lipschitz_uniform_emetric {A X : Type*} [Fintype A] [PseudoEMetricSpace X]
    (p : FiniteProbabilityWeights A) (f : A → X → ℝ) {L : ℝ≥0}
    (hf : ∀ a, LipschitzWith L (f a)) :
    LipschitzWith L (fun x => p.mean (fun a => f a x)) := by
  let w : A → ℝ≥0 := fun a => ⟨p.weight a, p.nonneg a⟩
  have hmul (a : A) : LipschitzWith (w a) (fun x : ℝ => p.weight a * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (p.nonneg a)]
    exact le_rfl
  have hsum (s : Finset A) :
      LipschitzWith (∑ a ∈ s, w a * L) (fun x => ∑ a ∈ s, p.weight a * f a x) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simpa only [Finset.sum_insert ha, Function.comp_def] using ((hmul a).comp (hf a)).add ih
  have hw : (∑ a, w a) = 1 := by
    apply NNReal.coe_injective
    change (↑(∑ a, w a) : ℝ) = 1
    rw [NNReal.coe_sum]
    exact p.total
  simpa only [← Finset.sum_mul, hw, one_mul, mean] using hsum Finset.univ

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

def multiplicativeDerivative (f : H → ℂ) (h : H) : H → ℂ :=
  fun x ↦ f x * star (f (x + h))

noncomputable def gowersMoment : ℕ → (H → ℂ) → ℂ
  | 0, f => 𝔼 x, f x
  | j + 1, f => 𝔼 h, gowersMoment j (multiplicativeDerivative f h)

omit [AddCommGroup H] in
theorem expect_star (f : H → ℂ) : (𝔼 x, star (f x)) = star (𝔼 x, f x) := by
  simp [Fintype.expect_eq_sum_div_card]

omit [AddCommGroup H] in
theorem expect_re (f : H → ℂ) : (𝔼 x, f x).re = 𝔼 x, (f x).re := by
  simp [Fintype.expect_eq_sum_div_card]

omit [AddCommGroup H] in
theorem expect_im (f : H → ℂ) : (𝔼 x, f x).im = 𝔼 x, (f x).im := by
  simp [Fintype.expect_eq_sum_div_card]

theorem expect_translate (f : H → ℂ) (x : H) : (𝔼 h, f (x + h)) = 𝔼 h, f h := by
  exact Fintype.expect_equiv (Equiv.addLeft x) _ f (fun _ ↦ rfl)

omit [Fintype H] in
theorem multiplicativeDerivative_comm (f : H → ℂ) (h k : H) :
    multiplicativeDerivative (multiplicativeDerivative f h) k =
      multiplicativeDerivative (multiplicativeDerivative f k) h := by
  funext x
  simp only [multiplicativeDerivative, star_mul, star_star]
  rw [show x + k + h = x + h + k by abel]
  ring

theorem gowersMoment_one (f : H → ℂ) :
    gowersMoment 1 f = (𝔼 x, f x) * star (𝔼 x, f x) := by
  change (𝔼 h, 𝔼 x, f x * star (f (x + h))) = _
  rw [Finset.expect_comm]
  calc
    (𝔼 x, 𝔼 h, f x * star (f (x + h))) =
        𝔼 x, f x * star (𝔼 h, f h) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [← Finset.mul_expect, expect_translate (fun h ↦ star (f h)), expect_star]
    _ = _ := (Finset.expect_mul _ _ _).symm

theorem gowersMoment_re_nonneg (j : ℕ) (f : H → ℂ) :
    0 ≤ (gowersMoment (j + 1) f).re := by
  induction j generalizing f with
  | zero =>
    rw [gowersMoment_one]
    change 0 ≤ ((𝔼 x, f x) * starRingEnd ℂ (𝔼 x, f x)).re
    rw [Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  | succ j ih =>
    rw [gowersMoment, expect_re]
    exact Finset.expect_nonneg (fun h _ ↦ ih (multiplicativeDerivative f h))

theorem gowersMoment_im_zero (j : ℕ) (f : H → ℂ) :
    (gowersMoment (j + 1) f).im = 0 := by
  induction j generalizing f with
  | zero =>
    rw [gowersMoment_one]
    change ((𝔼 x, f x) * starRingEnd ℂ (𝔼 x, f x)).im = 0
    rw [Complex.mul_conj, Complex.ofReal_im]
  | succ j ih =>
    rw [gowersMoment, expect_im]
    exact Finset.expect_eq_zero (fun h _ ↦ ih (multiplicativeDerivative f h))

theorem gowersMoment_const_one (j : ℕ) : gowersMoment j (fun _ : H ↦ 1) = 1 := by
  induction j with
  | zero => simp [gowersMoment]
  | succ j ih =>
    change (𝔼 h : H, gowersMoment j (multiplicativeDerivative (fun _ : H ↦ 1) h)) = 1
    have hder (h : H) : multiplicativeDerivative (fun _ : H ↦ 1) h = (fun _ : H ↦ 1) := by
      funext x
      simp [multiplicativeDerivative]
    simp_rw [hder, ih]
    exact Fintype.expect_one (ι := H)

noncomputable def gowersNorm (j : ℕ) (f : H → ℂ) : ℝ :=
  (gowersMoment j f).re ^ (((2 ^ j : ℕ) : ℝ)⁻¹)

theorem gowersNorm_nonneg (j : ℕ) (f : H → ℂ) : 0 ≤ gowersNorm (j + 1) f :=
  Real.rpow_nonneg (gowersMoment_re_nonneg j f) _

theorem gowersNorm_pow (j : ℕ) (f : H → ℂ) :
    gowersNorm (j + 1) f ^ (2 ^ (j + 1)) = (gowersMoment (j + 1) f).re := by
  exact Real.rpow_inv_natCast_pow (n := 2 ^ (j + 1)) (gowersMoment_re_nonneg j f)
    (pow_ne_zero _ (by norm_num))

theorem gowersNorm_one (f : H → ℂ) : gowersNorm 1 f = ‖𝔼 x, f x‖ := by
  have hmoment : (gowersMoment 1 f).re = ‖𝔼 x, f x‖ ^ 2 := by
    rw [gowersMoment_one]
    change ((𝔼 x, f x) * starRingEnd ℂ (𝔼 x, f x)).re = _
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  unfold gowersNorm
  rw [hmoment]
  norm_num only [pow_one, Nat.cast_ofNat]
  simpa using Real.pow_rpow_inv_natCast (norm_nonneg (𝔼 x : H, f x))
    (by norm_num : (2 : ℕ) ≠ 0)

theorem gowersNorm_const_one (j : ℕ) : gowersNorm j (fun _ : H ↦ 1) = 1 := by
  simp [gowersNorm, gowersMoment_const_one]

theorem gowersNorm_derivative (j : ℕ) (f : H → ℂ) :
    gowersNorm (j + 2) f ^ (2 ^ (j + 2)) =
      𝔼 h, gowersNorm (j + 1) (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) := by
  simp only [gowersNorm_pow]
  exact expect_re _

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

def conjugationPower : ℕ → (ℂ →+* ℂ)
  | 0 => RingHom.id ℂ
  | n + 1 => (starRingEnd ℂ).comp (conjugationPower n)

theorem conjugationPower_star (n : ℕ) (z : ℂ) :
    conjugationPower n (star z) = star (conjugationPower n z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change star (conjugationPower n (star z)) = star (star (conjugationPower n z))
    exact congrArg star ih

variable {H : Type*} [AddCommGroup H]

def cubeProduct (f : H → ℂ) (hs : List H) (x : H) : ℂ :=
  (hs.sublists'.map fun ks ↦ conjugationPower ks.length (f (x + ks.sum))).prod

@[simp] theorem cubeProduct_nil (f : H → ℂ) (x : H) : cubeProduct f [] x = f x := by
  simp [cubeProduct, conjugationPower]

theorem cubeProduct_cons (f : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct f (h :: hs) x = cubeProduct f hs x * star (cubeProduct f hs (x + h)) := by
  simp only [cubeProduct, List.sublists'_cons, List.map_append, List.prod_append,
    List.map_map, Function.comp_def, List.length_cons, List.sum_cons,
    conjugationPower, RingHom.comp_apply]
  congr 1
  change _ = (starRingEnd ℂ) _
  rw [map_list_prod, List.map_map]
  simp only [Function.comp_def, add_assoc]

theorem cubeProduct_derivative (f : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct (multiplicativeDerivative f h) hs x =
      cubeProduct f hs x * star (cubeProduct f hs (x + h)) := by
  induction hs generalizing x with
  | nil => simp [multiplicativeDerivative]
  | cons k hs ih =>
    simp only [cubeProduct_cons, ih, star_mul, star_star]
    rw [show x + k + h = x + h + k by abel]
    ring

theorem cubeProduct_cons_eq_derivative (f : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct f (h :: hs) x = cubeProduct (multiplicativeDerivative f h) hs x := by
  rw [cubeProduct_cons, cubeProduct_derivative]

variable [Fintype H]

noncomputable def cubeAverage {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] :
    ℕ → (List H → M) → M
  | 0, F => F []
  | j + 1, F => 𝔼 h, cubeAverage j (fun hs ↦ F (h :: hs))

omit [AddCommGroup H] in

theorem cubeAverage_eq_expect_tuple {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (j : ℕ) (F : List H → M) :
    cubeAverage j F = 𝔼 h : Fin j → H, F (List.ofFn h) := by
  induction j generalizing F with
  | zero => simp [cubeAverage]
  | succ j ih =>
    rw [cubeAverage, expect_fin_cons]
    apply Finset.expect_congr rfl
    intro h hh
    rw [ih]
    apply Finset.expect_congr rfl
    intro hs hhs
    simp

omit [AddCommGroup H] in
theorem cubeAverage_re (j : ℕ) (F : List H → ℂ) :
    (cubeAverage j F).re = cubeAverage j (fun hs ↦ (F hs).re) := by
  simp only [cubeAverage_eq_expect_tuple, expect_re]

omit [AddCommGroup H] in
theorem cubeAverage_comm_expect {Ω : Type*} [Fintype Ω]
    {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (j : ℕ) (F : List H → Ω → M) :
    cubeAverage j (fun hs ↦ 𝔼 x, F hs x) = 𝔼 x, cubeAverage j (fun hs ↦ F hs x) := by
  simp only [cubeAverage_eq_expect_tuple]
  exact Finset.expect_comm _ _ _

omit [AddCommGroup H] in
theorem cubeAverage_norm_inner_sq_le (j : ℕ) (F G : List H → ℂ) :
    ‖cubeAverage j (fun hs ↦ F hs * star (G hs))‖ ^ 2 ≤
      cubeAverage j (fun hs ↦ ‖F hs‖ ^ 2) * cubeAverage j (fun hs ↦ ‖G hs‖ ^ 2) := by
  simp only [cubeAverage_eq_expect_tuple]
  exact norm_expect_mul_star_sq_le _ _

theorem gowersMoment_eq_cubeAverage (j : ℕ) (f : H → ℂ) :
    gowersMoment j f = cubeAverage j (fun hs ↦ 𝔼 x, cubeProduct f hs x) := by
  induction j generalizing f with
  | zero => simp [gowersMoment, cubeAverage]
  | succ j ih =>
    simp only [gowersMoment, cubeAverage, ih, cubeProduct_cons_eq_derivative]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω H : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

noncomputable def complexMean (v : Ω → ℂ) : ℂ := ∑ x, (p.weight x : ℂ) * v x

theorem correlation_eq_complexMean (v w : Ω → ℂ) :
    p.correlation v w = p.complexMean (fun x => v x * star (w x)) := rfl

theorem complexMean_mul_left (a : ℂ) (v : Ω → ℂ) :
    p.complexMean (fun x => a * v x) = a * p.complexMean v := by
  unfold complexMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem complexMean_re (v : Ω → ℂ) :
    (p.complexMean v).re = p.mean (fun x => (v x).re) := by
  simp [complexMean, mean, Complex.mul_re]

variable [Fintype H]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteWeightedTest {Ω T : Type*} [Fintype T]
    (ψ : T → Ω) (w : T → ℂ) : (Ω → ℂ) →ₗ[ℂ] ℂ where
  toFun v := 𝔼 t, w t * v (ψ t)
  map_add' v z := by simp only [Pi.add_apply, mul_add, Finset.expect_add_distrib]
  map_smul' c v := by
    change (𝔼 t, w t * (c * v (ψ t))) = c * (𝔼 t, w t * v (ψ t))
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro t _
    ring

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

def crossDerivative (f g : H → ℂ) (h : H) : H → ℂ :=
  fun x ↦ f x * star (g (x + h))

omit [Fintype H] in
@[simp] theorem crossDerivative_self (f : H → ℂ) (h : H) :
    crossDerivative f f h = multiplicativeDerivative f h := rfl

omit [Fintype H] in
theorem cubeProduct_crossDerivative (f g : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct (crossDerivative f g h) hs x =
      cubeProduct f hs x * star (cubeProduct g hs (x + h)) := by
  induction hs generalizing x with
  | nil => simp [crossDerivative]
  | cons k hs ih =>
    simp only [cubeProduct_cons, ih, star_mul, star_star]
    rw [show x + k + h = x + h + k by abel]
    ring

theorem expect_crossDerivative (f g : H → ℂ) :
    (𝔼 h, 𝔼 x, crossDerivative f g h x) = (𝔼 x, f x) * star (𝔼 x, g x) := by
  change (𝔼 h, 𝔼 x, f x * star (g (x + h))) = _
  rw [Finset.expect_comm]
  calc
    (𝔼 x, 𝔼 h, f x * star (g (x + h))) = 𝔼 x, f x * star (𝔼 y, g y) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [← Finset.mul_expect, expect_translate (fun y ↦ star (g y)), expect_star]
    _ = _ := (Finset.expect_mul _ _ _).symm

theorem expect_gowersMoment_crossDerivative (j : ℕ) (f g : H → ℂ) :
    (𝔼 h, gowersMoment j (crossDerivative f g h)) =
      cubeAverage j (fun hs ↦ (𝔼 x, cubeProduct f hs x) * star (𝔼 x, cubeProduct g hs x)) := by
  simp only [gowersMoment_eq_cubeAverage]
  rw [← cubeAverage_comm_expect]
  simp_rw [cubeProduct_crossDerivative]
  have hpoint : ∀ hs : List H,
      (𝔼 h, 𝔼 x, cubeProduct f hs x * star (cubeProduct g hs (x + h))) =
        (𝔼 x, cubeProduct f hs x) * star (𝔼 x, cubeProduct g hs x) := by
    intro hs
    exact expect_crossDerivative (cubeProduct f hs) (cubeProduct g hs)
  simp_rw [hpoint]

theorem mul_star_re_eq_norm_sq (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  change (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem gowersMoment_eq_average_square (j : ℕ) (f : H → ℂ) :
    (gowersMoment (j + 1) f).re =
      cubeAverage j (fun hs ↦ ‖𝔼 x, cubeProduct f hs x‖ ^ 2) := by
  have h := congrArg Complex.re (expect_gowersMoment_crossDerivative j f f)
  change (𝔼 h, gowersMoment j (multiplicativeDerivative f h)).re = _
  simpa only [crossDerivative_self, cubeAverage_re,
    mul_star_re_eq_norm_sq] using h

theorem norm_expect_gowersMoment_crossDerivative_sq_le (j : ℕ) (f g : H → ℂ) :
    ‖𝔼 h, gowersMoment j (crossDerivative f g h)‖ ^ 2 ≤
      (gowersMoment (j + 1) f).re * (gowersMoment (j + 1) g).re := by
  rw [expect_gowersMoment_crossDerivative,
    gowersMoment_eq_average_square, gowersMoment_eq_average_square]
  exact cubeAverage_norm_inner_sq_le j _ _

theorem expect_cross_gowersNorm_pow_le (j : ℕ) (f g : H → ℂ) :
    (𝔼 h, gowersNorm (j + 1) (crossDerivative f g h) ^ (2 ^ (j + 1))) ≤
      (gowersNorm (j + 2) f * gowersNorm (j + 2) g) ^ (2 ^ (j + 1)) := by
  let A := 𝔼 h, gowersNorm (j + 1) (crossDerivative f g h) ^ (2 ^ (j + 1))
  let B := (gowersNorm (j + 2) f * gowersNorm (j + 2) g) ^ (2 ^ (j + 1))
  have hA : 0 ≤ A := Finset.expect_nonneg (fun h _ ↦
    pow_nonneg (gowersNorm_nonneg j _) _)
  have hB : 0 ≤ B := pow_nonneg
    (mul_nonneg (gowersNorm_nonneg (j + 1) f) (gowersNorm_nonneg (j + 1) g)) _
  have hnorm : A ≤ ‖𝔼 h, gowersMoment (j + 1) (crossDerivative f g h)‖ := by
    dsimp [A]
    simp only [gowersNorm_pow, ← expect_re]
    exact Complex.re_le_norm _
  have hpower : (gowersMoment (j + 2) f).re * (gowersMoment (j + 2) g).re = B ^ 2 := by
    dsimp [B]
    rw [← gowersNorm_pow, ← gowersNorm_pow, ← mul_pow, ← pow_mul]
    congr 1
  have hsq : A ^ 2 ≤ B ^ 2 := (pow_le_pow_left₀ hA hnorm 2).trans
    ((norm_expect_gowersMoment_crossDerivative_sq_le (j + 1) f g).trans_eq hpower)
  change A ≤ B
  nlinarith

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]

noncomputable def pi (p : ∀ j, FiniteProbabilityWeights (Ω j)) :
    FiniteProbabilityWeights (∀ j, Ω j) := by
  classical
  exact {
    weight := fun x => ∏ j, (p j).weight (x j)
    nonneg := fun x => Finset.prod_nonneg (fun j _ => (p j).nonneg (x j))
    total := by
      calc
        _ = ∏ j, ∑ x, (p j).weight x := (Fintype.prod_sum _).symm
        _ = ∏ _j : J, (1 : ℝ) := Finset.prod_congr rfl (fun j _ => (p j).total)
        _ = 1 := by simp }

end Erdos3.FiniteProbabilityWeights

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem correlation_sq_eq_expect_derivative (f u : H → ℂ) :
    ‖finiteCorrelation Finset.univ f u‖ ^ 2 =
      𝔼 h, (finiteCorrelation Finset.univ
        (multiplicativeDerivative f h) (multiplicativeDerivative u h)).re := by
  calc
    _ = (gowersMoment 1 (fun x => f x * star (u x))).re := by
      rw [gowersMoment_one, mul_star_re_eq_norm_sq]
      rfl
    _ = _ := by
      rw [gowersMoment, expect_re]
      apply Finset.expect_congr rfl
      intro h _
      congr 1
      change (𝔼 x, multiplicativeDerivative (fun x => f x * star (u x)) h x) = _
      apply Finset.expect_congr rfl
      intro x _
      simp only [multiplicativeDerivative, star_mul, star_star]
      ring

theorem correlation_sq_le_expect_norm_derivative (f u : H → ℂ) :
    ‖finiteCorrelation Finset.univ f u‖ ^ 2 ≤
      𝔼 h, ‖finiteCorrelation Finset.univ
        (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ := by
  rw [correlation_sq_eq_expect_derivative]
  exact Finset.expect_le_expect (fun _ _ => Complex.re_le_norm _)

theorem norm_derivativeCorrelation_le (f u : H → ℂ) {B : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ 1) (hu : ∀ x, ‖u x‖ ≤ B) (h : H) :
    ‖finiteCorrelation Finset.univ
      (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ ≤ B ^ 2 := by
  apply norm_finiteCorrelation_le Finset.univ_nonempty
  · intro x _
    simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
      mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · intro x _
    have hB : 0 ≤ B := (norm_nonneg (u x)).trans (hu x)
    simpa only [multiplicativeDerivative, norm_mul, norm_star, pow_two] using
      mul_le_mul (hu x) (hu (x + h)) (norm_nonneg _) hB

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitExpansionCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_weighted_term {I : Type*} [Fintype I] (c z : I → ℂ)
    {delta M : ℝ} (hdelta : 0 < delta) (hM : 0 < M)
    (hc : (∑ i, ‖c i‖) ≤ M) (hsum : delta ≤ ‖∑ i, c i * z i‖) :
    ∃ i, delta / M ≤ ‖z i‖ := by
  classical
  have hI : (Finset.univ : Finset I).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, norm_zero] at hsum
    linarith
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z i‖) hI
  refine ⟨i, (div_le_iff₀ hM).mpr ?_⟩
  calc
    delta ≤ ‖∑ j, c j * z j‖ := hsum
    _ ≤ ∑ j, ‖c j * z j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖c j‖ * ‖z i‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ _)) (norm_nonneg _)
    _ = (∑ j, ‖c j‖) * ‖z i‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ M * ‖z i‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖z i‖ * M := mul_comm _ _

theorem sum_pair_coefficient_norms_le {I : Type*} {J : I → Type*}
    [Fintype I] [∀ i, Fintype (J i)] (c : I → ℂ) (d : ∀ i, J i → ℂ)
    {C D : ℝ} (hD : 0 ≤ D) (hc : (∑ i, ‖c i‖) ≤ C)
    (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D) :
    (∑ p : Sigma J, ‖c p.1 * d p.1 p.2‖) ≤ C * D := by
  rw [Fintype.sum_sigma]
  simp_rw [norm_mul, ← Finset.mul_sum]
  calc
    _ ≤ ∑ i, ‖c i‖ * D := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd i) (norm_nonneg _))
    _ = (∑ i, ‖c i‖) * D := (Finset.sum_mul _ _ _).symm
    _ ≤ C * D := mul_le_mul_of_nonneg_right hc hD

theorem exists_large_weighted_pair {I : Type*} {J : I → Type*}
    [Fintype I] [∀ i, Fintype (J i)] (c : I → ℂ) (d z : ∀ i, J i → ℂ)
    {delta C D : ℝ} (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (hc : (∑ i, ‖c i‖) ≤ C) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D)
    (hsum : delta ≤ ‖∑ i, ∑ j, (c i * d i j) * z i j‖) :
    ∃ i j, delta / (C * D) ≤ ‖z i j‖ := by
  obtain ⟨p, hp⟩ := exists_large_weighted_term
    (fun p : Sigma J => c p.1 * d p.1 p.2) (fun p => z p.1 p.2)
    hdelta (mul_pos hC hD) (sum_pair_coefficient_norms_le c d hD.le hc hd)
    (by simpa only [Fintype.sum_sigma] using hsum)
  exact ⟨p.1, p.2, hp⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_correlating_components_on_finset {X I J : Type*} [Fintype I] [Fintype J]
    (s : Finset X) (hs : s.Nonempty) (U Q R : X → ℂ) (V : I → X → ℂ) (W : J → X → ℂ)
    {delta C D rho eta : ℝ} (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (hrho : 0 ≤ rho) (_heta : 0 ≤ eta)
    (hI : (Fintype.card I : ℝ) ≤ C) (hJ : (Fintype.card J : ℝ) ≤ D)
    (hU : ∀ x ∈ s, ‖U x‖ ≤ 1) (hR : ∀ x ∈ s, ‖R x‖ ≤ 1)
    (hV : ∀ i x, x ∈ s → ‖V i x‖ ≤ 1)
    (hQa : ∀ x ∈ s, ‖Q x - ∑ i, V i x‖ ≤ rho)
    (hRa : ∀ x ∈ s, ‖R x - ∑ j, W j x‖ ≤ eta)
    (hsmall : rho + C * eta ≤ delta / 2)
    (hcorr : delta ≤ ‖𝔼 x ∈ s, U x * Q x * R x‖) :
    ∃ i j, (delta / 2) / (C * D) ≤ ‖𝔼 x ∈ s, U x * V i x * W j x‖ := by
  have hpoint (x : X) (hx : x ∈ s) :
      ‖U x * Q x * R x - ∑ i, ∑ j, U x * V i x * W j x‖ ≤ rho + C * eta := by
    have hsum : ‖∑ i, V i x‖ ≤ C := by
      apply (norm_sum_le _ _).trans
      exact (Finset.sum_le_sum (fun i _ => hV i x hx)).trans (by simpa using hI)
    have hid : U x * Q x * R x - ∑ i, ∑ j, U x * V i x * W j x =
        U x * (Q x - ∑ i, V i x) * R x +
          U x * (∑ i, V i x) * (R x - ∑ j, W j x) := by
      rw [← Finset.sum_mul_sum, ← Finset.mul_sum]
      ring
    rw [hid]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · simp only [norm_mul]
      calc
        _ ≤ 1 * rho * 1 := mul_le_mul
          (mul_le_mul (hU x hx) (hQa x hx) (norm_nonneg _) (by norm_num))
          (hR x hx) (norm_nonneg _) (by positivity)
        _ = rho := by ring
    · simp only [norm_mul]
      calc
        _ ≤ 1 * C * eta := mul_le_mul
          (mul_le_mul (hU x hx) hsum (norm_nonneg _) (by norm_num))
          (hRa x hx) (norm_nonneg _) (by positivity)
        _ = C * eta := by ring
  have hsum : (𝔼 x ∈ s, ∑ i, ∑ j, U x * V i x * W j x) =
      ∑ i, ∑ j, 𝔼 x ∈ s, U x * V i x * W j x := by
    simp_rw [Finset.expect_sum_comm]
  have herr : ‖(𝔼 x ∈ s, U x * Q x * R x) -
      (∑ i, ∑ j, 𝔼 x ∈ s, U x * V i x * W j x)‖ ≤ delta / 2 := by
    rw [← hsum, ← Finset.expect_sub_distrib]
    exact (RCLike.norm_expect_le (K := ℂ)).trans ((Finset.expect_le hs hpoint).trans hsmall)
  apply exists_large_weighted_pair (fun _ : I => (1 : ℂ)) (fun (_ : I) (_ : J) => (1 : ℂ))
    (fun i j => 𝔼 x ∈ s, U x * V i x * W j x) (by positivity) hC hD
  · simpa using hI
  · intro _
    simpa using hJ
  · simp only [one_mul]
    have htri := norm_add_le
      ((𝔼 x ∈ s, U x * Q x * R x) - (∑ i, ∑ j, 𝔼 x ∈ s, U x * V i x * W j x))
      (∑ i, ∑ j, 𝔼 x ∈ s, U x * V i x * W j x)
    rw [sub_add_cancel] at htri
    linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem complex_unit_vector_resolution {K : Type*} [Fintype K] (u : K → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 = 1) (z : ℂ) : z = ∑ k, (z * star (u k)) * u k := by
  have hunit : (∑ k, star (u k) * u k) = (1 : ℂ) := by
    calc
      _ = ∑ k, ((‖u k‖ ^ 2 : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
      _ = ((∑ k, ‖u k‖ ^ 2 : ℝ) : ℂ) := (Complex.ofReal_sum _ _).symm
      _ = 1 := by rw [hu, Complex.ofReal_one]
  rw [show (∑ k, (z * star (u k)) * u k) = z * ∑ k, star (u k) * u k by
    rw [Finset.mul_sum]; simp only [mul_assoc], hunit, mul_one]

theorem exists_unit_expansion_correlation {X K : Type*} {A : K → Type*}
    [Fintype K] [∀ k, Fintype (A k)] (s : Finset X)
    (f Q : X → ℂ) (P : K → X → ℂ) (c : ∀ k, A k → ℂ) (psi : ∀ k, A k → X → ℂ)
    (hunit : ∀ x ∈ s, ∑ k, ‖P k x‖ ^ 2 = 1)
    (hexp : ∀ k x, x ∈ s → Q x * star (P k x) = ∑ a, c k a * psi k a x)
    {rho D M : ℝ} (hrho : 0 < rho) (hD : 0 < D) (hM : 0 < M)
    (hcard : (Fintype.card K : ℝ) ≤ D) (hc : ∀ k, (∑ a, ‖c k a‖) ≤ M)
    (hcorr : rho ≤ ‖𝔼 x ∈ s, f x * Q x‖) :
    ∃ k a, rho / (D * M) ≤ ‖𝔼 x ∈ s, f x * P k x * psi k a x‖ := by
  have hpoint (x : X) (hx : x ∈ s) :
      f x * Q x = ∑ k, ∑ a, c k a * (f x * P k x * psi k a x) := by
    rw [complex_unit_vector_resolution (fun k => P k x) (hunit x hx) (Q x), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hexp k x hx, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hmean : (𝔼 x ∈ s, f x * Q x) =
      ∑ k, ∑ a, c k a * (𝔼 x ∈ s, f x * P k x * psi k a x) := by
    calc
      _ = 𝔼 x ∈ s, ∑ k, ∑ a, c k a * (f x * P k x * psi k a x) :=
        Finset.expect_congr rfl hpoint
      _ = _ := by simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  apply exists_large_weighted_pair (fun _ : K => (1 : ℂ)) c
    (fun k a => 𝔼 x ∈ s, f x * P k x * psi k a x) hrho hD hM
  · simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hcard
  · exact hc
  · simpa only [one_mul, ← hmean] using hcorr

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def finiteMask (G : Finset Ω) : (Ω → ℂ) →ₗ[ℂ] (Ω → ℂ) where
  toFun v x := if x ∈ G then v x else 0
  map_add' v w := by ext x; by_cases hx : x ∈ G <;> simp [hx]
  map_smul' c v := by ext x; by_cases hx : x ∈ G <;> simp [hx]

omit [Fintype Ω] in
@[simp] theorem finiteMask_apply (G : Finset Ω) (v : Ω → ℂ) (x : Ω) :
    finiteMask G v x = if x ∈ G then v x else 0 := rfl

namespace FiniteProbabilityWeights

variable (p : FiniteProbabilityWeights Ω) (G : Finset Ω)

omit [DecidableEq Ω] in
theorem mean_add (f g : Ω → ℝ) :
    p.mean (fun x => f x + g x) = p.mean f + p.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

omit [DecidableEq Ω] in
theorem mean_const_mul (c : ℝ) (f : Ω → ℝ) :
    p.mean (fun x => c * f x) = c * p.mean f := by
  simp only [mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

noncomputable def mass : ℝ := ∑ x ∈ G, p.weight x

omit [DecidableEq Ω] in
theorem mass_nonneg : 0 ≤ p.mass G :=
  Finset.sum_nonneg (fun x _ => p.nonneg x)

omit [DecidableEq Ω] in
theorem mass_le_one : p.mass G ≤ 1 := by
  rw [← p.total]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
    (fun x _ _ => p.nonneg x)

omit [DecidableEq Ω] in
theorem weight_le_mass {x : Ω} (hx : x ∈ G) : p.weight x ≤ p.mass G :=
  Finset.single_le_sum (fun y _ => p.nonneg y) hx

theorem mean_indicator : p.mean (fun x => if x ∈ G then 1 else 0) = p.mass G := by
  simp [mean, mass, mul_ite]

noncomputable def condition (hG : 0 < p.mass G) : FiniteProbabilityWeights Ω where
  weight x := (if x ∈ G then p.weight x else 0) / p.mass G
  nonneg x := div_nonneg (by split_ifs; exact p.nonneg x; exact le_rfl) hG.le
  total := by
    rw [← Finset.sum_div]
    have hsum : (∑ x, if x ∈ G then p.weight x else 0) = p.mass G := by
      simp [mass]
    rw [hsum, div_self hG.ne']

theorem condition_mean (hG : 0 < p.mass G) (f : Ω → ℝ) :
    (p.condition G hG).mean f =
      p.mean (fun x => if x ∈ G then f x else 0) / p.mass G := by
  unfold mean condition
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ G <;> simp [hx, div_mul_eq_mul_div]

theorem mass_mul_condition_mean (hG : 0 < p.mass G) (f : Ω → ℝ) :
    p.mass G * (p.condition G hG).mean f =
      p.mean (fun x => if x ∈ G then f x else 0) := by
  rw [condition_mean, mul_div_cancel₀ _ hG.ne']

theorem mass_mul_condition_correlation (hG : 0 < p.mass G) (v Q : Ω → ℂ) :
    (p.mass G : ℂ) * (p.condition G hG).correlation v Q =
      p.correlation (finiteMask G v) Q := by
  unfold correlation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ G
  · simp only [condition, hx, ite_true, finiteMask_apply]
    have hm : (p.mass G : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
    push_cast
    field_simp
  · simp [condition, hx]

theorem norm_correlation_mask (hG : 0 < p.mass G) (v Q : Ω → ℂ) :
    ‖p.correlation (finiteMask G v) Q‖ =
      p.mass G * ‖(p.condition G hG).correlation v Q‖ := by
  rw [← mass_mul_condition_correlation, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (p.mass_nonneg G)]

theorem mean_mask_zero (hG : p.mass G = 0) (f : Ω → ℝ) :
    p.mean (fun x => if x ∈ G then f x else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x ∈ G
  · have hw : p.weight x = 0 := le_antisymm
      (by simpa [hG] using p.weight_le_mass G hx) (p.nonneg x)
    simp [hx, hw]
  · simp [hx]

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem complexMean_sub (f g : X → ℂ) :
    p.complexMean (fun x => f x - g x) = p.complexMean f - p.complexMean g := by
  simp only [complexMean, mul_sub, Finset.sum_sub_distrib]

theorem complexMean_ofReal (f : X → ℝ) :
    p.complexMean (fun x => (f x : ℂ)) = (p.mean f : ℂ) := by
  simp only [complexMean, mean, Complex.ofReal_sum, Complex.ofReal_mul]

theorem complexMean_finset_expect {V : Type*} (s : Finset V) (f : X → V → ℂ) :
    p.complexMean (fun x => 𝔼 v ∈ s, f x v) = 𝔼 v ∈ s, p.complexMean (fun x => f x v) := by
  unfold complexMean
  simp_rw [Finset.mul_expect]
  exact (Finset.expect_sum_comm _ _ _).symm

theorem norm_complexMean_le_mean_norm (f : X → ℂ) :
    ‖p.complexMean f‖ ≤ p.mean (fun x => ‖f x‖) := by
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro x _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (p.nonneg x)]

theorem norm_complexMean_sub_le (f g : X → ℂ) (e : X → ℝ)
    (h : ∀ x, p.weight x ≠ 0 → ‖f x - g x‖ ≤ e x) :
    ‖p.complexMean f - p.complexMean g‖ ≤ p.mean e := by
  rw [← p.complexMean_sub]
  apply (p.norm_complexMean_le_mean_norm _).trans
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left (h x hx) (p.nonneg x)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X R : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

noncomputable def fiberMean (F : X → R) (r : R) (f : X → ℝ) : ℝ := by
  classical
  exact p.mean (fun x => if F x = r then f x else 0)

theorem fiberMean_nonneg (F : X → R) (r : R) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ p.fiberMean F r f := by
  classical
  apply p.mean_nonneg
  intro x
  split_ifs
  · exact hf x
  · exact le_rfl

theorem sum_fiberMean [Fintype R] (F : X → R) (f : X → ℝ) :
    (∑ r, p.fiberMean F r f) = p.mean f := by
  classical
  unfold fiberMean mean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  simp

noncomputable def fiberLaw [Fintype R] (F : X → R) : FiniteProbabilityWeights R where
  weight r := p.fiberMean F r (fun _ => 1)
  nonneg r := p.fiberMean_nonneg F r (fun _ => 1) (fun _ => zero_le_one)
  total := by rw [p.sum_fiberMean, p.mean_const]

theorem fiberLaw_weight [Fintype R] (F : X → R) (r : R) :
    (p.fiberLaw F).weight r = p.fiberMean F r (fun _ => 1) := rfl

theorem complexMean_fiber_factor [Fintype R] (F : X → R) (f : X → ℝ) (a : R → ℂ) :
    p.complexMean (fun x => (f x : ℂ) * a (F x)) =
      ∑ r, (p.fiberMean F r f : ℂ) * a r := by
  classical
  unfold complexMean fiberMean mean
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have he (r : R) : ((if F x = r then f x else 0 : ℝ) : ℂ) =
      if F x = r then (f x : ℂ) else 0 := by split_ifs <;> rfl
  simp [he, mul_ite, ite_mul, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators

variable {X C : Type*} [Fintype X] [MeasurableSpace C] (p : FiniteProbabilityWeights X)

theorem mean_measurable (f : C → X → ℝ) (hf : ∀ x, Measurable (fun c => f c x)) :
    Measurable (fun c => p.mean (f c)) :=
  Finset.measurable_sum _ (fun x _ => (hf x).const_mul (p.weight x))

theorem mean_integrable (μ : Measure C) (f : C → X → ℝ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    Integrable (fun c => p.mean (f c)) μ :=
  integrable_finsetSum _ (fun x _ => (hf x).const_mul (p.weight x))

theorem integral_mean (μ : Measure C) (f : C → X → ℝ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    (∫ c, p.mean (f c) ∂μ) = p.mean (fun x => ∫ c, f c x ∂μ) := by
  unfold mean
  rw [integral_finsetSum _ (fun x _ => (hf x).const_mul (p.weight x))]
  simp only [integral_const_mul]

theorem complexMean_measurable (f : C → X → ℂ) (hf : ∀ x, Measurable (fun c => f c x)) :
    Measurable (fun c => p.complexMean (f c)) :=
  Finset.measurable_sum _ (fun x _ => (hf x).const_mul (p.weight x : ℂ))

theorem complexMean_integrable (μ : Measure C) (f : C → X → ℂ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    Integrable (fun c => p.complexMean (f c)) μ :=
  integrable_finsetSum _ (fun x _ => (hf x).const_mul (p.weight x : ℂ))

theorem integral_complexMean (μ : Measure C) (f : C → X → ℂ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    (∫ c, p.complexMean (f c) ∂μ) = p.complexMean (fun x => ∫ c, f c x ∂μ) := by
  unfold complexMean
  rw [integral_finsetSum _ (fun x _ => (hf x).const_mul (p.weight x : ℂ))]
  simp only [integral_const_mul]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

noncomputable def pointWeights {Y : Type*} [Fintype Y] (y : Y) : FiniteProbabilityWeights Y where
  weight z := if z = y then 1 else 0
  nonneg z := by split_ifs <;> norm_num
  total := by
    rw [Finset.sum_eq_single y]
    · simp
    · intro z _ hz
      simp [hz]
    · simp

theorem pointWeights_complexMean {Y : Type*} [Fintype Y] (y : Y) (f : Y → ℂ) :
    (pointWeights y).complexMean f = f y := by
  unfold complexMean pointWeights
  dsimp only
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz]
  · simp

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] (law : FiniteProbabilityWeights I)
variable (P : I → Prop) (hP : ∀ i, P i ↔ 0 < law.weight i)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

variable {Ω R : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω) (F : Ω → R)

noncomputable def fiberTest (f : Ω → ℝ) (y : R) : ℝ :=
  p.fiberMean F y f / p.fiberMean F y (fun _ => 1)

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteProbabilityWeights Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

theorem uniform_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).mean f = 𝔼 x, f x := by
  simp only [mean, uniform, ← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

theorem uniform_complexMean {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℂ) :
    (uniform Ω).complexMean f = 𝔼 x, f x := by
  simp only [complexMean, uniform, Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def eventProbability {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E : Ω → Prop) : ℝ := by
  classical
  exact p.mean (fun x => if E x then 1 else 0)

theorem eventProbability_union_bound {Ω C : Type*} [Fintype Ω] [Fintype C]
    (p : FiniteProbabilityWeights Ω) (E : Ω → Prop) (F : C → Ω → Prop)
    (hEF : ∀ x, E x → ∃ c, F c x) :
    p.eventProbability E ≤ ∑ c, p.eventProbability (F c) := by
  classical
  have hpoint (x) : (if E x then (1 : ℝ) else 0) ≤ ∑ c, if F c x then (1 : ℝ) else 0 := by
    by_cases hE : E x
    · obtain ⟨c, hc⟩ := hEF x hE
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun c => if F c x then (1 : ℝ) else 0)
        (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ c)
      simpa only [hE, hc, ite_true] using h
    · simp only [hE, ite_false]
      exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  apply (p.mean_mono hpoint).trans_eq
  simp only [eventProbability, mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem mean_pi_product {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (v : ∀ j, Ω j → ℝ) :
    (pi p).mean (fun x => ∏ j, v j (x j)) = ∏ j, (p j).mean (v j) := by
  classical
  change (∑ x : ∀ j, Ω j, (∏ j, (p j).weight (x j)) * (∏ j, v j (x j))) =
    ∏ j, ∑ x, (p j).weight x * v j x
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j (x : Ω j) => (p j).weight x * v j x)).symm

theorem eventProbability_pi {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (E : ∀ j, Ω j → Prop) :
    (pi p).eventProbability (fun x => ∀ j, E j (x j)) = ∏ j, (p j).eventProbability (E j) := by
  classical
  have hpoint (x : ∀ j, Ω j) :
      (@ite ℝ (∀ j, E j (x j)) (Classical.propDecidable _) 1 0) =
        ∏ j, if E j (x j) then (1 : ℝ) else 0 := by
    by_cases h : ∀ j, E j (x j)
    · simp [h]
    · rw [if_neg h]
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm
  simpa only [eventProbability] using
    (congrArg (pi p).mean (funext hpoint)).trans
      (mean_pi_product p (fun j y => if E j y then (1 : ℝ) else 0))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem uniform_mass {Ω : Type*} [Fintype Ω] [Nonempty Ω] (G : Finset Ω) :
    (uniform Ω).mass G = (G.card : ℝ) / Fintype.card Ω := by
  simp [mass, uniform, div_eq_mul_inv]

theorem uniform_condition_mean {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (G : Finset Ω) (hG : 0 < (uniform Ω).mass G) (f : Ω → ℝ) :
    ((uniform Ω).condition G hG).mean f = 𝔼 x : G, f x := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hg : (G.card : ℝ) ≠ 0 := by
    intro hz
    rw [uniform_mass, hz, zero_div] at hG
    exact (lt_irrefl _ hG)
  rw [condition_mean, uniform_mean, uniform_mass, Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card, Finset.sum_coe_sort G f, Fintype.card_coe]
  have hsum : (∑ x, if x ∈ G then f x else 0) = ∑ x ∈ G, f x := by simp
  rw [hsum]
  field_simp

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem disjoint_cells_card_mul_le {Ω X : Type*} [Fintype Ω] [MeasurableSpace X]
    (μ : Measure X) (C : Ω → Set X) (A : Set X) (v : ℝ)
    (hdis : Pairwise (fun a b => Disjoint (C a) (C b))) (hm : ∀ ω, MeasurableSet (C ω))
    (hfin : ∀ ω, μ (C ω) ≠ ⊤) (hv : ∀ ω, μ.real (C ω) = v)
    (hsub : ∀ ω, C ω ⊆ A) (hA : μ A ≠ ⊤) :
    (Fintype.card Ω : ℝ) * v ≤ μ.real A := by
  have heq : μ.real (⋃ ω, C ω) = (Fintype.card Ω : ℝ) * v := by
    rw [measureReal_iUnion_fintype hdis hm hfin]
    simp only [hv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← heq]
  exact measureReal_mono (Set.iUnion_subset hsub) hA

theorem finite_cell_event_probability_le {Ω X : Type*} [Fintype Ω] [MeasurableSpace X]
    (p : FiniteProbabilityWeights Ω) (E : Ω → Prop)
    (μ : Measure X) (C : Ω → Set X) (A : Set X) (M v : ℝ) (hM : 0 ≤ M)
    (hdis : Pairwise (fun a b => Disjoint (C a) (C b))) (hm : ∀ ω, MeasurableSet (C ω))
    (hfin : ∀ ω, μ (C ω) ≠ ⊤) (hv : ∀ ω, μ.real (C ω) = v)
    (hw : ∀ ω, p.weight ω ≤ M * v) (hsub : ∀ ω, E ω → C ω ⊆ A) (hA : μ A ≠ ⊤) :
    p.eventProbability E ≤ M * μ.real A := by
  classical
  let S := Finset.univ.filter E
  have hc : (S.card : ℝ) * v ≤ μ.real A := by
    have h := disjoint_cells_card_mul_le μ (fun ω : S => C ω.val) A v
      (fun a b hab => hdis (Subtype.coe_injective.ne hab))
      (fun ω => hm ω) (fun ω => hfin ω) (fun ω => hv ω)
      (fun ω => hsub ω (Finset.mem_filter.mp ω.property).2) hA
    simpa only [Fintype.card_coe] using h
  calc
    p.eventProbability E = ∑ ω ∈ S, p.weight ω := by
      simp only [FiniteProbabilityWeights.eventProbability, FiniteProbabilityWeights.mean,
        S, Finset.sum_filter, mul_ite, mul_one, mul_zero]
    _ ≤ ∑ _ω ∈ S, M * v := Finset.sum_le_sum (fun ω _ => hw ω)
    _ = M * ((S.card : ℝ) * v) := by simp [mul_left_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hM

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem condition_mass {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G R : Finset Ω) (hG : 0 < p.mass G) :
    (p.condition G hG).mass R = p.mass (G ∩ R) / p.mass G := by
  simp only [mass, condition]
  rw [← Finset.sum_div, ← Finset.sum_filter]
  congr 1
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter, and_comm]

theorem mass_inter_le_condition_mass {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G R : Finset Ω) (hG : 0 < p.mass G) :
    p.mass (G ∩ R) ≤ (p.condition G hG).mass R := by
  rw [condition_mass]
  apply (le_div_iff₀ hG).mpr
  exact mul_le_of_le_one_right (p.mass_nonneg _) (p.mass_le_one G)

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.LargeCokernelProbability
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def sampledColumnMatrix {I J : Type*} {Ω : J → Type*}
    (column : ∀ j, Ω j → I → ℤ) (x : ∀ j, Ω j) : Matrix I J ℤ :=
  fun i j => column j (x j) i

def largeCokernelEvent {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    {Ω : J → Type*} (column : ∀ j, Ω j → I → ℤ) (B R : ℕ) (x : ∀ j, Ω j) : Prop :=
  ∃ A : Matrix I I ℤ, A.det ≠ 0 ∧
    A.mulVecLin.range ≤ (sampledColumnMatrix column x).mulVecLin.range ∧
    A.det.natAbs ≤ R ∧ B < integerCokernelExponent (sampledColumnMatrix column x).mulVecLin.range

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerColumnMinor
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integer_det_natAbs_le (A : Matrix ι ι ℤ) {H : ℕ}
    (hA : ∀ i j, (A i j).natAbs ≤ H) :
    A.det.natAbs ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι := by
  have h := Matrix.det_le (A := A) (abv := AbsoluteValue.abs) (x := (H : ℤ))
    (fun i j => show |A i j| ≤ (H : ℤ) from by
      simpa only [← Int.natCast_natAbs] using (show
        ((A i j).natAbs : ℤ) ≤ (H : ℤ) from by exact_mod_cast hA i j))
  change |A.det| ≤ (Fintype.card ι).factorial • (H : ℤ) ^ Fintype.card ι at h
  rw [← Int.natCast_natAbs, nsmul_eq_mul] at h
  exact_mod_cast h

theorem integer_cramer_natAbs_le (A : Matrix ι ι ℤ) (b : ι → ℤ) {H : ℕ}
    (hA : ∀ i j, (A i j).natAbs ≤ H) (hb : ∀ i, (b i).natAbs ≤ H) (i : ι) :
    (A.cramer b i).natAbs ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι := by
  rw [Matrix.cramer_apply]
  apply integer_det_natAbs_le
  intro j k
  rw [Matrix.updateCol_apply]
  split
  · exact hb j
  · exact hA j k

def rationalCramerSolution (A : Matrix ι ι ℚ) (b : ι → ℚ) : ι → ℚ :=
  A.det⁻¹ • A.cramer b

theorem rationalCramerSolution_solves (A : Matrix ι ι ℚ) (b : ι → ℚ)
    (hA : A.det ≠ 0) : A *ᵥ rationalCramerSolution A b = b := by
  rw [rationalCramerSolution, Matrix.mulVec_smul, Matrix.mulVec_cramer,
    smul_smul, inv_mul_cancel₀ hA, one_smul]

theorem rationalCramerSolution_unique (A : Matrix ι ι ℚ) (b x : ι → ℚ)
    (hA : A.det ≠ 0) (hx : A *ᵥ x = b) : x = rationalCramerSolution A b := by
  apply Matrix.mulVec_injective_of_isUnit (A.isUnit_iff_isUnit_det.mpr
    (isUnit_iff_ne_zero.mpr hA))
  exact hx.trans (rationalCramerSolution_solves A b hA).symm

theorem integerCramerSolution_apply (A : Matrix ι ι ℤ) (b : ι → ℤ) (i : ι) :
    rationalCramerSolution (A.map (Int.castRingHom ℚ)) (fun j => (b j : ℚ)) i =
      (A.cramer b i : ℚ) / (A.det : ℚ) := by
  have hdet : (A.map (Int.castRingHom ℚ)).det = (A.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det A).symm
  have hnum : (A.map (Int.castRingHom ℚ)).cramer (fun j => (b j : ℚ)) i =
      (A.cramer b i : ℚ) := by
    rw [Matrix.cramer_apply, Matrix.cramer_apply]
    have h := ((Int.castRingHom ℚ).map_det (A.updateCol i b)).symm
    change ((A.updateCol i b).map (Int.castRingHom ℚ)).det = _ at h
    rw [Matrix.map_updateCol] at h
    exact h
  simp only [rationalCramerSolution, Pi.smul_apply, smul_eq_mul, hdet, hnum,
    div_eq_mul_inv, mul_comm]

theorem integerCramerSolution_height (A : Matrix ι ι ℤ) (b : ι → ℤ)
    (hdet : A.det ≠ 0) {H : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ H)
    (hb : ∀ i, (b i).natAbs ≤ H) (i : ι) :
    RationalHeightLE
      (rationalCramerSolution (A.map (Int.castRingHom ℚ)) (fun j => (b j : ℚ)) i)
      ((Fintype.card ι).factorial * H ^ Fintype.card ι) := by
  rw [integerCramerSolution_apply]
  exact rationalHeightLE_fraction _ _ hdet (integer_cramer_natAbs_le A b hA hb i)
    (integer_det_natAbs_le A hA)

theorem exists_bounded_integer_system_solution (A : Matrix ι ι ℤ) (b : ι → ℤ)
    (hdet : A.det ≠ 0) {H : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ H)
    (hb : ∀ i, (b i).natAbs ≤ H) :
    ∃ x : ι → ℚ, (A.map (Int.castRingHom ℚ)) *ᵥ x = (fun i => (b i : ℚ)) ∧
      ∀ i, RationalHeightLE (x i)
        ((Fintype.card ι).factorial * H ^ Fintype.card ι) := by
  refine ⟨rationalCramerSolution _ _, rationalCramerSolution_solves _ _ ?_,
    integerCramerSolution_height A b hdet hA hb⟩
  have h : (A.map (Int.castRingHom ℚ)).det = (A.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det A).symm
  rw [h]
  exact_mod_cast hdet

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalRowReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def rationalSolveHeight (r H : ℕ) : ℕ :=
  r.factorial * (H ^ (r * r + r)) ^ r

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_bounded_rational_system_solution (A : Matrix ι ι ℚ) (b : ι → ℚ)
    (hdet : A.det ≠ 0) {H : ℕ} (hA : ∀ i j, RationalHeightLE (A i j) H)
    (hb : ∀ i, RationalHeightLE (b i) H) :
    ∃ x : ι → ℚ, A *ᵥ x = b ∧
      ∀ i, RationalHeightLE (x i) (rationalSolveHeight (Fintype.card ι) H) := by
  let q : (ι × ι) ⊕ ι → ℚ := Sum.elim (fun p => A p.1 p.2) b
  have hq : ∀ u, RationalHeightLE (q u) H := by
    intro u
    cases u with
    | inl p => exact hA p.1 p.2
    | inr i => exact hb i
  obtain ⟨D, hDpos, _, a, ha, hbound⟩ := exists_bounded_integer_array q hq
  let Z : Matrix ι ι ℤ := fun i j => a (.inl (i, j))
  let c : ι → ℤ := fun i => a (.inr i)
  have hD : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hZ : Z.map (Int.castRingHom ℚ) = (D : ℚ) • A := by
    ext i j
    exact ha (.inl (i, j))
  have hc : (fun i => (c i : ℚ)) = (D : ℚ) • b := by
    funext i
    exact ha (.inr i)
  have hZdet : Z.det ≠ 0 := by
    have hcast : (Z.det : ℚ) = (D : ℚ) ^ Fintype.card ι * A.det := by
      calc
        (Z.det : ℚ) = (Z.map (Int.castRingHom ℚ)).det :=
          (Int.castRingHom ℚ).map_det Z
        _ = _ := by rw [hZ, Matrix.det_smul]
    have hn := mul_ne_zero (pow_ne_zero (Fintype.card ι) hD) hdet
    rw [← hcast] at hn
    exact_mod_cast hn
  have hZA : ∀ i j, (Z i j).natAbs ≤ H ^ (Fintype.card ι * Fintype.card ι +
      Fintype.card ι) := by
    intro i j
    simpa only [Fintype.card_sum, Fintype.card_prod] using hbound (.inl (i, j))
  have hcA : ∀ i, (c i).natAbs ≤ H ^ (Fintype.card ι * Fintype.card ι +
      Fintype.card ι) := by
    intro i
    simpa only [Fintype.card_sum, Fintype.card_prod] using hbound (.inr i)
  obtain ⟨x, hx, hxH⟩ := exists_bounded_integer_system_solution Z c hZdet hZA hcA
  refine ⟨x, ?_, hxH⟩
  rw [hZ, hc, Matrix.smul_mulVec] at hx
  funext i
  have hi := congrFun hx i
  change (D : ℚ) * (A *ᵥ x) i = (D : ℚ) * b i at hi
  exact mul_left_cancel₀ hD hi

theorem rationalCramerSolution_height (A : Matrix ι ι ℚ) (b : ι → ℚ)
    (hdet : A.det ≠ 0) {H : ℕ} (hA : ∀ i j, RationalHeightLE (A i j) H)
    (hb : ∀ i, RationalHeightLE (b i) H) (i : ι) :
    RationalHeightLE (rationalCramerSolution A b i)
      (rationalSolveHeight (Fintype.card ι) H) := by
  obtain ⟨x, hx, hheight⟩ := exists_bounded_rational_system_solution A b hdet hA hb
  rw [← rationalCramerSolution_unique A b x hdet hx]
  exact hheight i

theorem rationalHeightLE_zero {H : ℕ} (hH : 1 ≤ H) : RationalHeightLE 0 H := by
  exact ⟨by simp, by simpa using hH⟩

theorem rationalHeightLE_one {H : ℕ} (hH : 1 ≤ H) : RationalHeightLE 1 H := by
  exact ⟨by simpa using hH, by simpa using hH⟩

theorem exists_bounded_rational_right_inverse (A : Matrix ι ι ℚ) (hdet : A.det ≠ 0)
    {H : ℕ} (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ B : Matrix ι ι ℚ, A * B = 1 ∧
      ∀ i j, RationalHeightLE (B i j) (rationalSolveHeight (Fintype.card ι) H) := by
  let B : Matrix ι ι ℚ := fun i j => rationalCramerSolution A (Pi.single j 1) i
  refine ⟨B, ?_, ?_⟩
  · ext i j
    have h := congrFun (rationalCramerSolution_solves A (Pi.single j 1) hdet) i
    change (A *ᵥ rationalCramerSolution A (Pi.single j 1)) i = (1 : Matrix ι ι ℚ) i j
    simpa only [Pi.single_apply, Matrix.one_apply, eq_comm] using h
  · intro i j
    apply rationalCramerSolution_height A (Pi.single j 1) hdet hA
    intro k
    by_cases hkj : k = j
    · simpa [Pi.single_apply, hkj] using rationalHeightLE_one hH
    · simpa [Pi.single_apply, hkj, Ne.symm hkj] using rationalHeightLE_zero hH

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem RationalHeightLE.neg {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) :
    RationalHeightLE (-q) H := by
  simpa only [RationalHeightLE, Rat.neg_num, Rat.neg_den, Int.natAbs_neg] using hq

theorem RationalHeightLE.mul {q r : ℚ} {H K : ℕ}
    (hq : RationalHeightLE q H) (hr : RationalHeightLE r K) :
    RationalHeightLE (q * r) (H * K) := by
  have hd : (q.den : ℤ) * r.den ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast q.den_ne_zero) (by exact_mod_cast r.den_ne_zero)
  have heq : q * r = ((q.num * r.num : ℤ) : ℚ) / ((q.den : ℤ) * r.den : ℤ) := by
    push_cast
    rw [mul_div_mul_comm, Rat.num_div_den, Rat.num_div_den]
  rw [heq]
  apply rationalHeightLE_fraction _ _ hd
  · simpa only [Int.natAbs_mul] using Nat.mul_le_mul hq.1 hr.1
  · simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul hq.2 hr.2

theorem RationalHeightLE.add {q r : ℚ} {H K : ℕ}
    (hq : RationalHeightLE q H) (hr : RationalHeightLE r K) :
    RationalHeightLE (q + r) (2 * H * K) := by
  have hqd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hrd : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hd : (q.den : ℤ) * r.den ≠ 0 := by
    exact_mod_cast mul_ne_zero hqd hrd
  have heq : q + r = ((q.num * r.den + (q.den : ℤ) * r.num : ℤ) : ℚ) /
      ((q.den : ℤ) * r.den : ℤ) := by
    calc
      q + r = (q.num : ℚ) / q.den + (r.num : ℚ) / r.den :=
        congrArg₂ (· + ·) q.num_div_den.symm r.num_div_den.symm
      _ = _ := by push_cast; exact div_add_div _ _ hqd hrd
  rw [heq]
  apply rationalHeightLE_fraction _ _ hd
  · calc
      _ ≤ (q.num * r.den).natAbs + ((q.den : ℤ) * r.num).natAbs :=
        Int.natAbs_add_le _ _
      _ ≤ H * K + H * K := by
        simp only [Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2) (Nat.mul_le_mul hq.2 hr.1)
      _ = _ := by ring
  · calc
      _ = q.den * r.den := by simp only [Int.natAbs_mul, Int.natAbs_natCast]
      _ ≤ H * K := Nat.mul_le_mul hq.2 hr.2
      _ ≤ 2 * H * K := by
        simpa only [mul_assoc] using Nat.le_mul_of_pos_left (H * K) (by decide : 0 < 2)

theorem RationalHeightLE.sub {q r : ℚ} {H K : ℕ}
    (hq : RationalHeightLE q H) (hr : RationalHeightLE r K) :
    RationalHeightLE (q - r) (2 * H * K) := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg

theorem rationalHeightLE_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℚ) {H : ℕ} (hq : ∀ i, RationalHeightLE (q i) H) :
    RationalHeightLE (∑ i, q i) ((Fintype.card ι + 1) * H ^ Fintype.card ι) := by
  obtain ⟨D, hDpos, hD, a, ha, hbound⟩ := exists_bounded_integer_array q hq
  have hsum : ((∑ i, a i : ℤ) : ℚ) = (D : ℚ) * ∑ i, q i := by
    push_cast
    simp_rw [ha]
    rw [Finset.mul_sum]
  have heq : (∑ i, q i) = ((∑ i, a i : ℤ) : ℚ) / (D : ℤ) := by
    apply (eq_div_iff (by exact_mod_cast hDpos.ne')).mpr
    simpa only [Int.cast_natCast, mul_comm] using hsum.symm
  rw [heq]
  apply rationalHeightLE_fraction _ _ (by exact_mod_cast hDpos.ne')
  · calc
      _ ≤ ∑ i, (a i).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _ : ι, H ^ Fintype.card ι := Finset.sum_le_sum fun i _ => hbound i
      _ = Fintype.card ι * H ^ Fintype.card ι := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ _)
  · simp only [Int.natAbs_natCast]
    exact hD.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))

theorem rationalHeightLE_matrix_mul {ι κ ν : Type*}
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℚ) (B : Matrix κ ν ℚ)
    {H K : ℕ} (hA : ∀ i j, RationalHeightLE (A i j) H)
    (hB : ∀ i j, RationalHeightLE (B i j) K) (i : ι) (j : ν) :
    RationalHeightLE ((A * B) i j) ((Fintype.card κ + 1) * (H * K) ^ Fintype.card κ) :=
  rationalHeightLE_sum (fun k => A i k * B k j) (fun k => (hA i k).mul (hB k j))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in

theorem exists_nonsingular_columns (A : Matrix ι κ ℚ)
    (hA : Function.Surjective A.mulVec) :
    ∃ c : ι → κ, Function.Injective c ∧ (A.submatrix id c).det ≠ 0 := by
  classical
  have hspan : Submodule.span ℚ (Set.range A.col) = ⊤ := by
    rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]
    exact hA
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range A.col)
  rw [hspan, finrank_top, Module.finrank_pi] at hex
  obtain ⟨v, hv, _, hli⟩ := hex
  choose f hf using hv
  let e := Fintype.equivFin ι
  let c : ι → κ := fun i => f (e i)
  have hcol : (A.submatrix id c).col = fun i => v (e i) := by
    funext i
    exact hf (e i)
  have hcols : LinearIndependent ℚ (A.submatrix id c).col := by
    rw [hcol]
    exact hli.comp e e.injective
  refine ⟨c, ?_, ?_⟩
  · intro i j hij
    apply hcols.injective
    change A.col (c i) = A.col (c j)
    rw [hij]
  · exact (isUnit_iff_ne_zero.mp
      ((A.submatrix id c).isUnit_iff_isUnit_det.mp
        (Matrix.linearIndependent_cols_iff_isUnit.mp hcols)))

def extendRows (c : ι → κ) (B : Matrix ι ι ℚ) : Matrix κ ι ℚ :=
  fun k j => ∑ i, if c i = k then B i j else 0

omit [Fintype κ] in
theorem extendRows_apply (c : ι → κ) (hc : Function.Injective c)
    (B : Matrix ι ι ℚ) (i j : ι) : extendRows c B (c i) j = B i j := by
  simp only [extendRows, hc.eq_iff]
  simp

omit [DecidableEq ι] [Fintype κ] in
theorem extendRows_apply_of_not_mem (c : ι → κ) (B : Matrix ι ι ℚ)
    (k : κ) (hk : k ∉ Set.range c) (j : ι) : extendRows c B k j = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (fun h => hk ⟨i, h⟩)

omit [DecidableEq ι] in
theorem mul_extendRows (A : Matrix ι κ ℚ) (c : ι → κ) (B : Matrix ι ι ℚ) :
    A * extendRows c B = A.submatrix id c * B := by
  ext r j
  change (∑ k, A r k * ∑ i, if c i = k then B i j else 0) =
    ∑ i, A r (c i) * B i j
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_ite, mul_zero]
  simp

theorem rationalSolveHeight_pos (r : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    0 < rationalSolveHeight r H := by
  have hHpos : 0 < H := Nat.zero_lt_one.trans_le hH
  unfold rationalSolveHeight
  positivity

theorem exists_bounded_rational_section (A : Matrix ι κ ℚ)
    (hsurj : Function.Surjective A.mulVec) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ S : Matrix κ ι ℚ, A * S = 1 ∧
      ∀ i j, RationalHeightLE (S i j) (rationalSolveHeight (Fintype.card ι) H) := by
  obtain ⟨c, hc, hdet⟩ := exists_nonsingular_columns A hsurj
  obtain ⟨B, hB, hBH⟩ := exists_bounded_rational_right_inverse (A.submatrix id c) hdet
    hH (fun i j => hA i (c j))
  refine ⟨extendRows c B, ?_, ?_⟩
  · rw [mul_extendRows, hB]
  · intro k j
    by_cases hk : k ∈ Set.range c
    · obtain ⟨i, rfl⟩ := hk
      rw [extendRows_apply c hc]
      exact hBH i j
    · rw [extendRows_apply_of_not_mem c B k hk]
      exact rationalHeightLE_zero (rationalSolveHeight_pos _ hH)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem rational_sum_cost_le_exp (m H : ℕ) {p : ℝ} (hp : 0 ≤ p) (a c : ℕ)
    (hH : (H : ℝ) ≤ Real.exp ((p + 2) ^ a)) (hm : (m : ℝ) ≤ (p + 2) ^ c) :
    (((m + 1) * H ^ m : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (a + c + 1)) := by
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg H) hH m
  rw [← Real.exp_nat_mul] at hpower
  have hone : 1 + (p + 2) ^ a ≤ (p + 2) ^ (a + 1) := by
    have ha : (1 : ℝ) ≤ (p + 2) ^ a := one_le_pow₀ (by linarith)
    calc
      _ ≤ 2 * (p + 2) ^ a := by linarith
      _ ≤ (p + 2) * (p + 2) ^ a :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  push_cast
  calc
    _ ≤ Real.exp m * Real.exp ((m : ℝ) * (p + 2) ^ a) :=
      mul_le_mul (Real.add_one_le_exp m) hpower (by positivity) (by positivity)
    _ = Real.exp ((m : ℝ) * (1 + (p + 2) ^ a)) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((p + 2) ^ c * (p + 2) ^ (a + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul hm hone (by positivity) (by positivity))
    _ = _ := by rw [← pow_add]; congr 2; omega

theorem rational_sum_exp_height {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℚ) {H : ℕ} (hq : ∀ i, RationalHeightLE (q i) H)
    {p : ℝ} (hp : 0 ≤ p) (a c : ℕ)
    (hH : (H : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hcard : (Fintype.card ι : ℝ) ≤ (p + 2) ^ c) :
    ((∑ i, q i).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ (a + c + 1)) ∧
      ((∑ i, q i).den : ℝ) ≤ Real.exp ((p + 2) ^ (a + c + 1)) := by
  have hheight := rationalHeightLE_sum q hq
  have hcost := rational_sum_cost_le_exp (Fintype.card ι) H hp a c hH hcard
  constructor
  · exact (show ((∑ i, q i).num.natAbs : ℝ) ≤ ((Fintype.card ι + 1) * H ^ Fintype.card ι : ℕ) from
      by exact_mod_cast hheight.1).trans hcost
  · exact (show ((∑ i, q i).den : ℝ) ≤ ((Fintype.card ι + 1) * H ^ Fintype.card ι : ℕ) from
      by exact_mod_cast hheight.2).trans hcost

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in

theorem mulVec_eq_zero_iff_row_span (A : Matrix ι κ ℚ) (x : κ → ℚ) :
    A *ᵥ x = 0 ↔ ∀ v ∈ Submodule.span ℚ (Set.range A.row), v ⬝ᵥ x = 0 := by
  constructor
  · intro hx v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact congrFun hx i
    | zero => exact zero_dotProduct x
    | add y z _ _ hy hz => rw [add_dotProduct, hy, hz, add_zero]
    | smul a y _ hy => rw [smul_dotProduct, hy, smul_zero]
  · intro hx
    funext i
    exact hx (A.row i) (Submodule.subset_span ⟨i, rfl⟩)

theorem mulVec_surjective_of_independent_rows (A : Matrix ι κ ℚ)
    (hA : LinearIndependent ℚ A.row) : Function.Surjective A.mulVec := by
  change Function.Surjective A.mulVecLin
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  change A.rank = Module.finrank ℚ (ι → ℚ)
  rw [hA.rank_matrix, Module.finrank_pi]

theorem exists_independent_defining_rows (A : Matrix ι κ ℚ) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ rows : Fin r → ι,
      Function.Injective rows ∧ Function.Surjective (A.submatrix rows id).mulVec ∧
      LinearMap.ker (A.submatrix rows id).mulVecLin = LinearMap.ker A.mulVecLin := by
  classical
  let r := Module.finrank ℚ (Submodule.span ℚ (Set.range A.row))
  obtain ⟨v, hv, hspan, hli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range A.row)
  choose rows hrows using hv
  have hrow : (A.submatrix rows id).row = v := by
    funext i
    exact hrows i
  have hind : LinearIndependent ℚ (A.submatrix rows id).row := by
    rw [hrow]
    exact hli
  refine ⟨r, ?_, rows, ?_, mulVec_surjective_of_independent_rows _ hind, ?_⟩
  · change Module.finrank ℚ (Submodule.span ℚ (Set.range A.row)) ≤ Fintype.card ι
    rw [← A.rank_eq_finrank_span_row]
    exact A.rank_le_card_height
  · intro i j hij
    apply hind.injective
    change A.row (rows i) = A.row (rows j)
    rw [hij]
  · ext x
    change (A.submatrix rows id) *ᵥ x = 0 ↔ A *ᵥ x = 0
    rw [mulVec_eq_zero_iff_row_span, mulVec_eq_zero_iff_row_span, hrow, hspan]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RationalHeightBudget
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem factorial_le_exp_sq (r : ℕ) :
    (r.factorial : ℝ) ≤ Real.exp ((r : ℝ) ^ 2) := by
  calc
    (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
    _ ≤ (Real.exp r) ^ r := pow_le_pow_left₀ (Nat.cast_nonneg _)
      ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp r)) r
    _ = Real.exp ((r : ℝ) ^ 2) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem rationalSolveHeight_le_exp (r H : ℕ) {p : ℝ} (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalSolveHeight r H : ℝ) ≤
      Real.exp ((r : ℝ) ^ 2 + p * ((r : ℝ) ^ 3 + (r : ℝ) ^ 2)) := by
  have hpower : (((H : ℝ) ^ (r * r + r)) ^ r) ≤
      Real.exp (p * ((r : ℝ) ^ 3 + (r : ℝ) ^ 2)) := by
    calc
      _ ≤ ((Real.exp p) ^ (r * r + r)) ^ r := by gcongr
      _ = _ := by rw [← pow_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  unfold rationalSolveHeight
  push_cast
  calc
    _ ≤ Real.exp ((r : ℝ) ^ 2) *
        Real.exp (p * ((r : ℝ) ^ 3 + (r : ℝ) ^ 2)) :=
      mul_le_mul (factorial_le_exp_sq r) hpower (by positivity) (by positivity)
    _ = _ := (Real.exp_add _ _).symm

theorem rationalSolveHeight_le_budget (r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalSolveHeight r H : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  apply (rationalSolveHeight_le_exp r H hH).trans
  apply Real.exp_le_exp.mpr
  calc
    (r : ℝ) ^ 2 + p * ((r : ℝ) ^ 3 + (r : ℝ) ^ 2) ≤
        p ^ 2 + p * (p ^ 3 + p ^ 2) := by gcongr
    _ ≤ (p + 2) ^ 5 := by
      have h : 0 ≤ p ^ 5 + 9 * p ^ 4 + 39 * p ^ 3 + 79 * p ^ 2 + 80 * p + 32 := by
        positivity
      nlinarith

theorem exists_rational_section_exp_height {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℚ) (hsurj : Function.Surjective A.mulVec)
    {H : ℕ} (hHpos : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ S : Matrix κ ι ℚ, A * S = 1 ∧ ∀ i j,
      ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 5) ∧
      ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section A hsurj hHpos hA
  refine ⟨S, hS, fun i j => ?_⟩
  have hbudget := rationalSolveHeight_le_budget (Fintype.card ι) H hp hdim hH
  constructor
  · exact (show ((S i j).num.natAbs : ℝ) ≤ rationalSolveHeight (Fintype.card ι) H from
      by exact_mod_cast (hSH i j).1).trans hbudget
  · exact (show ((S i j).den : ℝ) ≤ rationalSolveHeight (Fintype.card ι) H from
      by exact_mod_cast (hSH i j).2).trans hbudget

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LinearMapCoordinateHeight
namespace OAI

section

namespace Erdos3

open Module

variable {V W ι κ : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [Fintype ι]

theorem linearMap_coordinate_height (e : Basis ι ℚ V) (f : Basis κ ℚ W)
    (T : V →ₗ[ℚ] W) {H K : ℕ}
    (hT : ∀ i j, RationalHeightLE (f.repr (T (e i)) j) H)
    (x : V) (hx : ∀ i, RationalHeightLE (e.repr x i) K) (j : κ) :
    RationalHeightLE (f.repr (T x) j) ((Fintype.card ι + 1) * (K * H) ^ Fintype.card ι) := by
  classical
  have he : f.repr (T x) j = ∑ i, e.repr x i * f.repr (T (e i)) j := by
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [he]
  exact rationalHeightLE_sum _ (fun i => (hx i).mul (hT i j))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open MvPolynomial

def earlierSlot {d : ℕ} (i : Fin d) (j : Fin i.val) : Fin d :=
  ⟨j.val, lt_trans j.isLt i.isLt⟩

def patchVariableWeight {σ : Type*} {d : ℕ} (w : Fin d → ℕ) (i : Fin d) :
    σ ⊕ Fin i.val → ℕ := Sum.elim (fun _ => 1) (fun j => w (earlierSlot i j))

structure PolynomialSlots (σ : Type*) (d : ℕ) (w : Fin d → ℕ) where
  center : (i : Fin d) → MvPolynomial (σ ⊕ Fin i.val) ℝ
  degree : ∀ i, center i ∈ weightedSupportLE (patchVariableWeight w i) (w i)

namespace PolynomialSlots

variable {σ : Type*} {d D E : ℕ} {w : Fin d → ℕ}

noncomputable def slots (A : PolynomialSlots σ d w) (t : σ → ℝ) : TriangularSlots d where
  center x i := aeval (Sum.elim t (fun j => x (earlierSlot i j))) (A.center i)
  lower i x y hxy := by
    apply congrArg (fun f : σ ⊕ Fin i.val → ℝ => aeval f (A.center i))
    funext v
    cases v with
    | inl a => rfl
    | inr j => exact hxy (earlierSlot i j) (by simpa only [Fin.lt_def, earlierSlot] using j.isLt)

noncomputable def prefixSubstitution (I : Fin D → MvPolynomial σ ℝ) (i : Fin E) :
    σ ⊕ Fin (D + i.val) → MvPolynomial (σ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => X (Sum.inl a))
    (Fin.addCases (fun j => aeval (fun a => X (Sum.inl a)) (I j))
      (fun j => X (Sum.inr j)))

theorem prefixSubstitution_degree {w : Fin (D + E) → ℕ}
    (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (w (j.castAdd E)))
    (i : Fin E) (v : σ ⊕ Fin (D + i.val)) :
    prefixSubstitution I i v ∈
      weightedSupportLE (patchVariableWeight (fun j => w (j.natAdd D)) i)
        (patchVariableWeight w (i.natAdd D) v) := by
  cases v with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [prefixSubstitution, Sum.elim_inr, Fin.addCases_left]
      apply weightedSupportLE_aeval (fun _ : σ => 1)
        (patchVariableWeight (fun j => w (j.natAdd D)) i)
        (fun a => (X (Sum.inl a) : MvPolynomial (σ ⊕ Fin i.val) ℝ))
      · intro a
        exact weightedSupportLE_X _ (Sum.inl a)
      · exact hI k
    · simp only [prefixSubstitution, Sum.elim_inr, Fin.addCases_right]
      exact weightedSupportLE_X (R := ℝ)
        (patchVariableWeight (fun j => w (j.natAdd D)) i) (Sum.inr k)

noncomputable def freezePrefix {w : Fin (D + E) → ℕ}
    (A : PolynomialSlots σ (D + E) w) (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (w (j.castAdd E))) :
    PolynomialSlots σ E (fun j => w (j.natAdd D)) where
  center i := aeval (prefixSubstitution I i) (A.center (i.natAdd D))
  degree i := weightedSupportLE_aeval _ _ _ (prefixSubstitution_degree I hI i)
    (A.degree (i.natAdd D))

end PolynomialSlots

structure PolynomialPatch (σ : Type*) (s d : ℕ) where
  weight : Fin d → ℕ
  weight_pos : ∀ i, 1 ≤ weight i
  weight_le : ∀ i, weight i ≤ s
  weight_mono : Monotone weight
  form : PolynomialSlots σ d weight
  kernel : PatchKernel d

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

noncomputable def value (A : PolynomialPatch σ s d) (t : σ → ℝ) : ℝ :=
  (A.form.slots t).patchValue A.kernel

noncomputable def freezePrefix (A : PolynomialPatch σ s (D + E))
    (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)))
    (z : Fin D → ℝ) : PolynomialPatch σ s E where
  weight i := A.weight (i.natAdd D)
  weight_pos i := A.weight_pos _
  weight_le i := A.weight_le _
  weight_mono i j hij := A.weight_mono (by simpa only [Fin.le_def, Fin.val_natAdd,
    Nat.add_le_add_iff_left] using hij)
  form := A.form.freezePrefix I hI
  kernel := A.kernel.freeze z

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def ofCoordinates (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i)) : PolynomialSlots σ d w where
  center i := aeval (fun a => X (Sum.inl a)) (P i)
  degree i := weightedSupportLE_aeval (fun _ : σ => 1) (patchVariableWeight w i)
    (fun a => X (Sum.inl a)) (fun a => weightedSupportLE_X _ (Sum.inl a)) (hP i)

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

noncomputable def ofCoordinates (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hws : ∀ i, w i ≤ s) (hmono : Monotone w) (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i)) (Φ : PatchKernel d) :
    PolynomialPatch σ s d where
  weight := w
  weight_pos := hw
  weight_le := hws
  weight_mono := hmono
  form := PolynomialSlots.ofCoordinates P hP
  kernel := Φ

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

end PolynomialPatch

noncomputable def shiftedParameterPolynomials {σ : Type*} {D : ℕ}
    (I : Fin D → MvPolynomial σ ℝ) (t₀ : σ → ℝ) (b₀ : Fin D → ℤ) :
    Fin D → MvPolynomial σ ℝ := fun i => C (b₀ i : ℝ) + I i - C (aeval t₀ (I i))

namespace PolynomialPatch

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def parameterSubstitution (f : σ → MvPolynomial τ ℝ) (i : Fin d) :
    σ ⊕ Fin i.val → MvPolynomial (τ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => aeval (fun b => X (Sum.inl b)) (f a)) (fun j => X (Sum.inr j))

theorem parameterSubstitution_degree (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (i : Fin d)
    (v : σ ⊕ Fin i.val) :
    parameterSubstitution f i v ∈
      weightedSupportLE (patchVariableWeight (σ := τ) w i)
        (patchVariableWeight (σ := σ) w i v) := by
  cases v with
  | inl a =>
    apply weightedSupportLE_aeval (fun _ : τ => 1) (patchVariableWeight w i)
    · intro b
      exact weightedSupportLE_X _ (Sum.inl b)
    · exact hf a
  | inr j => exact weightedSupportLE_X _ (Sum.inr j)

noncomputable def reparam (A : PolynomialSlots σ d w) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) : PolynomialSlots τ d w where
  center i := aeval (parameterSubstitution f i) (A.center i)
  degree i := weightedSupportLE_aeval _ _ _ (parameterSubstitution_degree f hf i) (A.degree i)

theorem reparam_slots (A : PolynomialSlots σ d w) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (t : τ → ℝ) :
    (A.reparam f hf).slots t = A.slots (fun a => aeval t (f a)) := by
  apply TriangularSlots.ext
  intro x i
  simp only [slots, reparam, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun g : σ ⊕ Fin i.val → ℝ => aeval g (A.center i))
  funext v
  cases v with
  | inl a =>
    simp only [parameterSubstitution, Sum.elim_inl, MvPolynomial.comp_aeval_apply, aeval_X]
  | inr j => simp [parameterSubstitution]

end PolynomialSlots

namespace PolynomialPatch

variable {σ τ : Type*} {s d : ℕ}

noncomputable def reparam (A : PolynomialPatch σ s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) : PolynomialPatch τ s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := A.form.reparam f hf
  kernel := A.kernel

theorem reparam_value (A : PolynomialPatch σ s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (t : τ → ℝ) :
    (A.reparam f hf).value t = A.value (fun a => aeval t (f a)) := by
  change ((A.form.reparam f hf).slots t).patchValue A.kernel = _
  rw [PolynomialSlots.reparam_slots]
  rfl

noncomputable def affineLineParameters (a q : σ → ℝ) : σ → MvPolynomial Unit ℝ :=
  fun i => C (a i) + q i • X ()

theorem affineLineParameters_degree (a q : σ → ℝ) (i : σ) :
    affineLineParameters a q i ∈ weightedSupportLE (fun _ : Unit => 1) 1 :=
  (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    ((weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ ()))

noncomputable def onAffineLine (A : PolynomialPatch σ s d) (a q : σ → ℝ) :
    PolynomialPatch Unit s d := A.reparam (affineLineParameters a q) (affineLineParameters_degree a q)

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open MvPolynomial

variable {X : Type*} {s d : ℕ}

noncomputable def shiftedKernel (A : PolynomialPatch X s d)
    (v : Fin d → ℝ) (Φ : PatchKernel d) : PolynomialPatch X s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := {
    center := fun i => A.form.center i + C (v i)
    degree := fun i => (weightedSupportLE _ _).add_mem (A.form.degree i)
      (weightedSupportLE_C _ _ _) }
  kernel := Φ

theorem shiftedKernel_residual (A : PolynomialPatch X s d)
    (v : Fin d → ℝ) (Φ : PatchKernel d) (t : X → ℝ) (b : Fin d → ℤ) :
    ((A.shiftedKernel v Φ).form.slots t).residual b = (A.form.slots t).residual b - v := by
  funext i
  simp only [shiftedKernel, TriangularSlots.residual, PolynomialSlots.slots,
    map_add, aeval_C, Pi.sub_apply, Algebra.algebraMap_self, RingHom.id_apply]
  ring

theorem shiftedKernel_value (A : PolynomialPatch X s d)
    (v : Fin d → ℝ) (Φ : PatchKernel d) (t : X → ℝ) :
    (A.shiftedKernel v Φ).value t =
      ∑' b, Φ.value ((A.form.slots t).residual b - v) := by
  simp only [value, TriangularSlots.patchValue, shiftedKernel_residual]
  rfl

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d n D E : ℕ}

noncomputable def placementSubstitution (f : Fin d → Fin n) (k : Fin n) (i : Fin d) :
    σ ⊕ Fin i.val → MvPolynomial (σ ⊕ Fin k.val) ℝ :=
  Sum.elim (fun a => X (Sum.inl a)) (fun j =>
    if h : (f (earlierSlot i j)).val < k.val then X (Sum.inr ⟨_, h⟩) else 0)

theorem placementSubstitution_degree {w : Fin d → ℕ} {v : Fin n → ℕ}
    (f : Fin d → Fin n) (hweight : ∀ i, v (f i) = w i) (k : Fin n) (i : Fin d)
    (a : σ ⊕ Fin i.val) :
    placementSubstitution f k i a ∈
      weightedSupportLE (patchVariableWeight v k) (patchVariableWeight w i a) := by
  cases a with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
    simp only [placementSubstitution, Sum.elim_inr]
    split_ifs with h
    · have hX := weightedSupportLE_X (R := ℝ) (patchVariableWeight (σ := σ) v k)
        (Sum.inr (⟨(f (earlierSlot i j)).val, h⟩ : Fin k.val))
      change _ ∈ weightedSupportLE _ (v (f (earlierSlot i j))) at hX
      rw [hweight] at hX
      exact hX
    · exact (weightedSupportLE _ _).zero_mem

noncomputable def placeCenter {w : Fin d → ℕ} (A : PolynomialSlots σ d w)
    (f : Fin d → Fin n) (k : Fin n) (i : Fin d) :
    MvPolynomial (σ ⊕ Fin k.val) ℝ := aeval (placementSubstitution f k i) (A.center i)

theorem placeCenter_degree {w : Fin d → ℕ} {v : Fin n → ℕ}
    (A : PolynomialSlots σ d w) (f : Fin d → Fin n)
    (hweight : ∀ i, v (f i) = w i) (k : Fin n) (i : Fin d) :
    A.placeCenter f k i ∈ weightedSupportLE (patchVariableWeight v k) (w i) :=
  weightedSupportLE_aeval _ _ _ (placementSubstitution_degree f hweight k i) (A.degree i)

theorem placeCenter_eval {w : Fin d → ℕ} (A : PolynomialSlots σ d w)
    (f : Fin d → Fin n) (hf : StrictMono f) (i : Fin d) (t : σ → ℝ) (x : Fin n → ℝ) :
    aeval (Sum.elim t (fun j => x (earlierSlot (f i) j))) (A.placeCenter f (f i) i) =
      (A.slots t).center (fun j => x (f j)) i := by
  simp only [placeCenter, MvPolynomial.comp_aeval_apply, slots]
  apply congrArg (fun g : σ ⊕ Fin i.val → ℝ => aeval g (A.center i))
  funext a
  cases a with
  | inl a => simp [placementSubstitution]
  | inr j =>
    have h : (f (earlierSlot i j)).val < (f i).val :=
      hf (show earlierSlot i j < i from j.isLt)
    simp only [placementSubstitution, Sum.elim_inr, dif_pos h, aeval_X]
    rfl

noncomputable def interleave {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : PolynomialSlots σ D w) (B : PolynomialSlots σ E v) (I : SlotInterleaving D E) :
    PolynomialSlots σ (D + E) (I.fill w v) where
  center k := Fin.addCases (A.placeCenter I.left k) (B.placeCenter I.right k) (I.perm k)
  degree k := by
    change Fin.addCases (A.placeCenter I.left k) (B.placeCenter I.right k) (I.perm k) ∈
      weightedSupportLE (patchVariableWeight (I.fill w v) k) (Fin.append w v (I.perm k))
    generalize I.perm k = z
    refine Fin.addCases (fun i => ?_) (fun i => ?_) z
    · simpa only [Fin.addCases_left, Fin.append_left] using
        A.placeCenter_degree I.left (fun j => I.fill_left w v j) k i
    · simpa only [Fin.addCases_right, Fin.append_right] using
        B.placeCenter_degree I.right (fun j => I.fill_right w v j) k i

@[simp] theorem interleave_center_left {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : PolynomialSlots σ D w) (B : PolynomialSlots σ E v) (I : SlotInterleaving D E)
    (i : Fin D) : (A.interleave B I).center (I.left i) = A.placeCenter I.left (I.left i) i := by
  simp [interleave, SlotInterleaving.left]

@[simp] theorem interleave_center_right {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : PolynomialSlots σ D w) (B : PolynomialSlots σ E v) (I : SlotInterleaving D E)
    (i : Fin E) : (A.interleave B I).center (I.right i) = B.placeCenter I.right (I.right i) i := by
  simp [interleave, SlotInterleaving.right]

theorem interleave_slots {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : PolynomialSlots σ D w) (B : PolynomialSlots σ E v) (I : SlotInterleaving D E)
    (t : σ → ℝ) : (A.interleave B I).slots t = (A.slots t).interleave (B.slots t) I := by
  apply TriangularSlots.ext
  intro x k
  apply I.cases (p := fun k => ((A.interleave B I).slots t).center x k =
    ((A.slots t).interleave (B.slots t) I).center x k) _ _ k
  · intro i
    change aeval _ ((A.interleave B I).center (I.left i)) = _
    rw [interleave_center_left]
    simpa only [TriangularSlots.interleave, SlotInterleaving.fill_left] using
      A.placeCenter_eval I.left I.left_strictMono i t x
  · intro i
    change aeval _ ((A.interleave B I).center (I.right i)) = _
    rw [interleave_center_right]
    simpa only [TriangularSlots.interleave, SlotInterleaving.fill_right] using
      B.placeCenter_eval I.right I.right_strictMono i t x

end PolynomialSlots

end Erdos3

end

section

namespace Erdos3

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

def constant (σ : Type*) (s : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    PolynomialPatch σ s 0 where
  weight := Fin.elim0
  weight_pos := fun i => Fin.elim0 i
  weight_le := fun i => Fin.elim0 i
  weight_mono i := Fin.elim0 i
  form := { center := fun i => Fin.elim0 i, degree := fun i => Fin.elim0 i }
  kernel := {
    value := fun _ => c
    nonneg := fun _ => hc.1
    le_one := fun _ => hc.2
    support := fun _ _ i => Fin.elim0 i
    lip := 0
    lipschitz := LipschitzWith.const c }

@[simp] theorem constant_value (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (t : σ → ℝ) :
    (constant σ s c hc).value t = c := by
  exact ((constant σ s c hc).form.slots t).patchValue_eq_at_residual (constant σ s c hc).kernel
    (b := 0) (fun i => Fin.elim0 i)

@[simp] theorem constant_lip (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (constant σ s c hc).kernel.lip = 0 := rfl

noncomputable def product (A : PolynomialPatch σ s D) (B : PolynomialPatch σ s E) :
    PolynomialPatch σ s (D + E) :=
  let I := SlotInterleaving.sorted A.weight B.weight A.weight_mono B.weight_mono
  { weight := I.fill A.weight B.weight
    weight_pos := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_pos i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_pos i)
    weight_le := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_le i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_le i)
    weight_mono := SlotInterleaving.sorted_weight_mono _ _ _ _
    form := A.form.interleave B.form I
    kernel := A.kernel.product B.kernel I }

@[simp] theorem product_lip (A : PolynomialPatch σ s D) (B : PolynomialPatch σ s E) :
    (A.product B).kernel.lip = A.kernel.lip + B.kernel.lip := rfl

@[simp] theorem product_value (A : PolynomialPatch σ s D) (B : PolynomialPatch σ s E)
    (t : σ → ℝ) : (A.product B).value t = A.value t * B.value t := by
  let I := SlotInterleaving.sorted A.weight B.weight A.weight_mono B.weight_mono
  change ((A.form.interleave B.form I).slots t).patchValue (A.kernel.product B.kernel I) = _
  rw [PolynomialSlots.interleave_slots, TriangularSlots.interleave_patchValue]
  rfl

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3
namespace PolynomialPatch

open MvPolynomial

variable {σ τ : Type*} {s : ℕ}

end PolynomialPatch
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NormalizedRealBoxHalfGrid
namespace OAI

section

namespace Erdos3

noncomputable def uniformIntervalGrid (B : ℝ) (N : ℕ) (k : Fin (N + 1)) : ℝ :=
  -B + (2 * B / N) * k

theorem uniformIntervalGrid_mem {B : ℝ} (hB : 0 ≤ B) {N : ℕ} (hN : 0 < N)
    (k : Fin (N + 1)) : |uniformIntervalGrid B N k| ≤ B := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (k : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ k.isLt
  have hstep : 0 ≤ 2 * B / N := by positivity
  have htop : (2 * B / N) * N = 2 * B := div_mul_cancel₀ _ hNr.ne'
  have hle := mul_le_mul_of_nonneg_left hk hstep
  apply abs_le.mpr
  dsimp [uniformIntervalGrid]
  constructor
  · have := mul_nonneg hstep (Nat.cast_nonneg k.val)
    linarith
  · linarith

theorem exists_uniformIntervalGrid_approx {B : ℝ} (hB : 0 < B) {N : ℕ} (hN : 0 < N)
    (x : ℝ) (hx : |x| ≤ B) :
    ∃ k : Fin (N + 1), |x - uniformIntervalGrid B N k| ≤ 2 * B / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let δ : ℝ := 2 * B / N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδN : δ * N = 2 * B := div_mul_cancel₀ _ hNr.ne'
  let q : ℝ := (x + B) / δ
  have hq0 : 0 ≤ q := div_nonneg (by linarith [(abs_le.mp hx).1]) hδ.le
  have hqN : q ≤ N := by
    apply (div_le_iff₀ hδ).mpr
    linarith [(abs_le.mp hx).2]
  let k : Fin (N + 1) := ⟨⌊q⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le hqN)⟩
  refine ⟨k, ?_⟩
  have hq : δ * q = x + B := by dsimp [q]; field_simp
  have heq : x - uniformIntervalGrid B N k = δ * (q - ⌊q⌋₊) := by
    change x - (-B + δ * (⌊q⌋₊ : ℝ)) = _
    rw [mul_sub, hq]
    ring
  rw [heq, abs_mul, abs_of_pos hδ]
  exact (mul_le_mul_of_nonneg_left (Nat.abs_sub_floor_le hq0) hδ.le).trans_eq (mul_one δ)

noncomputable def uniformBoxGrid {ι : Type*} (B : ℝ) (N : ℕ) (k : ι → Fin (N + 1)) : ι → ℝ :=
  fun i => uniformIntervalGrid B N (k i)

theorem uniformBoxGrid_mem {ι : Type*} {B : ℝ} (hB : 0 ≤ B) {N : ℕ} (hN : 0 < N)
    (k : ι → Fin (N + 1)) (i : ι) : |uniformBoxGrid B N k i| ≤ B :=
  uniformIntervalGrid_mem hB hN (k i)

theorem exists_uniformBoxGrid_approx {ι : Type*} [Fintype ι] {B : ℝ} (hB : 0 < B)
    {N : ℕ} (hN : 0 < N) (v : ι → ℝ) (hv : ∀ i, |v i| ≤ B) :
    ∃ k : ι → Fin (N + 1), dist v (uniformBoxGrid B N k) ≤ 2 * B / N := by
  classical
  choose k hk using fun i => exists_uniformIntervalGrid_approx hB hN (v i) (hv i)
  refine ⟨k, ?_⟩
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 2 * B / N)).mpr
  intro i
  simpa only [Real.dist_eq, uniformBoxGrid] using hk i

end Erdos3

end

section

namespace Erdos3

noncomputable def normalizedRealBoxGrid {σ : Type*} (T : σ → ℝ) (M : ℕ)
    (j : σ → Fin (M + 1)) : σ → ℝ :=
  fun i => T i * uniformBoxGrid 1 M j i

theorem normalizedRealBoxGrid_bound {σ : Type*} (T : σ → ℝ)
    (hT : ∀ i, 0 < T i) {M : ℕ} (hM : 0 < M)
    (j : σ → Fin (M + 1)) (i : σ) :
    |normalizedRealBoxGrid T M j i| ≤ T i := by
  rw [normalizedRealBoxGrid, abs_mul, abs_of_pos (hT i)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (uniformBoxGrid_mem (by norm_num : (0 : ℝ) ≤ 1) hM j i) (hT i).le

end Erdos3

end

section

namespace Erdos3

theorem exists_uniformIntervalGrid_half_approx {B : ℝ} (hB : 0 < B)
    {N : ℕ} (hN : 0 < N) (x : ℝ) (hx : |x| ≤ B) :
    ∃ k : Fin (N + 1), |x - uniformIntervalGrid B N k| ≤ B / N := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let δ : ℝ := 2 * B / N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδN : δ * N = 2 * B := div_mul_cancel₀ _ hNr.ne'
  let q : ℝ := (x + B) / δ
  have hq0 : 0 ≤ q := div_nonneg (by linarith [(abs_le.mp hx).1]) hδ.le
  have hqN : q ≤ N := by
    apply (div_le_iff₀ hδ).mpr
    linarith [(abs_le.mp hx).2]
  let k : Fin (N + 1) := ⟨⌊q + 1 / 2⌋₊, (Nat.floor_lt (by positivity)).mpr (by
    push_cast
    linarith)⟩
  have hk : |q - (k.val : ℝ)| ≤ 1 / 2 := by
    apply abs_le.mpr
    have hlo := Nat.floor_le (show 0 ≤ q + 1 / 2 by positivity)
    have hhi := Nat.lt_floor_add_one (q + 1 / 2)
    change -(1 / 2) ≤ q - (⌊q + 1 / 2⌋₊ : ℝ) ∧ _
    constructor <;> linarith
  refine ⟨k, ?_⟩
  have heq : x - uniformIntervalGrid B N k = δ * (q - k.val) := by
    have hδq : δ * q = x + B := by dsimp [q]; field_simp
    change x - (-B + δ * k.val) = _
    rw [mul_sub, hδq]
    ring
  rw [heq, abs_mul, abs_of_pos hδ]
  exact (mul_le_mul_of_nonneg_left hk hδ.le).trans_eq (by dsimp [δ]; ring)

theorem exists_normalizedRealBoxGrid_half_cell {σ : Type*}
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {N : ℕ} (hN : 0 < N)
    (v : σ → ℝ) (hv : ∀ i, |v i| ≤ T i) :
    ∃ j : σ → Fin (N + 1), ∀ i,
      |v i - normalizedRealBoxGrid T N j i| ≤ T i / N := by
  classical
  have hnorm (i : σ) : |v i / T i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hT i)]
    exact (div_le_one (hT i)).mpr (hv i)
  choose j hj using fun i => exists_uniformIntervalGrid_half_approx
    (by norm_num : (0 : ℝ) < 1) hN (v i / T i) (hnorm i)
  refine ⟨j, fun i => ?_⟩
  have heq : v i - normalizedRealBoxGrid T N j i =
      T i * (v i / T i - uniformIntervalGrid 1 N (j i)) := by
    dsimp only [normalizedRealBoxGrid, uniformBoxGrid]
    field_simp [(hT i).ne']
  rw [heq, abs_mul, abs_of_pos (hT i)]
  exact (mul_le_mul_of_nonneg_left (hj i) (hT i).le).trans_eq (by ring)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
namespace OAI

section

namespace Erdos3

structure ResidueBoxSlice {ι : Type*} (N : ι → ℕ) (q : ℕ) where
  start : ι → ℕ
  length : ι → ℕ
  inside : ∀ i j, j < length i → start i + q * j < N i

namespace ResidueBoxSlice

variable {ι : Type*} {N : ι → ℕ} {q : ℕ}

def point (A : ResidueBoxSlice N q) (j : ∀ i, Fin (A.length i)) : ∀ i, Fin (N i) :=
  fun i => ⟨A.start i + q * (j i).val, A.inside i _ (j i).isLt⟩

noncomputable def center (A : ResidueBoxSlice N q) : ι → ℝ :=
  fun i => (A.start i : ℝ) / N i

noncomputable abbrev ofBlocks (H : ι → ℕ) (hq : 0 < q) (hH : ∀ i, 0 < H i)
    (a : ∀ i, (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).Label) :
    ResidueBoxSlice N q where
  start i := (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).start (a i)
  length i := (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).length (a i)
  inside i _j hj := (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).point_lt (a i) hj

theorem ofBlocks_point (H : ι → ℕ) (hq : 0 < q) (hH : ∀ i, 0 < H i)
    (a : ∀ i, (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).Label)
    (j : ∀ i, Fin ((ofBlocks H hq hH a).length i)) :
    (ofBlocks H hq hH a).point j =
      BoxProgressionPartition.point (fun i => FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)) a j := by
  funext i
  apply Fin.ext
  rfl

end ResidueBoxSlice
end Erdos3

end

section

namespace Erdos3

namespace FiniteProgressionPartition

theorem entireResidue_length_ge {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (blocks N q (N + 1) hq (Nat.succ_pos N)).Label) :
    H ≤ (blocks N q (N + 1) hq (Nat.succ_pos N)).length i := by
  have hdiv : N / q / (N + 1) = 0 :=
    Nat.div_eq_of_lt ((Nat.div_le_self N q).trans_lt (Nat.lt_succ_self N))
  have hi : i.2.val = 0 := by
    have hi := i.2.isLt
    omega
  have hHN : H ≤ N := (Nat.le_mul_of_pos_left H hq).trans hfit
  have hlast : i.1.val + q * (H - 1) < N := by
    calc
      _ < q + q * (H - 1) := Nat.add_lt_add_right i.1.isLt _
      _ = q * ((H - 1) + 1) := by ring
      _ = q * H := by rw [Nat.sub_add_cancel hH]
      _ ≤ N := hfit
  have hlen : H - 1 < truncatedProgressionLength N (progressionBlockStart i) q (N + 1) := by
    apply (lt_truncatedProgressionLength_iff hq).mpr
    refine ⟨by omega, ?_⟩
    simpa only [progressionBlockStart, hi, Nat.mul_zero, Nat.add_zero] using hlast
  change H ≤ truncatedProgressionLength N (progressionBlockStart i) q (N + 1)
  omega

noncomputable def comparableResidues (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) : FiniteProgressionPartition N :=
  (blocks N q (N + 1) hq (Nat.succ_pos N)).bind
    (fun i => mergedIntervals _ H hH (entireResidue_length_ge hq hH hfit i))

theorem comparableResidues_step (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (comparableResidues N q H hq hH hfit).Label) :
    (comparableResidues N q H hq hH hfit).step i = q := by
  change q * 1 = q
  exact mul_one q

theorem comparableResidues_length (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (comparableResidues N q H hq hH hfit).Label) :
    H ≤ (comparableResidues N q H hq hH hfit).length i ∧
      (comparableResidues N q H hq hH hfit).length i < 2 * H :=
  mergedIntervals_length_bounds _ H hH (entireResidue_length_ge hq hH hfit i.1) i.2

end FiniteProgressionPartition

open scoped BigOperators

theorem exists_partition_cell_average {Ω K : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype K] (cell : Ω → K) (f : Ω → ℝ) :
    ∃ k, (partitionCell cell k).Nonempty ∧
      (𝔼 x, f x) ≤ 𝔼 x ∈ partitionCell cell k, f x := by
  classical
  by_contra! hnone
  have hstrict (k : K) (hk : (partitionCell cell k).Nonempty) :
      (∑ x ∈ partitionCell cell k, f x) < (partitionCell cell k).card * (𝔼 x, f x) := by
    have hcard : (0 : ℝ) < (partitionCell cell k).card := by exact_mod_cast hk.card_pos
    have h := mul_lt_mul_of_pos_left (hnone k hk) hcard
    rwa [Finset.card_mul_expect] at h
  have hle (k : K) : (∑ x ∈ partitionCell cell k, f x) ≤
      (partitionCell cell k).card * (𝔼 x, f x) := by
    by_cases hk : (partitionCell cell k).Nonempty
    · exact (hstrict k hk).le
    · simp [Finset.not_nonempty_iff_eq_empty.mp hk]
  obtain ⟨x₀⟩ := ‹Nonempty Ω›
  have hk : (partitionCell cell (cell x₀)).Nonempty :=
    ⟨x₀, (mem_partitionCell cell (cell x₀) x₀).mpr rfl⟩
  have hsum := Finset.sum_lt_sum (fun k (_ : k ∈ (Finset.univ : Finset K)) => hle k)
    ⟨cell x₀, Finset.mem_univ _, hstrict _ hk⟩
  rw [sum_partitionCell, ← Finset.sum_mul, card_partitionCell_sum,
    Fintype.expect_eq_sum_div_card] at hsum
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_div_cancel₀ _ hcard] at hsum
  exact lt_irrefl _ hsum

theorem exists_comparable_residueBoxSlice {I : Type*} [Fintype I] [DecidableEq I]
    (N H : I → ℕ) {q : ℕ} (hq : 0 < q) (hH : ∀ i, 0 < H i)
    (hfit : ∀ i, q * H i ≤ N i) (f : (∀ i, Fin (N i)) → ℝ) :
    ∃ A : ResidueBoxSlice N q,
      (∀ i, H i ≤ A.length i ∧ A.length i < 2 * H i) ∧
      (𝔼 x, f x) ≤ 𝔼 j : (∀ i, Fin (A.length i)), f (A.point j) := by
  classical
  let P := fun i => FiniteProgressionPartition.comparableResidues (N i) q (H i) hq (hH i) (hfit i)
  let : ∀ i, NeZero (N i) := fun i => ⟨ne_of_gt ((Nat.mul_pos hq (hH i)).trans_le (hfit i))⟩
  obtain ⟨k, _, hk⟩ := exists_partition_cell_average (BoxProgressionPartition.cell P) f
  let A : ResidueBoxSlice N q := {
    start := fun i => (P i).start (k i)
    length := fun i => (P i).length (k i)
    inside := fun i j hj => by
      have hp := (P i).point_lt (k i) hj
      rwa [FiniteProgressionPartition.comparableResidues_step] at hp }
  refine ⟨A, ?_, ?_⟩
  · intro i
    exact FiniteProgressionPartition.comparableResidues_length (N i) q (H i) hq (hH i) (hfit i) (k i)
  · rw [BoxProgressionPartition.expect_cell] at hk
    convert hk using 1
    apply Finset.expect_congr rfl
    intro j _
    congr 1
    ext i
    simp only [ResidueBoxSlice.point, BoxProgressionPartition.point_val,
      FiniteProgressionPartition.comparableResidues_step, A, P]

theorem exists_narrow_residueBoxSlice {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) {q : ℕ} (hq : 0 < q) {ρ : ℝ} (_hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hlarge : ∀ i, 4 * (q : ℝ) ≤ ρ * N i) (f : (∀ i, Fin (N i)) → ℝ) :
    ∃ A : ResidueBoxSlice N q,
      (∀ i, 0 < A.length i ∧ ρ * N i ≤ 4 * q * A.length i ∧
        (q : ℝ) * A.length i ≤ ρ * N i) ∧
      (𝔼 x, f x) ≤ 𝔼 j : (∀ i, Fin (A.length i)), f (A.point j) := by
  let H : I → ℕ := fun i => ⌊ρ * N i / (2 * q)⌋₊
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htwoq : (0 : ℝ) < 2 * q := by positivity
  have harg (i : I) : 2 ≤ ρ * N i / (2 * q) :=
    (le_div_iff₀ htwoq).mpr (by nlinarith [hlarge i])
  have hH (i : I) : 0 < H i := Nat.floor_pos.mpr (by linarith [harg i])
  have hupper (i : I) : (H i : ℝ) * (2 * q) ≤ ρ * N i :=
    (le_div_iff₀ htwoq).mp (Nat.floor_le (by linarith [harg i]))
  have hlower (i : I) : ρ * N i ≤ 4 * q * H i := by
    have hn : ρ * N i / (2 * q) < (H i : ℝ) + 1 := Nat.lt_floor_add_one _
    have hh : 1 ≤ (H i : ℝ) := by exact_mod_cast hH i
    have hquot : ρ * N i / (2 * q) ≤ 2 * H i := by linarith
    have hm := (div_le_iff₀ htwoq).mp hquot
    nlinarith
  have hfit (i : I) : q * H i ≤ N i := by
    have hn : ρ * (N i : ℝ) ≤ N i := mul_le_of_le_one_left (Nat.cast_nonneg _) hρ1
    have hm : (q : ℝ) * H i ≤ N i := by
      nlinarith [hupper i, mul_nonneg (Nat.cast_nonneg (α := ℝ) q) (Nat.cast_nonneg (α := ℝ) (H i))]
    exact_mod_cast hm
  obtain ⟨A, hA, hscore⟩ := exists_comparable_residueBoxSlice N H hq hH hfit f
  refine ⟨A, ?_, hscore⟩
  intro i
  have hlow : (H i : ℝ) ≤ A.length i := by exact_mod_cast (hA i).1
  have hhigh : (A.length i : ℝ) < 2 * H i := by exact_mod_cast (hA i).2
  refine ⟨(hH i).trans_le (hA i).1, ?_, ?_⟩
  · exact (hlower i).trans (mul_le_mul_of_nonneg_left hlow (by positivity))
  · have hm := mul_le_mul_of_nonneg_left hhigh.le hqR.le
    nlinarith [hupper i]

end Erdos3

end

section

namespace Erdos3

theorem denseResidueMeshInterval (b len M : ℕ) (hM : 0 < M) (hlen : 2 * M < len) :
    let lo := b / M + 1
    let hi := (b + len) / M
    lo < hi ∧ b ≤ M * lo ∧ M * hi ≤ b + len ∧
      len - (M * hi - M * lo) ≤ 2 * M := by
  dsimp only
  have hb := Nat.mod_add_div b M
  have he := Nat.mod_add_div (b + len) M
  have hbm := Nat.mod_lt b hM
  have hem := Nat.mod_lt (b + len) hM
  have hstart : b < M * (b / M + 1) := by nlinarith
  have hstartUpper : M * (b / M + 1) ≤ b + M := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hend : M * ((b + len) / M) ≤ b + len := by omega
  have hendLower : b + len < M * ((b + len) / M) + M := by omega
  have hlt : b / M + 1 < (b + len) / M := by nlinarith
  refine ⟨hlt, hstart.le, hend, ?_⟩
  have hmul : M * (b / M + 1) ≤ M * ((b + len) / M) :=
    Nat.mul_le_mul_left M hlt.le
  omega

theorem denseResidueMeshInterval_code_bound (b len M K : ℕ)
    (hM : 0 < M) (hlen : 2 * M < len) (hbox : b + len ≤ K * M) :
    b / M + 1 ≤ K ∧ (b + len) / M ≤ K := by
  have h := denseResidueMeshInterval b len M hM hlen
  dsimp only at h
  have hhi : (b + len) / M ≤ K := by nlinarith [h.2.2.1]
  exact ⟨h.1.le.trans hhi, hhi⟩

namespace ResidueBoxSlice
variable {X : Type*} {N : X → ℕ} {q : ℕ}

theorem residueIndex_endpoint_le (S : ResidueBoxSlice N q) (hq : 0 < q)
    (hlen : ∀ i, 0 < S.length i) (i : X) :
    S.start i / q + S.length i ≤ N i := by
  have hi := S.inside i (S.length i - 1) (by have := hlen i; omega)
  have hmul : S.length i - 1 ≤ q * (S.length i - 1) := by nlinarith
  have hdiv : S.start i / q ≤ S.start i := Nat.div_le_self _ _
  omega

def meshRounded (S : ResidueBoxSlice N q) (_hq : 0 < q) (M : ℕ)
    (hM : 0 < M) (hlen : ∀ i, 2 * M < S.length i) : ResidueBoxSlice N q where
  start i := S.start i % q + q * (M * (S.start i / q / M + 1))
  length i := M * ((S.start i / q + S.length i) / M) - M * (S.start i / q / M + 1)
  inside i j hj := by
    have h := denseResidueMeshInterval (S.start i / q) (S.length i) M hM (hlen i)
    dsimp only at h
    let offset := M * (S.start i / q / M + 1) - S.start i / q
    have ho : offset + j < S.length i := by dsimp [offset]; omega
    have he := S.inside i (offset + j) ho
    have hmod := Nat.mod_add_div (S.start i) q
    have hstart := h.2.1
    have hoff : offset + S.start i / q = M * (S.start i / q / M + 1) := by
      dsimp [offset]
      omega
    nlinarith

end ResidueBoxSlice
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {ι : Type*} {N : ι → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open MvPolynomial

variable {ι : Type*} {N : ι → ℕ} {q s d : ℕ}

noncomputable def parameters (A : ResidueBoxSlice N q) (i : ι) : MvPolynomial ι ℝ :=
  C (A.start i : ℝ) + (q : ℝ) • X i

theorem parameters_degree (A : ResidueBoxSlice N q) (i : ι) :
    A.parameters i ∈ weightedSupportLE (fun _ : ι => 1) 1 :=
  (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    ((weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ i))

noncomputable def reparamPatch (A : ResidueBoxSlice N q) (P : PolynomialPatch ι s d) :
    PolynomialPatch ι s d := P.reparam A.parameters A.parameters_degree

@[simp] theorem reparamPatch_kernel (A : ResidueBoxSlice N q) (P : PolynomialPatch ι s d) :
    (A.reparamPatch P).kernel = P.kernel := rfl

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

theorem exists_normalized_cell_of_coordinate_intervals {ι : Type*}
    (T lo hi : ι → ℝ) (hT : ∀ i, 0 < T i) {Q : ℕ} (hQ : 0 < Q)
    (hlo : ∀ i, |lo i| ≤ T i) (hhi : ∀ i, |hi i| ≤ T i)
    (hwidth : ∀ i, hi i - lo i ≤ 2 * T i / Q) :
    ∃ a : ι → Fin (Q + 1), ∀ v : ι → ℝ,
      (∀ i, lo i ≤ v i ∧ v i ≤ hi i) →
      ∀ i, |v i - normalizedRealBoxGrid T Q a i| ≤ T i * (2 / Q) := by
  let mid := fun i => (lo i + hi i) / 2
  have hm (i) : |mid i| ≤ T i := by
    apply abs_le.mpr
    have hl := abs_le.mp (hlo i)
    have hh := abs_le.mp (hhi i)
    dsimp only [mid]
    constructor <;> linarith
  obtain ⟨a, ha⟩ := exists_normalizedRealBoxGrid_half_cell T hT hQ mid hm
  refine ⟨a, ?_⟩
  intro v hv i
  have hd : |v i - mid i| ≤ T i / Q := by
    apply abs_le.mpr
    have hw := hwidth i
    rw [mul_div_assoc] at hw
    have hh := hv i
    dsimp only [mid]
    constructor <;> linarith
  calc
    _ ≤ |v i - mid i| + |mid i - normalizedRealBoxGrid T Q a i| := abs_sub_le _ _ _
    _ ≤ T i / Q + T i / Q := add_le_add hd (ha i)
    _ = T i * (2 / Q) := by ring

namespace ResidueBoxSlice

theorem exists_affine_normalized_cell {ι : Type*} {N : ι → ℕ} {q Q : ℕ}
    (A : ResidueBoxSlice N q) (hlen : ∀ i, 0 < A.length i)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i) (hQ : 0 < Q)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hwidth : ∀ i, step * q * A.length i ≤ 2 * T i / Q) :
    ∃ a : ι → Fin (Q + 1), ∀ j : ∀ i, Fin (A.length i), ∀ i,
      |origin i + step * (A.point j i).val - normalizedRealBoxGrid T Q a i| ≤
        T i * (2 / Q) := by
  let lo := fun i => origin i + step * A.start i
  let hi := fun i => origin i + step * (A.start i + q * (A.length i - 1) : ℕ)
  have hlo (i) : |lo i| ≤ T i := by
    apply hparent i (A.start i)
    simpa only [Nat.mul_zero, Nat.add_zero] using A.inside i 0 (hlen i)
  have hhi (i) : |hi i| ≤ T i :=
    hparent i _ (A.inside i _ (Nat.sub_lt (hlen i) (by decide)))
  have hw (i) : hi i - lo i ≤ 2 * T i / Q := by
    have hs : step * (q : ℝ) * (A.length i - 1 : ℕ) ≤ step * q * A.length i :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.sub_le _ _)) (by positivity)
    dsimp only [hi, lo]
    push_cast
    nlinarith [hwidth i]
  obtain ⟨a, ha⟩ := exists_normalized_cell_of_coordinate_intervals T lo hi hT hQ hlo hhi hw
  refine ⟨a, fun j => ha (fun i => origin i + step * (A.point j i).val) ?_⟩
  intro i
  have hj : (j i).val ≤ A.length i - 1 := by have := (j i).isLt; omega
  have hs := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hj : ((j i).val : ℝ) ≤ _)
    (show 0 ≤ step * (q : ℝ) by positivity)
  dsimp only [lo, hi, point]
  push_cast
  constructor
  · have hn : 0 ≤ step * (q : ℝ) * ((j i).val : ℝ) := by positivity
    nlinarith
  · nlinarith

end ResidueBoxSlice
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteSpanRounding
namespace OAI

section

namespace Erdos3

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

def boundedSpanCell (v : ι → V) (c : ℝ) : Set V :=
  (fun t : ι → ℝ => ∑ i, t i • v i) '' Set.univ.pi (fun _ => Set.Icc 0 c)

theorem boundedSpanCell_subset_span (v : ι → V) (c : ℝ) :
    boundedSpanCell v c ⊆ Submodule.span ℝ (Set.range v) := by
  rintro _ ⟨t, _, rfl⟩
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem exists_bounded_span_remainder (v : ι → V) (c : ℝ) (hc : 0 < c)
    (x : V) (hx : x ∈ Submodule.span ℝ (Set.range v)) :
    ∃ r ∈ boundedSpanCell v c, ∃ z : ι → ℤ, x = r + ∑ i, ((z i : ℝ) * c) • v i := by
  classical
  obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  let z : ι → ℤ := fun i => ⌊t i / c⌋
  let u : ι → ℝ := fun i => t i - (z i : ℝ) * c
  refine ⟨∑ i, u i • v i, ⟨u, ?_, rfl⟩, z, ?_⟩
  · intro i _
    exact ⟨Int.sub_floor_div_mul_nonneg (t i) hc, (Int.sub_floor_div_mul_lt (t i) hc).le⟩
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← add_smul]
    congr 1
    dsimp [u]
    ring

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

theorem isCompact_boundedSpanCell (v : ι → V) (c : ℝ) : IsCompact (boundedSpanCell v c) := by
  apply (isCompact_univ_pi (fun _ : ι => isCompact_Icc)).image
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).smul continuous_const)

end Erdos3

end

end OAI

end


