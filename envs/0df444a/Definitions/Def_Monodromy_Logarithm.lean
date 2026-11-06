-- Prove2me | Definitions.Def_Monodromy_Logarithm
-- name    : Monodromy_Logarithm
-- status  : Definition
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:18:39.60058+00:00
-- url     : https://prove2.me/theorems/8f99602a-f28b-43b2-a414-13f430222290
-- title:
--   Logarithm Sheets and Nested Exponential Lift Execution
-- statement:
--   Identifies the exponential circle fiber with integer sheet labels and defines loop transport as a common translation of those labels. Builds nested complex-exponential execution from two actual logarithmic lifts, including a fixed zero-conditional upper write, branch preparation, concatenation, reversal and the matching restricted pullback covering.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Logarithm.lean (file SHA-256 7c717767a34b9975b34b033cf81fed276c1e642f6bb7abceab23baba8a3ee1d1):
--   Monodromy.Logarithm.Memory at L29-L29 [UTF-8 858:914].
--   Monodromy.Logarithm.sheet at L31-L32 [UTF-8 916:1024].
--   Monodromy.Logarithm.integers at L34-L42 [UTF-8 1026:1466].
--   Monodromy.Logarithm.turn at L44-L49 [UTF-8 1468:1758].
--   Monodromy.Logarithm.lift at L51-L54 [UTF-8 1760:1993].
--   Monodromy.NestedContinuation.Punctured at L103-L103 [UTF-8 3914:3954].
--   Monodromy.NestedContinuation.expCover at L105-L105 [UTF-8 3956:4036].
--   Monodromy.NestedContinuation.covering at L107-L107 [UTF-8 4038:4108].
--   Monodromy.NestedContinuation.period at L109-L109 [UTF-8 4110:4177].
--   Monodromy.NestedContinuation.exp_period at L111-L112 [UTF-8 4179:4281].
--   Monodromy.NestedContinuation.rotor at L114-L114 [UTF-8 4283:4356].
--   Monodromy.NestedContinuation.continuous_rotor at L116-L116 [UTF-8 4358:4430].
--   Monodromy.NestedContinuation.rotor_zero at L118-L118 [UTF-8 4432:4491].
--   Monodromy.NestedContinuation.rotor_one at L119-L119 [UTF-8 4492:4550].
--   Monodromy.NestedContinuation.rotor_ne_zero at L121-L121 [UTF-8 4552:4627].
--   Monodromy.NestedContinuation.rotor_norm at L123-L123 [UTF-8 4629:4702].
--   Monodromy.NestedContinuation.firstRoot at L125-L125 [UTF-8 4704:4749].
--   Monodromy.NestedContinuation.firstRoot_slit at L127-L129 [UTF-8 4751:4859].
--   Monodromy.NestedContinuation.firstRoot_ne_zero at L131-L132 [UTF-8 4861:4966].
--   Monodromy.NestedContinuation.secondRoot at L134-L134 [UTF-8 4968:5040].
--   Monodromy.NestedContinuation.exp_secondRoot at L136-L137 [UTF-8 5042:5222].
--   Monodromy.NestedContinuation.base at L139-L139 [UTF-8 5224:5258].
--   Monodromy.NestedContinuation.exp_firstRoot at L141-L144 [UTF-8 5260:5445].
--   Monodromy.NestedContinuation.loop at L146-L151 [UTF-8 5447:5687].
--   Monodromy.NestedContinuation.firstLift at L153-L155 [UTF-8 5689:5908].
--   Monodromy.NestedContinuation.firstWitness at L157-L159 [UTF-8 5910:6054].
--   Monodromy.NestedContinuation.firstWitness_projects at L161-L165 [UTF-8 6056:6287].
--   Monodromy.NestedContinuation.firstLift_eq at L167-L172 [UTF-8 6289:6723].
--   Monodromy.NestedContinuation.firstLift_slit at L174-L191 [UTF-8 6725:7721].
--   Monodromy.NestedContinuation.firstLift_ne_zero at L193-L197 [UTF-8 7723:7955].
--   Monodromy.NestedContinuation.firstPath at L199-L206 [UTF-8 7957:8437].
--   Monodromy.NestedContinuation.secondLift at L208-L211 [UTF-8 8439:8721].
--   Monodromy.NestedContinuation.zeroWitness at L213-L215 [UTF-8 8723:8878].
--   Monodromy.NestedContinuation.zeroWitness_projects at L217-L222 [UTF-8 8880:9199].
--   Monodromy.NestedContinuation.nonzeroWitness at L224-L226 [UTF-8 9201:9429].
--   Monodromy.NestedContinuation.nonzeroWitness_projects at L228-L233 [UTF-8 9431:9762].
--   Monodromy.NestedContinuation.secondLift_end at L235-L252 [UTF-8 9764:10741].
--   Monodromy.NestedContinuation.loop_avoids_one at L277-L286 [UTF-8 11894:12365].
--   Monodromy.NestedContinuation.Memory at L288-L289 [UTF-8 12367:12546].
--   Monodromy.NestedContinuation.prepare at L291-L294 [UTF-8 12548:12707].
--   Monodromy.NestedContinuation.firstRaw at L296-L298 [UTF-8 12709:12943].
--   Monodromy.NestedContinuation.firstRaw_projects at L300-L302 [UTF-8 12945:13155].
--   Monodromy.NestedContinuation.firstRaw_start at L304-L306 [UTF-8 13157:13369].
--   Monodromy.NestedContinuation.firstRaw_ne_zero at L308-L317 [UTF-8 13371:13833].
--   Monodromy.NestedContinuation.firstRawPath at L319-L327 [UTF-8 13835:14367].
--   Monodromy.NestedContinuation.secondRaw at L329-L331 [UTF-8 14369:14609].
--   Monodromy.NestedContinuation.secondRaw_exp at L333-L338 [UTF-8 14611:15010].
--   Monodromy.NestedContinuation.secondRaw_start at L340-L344 [UTF-8 15012:15307].
--   Monodromy.NestedContinuation.secondRaw_projects at L346-L350 [UTF-8 15309:15599].
--   Monodromy.NestedContinuation.execute at L352-L355 [UTF-8 15601:15903].
--   Monodromy.NestedContinuation.firstRaw_prepare at L357-L361 [UTF-8 15905:16181].
--   Monodromy.NestedContinuation.secondRaw_prepare at L363-L372 [UTF-8 16183:16762].
--   Monodromy.NestedContinuation.execute_prepare at L374-L379 [UTF-8 16764:17022].
--   Monodromy.NestedContinuation.advanceLoop at L381-L391 [UTF-8 17024:17614].
--   Monodromy.NestedContinuation.advanceLoop_avoids_one at L393-L399 [UTF-8 17616:17993].
--   Monodromy.NestedContinuation.advanceWitness at L401-L403 [UTF-8 17995:18164].
--   Monodromy.NestedContinuation.advanceWitness_start at L405-L406 [UTF-8 18166:18277].
--   Monodromy.NestedContinuation.advanceWitness_end at L408-L410 [UTF-8 18279:18420].
--   Monodromy.NestedContinuation.advanceWitness_slit at L412-L414 [UTF-8 18422:18574].
--   Monodromy.NestedContinuation.advanceWitness_projects at L416-L422 [UTF-8 18576:18956].
--   Monodromy.NestedContinuation.advance_firstRaw at L424-L428 [UTF-8 18958:19345].
--   Monodromy.NestedContinuation.advanceSecondWitness at L430-L432 [UTF-8 19347:19570].
--   Monodromy.NestedContinuation.advance_secondRaw at L434-L448 [UTF-8 19572:20500].
--   Monodromy.NestedContinuation.execute_advance at L450-L458 [UTF-8 20502:20936].
--   Monodromy.NestedContinuation.period_injective at L465-L470 [UTF-8 21013:21325].
--   Monodromy.NestedContinuation.firstRoot_injective at L472-L474 [UTF-8 21327:21465].
--   Monodromy.NestedContinuation.avoids_trans at L524-L533 [UTF-8 23613:24066].
--   Monodromy.NestedContinuation.avoids_symm at L535-L539 [UTF-8 24068:24281].
--   Monodromy.NestedContinuation.executionPath at L541-L548 [UTF-8 24283:24716].
--   Monodromy.NestedContinuation.sequentialPath at L555-L561 [UTF-8 24985:25508].
--   Monodromy.NestedRestricted.baseSet at L706-L706 [UTF-8 31877:31939].
--   Monodromy.NestedRestricted.firstSet at L707-L707 [UTF-8 31940:31992].
--   Monodromy.NestedRestricted.secondSet at L708-L708 [UTF-8 31993:32047].
--   Monodromy.NestedRestricted.firstProjection at L710-L710 [UTF-8 32049:32131].
--   Monodromy.NestedRestricted.secondProjection at L711-L711 [UTF-8 32132:32218].
--   Monodromy.NestedRestricted.firstCovering at L713-L716 [UTF-8 32220:32389].
--   Monodromy.NestedRestricted.firstSet_nonzero at L718-L722 [UTF-8 32391:32579].
--   Monodromy.NestedRestricted.basePath at L739-L751 [UTF-8 33185:33942].
--   Monodromy.NestedContinuation.firstRaw_mem at L762-L771 [UTF-8 34041:34604].
--   Monodromy.NestedContinuation.secondRaw_mem at L773-L779 [UTF-8 34606:35049].
--   Monodromy.NestedContinuation.lowerCurve at L781-L785 [UTF-8 35051:35361].
--   Monodromy.NestedContinuation.upperCurve at L787-L791 [UTF-8 35363:35691].

-- Generated by Lean-fact skeleton subtraction; original source is frozen in imports/monodromy/source.
module
public import Definitions.Def_Monodromy_Covering
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section


/-!
# The branches of the logarithm

Restricting the exponential to imaginary arguments gives the circle covering.
Its fiber over one retains an integer. A loop transports every initial
branch by addition, proved from its actual continuous lift. Nested complex
exponentials supply a conditional upper write: the actual lower lift winds
around the upper logarithm's omitted point only on the zero branch.
-/

@[expose] public section

namespace Monodromy.Logarithm

open unitInterval

abbrev Memory := Transport.Fiber Circle.exp (1 : Circle)

noncomputable def sheet (k : ℤ) : Memory :=
  ⟨(k : ℝ) * (2 * Real.pi), Circle.exp_int_mul_two_pi k⟩

noncomputable def integers : ℤ ≃ Memory := Equiv.ofBijective sheet ⟨by
    intro k n same
    have values := congrArg Subtype.val same
    change (k : ℝ) * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) at values
    exact Int.cast_injective (mul_right_cancel₀
      (mul_ne_zero two_ne_zero Real.pi_ne_zero) values), by
    intro root
    obtain ⟨k, same⟩ := Circle.exp_eq_one.mp root.2
    exact ⟨k, Subtype.ext same.symm⟩⟩

noncomputable def turn (n : ℤ) : Path (1 : Circle) 1 where
  toFun t := Circle.exp (((n : ℝ) * (t : ℝ)) * (2 * Real.pi))
  continuous_toFun := Circle.exp.continuous.comp
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  source' := by simp
  target' := by simp

noncomputable def lift (k n : ℤ) : C(I, ℝ) where
  toFun t := ((k : ℝ) + (n : ℝ) * (t : ℝ)) * (2 * Real.pi)
  continuous_toFun := (continuous_const.add
    (continuous_const.mul continuous_subtype_val)).mul continuous_const





end Monodromy.Logarithm


/-! Two successive logarithmic lifts and their fixed-loop actions. -/

noncomputable section

namespace Monodromy.NestedContinuation

open unitInterval

abbrev Punctured := {z : ℂ // z ≠ 0}

def expCover (z : ℂ) : Punctured := ⟨Complex.exp z, Complex.exp_ne_zero z⟩

theorem covering : IsCoveringMap expCover := Complex.isCoveringMap_exp

def period (k : ℤ) : ℂ := (k : ℂ) * (2 * Real.pi * Complex.I)

theorem exp_period (k : ℤ) : Complex.exp (period k) = 1 :=
  Complex.exp_eq_one_iff.mpr ⟨k, rfl⟩

def rotor (t : I) : ℂ := (Circle.exp ((2 * Real.pi) * (t : ℝ)) : ℂ)

theorem continuous_rotor : Continuous rotor := by unfold rotor; fun_prop

@[simp] theorem rotor_zero : rotor 0 = 1 := by simp [rotor]
@[simp] theorem rotor_one : rotor 1 = 1 := by simp [rotor]

theorem rotor_ne_zero (t : I) : rotor t ≠ 0 := (Circle.exp _).coe_ne_zero

theorem rotor_norm (t : I) : ‖rotor t‖ = 1 := (Circle.exp _).norm_coe

def firstRoot (k : ℤ) : ℂ := 1 + period k

theorem firstRoot_slit (k : ℤ) : firstRoot k ∈ Complex.slitPlane := by
  left
  simp [firstRoot, period]

theorem firstRoot_ne_zero (k : ℤ) : firstRoot k ≠ 0 :=
  Complex.slitPlane_ne_zero (firstRoot_slit k)

def secondRoot (k m : ℤ) : ℂ := Complex.log (firstRoot k) + period m

theorem exp_secondRoot (k m : ℤ) : Complex.exp (secondRoot k m) = firstRoot k := by
  rw [secondRoot, Complex.exp_add, exp_period, mul_one, Complex.exp_log (firstRoot_ne_zero k)]

def base : Punctured := expCover 1

theorem exp_firstRoot (k : ℤ) : expCover (firstRoot k) = base := by
  apply Subtype.ext
  change Complex.exp (1 + period k) = Complex.exp 1
  rw [Complex.exp_add, exp_period, mul_one]

/-- One fixed base loop, independent of both branch indices. -/
def loop : Path base base where
  toFun t := expCover (rotor t)
  continuous_toFun := by unfold expCover rotor; fun_prop
  source' := by simp [base]
  target' := by simp [base]

/-- This is the actual first lift supplied by the covering, not a prescribed successor. -/
 def firstLift (k : ℤ) : C(I, ℂ) :=
  covering.liftPath loop (firstRoot k) (loop.source.trans (exp_firstRoot k).symm)

 def firstWitness (k : ℤ) : C(I, ℂ) where
  toFun t := rotor t + period k
  continuous_toFun := continuous_rotor.add continuous_const

 theorem firstWitness_projects (k : ℤ) : expCover ∘ firstWitness k = loop := by
  funext t
  apply Subtype.ext
  change Complex.exp (rotor t + period k) = Complex.exp (rotor t)
  rw [Complex.exp_add, exp_period, mul_one]

/-- The explicit circle is identified with the unique first lift only in the proof. -/
 theorem firstLift_eq (k : ℤ) (t : I) : firstLift k t = rotor t + period k := by
  have same : firstWitness k = firstLift k :=
    (covering.eq_liftPath_iff' (loop.source.trans (exp_firstRoot k).symm)).mpr
      ⟨firstWitness_projects k, by simp [firstWitness, firstRoot]⟩
  exact congrArg (fun curve : C(I, ℂ) => curve t) same.symm

/-- Every nonzero first-level index keeps its circle in one logarithm chart. -/
 theorem firstLift_slit {k : ℤ} (nonzero : k ≠ 0) (t : I) :
    firstLift k t ∈ Complex.slitPlane := by
  rw [firstLift_eq]
  apply Or.inr
  have bound : |(rotor t).im| ≤ 1 := (Complex.abs_im_le_norm _).trans_eq (rotor_norm t)
  have imag : (period k).im = (k : ℝ) * (2 * Real.pi) := by simp [period]
  simp only [Complex.add_im, imag]
  intro zero
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · have integer : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    have lower : -1 ≤ (rotor t).im := (abs_le.mp bound).1
    have upper : (rotor t).im ≤ 1 := (abs_le.mp bound).2
    nlinarith [Real.pi_gt_three, Real.pi_pos]
  · have integer : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have lower : -1 ≤ (rotor t).im := (abs_le.mp bound).1
    have upper : (rotor t).im ≤ 1 := (abs_le.mp bound).2
    nlinarith [Real.pi_gt_three, Real.pi_pos]

 theorem firstLift_ne_zero (k : ℤ) (t : I) : firstLift k t ≠ 0 := by
  by_cases zero : k = 0
  · subst k
    simpa [firstLift_eq, period] using rotor_ne_zero t
  · exact Complex.slitPlane_ne_zero (firstLift_slit zero t)

/-- The next covering receives the actual first lift, preserving its nonzero values. -/
 def firstPath (k : ℤ) : Path
    (⟨firstRoot k, firstRoot_ne_zero k⟩ : Punctured)
    ⟨firstRoot k, firstRoot_ne_zero k⟩ where
  toFun t := ⟨firstLift k t, firstLift_ne_zero k t⟩
  continuous_toFun := (firstLift k).continuous.subtype_mk _
  source' := by apply Subtype.ext; simp [firstLift_eq, firstRoot]
  target' := by apply Subtype.ext; simp [firstLift_eq, firstRoot]

/-- The second lift is generated from the first actual lift and the initial branch alone. -/
 def secondLift (k m : ℤ) : C(I, ℂ) :=
  covering.liftPath (firstPath k) (secondRoot k m)
    ((firstPath k).source.trans (by apply Subtype.ext; exact (exp_secondRoot k m).symm))

 def zeroWitness (m : ℤ) : C(I, ℂ) where
  toFun t := ((2 * Real.pi) * (t : ℝ) : ℂ) * Complex.I + period m
  continuous_toFun := by fun_prop

 theorem zeroWitness_projects (m : ℤ) : expCover ∘ zeroWitness m = firstPath 0 := by
  funext t
  apply Subtype.ext
  change Complex.exp (((2 * Real.pi) * (t : ℝ) : ℂ) * Complex.I + period m) = firstLift 0 t
  rw [Complex.exp_add, exp_period, mul_one, firstLift_eq]
  simp [period, rotor, Circle.coe_exp]

 def nonzeroWitness (k m : ℤ) (nonzero : k ≠ 0) : C(I, ℂ) where
  toFun t := Complex.log (firstLift k t) + period m
  continuous_toFun := ((firstLift k).continuous.clog (firstLift_slit nonzero)).add continuous_const

 theorem nonzeroWitness_projects (k m : ℤ) (nonzero : k ≠ 0) :
    expCover ∘ nonzeroWitness k m nonzero = firstPath k := by
  funext t
  apply Subtype.ext
  change Complex.exp (Complex.log (firstLift k t) + period m) = firstLift k t
  rw [Complex.exp_add, exp_period, mul_one, Complex.exp_log (firstLift_ne_zero k t)]

/-- Native conditional execution comes from two actual lifts of one fixed loop. -/
 theorem secondLift_end (k m : ℤ) :
    secondLift k m 1 = secondRoot k (m + if k = 0 then 1 else 0) := by
  by_cases zero : k = 0
  · subst k
    have same : zeroWitness m = secondLift 0 m :=
      (covering.eq_liftPath_iff'
        ((firstPath 0).source.trans (by apply Subtype.ext; exact (exp_secondRoot 0 m).symm))).mpr
        ⟨zeroWitness_projects m, by simp [zeroWitness, secondRoot, firstRoot, period]⟩
    rw [← same]
    simp [zeroWitness, secondRoot, firstRoot, period]
    ring
  · have same : nonzeroWitness k m zero = secondLift k m :=
      (covering.eq_liftPath_iff'
        ((firstPath k).source.trans (by apply Subtype.ext; exact (exp_secondRoot k m).symm))).mpr
        ⟨nonzeroWitness_projects k m zero, by simp [nonzeroWitness, firstLift_eq, secondRoot, firstRoot]⟩
    rw [← same]
    simp [nonzeroWitness, firstLift_eq, secondRoot, firstRoot, zero]












/-- The fixed base path avoids the second singular value. -/
theorem loop_avoids_one (t : I) : loop t ≠ (⟨1, one_ne_zero⟩ : Punctured) := by
  intro same
  have exponential : Complex.exp (rotor t) = 1 := congrArg Subtype.val same
  obtain ⟨n, period_eq⟩ := Complex.exp_eq_one_iff.mp exponential
  have zero : firstLift (-n) t = 0 := by
    rw [firstLift_eq]
    rw [show rotor t = period n from period_eq]
    simp [period]
  exact firstLift_ne_zero (-n) t zero

/-- A native state is the retained root value, with no integer indices in the runtime interface. -/
abbrev Memory := Transport.Fiber (fun z : ℂ => expCover (Complex.exp z)) base

def prepare (k m : ℤ) : Memory :=
  ⟨secondRoot k m, by
    change expCover (Complex.exp (secondRoot k m)) = base
    rw [exp_secondRoot, exp_firstRoot]⟩

/-- The first lift starts at the exponential of the retained root itself. -/
def firstRaw (path : Path base base) (state : Memory) : C(I, ℂ) :=
  covering.liftPath path (Complex.exp state.val) (path.source.trans state.property.symm)

theorem firstRaw_projects (path : Path base base) (state : Memory) :
    expCover ∘ firstRaw path state = path :=
  covering.liftPath_lifts path (Complex.exp state.val) (path.source.trans state.property.symm)

theorem firstRaw_start (path : Path base base) (state : Memory) :
    firstRaw path state 0 = Complex.exp state.val :=
  covering.liftPath_zero path (Complex.exp state.val) (path.source.trans state.property.symm)

theorem firstRaw_ne_zero (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    firstRaw path state t ≠ 0 := by
  intro zero
  have projects := congrFun (firstRaw_projects path state) t
  apply avoids t
  calc
    path t = expCover (firstRaw path state t) := projects.symm
    _ = expCover 0 := congrArg expCover zero
    _ = (⟨1, one_ne_zero⟩ : Punctured) := Subtype.ext Complex.exp_zero

/-- The upper covering receives exactly the actual first lift. -/
def firstRawPath (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    Path (expCover state.val)
      ⟨firstRaw path state 1, firstRaw_ne_zero path avoids state 1⟩ where
  toFun t := ⟨firstRaw path state t, firstRaw_ne_zero path avoids state t⟩
  continuous_toFun := (firstRaw path state).continuous.subtype_mk _
  source' := by apply Subtype.ext; exact firstRaw_start path state
  target' := rfl

def secondRaw (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) : C(I, ℂ) :=
  covering.liftPath (firstRawPath path avoids state) state.val (firstRawPath path avoids state).source

theorem secondRaw_exp (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    Complex.exp (secondRaw path avoids state t) = firstRaw path state t := by
  have projects := covering.liftPath_lifts (firstRawPath path avoids state) state.val
    (firstRawPath path avoids state).source
  exact congrArg Subtype.val (congrFun projects t)

theorem secondRaw_start (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    secondRaw path avoids state 0 = state.val :=
  covering.liftPath_zero (firstRawPath path avoids state) state.val
    (firstRawPath path avoids state).source

theorem secondRaw_projects (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    expCover (Complex.exp (secondRaw path avoids state t)) = path t := by
  rw [secondRaw_exp]
  exact congrFun (firstRaw_projects path state) t

/-- Execution uses only the fixed path and the actual retained root. -/
def execute (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) : Memory :=
  ⟨secondRaw path avoids state 1, (secondRaw_projects path avoids state 1).trans path.target⟩

 theorem firstRaw_prepare (k m : ℤ) : firstRaw loop (prepare k m) = firstLift k :=
  (covering.eq_liftPath_iff' (loop.source.trans (exp_firstRoot k).symm)).mpr
    ⟨firstRaw_projects loop (prepare k m), by
      rw [firstRaw_start]
      exact exp_secondRoot k m⟩

 theorem secondRaw_prepare (k m : ℤ) :
    secondRaw loop loop_avoids_one (prepare k m) = secondLift k m := by
  have projects : expCover ∘ secondRaw loop loop_avoids_one (prepare k m) = firstPath k := by
    funext t
    apply Subtype.ext
    change Complex.exp (secondRaw loop loop_avoids_one (prepare k m) t) = firstLift k t
    rw [secondRaw_exp, firstRaw_prepare]
  exact (covering.eq_liftPath_iff'
    ((firstPath k).source.trans (by apply Subtype.ext; exact (exp_secondRoot k m).symm))).mpr
    ⟨projects, secondRaw_start loop loop_avoids_one (prepare k m)⟩

theorem execute_prepare (k m : ℤ) :
    execute loop loop_avoids_one (prepare k m) = prepare k (m + if k = 0 then 1 else 0) := by
  apply Subtype.ext
  change secondRaw loop loop_avoids_one (prepare k m) 1 = _
  rw [secondRaw_prepare, secondLift_end]
  rfl

/-- A second fixed base loop uses the same two coverings. -/
def advanceLoop : Path base base where
  toFun t := expCover (1 + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I)
  continuous_toFun := by unfold expCover; fun_prop
  source' := by apply Subtype.ext; simp [base, expCover]
  target' := by
    apply Subtype.ext
    change Complex.exp (1 + (((2 * Real.pi) * (1 : ℝ) : ℝ) : ℂ) * Complex.I) = Complex.exp 1
    have turn : (((2 * Real.pi) * (1 : ℝ) : ℝ) : ℂ) * Complex.I = period 1 := by simp [period]
    rw [turn]
    exact congrArg Subtype.val (exp_firstRoot 1)

theorem advanceLoop_avoids_one (t : I) : advanceLoop t ≠ (⟨1, one_ne_zero⟩ : Punctured) := by
  intro same
  have exponential : Complex.exp (1 + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I) = 1 :=
    congrArg Subtype.val same
  obtain ⟨n, period_eq⟩ := Complex.exp_eq_one_iff.mp exponential
  have real_eq := congrArg Complex.re period_eq
  simp at real_eq

 def advanceWitness (k : ℤ) : C(I, ℂ) where
  toFun t := firstRoot k + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I
  continuous_toFun := by fun_prop

 theorem advanceWitness_start (k : ℤ) : advanceWitness k 0 = firstRoot k := by
  simp [advanceWitness]

 theorem advanceWitness_end (k : ℤ) : advanceWitness k 1 = firstRoot (k + 1) := by
  simp [advanceWitness, firstRoot, period]
  ring

 theorem advanceWitness_slit (k : ℤ) (t : I) : advanceWitness k t ∈ Complex.slitPlane := by
  left
  simp [advanceWitness, firstRoot, period]

 theorem advanceWitness_projects (k : ℤ) : expCover ∘ advanceWitness k = advanceLoop := by
  funext t
  apply Subtype.ext
  change Complex.exp (firstRoot k + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
    Complex.exp (1 + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I)
  unfold firstRoot
  rw [add_right_comm, Complex.exp_add, exp_period, mul_one]

 theorem advance_firstRaw (k m : ℤ) : firstRaw advanceLoop (prepare k m) = advanceWitness k := by
  have same : advanceWitness k = firstRaw advanceLoop (prepare k m) :=
    (covering.eq_liftPath_iff' (advanceLoop.source.trans (prepare k m).property.symm)).mpr
      ⟨advanceWitness_projects k, by rw [advanceWitness_start]; exact (exp_secondRoot k m).symm⟩
  exact same.symm

 def advanceSecondWitness (k m : ℤ) : C(I, ℂ) where
  toFun t := Complex.log (advanceWitness k t) + period m
  continuous_toFun := ((advanceWitness k).continuous.clog (advanceWitness_slit k)).add continuous_const

 theorem advance_secondRaw (k m : ℤ) :
    secondRaw advanceLoop advanceLoop_avoids_one (prepare k m) = advanceSecondWitness k m := by
  have projects : expCover ∘ advanceSecondWitness k m = firstRawPath advanceLoop advanceLoop_avoids_one (prepare k m) := by
    funext t
    apply Subtype.ext
    change Complex.exp (Complex.log (advanceWitness k t) + period m) = firstRaw advanceLoop (prepare k m) t
    rw [Complex.exp_add, exp_period, mul_one,
      Complex.exp_log (Complex.slitPlane_ne_zero (advanceWitness_slit k t)), advance_firstRaw]
  have same : advanceSecondWitness k m = secondRaw advanceLoop advanceLoop_avoids_one (prepare k m) :=
    (covering.eq_liftPath_iff' (firstRawPath advanceLoop advanceLoop_avoids_one (prepare k m)).source).mpr
      ⟨projects, by
        change Complex.log (advanceWitness k 0) + period m = secondRoot k m
        rw [advanceWitness_start]
        rfl⟩
  exact same.symm

/-- The other fixed loop advances the lower branch, retaining the upper branch. -/
theorem execute_advance (k m : ℤ) :
    execute advanceLoop advanceLoop_avoids_one (prepare k m) = prepare (k + 1) m := by
  apply Subtype.ext
  change secondRaw advanceLoop advanceLoop_avoids_one (prepare k m) 1 = secondRoot (k + 1) m
  rw [advance_secondRaw]
  change Complex.log (advanceWitness k 1) + period m = _
  rw [advanceWitness_end]
  rfl

end Monodromy.NestedContinuation


namespace Monodromy.NestedContinuation

theorem period_injective : Function.Injective period := by
  intro first second same
  have factor : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  unfold period at same
  exact_mod_cast mul_right_cancel₀ factor same

theorem firstRoot_injective : Function.Injective firstRoot := by
  intro first second same
  exact period_injective (add_left_cancel same)






end Monodromy.NestedContinuation

namespace Monodromy.NestedContinuation

open unitInterval



/-- A composite program still avoids the excluded singular value. -/
theorem avoids_trans (first second : Path base base)
    (first_avoids : ∀ t, first t ≠ (⟨1, one_ne_zero⟩ : Punctured))
    (second_avoids : ∀ t, second t ≠ (⟨1, one_ne_zero⟩ : Punctured)) :
    ∀ t, (first.trans second) t ≠ (⟨1, one_ne_zero⟩ : Punctured) := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact first_avoids _
  · exact second_avoids _

theorem avoids_symm (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) :
    ∀ t, path.symm t ≠ (⟨1, one_ne_zero⟩ : Punctured) := by
  intro t
  exact avoids (σ t)

/-- This path is the actual second lift itself, with its proved start and end. -/
def executionPath (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    Path state.val (execute path avoids state).val where
  toFun := secondRaw path avoids state
  continuous_toFun := (secondRaw path avoids state).continuous
  source' := secondRaw_start path avoids state
  target' := rfl



/-- Later execution begins at the actual retained endpoint of the preceding lift. -/
def sequentialPath (first second : Path base base)
    (first_avoids : ∀ t, first t ≠ (⟨1, one_ne_zero⟩ : Punctured))
    (second_avoids : ∀ t, second t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    Path state.val (execute second second_avoids (execute first first_avoids state)).val :=
  (executionPath first first_avoids state).trans
    (executionPath second second_avoids (execute first first_avoids state))











end Monodromy.NestedContinuation

namespace Monodromy.NestedContinuation









end Monodromy.NestedContinuation


namespace Monodromy.NestedContinuation





end Monodromy.NestedContinuation


namespace Monodromy.NestedContinuation




end Monodromy.NestedContinuation


namespace Monodromy.NestedRestricted

open unitInterval

noncomputable section

def baseSet : Set ℂ := {value | value ≠ 0 ∧ value ≠ 1}
def firstSet : Set ℂ := Complex.exp ⁻¹' baseSet
def secondSet : Set ℂ := Complex.exp ⁻¹' firstSet

def firstProjection : firstSet → baseSet := baseSet.restrictPreimage Complex.exp
def secondProjection : secondSet → firstSet := firstSet.restrictPreimage Complex.exp

theorem firstCovering : IsCoveringMap firstProjection :=
  (Complex.isCoveringMapOn_exp.mono (by
    intro value valid
    exact valid.1)).isCoveringMap_restrictPreimage

theorem firstSet_nonzero {value : ℂ} (valid : value ∈ firstSet) : value ≠ 0 := by
  intro zero
  have avoids_one : Complex.exp value ≠ 1 := valid.2
  apply avoids_one
  simp [zero]









/-- The fixed admissible paths are paths in the common twice-punctured base. -/
def basePath {start finish : {value : ℂ // value ≠ 0}}
    (path : Path start finish) (avoids_one : ∀ t : I, (path t : ℂ) ≠ 1) :
    Path (⟨start.val, start.property, by simpa using avoids_one 0⟩ : baseSet)
      ⟨finish.val, finish.property, by simpa using avoids_one 1⟩ where
  toFun t := ⟨path t, (path t).property, avoids_one t⟩
  continuous_toFun := (path.continuous.subtype_val).subtype_mk _
  source' := by
    apply Subtype.ext
    exact congrArg (fun value : {value : ℂ // value ≠ 0} => (value : ℂ)) path.source
  target' := by
    apply Subtype.ext
    exact congrArg (fun value : {value : ℂ // value ≠ 0} => (value : ℂ)) path.target

end

end Monodromy.NestedRestricted


namespace Monodromy.NestedContinuation

open unitInterval

/-- The actual first lift stays in the total space of the first restricted cover. -/
theorem firstRaw_mem (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    firstRaw path state t ∈ NestedRestricted.firstSet := by
  change Complex.exp (firstRaw path state t) ≠ 0 ∧ Complex.exp (firstRaw path state t) ≠ 1
  refine ⟨Complex.exp_ne_zero _, ?_⟩
  intro one
  apply avoids t
  apply Subtype.ext
  exact (congrArg Subtype.val (congrFun (firstRaw_projects path state) t)).symm.trans one

/-- The actual second lift stays in the total space of the second restricted cover. -/
theorem secondRaw_mem (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    secondRaw path avoids state t ∈ NestedRestricted.secondSet := by
  change Complex.exp (secondRaw path avoids state t) ∈ NestedRestricted.firstSet
  rw [secondRaw_exp]
  exact firstRaw_mem path avoids state t

def lowerCurve (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    C(I, NestedRestricted.firstSet) where
  toFun t := ⟨firstRaw path state t, firstRaw_mem path avoids state t⟩
  continuous_toFun := (firstRaw path state).continuous.subtype_mk _

def upperCurve (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    C(I, NestedRestricted.secondSet) where
  toFun t := ⟨secondRaw path avoids state t, secondRaw_mem path avoids state t⟩
  continuous_toFun := (secondRaw path avoids state).continuous.subtype_mk _



end Monodromy.NestedContinuation


