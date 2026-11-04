-- Prove2me | Definitions.Def_RyserOddSupport
-- name    : RyserOddSupport
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-03T23:18:56.207061+00:00
-- url     : https://prove2.me/theorems/aec716e6-8017-4c59-acc5-faebe5d94d4c
-- title:
--   Supporting definitions for the odd-degree Ryser counterexample
-- statement:
--   This module collects OpenAI's definitions from the Ryser development that are needed to state the uniform incidence bound, the line-cover theorem after random deletions, and the compatible-translate selection theorem. It builds on the published module `RyserOddExtensions`.
--
--   **Plane geometry over a field $F$.** A point is an element of $F^2$. A direction is an element of $F\cup\{\infty\}$, encoded as `Option F`. An affine line is a pair $(d,c)$ of a direction and an intercept, with projection $\pi_\infty(x,y)=x$ and $\pi_a(x,y)=y-ax$, and a point $p$ is incident to $(d,c)$ when $\pi_d(p)=c$. A projective point is a point or a direction. A projective line is an affine line or the line at infinity. `ProjectiveIncidence` is the usual incidence relation of $\mathbb P^2(F)$.
--
--   **Incidence counting.** For a relation $R$, `incidenceCount` is $\sum_{p\in P}|\{\ell\in L : R(p,\ell)\}|$. The exponent `savingExponent` equals $\kappa=10^{-10}$, and `incidenceThreshold` is a threshold $Q$ chosen by Classical.choice so that the explicit numerical inequalities `LargeEnough` hold for all $q\ge Q$. The predicate `SmallProperSubfields` says that every proper subfield $M$ of $F$ satisfies $|M|^3\le |F|$.
--
--   **Finite probability and deletion processes.** `FiniteLaw` is a probability distribution on a finite type, with `prob`, product law `pi` and `uniform` law. For a family of shapes, an outcome is a list of at most $D$ shapes, and `survivors` is the set of points not deleted by any trial, optionally ignoring some shapes. `DeletionProcess F D δ` packages the hypotheses of Lemma 3.2 of the paper: at most $D|F|^D$ shapes of size at most $D|F|$, each meeting any different line in at most $D$ points; at most $D|F|$ independent trials; per-trial point deletion probability at most $D/|F|$; a uniform survival probability that is at least $\delta$; and exact-line occurrence probabilities summing to at most $D/|F|$ for each line. `GoodLineCover δ ρ` is the conclusion of that lemma for a realization.
--
--   **Selection.** `Data F n` records finite point sets $W_i$ and direction sets $D_i$. `Conflict` says that translates $b+W_i$ and $b'+W_j$ have two points joined by a direction of $D_i\cup D_j$. `Bounded D` is the size and multiplicity hypothesis of Theorem 4.1 of the paper. `poolLaw` is the law of independent uniform shifts, and `HasCompatibleChoice` asserts that one shift can be chosen per index with no conflicts.
--
--   The module also contains compatibility restatements `ite_eq_left`, `ite_eq_right`, `dite_eq_left` and `dite_eq_right` of `if_pos`, `if_neg`, `dif_pos` and `dif_neg`, which are absent from this Mathlib, and the instances `Decidable` for incidence, `Fintype` for the extension field and coset index. These definitions are OpenAI's, carved from the source above by deleting unneeded declarations and ported to Lean 4.33.1 and this Mathlib.
-- source:
--   OpenAI, A counterexample to Ryser's covering conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Ryser/ (Geometry/Basic.lean, LineCover/DeletionDefinitions.lean, LineCover/Definitions.lean, LineCover/Process.lean, Probability/Finite.lean, Field/Extension.lean, Incidence/PruningCore.lean, Incidence/Parameters.lean, Incidence/Uniform.lean, Selection/Definitions.lean, Selection/PoolLaw.lean, Construction/CosetIndex.lean)

import Mathlib
import Definitions.Def_RyserOddExtensions

set_option linter.all false

section
namespace OAI

theorem ite_eq_left {α : Sort*} {c : Prop} {_ : Decidable c} {a b : α} (h : c) : ite c a b = a := if_pos h
theorem ite_eq_right {α : Sort*} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) : ite c a b = b := if_neg h
theorem dite_eq_left {α : Sort*} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort*} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample

abbrev Point (F : Type*) := F × F
abbrev Direction (F : Type*) := Option F
abbrev AffineLine (F : Type*) := Direction F × F
abbrev ProjectivePoint (F : Type*) := Point F ⊕ Direction F
abbrev ProjectiveLine (F : Type*) := Option (AffineLine F)

variable {F : Type*} [Field F]

def projection : Direction F → Point F → F
  | none, p => p.1
  | some a, p => p.2 - a * p.1

def Incidence (p : Point F) (l : AffineLine F) : Prop :=
  projection l.1 p = l.2

instance [DecidableEq F] (p : Point F) (l : AffineLine F) :
    Decidable (Incidence p l) :=
  inferInstanceAs (Decidable (projection l.1 p = l.2))

def ProjectiveIncidence : ProjectivePoint F → ProjectiveLine F → Prop
  | Sum.inl p, some l => Incidence p l
  | Sum.inr d, some l => d = l.1
  | Sum.inl _, none => False
  | Sum.inr _, none => True

instance [DecidableEq F] (p : ProjectivePoint F) (l : ProjectiveLine F) :
    Decidable (ProjectiveIncidence p l) := by
  cases p <;> cases l <;> simp only [ProjectiveIncidence] <;> infer_instance

section Finite
variable [Fintype F] [DecidableEq F]

def linePoints (l : AffineLine F) : Finset (Point F) :=
  Finset.univ.filter fun p => Incidence p l

end Finite
end RyserCoveringCounterexample

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [DecidableEq P]

abbrev Outcome (shapes : Finset (Finset P)) (D : ℕ) :=
  {A : Finset ↥shapes // A.card ≤ D}

variable {shapes : Finset (Finset P)} {D n : ℕ}

def deleted (ignore : Finset (Finset P)) (a : Outcome shapes D) : Finset P :=
  (a.val.filter (fun L => L.val ∉ ignore)).biUnion Subtype.val

variable [instFintypeP : Fintype P]

def survivors (ignore : Finset (Finset P))
    (ω : Fin n → Outcome shapes D) : Finset P :=
  Finset.univ \ Finset.univ.biUnion (fun i => deleted ignore (ω i))

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open scoped Classical

variable {F : Type*} [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

def SparseShapes (shapes : Finset (Finset (Point F))) (D : ℕ) : Prop :=
  ∀ S ∈ shapes, ∀ l : AffineLine F, S ≠ linePoints l →
    (S ∩ linePoints l).card ≤ D

def coverPencil (L : Finset (AffineLine F)) (p : ProjectivePoint F) :
    Finset (AffineLine F) :=
  L.filter fun l => ProjectiveIncidence p (some l)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw

def prob {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if P ω then μ.weight ω else 0

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def pi {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (μ : ∀ i, FiniteLaw (A i)) : FiniteLaw (∀ i, A i) := by
  classical
  exact {
    weight := fun ω => ∏ i, (μ i).weight (ω i)
    nonneg := fun ω => Finset.prod_nonneg fun i _ => (μ i).nonneg (ω i)
    total := by
      rw [← Fintype.prod_sum (fun i a => (μ i).weight a)]
      simp_rw [(μ _).total]
      simp }

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [hN]

end FiniteLaw

end RyserCoveringCounterexample

end

end OAI
end

section
namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

structure DeletionProcess (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (D : ℕ) (δ : ℝ) where
  shapes : Finset (Finset (Point F))
  shapeCount : shapes.card ≤ D * Fintype.card F ^ D
  shapeSize : ∀ S ∈ shapes, S.card ≤ D * Fintype.card F
  sparse : SparseShapes shapes D
  trialsCount : ℕ
  trials : Fin trialsCount → FiniteLaw (Outcome shapes D)
  trialsCount_le : trialsCount ≤ D * Fintype.card F
  pointCap : ∀ i x,
    (trials i).prob (fun a => x ∈ deleted ∅ a) ≤ (D : ℝ) / Fintype.card F
  survival : ℝ
  survivalLower : δ ≤ survival
  uniformSurvival : ∀ x,
    (FiniteLaw.pi trials).prob (fun ω => x ∈ survivors ∅ ω) = survival
  lineCap : ∀ l : AffineLine F,
    (∑ i, (trials i).prob (fun a => ∃ S ∈ a.val, S.val = linePoints l)) ≤
      (D : ℝ) / Fintype.card F

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n : ℕ}

def GoodLineCover (δ ρ : ℝ) (ω : Fin n → Outcome shapes D) : Prop :=
  (∀ l : AffineLine F,
    δ * Fintype.card F / 2 ≤
      ((survivors {linePoints l} ω ∩ linePoints l).card : ℝ)) ∧
  (∀ L : Finset (AffineLine F), L.card ≤ Fintype.card F →
    (survivors ∅ ω \ L.biUnion linePoints).card ≤ 2 * Fintype.card F →
    ∃ p : ProjectivePoint F,
      (1 - ρ) * Fintype.card F ≤ ((coverPencil L p).card : ℝ))

namespace DeletionProcess

variable {δ : ℝ} (process : DeletionProcess F D δ)

abbrev Config := Fin process.trialsCount → Outcome process.shapes D

def law : FiniteLaw process.Config := FiniteLaw.pi process.trials

end DeletionProcess
end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample

abbrev ExtensionField (p n : ℕ) [Fact p.Prime] := GaloisField p n

noncomputable instance extensionFieldFintype (p n : ℕ) [Fact p.Prime] :
    Fintype (ExtensionField p n) := Fintype.ofFinite _

end RyserCoveringCounterexample

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Incidence

variable {Pt Ln : Type*} [instDecidableEqPt : DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

def leftDegree (R : Pt → Ln → Prop) (L : Finset Ln) (p : Pt) : ℕ := by
  classical
  exact (L.filter (R p)).card

def incidenceCount (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln) : ℕ :=
  ∑ p ∈ P, leftDegree R L p

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
open Filter Topology

def savingExponent : ℝ := 1 / 10000000000
def witnessConstant : ℝ := 1 / (9 * 2 ^ 57)
def graphScaleConstant : ℝ := 9 * 2 ^ 58
def densityScale (q : ℝ) : ℝ := q ^ savingExponent
def graphScale (U : ℝ) : ℝ := graphScaleConstant * U ^ 39
def expansionScale (V : ℝ) : ℝ := 2 ^ 23 * V ^ 24

@[simp] theorem savingExponent_pos : 0 < savingExponent := by
  norm_num [savingExponent]

theorem scaled_power_identity (A U : ℝ) (a b c : ℕ) :
    A * U ^ a * (graphScale U) ^ b * (expansionScale (graphScale U)) ^ c =
      (A * graphScaleConstant ^ b * (2 ^ 23 * graphScaleConstant ^ 24) ^ c) *
        U ^ (a + 39 * b + 936 * c) := by
  simp only [graphScale, expansionScale, mul_pow, pow_add, pow_mul]
  rw [show (936 : ℕ) = 39 * 24 from rfl, pow_mul]
  ring

theorem eventually_coefficient_density_power_lt_sqrt
    (A : ℝ) (m : ℕ) (hm : savingExponent * m < 1 / 2) :
    ∀ᶠ q : ℝ in atTop, A * densityScale q ^ m < Real.sqrt q := by
  have hgap : 0 < (1 / 2 : ℝ) - savingExponent * m := sub_pos.mpr hm
  have hgrow := (tendsto_rpow_atTop hgap).eventually_gt_atTop A
  filter_upwards [eventually_gt_atTop (0 : ℝ), hgrow] with q hq hbound
  have hpow : 0 < q ^ (savingExponent * m) := Real.rpow_pos_of_pos hq _
  have hmul := mul_lt_mul_of_pos_right hbound hpow
  have hid : q ^ ((1 / 2 : ℝ) - savingExponent * m) *
      q ^ (savingExponent * m) = Real.sqrt q := by
    rw [← Real.rpow_add hq, sub_add_cancel, Real.sqrt_eq_rpow]
  rw [hid] at hmul
  simpa only [densityScale, Real.rpow_mul_natCast hq.le] using hmul

theorem eventually_scaled_powers_lt_sqrt (A : ℝ) (a b c : ℕ)
    (hExp : savingExponent * (a + 39 * b + 936 * c : ℕ) < 1 / 2) :
    ∀ᶠ q : ℝ in atTop,
      A * densityScale q ^ a * (graphScale (densityScale q)) ^ b *
        (expansionScale (graphScale (densityScale q))) ^ c < Real.sqrt q := by
  have h := eventually_coefficient_density_power_lt_sqrt
    (A * graphScaleConstant ^ b * (2 ^ 23 * graphScaleConstant ^ 24) ^ c)
    (a + 39 * b + 936 * c) hExp
  filter_upwards [h] with q hq
  simpa only [scaled_power_identity] using hq

def LargeEnough (q : ℝ) : Prop :=
  let U := densityScale q
  let V := graphScale U
  let K := expansionScale V
  0 < q ∧ 2 ≤ U ∧
    16 * U ^ 2 ≤ Real.sqrt q ∧
    4096 * U ^ 7 ≤ Real.sqrt q ∧
    (96 / witnessConstant) * U ^ 42 ≤ Real.sqrt q ∧
    32 * V ^ 2 * K ^ 127942 < 3 * Real.sqrt q ∧
    4096 * V ^ 6 * K ^ 3 < 27 * Real.sqrt q ∧
    2 * K ^ 527 * V ≤ Real.sqrt q

theorem eventually_largeEnough : ∀ᶠ q : ℝ in atTop, LargeEnough q := by
  have hU := (tendsto_rpow_atTop savingExponent_pos).eventually_ge_atTop 2
  have h2 := eventually_scaled_powers_lt_sqrt 16 2 0 0 (by norm_num [savingExponent])
  have h7 := eventually_scaled_powers_lt_sqrt 4096 7 0 0 (by norm_num [savingExponent])
  have h42 := eventually_scaled_powers_lt_sqrt (96 / witnessConstant) 42 0 0
    (by norm_num [savingExponent])
  have hfirst := eventually_scaled_powers_lt_sqrt (32 / 3) 0 2 127942
    (by norm_num [savingExponent])
  have hsecond := eventually_scaled_powers_lt_sqrt (4096 / 27) 0 6 3
    (by norm_num [savingExponent])
  have hthird := eventually_scaled_powers_lt_sqrt 2 0 1 527
    (by norm_num [savingExponent])
  filter_upwards [eventually_gt_atTop (0 : ℝ), hU, h2, h7, h42,
    hfirst, hsecond, hthird] with q hq hu h2q h7q h42q hf hs ht
  simp only [pow_zero, pow_one, mul_one] at h2q h7q h42q hf hs ht
  refine ⟨hq, hu, h2q.le, h7q.le, h42q.le, ?_, ?_, ?_⟩
  · nlinarith only [hf]
  · nlinarith only [hs]
  · have heq : 2 * expansionScale (graphScale (densityScale q)) ^ 527 *
        graphScale (densityScale q) =
      2 * graphScale (densityScale q) * expansionScale (graphScale (densityScale q)) ^ 527 := by
        ring
    rw [heq]
    exact ht.le

theorem exists_threshold_largeEnough :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → LargeEnough (q : ℝ) := by
  have h : ∀ᶠ q : ℕ in atTop, LargeEnough (q : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually eventually_largeEnough
  exact eventually_atTop.mp h

def incidenceThreshold : ℕ := Classical.choose exists_threshold_largeEnough

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section

def SmallProperSubfields (F : Type*) [Field F] [Fintype F] : Prop :=
  ∀ M : Subfield F, M ≠ ⊤ → Nat.card M ^ 3 ≤ Fintype.card F

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

structure Data (F : Type*) [Field F] (n : ℕ) where
  W : Fin n → Finset (Point F)
  dirs : Fin n → Finset (Direction F)

abbrev Position (n K : ℕ) := Fin n × Fin K
abbrev Pool (F : Type*) (n K : ℕ) := Position n K → Point F

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F] {n K : ℕ}

def Conflict (data : Data F n) (i j : Fin n) (b b' : Point F) : Prop :=
  ∃ u ∈ data.W i, ∃ v ∈ data.W j, ∃ d ∈ data.dirs i ∪ data.dirs j,
    projection d ((b + u) - (b' + v)) = 0

def HasCompatibleChoice (data : Data F n) (pool : Pool F n K) : Prop :=
  ∃ choice : Fin n → Fin K, ∀ i j, i ≠ j →
    ¬ Conflict data i j (pool (i, choice i)) (pool (j, choice j))

section Finite
variable [Fintype F]

def Bounded (D : ℕ) (data : Data F n) : Prop :=
  n ≤ D * Fintype.card F ∧
    (∀ i, (data.W i).card ≤ D) ∧
    (∀ i, (data.dirs i).card ≤ D) ∧
    ∀ d, (Finset.univ.filter fun i => d ∈ data.dirs i).card ≤ D

end Finite
end RyserCoveringCounterexample.Selection

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]

def embeddedUnits (σ : k →+* F) : kˣ →* Fˣ := Units.map σ.toMonoidHom

def smallUnitSubgroup (σ : k →+* F) : Subgroup Fˣ := (embeddedUnits σ).range

abbrev CosetIndex (σ : k →+* F) := Fˣ ⧸ smallUnitSubgroup σ

section Finite

variable [instFintypek : Fintype k] [Fintype F]

instance (σ : k →+* F) : Fintype (CosetIndex σ) := Fintype.ofFinite _

end Finite

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Selection

variable (F : Type*) [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F] (n K : ℕ)

noncomputable def poolLaw : FiniteLaw (Pool F n K) :=
  FiniteLaw.pi (fun _ : Position n K => FiniteLaw.uniform (Point F))

variable {F n K}

end RyserCoveringCounterexample.Selection

end OAI
end


