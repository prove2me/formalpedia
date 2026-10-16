-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Computing
-- name    : OAI_MathematicalPhysics_SheetFlows_Computing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:23:58.162329+00:00
-- url     : https://prove2.me/theorems/ba08e829-89f5-4a6a-8593-2ae03aaaa004
-- title:
--   A primitive recursive encoding of the rational numbers
-- statement:
--   This file supplies the computability facts about integers and rationals needed to use rational numbers as inputs and outputs of partial recursive functions. Natural numbers, integers, pairs and disjoint sums carry their standard encodings into $\mathbb{N}$, and a function between such encoded types is *primitive recursive* if the induced function on codes is.
--
--   1. **Greatest common divisor by bounded search.** For $a,b\in\mathbb{N}$, the largest $d\le a+b$ dividing both $a$ and $b$ is their greatest common divisor:
--   $$\max\{d\in\mathbb{N}:\ d\le a+b,\ d\mid a,\ d\mid b\}=\gcd(a,b)$$
--   (both sides are $0$ when $a=b=0$). Consequently divisibility on $\mathbb{N}$ is a primitive recursive relation and $\gcd:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ is a primitive recursive function.
--   2. **Integers.** The encoding of integers sends $n\ge0$ to $2n$ and $-(n+1)$ to $2n+1$. The map sending $n\ge0$ to the left copy of $n$ and $-(n+1)$ to the right copy of $n$ in $\mathbb{N}\sqcup\mathbb{N}$ is primitive recursive; hence a definition by cases on the sign of a primitive recursive integer-valued function, with primitive recursive branches, is primitive recursive, and the absolute value $\mathbb{Z}\to\mathbb{N}$, $n\mapsto|n|$, is primitive recursive.
--   3. **Valid rational pairs.** A pair $(n,d)\in\mathbb{Z}\times\mathbb{N}$ is *valid* if $d>0$ and $\gcd(|n|,d)=1$. This predicate is decidable and primitive recursive, so the set of valid pairs inherits a primitive recursive encoding as a subset of $\mathbb{Z}\times\mathbb{N}$.
--   4. **Rationals.** The bijection $q\mapsto\bigl(\mathrm{num}(q),\mathrm{den}(q)\bigr)$ from $\mathbb{Q}$ onto the valid pairs (numerator and denominator in lowest terms, with inverse $(n,d)\mapsto n/d$) transports this encoding to $\mathbb{Q}$, making $\mathbb{Q}$ a primitively encodable type.
--
--   With this encoding, rational constants, rational coordinates of points and rational balls can be read from and produced by codes of partial recursive functions. This is the language in which the effectivity statements of the construction are expressed and proved: approximations of the forcing field and of its derivatives to any rational accuracy, computed by a fixed partial recursive procedure.
--
--   **Formalization Note** The declarations are `gcd_findGreatest` (stated with `Nat.findGreatest`), `nat_dvd` (`PrimrecRel`), `nat_gcd` (`Primrec₂`), the simp lemmas `encode_int_ofNat` and `encode_int_negSucc`, `intToSum` with `intToSum_pr`, `int_cases`, `int_natAbs`, `ratValid` with a `DecidablePred` instance and `ratValid_pr` (`PrimrecPred`), the instance `ratPairPrimcodable` (via `Primcodable.subtype`), the equivalence `ratEquiv`, and the instance `ratPrimcodable : Primcodable ℚ` (via `Primcodable.ofEquiv`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Computing.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Computing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SolenoidalSheetPrograms mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalBalls

namespace OAI

/-! SheetFlows computing. -/

section
open Encodable
namespace Solenoidal.Computing

theorem gcd_findGreatest (a b : ℕ) :
    Nat.findGreatest (fun d => d ∣ a ∧ d ∣ b) (a+b) = Nat.gcd a b := by
  by_cases h : a+b=0
  · have ha : a=0 := by omega
    have hb : b=0 := by omega
    simp [ha,hb]
  have hg : 0 < Nat.gcd a b := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simpa using (show 0 < b by omega)
    · exact Nat.gcd_pos_of_pos_left b ha
  apply le_antisymm
  · have hh := Nat.findGreatest_spec (P := fun d => d ∣ a ∧ d ∣ b)
      (show 1 ≤ a+b by omega) (show 1 ∣ a ∧ 1 ∣ b from ⟨one_dvd _,one_dvd _⟩)
    exact Nat.le_of_dvd hg (Nat.dvd_gcd hh.1 hh.2)
  · apply Nat.le_findGreatest
    · rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · exact (Nat.gcd_le_left b ha).trans (Nat.le_add_right a b)
    · exact ⟨Nat.gcd_dvd_left _ _,Nat.gcd_dvd_right _ _⟩

theorem nat_dvd : PrimrecRel ((· ∣ ·) : ℕ → ℕ → Prop) :=
  (Primrec.eq.comp (Primrec.nat_mod.comp .snd .fst) (.const 0)).of_eq
    (fun _ => Nat.dvd_iff_mod_eq_zero.symm)

theorem nat_gcd : Primrec₂ Nat.gcd := by
  refine (Primrec.nat_findGreatest Primrec.nat_add
    (((nat_dvd.comp .snd (Primrec.fst.comp .fst)).and
      (nat_dvd.comp .snd (Primrec.snd.comp .fst))).primrecRel)).of_eq ?_
  intro p
  exact gcd_findGreatest p.1 p.2

@[simp] theorem encode_int_ofNat (n : ℕ) : encode (Int.ofNat n) = 2*n := rfl
@[simp] theorem encode_int_negSucc (n : ℕ) : encode (Int.negSucc n) = 2*n+1 := rfl

def intToSum : ℤ → ℕ ⊕ ℕ := fun z => Int.casesOn z Sum.inl Sum.inr

theorem intToSum_pr : Primrec intToSum :=
  Primrec.encode_iff.mp (Primrec.encode.of_eq (by intro z; cases z <;> rfl))

theorem int_cases {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → ℤ} {g h : α → ℕ → β} (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec (fun a => Int.casesOn (motive := fun _ => β) (f a) (g a) (h a)) :=
  (Primrec.sumCasesOn (intToSum_pr.comp hf) hg hh).of_eq
    (fun a => by cases f a <;> rfl)

theorem int_natAbs : Primrec Int.natAbs :=
  (int_cases .id .right (Primrec.succ.comp₂ .right)).of_eq
    (fun z => by cases z <;> rfl)

def ratValid (p : ℤ×ℕ) : Prop := 0 < p.2 ∧ p.1.natAbs.Coprime p.2

instance : DecidablePred ratValid := fun p => inferInstanceAs
  (Decidable (0 < p.2 ∧ p.1.natAbs.Coprime p.2))

theorem ratValid_pr : PrimrecPred ratValid :=
  (Primrec.nat_lt.comp (.const 0) .snd).and
    ((Primrec.eq.comp (nat_gcd.comp (int_natAbs.comp .fst) .snd) (.const 1)).of_eq
      (fun _ => Iff.rfl))

instance ratPairPrimcodable : Primcodable {p : ℤ×ℕ // ratValid p} :=
  Primcodable.subtype ratValid_pr

def ratEquiv : ℚ ≃ {p : ℤ×ℕ // ratValid p} where
  toFun q := ⟨(q.num,q.den),q.den_pos,q.reduced⟩
  invFun p := ⟨p.1.1,p.1.2,ne_of_gt p.2.1,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance ratPrimcodable : Primcodable ℚ := Primcodable.ofEquiv _ ratEquiv

end Solenoidal.Computing
end

section
open Encodable
open scoped BigOperators
namespace Solenoidal.Computing

end Solenoidal.Computing
end

end OAI


