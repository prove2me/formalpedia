-- Prove2me | Definitions.Def_JainCRERepetition_Cubic_allocation
-- name    : JainCRERepetition_Cubic_allocation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:27.163386+00:00
-- url     : https://prove2.me/theorems/37709d6f-1298-4b9e-a5db-d97b49e36eb0
-- title:
--   Lemmas 2.20, 2.25 and 2.26 — ordered restrictions and quantum information
-- statement:
--   An ordered register system has copied local questions, classical remote references, a remaining workspace and an optional classical record. A comparison for the product prior is constructed from a single supported matching-copy seed. For a coordinate order, the prefix, previous prefix and exposed history are explicit finite register sets. The allocation expression averages separately normalized divergence differences under the target history law.
--
--   $$\Delta_i=\mathbb E_{H_i}\bigl[D(\rho^{R_{\le i}K}_{H_i}\|\nu^{R_{\le i}K}_{H_i})-D(\rho^{R_{<i}K}_{H_i}\|\nu^{R_{<i}K}_{H_i})\bigr].$$
--
--   The comparison form of each restriction is the same seed-based map as in Definition 2.6. The module also computes classical–quantum joint states, local marginals and $I(Y:A\mid X)$ through entropy. The allocation claim is a proposition asserted by Lemma 2.25, never a hypothesis of the game model or the main theorem. Arbitrary coordinate orders include Alice's forward and Bob's reversed order after swapping the players.
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), pp. 17, 19–21, Lemmas 2.20, 2.25, 2.26; pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_registers
import Definitions.Def_JainCRERepetition_Cubic_copied

open scoped BigOperators
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

inductive AllocReg (m : ℕ)
  | xh : Fin m → AllocReg m
  | x : Fin m → AllocReg m
  | yh : Fin m → AllocReg m
  | work : AllocReg m
  | record : AllocReg m
  deriving DecidableEq, Fintype

section Allocation
variable {X Y K T : Type} [Fintype X] [Fintype Y] [Fintype K] [Fintype T]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq K] [DecidableEq T]
variable [Nonempty X] [Nonempty Y] [Nonempty K] [Nonempty T] {m : ℕ}

def allocType (X Y K T : Type) : AllocReg m → Type
  | .xh _ | .x _ => X
  | .yh _ => Y
  | .work => K
  | .record => T

instance allocFintype (r : AllocReg m) : Fintype (allocType (m := m) X Y K T r) := by
  cases r <;> simp only [allocType] <;> infer_instance
instance allocDecidable (r : AllocReg m) : DecidableEq (allocType (m := m) X Y K T r) := by
  cases r <;> simp only [allocType] <;> infer_instance
instance allocNonempty (r : AllocReg m) : Nonempty (allocType (m := m) X Y K T r) := by
  cases r <;> simp only [allocType] <;> infer_instance

def allocK : Finset (AllocReg m) := Finset.univ.image AllocReg.x ∪ {.work,.record}

def allocRefs (sites : Finset (Fin m)) : Finset (AllocReg m) :=
  sites.image AllocReg.xh ∪ sites.image AllocReg.yh

def sitesBefore (order : Fin m ≃ Fin m) (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun j => order.symm j < i

def sitesAfter (order : Fin m ≃ Fin m) (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun j => i < order.symm j

def allocHistory (order : Fin m ≃ Fin m) (i : Fin m) : Finset (AllocReg m) :=
  {.record} ∪ (sitesBefore order i).image AllocReg.yh ∪ (sitesAfter order i).image AllocReg.x

def allocThrough (order : Fin m ≃ Fin m) (i : Fin m) : Finset (AllocReg m) :=
  allocK ∪ allocRefs (insert (order i) (sitesBefore order i))

def allocBefore (order : Fin m ≃ Fin m) (i : Fin m) : Finset (AllocReg m) :=
  allocK ∪ allocRefs (sitesBefore order i)

def manyAttach (μ : Law (X × Y))
    (τ : Op (Config (allocType (m := m) X Y K T) (Finset.univ \ Finset.univ.image AllocReg.yh))) :
    Op (Config (allocType (m := m) X Y K T) Finset.univ) :=
  let V := allocType (m := m) X Y K T
  fun a b => if (∀ i : Fin m, readReg V a (.yh i) = readReg V b (.yh i)) then
    (∏ i : Fin m, (Real.sqrt (kernel μ.p (readReg V a (.x i)) (readReg V a (.yh i))) : ℂ) *
      (Real.sqrt (kernel μ.p (readReg V b (.x i)) (readReg V b (.yh i))) : ℂ)) *
    τ (restrictReg V a _) (restrictReg V b _) else 0

def ManyComparison (μ : Law (X × Y))
    (ν : Op (Config (allocType (m := m) X Y K T) (Finset.univ : Finset (AllocReg m)))) : Prop :=
  let V := allocType (m := m) X Y K T
  ∃ τ : Op (Config V (Finset.univ \ Finset.univ.image AllocReg.yh)),
    IsState τ ∧ (∀ i : Fin m, matchingOn V τ (.xh i) (.x i) (Equiv.refl X)) ∧
    (∀ i a, marginalX μ.p (readReg V a (.x i)) = 0 → τ a a = 0) ∧ ν = manyAttach μ τ

def allocationSum (order : Fin m ≃ Fin m)
    (ρ ν : Op (Config (allocType (m := m) X Y K T) (Finset.univ : Finset (AllocReg m)))) : ℝ :=
  let V := allocType (m := m) X Y K T
  ∑ i : Fin m, ∑ h : Config V (allocHistory order i),
    if 0 < recordProb V ρ (allocHistory order i) h then
      recordProb V ρ (allocHistory order i) h *
      (d (conditioned V ρ (allocHistory order i) h (allocThrough order i))
         (conditioned V ν (allocHistory order i) h (allocThrough order i)) -
       d (conditioned V ρ (allocHistory order i) h (allocBefore order i))
         (conditioned V ν (allocHistory order i) h (allocBefore order i))) else 0

/-- Exact telescoping and comparison preservation. An arbitrary coordinate ordering includes
Alice's forward order and Bob's reverse order after interchanging the alphabets. -/
def AllocationClaim (μ : Law (X × Y)) : Prop :=
  ∀ (m : ℕ) (K T : Type) [Fintype K] [Fintype T] [DecidableEq K] [DecidableEq T]
    [Nonempty K] [Nonempty T] (order : Fin m ≃ Fin m)
    (ρ ν : Op (Config (allocType (m := m) X Y K T) (Finset.univ : Finset (AllocReg m)))),
    let V := allocType (m := m) X Y K T
    IsState ρ → IsState ν → FiniteD ρ ν →
    classicalOn V ρ (Finset.univ.image AllocReg.yh) →
    classicalOn V ν (Finset.univ.image AllocReg.yh) →
    classicalOn V ρ {.record} → classicalOn V ν {.record} →
    (∀ i : Fin m, matchingOn V ρ (.xh i) (.x i) (Equiv.refl X)) →
    (∀ i : Fin m, matchingOn V ν (.xh i) (.x i) (Equiv.refl X)) →
      allocationSum order ρ ν = d ρ ν - d (reduced V ρ allocK) (reduced V ν allocK) ∧
      (ManyComparison μ ν → ∀ i h, 0 < recordProb V ρ (allocHistory order i) h →
        RegComparison V (.xh (order i)) (.x (order i)) (.yh (order i)) (Equiv.refl X) μ
          (conditioned V ν (allocHistory order i) h (allocThrough order i)))

end Allocation

section CQ
variable {X Y A : Type} [Fintype X] [Fintype Y] [Fintype A]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A]

def cqXY (q : X × Y → ℝ) (ρ : X → Y → Op A) : Op ((X × Y) × A) :=
  cq q (fun z => ρ z.1 z.2)

def cqXA (q : X × Y → ℝ) (ρ : X → Y → Op A) : Op (X × A) :=
  fun a b => if a.1 = b.1 then ∑ y, (q (a.1,y) : ℂ) * ρ a.1 y a.2 b.2 else 0

def conditionalInfo (q : X × Y → ℝ) (ρ : X → Y → Op A) : ℝ :=
  entropy (cqXA q ρ) + entropy (diagonal q) - entropy (diagonal (marginalX q)) - entropy (cqXY q ρ)

def informationRHS (μ : Law (X × Y)) (ρ : Op (AliceIndex X Y A)) : ℝ :=
  let χ : Op ((X × Y) × A) := fun a b =>
    ∑ xh, ρ ((xh,a.1.2),(a.1.1,a.2)) ((xh,b.1.2),(b.1.1,b.2))
  let q : X × Y → ℝ := fun xy => ∑ a, (χ (xy,a) (xy,a)).re
  let XA := trL ρ
  entropy XA + entropy (diagonal q) - entropy (diagonal (marginalX q)) - entropy χ +
    classicald q (fun xy => marginalX q xy.1 * kernel μ.p xy.1 xy.2)

def copyMatching (ρ : Op (AliceIndex X Y A)) : Prop :=
  ∀ a b, (a.1.1 ≠ a.2.1 ∨ b.1.1 ≠ b.2.1) → ρ a b = 0

def classicalRemote (ρ : Op (AliceIndex X Y A)) : Prop :=
  ∀ a b, a.1.2 ≠ b.1.2 → ρ a b = 0

def isDiagonal {I : Type} (ρ : Op I) : Prop := ∀ a b, a ≠ b → ρ a b = 0

end CQ
end JainCRERepetition.Cubic


