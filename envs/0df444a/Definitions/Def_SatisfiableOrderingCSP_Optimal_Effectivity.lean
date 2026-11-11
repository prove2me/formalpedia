-- Prove2me | Definitions.Def_SatisfiableOrderingCSP_Optimal_Effectivity
-- name    : SatisfiableOrderingCSP_Optimal_Effectivity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:46:44.306759+00:00
-- url     : https://prove2.me/theorems/aae04eb4-91cf-4364-8b8a-deb2e0e2671e
-- title:
--   Finite operational interfaces for preprocessing and LP characterization
-- statement:
--   Scheme inputs contain a finite language truth-table encoding and a real accuracy parameter. Outputs contain explicit finite bit strings for a rational value and rational mixture. Model tables enumerate tuples lexicographically, with singletons first. Effective LP characterization asks for two fixed rational-constant exact-arithmetic programs: one turns any valid pair of canonical relaxed orders into a finite basic LP solution, and the other reads any finite real basic LP table and returns a pair of canonical relaxed orders. Every claimed output is tied to a finite operational run from zero work memory. This predicate asserts neither existence nor correctness by definition; Theorem 4.8 supplies them as its conclusion.
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission (not an acceptance claim), sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc; citation_basis: published; Theorems 4.4, 4.8 and Appendix A.6; pp. 18, 20–23, 62–63 (PDF 21, 23–26, 65–66)

import Definitions.Def_SatisfiableOrderingCSP_Optimal_LocalModel
import Definitions.Def_SatisfiableOrderingCSP_Optimal_Computation

open scoped BigOperators

namespace SatisfiableOrderingCSP.Optimal
noncomputable section
attribute [local instance] Classical.propDecidable
open NearLinearRSP.TwoResources

def OutputBits (s : RAMState) (bits : List Bool) : Prop :=
  s.nm 0 = bits.length ∧ ∀ i : Fin bits.length,
    s.nm (i.val + 1) = (if bits[i] then 1 else 0)

def SchemeInput (code : List Bool) (ε : ℝ) : RAMInput :=
  ⟨fun i => if i = 0 then code.length else
    if code[i-1]?.getD false then 1 else 0,
    fun i => if i = 0 then ε else 0⟩

/-- Deterministic lexicographic tuple enumeration is part of the interface. -/
def tuples (k q : ℕ) : List (List ℕ) :=
  match k with
  | 0 => [[]]
  | k+1 => (List.range q).flatMap fun a => (tuples k q).map (List.cons a)

def ModelTable {n q : ℕ} {S : Scopes n} (M : LocalModel S q) : List ℝ :=
  (List.finRange n).flatMap (fun v => List.ofFn (M.singleton v)) ++
  (List.finRange S.count).flatMap fun c =>
    (tuples (S.arity c) q).map fun l =>
      ∑ x, if List.ofFn (fun i => (x i).val) = l then M.joint c x else 0

def LPInput (I : Instance) {q : ℕ} (M : LocalModel I.scopes q) : RAMInput :=
  ⟨fun i => (q :: I.data)[i]?.getD 0, fun i => (ModelTable M)[i]?.getD 0⟩

def OrdersInput (I : Instance) (L R : Order I.n) : RAMInput :=
  ⟨fun i => (I.data ++ List.ofFn (fun j => (L j).val) ++
    List.ofFn (fun j => (R j).val))[i]?.getD 0, fun _ => 0⟩

def OutputModel (s : RAMState) {n q : ℕ} {S : Scopes n} (M : LocalModel S q) : Prop :=
  s.nm 0 = q ∧ ∀ i : Fin (ModelTable M).length, s.rm i.val = (ModelTable M)[i]

def EffectiveLPCharacterization : Prop :=
  ∃ P Q : Program, ArithmeticProgram P ∧ ArithmeticProgram Q ∧
    (∀ (I : Instance) (L R : Order I.n), I.RelaxedOrders L R →
      ∃ t s, Execution P (OrdersInput I L R) initialState s t ∧
        ∃ (q : ℕ) (M : LocalModel I.scopes q), BasicLP I M ∧ OutputModel s M) ∧
    (∀ (I : Instance) (q : ℕ) (M : LocalModel I.scopes q), BasicLP I M →
      ∃ t s, Execution Q (LPInput I M) initialState s t ∧
        ∃ L R : Order I.n, I.RelaxedOrders L R ∧
          (∀ i, s.nm i.val = (L i).val) ∧ (∀ i, s.nm (I.n + i.val) = (R i).val))

end
end SatisfiableOrderingCSP.Optimal


