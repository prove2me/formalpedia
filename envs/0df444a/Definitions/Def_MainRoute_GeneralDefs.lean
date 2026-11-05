-- Prove2me | Definitions.Def_MainRoute_GeneralDefs
-- name    : MainRoute_GeneralDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:57:30.31461+00:00
-- url     : https://prove2.me/theorems/3273dba9-3941-41e2-8ac7-26314926eb38
-- title:
--   General Defs
-- statement:
--   Definitions and structural lemmas for General Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/GeneralDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_Defs
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace MainRoute
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)
structure RouteOn {Idx : Type} [Enc Idx] (S : Solver Idx) {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) (num : U × U → ℕ × ℕ) (fm : List Bool × U → List Bool) (em : List Bool → ℕ) (n₁ : ℕ) : Prop where
  /-- (3) Theorem D (a): EVERY machine that computes the function of Steps 1 to 5 on S has the
      conclusion of Theorem D (a) for this sequence -/
  da : ∀ (Ma : TM2ComputableAux Bool Bool) (qa : ℕ), Computes Ma (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) qa → ∃ Ca : ℕ, ThmVariablesAFor S Q Ma Ca
  /-- (4) Step 6, from the BODY of Theorem D (a): for EVERY machine Ma with the conclusion of
      Theorem D (a) for this sequence and EVERY machine Mb that tries all assignments, EVERY machine
      that chooses between them as Step 6 says meets the bound of Theorem D (b) -/
  variablesBFromTheBody : ∀ (Ma : TM2ComputableAux Bool Bool) (Ca : ℕ), ThmVariablesAFor S Q Ma Ca → ∀ (Mb : TM2ComputableAux Bool Bool) (cb : ℕ), TriesAllWithin Mb cb →
    ∀ (pre : List Bool → List Bool) (test : List Bool → Bool), RewritesAtWidthOr3 pre → TestsTheMainRegime (S.K (Q.idx 0)) test →
      ∀ (M₂ : TM2ComputableAux Bool Bool) (q₂ : ℕ), Chooses Ma Mb test pre id id id M₂ q₂ → ∃ C₂ : ℕ, ThmVariablesBFor M₂ C₂
  /-- EVERY machine that computes exhaustive counting tries all assignments within 2^{cb·n}·n^{cb·k}
  steps, for some cb that depends on the machine -/
  tries : ∀ (Mb : TM2ComputableAux Bool Bool) (qb : ℕ), Computes Mb exhaust (fun x => (fmlOf x).1.length) qb → ∃ cb : ℕ, TriesAllWithin Mb cb
  /-- (4) Step 6, for the named function: EVERY machine made as Step 6 says meets the bound of
      Theorem D (b) -/
  db : ∀ M₂ : TM2ComputableAux Bool Bool, ChosenAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) (S.K (Q.idx 0)) M₂ → ∃ C₂ : ℕ, ThmVariablesBFor M₂ C₂
  /-- (6) Corollary 11, from the BODIES of Theorem A (c) and Theorem D (b): for EVERY machine M₁
      that meets the bound in m and EVERY machine M₂ that meets the bound of Theorem D (b), EVERY
      machine that runs them in alternation behind a renaming meets the bound of Corollary 11 -/
  cor : ∀ ren : List Bool → List Bool, RenamesTheVariablesThatOccur ren → ∀ (M₁ : TM2ComputableAux Bool Bool) (C₁ : ℕ), MeetsBoundInM M₁ C₁ → ∀ (M₂ : TM2ComputableAux Bool Bool) (C₂ : ℕ), ThmVariablesBFor M₂ C₂ →
    ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Alternates M₁ M₂ ren ren id id N q → ∃ C : ℕ, MeetsMinBound N C
  /-- (6), (7) Corollary 11, which is the Main Theorem, for the named function and fm: EVERY machine
  assembled as printed meets the bound of Corollary 11 and that of Theorem 1 on the compact code -/
  main : ∀ N : TM2ComputableAux Bool Bool, AssembledAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) fm em (S.K (Q.idx 0)) id N →
    ∃ C : ℕ, MeetsMinBound N C ∧ CountsCompactKCNFWithinMinBound N C
  /-- the same for deciding, with `someBit` (“some bit is 1”) after either machine -/
  decides : ∀ N : TM2ComputableAux Bool Bool, AssembledAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) fm em (S.K (Q.idx 0)) someBit N →
    ∃ C : ℕ, DecidesWithinMinBound N C
  /-- there IS a machine built as printed, for counting and for deciding: finite alphabets,
  polynomial-time front ends and test, and the named computations `choose` and `alt` carried out -/
  exist : (∃ N : TM2ComputableAux Bool Bool, BuiltAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) fm em (S.K (Q.idx 0)) id N) ∧
    ∃ N : TM2ComputableAux Bool Bool, BuiltAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) fm em (S.K (Q.idx 0)) someBit N
def RouteOnEverySolver : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ num : U × U → ℕ × ℕ, NumberBetween S Q num →
    ∃ n₀ : ℕ, ∀ a : ℕ, (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) →
      ∀ (fm : List Bool × U → List Bool) (em : List Bool → ℕ), (∃ (M : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Computes M fm em q) →
        (∀ (M : TM2ComputableAux Bool Bool) (q : ℕ), Computes M fm em q → ∃ C : ℕ, MeetsBoundInM M C) →
          ∀ n₁ : ℕ, n₀ ≤ n₁ → RouteOn S Q num fm em n₁
def BoundInMOnEverySolver : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ a : ℕ, (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) →
    (∃ (M : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Computes M (AM S Q.pick) (eM S Q.pick) q) ∧
    ∀ (M : TM2ComputableAux Bool Bool) (q : ℕ), Computes M (AM S Q.pick) (eM S Q.pick) q → ∃ C : ℕ, MeetsBoundInM M C
def BothBoundsOnEverySolver : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ num : U × U → ℕ × ℕ, NumberBetween S Q num →
    ∃ n₀ : ℕ, ∀ a : ℕ, (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) →
      (∀ (M₁ : TM2ComputableAux Bool Bool) (q₁ : ℕ), Computes M₁ (AM S Q.pick) (eM S Q.pick) q₁ → ∃ C₁ : ℕ, MeetsBoundInM M₁ C₁) ∧
      ∀ n₁ : ℕ, n₀ ≤ n₁ → RouteOn S Q num (AM S Q.pick) (eM S Q.pick) n₁
end MainRoute


