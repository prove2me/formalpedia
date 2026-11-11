-- Prove2me | Definitions.Def_DistLTLSynth_Char_Consensus
-- name    : DistLTLSynth_Char_Consensus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:15:39.230758+00:00
-- url     : https://prove2.me/theorems/b203bafc-4b9a-4b1d-806f-b447e2675c82
-- title:
--   Decision problems, consensus, solvability in (uniformly) bounded time and repeated solvability under a message adversary
-- statement:
--   A **decision problem** has finite nonempty inputs $I$, outputs $O$ and a relation $\Delta\subseteq I^2\times O^2$; processes have $X_1=X_2=I$ and $Y_1=Y_2=O\cup\{\bot\}$ ($\bot$ = no decision). An algorithm **solves** it under $A$ if, in every execution whose graph history is in $A$, (1) a non-$\bot$ output never changes afterwards and (2) with round-1 inputs $(i_1,i_2)$, both processes eventually output non-$\bot$ values $(o_1,o_2)$ with $((i_1,i_2),(o_1,o_2))\in\Delta$. **Consensus** with value set $V$ is $I=O=V$ with outputs equal and equal to one of the two proposals. It is **solvable within $R$ rounds** if moreover all $\bot$ outputs occur before round $R$; **in bounded time** if this holds for some $R$; **repeatedly solvable in bounded time** under $A$ if it is solvable in bounded time under every $h^{-1}A$, $h\in\mathrm{Pref}(A)$ (algorithm and bound depending on $h$); **in uniformly bounded time** if one $R$ works for all $h\in\mathrm{Pref}(A)$.
--
--   **Formalization Note.** $\bot$ is `none`. Irrevocability (1) is required in the executions with graph history in $A$, those considered for solvability.
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 7–8 (PDF 8–9), §3.1; pp. 17, 19 (PDF 18, 20), §5.1, §5.3

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model

namespace DistLTLSynth.Char

/-- Output of process 1 in round `r ≥ 1` of `exec(f, h)`: `f₁(v₁(h[...r]))`. -/
def outAt1 {X1 X2 Y1 Y2 : Type} (f : Algorithm X1 X2 Y1 Y2) (h : ℕ → Signal X1 X2) (r : ℕ) :
    Y1 :=
  f.f1 (view1 (pre h r))

/-- Output of process 2 in round `r ≥ 1` of `exec(f, h)`: `f₂(v₂(h[...r]))`. -/
def outAt2 {X1 X2 Y1 Y2 : Type} (f : Algorithm X1 X2 Y1 Y2) (h : ℕ → Signal X1 X2) (r : ℕ) :
    Y2 :=
  f.f2 (view2 (pre h r))

/-- A decision problem (§5.1, p. 17): inputs `I`, outputs `O` (finite, nonempty) and the
relation `Δ ⊆ I² × O²` of allowed input–output pairs. -/
structure DecisionProblem (I O : Type) : Type where
  rel : I × I → O × O → Prop

/-- `f` solves `P` under `A` (§5.1): `X₁ = X₂ = I`, `Y₁ = Y₂ = O ∪ {⊥}` (`none` is `⊥`);
(1) in every execution with graph history in `A`, non-`⊥` outputs never change;
(2) in every execution with graph history in `A` and round-1 inputs `(i₁, i₂)`, both processes
eventually output non-`⊥` values `(o₁, o₂)` with `((i₁, i₂), (o₁, o₂)) ∈ Δ`. -/
def Solves {I O : Type} (P : DecisionProblem I O) (f : Algorithm I I (Option O) (Option O))
    (A : Set (ℕ → CommGraph)) : Prop :=
  (∀ h : ℕ → Signal I I, graphOf h ∈ A → ∀ r ≥ 1,
      (∀ o, outAt1 f h r = some o → outAt1 f h (r + 1) = some o) ∧
      (∀ o, outAt2 f h r = some o → outAt2 f h (r + 1) = some o)) ∧
  (∀ h : ℕ → Signal I I, graphOf h ∈ A → ∃ r ≥ 1, ∃ o1 o2 : O,
      outAt1 f h r = some o1 ∧ outAt2 f h r = some o2 ∧ P.rel ((h 0).1, (h 0).2.1) (o1, o2))

/-- All `⊥` outputs happen before round `R` in all executions with graph history in `A`
(both processes have decided by round `R`). -/
def DecidesWithin {I O : Type} (f : Algorithm I I (Option O) (Option O))
    (A : Set (ℕ → CommGraph)) (R : ℕ) : Prop :=
  ∀ h : ℕ → Signal I I, graphOf h ∈ A → ∀ r ≥ 1,
    (outAt1 f h r = none → r < R) ∧ (outAt2 f h r = none → r < R)

/-- Consensus with value set `V` (§5.1): `I = O = V`, both outputs equal and one of the
proposals. -/
def consensus (V : Type) : DecisionProblem V V where
  rel i o := o.1 = o.2 ∧ (o.1 = i.1 ∨ o.1 = i.2)

/-- Consensus is solvable under `A`. -/
def ConsensusSolvable (V : Type) (A : Set (ℕ → CommGraph)) : Prop :=
  ∃ f : Algorithm V V (Option V) (Option V), Solves (consensus V) f A

/-- Consensus is solvable within `R` rounds under `A`. -/
def ConsensusSolvableWithin (V : Type) (A : Set (ℕ → CommGraph)) (R : ℕ) : Prop :=
  ∃ f : Algorithm V V (Option V) (Option V), Solves (consensus V) f A ∧ DecidesWithin f A R

/-- Consensus is solvable in bounded time under `A`. -/
def ConsensusSolvableBounded (V : Type) (A : Set (ℕ → CommGraph)) : Prop :=
  ∃ R : ℕ, ConsensusSolvableWithin V A R

/-- Consensus is repeatedly solvable in bounded time under `A`: solvable in bounded time
under every `h⁻¹A` with `h ∈ Pref(A)` (algorithm and bound may depend on `h`). -/
def RepeatedlySolvableBounded (V : Type) (A : Set (ℕ → CommGraph)) : Prop :=
  ∀ h ∈ Pref A, ConsensusSolvableBounded V (leftQuot h A)

/-- Consensus is repeatedly solvable in uniformly bounded time under `A`: one bound `R` and,
for each `h ∈ Pref(A)`, an algorithm solving consensus under `h⁻¹A` within `R` rounds. -/
def RepeatedlySolvableUniform (V : Type) (A : Set (ℕ → CommGraph)) : Prop :=
  ∃ R : ℕ, ∀ h ∈ Pref A, ConsensusSolvableWithin V (leftQuot h A) R

end DistLTLSynth.Char


