-- Prove2me | Definitions.Def_CorrelatedLocalSearch_Supplement_SAT
-- name    : CorrelatedLocalSearch_Supplement_SAT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:01:56.037516+00:00
-- url     : https://prove2.me/theorems/c7b236de-096b-4f7e-b85e-26fcf555af70
-- title:
--   Complete formula family, single-depth costs, Hamming-ball restarts and archived portfolio
-- statement:
--   The complete formula $\Phi_n$ contains every ordered $k$-clause with $r$ positive literals first and $k-r$ negative literals, on distinct variables. The definition layer also supplies the exact worst survival probability, single-depth cover cost, $\Psi_s(L)=\min\{L^3,L/(s-s_*)\}$ with $L/0=\infty$, the Hamming-ball restart walk, its source-flip stopping time and restoration cost, and the archived-tape portfolio schedule of Appendix C.6.
--
--   **Formalization Note** The complete family is constructed rather than introduced as an unrelated variable. Hamming resets consume no new tape symbol.
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), §4 pp.10–12 and App. C.5–C.6 pp.31–32 (PDF pp.12–14, 33–34)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_SourceClass
import Definitions.Def_CorrelatedLocalSearch_sStar
import Definitions.Def_CorrelatedLocalSearch_Clause
import Definitions.Def_CorrelatedLocalSearch_walkTau
import Definitions.Def_CorrelatedLocalSearch_Supplement_GeneralSource

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- The complete family `Phi_n`: every ordered clause with `r` positive literals first and
`k-r` negative literals, on distinct variables. -/
noncomputable def completeFormula (k r n : Nat) : List (CorrelatedLocalSearch.Clause k n) := by
  classical
  let fs : Finset {f : Fin k -> Fin n // Function.Injective f} := Finset.univ
  exact fs.toList.map (fun f =>
    { lit := fun i => (f.1 i, decide (i.val < r))
      inj := f.2 })

/-- The all-one assignment, the complete family's strong witness. -/
def allOneAssignment (n : Nat) : Fin n -> Bool := fun _ => true

/-- An assignment has exactly `r` zero coordinates. -/
def HasExactlyRZeros {n : Nat} (r : Nat) (x : Fin n -> Bool) : Prop :=
  Set.ncard {i | x i = false} = r

/-- Survival of the published promise-SAT walk beyond a deadline. -/
def satSurvivalEvent {k n : Nat} (Phi : List (CorrelatedLocalSearch.Clause k n))
    (sel : CorrelatedLocalSearch.Selector k n) (x0 : Fin n -> Bool) (T : Nat) :
    Set (Nat -> Fin k) :=
  {omega | (T : ℕ∞) < CorrelatedLocalSearch.walkTau Phi sel x0 omega}

/-- The exact worst survival probability for the complete family at `D=1`. -/
noncomputable def completeWorstTail (k r n : Nat) (s : Real)
    (sel : CorrelatedLocalSearch.Selector k n) (x0 : Fin n -> Bool) (T : Nat) : ENNReal :=
  ⨆ nu : {nu : Measure (Nat -> Fin k) //
      nu ∈ CorrelatedLocalSearch.SourceClass k s 1},
    nu.1 (satSurvivalEvent (completeFormula k r n) sel x0 T)

/-- The uniform reference distribution on `[k]`. -/
noncomputable def uniformPi (k : Nat) : Fin k -> Real := fun _ => (k : Real)⁻¹

/-- The best single-depth cover cost for the complete-family survival event. -/
noncomputable def completeSingleDepthCost (k r n : Nat)
    (sel : CorrelatedLocalSearch.Selector k n) (x0 : Fin n -> Bool) (T t : Nat) : ENNReal :=
  singleDepthCost (uniformPi k) (CorrelatedLocalSearch.sStar k r)
    (satSurvivalEvent (completeFormula k r n) sel x0 T) t

/-- `Psi_s(L)=min{L^3,L/(s-s_*)}`, with the second branch infinite at the threshold. -/
noncomputable def Psi (k r : Nat) (s L : Real) : ENNReal :=
  min (ENNReal.ofReal (L ^ 3))
    (if s = CorrelatedLocalSearch.sStar k r then ⊤
      else ENNReal.ofReal (L / (s - CorrelatedLocalSearch.sStar k r)))

open Classical in
/-- One step of the Hamming-ball restart walk: reset an unsatisfying proposal outside radius
`2H` to `x0`, without consuming another source symbol. -/
noncomputable def hammingRestartStep {k n : Nat}
    (Phi : List (CorrelatedLocalSearch.Clause k n))
    (sel : CorrelatedLocalSearch.Selector k n) (x0 : Fin n -> Bool) (H : Nat)
    (pre : List (Fin k)) (x : Fin n -> Bool) (a : Fin k) : Fin n -> Bool :=
  let y := CorrelatedLocalSearch.walkStep Phi sel pre x a
  if CorrelatedLocalSearch.Satisfies Phi y then y
  else if 2 * H < hammingDist y x0 then x0 else y

noncomputable def hammingRestartRun {k n : Nat}
    (Phi : List (CorrelatedLocalSearch.Clause k n))
    (sel : CorrelatedLocalSearch.Selector k n) (x0 : Fin n -> Bool) (H : Nat) :
    List (Fin k) -> (Fin n -> Bool) -> List (Fin k) -> (Fin n -> Bool)
  | _, x, [] => x
  | pre, x, a :: rest =>
      hammingRestartRun Phi sel x0 H (pre ++ [a])
        (hammingRestartStep Phi sel x0 H pre x a) rest

noncomputable def hammingRestartState {k n : Nat}
    (Phi : List (CorrelatedLocalSearch.Clause k n))
    (sel : CorrelatedLocalSearch.Selector k n) (x0 : Fin n -> Bool) (H : Nat)
    (w : List (Fin k)) : Fin n -> Bool :=
  hammingRestartRun Phi sel x0 H [] x0 w

/-- Source-driven flips until the Hamming-ball restart walk satisfies the formula. -/
noncomputable def hammingRestartTau {k n : Nat}
    (Phi : List (CorrelatedLocalSearch.Clause k n))
    (sel : CorrelatedLocalSearch.Selector k n) (x0 : Fin n -> Bool) (H : Nat)
    (omega : Nat -> Fin k) : ℕ∞ :=
  ⨅ (t : Nat) (_h : CorrelatedLocalSearch.Satisfies Phi
      (hammingRestartState Phi sel x0 H (CorrelatedLocalSearch.tapePrefix omega t))), (t : ℕ∞)

open Classical in
/-- Variable updates used by the list-restoration implementation on a finite consumed word:
one per source-driven flip plus one per coordinate restored at each reset. -/
noncomputable def hammingRestartUpdateCost {k n : Nat}
    (Phi : List (CorrelatedLocalSearch.Clause k n))
    (sel : CorrelatedLocalSearch.Selector k n) (x0 : Fin n -> Bool) (H : Nat)
    (w : List (Fin k)) : Nat :=
  w.length + ∑ i : Fin w.length,
    let pre := w.take i.val
    let x := hammingRestartState Phi sel x0 H pre
    let y := CorrelatedLocalSearch.walkStep Phi sel pre x w[i]
    if ¬ CorrelatedLocalSearch.Satisfies Phi y ∧ 2 * H < hammingDist y x0
      then hammingDist y x0 else 0

/-- A deterministic archived-tape portfolio with the exact schedule in Appendix C.6 is represented
by its total update count and its semantic schedule obligations. -/
structure ArchivedPortfolio (k n : Nat)
    (Phi : List (CorrelatedLocalSearch.Clause k n)) (x0 : Fin n -> Bool) where
  simulatedAssignments : Nat
  baseSelector : CorrelatedLocalSearch.Selector k n
  auxiliaryRadius : Nat -> Nat
  groupAtRound : Nat -> Nat
  auxiliaryAtRound : Nat -> Nat
  activationCount : Nat -> Nat -> Nat
  localSelector : Nat -> CorrelatedLocalSearch.Selector k n

def portfolioHaltedByRound {k n : Nat}
    {Phi : List (CorrelatedLocalSearch.Clause k n)} {x0 : Fin n -> Bool}
    (A : ArchivedPortfolio k n Phi x0) (omega : Nat -> Fin k) (m : Nat) : Prop :=
  CorrelatedLocalSearch.Satisfies Phi
      (CorrelatedLocalSearch.walkState Phi A.baseSelector x0
        (CorrelatedLocalSearch.tapePrefix omega m)) ∨
    ∃ j ≤ Nat.clog 2 n,
      CorrelatedLocalSearch.Satisfies Phi
        (hammingRestartState Phi (A.localSelector j) x0 (A.auxiliaryRadius j)
          (CorrelatedLocalSearch.tapePrefix omega (A.activationCount j m)))

noncomputable def portfolioUpdatesAtRound {k n : Nat}
    {Phi : List (CorrelatedLocalSearch.Clause k n)} {x0 : Fin n -> Bool}
    (A : ArchivedPortfolio k n Phi x0) (omega : Nat -> Fin k) (m : Nat) : Nat :=
  m + ∑ j ∈ Finset.range (Nat.clog 2 n + 1),
    hammingRestartUpdateCost Phi (A.localSelector j) x0 (A.auxiliaryRadius j)
      (CorrelatedLocalSearch.tapePrefix omega (A.activationCount j m))

/-- Total variable updates at the first scheduled round in which a simulation satisfies `Phi`. -/
noncomputable def portfolioSigma {k n : Nat}
    {Phi : List (CorrelatedLocalSearch.Clause k n)} {x0 : Fin n -> Bool}
    (A : ArchivedPortfolio k n Phi x0) (omega : Nat -> Fin k) : ℕ∞ :=
  ⨅ (m : Nat) (_h : portfolioHaltedByRound A omega m),
    (portfolioUpdatesAtRound A omega m : ℕ∞)

/-- The number of source symbols retained when the first simulation halts.  The base walk reads
and archives exactly one new symbol per portfolio round. -/
noncomputable def portfolioArchiveSize {k n : Nat}
    {Phi : List (CorrelatedLocalSearch.Clause k n)} {x0 : Fin n -> Bool}
    (A : ArchivedPortfolio k n Phi x0) (omega : Nat -> Fin k) : ℕ∞ :=
  ⨅ (m : Nat) (_h : portfolioHaltedByRound A omega m), (m : ℕ∞)

/-- The exact schedule required of the portfolio: one base walk; auxiliary radii `2^j`; in round
`m>=1`, group `G_{v_2(m)}={2^b-1,...,2^(b+1)-2}` advances cyclically; auxiliary activation `q`
replays archived symbol `omega_q`; resets restore changed coordinates. -/
def IsExactArchivedSchedule {k n : Nat}
    {Phi : List (CorrelatedLocalSearch.Clause k n)} {x0 : Fin n -> Bool}
    (A : ArchivedPortfolio k n Phi x0) : Prop :=
  A.simulatedAssignments = 2 + Nat.clog 2 n ∧
  (∀ j, A.auxiliaryRadius j = 2 ^ j) ∧
  (∀ m, 0 < m -> 2 ^ A.groupAtRound m ∣ m ∧
    ¬ 2 ^ (A.groupAtRound m + 1) ∣ m) ∧
  (∀ m, 0 < m ->
    2 ^ A.groupAtRound m - 1 ≤ A.auxiliaryAtRound m ∧
    A.auxiliaryAtRound m ≤ 2 ^ (A.groupAtRound m + 1) - 2 ∧
    A.auxiliaryAtRound m = 2 ^ A.groupAtRound m - 1 +
      (((m / 2 ^ A.groupAtRound m - 1) / 2) % 2 ^ A.groupAtRound m)) ∧
  (∀ j m, A.activationCount j m =
    ((Finset.Icc 1 m).filter (fun q => A.auxiliaryAtRound q = j)).card)

/-- Main catalog declaration for the complete-family and restart SAT supplement. -/
noncomputable abbrev SAT (k r n : Nat) := completeFormula k r n

end CorrelatedLocalSearch.Supplement


