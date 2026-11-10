-- Prove2me | Definitions.Def_NogoodColoring1137_Main_Computation
-- name    : NogoodColoring1137_Main_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T17:01:37.569199+00:00
-- url     : https://prove2.me/theorems/916e1d95-d623-4066-b1b7-487392fef2f2
-- title:
--   Binary task encodings and uniform execution bounds
-- statement:
--   Encode binary $n$, the row-major adjacency matrix and, for list tasks, three membership bits per vertex. A natural has a unary bit-length header followed by binary magnitude. Search returns a tagged actual coloring or tagged failure. A run is an actual halting finite multitape computation.
--   $$\operatorname{LogTime}_p(A,C,n)=A\exp(C[\ln(n+1)]^p).$$
--   SixTasks specifies ordinary/list decision, search and exact counting in that order. Decision languages consist exactly of encoded promised yes-instances. InQP requires correct Boolean output on all binary strings, including malformed encodings and graphs outside the promise. Programs, positive constants and fixed exponents precede inputs.
--
--   This interface exposes computational content without assuming a successful solver. **Formalization Note** Real functions specify bounds only. Counts have binary magnitude; fixed color names count separately.
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), §§2.1.1–2.1.3,3.1, pp.4–6,9

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_NogoodColoring1137_Main_Instances

namespace NogoodColoring1137.Main

/-- Binary magnitude with a unary bit-length header, not a unary magnitude. -/
def EncodeNat (a : ℕ) : List Bool :=
  List.replicate a.size true ++ [false] ++ IntMul.bin a.size a

def EncodeGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List Bool :=
  EncodeNat n ++ (List.finRange n).flatMap (fun v =>
    (List.finRange n).map (fun w => decide (G.Adj v w)))

def EncodeInstance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : Lists n) : List Bool :=
  EncodeGraph G ++ (List.finRange n).flatMap (fun v =>
    (List.finRange 3).map (fun a => decide (a ∈ L v)))

def EncodeColoring {n : ℕ} (c : Fin n → Color) : List Bool :=
  (List.finRange n).flatMap (fun v => IntMul.bin 2 (c v).val)

/-- Empty output tape is not success: failure has an explicit tag. -/
def SearchAnswer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : Lists n) (out : List Bool) : Prop :=
  (out = [false] ∧ Solutions G L = ∅) ∨
    ∃ c ∈ Solutions G L, out = true :: EncodeColoring c

/-- An actual finite-program computation; every head movement is charged. -/
def Runs (P : IntMul.MultitapeTM) (input out : List Bool) (bound : ℝ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ bound ∧ P.HaltsWithOutput input [] t out

noncomputable def LogTime (power : ℕ) (A C : ℝ) (n : ℕ) : ℝ :=
  A * Real.exp (C * Real.log ((n : ℝ) + 1) ^ power)

/-- Only a semantic language specification, never a computation oracle. -/
def DecisionLanguage (listVersion : Bool) (input : List Bool) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (adj : DecidableRel G.Adj) (L : Lists n),
    DiameterTwo G ∧
    input = (if listVersion then @EncodeInstance n G adj L else @EncodeGraph n G adj) ∧
    (@Solutions n G adj (if listVersion then L else FullLists n)).Nonempty

/-- QP is over all input strings, including malformed strings and graphs outside the promise. -/
def InQP (language : List Bool → Prop) : Prop :=
  ∃ (P : IntMul.MultitapeTM) (A C : ℝ) (power : ℕ),
    0 < A ∧ 0 < C ∧ 1 ≤ power ∧ ∀ input,
      ∃ b : Bool, Runs P input [b] (LogTime power A C input.length) ∧
        (b = true ↔ language input)

/-- All six tasks; a single program and constants per task precede every graph and list. -/
def SixTasks (A C : ℝ) (P : Fin 6 → IntMul.MultitapeTM) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)) (adj : DecidableRel G.Adj) (L : Lists n),
    DiameterTwo G →
    (∃ b : Bool, Runs (P 0) (@EncodeGraph n G adj) [b] (LogTime 3 A C n) ∧
      (b = true ↔ (@Solutions n G adj (FullLists n)).Nonempty)) ∧
    (∃ b : Bool, Runs (P 1) (@EncodeInstance n G adj L) [b] (LogTime 3 A C n) ∧
      (b = true ↔ (@Solutions n G adj L).Nonempty)) ∧
    (∃ out, Runs (P 2) (@EncodeGraph n G adj) out (LogTime 3 A C n) ∧
      @SearchAnswer n G adj (FullLists n) out) ∧
    (∃ out, Runs (P 3) (@EncodeInstance n G adj L) out (LogTime 3 A C n) ∧
      @SearchAnswer n G adj L out) ∧
    Runs (P 4) (@EncodeGraph n G adj)
      (EncodeNat (@Solutions n G adj (FullLists n)).card) (LogTime 3 A C n) ∧
    Runs (P 5) (@EncodeInstance n G adj L)
      (EncodeNat (@Solutions n G adj L).card) (LogTime 3 A C n)

end NogoodColoring1137.Main


