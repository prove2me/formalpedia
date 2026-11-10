-- Prove2me | Definitions.Def_BhangaleHypergraph_Main_Computation
-- name    : BhangaleHypergraph_Main_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:07:27.484588+00:00
-- url     : https://prove2.me/theorems/ef974e4f-8c1e-4b02-bc56-49f366db9536
-- title:
--   Operational time certificates and the growing-color promise
-- statement:
--   An input-dependent time certificate supplies one finite bundled TM2 machine which outputs the prescribed encoded result within the stated number of steps on every input. Counts and tables use terminated unary numbers; subsets use membership bit strings; lists are length-delimited. Circuit-SAT and its evaluation are the published acyclic Boolean circuit model, and NP is the published polynomially verifiable language class. The generic published gap reduction supplies the polynomial-time machine and both promise implications.
--
--   All logarithms below are base two. For a positive absolute $c$, put
--   $$b_c(N)=c\sqrt{\frac{\log_2\log_2 N}{\log_2\log_2\log_2 N}}.$$
--   For a fixed sufficiently large cutoff $N_0$, the YES promise is $N\ge N_0$ and 2-colorability. The NO promise is $N\ge N_0$ and absence of a $k$-coloring for every natural $k\le b_c(N)$. This is equivalent to the strict chromatic inequality, including integer thresholds. NP-hardness quantifies over every polynomially verifiable language and requires an actual polynomial-time gap reduction.
--
--   Low-error requests encode an upward power-of-two rounding of the real error parameter. Their specification still quantifies over every real $g$ in the source interval. Core and closed-domain enumeration specifications demand exact lists of subset membership codes and explicit, uniform machine bounds. None of the runtime or correctness claims is assumed as input data.
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Lemma 2.5 and §§2.6, 3.2, 3.6, pp. 6–7, 11–12, 14–15, 18–20 (printed pages = PDF pages); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Mathlib
import Definitions.Def_BhangaleHypergraph_Main_Base
import Definitions.Def_BhangaleHypergraph_Main_Outer
import Definitions.Def_FourToOneGames_LabelCover
import Definitions.Def_FourToOneGames_Hypergraph
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_PrivPCP_Circuit

namespace BhangaleHypergraph.Main

/-- Input-dependent time bound on one actual, finite, bundled TM2 machine. -/
def ComputesWithin {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) (bound : α → ℕ) : Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ a,
    Nonempty (Turing.TM2OutputsInTime M.tm ((ea a).map M.inputAlphabet.symm)
      (some ((eb (f a)).map M.outputAlphabet.symm)) (bound a))

def NatCode := FourToOneGames.unaryCode

def SubsetCode {R : ℕ} (A : Finset (Fin R)) : List Bool :=
  (List.finRange R).map fun a => decide (a ∈ A)

def ListCode (xs : List (List Bool)) : List Bool :=
  NatCode xs.length ++ xs.flatMap fun x => NatCode x.length ++ x

def BaseCode (B : BaseCover) : List Bool :=
  [B.A, B.B, B.E, B.L, B.R].flatMap NatCode ++
    (List.finRange B.E).flatMap fun e =>
      NatCode (B.left e).val ++ NatCode (B.right e).val ++
        (List.finRange B.L).flatMap fun a => NatCode (B.proj e a).val

def LayeredCode (G : Layered) : List Bool :=
  [G.n, G.layers, G.edges].flatMap NatCode ++
    (List.finRange G.n).flatMap (fun x => NatCode (G.layer x).val ++ NatCode (G.R x)) ++
    (List.finRange G.edges).flatMap fun e =>
      NatCode (G.src e).val ++ NatCode (G.dst e).val ++
        (List.finRange (G.R (G.src e))).flatMap fun a => NatCode (G.proj e a).val

noncomputable def Log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

noncomputable def ColorThreshold (c : ℝ) (N : ℕ) : ℝ :=
  c * Real.sqrt (Log2 (Log2 N) / Log2 (Log2 (Log2 N)))

/-- Every allowed integer color count is ruled out. This preserves strictness at integer thresholds. -/
def GapNo (c : ℝ) (N0 : ℕ) (H : FourToOneGames.Hypergraph3) : Prop :=
  N0 ≤ H.n ∧ ∀ k : ℕ, (k : ℝ) ≤ ColorThreshold c H.n → ¬ H.Colorable k

def GapYes (N0 : ℕ) (H : FourToOneGames.Hypergraph3) : Prop :=
  N0 ≤ H.n ∧ H.Colorable 2

/-- Operational NP-hardness, quantifying over every polynomially verifiable language.
The constant and size cutoff are arguments, fixed before any source language or input. -/
def GapNPHard (c : ℝ) (N0 : ℕ) : Prop :=
  ∀ (A : Type) [Fintype A] [Nonempty A] (K : CookPvsNP.Lang A), K ∈ CookPvsNP.NP A →
    Nonempty (FourToOneGames.GapReduction (fun x : List A => x)
      FourToOneGames.encodeHypergraph3 (fun x => x ∈ K) (fun x => x ∉ K)
      (GapYes N0) (GapNo c N0))

/-- `t` encodes an upward power-of-two rounding of the requested real error parameter. -/
abbrev LowRequest := PrivPCP.Circuit × ℕ

def LowRequestCode (x : LowRequest) : List Bool :=
  ListCode [PrivPCP.Circuit.code x.1, NatCode x.2]

noncomputable def LowBudget (b beta : ℝ) (k : ℕ) (x : LowRequest) : ℕ :=
  let n : ℝ := PrivPCP.Circuit.size x.1
  let g : ℝ := (2 : ℝ) ^ x.2
  (⌈(n + 1) + (n + 1) * (2 : ℝ) ^ (b * (Log2 (max 2 n)) ^ beta) * g ^ k + Real.exp (b * g ^ k)⌉₊ + 1) ^ k

/-- Uniform resource claims use the actual circuit size; coefficients are explicit absolutes. -/
def LowErrorClaims (a beta b : ℝ) (k : ℕ) (F : LowRequest → BaseCover) : Prop :=
  ∀ (Φ : PrivPCP.Circuit) (g : ℝ), 2 ≤ g →
    g ≤ (2 : ℝ) ^ (a * (Log2 (PrivPCP.Circuit.size Φ)) ^ beta) →
    let B := F (Φ, ⌈Log2 g⌉₊)
    0 < B.E ∧ (Φ ∈ PrivPCP.CircuitSAT → BaseSatisfiable B) ∧
    (Φ ∉ PrivPCP.CircuitSAT → BaseValue B ≤ 1 / g) ∧
    (max B.degreeA B.degreeB : ℝ) ≤ b * g ^ k ∧
    Log2 (2 * (max B.L B.R : ℝ)) ≤ b * g ^ k ∧
    (B.A + B.B : ℝ) ≤ b * PrivPCP.Circuit.size Φ *
      (2 : ℝ) ^ (b * (Log2 (PrivPCP.Circuit.size Φ)) ^ beta) * g ^ k

abbrev CoreRequest := ℕ × ℕ × ℕ

def CoreRequestCode (x : CoreRequest) : List Bool := [x.1, x.2.1, x.2.2].flatMap NatCode

/-- Exact enumeration as full membership bit strings, with duplicates allowed. -/
def EnumeratesCore (E : CoreRequest → List (List Bool)) : Prop :=
  ∀ C s R, 2 ≤ C → 1 ≤ s → 1 ≤ R →
    (E (C, s, R)).toFinset = (Core C s R).image SubsetCode

abbrev ClosedRequest := Layered × ℕ × ℕ

def ClosedRequestCode (x : ClosedRequest) : List Bool :=
  ListCode [LayeredCode x.1, NatCode x.2.1, NatCode x.2.2]

noncomputable def ClosureBudget (K k : ℕ) (x : ClosedRequest) : ℕ :=
  let G := x.1
  let C := x.2.1
  let s := x.2.2
  ((G.n + 1) * (1 + MaxOutdegree G) ^ C *
    (2 * max 1 (MaxAlphabet G)) ^ (K * (C * s + C)) +
      (LayeredCode G).length + C + s + 1) ^ k

def EnumeratesClosed (E : ClosedRequest → List (List (List Bool))) : Prop :=
  ∀ G C s, 2 ≤ C → 1 ≤ s → G.layers ≤ C + 1 →
    (E (G, C, s)).length = G.n ∧ ∀ x : Fin G.n,
      ((E (G, C, s))[x.val]?.getD []).toFinset = (Closed G C s x).image SubsetCode

end BhangaleHypergraph.Main


