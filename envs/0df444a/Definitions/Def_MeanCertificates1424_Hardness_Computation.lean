-- Prove2me | Definitions.Def_MeanCertificates1424_Hardness_Computation
-- name    : MeanCertificates1424_Hardness_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:37.600195+00:00
-- url     : https://prove2.me/theorems/e6f55675-85d6-4188-8d50-cdbbee65aff2
-- title:
--   Binary codecs, finite machine execution, uniform resources and operational ETH
-- statement:
--   An algorithm is a finite deterministic multi-stack machine with finite alphabets and Mathlib's actual transition semantics. Inputs and outputs are finite words over four symbols: zero and one encode bits, two separates numbers, and three is reserved. Natural numbers use terminated binary digits; rationals use a sign and reduced numerator and denominator. Graphs use sorted adjacency lists, with a row for each vertex. The complete input code contains only the graph, budget, Lipschitz bound, noise tolerance, and reports. Concrete parsers are provided for these numerical inputs and outputs.
--
--   A polynomial solver chooses one program and constants $C>0,d\in\mathbb N$ before every input. It must halt on every promised instance with a rational output satisfying the specified approximation, within
--
--   $$C(\operatorname{length}(\operatorname{enc}(I))+1)^d$$
--
--   actual steps. The general reduction constructor instead has a bound polynomial in $r+m+R$; the $R=3k$ headline constructor has a polynomial bound in ordinary binary graph input length. Fixed $\rho$, approximation factor, or error improvement may affect the program and constants. An unknown field, certificate endpoint, or input optimum never appears in a machine's input.
--
--   A normalized 3CNF formula is a finite set of clauses, each a set of at most three signed variables from $r$ named variables. Satisfiability is the existence of a Boolean assignment making every clause true. Empty clauses are false and the empty formula is true. The operational Exponential Time Hypothesis excludes one deterministic machine deciding these formulas in time
--
--   $$C(\operatorname{length}(\operatorname{enc}(F))+1)^d\,2^{f(r)},\qquad f(r)=o(r).$$
--
--   The sublinear condition quantifies over every positive real tolerance and an eventual threshold. This defines the hypothesis in terms of SAT truth and charged computation, independently of graph approximation or certificate hardness.
--
--   **Formalization Note** The underlying general machine object and step semantics are Mathlib's, with finiteness required on every stack alphabet. The file adds codecs and paper-specific predicates rather than a caller-defined execution cost or an oracle. Clause normalization keeps representation size polynomial in the variable count.
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Section 2 Representation and ETH convention in Section 1.1, printed pp.2,6 (PDF pp.4,8)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Reduction

set_option autoImplicit false

namespace MeanCertificates1424.Hardness

/-- Binary data with separator 2. Symbol 3 is reserved. No real numbers or oracles
are machine symbols. §2 Representation, printed p.6 (PDF p.8). -/
abbrev Symbol := Fin 4

/-- Reuse Mathlib's operational multi-stack machines. Every stack alphabet is finite;
no correctness or complexity assertion is stored in a machine. -/
abbrev Machine := {M : Turing.TM2ComputableAux Symbol Symbol // ∀ j, Finite (M.tm.Γ j)}

def encNat (n : ℕ) : List Symbol :=
  ((Nat.digits 2 n).map fun b => if b = 0 then 0 else 1) ++ [2]

def parseNat (w : List Symbol) : Option (ℕ × List Symbol) := do
  let bits := w.takeWhile (· ≠ 2)
  let tail := w.dropWhile (· ≠ 2)
  if tail.isEmpty || !(bits.all fun b => b = 0 || b = 1) then none else
    let n := bits.foldr (fun b a => b.val + 2 * a) 0
    if encNat n = bits ++ [2] then some (n, tail.drop 1) else none

def encRat (q : ℚ) : List Symbol :=
  (if q < 0 then 1 else 0) :: (encNat q.num.natAbs ++ encNat q.den)

def parseRat (w : List Symbol) : Option (ℚ × List Symbol) := do
  let s ← w.head?
  if s ≠ 0 ∧ s ≠ 1 then none else do
    let (a, w') ← parseNat (w.drop 1)
    let (b, rest) ← parseNat w'
    if b = 0 then none else
      let q : ℚ := (if s = 1 then -(a : ℤ) else a) / (b : ℚ)
      some (q, rest)

/-- A total, fuel-free finite parser: the number of components is explicit. -/
def parseMany {α : Type} (parse : List Symbol → Option (α × List Symbol)) :
    ℕ → List Symbol → Option (List α × List Symbol)
  | 0, w => some ([], w)
  | n + 1, w => do
    let (a, rest) ← parse w
    let (as, rest') ← parseMany parse n rest
    some (a :: as, rest')

def encList {α : Type} (enc : α → List Symbol) (as : List α) : List Symbol :=
  encNat as.length ++ as.flatMap enc

def parseList {α : Type} (parse : List Symbol → Option (α × List Symbol))
    (w : List Symbol) : Option (List α × List Symbol) := do
  let (n, rest) ← parseNat w
  parseMany parse n rest

/-- Sorted adjacency lists, including a row for isolated vertices; not a dense or unary code. -/
noncomputable def encGraph {n : ℕ} (G : SimpleGraph (Fin n)) : List Symbol := by
  classical
  exact encNat n ++ (List.finRange n).flatMap fun u =>
    encList (fun v : Fin n => encNat v.val) ((Finset.univ.filter (G.Adj u)).sort (· ≤ ·))

noncomputable def encInstance (I : UniformInstance) : List Symbol :=
  encGraph I.graph ++ encNat I.budget ++ encRat I.lipschitz ++ encRat I.noise ++
  (List.finRange I.n).flatMap fun v => encRat (I.reports v)

/-- Concrete parser of the finite input representation. Invalid rows may be rejected by
promise validation; no parser consults feasibility, an endpoint, or an unknown field. -/
def parseInstance (w : List Symbol) : Option (UniformInstance × List Symbol) := do
  let (n, rest) ← parseNat w
  let (rows, rest) ← parseMany (parseList parseNat) n rest
  let (b, rest) ← parseNat rest
  let (L, rest) ← parseRat rest
  let (eps, rest) ← parseRat rest
  let (y, rest) ← parseMany parseRat n rest
  let G : SimpleGraph (Fin n) := SimpleGraph.fromRel
    (fun u v => v.val ∈ rows.getD u.val [])
  some (⟨n, G, b, L, eps, fun v => y.getD v.val 0⟩, rest)

def decodeInstance (w : List Symbol) : Option UniformInstance := do
  let (I, rest) ← parseInstance w
  if rest.isEmpty then some I else none

def decodeRat (w : List Symbol) : Option ℚ := do
  let (q, rest) ← parseRat w
  if rest.isEmpty then some q else none

noncomputable def encReductionInput {r : ℕ} (H : SimpleGraph (Fin r))
    (k R : ℕ) : List Symbol := encGraph H ++ encNat k ++ encNat R

noncomputable def encHeadlineInput {r : ℕ} (H : SimpleGraph (Fin r))
    (k : ℕ) : List Symbol := encGraph H ++ encNat k

/-- `TM2OutputsInTime` is charged iteration of `TM2.step` from `initList` to a
halting output configuration. Every statement has finite syntax and finite alphabets. -/
def RunsWithin (M : Machine) (input output : List Symbol) (T : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime M.val.tm
    (input.map M.val.inputAlphabet.invFun)
    (some (output.map M.val.outputAlphabet.invFun)) T)

/-- A uniform polynomial on encoded input length; constants precede every input. -/
noncomputable def PolySolves (promise : UniformInstance → Prop)
    (spec : UniformInstance → ℚ → Prop) : Prop :=
  ∃ (M : Machine) (C d : ℕ), 0 < C ∧ ∀ I, promise I →
    ∃ q : ℚ, RunsWithin M (encInstance I) (encRat q)
      (C * ((encInstance I).length + 1) ^ d) ∧ spec I q

noncomputable def WidthAlgorithm (α : ℝ) (ρ : ℚ) : Prop :=
  PolySolves (Restricted ρ) (fun I q => WidthApprox α I (q : ℝ))

noncomputable def Estimator (factor : ℝ) (promise : UniformInstance → Prop) : Prop :=
  PolySolves promise (fun I q => ErrorApprox factor I (q : ℝ))

/-- Constructor cost polynomial in r+m+R, not in log R, as in Theorem 3.1. -/
noncomputable def Constructs (pad : ∀ {r : ℕ}, SimpleGraph (Fin r) → ℕ → ℕ → ℕ) : Prop :=
  ∃ (M : Machine) (C d : ℕ), 0 < C ∧
    ∀ (r : ℕ) (H : SimpleGraph (Fin r)) (k R : ℕ), Admissible H k → 1 ≤ R →
      RunsWithin M (encReductionInput H k R) (encInstance (gadget H k R (pad H k R)))
        (C * (r + edgeCount H + R + 1) ^ d)

/-- R=3k uses ordinary encoded graph input length. The fixed rational fraction
may affect the program and constants, but no instance may affect them. -/
noncomputable def HeadlineConstructs (ρ : ℚ) : Prop :=
  ∃ (M : Machine) (C d : ℕ), 0 < C ∧
    ∀ (r : ℕ) (H : SimpleGraph (Fin r)) (k : ℕ), Admissible H k →
      RunsWithin M (encHeadlineInput H k)
        (encInstance (gadget H k (3 * k) (padding H k (3 * k) ρ)))
        (C * ((encHeadlineInput H k).length + 1) ^ d)

/-- An actual 3CNF formula is a normalized set of clauses, each a set of at most
three signed variables. Duplicates are irrelevant; empty clauses/formulas retain
ordinary SAT semantics. The number of possible clauses is polynomial in r. -/
abbrev Literal (r : ℕ) := Fin r × Bool
abbrev Clause (r : ℕ) := {c : Finset (Literal r) // c.card ≤ 3}
abbrev Formula (r : ℕ) := Finset (Clause r)

def Satisfiable {r : ℕ} (F : Formula r) : Prop :=
  ∃ a : Fin r → Bool, ∀ c ∈ F, ∃ l ∈ c.val, a l.1 = l.2

noncomputable def encFormula {r : ℕ} (F : Formula r) : List Symbol := by
  classical
  let clauses := F.toList.map fun c =>
    encList encNat ((c.val.image fun l => 2 * l.1.val + l.2.toNat).sort (· ≤ ·))
  -- Sort the serialized clauses, so enumeration is canonical and independent of proofs.
  exact encNat r ++ encList id (clauses.mergeSort (· ≤ ·))

/-- f(r)=o(r), with the threshold allowed to depend on every positive ε. -/
def Sublinear (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ r : ℕ, n₀ ≤ r → (f r : ℝ) ≤ ε * r

/-- ETH of printed p.2 / PDF p.4. One finite deterministic SAT decider, actual
truth, time 2^f(r) times ordinary polynomial input-reading overhead. It is not a
free proposition and assumes no graph/certificate hardness result. -/
noncomputable def ETH : Prop :=
  ¬ ∃ (M : Machine) (f : ℕ → ℕ) (C d : ℕ), 0 < C ∧ Sublinear f ∧
    ∀ (r : ℕ) (F : Formula r), ∃ answer : Bool,
      (answer = true ↔ Satisfiable F) ∧
      RunsWithin M (encFormula F) [if answer then 1 else 0]
        (C * ((encFormula F).length + 1) ^ d * 2 ^ f r)

end MeanCertificates1424.Hardness


