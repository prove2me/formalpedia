-- Prove2me | Definitions.Def_RamanujanLiftTower136_Tower_Computation
-- name    : RamanujanLiftTower136_Tower_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:39:44.936663+00:00
-- url     : https://prove2.me/theorems/91431d26-dc0f-44dd-99db-2235ee246a40
-- title:
--   Binary encodings and exact multi-stack time and space predicates
-- statement:
--   A bit query at fixed prime $p$ contains the level $n\ge1$, a residue $t$, a label $j$, and a mode selecting a neighbor or a lift bit. Encode $t$ as exactly $n$ little-endian bits, followed by a fixed-width label and the mode. The total length determines $n$. The answer is exactly $n$ neighbor bits or one lift bit.
--
--   Machines use Mathlib's finite-control multi-stack model, with every stack alphabet required finite. Strong explicitness asserts a machine and positive constant $C_p$ such that
--   $$\operatorname{time}(n,t,j,\mathrm{mode})\le C_pn^3.$$
--   The machine and constant are chosen once for $p$. Preprocessing instead has absolute constants before $p$, with bounds $Cp(\lfloor\log_2p\rfloor+1)^k$ and $Cp^2(\lfloor\log_2p\rfloor+1)^k$. Generator coefficient encodings have length at most $H(\lfloor\log_2p\rfloor+1)$ with absolute $H$.
--
--   A uniform coordinate-query machine receives only $n,t$, eight signed coordinates, and the mode; $p$ indexes its correctness domain but is absent from its input encoding. Its time is at most $C(n+\lfloor\log_2p\rfloor+1)^3$, and every reachable configuration has at most $S(n+\lfloor\log_2p\rfloor+1)^k$ stack symbols. Its machine and constants are uniform in $p$.
--
--   **Formalization Note** Natural and signed integers use self-delimiting binary codes; the coordinate-query level uses a unary delimiter. These encodings have the prescribed linear bit lengths. All machine existence, correctness, time, and space requirements are conclusions of theorem items.
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.8 (PDF p.9), §2 computational model; §7.1–§7.2, Lemma 7.1 and Propositions 7.2–7.3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Graphs

set_option maxHeartbeats 1000000

noncomputable section

namespace RamanujanLiftTower136.Tower
open Classical
open Turing

/-- Little-endian fixed-width binary representation. -/
def bits (w x : ℕ) : List Bool := List.ofFn (fun i : Fin w => decide (x / 2^i.val % 2 = 1))
def bitLength (x : ℕ) : ℕ := Nat.log 2 x + 1
def natCode (x : ℕ) : List Bool :=
  List.replicate (bitLength x) true ++ [false] ++ bits (bitLength x) x
def intCode (x : ℤ) : List Bool := decide (x < 0) :: natCode x.natAbs

def finiteAlphabet (M : Turing.FinTM2) : Prop := ∀ k, Finite (M.Γ k)

def stackSpace (M : FinTM2) (input : List (M.Γ M.k₀)) (B : ℕ) : Prop :=
  letI : Fintype M.K := M.kFin
  ∀ (s : ℕ) (c : M.Cfg),
    (fun q : Option M.Cfg => q.bind M.step)^[s] (some (Turing.initList M input)) = some c →
    (∑ k, (c.stk k).length) ≤ B

structure Query (p : ℕ) where
  n : ℕ
  positive : 1 ≤ n
  t : Vertex n
  j : Label p
  liftMode : Bool

def encodeQuery (p : ℕ) (q : Query p) : List Bool :=
  bits q.n q.t.val ++ bits (bitLength ((labels p).length)) q.j.val ++ [q.liftMode]
def queryAnswer (p : ℕ) (q : Query p) : List Bool :=
  if q.liftMode then [liftBit p q.n q.t q.j]
  else bits q.n (neighbor p q.n q.t q.j).val

def stronglyExplicit (p : ℕ) : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∃ M : TM2ComputableInTime (encodeQuery p) id (queryAnswer p),
    finiteAlphabet M.tm ∧ ∀ q, M.time (encodeQuery p q).length ≤ C*q.n^3

abbrev PreInput := {p : ℕ // admissible p}
def encodePre (p : PreInput) : List Bool := natCode p.val ++ natCode (smallerRoot p.val)
def balancedAnswer (p : PreInput) : List Bool :=
  let a := balancedCoordinates p.val (smallerRoot p.val)
  intCode a.1 ++ intCode a.2

def balancedAlgorithm : Prop :=
  ∃ C k : ℕ, 0 < C ∧ ∃ M : TM2ComputableInTime encodePre id balancedAnswer,
    finiteAlphabet M.tm ∧ ∀ p, M.time (encodePre p).length ≤ C*p.val*(bitLength p.val)^k

def encodeGeneratorsInput (p : PreInput) : List Bool := natCode p.val ++ balancedAnswer p
def generatorsAnswer (p : PreInput) : List Bool :=
  ((labels p.val).map (fun m => ((List.ofFn m).map intCode).flatten)).flatten ++
  ((List.finRange (labels p.val).length).map (fun j => natCode (reverse p.val j).val)).flatten

def generatorsAlgorithm : Prop :=
  ∃ C k H : ℕ, 0 < C ∧ 0 < H ∧
    ∃ M : TM2ComputableInTime encodeGeneratorsInput id generatorsAnswer,
      finiteAlphabet M.tm ∧ (∀ p, M.time (encodeGeneratorsInput p).length ≤ C*p.val^2*(bitLength p.val)^k) ∧
      ∀ (p : PreInput) (j : Label p.val), (((List.ofFn ((labels p.val).get j)).map intCode).flatten).length ≤ H*bitLength p.val

structure CoordinateQuery where
  p : ℕ
  primeCondition : admissible p
  n : ℕ
  positive : 1 ≤ n
  t : Vertex n
  m : Fin 8 → ℤ
  selected : m ∈ labels p
  liftMode : Bool

def encodeCoordinateQuery (q : CoordinateQuery) : List Bool :=
  List.replicate q.n true ++ [false] ++ bits q.n q.t.val ++
    ((List.ofFn q.m).map intCode).flatten ++ [q.liftMode]
def coordinateAnswer (q : CoordinateQuery) : List Bool :=
  let g := psi (conjugate (fromCoordinates q.m))
  let a := phi g (q.t.val : ℤ_[2])
  if q.liftMode then
    [decide (((PadicInt.toZModPow (q.n+1) a).val / 2^q.n) % 2 = 1)]
  else bits q.n (PadicInt.toZModPow q.n a).val

def localAlgorithm : Prop :=
  ∃ C S k : ℕ, 0 < C ∧ 0 < S ∧
    ∃ M : TM2ComputableInTime encodeCoordinateQuery id coordinateAnswer,
      finiteAlphabet M.tm ∧
      (∀ q, M.time (encodeCoordinateQuery q).length ≤ C*(q.n + bitLength q.p)^3) ∧
      (∀ q, stackSpace M.tm ((encodeCoordinateQuery q).map M.inputAlphabet.symm)
        (S*(q.n + bitLength q.p)^k)) ∧
      ∀ p, admissible p → stronglyExplicit p

end RamanujanLiftTower136.Tower


