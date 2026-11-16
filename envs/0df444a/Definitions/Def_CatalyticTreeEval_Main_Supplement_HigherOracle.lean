-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_Supplement_HigherOracle
-- name    : CatalyticTreeEval_Main_Supplement_HigherOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:33:27.229354+00:00
-- url     : https://prove2.me/theorems/d52e0c47-7026-4ce6-93f6-21c3f8f27482
-- title:
--   Theorem 4.11 proof — charged positional oracle execution
-- statement:
--   The finite binary control is extended by query states. At a query, local binary fields specify the scalar, control bit and child position; the only transition that can inspect a hidden label is the positional register oracle. Every other transition is a step of the published binary machine.
--
--   An execution realizes an explicit register-operation list when strictly increasing transition cut times agree with its partial executions, with queries at the end of their spans and all other register writes confined to the named positions. Across a query, scratch is blank beyond the retained prefix and the input and register heads return to origin. In particular,
--   $$\text{local space counts every visited work position, and time counts every transition.}$$
--   The child position occupies a binary field of width $1+\lfloor\log_2(r-1)\rfloor$, decoded modulo $r$. A position field in the machine record guarantees $r>0$; the theorem uses only $r\ge2$. The interface permits the shared scratch and retained-state bounds of the variable-arity recursion without encoding them as assumed resource labels.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Theorem 4.11 proof, printed pp. 28–29 (PDF pp. 30–31); positional convention of Theorem 4.4, printed p. 22 (PDF p. 24)

import Definitions.Def_CatalyticTreeEval_Main_Supplement_HigherProgram

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

/-- Ordinary finite binary control, extended only by a finite set of query states. -/
structure OracleMachine (r : ℕ) where
  position : Fin r
  base : Machine
  isQuery : Fin base.states → Bool
  queryNext : Fin base.states → Option (Fin base.states)

def width (m : ℕ) : ℕ := Nat.log 2 (m - 1) + 1

def readNat (work : ℕ → Bool) (offset count : ℕ) : ℕ :=
  ∑ i ∈ Finset.range count, if work (offset + i) then 2 ^ i else 0

def decodeRegisters (r m d : ℕ) (τ : List Bool) : Registers r m d :=
  fun i c => (readNat (fun b => τ.getD b false) ((i.val * d + c.val) * width m) (width m) : ZMod m)

def OracleMachine.query {r m : ℕ} (P : OracleMachine r)
    (c : CatalyticMatching.General.Configuration P.base) : ZMod m × Bool × Fin r :=
  ((readNat c.work 0 (width m) : ZMod m), c.work (width m),
    ⟨readNat c.work (width m + 1) (width r) % r,
      Nat.mod_lt _ (Nat.zero_lt_of_lt P.position.isLt)⟩)

/-- Only this transition can use U,V or the hidden x. All other steps are binary tape steps. -/
def OracleMachine.step {r m d l : ℕ} (P : OracleMachine r)
    (U V : Label l → Vec m d) (x : Fin r → Label l) (input : List Bool)
    (c : CatalyticMatching.General.Configuration P.base) :
    Option (CatalyticMatching.General.Configuration P.base) :=
  match c.state with
  | none => some c
  | some q =>
    if P.isQuery q then
      if c.catalyst = registerCode (decodeRegisters r m d c.catalyst) then
        let a := P.query c
        some { c with
          state := P.queryNext q
          catalyst := registerCode (oracle U V x a.1 a.2.1 a.2.2 (decodeRegisters r m d c.catalyst)) }
      else none
    else P.base.step input c

/-- A scalar is supplied in local space, with all other work cells initially blank. -/
def OracleMachine.initial {r m d : ℕ} (P : OracleMachine r) (α : ZMod m) (R : Registers r m d) :
    CatalyticMatching.General.Configuration P.base :=
  { P.base.initial (registerCode R) with work := fun i => (bits (width m) α.val).getD i false }

def OracleMachine.run {r m d l : ℕ} (P : OracleMachine r)
    (U V : Label l → Vec m d) (x : Fin r → Label l) (input : List Bool)
    (α : ZMod m) (R : Registers r m d) : ℕ → Option (CatalyticMatching.General.Configuration P.base)
  | 0 => some (P.initial α R)
  | t + 1 => (P.run U V x input α R t).bind (P.step U V x input)

def OracleMachine.querying {r : ℕ} (P : OracleMachine r)
    (c : CatalyticMatching.General.Configuration P.base) : Bool :=
  match c.state with | none => false | some q => P.isQuery q

/-- At suspension, unused scratch is zero and the input/register heads are at origin.
Thus their positions carry no uncharged caller state. The control state is finite. -/
def Suspended {M : Machine} (c : CatalyticMatching.General.Configuration M) (retained : ℕ) : Prop :=
  c.workHead < retained ∧ c.inputHead = 0 ∧ c.catalystHead = 0 ∧ ∀ i, retained ≤ i → c.work i = false

/-- Exact elementary register operations are realized by spans of actual binary steps.
Queries are the final step of their span. Ordinary register writes are confined to the
register(s) named by the operation, including throughout any transient binary encoding. -/
def Realizes {r m d l : ℕ} (P : OracleMachine r) (U V : Label l → Vec m d)
    (x : Fin r → Label l) (input : List Bool) (α : ZMod m) (R : Registers r m d)
    (ops : List (RegisterOp r m d)) (T : ℕ) : Prop :=
  ∃ cuts : Fin (ops.length + 1) → ℕ,
    StrictMono cuts ∧ cuts 0 = 0 ∧ cuts (Fin.last ops.length) = T ∧
    ∀ i : Fin ops.length,
      ∃ c0 c1,
        P.run U V x input α R (cuts i.castSucc) = some c0 ∧
        P.run U V x input α R (cuts i.succ) = some c1 ∧
        c0.catalyst = registerCode (execute U V x R (ops.take i.val)) ∧
        c1.catalyst = registerCode (execute U V x R (ops.take (i.val + 1))) ∧
        (∀ u, cuts i.castSucc ≤ u → u < cuts i.succ →
          ∀ c, P.run U V x input α R u = some c →
          match ops.get i with
          | .query a ctrl σ =>
            (P.querying c = true ↔ u + 1 = cuts i.succ) ∧
              c.catalyst = c0.catalyst ∧
              (P.querying c = true → P.query c = (a, ctrl, σ))
          | .target _ =>
            P.querying c = false ∧
              (∀ b, b < r * d * width m → c.catalyst.getD b false = c0.catalyst.getD b false)
          | .swap a b =>
            P.querying c = false ∧
              (∀ j : Fin (r + 1), j ≠ a → j ≠ b → ∀ z, z < d * width m →
                c.catalyst.getD (j.val * d * width m + z) false =
                  c0.catalyst.getD (j.val * d * width m + z) false))

/-- Final state, actual time, between-query workspace, and state retained across queries. -/
def OracleExecution {r m d l : ℕ} (P : OracleMachine r) (U V : Label l → Vec m d)
    (x : Fin r → Label l) (input : List Bool) (α : ZMod m) (R : Registers r m d)
    (ops : List (RegisterOp r m d)) (space retained : ℝ) (time : Option ℝ)
    (localResult : Option (ZMod m)) : Prop :=
  ∃ (T : ℕ) (c : CatalyticMatching.General.Configuration P.base),
    P.run U V x input α R T = some c ∧ c.state = none ∧ c.output = [] ∧
    c.catalyst = registerCode (execute U V x R ops) ∧
    Realizes P U V x input α R ops T ∧
    (∀ u ≤ T, ∀ cu, P.run U V x input α R u = some cu →
      cu.workHead < ⌈space⌉₊ ∧
        (P.querying cu = true → Suspended cu ⌈retained⌉₊)) ∧
    (∀ b ∈ time, (T : ℝ) ≤ b) ∧
    (∀ z ∈ localResult, readNat c.work 0 (width m) = z.val)

end CatalyticTreeEval.Main.Supplement


