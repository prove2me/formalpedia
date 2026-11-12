-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_OracleMachine
-- name    : CatalyticTreeEval_Main_OracleMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:29:43.277283+00:00
-- url     : https://prove2.me/theorems/99332eea-910a-4007-9790-cd3992296f52
-- title:
--   Finite binary oracle machines and charged register-program realization
-- statement:
--   An oracle machine extends a finite binary machine by finitely many query states. Ordinary transitions inspect only scanned bits and origin sensors. Query transitions read a scalar, control bit and positional child index from local work, and apply the specified positional oracle to the three encoded registers. Hidden labels are absent from every ordinary transition.
--
--   A run realizes a register-operation list when strictly increasing transition cuts delimit exactly those operations. At each cut the catalyst is the corresponding register encoding. Query spans contain exactly one query at their end and leave register bits unchanged beforehand. Target spans preserve all child bits; swap spans preserve all uninvolved register bits. Every span consists of charged binary steps, apart from the single oracle transition itself.
--
--   $$\mathrm{time}=T,\qquad\mathrm{workHead}<\lceil S\rceil\text{ throughout the run}.$$
--
--   At each query, retained state occupies a prefix of at most $\lceil R\rceil$ work bits; other scratch bits are zero and the input and catalyst heads are at the origin. Final output is empty, register contents match the executed program, and an optional local scalar result is read from the work prefix.
--
--   This makes suspension and retained space operational, preventing query interfaces or tape heads from hiding an uncharged caller stack.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Theorem 4.4; Section 4.2, printed p. 22 (PDF p. 24); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_RegisterProgram

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- Ordinary finite binary control, extended only by a finite set of query states. -/
structure OracleMachine where
  base : Machine
  isQuery : Fin base.states → Bool
  queryNext : Fin base.states → Option (Fin base.states)

def width (m : ℕ) : ℕ := Nat.log 2 (m - 1) + 1

def readNat (work : ℕ → Bool) (offset count : ℕ) : ℕ :=
  ∑ i ∈ Finset.range count, if work (offset + i) then 2 ^ i else 0

def decodeRegisters (m d : ℕ) (τ : List Bool) : Registers m d :=
  fun i c => (readNat (fun b => τ.getD b false) ((i.val * d + c.val) * width m) (width m) : ZMod m)

def OracleMachine.query {m : ℕ} (P : OracleMachine)
    (c : CatalyticMatching.General.Configuration P.base) : ZMod m × Bool × Fin 2 :=
  ((readNat c.work 0 (width m) : ZMod m), c.work (width m),
    if c.work (width m + 1) then 1 else 0)

/-- Only this transition can use U,V or the hidden x. All other steps are binary tape steps. -/
def OracleMachine.step {m d l : ℕ} (P : OracleMachine)
    (U V : Label l → Vec m d) (x : Fin 2 → Label l) (input : List Bool)
    (c : CatalyticMatching.General.Configuration P.base) :
    Option (CatalyticMatching.General.Configuration P.base) :=
  match c.state with
  | none => some c
  | some q =>
    if P.isQuery q then
      if c.catalyst = registerCode (decodeRegisters m d c.catalyst) then
        let a := P.query c
        some { c with
          state := P.queryNext q
          catalyst := registerCode (oracle U V x a.1 a.2.1 a.2.2 (decodeRegisters m d c.catalyst)) }
      else none
    else P.base.step input c

/-- A scalar is supplied in local space, with all other work cells initially blank. -/
def OracleMachine.initial {m d : ℕ} (P : OracleMachine) (α : ZMod m) (R : Registers m d) :
    CatalyticMatching.General.Configuration P.base :=
  { P.base.initial (registerCode R) with work := fun i => (bits (width m) α.val).getD i false }

def OracleMachine.run {m d l : ℕ} (P : OracleMachine)
    (U V : Label l → Vec m d) (x : Fin 2 → Label l) (input : List Bool)
    (α : ZMod m) (R : Registers m d) : ℕ → Option (CatalyticMatching.General.Configuration P.base)
  | 0 => some (P.initial α R)
  | t + 1 => (P.run U V x input α R t).bind (P.step U V x input)

def OracleMachine.querying (P : OracleMachine)
    (c : CatalyticMatching.General.Configuration P.base) : Bool :=
  match c.state with | none => false | some q => P.isQuery q

/-- At suspension, unused scratch is zero and the input/register heads are at origin.
Thus their positions carry no uncharged caller state. The control state is finite. -/
def Suspended {M : Machine} (c : CatalyticMatching.General.Configuration M) (r : ℕ) : Prop :=
  c.workHead < r ∧ c.inputHead = 0 ∧ c.catalystHead = 0 ∧ ∀ i, r ≤ i → c.work i = false

/-- Exact elementary register operations are realized by spans of actual binary steps.
Queries are the final step of their span. Ordinary register writes are confined to the
register(s) named by the operation, including throughout any transient binary encoding. -/
def Realizes {m d l : ℕ} (P : OracleMachine) (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (input : List Bool) (α : ZMod m) (R : Registers m d)
    (ops : List (RegisterOp m d)) (T : ℕ) : Prop :=
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
              (∀ b, b < 2 * d * width m → c.catalyst.getD b false = c0.catalyst.getD b false)
          | .swap a b =>
            P.querying c = false ∧
              (∀ j : Fin 3, j ≠ a → j ≠ b → ∀ z, z < d * width m →
                c.catalyst.getD (j.val * d * width m + z) false =
                  c0.catalyst.getD (j.val * d * width m + z) false))

/-- Final state, actual time, between-query workspace, and state retained across queries. -/
def OracleExecution {m d l : ℕ} (P : OracleMachine) (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (input : List Bool) (α : ZMod m) (R : Registers m d)
    (ops : List (RegisterOp m d)) (space retained : ℝ) (time : Option ℝ)
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

end CatalyticTreeEval.Main


