-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_Supplement_HigherProgram
-- name    : CatalyticTreeEval_Main_Supplement_HigherProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:32:46.481205+00:00
-- url     : https://prove2.me/theorems/f9d0df93-2d19-4ae4-9810-bacad50e2193
-- title:
--   Theorem 4.11 proof — positional register program for r children
-- statement:
--   There are $r+1$ vector registers in $(\mathbb Z_m)^d$, with children at positions $0,\ldots,r-1$ and target at position $r$. A query $(\alpha,\mathrm{ctrl},i)$ changes position $i$ by adding $\alpha U_{x_i}$ or $\alpha V_{x_i}$ according to its control bit. The hidden labels enter the program only through those queries.
--
--   The explicit program uses the neighboring-position swap trick to compute a correction scalar from register inner products. Each decoder iteration shares one term index across all $r$ children, shifts every child, enumerates candidate tuples in lexicographic order, updates the target, and undoes the shifts. Its query count is the literal count
--   $$2r+2rk=2r(k+1).$$
--   The execution folds the explicit swap, query and target instructions over the initial registers. The full-output predicate separately requires a run of the published finite binary machine, the entire output label, exact restoration of the serialized registers, a bound on every visited work cell, and a bound on actual transitions. These are execution conditions to be proved, not fields assumed of an evaluator.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Theorem 4.11 and its one-level proof, printed pp. 28–29 (PDF pp. 30–31); §4.3 readout conventions, printed pp. 25–26 (PDF pp. 27–28)

import Definitions.Def_CatalyticTreeEval_Main_Decoder
import Definitions.Def_CatalyticTreeEval_Main_Supplement_HigherEncoding

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

/-- Position r is the target; positions below r are the child registers. -/
abbrev Registers (r m d : ℕ) := Fin (r + 1) → Vec m d

def addAt {r m d : ℕ} (R : Registers r m d) (i : Fin (r + 1))
    (v : Vec m d) : Registers r m d := Function.update R i (R i + v)

def swapAt {r m d : ℕ} (R : Registers r m d) (i j : Fin (r + 1)) : Registers r m d :=
  Function.update (Function.update R i (R j)) j (R i)

/-- Labels enter only through this positional oracle; swaps do not change addressing. -/
def oracle {r m d l : ℕ} (U V : Label l → Vec m d) (x : Fin r → Label l)
    (α : ZMod m) (ctrl : Bool) (σ : Fin r) (R : Registers r m d) : Registers r m d :=
  addAt R σ.castSucc (α • (if ctrl then V (x σ) else U (x σ)))

inductive RegisterOp (r m d : ℕ) where
  | swap : Fin (r + 1) → Fin (r + 1) → RegisterOp r m d
  | query : ZMod m → Bool → Fin r → RegisterOp r m d
  | target : Vec m d → RegisterOp r m d

def RegisterOp.inverse {r m d : ℕ} : RegisterOp r m d → RegisterOp r m d
  | .swap i j => .swap i j
  | .query a c i => .query (-a) c i
  | .target v => .target (-v)

def RegisterOp.apply {r m d l : ℕ} (U V : Label l → Vec m d) (x : Fin r → Label l)
    (R : Registers r m d) : RegisterOp r m d → Registers r m d
  | .swap i j => swapAt R i j
  | .query a c i => oracle U V x a c i R
  | .target v => addAt R (Fin.last r) v

def execute {r m d l : ℕ} (U V : Label l → Vec m d) (x : Fin r → Label l)
    (R : Registers r m d) (ops : List (RegisterOp r m d)) : Registers r m d :=
  ops.foldl (RegisterOp.apply U V x) R

def neighbor {r : ℕ} (i : Fin r) : Fin r :=
  ⟨(i.val + 1) % r, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- One swap/compute/query/undo procedure from the proof of Theorem 4.11.
The scalar is computed from register inner products after the actual oracle update. -/
def innerChunk {r m d l : ℕ} (U V : Label l → Vec m d) (x : Fin r → Label l)
    (R : Registers r m d) (i : Fin r) : ZMod m × List (RegisterOp r m d) :=
  let j := neighbor i
  let before := R j.castSucc ⬝ᵥ R i.castSucc
  let R1 := swapAt R i.castSucc j.castSucc
  let R2 := oracle U V x 1 true i R1
  (R2 i.castSucc ⬝ᵥ R2 j.castSucc - before,
    [.swap i.castSucc j.castSucc, .query 1 true i, .query (-1) true i,
      .swap i.castSucc j.castSucc])

def innerProgram {r m d l : ℕ} (U V : Label l → Vec m d) (x : Fin r → Label l)
    (R : Registers r m d) : ZMod m × List (RegisterOp r m d) :=
  let result := (List.finRange r).foldl (fun acc i =>
    let chunk := innerChunk U V x acc.1 i
    (execute U V x acc.1 chunk.2, acc.2.1 + chunk.1, acc.2.2 ++ chunk.2)) (R, 0, [])
  (result.2.1, result.2.2)

/-- One shared decoder index j across the entire tuple of r candidate labels. -/
def termProgram {r m d l k : ℕ} (U V W : Label l → Vec m d) (D : Decoder m k)
    (f : (Fin r → Label l) → Label l) (x : Fin r → Label l)
    (α g : ZMod m) (R : Registers r m d) (j : Fin k) : List (RegisterOp r m d) :=
  let b := D.shift j
  let pre := (List.finRange r).map (fun i => RegisterOp.query b false i)
  let Q := execute U V x R pre
  pre ++ (tuples r l).map (fun y =>
    let c := D.term j ((∑ i, Q i.castSucc ⬝ᵥ V (y i)) - g)
    RegisterOp.target ((α * c) • W (f y))) ++
    (List.finRange r).map (fun i => RegisterOp.query (-b) false i)

def oneLevelProgram {r m d l k : ℕ} (U V W : Label l → Vec m d) (D : Decoder m k)
    (f : (Fin r → Label l) → Label l) (x : Fin r → Label l)
    (α : ZMod m) (R : Registers r m d) : List (RegisterOp r m d) :=
  let ip := innerProgram U V x R
  let start := execute U V x R ip.2
  let result := (List.finRange k).foldl (fun acc j =>
    let ops := termProgram U V W D f x α ip.1 acc.1 j
    (execute U V x acc.1 ops, acc.2 ++ ops)) (start, ip.2)
  result.2

def registerCode {r m d : ℕ} (R : Registers r m d) : List Bool :=
  (List.finRange (r + 1)).flatMap fun i => vecCode (R i)

/-- Full output and restoration by a raw finite binary machine, charging every step
and every visited local work bit; all r+1 registers have arbitrary initial values. -/
def RegisterComputes {r m d : ℕ} (M : Machine) (input output : List Bool)
    (R : Registers r m d) (space time : ℝ) : Prop :=
  ∃ (t : ℕ) (c : CatalyticMatching.General.Configuration M),
    M.run input (registerCode R) t = some c ∧ c.state = none ∧ c.output = output ∧
    c.catalyst = registerCode R ∧ M.workBound input (registerCode R) t ⌈space⌉₊ ∧
    (t : ℝ) ≤ time

end CatalyticTreeEval.Main.Supplement


