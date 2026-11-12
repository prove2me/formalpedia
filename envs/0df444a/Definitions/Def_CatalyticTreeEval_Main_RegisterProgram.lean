-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_RegisterProgram
-- name    : CatalyticTreeEval_Main_RegisterProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:38.303442+00:00
-- url     : https://prove2.me/theorems/7af0797c-546f-4878-9d7a-99af62407ad0
-- title:
--   Positional oracle and the concrete one-level program
-- statement:
--   Three global registers occupy positions $0,1,2$. Fixed hidden labels $x_0,x_1$ enter only through a query $(\alpha,\mathrm{ctrl},\sigma)$, which adds $\alpha U_{x_\sigma}$ or $\alpha V_{x_\sigma}$ to position $\sigma$. Swaps change register contents without changing the oracle's positional addressing.
--
--   The inner-product program is the literal swap-and-four-query procedure of Lemma 4.5. The one-level program then loops through decoder terms, adds the shift vectors to the children, enumerates every candidate pair $(y_0,y_1)$, and adds to the target
--
--   $$\alpha\varphi_j(\langle\tau_0,V_{y_0}\rangle+\langle\tau_1,V_{y_1}\rangle-g)W_{f(y_0,y_1)},$$
--
--   before undoing the two shift queries. The program records its actual operations and executes them by sequential fold. Exact inverse pairing is a fixed-point-free involution on the list of child-operation occurrences; deliberate target additions are excluded. Register computation on a binary machine separately requires halting, full output, exact register restoration, charged workspace and charged time.
--
--   The mathematical operation list specifies the algorithm for algebraic correctness. Its resource-preserving binary realization is a conclusion of Theorem 4.4, rather than an assumption of this definition.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Sections 4.1–4.2; Lemmas 4.5–4.6, printed p. 23 (PDF p. 25); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Decoder

set_option autoImplicit false

namespace CatalyticTreeEval.Main

abbrev Registers (m d : ℕ) := Fin 3 → Vec m d

def addAt {m d : ℕ} (R : Registers m d) (i : Fin 3) (v : Vec m d) : Registers m d :=
  Function.update R i (R i + v)

def swapAt {m d : ℕ} (R : Registers m d) (i j : Fin 3) : Registers m d :=
  Function.update (Function.update R i (R j)) j (R i)

/-- This oracle addresses positions, not the current owners of their contents. -/
def oracle {m d l : ℕ} (U V : Label l → Vec m d) (x : Fin 2 → Label l)
    (α : ZMod m) (ctrl : Bool) (σ : Fin 2) (R : Registers m d) : Registers m d :=
  addAt R ⟨σ.val, by omega⟩ (α • (if ctrl then V (x σ) else U (x σ)))

inductive RegisterOp (m d : ℕ) where
  | swap : Fin 3 → Fin 3 → RegisterOp m d
  | query : ZMod m → Bool → Fin 2 → RegisterOp m d
  | target : Vec m d → RegisterOp m d

def RegisterOp.inverse {m d : ℕ} : RegisterOp m d → RegisterOp m d
  | .swap i j => .swap i j
  | .query α c σ => .query (-α) c σ
  | .target v => .target (-v)

def RegisterOp.apply {m d l : ℕ} (U V : Label l → Vec m d) (x : Fin 2 → Label l)
    (R : Registers m d) : RegisterOp m d → Registers m d
  | .swap i j => swapAt R i j
  | .query α c σ => oracle U V x α c σ R
  | .target v => addAt R 2 v

def execute {m d l : ℕ} (U V : Label l → Vec m d) (x : Fin 2 → Label l)
    (R : Registers m d) (ops : List (RegisterOp m d)) : Registers m d :=
  ops.foldl (RegisterOp.apply U V x) R

def childOps {m d : ℕ} (ops : List (RegisterOp m d)) : List (RegisterOp m d) :=
  ops.filter fun op => match op with | .target _ => false | _ => true

/-- Every child operation belongs to an exact inverse pair; the earlier member is undone later.
Target operations are excluded because they deliberately accumulate the answer. -/
def InversePairs {m d : ℕ} (ops : List (RegisterOp m d)) : Prop :=
  ∃ σ : Equiv.Perm (Fin (childOps ops).length),
    Function.Involutive σ ∧ (∀ i, σ i ≠ i) ∧
    ∀ i, (childOps ops).get (σ i) = ((childOps ops).get i).inverse

/-- Literal swap/compute/query procedure of Lemma 4.5. Hidden labels enter only through oracle. -/
def innerProgram {m d l : ℕ} (U V : Label l → Vec m d) (x : Fin 2 → Label l)
    (R : Registers m d) : ZMod m × List (RegisterOp m d) :=
  let tmp1 := R 0 ⬝ᵥ R 1
  let R1 := swapAt R 0 1
  let R2 := oracle U V x 1 true 0 R1
  let tmp2 := R2 0 ⬝ᵥ R2 1
  let R3 := oracle U V x (-1) true 0 R2
  let R4 := oracle U V x 1 true 1 R3
  let tmp3 := R4 0 ⬝ᵥ R4 1
  ((tmp2 - tmp1) + (tmp3 - tmp1),
    [.swap 0 1, .query 1 true 0, .query (-1) true 0,
      .query 1 true 1, .query (-1) true 1, .swap 0 1])

/-- One complete iteration of §4.2, with explicit candidate-pair enumeration. -/
def termProgram {m d l k : ℕ} (U V W : Label l → Vec m d) (D : Decoder m k)
    (f : Label l → Label l → Label l) (x : Fin 2 → Label l)
    (α g : ZMod m) (R : Registers m d) (j : Fin k) : List (RegisterOp m d) :=
  let b := D.shift j
  let Q := oracle U V x b false 1 (oracle U V x b false 0 R)
  [.query b false 0, .query b false 1] ++
    (List.finRange (2 ^ l)).flatMap (fun y0 =>
      (List.finRange (2 ^ l)).map fun y1 =>
        let c := D.term j ((Q 0 ⬝ᵥ V y0) + (Q 1 ⬝ᵥ V y1) - g)
        RegisterOp.target ((α * c) • W (f y0 y1))) ++
    [.query (-b) false 0, .query (-b) false 1]

/-- The actual mathematical program of §4.2, rather than its desired net effect. -/
def oneLevelProgram {m d l k : ℕ} (U V W : Label l → Vec m d) (D : Decoder m k)
    (f : Label l → Label l → Label l) (x : Fin 2 → Label l)
    (α : ZMod m) (R : Registers m d) : List (RegisterOp m d) :=
  let ip := innerProgram U V x R
  let start := execute U V x R ip.2
  let result := (List.finRange k).foldl (fun acc j =>
    let ops := termProgram U V W D f x α ip.1 acc.1 j
    (execute U V x acc.1 ops, acc.2 ++ ops)) (start, ip.2)
  result.2

def registerCode {m d : ℕ} (R : Registers m d) : List Bool :=
  (List.finRange 3).flatMap fun i => vecCode (R i)

/-- Register output semantics still charges every actual finite-table step and every local work bit. -/
def RegisterComputes {m d : ℕ} (M : Machine) (input output : List Bool)
    (R : Registers m d) (space time : ℝ) : Prop :=
  ∃ (t : ℕ) (c : CatalyticMatching.General.Configuration M),
    M.run input (registerCode R) t = some c ∧ c.state = none ∧ c.output = output ∧
    c.catalyst = registerCode R ∧ M.workBound input (registerCode R) t ⌈space⌉₊ ∧
    (t : ℝ) ≤ time

end CatalyticTreeEval.Main


