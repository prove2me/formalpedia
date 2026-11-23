-- Prove2me | Definitions.Def_zf192_spec
-- name    : zf192_spec
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T15:47:40.94393+00:00
-- url     : https://prove2.me/theorems/9cdc74be-e93e-4c54-989a-43994a6b682c
-- title:
--   ZF192 machine, set-theory model, and coding definitions
-- statement:
--   This definition module transcribes the standalone ZF192 challenge vocabulary: a literal 192-state transition table, ordinary binary-tape configurations and halting, a finite syntax and natural-deduction calculus for ZF, internal natural-number arithmetic and coding of configurations and histories, and the conditional-independence predicates. The two theorem targets use these definitions to state the represented halting sentence and the blank-tape nonhalting claim.
-- source:
--   https://github.com/jamesyc/BusyBeaver/blob/e71174d78877133222a7784fa371ced827fa6aca/ZF192/ProofSources/ZF192/Challenge.lean

module
public import Std
@[expose] public section
/-! Standalone statement for the exact 192-state machine. -/
namespace PalomarZF192Arithmetic
section InternalSets
variable {V : Type} (E : V → V → Prop)
def Empty (a : V) : Prop := ∀ x, ¬ E x a
def Succ (a b : V) : Prop := ∀ x, E x b ↔ E x a ∨ x = a
def Pair (a b p : V) : Prop := ∀ x, E x p ↔ x = a ∨ x = b
def OrderedPair (a b p : V) : Prop :=
 ∃ aa ab, Pair E a a aa ∧ Pair E a b ab ∧ Pair E aa ab p
def At (f x y : V) : Prop := ∃ p, E p f ∧ OrderedPair E x y p
/-- The function and its domain are elements of the model, not external maps. -/
def FunctionOn (f domain : V) : Prop :=
 (∀ x, E x domain → ∃ y, At E f x y ∧ ∀ z, At E f x z → z = y) ∧
 (∀ p, E p f → ∃ x y, E x domain ∧ OrderedPair E x y p)
def Inductive (a : V) : Prop :=
 (∃ z, Empty E z ∧ E z a) ∧ ∀ x, E x a → ∃ y, Succ E x y ∧ E y a
def Omega (w : V) : Prop :=
 Inductive E w ∧ ∀ a, Inductive E a → ∀ x, E x w → E x a
/-- Meaningful on actual ZF models, where a unique omega exists. -/
def NatObject (x : V) : Prop := ∃ w, Omega E w ∧ E x w
def Numeral : Nat → V → Prop
 | 0, x => Empty E x
 | n + 1, x => ∃ y, Numeral n y ∧ Succ E y x
/-- Internal finite recursion, including nonstandard finite lengths. -/
def Add (a b c : V) : Prop :=
 NatObject E a ∧ NatObject E b ∧ NatObject E c ∧
 ∃ z domain f, Empty E z ∧ Succ E b domain ∧ FunctionOn E f domain ∧
 At E f z a ∧ At E f b c ∧
 (∀ i x, E i domain → At E f i x → NatObject E x) ∧
 ∀ i, E i b → ∃ j x y, Succ E i j ∧ At E f i x ∧ At E f j y ∧ Succ E x y
def Mul (a b c : V) : Prop :=
 NatObject E a ∧ NatObject E b ∧ NatObject E c ∧
 ∃ z domain f, Empty E z ∧ Succ E b domain ∧ FunctionOn E f domain ∧
 At E f z z ∧ At E f b c ∧
 (∀ i x, E i domain → At E f i x → NatObject E x) ∧
 ∀ i, E i b → ∃ j x y, Succ E i j ∧ At E f i x ∧ At E f j y ∧ Add E x a y
/-- y = bit + 2*x, using arithmetic internal to the set model. -/
def BitCons (bit : Bool) (x y : V) : Prop :=
 ∃ b two twice, Numeral E (if bit then 1 else 0) b ∧ Numeral E 2 two ∧
 Mul E two x twice ∧ Add E b twice y
structure Conf (V : Type) where
 q : V
 left : V
 right : V
def Valid (s : Conf V) : Prop := NatObject E s.q ∧ NatObject E s.left ∧ NatObject E s.right
/-- Literal table movement. true means right; false means left. -/
def Move (read write direction : Bool) (next : Nat) (s t : Conf V) : Prop :=
 ∃ r, BitCons E read r s.right ∧ Numeral E next t.q ∧
 if direction then BitCons E write s.left t.left ∧ t.right = r
 else ∃ l bit middle, BitCons E bit l s.left ∧ t.left = l ∧
   BitCons E write r middle ∧ BitCons E bit middle t.right
/-- Cantor graph, matching the production equation
2*z=(a+b)*(a+b+1)+2*b. All witnesses are model objects. -/
def Cantor (a b z : V) : Prop :=
 NatObject E a ∧ NatObject E b ∧ NatObject E z ∧
 ∃ two sum next product twiceB twiceZ total,
 Numeral E 2 two ∧ Add E a b sum ∧ Succ E sum next ∧
 Mul E sum next product ∧ Mul E two b twiceB ∧
 Mul E two z twiceZ ∧ Add E product twiceB total ∧ twiceZ = total
def ListCons (a b c : V) : Prop := ∃ p, Cantor E a b p ∧ Succ E p c
def ListHead (x a : V) : Prop :=
 (Empty E x ∧ Empty E a) ∨ ∃ b, ListCons E a b x
def ListTail (x b : V) : Prop :=
 (Empty E x ∧ Empty E b) ∨ ∃ a, ListCons E a b x
def NumericConfCode (s : Conf V) (code : V) : Prop :=
 ∃ lr, Cantor E s.left s.right lr ∧ Cantor E s.q lr code
end InternalSets
end PalomarZF192Arithmetic

namespace PalomarZF192History
open PalomarZF192Arithmetic

abbrev Row := Option (Bool × Bool × Nat)
def literalRows : List (Row × Row) := [
  (some (true, false, 1), some (true, true, 192)),
  (some (false, false, 2), some (true, false, 3)),
  (some (false, false, 3), some (true, false, 4)),
  (some (false, false, 5), some (true, false, 6)),
  (some (false, false, 7), some (true, false, 8)),
  (some (false, false, 9), some (true, false, 10)),
  (some (false, false, 11), some (true, false, 12)),
  (some (false, false, 13), some (true, false, 14)),
  (some (false, false, 15), some (true, false, 16)),
  (some (false, false, 17), some (true, false, 18)),
  (some (false, false, 19), some (true, false, 12)),
  (some (false, false, 20), some (true, false, 21)),
  (some (false, false, 22), some (true, false, 20)),
  (some (false, false, 23), some (true, false, 24)),
  (some (false, false, 25), some (false, false, 26)),
  (some (false, false, 27), some (true, false, 6)),
  (some (false, false, 20), some (true, true, 28)),
  (some (true, true, 17), some (false, false, 26)),
  (some (false, false, 29), some (true, false, 30)),
  (some (false, false, 31), some (true, false, 32)),
  (some (true, true, 33), some (true, true, 34)),
  (some (false, false, 35), some (false, false, 36)),
  (some (false, false, 37), some (true, false, 38)),
  (some (true, true, 17), some (true, false, 39)),
  (some (false, false, 3), some (true, false, 5)),
  (some (false, false, 40), some (true, false, 41)),
  (some (false, false, 42), some (true, false, 26)),
  (some (false, false, 43), some (true, false, 44)),
  (some (false, false, 18), some (true, false, 45)),
  (some (false, false, 46), some (true, false, 34)),
  (some (false, false, 47), some (true, false, 48)),
  (some (true, false, 49), some (false, false, 50)),
  (some (false, true, 11), some (false, false, 51)),
  (some (false, false, 52), some (true, false, 33)),
  (some (false, false, 53), some (true, false, 54)),
  (some (true, true, 55), some (false, false, 26)),
  (some (false, false, 51), some (true, false, 36)),
  (some (false, false, 47), some (true, false, 34)),
  (some (true, false, 26), some (false, false, 56)),
  (some (false, true, 13), some (true, false, 40)),
  (some (false, false, 18), some (true, true, 57)),
  (some (false, false, 58), some (true, false, 12)),
  (some (false, false, 59), some (true, false, 42)),
  (some (false, false, 60), some (true, false, 61)),
  (some (false, false, 62), some (true, false, 10)),
  (some (false, false, 63), some (true, false, 64)),
  (some (false, false, 65), some (false, false, 66)),
  (some (true, false, 67), some (false, false, 66)),
  (some (false, false, 68), some (false, false, 56)),
  (some (false, false, 69), some (true, false, 49)),
  (some (false, false, 36), some (true, false, 50)),
  (some (false, false, 70), some (true, false, 51)),
  (some (false, false, 49), some (true, false, 52)),
  (some (false, false, 71), some (true, true, 72)),
  (some (false, false, 73), some (false, false, 74)),
  (some (true, false, 33), some (false, false, 66)),
  (some (false, false, 74), some (true, false, 56)),
  (some (false, false, 75), some (true, false, 76)),
  (some (false, false, 77), some (true, false, 78)),
  (some (false, false, 79), some (true, false, 59)),
  (some (false, false, 80), some (true, false, 41)),
  (some (false, false, 81), some (true, false, 82)),
  (some (false, false, 83), some (true, false, 57)),
  (some (false, false, 10), some (true, false, 31)),
  (some (false, false, 84), some (true, false, 85)),
  (some (true, true, 86), some (true, false, 87)),
  (some (false, false, 50), some (true, false, 66)),
  (some (false, false, 26), some (true, false, 67)),
  (some (false, false, 88), some (false, false, 89)),
  (some (false, false, 67), some (true, false, 69)),
  (some (false, false, 56), some (true, false, 70)),
  (some (true, true, 90), some (true, false, 72)),
  (some (false, false, 86), some (false, false, 89)),
  (some (true, true, 55), some (false, false, 89)),
  (some (false, false, 91), some (true, false, 74)),
  (some (false, false, 92), some (true, false, 6)),
  (some (false, false, 93), some (true, true, 94)),
  (some (true, false, 69), some (false, false, 50)),
  (some (false, true, 95), some (false, false, 70)),
  (some (true, false, 96), some (true, false, 79)),
  (some (true, true, 17), some (true, false, 97)),
  (some (false, false, 82), some (true, true, 98)),
  (some (false, false, 99), some (true, false, 12)),
  (some (false, false, 100), some (true, false, 101)),
  (some (true, false, 102), some (false, false, 66)),
  (some (false, false, 68), some (false, false, 103)),
  (some (true, false, 26), some (false, false, 50)),
  (some (true, true, 17), some (true, false, 17)),
  (some (true, true, 90), some (true, false, 104)),
  (some (false, false, 33), some (true, false, 89)),
  (some (true, true, 105), some (false, false, 50)),
  (some (false, false, 106), some (true, false, 91)),
  (some (false, false, 9), some (true, false, 41)),
  (some (false, false, 107), some (true, false, 28)),
  (some (false, false, 108), some (true, false, 109)),
  (some (false, false, 54), some (true, true, 110)),
  (some (true, true, 111), some (false, false, 79)),
  (some (false, true, 112), some (true, true, 24)),
  (some (false, false, 113), some (true, false, 114)),
  (some (false, false, 18), some (false, false, 26)),
  (some (false, false, 23), some (true, false, 115)),
  (some (false, false, 25), some (true, false, 100)),
  (some (false, false, 89), some (true, false, 102)),
  (some (false, false, 66), some (true, false, 103)),
  (some (false, false, 55), some (true, false, 116)),
  (some (true, true, 117), some (true, true, 105)),
  (some (false, false, 118), some (true, false, 106)),
  (some (false, false, 119), some (true, false, 120)),
  (some (false, false, 97), some (true, false, 121)),
  (some (false, false, 122), some (true, true, 123)),
  (some (false, false, 11), some (true, false, 20)),
  (some (false, true, 124), some (false, true, 125)),
  (some (false, false, 92), some (true, false, 99)),
  (some (false, false, 108), some (true, false, 5)),
  (some (false, false, 126), some (true, false, 18)),
  (some (false, false, 60), some (true, true, 112)),
  (some (true, true, 127), some (false, false, 50)),
  (some (false, false, 128), some (true, true, 117)),
  (some (false, true, 129), some (true, false, 111)),
  (some (false, false, 130), some (true, false, 131)),
  (some (false, false, 40), some (true, true, 27)),
  (some (false, false, 18), some (true, false, 82)),
  (some (false, false, 108), some (true, false, 132)),
  (some (false, false, 133), some (true, true, 109)),
  (some (false, true, 118), some (true, true, 124)),
  (some (false, true, 134), some (true, false, 125)),
  (some (false, false, 121), some (true, true, 98)),
  (some (true, true, 127), some (true, true, 135)),
  (some (false, false, 136), some (true, true, 137)),
  (some (true, true, 135), some (true, true, 129)),
  (some (false, false, 138), some (true, false, 75)),
  (some (false, false, 139), some (true, false, 25)),
  (some (false, false, 140), some (true, false, 41)),
  (some (false, false, 141), some (true, false, 142)),
  (some (true, true, 117), some (true, false, 96)),
  (some (false, false, 129), some (false, true, 128)),
  (some (false, true, 137), some (true, false, 143)),
  (some (false, true, 128), some (true, true, 128)),
  (some (false, false, 144), some (true, true, 7)),
  (some (false, false, 120), some (true, false, 39)),
  (some (false, false, 39), some (true, false, 6)),
  (some (false, false, 145), some (true, false, 146)),
  (some (false, false, 147), some (true, false, 126)),
  (some (false, true, 117), some (true, false, 148)),
  (some (false, false, 149), some (true, false, 147)),
  (some (false, false, 150), some (true, false, 151)),
  (some (false, false, 78), some (true, false, 81)),
  (some (false, false, 18), some (true, false, 92)),
  (some (false, true, 117), some (true, false, 152)),
  (some (false, false, 80), some (true, false, 6)),
  (some (false, false, 153), some (true, false, 154)),
  (some (false, false, 155), some (true, false, 156)),
  (some (false, false, 157), some (true, false, 143)),
  (some (true, true, 127), some (true, false, 151)),
  (some (false, false, 32), some (true, false, 55)),
  (some (true, true, 117), some (true, true, 95)),
  (some (false, false, 158), some (true, false, 159)),
  (some (false, false, 160), some (true, false, 161)),
  (some (false, false, 162), some (true, false, 155)),
  (some (true, true, 90), some (true, false, 163)),
  (some (true, true, 55), some (true, false, 164)),
  (some (false, false, 16), some (true, false, 165)),
  (some (true, true, 127), some (true, false, 90)),
  (some (false, false, 162), some (false, false, 36)),
  (some (false, false, 166), some (true, false, 167)),
  (some (false, false, 192), some (true, false, 156)),
  (some (false, false, 110), some (true, false, 168)),
  (some (false, false, 169), some (true, false, 170)),
  (some (false, false, 171), some (false, false, 70)),
  (some (false, false, 77), some (true, false, 64)),
  (some (false, false, 172), some (true, false, 173)),
  (some (true, true, 90), some (true, false, 174)),
  (some (false, false, 175), some (true, false, 176)),
  (some (true, true, 127), some (false, false, 103)),
  (some (false, false, 177), some (true, false, 178)),
  (some (false, false, 90), some (false, false, 42)),
  (some (false, false, 179), some (false, false, 91)),
  (some (false, false, 180), some (true, false, 28)),
  (some (false, false, 181), some (false, false, 70)),
  (some (false, true, 32), some (false, false, 102)),
  (some (false, false, 182), some (true, false, 20)),
  (some (false, false, 183), some (true, false, 1)),
  (some (false, false, 10), some (true, false, 156)),
  (some (false, false, 123), some (true, false, 184)),
  (some (false, false, 98), some (true, false, 185)),
  (some (false, false, 186), some (true, false, 187)),
  (some (false, false, 94), some (true, false, 188)),
  (some (false, false, 189), some (true, false, 138)),
  (some (false, false, 112), some (true, false, 25)),
  (some (false, false, 190), some (true, false, 149)),
  (some (false, false, 191), some (true, false, 147)),
  (some (false, false, 115), some (true, false, 140))
]

section InternalSets
variable {V : Type} (E : V → V → Prop)
def Step (s t : Conf V) : Prop :=
 Valid E s ∧ Valid E t ∧ ∃ q : Fin 192, Numeral E q.val s.q ∧
 ∃ read write direction next,
 (if read then (literalRows.getD q.val (none,none)).2 else (literalRows.getD q.val (none,none)).1) = some (write,direction,next) ∧
 Move E read write direction next s t
/-- This finite condition matches no outgoing row: both entries of every
in-range row are defined. It requires a separate exact-row totality proof. -/
def Terminal (s : Conf V) : Prop := ∀ q : Fin 192, ¬ Numeral E q.val s.q
def NumericStep (before after : V) : Prop :=
 ∃ s t : Conf V, NumericConfCode E s before ∧ NumericConfCode E t after ∧ Step E s t
def RunEdge (initial next tail : V) : Prop :=
 (Empty E tail ∧ next = initial) ∨
 (¬ Empty E tail ∧ ∃ previous, ListHead E tail previous ∧ NumericStep E previous next)
/-- Preferred production-aligned representation. The iterator f is an
internal set function on successor(code), NOT an external recursive function.
Every nonzero tail encountered before code steps has a correct run edge. -/
def LinkedRun (initial code : V) : Prop :=
 NatObject E initial ∧ NatObject E code ∧ ¬ Empty E code ∧
 ∃ zero domain f, Empty E zero ∧ Succ E code domain ∧ FunctionOn E f domain ∧
 At E f zero code ∧ At E f code zero ∧
 (∀ i x, E i domain → At E f i x → NatObject E x) ∧
 ∀ i, E i code → ∃ j x y, Succ E i j ∧ At E f i x ∧ At E f j y ∧
 ListTail E x y ∧ (Empty E x ∨ ∃ a b, ListHead E x a ∧ ListTail E x b ∧ RunEdge E initial a b)
def InternalLinkedHalts : Prop :=
 ∃ zero hist last, ∃ (t : Conf V), Empty E zero ∧ LinkedRun E zero hist ∧
 ListHead E hist last ∧ NumericConfCode E t last ∧ Valid E t ∧ Terminal E t
end InternalSets
end PalomarZF192History

namespace PalomarZF192Theory
inductive Formula where
 | bot : Formula
 | mem : Nat → Nat → Formula
 | eq : Nat → Nat → Formula
 | and : Formula → Formula → Formula
 | or : Formula → Formula → Formula
 | imp : Formula → Formula → Formula
 | all : Formula → Formula
 | ex : Formula → Formula
 deriving DecidableEq, Repr

def lift (σ : Nat → Nat) : Nat → Nat
 | 0 => 0
 | n+1 => σ n + 1

def rename (σ : Nat → Nat) : Formula → Formula
 | .bot => .bot
 | .mem i j => .mem (σ i) (σ j)
 | .eq i j => .eq (σ i) (σ j)
 | .and a b => .and (rename σ a) (rename σ b)
 | .or a b => .or (rename σ a) (rename σ b)
 | .imp a b => .imp (rename σ a) (rename σ b)
 | .all a => .all (rename (lift σ) a)
 | .ex a => .ex (rename (lift σ) a)


def shift (a:Formula) := rename Nat.succ a
def substMap (t:Nat) : Nat→Nat | 0=>t | n+1=>n
def subst (t:Nat) (a:Formula) := rename (substMap t) a

def Bound : Formula → Nat → Prop
  | .bot, _ => True
  | .mem i j, n => i < n ∧ j < n
  | .eq i j, n => i < n ∧ j < n
  | .and p q, n => Bound p n ∧ Bound q n
  | .or p q, n => Bound p n ∧ Bound q n
  | .imp p q, n => Bound p n ∧ Bound q n
  | .all p, n => Bound p (n+1)
  | .ex p, n => Bound p (n+1)


universe u
/-- Interpretation of a de Bruijn assignment after pushing an eigenvariable. -/
def pushValue {α : Type u} (s : Nat → α) (x : α) : Nat → α
  | 0 => x
  | n + 1 => s n

def eval {α : Type u} (mem : α → α → Prop) : Formula → (Nat → α) → Prop
  | .bot, _ => False
  | .mem i j, s => mem (s i) (s j)
  | .eq i j, s => s i = s j
  | .and p q, s => eval mem p s ∧ eval mem q s
  | .or p q, s => eval mem p s ∨ eval mem q s
  | .imp p q, s => eval mem p s → eval mem q s
  | .all p, s => ∀ x, eval mem p (pushValue s x)
  | .ex p, s => ∃ x, eval mem p (pushValue s x)


abbrev Context := List Formula

def ContextSub (Γ Δ : Context) : Prop := ∀ a, a ∈ Γ → a ∈ Δ
inductive Row where
 | seq : Context → Formula → Row
 | branches : Context → Formula → Formula → Formula → Row
 deriving DecidableEq, Repr


def shiftContext (Γ:Context):=Γ.map shift

inductive ND : Row → Prop where
 | ctx {Γ a} : a ∈ Γ → ND (.seq Γ a)
 | pc (Γ a b) : ND (.seq Γ (.imp (.imp (.imp a b) a) a))
 | ii {Γ a b} : ND (.seq (a :: Γ) b) → ND (.seq Γ (.imp a b))
 | ie {Γ a b} : ND (.seq Γ (.imp a b)) → ND (.seq Γ a) → ND (.seq Γ b)
 | exp {Γ a} : ND (.seq Γ .bot) → ND (.seq Γ a)
 | ci {Γ a b} : ND (.seq Γ a) → ND (.seq Γ b) → ND (.seq Γ (.and a b))
 | ce1 {Γ a b} : ND (.seq Γ (.and a b)) → ND (.seq Γ a)
 | ce2 {Γ a b} : ND (.seq Γ (.and a b)) → ND (.seq Γ b)
 | di1 {Γ a b} : ND (.seq Γ a) → ND (.seq Γ (.or a b))
 | di2 {Γ a b} : ND (.seq Γ b) → ND (.seq Γ (.or a b))
 | branchPair {Γ a b c} : ND (.seq (a :: Γ) c) → ND (.seq (b :: Γ) c) → ND (.branches Γ a b c)
 | de {Γ a b c} : ND (.seq Γ (.or a b)) → ND (.branches Γ a b c) → ND (.seq Γ c)
 | wk {Γ Δ a} : ContextSub Γ Δ → ND (.seq Γ a) → ND (.seq Δ a)
 | allI {Γ a} : ND (.seq (shiftContext Γ) a) → ND (.seq Γ (.all a))
 | allE {Γ a} (t : Nat) : ND (.seq Γ (.all a)) → ND (.seq Γ (subst t a))
 | exI {Γ a} (t : Nat) : ND (.seq Γ (subst t a)) → ND (.seq Γ (.ex a))
 | exE {Γ a c} : ND (.seq Γ (.ex a)) → ND (.seq (a :: shiftContext Γ) (shift c)) → ND (.seq Γ c)


def fixedRefl : Formula := (.all (.eq 0 0))

def fixedSym : Formula := (.all (.all (.imp (.eq 1 0) (.eq 0 1))))

def fixedTrans : Formula := (.all (.all (.all (.imp (.eq 2 1) (.imp (.eq 1 0) (.eq 2 0))))))

def fixedEqElem : Formula := (.all (.all (.all (.all (.imp (.eq 3 1) (.imp (.eq 2 0) (.imp (.mem 3 2) (.mem 1 0))))))))

def fixedExt : Formula := (.all (.all (.imp (.all (.imp (.mem 0 2) (.mem 0 1))) (.imp (.all (.imp (.mem 0 1) (.mem 0 2))) (.eq 1 0)))))

def fixedEmpty : Formula := (.ex (.all (.imp (.mem 0 1) (.bot))))

def fixedPair : Formula := (.all (.all (.ex (.all (.and (.imp (.mem 0 1) (.or (.eq 0 3) (.eq 0 2))) (.imp (.or (.eq 0 3) (.eq 0 2)) (.mem 0 1)))))))

def fixedUnion : Formula := (.all (.ex (.all (.and (.imp (.mem 0 1) (.ex (.and (.mem 0 3) (.mem 1 0)))) (.imp (.ex (.and (.mem 0 3) (.mem 1 0))) (.mem 0 1))))))

def fixedPower : Formula := (.all (.ex (.all (.and (.imp (.mem 0 1) (.all (.imp (.mem 0 1) (.mem 0 3)))) (.imp (.all (.imp (.mem 0 1) (.mem 0 3))) (.mem 0 1))))))

def fixedOmega : Formula := (.ex (.and (.and (.ex (.and (.all (.imp (.mem 0 1) (.bot))) (.mem 0 1))) (.all (.imp (.mem 0 1) (.ex (.and (.all (.and (.imp (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))) (.imp (.or (.mem 0 2) (.eq 0 2)) (.mem 0 1)))) (.mem 0 2)))))) (.all (.imp (.and (.ex (.and (.all (.imp (.mem 0 1) (.bot))) (.mem 0 1))) (.all (.imp (.mem 0 1) (.ex (.and (.all (.and (.imp (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))) (.imp (.or (.mem 0 2) (.eq 0 2)) (.mem 0 1)))) (.mem 0 2)))))) (.all (.imp (.mem 0 2) (.mem 0 1)))))))

def fixedFoundation : Formula := (.all (.imp (.ex (.mem 0 1)) (.ex (.and (.mem 0 1) (.all (.imp (.mem 0 1) (.imp (.mem 0 2) (.bot))))))))


def sourceIff (a b : Formula) := Formula.and (.imp a b) (.imp b a)
def separationFormula (body : Formula) := Formula.all (.ex (.all
 (sourceIff (.mem 0 1) (.and (.mem 0 2) body))))
def functionalityFormula (a b : Formula) := Formula.all (.all (.all
 (.imp a (.imp b (.eq 1 0)))))
def replacementFormula (a b c : Formula) := Formula.imp (functionalityFormula a b)
 (.all (.ex (.all (sourceIff (.mem 0 1) (.ex (.and (.mem 0 3) c))))))
def allPrefix : Nat → Formula → Formula
 | 0, a => a
 | n+1, a => .all (allPrefix n a)

def sepIndex (i : Nat) := if i=0 then 0 else i+2
def repAIndex (i : Nat) := if i=0 then 2 else if i=1 then 1 else i+1
def repBIndex (i : Nat) := if i=0 then 2 else if i=1 then 0 else i+1
def repCIndex (i : Nat) := if i=0 then 0 else if i=1 then 1 else i+2

def separationSchema (n : Nat) (phi : Formula) := allPrefix n (separationFormula (rename sepIndex phi))
def replacementSchema (n : Nat) (phi : Formula) := allPrefix n
 (replacementFormula (rename repAIndex phi) (rename repBIndex phi) (rename repCIndex phi))


/-- All fixed axioms, including logical equality, omega, and foundation. -/
def FixedAxiom (p:Formula):Prop:=
 p=fixedRefl ∨ p=fixedSym ∨ p=fixedTrans ∨ p=fixedEqElem ∨ p=fixedExt ∨
 p=fixedEmpty ∨ p=fixedPair ∨ p=fixedUnion ∨ p=fixedPower ∨ p=fixedOmega ∨ p=fixedFoundation
/-- Full standard schemas, with arbitrary finite parameter lists. -/
def Axiom (p:Formula):Prop:= FixedAxiom p ∨
 (∃ n body,Bound body (n+1) ∧ p=separationSchema n body) ∨
 (∃ n body,Bound body (n+2) ∧ p=replacementSchema n body)
def Provable (p:Formula):Prop:=∃Γ:Context,(∀q,q∈Γ→Axiom q) ∧ ND (.seq Γ p)
def Consistent:Prop:=¬Provable .bot
def Closed (p:Formula):Prop:=Bound p 0
def Neg (p:Formula):Formula:=.imp p .bot
/-- Nonemptiness is separately required at every quantified model use. -/
def Model {V:Type} (E:V→V→Prop):Prop:=∀p,Axiom p→∀s:Nat→V,eval E p s
end PalomarZF192Theory

namespace PalomarZF192Theory
inductive ArithTerm where
 | zero | one
 | var (index:Nat)
 | add (left right:ArithTerm)
 | mul (left right:ArithTerm)
inductive SigmaFormula where
 | atom (left right:ArithTerm) (equality positive:Bool)
 | conj (left right:SigmaFormula)
 | disj (left right:SigmaFormula)
 | exists_ (body:SigmaFormula)
 | forallLt (bound:ArithTerm) (body:SigmaFormula)
def ArithTerm.bound : ArithTerm→Nat→Prop
 | .zero,_ | .one,_=>True
 | .var i,n=>i<n
 | .add p q,n | .mul p q,n=>p.bound n ∧ q.bound n
def SigmaFormula.bound : SigmaFormula→Nat→Prop
 | .atom p q _ _,n=>p.bound n ∧ q.bound n
 | .conj p q,n | .disj p q,n=>p.bound n ∧ q.bound n
 | .exists_ p,n=>p.bound (n+1)
 | .forallLt t p,n=>t.bound n ∧ p.bound (n+1)
def ArithTerm.natValue : ArithTerm→(Nat→Nat)→Nat
 | .zero,_=>0 | .one,_=>1 | .var i,s=>s i
 | .add p q,s=>p.natValue s+q.natValue s
 | .mul p q,s=>p.natValue s*q.natValue s
def SigmaFormula.natEval : SigmaFormula→(Nat→Nat)→Prop
 | .atom p q eq pos,s=>
   let P:=if eq then p.natValue s=q.natValue s else p.natValue s<q.natValue s
   if pos then P else ¬P
 | .conj p q,s=>p.natEval s ∧ q.natEval s
 | .disj p q,s=>p.natEval s ∨ q.natEval s
 | .exists_ p,s=>∃x:Nat,p.natEval (pushValue s x)
 | .forallLt b p,s=>∀x:Nat,x<b.natValue s→p.natEval (pushValue s x)
open PalomarZF192Arithmetic
/-- Fully relational evaluation, including arithmetic internal to a ZF model. -/
def ArithTerm.graph {V:Type} (E:V→V→Prop):ArithTerm→(Nat→V)→V→Prop
 | .zero,_,z=>Numeral E 0 z
 | .one,_,z=>Numeral E 1 z
 | .var i,s,z=>NatObject E z ∧ z=s i
 | .add p q,s,z=>∃a b,p.graph E s a ∧ q.graph E s b ∧ Add E a b z
 | .mul p q,s,z=>∃a b,p.graph E s a ∧ q.graph E s b ∧ Mul E a b z
def SigmaFormula.internalEval {V:Type} (E:V→V→Prop):SigmaFormula→(Nat→V)→Prop
 | .atom p q eq pos,s=>∃a b,p.graph E s a ∧ q.graph E s b ∧
   (if pos then (if eq then a=b else E a b) else ¬(if eq then a=b else E a b))
 | .conj p q,s=>p.internalEval E s ∧ q.internalEval E s
 | .disj p q,s=>p.internalEval E s ∨ q.internalEval E s
 | .exists_ p,s=>∃x:V,NatObject E x ∧ p.internalEval E (pushValue s x)
 | .forallLt b p,s=>∃bound,b.graph E s bound ∧
   ∀x:V,NatObject E x→E x bound→p.internalEval E (pushValue s x)
/-- Correct arithmetic meaning in ALL ZF models, not just well-founded or
omega-standard models. Both syntax objects are fixed finite external syntax. -/
def RepresentsArithmetic (φ:SigmaFormula) (ψ:Formula):Prop:=
 Closed ψ ∧ ∀(V:Type) (E:V→V→Prop),Nonempty V→Model E→
 ∀(s env:Nat→V),(∀i,NatObject E (env i))→(eval E ψ s ↔ φ.internalEval E env)
/-- Arithmetic Σ₁-soundness for closed formulas in the standalone syntax.
The solution proves that this hypothesis implies Σ₁-soundness for
Foundation's formalization of ZF with arithmetic interpreted in ω. -/
def ArithmeticSigma1Sound:Prop:=
 ∀φ:SigmaFormula,φ.bound 0→∀ψ:Formula,RepresentsArithmetic φ ψ→
 Provable ψ→∀s:Nat→Nat,φ.natEval s
end PalomarZF192Theory

namespace BinaryTape
abbrev TMN := Nat → Bool → Option (Bool × Bool × Nat)

/-- Drop trailing blanks. -/
def trim : List Bool → List Bool
  | [] => []
  | b :: l => if b = false ∧ trim l = [] then [] else b :: trim l

/-- A configuration: state, left side (read leftwards), right side starting at the head. -/
structure Conf where
  q : Nat
  l : List Bool
  r : List Bool
  deriving DecidableEq, Repr

def zc (q : Nat) (l r : List Bool) : Conf := ⟨q, trim l, trim r⟩

def zl (q : Nat) (l r : List Bool) : Conf := zc q l.tail (l.headD false :: r)

def step (M : TMN) (c : Conf) : Option Conf :=
  match M c.q (c.r.headD false) with
  | none => none
  | some (w, true, q') => some (zc q' (w :: c.l) c.r.tail)
  | some (w, false, q') => some (zl q' c.l (w :: c.r.tail))

def run (M : TMN) : Nat → Conf → Option Conf
  | 0, c => some c
  | k + 1, c => match step M c with
    | none => none
    | some c' => run M k c'

/-- `c` reaches `c'` in some number of steps. -/
def Reach (M : TMN) (c c' : Conf) : Prop := ∃ k, run M k c = some c'

/-- `c` reaches `c'` in at least one step. -/
def Reach1 (M : TMN) (c c' : Conf) : Prop := ∃ k, run M (k + 1) c = some c'

/-- `c` halts: it reaches a configuration with no row. -/
def Halts (M : TMN) (c : Conf) : Prop := ∃ c', Reach M c c' ∧ step M c' = none

end BinaryTape

namespace PalomarZF192
open PalomarZF192Theory

/-- The standalone transition table, read as a two-sided binary machine. -/
def machine : BinaryTape.TMN := fun q read =>
  let rows := PalomarZF192History.literalRows.getD q (none, none)
  if read then rows.2 else rows.1

/-- The sentence means blank-tape halting of the exact table in every ZF model. -/
def Represents192 (H : Formula) : Prop :=
  Closed H ∧ ∀ (V : Type) (E : V → V → Prop), Nonempty V → Model E →
  ∀ s : Nat → V, eval E H s ↔ PalomarZF192History.InternalLinkedHalts E

/-- Conditional independence of the exact machine's blank-tape halting. -/
def Exact192Claim : Prop := ∃ H : Formula, Represents192 H ∧
  (Consistent → ¬ Provable (Neg H)) ∧
  (ArithmeticSigma1Sound → (¬ Provable H) ∧ (¬ Provable (Neg H)))

end PalomarZF192


