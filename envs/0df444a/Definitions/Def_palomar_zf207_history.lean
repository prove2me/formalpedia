-- Prove2me | Definitions.Def_palomar_zf207_history
-- name    : palomar_zf207_history
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T17:13:49.177117+00:00
-- url     : https://prove2.me/theorems/ad83400b-f224-4874-b102-251ffe9e8f1f
-- title:
--   ZF207: literal 207-state table and model-internal halting
-- statement:
--   This bundle fixes the machine and the model-internal meaning of its halting, exactly as in the standalone statement of the ZF207 package.
--
--   **The literal table.** `PalomarZF207History.literalRows` is the transition table of a binary Turing machine with working states $0,\ldots,206$ and halt label $207$: entry $q$ is the pair of rows for reading $0$ and reading $1$ in state $q$, each row `some (write, direction, next)` giving the symbol written, the move (`true` = right), and the next state. The initial state is $0$.
--
--   **Internal set primitives.** Over a domain $V$ with membership relation $E$, the bundle defines relationally: `Empty`, `Succ`, `Pair`, `OrderedPair`, `At` (application of an internal function), `FunctionOn` (an internal function with a given domain, both objects of the model), `Inductive`, `Omega`, `NatObject` (member of the model's $\omega$), `Numeral` (the standard finite numerals), and `Add`, `Mul` given by internal finite recursion — meaningful also at nonstandard lengths.
--
--   **Configurations and steps.** A configuration `Conf` holds the state and two tape halves as natural objects; `BitCons` expresses $y = b + 2x$ internally; `Move` and `Step` implement one table step; `Terminal` says the state is none of $0,\ldots,206$.
--
--   **Histories.** `Cantor` is the pairing $2z=(a+b)(a+b+1)+2b$; `ListCons`, `ListHead`, `ListTail` code finite lists; `NumericConfCode` codes a configuration as $\langle q,\langle \mathrm{left},\mathrm{right}\rangle\rangle$; `LinkedRun` asserts an internal set-function iterator on the successor of the code whose successive values form a run from the blank configuration; `InternalLinkedHalts` asserts such a run ending in a terminal configuration. All witnesses are model objects, so the predicate is meaningful in every ZF model, including models with nonstandard natural numbers.
-- source:
--   James Chang, 'Nonhalting and ZF-independence for a 207-state Turing machine' (2026), §2 (The machine), §6 (The internal premise); standalone definitions https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Challenge.lean#L4-L312 (production module Palomar207HistoryDefinition.lean); literal table https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/data/zf207.tm

/- Source: https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Challenge.lean#LL4-L312
   Machine table and model-internal halting; production module Palomar207HistoryDefinition.lean. -/
/-! Standalone exact207 mathematical definitions. The corresponding completed
Solution proves PalomarZF207.exact207Claim. This file and Solution are compiled
in separate environments; Solution must not import Challenge. -/
namespace PalomarZF207History
abbrev Row := Option (Bool × Bool × Nat)
def literalRows : List (Row × Row) := [
  (some (true, true, 1), some (true, true, 60)),
  (some (true, true, 81), some (true, true, 1)),
  (some (false, false, 2), some (true, false, 3)),
  (some (false, false, 4), some (true, false, 3)),
  (some (false, false, 6), some (true, false, 3)),
  (some (true, true, 7), some (false, false, 5)),
  (some (false, false, 9), some (true, false, 3)),
  (some (false, true, 7), some (false, true, 10)),
  (some (false, true, 13), some (true, true, 12)),
  (some (false, false, 14), some (true, false, 3)),
  (some (false, false, 15), some (false, true, 10)),
  (some (false, true, 16), some (true, true, 17)),
  (some (false, false, 78), some (true, false, 30)),
  (some (false, false, 45), some (false, true, 21)),
  (some (false, false, 22), some (true, false, 3)),
  (some (true, false, 2), some (false, false, 2)),
  (some (false, true, 23), some (false, true, 31)),
  (some (false, true, 83), some (false, false, 94)),
  (some (false, true, 27), some (true, true, 28)),
  (some (false, true, 29), some (true, true, 30)),
  (some (false, true, 23), some (false, true, 56)),
  (some (false, true, 32), some (true, true, 21)),
  (some (false, false, 33), some (true, false, 3)),
  (some (false, false, 34), some (false, true, 1)),
  (some (false, true, 35), some (true, true, 24)),
  (some (false, true, 76), some (true, true, 53)),
  (some (false, true, 37), some (false, false, 38)),
  (some (false, true, 39), some (true, true, 40)),
  (some (false, true, 41), some (true, true, 42)),
  (some (false, true, 43), some (true, true, 44)),
  (some (false, true, 20), some (true, true, 45)),
  (some (false, true, 46), some (true, true, 31)),
  (some (false, true, 31), some (true, true, 32)),
  (some (false, false, 68), some (true, false, 3)),
  (some (true, true, 34), some (true, false, 2)),
  (some (false, true, 48), some (true, true, 35)),
  (some (false, true, 27), some (true, true, 19)),
  (some (false, false, 45), some (false, true, 35)),
  (some (false, false, 5), some (true, false, 50)),
  (some (false, true, 23), some (false, true, 24)),
  (some (false, true, 12), some (false, false, 15)),
  (some (false, true, 52), some (true, true, 53)),
  (some (false, true, 54), some (true, true, 55)),
  (some (false, false, 44), some (false, true, 51)),
  (some (false, false, 25), some (true, true, 58)),
  (some (false, true, 43), some (true, false, 25)),
  (some (false, true, 24), some (true, true, 46)),
  (some (false, false, 34), some (false, true, 60)),
  (some (false, true, 15), some (true, true, 48)),
  (some (false, true, 62), some (true, true, 63)),
  (some (false, false, 38), some (true, false, 50)),
  (some (false, true, 21), some (true, true, 51)),
  (some (false, false, 45), some (false, true, 48)),
  (some (false, true, 57), some (false, false, 15)),
  (some (false, true, 64), some (true, true, 65)),
  (some (false, true, 58), some (true, true, 66)),
  (some (false, true, 51), some (true, true, 56)),
  (some (false, true, 47), some (false, true, 24)),
  (some (false, false, 27), some (true, false, 67)),
  (some (false, false, 101), some (true, false, 29)),
  (some (false, true, 0), some (true, true, 60)),
  (some (true, true, 123), some (true, false, 50)),
  (some (false, true, 69), some (true, true, 207)),
  (some (false, false, 124), some (true, true, 30)),
  (some (false, true, 39), some (true, true, 59)),
  (some (false, false, 78), some (true, true, 70)),
  (some (false, true, 52), some (true, false, 71)),
  (some (false, true, 72), some (true, true, 73)),
  (some (false, true, 68), some (true, true, 74)),
  (some (false, true, 75), some (true, true, 76)),
  (some (false, true, 78), some (true, false, 109)),
  (some (false, false, 97), some (true, true, 53)),
  (some (false, true, 47), some (false, true, 32)),
  (some (false, true, 80), some (false, false, 40)),
  (some (false, true, 49), some (true, true, 127)),
  (some (false, true, 45), some (true, true, 20)),
  (some (false, true, 100), some (true, true, 89)),
  (some (false, true, 91), some (true, true, 92)),
  (some (false, true, 72), some (true, true, 71)),
  (some (false, true, 90), some (true, true, 117)),
  (some (false, true, 94), some (true, true, 95)),
  (some (false, true, 61), some (false, true, 1)),
  (some (false, true, 26), some (true, true, 96)),
  (some (false, true, 88), some (true, true, 87)),
  (some (true, false, 98), some (true, false, 84)),
  (some (false, true, 18), some (true, true, 99)),
  (some (false, true, 57), some (true, true, 57)),
  (some (false, true, 115), some (true, true, 114)),
  (some (false, true, 16), some (true, true, 206)),
  (some (false, true, 94), some (false, false, 126)),
  (some (false, true, 101), some (true, true, 102)),
  (some (false, true, 66), some (true, true, 55)),
  (some (false, true, 54), some (true, true, 103)),
  (some (false, true, 20), some (true, true, 104)),
  (some (false, true, 20), some (false, false, 10)),
  (some (false, true, 58), some (true, true, 40)),
  (some (false, true, 105), some (true, true, 8)),
  (some (false, true, 90), some (true, true, 106)),
  (some (false, false, 126), some (false, false, 84)),
  (some (false, true, 107), some (true, true, 93)),
  (some (false, false, 108), some (false, false, 2)),
  (some (false, true, 37), some (true, true, 67)),
  (some (false, true, 58), some (true, true, 109)),
  (some (false, true, 58), some (true, true, 110)),
  (some (false, true, 65), some (false, false, 15)),
  (some (false, true, 13), some (true, true, 109)),
  (some (false, true, 20), some (true, true, 111)),
  (some (false, true, 112), some (true, false, 19)),
  (some (false, false, 36), some (true, true, 64)),
  (some (false, true, 37), some (true, false, 107)),
  (some (false, true, 119), some (false, false, 15)),
  (some (false, true, 113), some (false, false, 15)),
  (some (false, true, 23), some (false, true, 46)),
  (some (false, true, 47), some (false, true, 31)),
  (some (false, true, 69), some (true, true, 85)),
  (some (false, true, 124), some (true, true, 27)),
  (some (false, true, 120), some (true, true, 106)),
  (some (false, true, 93), some (true, true, 85)),
  (some (false, true, 82), some (true, true, 97)),
  (some (false, true, 86), some (true, true, 86)),
  (some (false, true, 16), some (true, false, 108)),
  (some (false, true, 69), some (true, true, 100)),
  (some (false, true, 95), some (true, true, 107)),
  (some (true, false, 38), some (true, false, 98)),
  (some (false, true, 79), some (true, true, 77)),
  (some (false, true, 118), some (true, true, 128)),
  (some (false, false, 5), some (false, false, 126)),
  (some (false, true, 125), some (true, true, 58)),
  (some (false, true, 11), some (true, true, 36)),
  (some (false, true, 18), some (true, true, 19)),
  (some (false, true, 77), some (true, true, 86)),
  (some (false, true, 85), some (true, true, 130)),
  (some (false, true, 129), some (true, true, 131)),
  (some (false, false, 158), some (true, true, 77)),
  (some (false, false, 168), some (true, true, 133)),
  (some (false, true, 18), some (true, true, 116)),
  (some (false, true, 135), some (true, true, 133)),
  (some (false, true, 133), some (true, false, 172)),
  (some (false, true, 57), some (true, true, 77)),
  (some (false, true, 18), some (true, true, 138)),
  (some (false, false, 195), some (true, true, 139)),
  (some (false, true, 139), some (true, true, 140)),
  (some (false, true, 137), some (true, true, 134)),
  (some (false, true, 136), some (true, true, 142)),
  (some (false, true, 135), some (true, true, 130)),
  (some (false, true, 129), some (true, true, 144)),
  (some (false, true, 131), some (true, true, 132)),
  (some (false, true, 144), some (true, true, 77)),
  (some (false, false, 146), some (true, false, 182)),
  (some (false, true, 148), some (true, true, 57)),
  (some (false, true, 129), some (true, true, 149)),
  (some (false, true, 147), some (true, true, 150)),
  (some (false, false, 173), some (true, true, 151)),
  (some (false, true, 145), some (true, true, 152)),
  (some (false, true, 143), some (true, true, 153)),
  (some (false, true, 134), some (true, true, 154)),
  (some (false, true, 124), some (true, true, 155)),
  (some (false, false, 189), some (true, true, 156)),
  (some (false, true, 157), some (true, true, 145)),
  (some (false, true, 135), some (true, false, 151)),
  (some (false, false, 182), some (true, true, 159)),
  (some (false, true, 137), some (true, true, 57)),
  (some (false, true, 160), some (true, true, 161)),
  (some (false, true, 162), some (true, true, 136)),
  (some (false, true, 163), some (true, true, 162)),
  (some (false, true, 158), some (true, true, 164)),
  (some (false, true, 85), some (true, true, 165)),
  (some (false, true, 141), some (true, true, 159)),
  (some (false, true, 166), some (true, true, 167)),
  (some (false, true, 129), some (true, true, 168)),
  (some (false, true, 63), some (true, true, 169)),
  (some (false, true, 57), some (true, true, 136)),
  (some (false, true, 146), some (true, true, 161)),
  (some (false, true, 171), some (true, true, 172)),
  (some (false, true, 170), some (true, true, 173)),
  (some (false, true, 174), some (true, true, 132)),
  (some (false, true, 132), some (true, true, 175)),
  (some (false, true, 129), some (true, true, 137)),
  (some (false, true, 177), some (true, true, 160)),
  (some (false, true, 147), some (true, true, 178)),
  (some (false, true, 150), some (true, true, 179)),
  (some (false, true, 152), some (true, true, 180)),
  (some (false, true, 138), some (true, true, 144)),
  (some (false, true, 136), some (true, true, 182)),
  (some (false, true, 135), some (true, true, 177)),
  (some (false, true, 139), some (true, true, 77)),
  (some (false, true, 185), some (true, true, 148)),
  (some (false, true, 184), some (true, true, 186)),
  (some (false, false, 204), some (true, true, 187)),
  (some (false, true, 188), some (true, true, 186)),
  (some (false, true, 183), some (true, true, 189)),
  (some (false, true, 181), some (true, true, 190)),
  (some (false, false, 195), some (true, true, 185)),
  (some (false, true, 77), some (true, true, 192)),
  (some (false, true, 131), some (true, true, 186)),
  (some (false, true, 193), some (true, true, 194)),
  (some (false, true, 191), some (true, true, 195)),
  (some (false, true, 192), some (true, true, 147)),
  (some (false, true, 140), some (true, true, 120)),
  (some (false, true, 121), some (false, false, 126)),
  (some (false, true, 122), some (true, true, 199)),
  (some (false, true, 121), some (true, true, 200)),
  (some (false, true, 198), some (true, true, 201)),
  (some (false, true, 197), some (true, true, 202)),
  (some (false, false, 188), some (true, true, 203)),
  (some (false, true, 196), some (true, true, 204)),
  (some (false, true, 176), some (true, true, 205))
]
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
/-- All 207 rows are fixed above. The initial state is 0, not a supplied parameter. -/
def Step (s t : Conf V) : Prop :=
 Valid E s ∧ Valid E t ∧ ∃ q : Fin 207, Numeral E q.val s.q ∧
 ∃ read write direction next,
 (if read then (literalRows.getD q.val (none,none)).2 else (literalRows.getD q.val (none,none)).1) = some (write,direction,next) ∧
 Move E read write direction next s t
/-- This finite condition matches no outgoing row: both entries of every
in-range row are defined. It requires a separate exact-row totality proof. -/
def Terminal (s : Conf V) : Prop := ∀ q : Fin 207, ¬ Numeral E q.val s.q
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
/-- Primary proposed Challenge operational predicate. The equivalence with
production physicalHalts is a NEW proof obligation, not assumed here. -/
def InternalLinkedHalts : Prop :=
 ∃ zero hist last, ∃ (t : Conf V), Empty E zero ∧ LinkedRun E zero hist ∧
 ListHead E hist last ∧ NumericConfCode E t last ∧ Valid E t ∧ Terminal E t
end InternalSets
end PalomarZF207History


