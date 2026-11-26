-- Prove2me | Definitions.Def_HennieStearnsWritableBuffer
-- name    : HennieStearnsWritableBuffer
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T17:17:45.42618+00:00
-- url     : https://prove2.me/theorems/489d4abd-23ee-469a-928d-6ee080b6e1a9
-- title:
--   Dyadic writable tape buffers
-- statement:
--   A writable tape buffer with a center symbol and dyadic layers, including its leftward and rightward movement, reference tape view, and cleanup traces.
-- source:
--   F. C. Hennie and R. E. Stearns, Two-Tape Simulation of Multitape Turing Machines, JACM 13(4), 533–546 (1966), §3, storage rearrangement and Lemmas 1–6, https://www.cs.toronto.edu/tss/files/papers/HennieStearns66.pdf. The submitted statement specifies the writable-buffer semantics and geometric charge independently of physical compilation.

import Mathlib.Data.List.Count
import Mathlib.Data.Nat.Size

set_option autoImplicit false

namespace PvsNP.HennieStearnsBuffer

/-- Ready at a level means its upper storage section is occupied on some
side. A cleanup clears both upper sections at lower levels. -/
def after (ready : ℕ → Bool) (level : ℕ) : ℕ → Bool :=
  fun i => if i < level then false else if i = level then true else ready i

/-- The schedule invariant used in the Hennie–Stearns charging argument.
Only a cleanup at a level can make that level ready for a larger cleanup. -/
def legal (ready : ℕ → Bool) : List ℕ → Prop
  | [] => True
  | level::tail => (∀ i < level, ready i = true) ∧ legal (after ready level) tail

def atLeast (i : ℕ) (orders : List ℕ) : ℕ := orders.countP (fun j => decide (i ≤ j))

def bill (orders : List ℕ) : ℕ := (orders.map (fun i => 2^i)).sum

/-- Storage areas below the selected level, in order out from the head. -/
def below : ℕ → List ℕ
  | 0 => []
  | i+1 => below i ++ [2^i]

/-- Fill consecutive areas from the nearest side, leaving the unshelved suffix. -/
def shelve {A : Type} : List ℕ → List A → List (List A) × List A
  | [], w => ([],w)
  | n::ns, w =>
    let next := shelve ns (w.drop n)
    (w.take n :: next.1,next.2)

structure Layer (A : Type) where
  left : List A
  right : List A

/-- Close to the head first. A layer contains two blocks in total, with
either zero, one, or two of them on the left. -/
def Layer.fits {A : Type} (length : ℕ) (level : Layer A) : Prop :=
  (level.left.length = 0 ∨ level.left.length = length ∨ level.left.length = 2*length) ∧
    level.left.length + level.right.length = 2*length

def place {A : Type} (lower : List (List A)) (upper : List (List A)) : List (Layer A) :=
  (lower.zip upper).map fun p => ⟨p.1,p.2⟩

def leftWord {A : Type} (layers : List (Layer A)) : List A :=
  (layers.map Layer.left).flatten

def rightWord {A : Type} (layers : List (Layer A)) : List A :=
  (layers.map Layer.right).flatten

structure Cleaned (A : Type) where
  center : A
  near : List (Layer A)
  selected : Layer A

/-- Move toward the left. All lower left areas start empty. A block from
the selected area supplies the new center and fills the lower left areas.
The old center joins the near right symbols, filling the lower right
areas and leaving one block to move into the selected area. -/
def slideLeft {A : Type} (i : ℕ) (center : A) (near : List (Layer A)) (selected : Layer A) :
    Cleaned A :=
  let front := selected.left.take (2^i)
  let left := shelve (below i) front.tail
  let right := shelve (below i) (center::rightWord near)
  ⟨front.headD center,place left.1 right.1,
    ⟨left.2 ++ selected.left.drop (2^i),right.2 ++ selected.right⟩⟩

/-- The upper area at the selected level can be filled or cleared.
The bookkeeping used for charging allows either transition. -/
def physicalAfter (ready : ℕ → Bool) (i : ℕ) (remains : Bool) : ℕ → Bool :=
  fun j => if j < i then false else if j = i then remains else ready j

def physicalSchedule (ready : ℕ → Bool) : List (ℕ × Bool) → Prop
  | [] => True
  | (i,remains)::tail =>
    (∀ j < i, ready j = true) ∧ physicalSchedule (physicalAfter ready i remains) tail

def sizesFrom (base : ℕ) : ℕ → List ℕ
  | 0 => []
  | n+1 => 2^base :: sizesFrom (base+1) n

def FitsFrom {A : Type} (base : ℕ) : List (Layer A) → Prop
  | [] => True
  | first::rest => first.fits (2^base) ∧ FitsFrom (base+1) rest

/-- The first area that supplies a symbol on the left. The initial prefix of
empty areas is retained in its original order. -/
def splitLeft {A : Type} : List (Layer A) → List (Layer A) × List (Layer A)
  | [] => ([],[])
  | l::rest =>
    if l.left.isEmpty then
      let result := splitLeft rest
      (l::result.1,result.2)
    else ([],l::rest)

def blankLayer {A : Type} (blank : A) (i : ℕ) : Layer A :=
  ⟨List.replicate (2^i) blank,List.replicate (2^i) blank⟩

structure Selection (A : Type) where
  near : List (Layer A)
  selected : Layer A
  far : List (Layer A)

def chooseLeft {A : Type} (blank : A) (layers : List (Layer A)) : Selection A :=
  let s := splitLeft layers
  ⟨s.1,s.2.headD (blankLayer blank s.1.length),s.2.tail⟩

def Selection.layers {A : Type} (s : Selection A) : List (Layer A) :=
  s.near++s.selected::s.far

structure TapeBuffer (A : Type) where
  center : A
  layers : List (Layer A)

structure Moved (A : Type) where
  tape : TapeBuffer A
  order : ℕ
  remains : Bool

def moveLeft {A : Type} (blank : A) (tape : TapeBuffer A) : Moved A :=
  let sel := chooseLeft blank tape.layers
  let i := sel.near.length
  let now := slideLeft i tape.center sel.near sel.selected
  ⟨⟨now.center,now.near++now.selected::sel.far⟩,i,
    decide (now.selected.left.length ≠ 2^i)⟩

def wordAt {A : Type} (blank : A) (word : List A) (i : ℕ) : A := word[i]?.getD blank

@[ext] structure Snapshot (A : Type) where
  center : A
  left : ℕ → A
  right : ℕ → A

def glimpse {A : Type} (blank : A) (tape : TapeBuffer A) : Snapshot A :=
  ⟨tape.center,wordAt blank (leftWord tape.layers),wordAt blank (rightWord tape.layers)⟩

def Snapshot.shiftLeft {A : Type} (s : Snapshot A) : Snapshot A :=
  ⟨s.left 0,fun i => s.left (i+1),fun i =>
    match i with | 0 => s.center | j+1 => s.right j⟩

def Snapshot.shiftRight {A : Type} (s : Snapshot A) : Snapshot A :=
  ⟨s.right 0,(fun i => match i with | 0 => s.center | j+1 => s.left j),
    fun i => s.right (i+1)⟩

def Layer.flip {A : Type} (l : Layer A) : Layer A := ⟨l.right,l.left⟩

def TapeBuffer.flip {A : Type} (tape : TapeBuffer A) : TapeBuffer A :=
  ⟨tape.center,tape.layers.map Layer.flip⟩

def Moved.flip {A : Type} (moved : Moved A) : Moved A :=
  ⟨moved.tape.flip,moved.order,moved.remains⟩

def Snapshot.flip {A : Type} (s : Snapshot A) : Snapshot A := ⟨s.center,s.right,s.left⟩

def moveRight {A : Type} (blank : A) (tape : TapeBuffer A) : Moved A :=
  (moveLeft blank tape.flip).flip

def levelFlags {A : Type} (base : ℕ) : List (Layer A) → List Bool
  | [] => []
  | area::rest => decide (area.left.length ≠ 2^base) :: levelFlags (base+1) rest

def readyAt {A : Type} (tape : TapeBuffer A) : ℕ → Bool :=
  wordAt false (levelFlags 0 tape.layers)

inductive Turn where
  | left | stay | right
  deriving DecidableEq

def snapshotStep {A : Type} (s : Snapshot A) (a : A) (dir : Turn) : Snapshot A :=
  let written := {s with center := a}
  match dir with
  | .left => written.shiftLeft
  | .stay => written
  | .right => written.shiftRight

def stepBuffer {A : Type} (blank : A) (tape : TapeBuffer A) (a : A) (dir : Turn) :
    TapeBuffer A × List (ℕ × Bool) :=
  let written := {tape with center := a}
  match dir with
  | .left =>
    let moved := moveLeft blank written
    (moved.tape,[(moved.order,moved.remains)])
  | .stay => (written,[])
  | .right =>
    let moved := moveRight blank written
    (moved.tape,[(moved.order,moved.remains)])

def runBuffer {A : Type} (blank : A) (tape : TapeBuffer A) :
    List (A × Turn) → TapeBuffer A × List (ℕ × Bool)
  | [] => (tape,[])
  | (a,dir)::rest =>
    let step := stepBuffer blank tape a dir
    let future := runBuffer blank step.1 rest
    (future.1,step.2++future.2)

def runSnapshot {A : Type} (tape : Snapshot A) (instructions : List (A × Turn)) : Snapshot A :=
  instructions.foldl (fun t instruction => snapshotStep t instruction.1 instruction.2) tape

def blankBuffer {A : Type} (blank : A) : TapeBuffer A := ⟨blank,[]⟩

end PvsNP.HennieStearnsBuffer


