-- Prove2me | Definitions.Def_EvenCycleListing723_Main_Execution
-- name    : EvenCycleListing723_Main_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:50.366544+00:00
-- url     : https://prove2.me/theorems/754eb803-b823-46fb-af10-6e34d89219fd
-- title:
--   Counted RAM execution and exact listing output
-- statement:
--   A program is a finite list of the published word-RAM instructions: unit arithmetic, direct and indirect memory access, conditional branches, and halting. Input is $n$ followed by the adjacency matrix in row-major order. Neither the number of cycles nor a cycle list is supplied. The output is its length followed by canonical lists of $2k$ vertex labels; output stores are ordinary charged instructions.
--
--   Let $\ell(n)=1+\lfloor\log_2(\max(2,n))\rfloor$. For positive constants $C,b$ and a natural exponent $q$, the required word width and time budget are
--
--   $$w\ge b\ell(n),\qquad B(C,q,n,s)=C(1+s)\ell(n)^q.$$
--
--   A successful run is an actual halting execution whose memory contains exactly the required listing. A deterministic procedure run additionally writes a perfect-family table and outputs the result of the specified BFS/color-coding procedure using that table. The family is constructed during the run, not provided as input. These are predicates on executions, with no assumed correctness or runtime facts.
--
--   The randomized interface supplies $R$ as a repetition control and a finite uniform palette tape; every tape read is a RAM operation and every padded draw is separately charged, adding $n^2R$ units. Its output must be the procedure's result for that exact tape. Signed output equality rules out wraparound decoding. Constants precede every graph, input size, word width, and tape. Mathematical ball, sorting and family functions are specifications to implement; they are never atomic machine instructions.
-- source:
--   Neha Pant and Virginia Vassilevska Williams, Listing Even Cycles Even Faster, STOC 2027 submission #723 (October 2026), pp.2,4–5, Theorem 1.1 and Lemma 3.1; finite-program word-RAM reading of the algorithmic convention; canonical PDF https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/723.pdf (SHA256 653ba349d1e9c1a87fe327137dddf959c6871a48cf5a052e91a47e341e9e9d8f)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_EvenCycleListing723_Main_Procedure

set_option autoImplicit false

namespace EvenCycleListing723.Main

noncomputable section

abbrev Program := List TrulySubcubicAPSP.Instr
abbrev Memory (W : ℕ) := ℤ → BitVec W

/-- Only n and its row-major adjacency matrix are given to the deterministic program.
The length k is fixed in the program. In particular neither t nor any cycle is input. -/
def graphInput {n : ℕ} (G : SimpleGraph (Fin n)) : List ℤ := by
  classical
  exact (n : ℤ) :: (List.ofFn fun u =>
    List.ofFn fun v => if G.Adj u v then (1 : ℤ) else 0).flatten

/-- Output memory is initially zero. Cell -1 holds the number of cycles, followed by
2k labels per cycle in cells -2,-3,... . Signed equality prevents overflow decoding. -/
def writesListing {n W : ℕ} (m : Memory W) (L : List (List (Fin n))) : Prop :=
  (m (-1)).toInt = (L.length : ℤ) ∧
    ∀ i (hi : i < L.flatten.length),
      (m (-((i : ℤ) + 2))).toInt = ((L.flatten[i]).val : ℤ)

/-- A family table is also written, after the adjacency matrix. It is not in the input. -/
def writesFamily {n W : ℕ} (m : Memory W) (k : ℕ)
    (F : List (Fin n → Fin (2 * k - 1))) : Prop :=
  (m ((n * n + 1 : ℕ) : ℤ)).toInt = (F.length : ℤ) ∧
    let table := (F.map fun f => List.ofFn fun v => (f v).val).flatten
    ∀ i (hi : i < table.length),
      (m ((n * n + 2 + i : ℕ) : ℤ)).toInt = (table[i] : ℤ)

/-- The halting instruction and every memory read, write and arithmetic operation count.
No bound is built into this relation. -/
def runFromInput (P : Program) (W t : ℕ) (input : List ℤ) (m : Memory W) : Prop :=
  TrulySubcubicAPSP.exec P t 0 (TrulySubcubicAPSP.loadWords W input) = some (true, m)

/-- Exact all-cycle output on an actual finite-program execution. -/
def haltsListing {n : ℕ} (P : Program) (k : ℕ) (G : SimpleGraph (Fin n)) (W t : ℕ) : Prop :=
  ∃ (m : Memory W) (L : List (List (Fin n))),
    runFromInput P W t (graphInput G) m ∧ writesListing m L ∧ correctListing G k L

/-- The deterministic Section 3 algorithm: its constructed family and its actual
output are checked against the explicit max-degree/BFS/pruning/DFS procedure.
Perfection and correctness are assertions to prove, not promises on the input. -/
def deterministicProcedureRun {n : ℕ} (P : Program) (k : ℕ) (G : SimpleGraph (Fin n))
    (W t : ℕ) (F : List (Fin n → Fin (2 * k - 1))) : Prop :=
  ∃ m : Memory W,
    runFromInput P W t (graphInput G) m ∧ writesFamily m k F ∧ isPerfectFamily k F ∧
    let L := listingProcedure G k (fun _ => familyColorings k F)
    writesListing m L ∧ correctListing G k L

/-- Random values are independent uniform palette words at every potential root,
repetition and vertex. Supplying R is a repetition control, independent of G's cycles. -/
def tapeWords {n k R : ℕ} (ω : RandomTape n k R) : List ℤ :=
  (List.ofFn fun u => (List.ofFn fun j =>
    List.ofFn fun v => ((ω u j v).val : ℤ)).flatten).flatten

def randomizedProcedureRun {n k R : ℕ} (P : Program) (G : SimpleGraph (Fin n))
    (ω : RandomTape n k R) (W t : ℕ) : Prop :=
  ∃ m : Memory W,
    runFromInput P W t (graphInput G ++ (R : ℤ) :: tapeWords ω) m ∧
    writesListing m (listingProcedure G k (randomColorings ω))

/-- One unit per uniform palette draw, including unused padded draws. All subsequent
reads and writes are counted by exec. This overhead is O_k,c(n² log n). -/
def randomDrawCost (n R : ℕ) : ℕ := n * R * n

def logarithmicSize (n : ℕ) : ℕ := 1 + Nat.log2 (max 2 n)
def requiredWidth (b n : ℕ) : ℕ := b * logarithmicSize n

/-- Uniform soft-O, with constants chosen before n and G; the additive one covers n=0,1. -/
def softBudget (C q n base : ℕ) : ℕ := C * (1 + base) * logarithmicSize n ^ q

end
end EvenCycleListing723.Main


