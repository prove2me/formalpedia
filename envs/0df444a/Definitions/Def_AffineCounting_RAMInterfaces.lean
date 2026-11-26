-- Prove2me | Definitions.Def_AffineCounting_RAMInterfaces
-- name    : AffineCounting_RAMInterfaces
-- status  : Definition
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:16:48.423453+00:00
-- url     : https://prove2.me/theorems/6683ec18-ba3c-5232-a8ec-7ae375077214
-- title:
--   Binary affine systems with pinned variables on a RAM
-- statement:
--   Let $E$ be a finite list of affine equations over $\mathbb F_2$ on $n$ Boolean variables. A list of bits can fix a suffix of the variables by adjoining unit equations. The dense representation of $E$ contains one row of coefficients and a right-hand side per equation. Counts under successive restrictions define a rank order on the solutions.
--
--   The RAM interface specifies where the equations, fixed bits and scratch storage reside, the command used for a count, and the meaning of a polynomial bound for its running time and storage. These definitions allow one counting subroutine to implement both total counts and selection by rank.
-- source:
--   Auxiliary result for the log-cost RAM formalization of Proposition 4 in T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission 811, PDF pp. 5 and 8–11. https://prove2.me/theorems/aa04b14a-8225-48c8-904c-8725ebdcac66

import Definitions.Def_EditGV897_Main_Affine
import Definitions.Def_LogCostRAM_StructuredExecution

set_option autoImplicit false

section AffinePrefixEnumeration

/-! Output-sensitive enumeration of affine Boolean systems using the registered Gaussian counter. -/

namespace AffinePrefixEnumeration

open EditGV897.Main

def bitsWord (n : ℕ) (a : List Bool) : Word n := fun i => finTwoEquiv.symm (a[i.val]?.getD false)

/-- In the DFS, k low positions are free and p fixes the remaining positions. -/
def pins (n k : ℕ) (p : List Bool) : List (Equation n) :=
  List.ofFn fun j : Fin p.length => (unitWord n (k+j.val), finTwoEquiv.symm p[j.val])

def viable {n : ℕ} (E : List (Equation n)) (k : ℕ) (p : List Bool) : Bool :=
  decide (k+p.length = n) && decide (0 < affineCount (E ++ pins n k p))

end AffinePrefixEnumeration

end AffinePrefixEnumeration

section AffineQueryEncoding

namespace AffinePrefixEnumeration

open EditGV897.Main

/-- Output bits of one row, in the order used by the registered binary counter. -/
def rowPayload {n : ℕ} (e : Equation n) :=
  (List.ofFn fun i => decide (e.1 i ≠ 0)) ++ [decide (e.2 ≠ 0)]

end AffinePrefixEnumeration

end AffineQueryEncoding

section AffineRAMSerialize

namespace AffinePrefixEnumeration

open EditGV897.Main TargetedSamplers.Structured

def bitWord (b : Bool) : ℕ := symbolCode (some b)

def denseWords {n : ℕ} (E : List (Equation n)) := (E.flatMap rowPayload).map bitWord

end AffinePrefixEnumeration

end AffineRAMSerialize

section CountedUnranking

namespace BoundedEnumeration

/-- Retrieve one accepted word by counting the left child at each of the k remaining levels. -/
def unrank (count : ℕ → List Bool → ℕ) : ℕ → List Bool → ℕ → List Bool
  | 0,p,_ => p
  | k+1,p,i =>
    let left := count k (false::p)
    if i < left then unrank count k (false::p) i else unrank count k (true::p) (i-left)

end BoundedEnumeration

end CountedUnranking

section AffineRankEnumeration

namespace AffinePrefixEnumeration

open BoundedEnumeration EditGV897.Main

def rankedSolution {n : ℕ} (E : List (Equation n)) (i : ℕ) : List Bool :=
  unrank (fun k p => affineCount (E++pins n k p)) n [] i

end AffinePrefixEnumeration

end AffineRankEnumeration

section AffineRAMCountPort

namespace AffinePrefixEnumeration

open EditGV897.Main

open TargetedSamplers TargetedSamplers.Structured

/-- The caller keeps the query registers in a disjoint bank across Gaussian calls. -/
def installCount (bank : ℕ) : Fragment := Structured.sequence [
  .op (.const 2 0),.op (.add 0 (bank+0) 2),.op (.add 1 (bank+1) 2),.op (.add 6 (bank+6) 2),
  .op (.add 9 (bank+9) 2),.op (.add 10 (bank+10) 2),.op (.add 11 (bank+11) 2),
  .op (.add 12 (bank+12) 2),.op (.add 13 (bank+13) 2)]

def countPort (bank : ℕ) (kernel : Cmd) := Cmd.seq (installCount bank).cmd kernel

structure Port {n : ℕ} (E : List (Equation n)) (base row pin bank : ℕ) (s : Store) : Prop where
  target : s.mem (bank+0)=base
  dimension : s.mem (bank+1)=n
  pinEnd : s.mem (bank+10)=pin+n
  rows : s.mem (bank+11)=E.length
  firstRow : s.mem (bank+12)=row
  afterRows : s.mem (bank+13)=row+(denseWords E).length
  rowData : ∀ i (hi : i < (denseWords E).length), s.mem (row+i)=(denseWords E)[i]

end AffinePrefixEnumeration

end AffineRAMCountPort

section AffineRAMUnrank

namespace AffinePrefixEnumeration

open EditGV897.Main TargetedSamplers.Structured TargetedSamplers.Structured.RankedPrefix

open BoundedEnumeration

def chooseRank (bank : ℕ) : Cmd := .branch 4 (bank+17) (useTrue bank).cmd .skip

def walkRank (bank : ℕ) (counter : Cmd) : Cmd :=
  .whileGt (bank+6) (bank+14) (.seq (enterFalse bank).cmd (.seq (countPort bank counter) (chooseRank bank)))

end AffinePrefixEnumeration

end AffineRAMUnrank

section AffineRAMSolver

namespace AffinePrefixEnumeration

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.RankedPrefix EditGV897.Main

open TargetedSamplers.Structured.BinaryStack

/-- One Gaussian kernel provides both the initial count and every count used while unranking. -/
structure Solver where
  command : Cmd
  floor : ℕ
  work : ℕ → ℕ
  space : ℕ → ℕ
  growth : ∃ c d : ℕ, ∀ N, work N+space N ≤ c*(N+1)^d
  count : ∀ (n : ℕ) (E : List (Equation n)) (k : ℕ) (p : List Bool), k+p.length=n →
    ∀ (base row pin bank b : ℕ) (s : Store) (τ : Tapes),
    let N := n+(E.length+n)
    floor ≤ bank → bank+20 ≤ row → row+(denseWords E).length ≤ pin → pin+n ≤ base →
    floor.size ≤ b → n+2 ≤ b → (base+space N).size ≤ b →
    Port E base row pin bank s → s.mem (bank+6)=k → s.mem (bank+9)=pin+k →
    (∀ i (hi : i < p.length), s.mem (pin+k+i)=bitWord p[i]) → s.Fits b →
    ∃ t j, Exec τ (fun u => u.Fits b) (countPort bank command) s t j ∧ j ≤ work N ∧
      t.mem 4=affineCount (E++pins n k p) ∧ t.out=s.out ∧
      ∀ a, floor ≤ a → (a < base ∨ base+space N ≤ a) → t.mem a=s.mem a

end AffinePrefixEnumeration

end AffineRAMSolver


