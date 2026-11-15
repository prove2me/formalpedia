-- Prove2me | Definitions.Def_StableMSR_BoundedWordCatalog
-- name    : StableMSR_BoundedWordCatalog
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-14T19:39:23.593863+00:00
-- url     : https://prove2.me/theorems/9a24dcfa-5882-47d4-9168-67fd7e5cac4d
-- title:
--   Fixed-width word records and bounded-subset decoding
-- statement:
--   Words of length $w$ over digits $0,\ldots,n$ are listed lexicographically. Digit zero is padding and digit $v+1$ represents vertex $v\in\mathrm{Fin}(n)$; decoding deletes zeros and repeated digits. Each word is stored as a width header followed by its $w$ digits in consecutive integer-memory cells. The catalog begins at address $2$, and its reader uses fixed record width $w+1$. These definitions specify exact catalog contents and memory readback; different words may represent the same subset.
-- source:
--   Concrete bounded-width enumeration kernel for the Exact Sum-of-Radii Clustering under Any Constant Stability mission, over Definitions.Def_StableMSR_Recovery_Execution and the verified structured compiler.

import Definitions.Def_StableMSR_StructuredCompiler
open scoped Classical
namespace StableMSR.Recovery.BoundedSubsetWords
def words (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | w+1 => (List.range (n+1)).flatMap (fun a => (words n w).map (List.cons a))

def decode (n : ℕ) (l : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v.val+1 ∈ l)

end StableMSR.Recovery.BoundedSubsetWords
namespace StableMSR.Recovery.Compiler.TupleWriter
def writeMemory (base : ℤ) (values : List ℤ) (mem : ℤ → ℤ) : ℤ → ℤ :=
  match values with
  | [] => mem
  | v::vs => writeMemory (base+1) vs (Function.update mem base v)

end StableMSR.Recovery.Compiler.TupleWriter
namespace StableMSR.Recovery.Compiler.TupleEnumeration
open TupleWriter BoundedSubsetWords
def wordStream (n w : ℕ) (pre : List ℤ) (r : ℕ) : List ℤ :=
  (words n r).flatMap (fun xs : List ℕ => (w : ℤ) :: (pre ++ xs.map (fun i : ℕ => (i : ℤ))))

def readWord (w : ℕ) (mem : ℤ → ℤ) (base : ℤ) : List ℕ :=
  (List.range w).map (fun i : ℕ => (mem (base+1+(i : ℤ))).toNat)

def catalogWords (n w : ℕ) (mem : ℤ → ℤ) : List (List ℕ) :=
  (List.range ((n+1)^w)).map (fun j : ℕ => readWord w mem (2+((w+1)*j : ℕ)))

end StableMSR.Recovery.Compiler.TupleEnumeration


