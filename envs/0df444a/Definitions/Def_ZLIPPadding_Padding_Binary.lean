-- Prove2me | Definitions.Def_ZLIPPadding_Padding_Binary
-- name    : ZLIPPadding_Padding_Binary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:50.576375+00:00
-- url     : https://prove2.me/theorems/db8da6ee-decc-4865-a406-6aedf14c5962
-- title:
--   Binary encodings and executable coordinate decoders
-- statement:
--   Signed integers use a sign bit followed by a self-delimiting binary magnitude. A natural number with $k$ payload bits is encoded as $k$ ones, a zero separator and its little-endian binary payload. Thus code length is linear in binary magnitude length, not in the represented value.
--
--   Vectors and matrices concatenate their signed entries, with matrices in row order. A query carries its dimension followed by the matrix entries. Decoders check canonical integer codes and exact entry counts. In particular,
--   $$\operatorname{query}(H)=\operatorname{encode}(n)\,\Vert\,\operatorname{encode}(H).$$
--   Public reduction requests carry only dimension, two natural error-request parameters and $G$. Finite randomization outputs encode $H$ and $U$; malformed outputs decode as failure. This layer supplies concrete finite representations for bit complexity, without giving algorithms the hidden factor.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed pp. 7–9, 27–32 (PDF pp. 8–10, 28–33), representation conventions and §§7.1–7.7

import Definitions.Def_ZLIPPadding_Padding_GramModel

namespace ZLIPPadding.Padding
abbrev Bits := List Bool
/-- Self-delimiting binary: unary bit-length, zero separator, little-endian payload. -/
def encNat (n : ℕ) : Bits := List.replicate n.bits.length true ++ [false] ++ n.bits

def readNat (w : Bits) : Option (ℕ × Bits) := do
  let k := (w.takeWhile id).length
  if w.length < 2 * k + 1 then none else
    let b := (w.drop (k + 1)).take k
    let n := b.foldr (fun x a => 2 * a + if x then 1 else 0) 0
    if encNat n = w.take (2 * k + 1) then some (n, w.drop (2 * k + 1)) else none

def encInt (z : ℤ) : Bits := (z < 0) :: encNat z.natAbs

def readInt : Bits → Option (ℤ × Bits)
  | [] => none
  | s :: w => do
    let (a, r) ← readNat w
    if s && a == 0 then none else some ((if s then -(a : ℤ) else (a : ℤ)), r)

def encInts (z : List ℤ) : Bits := z.flatMap encInt

def readIntsAux : ℕ → Bits → Option (List ℤ)
  | 0, w => if w = [] then some [] else none
  | k + 1, w => if w = [] then some [] else do
      let (z, r) ← readInt w
      let zs ← readIntsAux k r
      pure (z :: zs)

def readInts (w : Bits) : Option (List ℤ) := readIntsAux w.length w

def vecEntries {n : ℕ} (a : ZVec n) : List ℤ := List.ofFn a

def matEntries {n : ℕ} (G : ZMat n) : List ℤ :=
  (List.ofFn fun i => List.ofFn fun j => G i j).flatten

def encVec {n : ℕ} (a : ZVec n) : Bits := encInts (vecEntries a)

def vecFromList (n : ℕ) (z : List ℤ) : ZVec n := fun i => z[i.val]?.getD 0

def matFromList (n : ℕ) (z : List ℤ) : ZMat n := fun i j => z[n * i.val + j.val]?.getD 0

def decVec (n : ℕ) (w : Bits) : Option (ZVec n) := do
  let z ← readInts w
  if z.length = n then some (vecFromList n z) else none

def encMat {n : ℕ} (G : ZMat n) : Bits := encInts (matEntries G)

def decMat (n : ℕ) (w : Bits) : Option (ZMat n) := do
  let z ← readInts w
  if z.length = n * n then some (matFromList n z) else none

def encGram {n : ℕ} (G : ZMat n) : Bits := encNat n ++ encMat G

def decGram (w : Bits) : Option (Σ n : ℕ, ZMat n) := do
  let (n, r) ← readNat w
  let G ← decMat n r
  pure ⟨n, G⟩

def encRandom {n : ℕ} (hu : ZMat n × ZMat n) : Bits :=
  encInts (matEntries hu.1 ++ matEntries hu.2)

def decRandom (n : ℕ) (w : Bits) : Option (ZMat n × ZMat n) := do
  let z ← readInts w
  if z.length = 2 * n * n then
    some (matFromList n (z.take (n*n)), matFromList n (z.drop (n*n))) else none

/-- Public requests contain no hidden factor, retained U, or support labels. -/
def encRequest {n : ℕ} (G : ZMat n) (a b : ℕ) : Bits :=
  encNat n ++ encNat a ++ encNat b ++ encMat G

end ZLIPPadding.Padding


