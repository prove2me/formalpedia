-- Prove2me | Definitions.Def_EditGV897_Main_Codec
-- name    : EditGV897_Main_Codec
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:26:55.629327+00:00
-- url     : https://prove2.me/theorems/27118aed-2a3c-44a3-b650-13a91c090211
-- title:
--   Signed-bound encoder, image inverse and mixed-edit decoder
-- statement:
--   For shared parameters $P=(G,\beta)$, put $K=n-|G|-1$. Interpret each $K$-bit message as a big-endian integer $m$. Starting at the empty prefix, compute $L(p0)$ before appending a bit: choose zero when $m<L(p0)$; otherwise choose one and replace $m$ by $m-\max(0,L(p0))$. Stop after $n$ bits. The inverse scans a codeword and adds $\max(0,L(p0))$ before every one bit, then writes the sum in $K$ bits.
--
--   The code is precisely the encoder image
--
--   $$C=\{\operatorname{Enc}(u):u\in\mathbb F_2^K\}.$$
--
--   For an edited word $y$, enumerate at most $t$ legal operations from $y$, retain length-$n$ candidates of syndrome $\beta$, and invert the first retained word. Different scripts producing the same word are harmless. The decoder rejects words longer than $n+t$; no exact rejection claim is imposed on other invalid inputs.
--
--   This is the source's encoding and original-message recovery construction. Its correctness and efficient program realizations remain theorem conclusions.
--
--   **Formalization Note** Lower bounds and indices use integers throughout traversal. The inverse has a total extension off the image, while guarantees apply on the image. The code is neither the whole coset nor the whole separated subset. Variable received lengths remain ordered lists.
-- source:
--   Ryan Gabrys, Shubhransh Singhvi, Eitan Yaakobi, Making Every Edit Count: Efficient Binary Edit Correction at the Gilbert–Varshamov Bound, STOC 2027 submission #897 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §4.3 equation (12), Lemma 3 and proof of Theorem 1, printed pp. 11–14 / PDF pp. 12–15

import Definitions.Def_EditGV897_Main_Construction

namespace EditGV897.Main

/-- Source message order is big endian. All K-bit messages, including K=0, occur. -/
def messageIndex (u : List Bit) : ℤ :=
  u.foldl (fun m a => 2 * m + if a = 0 then 0 else 1) 0

def indexBits (K : ℕ) (m : ℕ) : List Bit :=
  (List.range K).map (fun j => if m.testBit (K - 1 - j) then 1 else 0)

def encodeSteps {n : ℕ} (F : Family n) (P : Parameters n) :
    ℕ → List Bit → ℤ → List Bit × ℤ
  | 0, p, m => (p, m)
  | k + 1, p, m =>
    let L := prefixBound F P.rows P.beta (p ++ [0])
    if m < L then encodeSteps F P k (p ++ [0]) m
    else encodeSteps F P k (p ++ [1]) (m - max 0 L)

def encodeList {n : ℕ} (F : Family n) (P : Parameters n) (u : Word (messageLength P)) : List Bit :=
  (encodeSteps F P n [] (messageIndex (wordList u))).1

def encodeWord {n : ℕ} (F : Family n) (P : Parameters n) (u : Word (messageLength P)) : Word n :=
  listWord n (encodeList F P u)

def inverseIndex {n : ℕ} (F : Family n) (P : Parameters n) (x : List Bit) : ℤ :=
  (x.foldl (fun s a =>
    let L := prefixBound F P.rows P.beta (s.1 ++ [0])
    (s.1 ++ [a], s.2 + if a = 0 then 0 else max 0 L)) (([] : List Bit), (0 : ℤ))).2

def inverseList {n : ℕ} (F : Family n) (P : Parameters n) (x : List Bit) : List Bit :=
  indexBits (messageLength P) (inverseIndex F P x).toNat

/-- Operational candidate search: every path of ≤t valid elementary operations. -/
def bitStep (x : List Bit) : PositionedOp → List Bit
  | .insert k a => x.take k ++ [a] ++ x.drop k
  | .delete k => x.take k ++ x.drop (k + 1)
  | .toggle k => x.take k ++ ((x.drop k).take 1).map (fun a => a + 1) ++ x.drop (k + 1)

def candidates : ℕ → List Bit → List (List Bit)
  | 0, y => [y]
  | t + 1, y => y :: (legalOps y.length).flatMap (fun op => candidates t (bitStep y op))

/-- On valid transmissions separation ensures uniqueness of the retained word.
Duplicates from different edit scripts are harmless; find? picks the first occurrence. -/
def decodeList {n : ℕ} (t : ℕ) (P : Parameters n) (y : List Bit) : Option (List Bit) :=
  if n + t < y.length then none else
  ((candidates t y).find? (fun x => x.length == n &&
    decide (syndrome P.rows (listWord n x) = P.beta))).map
      (inverseList (canonicalFamily t n) P)

noncomputable def codeImage {n : ℕ} (F : Family n) (P : Parameters n) : Finset (Word n) := by
  classical
  exact Finset.univ.image (encodeWord F P)

/-- Mathematical outputs on bad setup inputs are irrelevant to sufficiently large n. -/
def encoderInput {n : ℕ} (F : Family n) (P : Parameters n)
    (u : Word (messageLength P)) : List Bool :=
  familyRowsInput F P.rows ++ frame (bitCode P.beta) ++ frame (wordCode u)

def inverseInput {n : ℕ} (F : Family n) (P : Parameters n) (x : List Bit) : List Bool :=
  familyRowsInput F P.rows ++ frame (bitCode P.beta) ++ frame (bitCode x)

def editEncoderInput {n : ℕ} (P : Parameters n) (u : Word (messageLength P)) : List Bool :=
  unary n ++ parametersCode P ++ frame (wordCode u)

def editDecoderInput {n : ℕ} (P : Parameters n) (y : List Bit) : List Bool :=
  unary n ++ parametersCode P ++ frame (bitCode y)

end EditGV897.Main


