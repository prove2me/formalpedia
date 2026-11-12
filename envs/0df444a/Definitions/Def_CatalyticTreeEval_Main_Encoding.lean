-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_Encoding
-- name    : CatalyticTreeEval_Main_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:24:33.092871+00:00
-- url     : https://prove2.me/theorems/3a03e2e5-8485-412c-a2e6-e64362806e76
-- title:
--   Complete binary TreeEval instances and binary input encoding
-- statement:
--   For a label length $\ell$, labels are the integers $0\le y<2^\ell$, identified with their $\ell$ little-endian bits. A height-zero tree has a leaf label; a height-$h+1$ tree has an arbitrary two-input table $f$ and two height-$h$ subtrees. Its root value is defined recursively by
--
--   $$v_{\varnothing}=f(v_0,v_1).$$
--
--   The input begins with self-delimiting codes for $h$ and $\ell$, then lists each table in preorder, with rows ordered first by the left label and then by the right label, followed recursively by the subtree payloads. Leaf labels occupy exactly $\ell$ bits. Each natural code has a unary bit-length, a zero separator and that many little-endian bits. The payload contains $\ell 2^h+\ell(2^h-1)2^{2\ell}$ bits. Tables have no promise or algebraic restriction. The auxiliary list and parameter codes use the same convention; logarithms and exponentials are base two. The main results restrict both $h$ and $\ell$ to positive integers.
--
--   This supplies the actual function problem and a fixed input representation, without including an answer or an evaluator in the input.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Definition 2.1, printed p. 5 (PDF p. 7); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticMatching_General_Machine

set_option autoImplicit false

namespace CatalyticTreeEval.Main

abbrev Machine := CatalyticMatching.General.Machine
abbrev Label (l : ℕ) := Fin (2 ^ l)

def bits (width n : ℕ) : List Bool :=
  (List.range width).map n.testBit

/-- A length-prefixed binary natural: unary bit-length, a zero, then little-endian bits. -/
def natCode (n : ℕ) : List Bool :=
  let b := Nat.log 2 (n + 1) + 1
  List.replicate b true ++ [false] ++ bits b n

def listCode (x : List Bool) : List Bool := natCode x.length ++ x

def natsCode (x : List ℕ) : List Bool := natCode x.length ++ x.flatMap natCode

noncomputable def log₂ (x : ℝ) : ℝ := Real.log x / Real.log 2

noncomputable def exp₂ (x : ℝ) : ℝ := (2 : ℝ) ^ x

noncomputable def lg (n : ℕ) : ℝ := 1 + log₂ (n + 1)

/-- Unrestricted complete ordered binary trees, with full arbitrary gate tables. -/
inductive Tree (l : ℕ) : ℕ → Type
  | leaf : Label l → Tree l 0
  | node {h : ℕ} : (Label l → Label l → Label l) → Tree l h → Tree l h → Tree l (h + 1)

def Tree.value {l h : ℕ} : Tree l h → Label l
  | .leaf v => v
  | .node f a b => f a.value b.value

/-- Row order is increasing first label, then increasing second label. -/
def tableCode {l : ℕ} (f : Label l → Label l → Label l) : List Bool :=
  (List.finRange (2 ^ l)).flatMap fun a =>
    (List.finRange (2 ^ l)).flatMap fun b => bits l (f a b).val

/-- Preorder: a node's table, then its left and right subtrees; leaves output their labels. -/
def Tree.payload {l h : ℕ} : Tree l h → List Bool
  | .leaf v => bits l v.val
  | .node f a b => tableCode f ++ a.payload ++ b.payload

def Tree.encode {l h : ℕ} (I : Tree l h) : List Bool :=
  natCode h ++ natCode l ++ I.payload

end CatalyticTreeEval.Main


