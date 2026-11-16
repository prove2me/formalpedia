-- Prove2me | Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_Expressions
-- name    : IntervalMaxCutEPTAS_Scheme_Supplement_Expressions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:28:14.113107+00:00
-- url     : https://prove2.me/theorems/658a8582-e1e3-4946-af30-8f185baa3852
-- title:
--   Serialized clique-width expressions, including the empty graph
-- statement:
--   A width-$w$ expression is either a published nonempty clique-width expression or the empty expression, which evaluates only to the empty graph. Positive expressions retain the published creation, disjoint union, join of distinct labels, and relabel operations. The assertion that $H$ has an expression is
--
--   $$\exists e,\quad \operatorname{graph}(e)\cong H.$$
--
--   Leaves are ordered from left to right in the expression. A prefix integer code uses opcode 0 for empty, 1 for a labeled vertex, 2 for union, 3 for join, and 4 for relabel; the label operands follow their opcode. An executable bounds-checked parser is included. The output packet has successive regions containing the width, the $n^2$ adjacency bits, the code length, the code, and the $n$ input vertex names in leaf order. The output predicate requires an explicit leaf-to-input-vertex bijection, exact adjacency preservation and the exact packet in memory. There is no freely chosen decoder. This interface is reused by both costed width statements.
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), §3 and §6.2, PDF p. 24 (printed p. 23)

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_KExpr
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Machine

set_option autoImplicit false

namespace IntervalMaxCutEPTAS.Scheme.Supplement

open ApproxCliqueWidth.Certificate

/-- Only the empty graph is added to the published expression language. -/
abbrev Expression (w : ℕ) := Option (KExpr w)

def Expression.Vtx {w : ℕ} : Expression w → Type
  | none => Empty
  | some t => t.Vtx

def Expression.graph {w : ℕ} : (e : Expression w) → SimpleGraph e.Vtx
  | none => ⊥
  | some t => t.graph

def HasExpression {V : Type} (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∃ e : Expression w, Nonempty (e.graph ≃g G)

/-- Leaves in left-to-right syntactic order, without any chosen enumeration. -/
def expressionLeaves {w : ℕ} : (t : KExpr w) → List t.Vtx
  | .const _ => [()]
  | .eta _ _ _ t => expressionLeaves t
  | .rho _ _ t => expressionLeaves t
  | .union t u => (expressionLeaves t).map Sum.inl ++ (expressionLeaves u).map Sum.inr

def Expression.leaves {w : ℕ} : (e : Expression w) → List e.Vtx
  | none => []
  | some t => expressionLeaves t

/-- Prefix code: 1,label = vertex; 2 = union; 3,i,j = join; 4,i,j = relabel. -/
def expressionCode {w : ℕ} : KExpr w → List ℤ
  | .const i => [1, i.val]
  | .union t u => [2] ++ expressionCode t ++ expressionCode u
  | .eta i j _ t => ([3, i.val, j.val] : List ℤ) ++ expressionCode t
  | .rho i j t => ([4, i.val, j.val] : List ℤ) ++ expressionCode t

def Expression.code {w : ℕ} : Expression w → List ℤ
  | none => [0]
  | some t => expressionCode t

/-- Bounds-checked label decoding. No arbitrary interpretation of memory. -/
def parseLabel (w : ℕ) (a : ℤ) : Option (Fin w) :=
  if h : 0 ≤ a ∧ a.toNat < w then some ⟨a.toNat, h.2⟩ else none

/-- Fuel-bounded executable parser for the published nonempty language. -/
def parsePositive (w : ℕ) : ℕ → List ℤ → Option (KExpr w × List ℤ)
  | 0, _ => none
  | _fuel + 1, 1 :: i :: xs => do
      let a ← parseLabel w i
      pure (.const a, xs)
  | fuel + 1, 2 :: xs => do
      let (t, ys) ← parsePositive w fuel xs
      let (u, zs) ← parsePositive w fuel ys
      pure (.union t u, zs)
  | fuel + 1, 3 :: i :: j :: xs => do
      let a ← parseLabel w i
      let b ← parseLabel w j
      if h : a ≠ b then
        let (t, ys) ← parsePositive w fuel xs
        pure (.eta a b h t, ys)
      else none
  | fuel + 1, 4 :: i :: j :: xs => do
      let a ← parseLabel w i
      let b ← parseLabel w j
      let (t, ys) ← parsePositive w fuel xs
      pure (.rho a b t, ys)
  | _, _ => none

def parseExpression (w : ℕ) (xs : List ℤ) : Option (Expression w × List ℤ) :=
  match xs with
  | 0 :: ys => some (none, ys)
  | _ => do
      let (t, ys) ← parsePositive w (xs.length + 1) xs
      pure (some t, ys)

/-- Matrix bitmap in row-major order on Fin n. -/
def adjacencyWords {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List ℤ :=
  (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then (1 : ℤ) else 0).flatten

/-- Fixed successive regions: width, n² adjacency bits, code length, code, n leaf names.
The isomorphism's vertex names are explicitly written in syntactic leaf order. -/
def expressionPacket {n w : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : Expression w) (f : e.Vtx ≃ Fin n) : List ℤ :=
  [(w : ℤ)] ++ adjacencyWords G ++ [(e.code.length : ℤ)] ++ e.code ++
    e.leaves.map (fun v => ((f v).val : ℤ))

structure ParsedPacket (n : ℕ) where
  width : ℕ
  expression : Expression width
  matrix : List ℤ
  names : List ℤ

/-- Executable packet framing and syntax validation. Semantic checks use the fixed graph
evaluation and the explicitly output leaf bijection in ReportsExpression. -/
def parsePacket (n : ℕ) (ws : List ℤ) : Option (ParsedPacket n) := do
  let w :: rest := ws | none
  if w < 0 then none else do
    let matrix := rest.take (n * n)
    if matrix.length ≠ n * n ∨ ¬ matrix.all (fun a => a == 0 || a == 1) then none else do
      let len :: tail := rest.drop (n * n) | none
      if len < 0 ∨ tail.length < len.toNat + n then none else do
        let (e, unused) ← parseExpression w.toNat (tail.take len.toNat)
        if ¬ unused.isEmpty then none else do
          let names := (tail.drop len.toNat).take n
          if ¬ names.all (fun a => decide (0 ≤ a ∧ a < (n : ℤ))) then none else
            pure ⟨w.toNat, e, matrix, names⟩

def ReportsExpression {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w S : ℕ) (s : Light.State) : Prop :=
  ∃ (e : Expression w) (f : e.Vtx ≃ Fin n),
    (∀ u v, e.graph.Adj u v ↔ G.Adj (f u) (f v)) ∧
    WritesList S s (expressionPacket G e f)

end IntervalMaxCutEPTAS.Scheme.Supplement


