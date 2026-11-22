-- Prove2me | Definitions.Def_DistLTLSynth_Char_SymbolicArena
-- name    : DistLTLSynth_Char_SymbolicArena
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T12:39:37.161554+00:00
-- url     : https://prove2.me/theorems/8283a9a0-0b3c-4e28-9db3-bffaad5bf3f2
-- title:
--   Symbolic Compressed Component-Tree Arena and Edge-Thread Monitor
-- statement:
--   Symbolic compressed component-tree arena, finite view-equivalence encodings, and universal edge-thread monitor specification supporting Theorem 3.4 (distributed LTL synthesis under message adversaries with nowhere-dense geometric image).
--
--   1. **Symbolic compressed positions and actions (`SymPosCode`, `SymActCode`, `validSymLabels`):** Finite encodings of compressed view-complex positions $(k, \equiv_1, \equiv_2, q)$ of size $1 \le k \le B_{\mathrm{full}}$ together with idempotent compression retractions of image size $\le B_{\mathrm{red}}$ and view-coherent $1$-to-$D$-round output tables.
--   2. **Component decomposition and child transition (`symComponents`, `childSymPos`):** Primitive-recursive computation of connected live $D$-block extension components and induced child view-equivalence tables.
--   3. **Universal bad-thread NBW and parity tree specification (`badThreadNBW`, `buildTreeSpec`):** Encodes the violation of edge-thread parity along branches as a finite nondeterministic B\u00fcchi automaton and compiles its determinized complement into a `TreeSpecCode`.
--
--   **Formalization Note** All arena definitions are pure total functions over `Nat`, `Bool`, and `List` so downstream proofs share a lightweight, sorry-free definitional layer.
-- source:
--   arXiv:2611.04561, Distributed LTL Synthesis under Arbitrary Message Adversaries, Section 3.3 (Definitions 3.8 & 3.12, Lemmas 3.12 & 3.13, pp. 13-16)

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_Consensus
import Definitions.Def_DistLTLSynth_Char_ComponentTree
import Definitions.Def_DistLTLSynth_Char_SynthesisEngine

set_option autoImplicit false

namespace DistLTLSynth.Char

def commGraphEquivFin3 : CommGraph ≃ Fin 3 where
  toFun
    | .oneToTwo => ⟨0, by decide⟩
    | .both => ⟨1, by decide⟩
    | .twoToOne => ⟨2, by decide⟩
  invFun
    | ⟨0, _⟩ => .oneToTwo
    | ⟨1, _⟩ => .both
    | _ => .twoToOne
  left_inv g := by cases g <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Primcodable CommGraph := Primcodable.ofEquiv (Fin 3) commGraphEquivFin3

def iterNat {α : Type} (g : α → α) (m : ℕ) (x : α) : α :=
  (List.range m).foldl (fun acc _ => g acc) x

def wordsOf {α : Type} (choices : List α) (n : ℕ) : List (List α) :=
  ((List.range n).map (fun _ => choices)).sections

def dedupList {α : Type} [DecidableEq α] (xs : List α) : List α :=
  xs.foldr (fun x ys => if x ∈ ys then ys else x :: ys) []

def vdepth {X1 X2 : Type} : View X1 X2 → ℕ
  | .I1 => 0
  | .I2 => 0
  | .N1 _ u => vdepth u + 1
  | .N2 _ v => vdepth v + 1
  | .C1 _ u _ _ => vdepth u + 1
  | .C2 _ v _ _ => vdepth v + 1

def parentView {X1 X2 : Type} : View X1 X2 → View X1 X2
  | .I1 => .I1
  | .I2 => .I2
  | .N1 _ u => u
  | .N2 _ v => v
  | .C1 _ u _ _ => u
  | .C2 _ v _ _ => v

def iterParent {X1 X2 : Type} : ℕ → View X1 X2 → View X1 X2
  | 0, v => v
  | k + 1, v => iterParent k (parentView v)

inductive Proc : Type where
  | one
  | two
  deriving DecidableEq

def viewOf {X1 X2 : Type} : Proc → List (Signal X1 X2) → View X1 X2
  | .one => view1
  | .two => view2

def graphOfHist {X1 X2 : Type} (h : List (Signal X1 X2)) : List CommGraph :=
  h.map (fun s => s.2.2)

def ReachableInB {X1 X2 Y1 Y2 QB : Type} {D : ℕ}
    (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2)))
    (n : ℕ) (h : List (Signal X1 X2)) (q : QB) : Prop :=
  h.length = n * D ∧
    ∃ e : ℕ → Signal X1 X2 × (Y1 × Y2),
      pre (fun t => (e t).1) (n * D) = h ∧ B.run (toBlocks D e) n = q

def OddParityCond (c : ℕ → ℕ) : Prop :=
  ∃ p : ℕ, Odd p ∧ (∃ᶠ n in Filter.atTop, c n = p) ∧ ∀ᶠ n in Filter.atTop, p ≤ c n

def cMax (a b : ℕ) : ℕ := if a ≤ b then b else a

def maxList (xs : List ℕ) : ℕ :=
  xs.foldr cMax 0

def complementGenDPA (d : GenDPACode) : GenDPACode :=
  (d.1, d.2.1, (List.range (d.1 + 1)).map fun i => d.2.2.getD i 0 + 1)

def myPow (b e : ℕ) : ℕ :=
  (List.range e).foldl (fun acc _ => acc * b) 1

def tokKind (t : Token) : ℕ :=
  if (t.1 = 0 ∧ (t.2.1 = 1 ∨ t.2.1 = 2)) ∨
     (t.1 = 1 ∧ (t.2.1 = 1 ∨ t.2.1 = 2)) ∨
     (t.1 = 2 ∧ t.2.1 ≤ 2) then 0
  else if t.1 = 3 ∨ t.1 = 4 ∨ t.1 = 5 ∨ t.1 = 8 then 1
  else if t.1 = 6 ∨ t.1 = 7 ∨ t.1 = 9 ∨ t.1 = 10 ∨ t.1 = 11 ∨ t.1 = 12 then 2
  else 3

def parseEndStep (ts : List Token) (prev : List (Option ℕ)) : List (Option ℕ) :=
  (List.range (ts.length + 1)).map fun i =>
    if i < ts.length then
      let k := tokKind (ts.getD i (99, 0, 0))
      if k = 0 then some (i + 1)
      else if k = 1 then prev.getD (i + 1) none
      else if k = 2 then
        match prev.getD (i + 1) none with
        | some j => prev.getD j none
        | none => none
      else none
    else none

def parseEndIdx (ts : List Token) (fuel : ℕ) : List (Option ℕ) :=
  iterNat (parseEndStep ts) fuel ((List.range (ts.length + 1)).map fun _ => none)

def parseOk (ts : List Token) : Bool :=
  decide ((parseEndIdx ts ts.length).getD 0 none = some ts.length)

/-- Modular engine bundle supplying NBW determinization, `TreeSpecCode` solving, and
`IsBlockAutomaton` compilation. -/
structure Thm34Engine : Type where
  detListNBW : ℕ → ListNBWCode → GenDPACode
  primrec_detListNBW : Primrec₂ detListNBW
  detListNBW_accepts_iff : ∀ (αSize : ℕ) (B : ListNBWCode) (w : ℕ → Fin (αSize + 1)),
    (toGenDPA αSize (detListNBW αSize B)).Accepts w ↔ ListNBWAccepts αSize B w
  solveTreePG : TreeSpecCode → Option (List ℕ)
  packTS : TreeSpecCode → ℕ
  unfoldLabelPacked : ℕ → List ℕ → ℕ
  primrec_solveTreePG : Primrec solveTreePG
  primrec_packTS : Primrec packTS
  primrec₂_unfoldLabelPacked : Primrec₂ unfoldLabelPacked
  solveTreePG_some_sound : ∀ (ts : TreeSpecCode) (σ : List ℕ),
    solveTreePG ts = some σ →
      ValidAcceptingTree ts (fun addr =>
        ⟨(unfoldLabelPacked (Nat.pair (packTS ts) (Encodable.encode σ)) (addr.map Fin.val)) % (ts.2.1 + 1),
          Nat.mod_lt _ (Nat.succ_pos _)⟩)
  solveTreePG_iff_exists_tree : ∀ (ts : TreeSpecCode),
    solveTreePG ts ≠ none ↔
      ∃ t : List (Fin (ts.1 + 1)) → Fin (ts.2.1 + 1), ValidAcceptingTree ts t
  blockAlphaMinusOne : Instance → ℕ → ℕ
  primrec_blockAlphaMinusOne : Primrec₂ blockAlphaMinusOne
  encIOBlockNat : Instance → ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ
  primrec_encIOBlockNat : Primrec fun p : (Instance × ℕ) × List (ℕ × ℕ × ℕ × ℕ × ℕ) =>
    encIOBlockNat p.1.1 p.1.2 p.2
  encIOBlockTyped : ∀ (I : Instance) (D : ℕ),
    (Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) → Fin (blockAlphaMinusOne I D + 1)
  encIOBlock_compat : ∀ (I : Instance) (D : ℕ)
    (blk : Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)),
    (encIOBlockTyped I D blk).val =
      encIOBlockNat I D
        ((List.ofFn blk).map fun s => (s.1.1.val, s.1.2.1.val, s.1.2.2.idx, s.2.1.val, s.2.2.val)) %
        (blockAlphaMinusOne I D + 1)
  compileBlock : DPACode × Instance × ℕ → GenDPACode × List Bool
  primrec_compileBlock : Primrec compileBlock
  compileBlock_spec : ∀ (c : DPACode) (I : Instance) (D_m1 : ℕ) (φ : Formula ℕ ℕ ℕ ℕ),
    parse I.tokens = some φ →
      let D := D_m1 + 1
      let res := compileBlock (c, I, D_m1)
      let dpa := toGenDPA (blockAlphaMinusOne I D) res.1
      let B : DPA (Fin (res.1.1 + 1)) (Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) :=
        ⟨dpa.init, fun q blk => dpa.step q (encIOBlockTyped I D blk), dpa.prio⟩
      let Qlive : Set (Fin (res.1.1 + 1)) := {q | res.2.getD q.val false = true}
      IsBlockAutomaton c.lang (instFormulaOf I φ) D B Qlive

def andBool (a b : Bool) : Bool := if a = true then b else false

def orBool (a b : Bool) : Bool := if a = true then true else b

def notBool (a : Bool) : Bool := if a = true then false else true

def memNat (x : ℕ) (l : List ℕ) : Bool :=
  l.foldl (fun acc y => orBool acc (decide (y = x))) false

def cIdxOf {α : Type} [DecidableEq α] (xs : List α) (x : α) : ℕ :=
  xs.foldr (fun y acc => if x = y then 0 else acc + 1) 0

def stepCompIdx {α : Type} (inh : α) (S : List α) (adj : α → α → Bool) (cur : List ℕ) : List ℕ :=
  (List.range S.length).filter fun y =>
    orBool (memNat y cur)
      (cur.foldl (fun acc x => orBool acc (adj (S.getD x inh) (S.getD y inh))) false)

def compIdxOf {α : Type} (inh : α) (S : List α) (adj : α → α → Bool) (i : ℕ) : List ℕ :=
  iterNat (stepCompIdx inh S adj) S.length [i]

def componentsIdx {α : Type} (inh : α) (S : List α) (adj : α → α → Bool) : List (List ℕ) :=
  dedupList ((List.range S.length).map (compIdxOf inh S adj))

def sigCard (I : Instance) : ℕ := (I.k1 + 1) * (I.k2 + 1) * 3

def decSigG (s : ℕ) : ℕ := s % 3

def decSigX2 (I : Instance) (s : ℕ) : ℕ := (s / 3) % (I.k2 + 1)

def decSigX1 (I : Instance) (s : ℕ) : ℕ := ((s / 3) / (I.k2 + 1)) % (I.k1 + 1)

def decGraph (s : ℕ) : CommGraph :=
  if s % 3 = 0 then .oneToTwo else if s % 3 = 1 then .both else .twoToOne

def encSigTyped (I : Instance) (s : Signal I.X1 I.X2) : ℕ :=
  (s.1.val * (I.k2 + 1) + s.2.1.val) * 3 + s.2.2.idx

def decSigTyped (I : Instance) (s : ℕ) : Signal I.X1 I.X2 :=
  (⟨decSigX1 I s, Nat.mod_lt _ (Nat.succ_pos _)⟩,
   ⟨decSigX2 I s, Nat.mod_lt _ (Nat.succ_pos _)⟩,
   decGraph s)

def encHist (I : Instance) (h : List (Signal I.X1 I.X2)) : List ℕ :=
  h.map (encSigTyped I)

def decHist (I : Instance) (w : List ℕ) : List (Signal I.X1 I.X2) :=
  w.map (decSigTyped I)

def encBlock (I : Instance) {D : ℕ} (u : Fin D → Signal I.X1 I.X2) : List ℕ :=
  encHist I (List.ofFn u)

def decBlock (I : Instance) (D : ℕ) (uNat : List ℕ) : Fin D → Signal I.X1 I.X2 :=
  fun t => decSigTyped I (uNat.getD t.val 0)

def nonemptyExtWords (I : Instance) (D : ℕ) : List (List ℕ) :=
  ((List.range D).map (· + 1)).flatMap (wordsOf (List.range (sigCard I)))

def fullBlocks (I : Instance) (D : ℕ) : List (List ℕ) :=
  wordsOf (List.range (sigCard I)) D

def extStepBool (I : Instance) (prev : Bool × Bool) (ss : ℕ × ℕ) : Bool × Bool :=
  let s := ss.1
  let s' := ss.2
  let g := decSigG s
  let x1 := decSigX1 I s
  let x2 := decSigX2 I s
  let g' := decSigG s'
  let x1' := decSigX1 I s'
  let x2' := decSigX2 I s'
  let e1 :=
    if g = 0 then andBool (decide (g' = 0 ∧ x1 = x1')) prev.1
    else andBool (decide (g' ≠ 0 ∧ x1 = x1' ∧ x2 = x2')) (andBool prev.1 prev.2)
  let e2 :=
    if g = 2 then andBool (decide (g' = 2 ∧ x2 = x2')) prev.2
    else andBool (decide (g' ≠ 2 ∧ x2 = x2' ∧ x1 = x1')) (andBool prev.2 prev.1)
  (e1, e2)

def extEqFrom (I : Instance) (b1 b2 : Bool) (w1 w2 : List ℕ) : Bool × Bool :=
  if w1.length = w2.length then
    (w1.zip w2).foldl (extStepBool I) (b1, b2)
  else (false, false)

abbrev SymCtx : Type := Instance × ℕ × GenDPACode × List Bool

abbrev SymPosCode : Type := ℕ × List Bool × List Bool × List ℕ

abbrev SymActCode : Type := List ℕ × List ℕ × List ℕ

def ctxI (c : SymCtx) : Instance := c.1

def ctxDm1 (c : SymCtx) : ℕ := c.2.1

def ctxD (c : SymCtx) : ℕ := c.2.1 + 1

def ctxBCode (c : SymCtx) : GenDPACode := c.2.2.1

def ctxLive (c : SymCtx) : List Bool := c.2.2.2

def ctxQBCard (c : SymCtx) : ℕ := (ctxBCode c).1 + 1

def ctxBlockCard (c : SymCtx) : ℕ := myPow (sigCard (ctxI c)) (ctxD c)

def ctxBRed (c : SymCtx) : ℕ := myPow (1 + ctxQBCard c) (ctxBlockCard c) * ctxBlockCard c

def ctxBFull (c : SymCtx) : ℕ := ctxBRed c * ctxBlockCard c

def eq1At (pos : SymPosCode) (i j : ℕ) : Bool :=
  pos.2.1.getD (i * pos.1 + j) false

def eq2At (pos : SymPosCode) (i j : ℕ) : Bool :=
  pos.2.2.1.getD (i * pos.1 + j) false

def stateAt (pos : SymPosCode) (i : ℕ) : ℕ :=
  pos.2.2.2.getD i 0

def extEqNat (I : Instance) (pos : SymPosCode) (i : ℕ) (w1 : List ℕ) (j : ℕ) (w2 : List ℕ) : Bool × Bool :=
  extEqFrom I (eq1At pos i j) (eq2At pos i j) w1 w2

def initSymPos : SymPosCode := (1, [true], [true], [0])

def allSymPos (c : SymCtx) : List SymPosCode :=
  ((List.range (ctxBFull c)).map (· + 1)).flatMap fun k =>
    (wordsOf [false, true] (k * k)).flatMap fun e1 =>
      (wordsOf [false, true] (k * k)).flatMap fun e2 =>
        (wordsOf (List.range (ctxQBCard c)) k).map fun st => (k, e1, e2, st)

def allSymActsFor (c : SymCtx) (pos : SymPosCode) : List SymActCode :=
  let k := pos.1
  let NW := (nonemptyExtWords (ctxI c) (ctxD c)).length
  (wordsOf (List.range k) k).flatMap fun rList =>
    (wordsOf (List.range ((ctxI c).m1 + 1)) (k * NW)).flatMap fun o1 =>
      (wordsOf (List.range ((ctxI c).m2 + 1)) (k * NW)).map fun o2 => (rList, o1, o2)

def fixedIdxs (pos : SymPosCode) (act : SymActCode) : List ℕ :=
  (List.range pos.1).filter fun i => decide (act.1.getD i 0 = i)

def actValidProp (c : SymCtx) (pos : SymPosCode) (act : SymActCode) : Prop :=
  let k := pos.1
  let I := ctxI c
  let words := nonemptyExtWords I (ctxD c)
  let NW := words.length
  let fixed := fixedIdxs pos act
  (∀ i < k, act.1.getD (act.1.getD i 0) 0 = act.1.getD i 0) ∧
  fixed.length ≤ ctxBRed c ∧
  (∀ i < k, stateAt pos (act.1.getD i 0) = stateAt pos i) ∧
  (∀ i < k, ∀ j < k,
    (eq1At pos i j = true → eq1At pos (act.1.getD i 0) (act.1.getD j 0) = true) ∧
    (eq2At pos i j = true → eq2At pos (act.1.getD i 0) (act.1.getD j 0) = true)) ∧
  (∀ i ∈ fixed, ∀ j ∈ fixed, ∀ wi < NW, ∀ wj < NW,
    ((extEqNat I pos i (words.getD wi []) j (words.getD wj [])).1 = true →
      act.2.1.getD (i * NW + wi) 0 = act.2.1.getD (j * NW + wj) 0) ∧
    ((extEqNat I pos i (words.getD wi []) j (words.getD wj [])).2 = true →
      act.2.2.getD (i * NW + wi) 0 = act.2.2.getD (j * NW + wj) 0))

instance instDecidableActValidProp (c : SymCtx) (pos : SymPosCode) (act : SymActCode) :
    Decidable (actValidProp c pos act) := by
  unfold actValidProp; infer_instance

def inhInstance : Instance := ⟨0, 0, 0, 0, []⟩

def decodeOr {α : Type} [Primcodable α] (d : α) (n : ℕ) : α :=
  (Encodable.decode (α := α) n).getD d

def packCtx (c : SymCtx) : ℕ :=
  Nat.pair (Encodable.encode c.1)
    (Nat.pair c.2.1 (Nat.pair (Encodable.encode c.2.2.1) (Encodable.encode c.2.2.2)))

def unpackCtx (n : ℕ) : SymCtx :=
  (decodeOr inhInstance n.unpair.1,
   n.unpair.2.unpair.1,
   decodeOr (0, [], []) n.unpair.2.unpair.2.unpair.1,
   decodeOr [] n.unpair.2.unpair.2.unpair.2)

def actValid (c : SymCtx) (pos : SymPosCode) (act : SymActCode) : Bool :=
  decide (actValidProp c pos act)

def validActsFor (c : SymCtx) (pos : SymPosCode) : List (SymPosCode × SymActCode) :=
  ((allSymActsFor c pos).filter (actValid c pos)).map fun act => (pos, act)

def validSymLabels (c : SymCtx) : List (SymPosCode × SymActCode) :=
  dedupList ((allSymPos c).flatMap (validActsFor c))

def symNextState (E : Thm34Engine) (c : SymCtx) (pos : SymPosCode) (act : SymActCode)
    (i : ℕ) (u : List ℕ) : ℕ :=
  let I := ctxI c
  let D := ctxD c
  let words := nonemptyExtWords I D
  let NW := words.length
  let ioTuples : List (ℕ × ℕ × ℕ × ℕ × ℕ) := (List.range D).map fun t =>
    let s := u.getD t 0
    let wi := cIdxOf words (u.take (t + 1))
    let y1 := act.2.1.getD (i * NW + wi) 0
    let y2 := act.2.2.getD (i * NW + wi) 0
    (decSigX1 I s, decSigX2 I s, decSigG s, y1, y2)
  let A_blk := E.blockAlphaMinusOne I D + 1
  let bLetter := E.encIOBlockNat I D ioTuples % A_blk
  let bCode := ctxBCode c
  (bCode.2.1.getD (stateAt pos i * A_blk + bLetter) 0) % (bCode.1 + 1)

def symNextStatePacked (E : Thm34Engine) (q : ℕ) : ℕ :=
  symNextState E
    (unpackCtx q.unpair.1)
    (decodeOr initSymPos q.unpair.2.unpair.1)
    (decodeOr (([], [], []) : SymActCode) q.unpair.2.unpair.2.unpair.1)
    q.unpair.2.unpair.2.unpair.2.unpair.1
    (decodeOr ([] : List ℕ) q.unpair.2.unpair.2.unpair.2.unpair.2)

abbrev SymExtElem : Type := ℕ × List ℕ × ℕ

def symLiveExts (E : Thm34Engine) (c : SymCtx) (pos : SymPosCode) (act : SymActCode) :
    List SymExtElem :=
  (fixedIdxs pos act).flatMap fun i =>
    (fullBlocks (ctxI c) (ctxD c)).flatMap fun u =>
      let q' := symNextState E c pos act i u
      if (ctxLive c).getD q' false = true then [(i, u, q')] else []

def inhSymExt : SymExtElem := (0, [], 0)

def symExtAdj (I : Instance) (pos : SymPosCode) (e1 e2 : SymExtElem) : Bool :=
  let eqs := extEqNat I pos e1.1 e1.2.1 e2.1 e2.2.1
  orBool eqs.1 eqs.2

def symComponents (E : Thm34Engine) (c : SymCtx) (pos : SymPosCode) (act : SymActCode) :
    List (List SymExtElem) :=
  let S := symLiveExts E c pos act
  (componentsIdx inhSymExt S (symExtAdj (ctxI c) pos)).map fun idxs =>
    idxs.map fun idx => S.getD idx inhSymExt

def symComponentsPacked (E : Thm34Engine) (q : ℕ) : List (List SymExtElem) :=
  symComponents E
    (unpackCtx q.unpair.1)
    (decodeOr initSymPos q.unpair.2.unpair.1)
    (decodeOr (([], [], []) : SymActCode) q.unpair.2.unpair.2)

def childSymPos (I : Instance) (pos : SymPosCode) (comp : List SymExtElem) : SymPosCode :=
  let k' := comp.length
  let eq1' := (List.range k').flatMap fun a =>
    (List.range k').map fun b =>
      let ea := comp.getD a inhSymExt
      let eb := comp.getD b inhSymExt
      (extEqNat I pos ea.1 ea.2.1 eb.1 eb.2.1).1
  let eq2' := (List.range k').flatMap fun a =>
    (List.range k').map fun b =>
      let ea := comp.getD a inhSymExt
      let eb := comp.getD b inhSymExt
      (extEqNat I pos ea.1 ea.2.1 eb.1 eb.2.1).2
  let st' := comp.map fun e => e.2.2
  (k', eq1', eq2', st')

def edgeStepOk (E : Thm34Engine) (c : SymCtx) (labels : List (SymPosCode × SymActCode))
    (a d i p j : ℕ) : Bool :=
  if a = 0 then false
  else if a - 1 < labels.length then
    let pa := labels.getD (a - 1) (initSymPos, ([], [], []))
    let pos := pa.1
    let act := pa.2
    let comps := symComponents E c pos act
    if d < comps.length then
      let comp := comps.getD d []
      if i < pos.1 ∧ j < comp.length then
        let ej := comp.getD j (0, [], 0)
        andBool (decide (ej.1 = act.1.getD i 0))
          (decide (p = (ctxBCode c).2.2.getD ej.2.2 0))
      else false
    else false
  else false

def badThreadNBW (E : Thm34Engine) (c : SymCtx) (labels : List (SymPosCode × SymActCode)) :
    ListNBWCode :=
  let B_full := ctxBFull c
  let L_sym := labels.length + 1
  let A_mon := L_sym * B_full
  let K_prio := maxList (ctxBCode c).2.2
  let P_cnt := K_prio + 1
  let S_nbw := B_full + B_full * P_cnt * 2
  let accList := (List.range B_full).flatMap fun i =>
    (List.range P_cnt).flatMap fun p_odd =>
      if p_odd % 2 = 1 then [B_full + (i * P_cnt + p_odd) * 2 + 1] else []
  let transRows := (List.range S_nbw).flatMap fun q =>
    (List.range A_mon).map fun letter =>
      let a := letter / B_full
      let d := letter % B_full
      if q < B_full then
        let i := q
        (List.range P_cnt).flatMap fun p =>
          (List.range B_full).flatMap fun j =>
            if edgeStepOk E c labels a d i p j = true then
              j :: ((List.range P_cnt).flatMap fun p_odd =>
                if p_odd % 2 = 1 ∧ p_odd ≤ p then
                  [B_full + (j * P_cnt + p_odd) * 2 + (if p = p_odd then 1 else 0)]
                else [])
            else []
      else
        let rem := q - B_full
        let ip := rem / 2
        let i := ip / P_cnt
        let p_odd := ip % P_cnt
        if p_odd % 2 = 1 then
          (List.range P_cnt).flatMap fun p =>
            (List.range B_full).flatMap fun j =>
              if edgeStepOk E c labels a d i p j = true ∧ p_odd ≤ p then
                [B_full + (j * P_cnt + p_odd) * 2 + (if p = p_odd then 1 else 0)]
              else []
        else []
  (S_nbw - 1, [0], transRows, accList)

def buildTreeSpec (E : Thm34Engine) (c : SymCtx) : TreeSpecCode :=
  let labels := validSymLabels c
  let B_full := ctxBFull c
  let L_sym := labels.length + 1
  let rootOk : List Bool := (List.range L_sym).map fun a =>
    if a = 0 then false
    else decide ((labels.getD (a - 1) (initSymPos, ([], [], []))).1 = initSymPos)
  let childOk : List Bool := (List.range L_sym).flatMap fun a =>
    (List.range B_full).flatMap fun d =>
      (List.range L_sym).map fun a' =>
        if a = 0 then decide (a' = 0)
        else
          let pa := labels.getD (a - 1) (initSymPos, ([], [], []))
          let comps := symComponents E c pa.1 pa.2
          if d < comps.length then
            if a' = 0 then false
            else
              let pa' := labels.getD (a' - 1) (initSymPos, ([], [], []))
              decide (pa'.1 = childSymPos (ctxI c) pa.1 (comps.getD d []))
          else decide (a' = 0)
  let αMon := L_sym * B_full - 1
  let dpaGood := complementGenDPA (E.detListNBW αMon (badThreadNBW E c labels))
  (B_full - 1, labels.length, rootOk, childOk, dpaGood.1, dpaGood.2.1, dpaGood.2.2)

end DistLTLSynth.Char


