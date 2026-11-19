-- Prove2me | Definitions.Def_APSCounting893_Main_TrailingVerifierProgram
-- name    : APSCounting893_Main_TrailingVerifierProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:40:35.359244+00:00
-- url     : https://prove2.me/theorems/f73dc1ea-10e0-4296-89a2-9faad85db7b2
-- title:
--   The finite trailing-coefficient verifier program
-- statement:
--   For each fixed number $k$ of parameter variables, this module specifies the finite register program used to verify a trailing-coefficient candidate.
--
--   $$P_k=\operatorname{assemble}(\mathcal{T}_k,\operatorname{outerPair}).$$
--
--   The finite table $\mathcal{T}_k$ contains parsing, copying, binary-length counting, canonical integer encoding, exponent comparison and coefficient-query instructions. Its registers include the original input word, candidate and universal exponent fields, temporary buffers and three query words. The assembly operation expands each word instruction into finitely many single-register instructions. A query register is consumed by its oracle instruction.
--
--   The module also defines configurations of this program and the predicate that its four temporary buffers are empty. It supplies data and transition functions. The query-building identities, parser behavior, runtime bound and oracle-polynomial-time theorem are separate proof targets.
--
--   **Formalization Note** This is an auxiliary implementation for Lemma 6.5. It retains the exact coefficient-query delimiter and constructs the final query with exponent zero for $T$.
-- source:
--   Finite-register implementation of the inner predicate in Agarwal, Hari, Pandey, Shukla, STOC 2027 submission #893, Lemma 6.5, p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_OracleProofPrimitives

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

inductive WordOp (Q : Type) (r : ℕ) where
  | jump (next : Q)
  | push (dst : Fin (r + 2)) (b : Bool) (next : Q)
  | clear (reg : Fin (r + 2)) (next : Q)
  | reverse (src dst : Fin (r + 2)) (next : Q)
  | copy (src dst tmp scratch : Fin (r + 2)) (next : Q)
  | pair (src dst : Fin (r + 2)) (next : Q) (failure : Bool)
  | nat (src counter dst : Fin (r + 2)) (next : Q) (failure : Bool)
  | length (src counter tmp : Fin (r + 2)) (next : Q)
  | encodeNat (first second dst : Fin (r + 2)) (next : Q)
  | prepend (dst : Fin (r + 2)) (word : Word) (next : Q)
  | check (src : Fin (r + 2)) (word : Word) (next : Q) (failure : Bool)
  | compareLength (left right : Fin (r + 2)) (less equal greater : Q)
  | compareLex (left right : Fin (r + 2)) (less equal greater : Q)
  | query (reg : Fin (r + 2)) (yes no : Q)
  | halt (b : Bool)

def WordOp.constantLength {Q : Type} {r : ℕ} : WordOp Q r → ℕ
  | .prepend _ word _ => word.length
  | .check _ word _ _ => word.length
  | _ => 0

noncomputable def assemblyConstantBound {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) : ℕ :=
  ∑ q, (table q).constantLength

inductive AssemblyPhase (D : ℕ) where
  | entry | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10
  | constant (i : Fin (D + 1))
  deriving DecidableEq, Fintype

inductive AssemblyControl (Q : Type) (D : ℕ) where
  | at (site : Q) (phase : AssemblyPhase D)
  | halt (b : Bool)
  deriving DecidableEq, Fintype

open AssemblyControl AssemblyPhase in
noncomputable def assemble {Q : Type} [Fintype Q] {r : ℕ} (table : Q → WordOp Q r) (initial : Q) :
    StackProgram (AssemblyControl Q (assemblyConstantBound table)) r where
  initial := .at initial .entry
  transition := fun control => match control with
    | .halt b => .halt b
    | .at q phase =>
      let go := fun next => AssemblyControl.at next AssemblyPhase.entry
      let here := fun phase => AssemblyControl.at q phase
      match table q with
      | .jump next => .jump (go next)
      | .push dst b next => .push dst b (go next)
      | .clear reg next => .pop reg (here .entry) (here .entry) (go next)
      | .reverse src dst next => match phase with
        | .entry => .pop src (here .p1) (here .p2) (go next)
        | .p1 => .push dst false (here .entry)
        | .p2 => .push dst true (here .entry)
        | _ => .halt false
      | .copy src dst tmp scratch next => match phase with
        | .entry => .pop src (here .p1) (here .p2) (here .p5)
        | .p1 => .push scratch false (here .p3)
        | .p2 => .push scratch true (here .p4)
        | .p3 => .push tmp false (here .entry)
        | .p4 => .push tmp true (here .entry)
        | .p5 => .pop tmp (here .p6) (here .p7) (here .p8)
        | .p6 => .push src false (here .p5)
        | .p7 => .push src true (here .p5)
        | .p8 => .pop scratch (here .p9) (here .p10) (go next)
        | .p9 => .push dst false (here .p8)
        | .p10 => .push dst true (here .p8)
        | _ => .halt false
      | .pair src dst next failure => match phase with
        | .entry => .pop src (go next) (here .p1) (.halt failure)
        | .p1 => .pop src (here .p2) (here .p3) (.halt failure)
        | .p2 => .push dst false (here .entry)
        | .p3 => .push dst true (here .entry)
        | _ => .halt false
      | .nat src counter dst next failure => match phase with
        | .entry => .pop src (here .p2) (here .p1) (.halt failure)
        | .p1 => .push counter true (here .entry)
        | .p2 => .pop counter (here .p3) (here .p3) (here .p6)
        | .p3 => .pop src (here .p4) (here .p5) (.halt failure)
        | .p4 => .push dst false (here .p2)
        | .p5 => .push dst true (here .p2)
        | .p6 => .peek dst (.halt failure) (go next) (go next)
        | _ => .halt false
      | .length src counter tmp next => match phase with
        | .entry => .pop src (here .p1) (here .p1) (go next)
        | .p1 => .pop counter (here .p2) (here .p3) (here .p2)
        | .p2 => .push counter true (here .p4)
        | .p3 => .push tmp false (here .p1)
        | .p4 => .pop tmp (here .p5) (here .p6) (here .entry)
        | .p5 => .push counter false (here .p4)
        | .p6 => .push counter true (here .p4)
        | _ => .halt false
      | .encodeNat first second dst next => match phase with
        | .entry => .pop first (here .p1) (here .p2) (here .p3)
        | .p1 => .push dst false (here .entry)
        | .p2 => .push dst true (here .entry)
        | .p3 => .push dst false (here .p4)
        | .p4 => .pop second (here .p5) (here .p5) (go next)
        | .p5 => .push dst true (here .p4)
        | _ => .halt false
      | .prepend dst word next => match phase with
        | .entry => .jump (here (.constant 0))
        | .constant i => if h : i.val < word.length then
            .push dst (word.reverse[i.val]'(by simpa using h))
              (here (.constant (Fin.ofNat _ (i.val + 1))))
            else .jump (go next)
        | _ => .halt false
      | .check src word next failure => match phase with
        | .entry => .jump (here (.constant 0))
        | .constant i => if h : i.val < word.length then
            let target := here (.constant (Fin.ofNat _ (i.val + 1)))
            .pop src (if word[i.val] then .halt failure else target)
              (if word[i.val] then target else .halt failure) (.halt failure)
            else .jump (go next)
        | _ => .halt false
      | .compareLength left right less equal greater => match phase with
        | .entry => .pop left (here .p1) (here .p1) (here .p2)
        | .p1 => .pop right (here .entry) (here .entry) (go greater)
        | .p2 => .pop right (go less) (go less) (go equal)
        | _ => .halt false
      | .compareLex left right less equal greater => match phase with
        | .entry => .pop left (here .p1) (here .p2) (here .p3)
        | .p1 => .pop right (here .entry) (go less) (go greater)
        | .p2 => .pop right (go greater) (here .entry) (go greater)
        | .p3 => .pop right (go less) (go less) (go equal)
        | _ => .halt false
      | .query reg yes no => .query reg (go yes) (go no)
      | .halt b => .halt b


inductive TrailingReg (k : ℕ) where
  | outerRev | inner | xRev | x | natCount | copyTmp | copyScratch | first | second
  | lengthLSB | lengthMSB | inputPrefix | queryA | queryE | queryF | leftClone | rightClone
  | aField (i : Fin (k + 1)) | qA | eField (i : Fin (k + 1)) | qE | qF
  deriving DecidableEq, Fintype

noncomputable def trailingRegIndex {k : ℕ} (reg : TrailingReg k) : Fin (Fintype.card (TrailingReg k) + 2) :=
  ⟨2 + (Fintype.equivFin (TrailingReg k) reg).val, by have h := (Fintype.equivFin (TrailingReg k) reg).isLt; omega⟩

lemma trailingRegIndex_injective (k : ℕ) : Function.Injective (@trailingRegIndex k) := by
  intro a b h
  apply (Fintype.equivFin (TrailingReg k)).injective
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa only [trailingRegIndex, Nat.add_left_cancel_iff] using hv

@[simp] lemma trailingRegIndex_eq_iff {k : ℕ} (a b : TrailingReg k) :
    trailingRegIndex a = trailingRegIndex b ↔ a = b := (trailingRegIndex_injective k).eq_iff

@[simp] lemma trailingRegIndex_ne_zero {k : ℕ} (reg : TrailingReg k) : trailingRegIndex reg ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change 2 + _ = 0 % (Fintype.card (TrailingReg k) + 2) at hv
  simp at hv

@[simp] lemma trailingRegIndex_ne_one {k : ℕ} (reg : TrailingReg k) : trailingRegIndex reg ≠ 1 := by
  intro h
  have hv := congrArg Fin.val h
  change 2 + _ = 1 % (Fintype.card (TrailingReg k) + 2) at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  omega

inductive TrailingQuery where
  | candidate | earlier | final
  deriving DecidableEq, Fintype

inductive TrailingBuildPhase (k : ℕ) where
  | bitFirst | bitSecond | bitEncode | numerator
  | fieldStart (n : Fin (k + 2))
  | fieldSecond (i : Fin (k + 1)) | fieldEncode (i : Fin (k + 1))
  | countPrefix | inputPrefix
  deriving DecidableEq, Fintype

inductive TrailingSite (k : ℕ) where
  | outerPair | outerReverse | innerPair | xReverse | aPrefix
  | aField (i : Fin (k + 1)) | aBit
  | copyXForLength | lengthX | reverseLength | copyXPrefix | copyLengthFirst | copyLengthSecond | encodeLength
  | uPrefix | eField (i : Fin (k + 1)) | eBit | finalBit
  | build (q : TrailingQuery) (phase : TrailingBuildPhase k)
  | compareBegin (i : Fin (k + 1)) | compareRight (i : Fin (k + 1))
  | compareLengths (i : Fin (k + 1)) | compareBits (i : Fin (k + 1))
  | askA | askE | askF | accept | reject
  deriving DecidableEq, Fintype

noncomputable def trailingQueryReg {k : ℕ} : TrailingQuery → Fin (Fintype.card (TrailingReg k) + 2)
  | .candidate => trailingRegIndex .queryA
  | .earlier => trailingRegIndex .queryE
  | .final => trailingRegIndex .queryF

noncomputable def trailingBitReg {k : ℕ} : TrailingQuery → Fin (Fintype.card (TrailingReg k) + 2)
  | .candidate => trailingRegIndex .qA
  | .earlier => trailingRegIndex .qE
  | .final => trailingRegIndex .qF

noncomputable def trailingFieldReg {k : ℕ} (q : TrailingQuery) (i : Fin (k + 1)) :
    Fin (Fintype.card (TrailingReg k) + 2) :=
  match q with
  | .candidate | .final => trailingRegIndex (.aField i)
  | .earlier => trailingRegIndex (.eField i)

def trailingAfterBuild (k : ℕ) : TrailingQuery → TrailingSite k
  | .candidate => .askA
  | .earlier => .build .final .bitFirst
  | .final => .compareBegin 0

def trailingNextA {k : ℕ} (i : Fin (k + 1)) : TrailingSite k :=
  if h : i.val + 1 < k + 1 then .aField ⟨i.val + 1, h⟩ else .aBit

def trailingNextE {k : ℕ} (i : Fin (k + 1)) : TrailingSite k :=
  if h : i.val + 1 < k + 1 then .eField ⟨i.val + 1, h⟩ else .eBit

def trailingNextCompare {k : ℕ} (i : Fin (k + 1)) : TrailingSite k :=
  if h : i.val + 1 < k + 1 then .compareBegin ⟨i.val + 1, h⟩ else .askF

open TrailingSite TrailingReg in
noncomputable def trailingTable (k : ℕ) : TrailingSite k → WordOp (TrailingSite k) (Fintype.card (TrailingReg k)) :=
  fun site =>
    let reg := @trailingRegIndex k
    let copyTo := fun src dst next => WordOp.copy src dst (reg .copyTmp) (reg .copyScratch) next
    let parseNat := fun src dst next failure => WordOp.nat src (reg .natCount) dst next failure
    match site with
    | .outerPair => .pair 0 (reg .outerRev) .outerReverse false
    | .outerReverse => .reverse (reg .outerRev) (reg .inner) .innerPair
    | .innerPair => .pair (reg .inner) (reg .xRev) .xReverse false
    | .xReverse => .reverse (reg .xRev) (reg .x) .aPrefix
    | .aPrefix => .check (reg .inner) (encodeNat (k + 1)) (.aField 0) false
    | .aField i => parseNat (reg .inner) (reg (.aField i)) (trailingNextA i) false
    | .aBit => parseNat (reg .inner) (reg .qA) .copyXForLength false
    | .copyXForLength => copyTo (reg .x) (reg .first) .lengthX
    | .lengthX => .length (reg .first) (reg .lengthLSB) (reg .second) .reverseLength
    | .reverseLength => .reverse (reg .lengthLSB) (reg .lengthMSB) .copyXPrefix
    | .copyXPrefix => copyTo (reg .x) (reg .inputPrefix) .copyLengthFirst
    | .copyLengthFirst => copyTo (reg .lengthMSB) (reg .first) .copyLengthSecond
    | .copyLengthSecond => copyTo (reg .lengthMSB) (reg .second) .encodeLength
    | .encodeLength => .encodeNat (reg .first) (reg .second) (reg .inputPrefix) (.build .candidate .bitFirst)
    | .uPrefix => .check 0 (encodeNat (k + 1)) (.eField 0) true
    | .eField i => parseNat 0 (reg (.eField i)) (trailingNextE i) true
    | .eBit => parseNat 0 (reg .qE) .finalBit true
    | .finalBit => parseNat 0 (reg .qF) (.build .earlier .bitFirst) true
    | .build q phase =>
        let target := trailingQueryReg (k := k) q
        let atBuild := fun phase => TrailingSite.build q phase
        match phase with
        | .bitFirst => copyTo (trailingBitReg (k := k) q) (reg .first) (atBuild .bitSecond)
        | .bitSecond => copyTo (trailingBitReg (k := k) q) (reg .second) (atBuild .bitEncode)
        | .bitEncode => .encodeNat (reg .first) (reg .second) target (atBuild .numerator)
        | .numerator => .prepend target [false, true] (atBuild (.fieldStart ⟨k + 1, by omega⟩))
        | .fieldStart n =>
            if h : n.val = 0 then .jump (atBuild .countPrefix) else
              let i : Fin (k + 1) := ⟨n.val - 1, by have hn := n.isLt; omega⟩
              if q = .final ∧ i = Fin.last k then
                .prepend target (encodeNat 0) (atBuild (.fieldStart ⟨i.val, by have hi := i.isLt; omega⟩))
              else copyTo (trailingFieldReg q i) (reg .first) (atBuild (.fieldSecond i))
        | .fieldSecond i => copyTo (trailingFieldReg q i) (reg .second) (atBuild (.fieldEncode i))
        | .fieldEncode i => .encodeNat (reg .first) (reg .second) target
            (atBuild (.fieldStart ⟨i.val, by have hi := i.isLt; omega⟩))
        | .countPrefix => .prepend target (encodeNat (k + 1)) (atBuild .inputPrefix)
        | .inputPrefix => copyTo (reg .inputPrefix) target (trailingAfterBuild k q)
    | .compareBegin i => if i.val < k then
        copyTo (reg (.eField i)) (reg .leftClone) (.compareRight i) else .jump .askF
    | .compareRight i => copyTo (reg (.aField i)) (reg .rightClone) (.compareLengths i)
    | .compareLengths i => .compareLength (reg .leftClone) (reg .rightClone) .askE (.compareBits i) .askF
    | .compareBits i => .compareLex (reg (.eField i)) (reg (.aField i)) .askE (trailingNextCompare i) .askF
    | .askA => .query (reg .queryA) .uPrefix .reject
    | .askE => .query (reg .queryE) .reject .askF
    | .askF => .query (reg .queryF) .reject .accept
    | .accept => .halt true
    | .reject => .halt false

noncomputable def trailingBaseProgram (k : ℕ) := assemble (trailingTable k) TrailingSite.outerPair


abbrev TrailingConfig (k : ℕ) := StackConfig
  (AssemblyControl (TrailingSite k) (assemblyConstantBound (trailingTable k))) (Fintype.card (TrailingReg k))

structure TrailingClean {k : ℕ} (cfg : TrailingConfig k) : Prop where
  first : cfg.regs (trailingRegIndex .first) = []
  second : cfg.regs (trailingRegIndex .second) = []
  tmp : cfg.regs (trailingRegIndex .copyTmp) = []
  scratch : cfg.regs (trailingRegIndex .copyScratch) = []


end APSCounting893.Main


