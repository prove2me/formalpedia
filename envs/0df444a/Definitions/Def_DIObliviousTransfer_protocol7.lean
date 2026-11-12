-- Prove2me | Definitions.Def_DIObliviousTransfer_protocol7
-- name    : DIObliviousTransfer_protocol7
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:13:05.779419+00:00
-- url     : https://prove2.me/theorems/ddbccf6c-3f81-4ced-a8f6-95c3aaa05fde
-- title:
--   Protocol 7: one-window packed string commitment, MODE (21) and $\mathrm{OpenVer}_{\mathrm{str}}$ (23)
-- statement:
--   This module transcribes Protocol 7, Steps 1–11. The physical experiment is that of Protocol 2, in one window, with inner bit commitments $\mathrm{Com}$ for every committed field.
--
--   In Step 9, Bob sends $\sigma$ and $M=\beta+R$ with $R\in B^\sigma_{0^q}$ and proves the packed source mode relation of Definition 14 with the ZK proof system. In Step 10, Alice opens $(X,C)$ on the selectors and sends the payload (22) with $f\in A^\sigma_{0^q}$ and $D\in\mathcal D_u$. In Step 11, Bob issues the receipt and retains the public record.
--
--   The native-opening predicate (23) checks the full table opening, canonical syntax, agreement with earlier openings, the recomputed pads, and solutions of the two extension systems with $\mathrm{sec}(D)=u$ and $\mathrm{sec}_\sigma(f)=0^q$.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Definition 14, p.46; Protocol 7, pp.47–48; (23), p.48

import Mathlib
import Definitions.Def_DIObliviousTransfer_protocol2
import Definitions.Def_DIObliviousTransfer_ComSpec
import Definitions.Def_DIObliviousTransfer_IsExtractableStringCommitment
import Definitions.Def_DIObliviousTransfer_ZKSpec

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), §5.2–5.3,
pp.46–48: Definition 14 (the packed source mode relation, (21)), Protocol 7 (the one-window packed
string commitment, Steps 1–11, with (22)) and the public native-opening predicate (23).

**Formalization Note** (decisions D14, D15, D16, D20 and encodings). Every committed field is
committed bit by bit with the bit commitment `Com` ("Separately opened fields have separate bit
handles", p.46); an opening of a set of bits sends `[b]` and the witness for each, checked by `Ver`.
MODE is proved with the proof system `ZK` for the relation `relMode` of Definition 14 (statement:
`1^λ`, the offset and label commitment transcripts, `V`, `π`, the test set, the opened audit,
erasure and selector masks, `(σ, M)` and the opened offsets on the test set; witness: `U'`, `β'`
and their native witnesses). The receiver's retained record `τ` is the public transcript needed by
(23): the table commitment transcripts, `π`, the selector and erasure masks, `(σ, M)`, the payload,
and the earlier table openings; the committer's native witness `w` is the full canonical table with
its opening witnesses. One device batch (`0`) of `L_q = kN₀m + t_A` coordinates with
`m = Next(max{100q, 100ℓ, s_λ})` (7), the committer answering rows; Step 12 (the native opening
request) is the predicate `openVer7`.
-/

open Code

/-- Commit to each bit of `bs` with `Com`: the list of `(τ_i, w_i)`. -/
def comBits (Com : BitCom) (lam : ℕ) (bs : Bits) : Prog (List (Bits × Bits)) :=
  bs.mapM fun b => do
    let z ← (OptionT.mk (Com.commit lam b) : Prog Bits)
    match unpack z with
    | [τ, w] => pure (τ, w)
    | _ => failure

/-- Receive `n` bit commitments: the records `τ_i`. -/
def recvComs (Com : BitCom) (lam n : ℕ) : Prog (List Bits) :=
  (List.range n).mapM fun _ => (OptionT.mk (Com.receive lam) : Prog Bits)

/-- The opening message of the bits at positions `S`. -/
def openMsg (S : List ℕ) (bs : Bits) (ws : List (Bits × Bits)) : Bits :=
  pack (S.map fun i => pack [[bs.getD i false], (ws.getD i ([], [])).2])

/-- Check an opening of the bits at positions `S` against the records `τs`; returns the bits. -/
def checkOpen (Com : BitCom) (lam : ℕ) (τs : List Bits) (S : List ℕ) (msg : Bits) : Prog Bits := do
  let items := unpack msg
  Prog.check (decide (items.length = S.length))
  (S.zip items).mapM fun p => match unpack p.2 with
    | [[b], w] => do Prog.check (Com.Ver lam (τs.getD p.1 []) b w); pure b
    | _ => failure

/-- The length `m` of Protocol 7 for capacity `q` (7). -/
noncomputable def m7 (lam ell q : ℕ) : ℕ := mOf lam ell q

/-- **Definition 14** (packed source mode relation, (21)) for `Com`, `N₀` and the capacity and
leakage functions. Statement `pack [1^λ, pack τU, V, π, T_A, T_B, J, E, pack τβ, σ, M, U_T]`,
witness `pack [U', β', pack wU, pack wβ]`. -/
noncomputable def relMode (C : CodeFamily) (Com : BitCom) (N₀ : ℕ) (ell q : ℕ → ℕ)
    (x wit : Bits) : Bool := by
  classical
  exact match unpack x, unpack wit with
  | [l, τUb, Vb, πb, TAb, Tb, Jb, Eb, τβb, σb, Mb, UTb], [Ub, βb, wUb, wβb] =>
    let lam := l.length
    let m := m7 lam (ell lam) (q lam)
    let L := LOf N₀ m
    let τU := unpack τUb
    let τβ := unpack τβb
    let wU := unpack wUb
    let wβ := unpack wβb
    let TA := support TAb
    match decTrits L Vb with
    | none => false
    | some V =>
      let s : SelData := { m := m, N₀ := N₀, π := (unpack πb).map bitsNat, T := Tb, J := Jb, beta := βb, E := Eb, U := fun a => decTrit (Ub.getD (2 * a) false) (Ub.getD (2 * a + 1) false), V := fun a => if h : a < L then V ⟨a, h⟩ else 0, σ := decVec m σb, M := decVec m Mb }
      let R : Fin m → F64 := fun i => s.M i + labelVec m βb
        i
      decide (Ub.length = 2 * L ∧ βb.length = kk * m ∧ τU.length = 2 * L ∧ τβ.length = kk * m ∧
        (∀ i < 2 * L, Com.Ver lam (τU.getD i []) (Ub.getD i false) (wU.getD i []) = true) ∧
        (∀ i < kk * m, Com.Ver lam (τβ.getD i []) (βb.getD i false) (wβ.getD i []) = true) ∧
        proj (tritPos TA) Ub = UTb ∧ (∀ a < L, (s.U a).isSome) ∧
        s.syntaxOK ∧ s.labelsOK ∧ R ∈ twist s.σ (C.B m (q lam)) ∧
        secBσ C m (q lam) s.σ R = 0)
  | _, _ => false

/-- The witness bound of `relMode`. -/
noncomputable def pwMode (Com : BitCom) (N₀ : ℕ) (ell q : ℕ → ℕ) : ℕ → ℕ :=
  fun n => (Finset.range (n + 1)).sup fun l =>
    let L := LOf N₀ (m7 l (ell l) (q l))
    (2 * L + kk * L) * (Com.wbound l + 16) + 64

/-- The public native-opening predicate (23), `OpenVer_str(τ, u, w)` of Protocol 7: `u ∈ F₂^q`,
all table openings, canonical syntax, agreement with the earlier openings, the recomputed pads,
the common values `D_i = (p¹_{i,j} + p⁰_{i,j})/e_j`, `f_i = Σ_j p⁰_{i,j} + M_i D_i`, and solutions of
the two extension systems into `D` and `A^σ` with `sec(D) = u`, `sec_σ(f) = 0^q`. -/
noncomputable def openVer7 (C : CodeFamily) (Com : BitCom) (N₀ : ℕ) (ell q : ℕ → ℕ) (lam : ℕ)
    (τ u w : Bits) : Bool := by
  classical
  exact match unpack τ with
  | [τTb, πb, Jb, Eb, σb, Mb, P, xcb, audb] =>
    let m := m7 lam (ell lam) (q lam)
    let n := kk * N₀ * m
    let τT := unpack τTb
    let items := unpack w
    let tbl : Bits := items.map fun it => ((unpack it).headD []).headD false
    let s : SelData := { m := m, N₀ := N₀, π := (unpack πb).map bitsNat, T := [], J := Jb, beta := [], E := Eb, U := fun _ => none, V := fun _ => 0, σ := decVec m σb, M := decVec m Mb }
    let audIdxs := (unpack audb).map fun e => bitsNat ((unpack e).headD [])
    decide (u.length = q lam ∧ items.length = 6 * n ∧ τT.length = 6 * n ∧
      (∀ i < 6 * n, ∃ b wi, unpack (items.getD i []) = [[b], wi] ∧
        Com.Ver lam (τT.getD i []) b wi = true) ∧
      (∀ idx < n, (tableEntry tbl idx).isSome) ∧
      proj (xcPos (selIdx N₀ m Jb)) tbl = xcb ∧
      (∀ e ∈ unpack audb, ∃ i v, unpack e = [i, v] ∧ proj (entryPos [bitsNat i]) tbl = v) ∧
      audIdxs.Nodup ∧
      ∃ fg, payExtensions C (q lam) s tbl (readPayload s P) = some fg ∧
        C.secB m (q lam) fg.1 = bitsSecret (q lam) u ∧ secAσ C m (q lam) s.σ fg.2 = 0)
  | _ => false

/-- **Protocol 7**, the committer (Alice): input `u ∈ F₂^q`; returns `pack [τ, w]`. -/
noncomputable def protocol7Commit (C : CodeFamily) (Com : BitCom)
    (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol) (N₀ : ℕ) (ηMS : ℝ) (ell q : ℕ → ℕ)
    (lam : ℕ) (u : Bits) : Prog Bits := do
  let m := m7 lam (ell lam) (q lam)
  let n := kk * N₀ * m
  let tA := tAOf m
  let L := n + tA
  -- Step 1
  let Xin ← sampleVec (sampleTrit lam) L
  let perm ← shuffle lam (List.range L)
  let TA := perm.take tA
  let wTA ← comBits Com lam (incidence L TA)
  -- Step 2 (Bob's offset commitments)
  let τU ← recvComs Com lam (2 * L)
  -- Step 3
  let V ← sampleVec (sampleTrit lam) L
  Prog.send (encTrits V)
  let ans ← Prog.dev 0 (encQuestions Xin)
  let Ain : ℕ → Fin 3 → Bool := fun a => rowOf (ansPair ans a)
  let τB ← recvComs Com lam (3 * L)
  -- Step 4
  let π ← shuffle lam ((List.range L).filter fun a => a ∉ TA)
  Prog.send (pack [openMsg (List.range L) (incidence L TA) wTA, pack (π.map encNat)])
  -- Step 5 (Bob's audit, label, erasure and selector commitments)
  let τT ← recvComs Com lam n
  let τβ ← recvComs Com lam (kk * m)
  let τE ← recvComs Com lam m
  let τJ ← recvComs Com lam n
  -- Step 6
  let Cs ← sampleVec Prog.coin L
  let entry : ℕ → Entry := fun a =>
    if h : a < L then (if Cs ⟨a, h⟩ then ⟨Xin ⟨a, h⟩, Ain a, true⟩ else ⟨0, ![false, false, false], false⟩)
    else ⟨0, ![false, false, false], false⟩
  let tbl := (π.map fun a => (entry a).enc).flatten
  let wTbl ← comBits Com lam tbl
  -- Step 7
  let o7 ← Prog.recv
  let (oT, oU, oB) := match unpack o7 with | [a, b, c] => (a, b, c) | _ => ([], [], [])
  let Tb ← checkOpen Com lam τT (List.range n) oT
  let Ub ← checkOpen Com lam τU (tritPos TA) oU
  let Bb ← checkOpen Com lam τB (colPos TA) oB
  let sAud : SelData := { m := m, N₀ := N₀, π := π, T := Tb, J := [], beta := [], E := [], U := fun _ => none, V := fun _ => 0, σ := fun _ => 1, M := fun _ => 0 }
  Prog.check (decide (∀ i < m, ∀ j < kk, (sAud.Tset i j).length = 1))
  let losses := (List.range tA).filter fun t =>
    let a := TA.getD t 0
    let y : Fin 3 := match decTrit (Ub.getD (2 * t) false) (Ub.getD (2 * t + 1) false) with
      | some ut => ut + (if h : a < L then V ⟨a, h⟩ else 0)
      | none => 0
    let col : Fin 3 → Bool := ![Bb.getD (3 * t) false, Bb.getD (3 * t + 1) false, Bb.getD (3 * t + 2) false]
    (entry a).C && !(MS (entry a).X y (entry a).A col)
  let tst := decide ((losses.length : ℝ) ≤ kappaTest ηMS * tA)
  Prog.send [tst]
  Prog.check tst
  let audIdx := (List.range n).filter fun t => Tb.getD t false
  let audOpen := openMsg (entryPos audIdx) tbl wTbl
  Prog.send audOpen
  let aud ← Prog.recv
  Prog.check (aud = [true])
  -- Step 8
  let o8 ← Prog.recv
  let (oE, oJ) := match unpack o8 with | [a, b] => (a, b) | _ => ([], [])
  let Eb ← checkOpen Com lam τE (List.range m) oE
  let Jb ← checkOpen Com lam τJ (List.range n) oJ
  let sSel : SelData := { sAud with J := Jb, E := Eb }
  Prog.check (decide ((support Eb).length ≤ eraseCap m ∧
    ∀ i < m, ∀ j < kk, if sSel.erased i then sSel.Jset i j = [] else
      (∀ t ∈ sSel.Jset i j, t ∉ sSel.Tset i j) ∧ (N₀ : ℝ) / 8 ≤ (sSel.Jset i j).length ∧
        ((sSel.Jset i j).length : ℝ) ≤ (N₀ : ℝ) / 2))
  Prog.send [true]
  -- Step 9 (Bob's (σ, M) and MODE proof)
  let σM ← Prog.recv
  let (σb, Mb) := match unpack σM with | [a, b] => (a, b) | _ => ([], [])
  let xMode := pack [List.replicate lam true, pack τU, encTrits V, pack (π.map encNat),
    incidence L TA, Tb, Jb, Eb, pack τβ, σb, Mb, Ub]
  let pfM := ZK (relMode C Com N₀ ell q) (pwMode Com N₀ ell q)
  let ok ← (OptionT.mk (pfM.codeB lam xMode) : Prog Bits)
  Prog.check (ok = [true])
  -- Step 10
  let xc := xcPos (selIdx N₀ m Jb)
  Prog.send (openMsg xc tbl wTbl)
  let σ := decVec m σb
  let Mv := decVec m Mb
  let cf ← sampleVec sampleF64 (C.dimA m (q lam))
  let cD ← sampleVec sampleF64 (C.dimB m (q lam))
  let f : Fin m → F64 := fun i => σ i * C.paramA m (q lam) 0 cf i
  let D : Fin m → F64 := C.paramB m (q lam) (bitsSecret (q lam) u) cD
  let sPay : SelData := { sSel with σ := σ, M := Mv }
  let payload ← honestPayload sPay tbl f D
  Prog.send payload
  -- Step 11 (receipt)
  let rcpt ← Prog.recv
  Prog.check (rcpt = [true])
  let audRec := pack (audIdx.map fun i => pack [encNat i, proj (entryPos [i]) tbl])
  let τ := pack [pack (wTbl.map Prod.fst), pack (π.map encNat), Jb, Eb, σb, Mb, payload,
    proj xc tbl, audRec]
  let w := pack ((List.range (6 * n)).map fun i => pack [[tbl.getD i false], (wTbl.getD i ([], [])).2])
  pure (pack [τ, w])

open Classical in
/-- **Protocol 7**, the receiver (Bob); returns its retained record `τ`. -/
noncomputable def protocol7Receive (C : CodeFamily) (Com : BitCom)
    (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol) (N₀ : ℕ) (ηMS : ℝ) (ell q : ℕ → ℕ)
    (lam : ℕ) : Prog Bits := do
  let m := m7 lam (ell lam) (q lam)
  let n := kk * N₀ * m
  let tA := tAOf m
  let L := n + tA
  -- Step 1
  let τTA ← recvComs Com lam L
  -- Step 2
  let U ← sampleVec (sampleTrit lam) L
  let wU ← comBits Com lam (encTrits U)
  -- Step 3
  let Vb ← Prog.recv
  let V ← match decTrits L Vb with | some V => pure V | none => failure
  let Y : Fin L → Fin 3 := fun a => U a + V a
  let ans ← Prog.dev 0 (encQuestions Y)
  let Bcol : ℕ → Fin 3 → Bool := fun a => colOf (ansPair ans a)
  let Brec := (List.range L).flatMap fun a => List.ofFn (Bcol a)
  let wB ← comBits Com lam Brec
  -- Step 4
  let o4 ← Prog.recv
  let (oTA, πb) := match unpack o4 with | [a, b] => (a, b) | _ => ([], [])
  let TAb ← checkOpen Com lam τTA (List.range L) oTA
  let TA := support TAb
  let π := (unpack πb).map bitsNat
  Prog.check (decide (TA.length = tA ∧ π.length = n ∧ π.Nodup ∧ ∀ a ∈ π, a < L ∧ a ∉ TA))
  -- Step 5
  let Yat : ℕ → Fin 3 := fun a => if h : a < L then Y ⟨a, h⟩ else 0
  let auditT ← sampleVec (sampleBelow N₀ lam) (kk * m)
  let betaV ← sampleVec Prog.coin (kk * m)
  let blk : ℕ → ℕ → ℕ := fun i j => i * kk + j
  let audAt : ℕ → ℕ → ℕ := fun i j => if h : blk i j < kk * m then auditT ⟨blk i j, h⟩ else 0
  let betaAt : ℕ → ℕ → Bool := fun i j => if h : blk i j < kk * m then betaV ⟨blk i j, h⟩ else false
  let cand : ℕ → ℕ → Fin 3 → List ℕ := fun i j b =>
    (List.range N₀).filter fun t => t ≠ audAt i j ∧ Yat (blockPos π N₀ i j t) = b
  let erasedSym : ℕ → Bool := fun i => decide (∃ j < kk, ∃ b : Fin 3, b ≠ 2 ∧
    ¬ ((N₀ : ℝ) / 8 ≤ (cand i j b).length ∧ ((cand i j b).length : ℝ) ≤ (N₀ : ℝ) / 2))
  let Jsel : ℕ → ℕ → List ℕ := fun i j =>
    if erasedSym i then [] else cand i j (if betaAt i j then 1 else 0)
  let Tinc := (List.range n).map fun idx => decide (idx % N₀ = audAt (idx / N₀ / kk) (idx / N₀ % kk))
  let Jinc := (List.range n).map fun idx => decide (idx % N₀ ∈ Jsel (idx / N₀ / kk) (idx / N₀ % kk))
  let betaB := (List.range (kk * m)).map fun t => betaAt (t / kk) (t % kk)
  let Einc := (List.range m).map erasedSym
  let wT ← comBits Com lam Tinc
  let wβ ← comBits Com lam betaB
  let wE ← comBits Com lam Einc
  let wJ ← comBits Com lam Jinc
  -- Step 6 (Alice's table commitments)
  let τTbl ← recvComs Com lam (6 * n)
  -- Step 7
  Prog.send (pack [openMsg (List.range n) Tinc wT, openMsg (tritPos TA) (encTrits U) wU,
    openMsg (colPos TA) Brec wB])
  let tst ← Prog.recv
  Prog.check (tst = [true])
  let audIdx := (List.range n).filter fun t => Tinc.getD t false
  let audOpen ← Prog.recv
  let audVals ← checkOpen Com lam τTbl (entryPos audIdx) audOpen
  let audEntries := (List.range audIdx.length).map fun t => decEntry ((audVals.drop (6 * t)).take 6)
  Prog.check (decide (∀ e ∈ audEntries, e.isSome))
  let audLoss := ((List.range audIdx.length).filter fun t =>
    let a := π.getD (audIdx.getD t 0) 0
    match audEntries.getD t none with
    | some e => e.C && (e.A (Yat a) != Bcol a e.X)
    | none => false).length
  let aud := decide ((Einc.filter id).length ≤ eraseCap m ∧ (audLoss : ℝ) ≤ kappaAud N₀ ηMS * kk * m)
  Prog.send [aud]
  Prog.check aud
  -- Step 8
  Prog.send (pack [openMsg (List.range m) Einc wE, openMsg (List.range n) Jinc wJ])
  let sel ← Prog.recv
  Prog.check (sel = [true])
  -- Step 9
  let σ ← sampleVec (sampleF64Star m) m
  let cR ← sampleVec sampleF64 (C.dimB m (q lam))
  let R : Fin m → F64 := fun i => σ i * C.paramB m (q lam) 0 cR i
  let Mv : Fin m → F64 := fun i => labelVec m betaB i + R i
  Prog.send (pack [encVec σ, encVec Mv])
  let xMode := pack [List.replicate lam true, pack (wU.map Prod.fst), Vb, pack (π.map encNat),
    incidence L TA, Tinc, Jinc, Einc, pack (wβ.map Prod.fst), encVec σ, encVec Mv,
    proj (tritPos TA) (encTrits U)]
  let witMode := pack [encTrits U, betaB, pack (wU.map Prod.snd), pack (wβ.map Prod.snd)]
  let pfM := ZK (relMode C Com N₀ ell q) (pwMode Com N₀ ell q)
  let _ ← (OptionT.mk (pfM.codeA lam (pack [xMode, witMode])) : Prog Bits)
  -- Step 10 (openings of (X, C) on the selectors and the payload)
  let xc := xcPos (selIdx N₀ m Jinc)
  let oXC ← Prog.recv
  let xcVals ← checkOpen Com lam τTbl xc oXC
  let payload ← Prog.recv
  -- Step 11
  let s : SelData := { m := m, N₀ := N₀, π := π, T := Tinc, J := Jinc, beta := betaB, E := Einc, U := fun _ => none, V := fun _ => 0, σ := σ, M := Mv }
  Prog.check (decide (∀ i < m, s.erased i = false → ∀ j < kk, ∀ b : Bool,
    ∃ S F, unpack (readPayload s payload i j b) = [S, F] ∧ F.length = 6 ∧
      S.length = kk * (s.Jset i j).length) ∧
    ∀ t < (selIdx N₀ m Jinc).length, (decTrit (xcVals.getD (3 * t) false) (xcVals.getD (3 * t + 1) false)).isSome)
  Prog.send [true]
  let audRec := pack ((List.range audIdx.length).map fun t =>
    pack [encNat (audIdx.getD t 0), (audVals.drop (6 * t)).take 6])
  pure (pack [pack τTbl, pack (π.map encNat), Jinc, Einc, encVec σ, encVec Mv, payload, xcVals, audRec])

/-- **Protocol 7** as a string commitment: one batch of `L_q` coordinates (the committer
answering rows), one budget group, native opening (23). -/
noncomputable def protocol7 (C : CodeFamily) (Com : BitCom)
    (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol) (N₀ : ℕ) (ηMS : ℝ) (ell q : ℕ → ℕ) : StrCom where
  commit := fun lam u => (protocol7Commit C Com ZK N₀ ηMS ell q lam u).run
  receive := fun lam => (protocol7Receive C Com ZK N₀ ηMS ell q lam).run
  OpenVer := openVer7 C Com N₀ ell q
  nb := fun _ => 1
  ng := fun _ => 1
  group := fun _ _ => 0
  coords := fun lam _ => LOf N₀ (m7 lam (ell lam) (q lam))
  committerRows := fun _ _ => true
  steps := fun lam => 2 ^ (LOf N₀ (m7 lam (ell lam) (q lam)) * (Com.wbound lam + 64) + lam)
  wbound := fun lam => 6 * kk * N₀ * m7 lam (ell lam) (q lam) * (Com.wbound lam + 16)

end DIObliviousTransfer


