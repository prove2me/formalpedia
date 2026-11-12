-- Prove2me | Definitions.Def_DIObliviousTransfer_protocol2
-- name    : DIObliviousTransfer_protocol2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:10:11.810452+00:00
-- url     : https://prove2.me/theorems/cc79aca0-1369-4517-b618-c83f5c26b399
-- title:
--   Protocol 2: DI OT from commit-and-prove (with Definitions 12–13)
-- statement:
--   This module transcribes Protocol 2, Steps 1–15, in the commit-and-prove hybrid, with the predicates $P_{\mathrm{LABEL}}$ (Definition 12) and $P_{\mathrm{PAY}}$ (Definition 13).
--
--   The steps are: Alice's hidden test set; Bob's offsets; one window in which Alice inputs $X^{\mathrm{in}}$ and Bob $Y=U+V$; the opening of the test set and a fresh ordering; Bob's audits, labels, selectors and erasures; Alice's canonical anchored table; the sparse test and the global audit; selector disclosure; Bob's code mask $M=\beta+R$ with $R\in B^\sigma_d$ and the LABEL check; Alice's payload with $f\in A^\sigma_{S_0}$, $g\in D_{S_0+S_1}$ and the PAY check; and Bob's decoding.
--
--   The CP functionality uses Protocol 2's predicate language and its own request schedule. There is one device batch of $L$ coordinates.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Protocol 1, p.29; Definitions 12–13, pp.29–30; Protocol 2, pp.30–31

import Mathlib
import Definitions.Def_DIObliviousTransfer_SelData
import Definitions.Def_DIObliviousTransfer_idealCP

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), Protocol 1 (p.29),
Definitions 12–13 (pp.29–30) and Protocol 2 (pp.30–31): DI OT from commit-and-prove.

**Formalization Note** (decisions D10, D15, D16, D20, D22 and encodings). The protocol is in the
hybrid model of the commit-and-prove functionality with the predicate language `L2`: projections
`[π_S(M) = z]`, `P_LABEL` (Definition 12) and `P_PAY` (Definition 13); its authorized schedule
`sched2` admits exactly the protocol's own sequence of requests (owner, kind, records, predicate
kind). Records: `0` Alice's test-set incidence (`L` bits), `1` Bob's offsets (two bits per
trit), `2` Bob's columns (three bits each), `3` `M_B = enc((T_{i,j}), (J_{i,j}), (β_{i,j}), E)`
(audit and selector incidence over data positions, `km` labels, `m` erasure flags), `4` Alice's
table `M_A` (six bits per data position) (10). One device batch (`0`), of `L = kN₀m + t_A`
coordinates, Alice answering rows. Constants: `m` from (7) with `q = 1`; `κ_test`, `κ_aud` from
(8); `δ∗ = 1/2`, so `C_a ← Bern(1 − δ∗)` is a fair coin. Every failed check is a global abort.
-/

open Code

/-- The predicates of Protocol 2. -/
inductive P2Pred where
  | proj (S : List ℕ)
  | label
  | pay

/-- Encoding of the predicates. -/
def P2Pred.enc : P2Pred → Bits
  | .proj S => pack [encNat 0, pack (S.map encNat)]
  | .label => pack [encNat 1]
  | .pay => pack [encNat 2]

/-- Decoding of the predicates. -/
def P2Pred.dec (b : Bits) : Option P2Pred :=
  match unpack b with
  | [t, S] => if bitsNat t = 0 then some (.proj ((unpack S).map bitsNat)) else none
  | [t] => if bitsNat t = 1 then some .label else if bitsNat t = 2 then some .pay else none
  | _ => none

/-- `m` of (7) for one-bit OT at `λ` and leakage `ℓ`. -/
noncomputable def mOT (lam ell : ℕ) : ℕ := mOf lam ell 1

/-- The public parameters `(V, T_A, π, σ, M)` of `P_LABEL` and the record contents `(U, M_B)`
as selector data. -/
noncomputable def labelData (N₀ m L : ℕ) (contents y : Bits) : Option SelData :=
  match unpack y with
  | [Vb, TAb, πb, σb, Mb] =>
    let n := kk * N₀ * m
    let U := contents.take (2 * L)
    let MB := contents.drop (2 * L)
    match decTrits L Vb with
    | some V => some
        { m := m, N₀ := N₀, π := (unpack πb).map bitsNat, T := MB.take n, J := (MB.drop n).take n, beta := (MB.drop (2 * n)).take (kk * m), E := (MB.drop (2 * n + kk * m)).take m, U := fun a => decTrit (U.getD (2 * a) false) (U.getD (2 * a + 1) false), V := fun a => if h : a < L then V ⟨a, h⟩ else 0, σ := decVec m σb, M := decVec m Mb }
    | none => none
  | _ => none

/-- **Definition 12** (`P_LABEL`): syntax, the selector conditions, `U_a + V_a = β_{i,j}` on the
selectors, `σ ∈ (F₆₄^*)^m`, `R = M + β ∈ B^σ` and `sec_σ(R) ∈ {0, 1}`. -/
noncomputable def labelPred (C : CodeFamily) (N₀ : ℕ) (m : ℕ) (contents y : Bits) : Bool := by
  classical
  exact
  let L := LOf N₀ m
  match labelData N₀ m L contents y with
  | some s => decide (contents.length = 2 * L + 2 * (kk * N₀ * m) + kk * m + m ∧
      (unpack y).getD 1 [] = incidence L (support ((unpack y).getD 1 [])) ∧
      s.syntaxOK ∧ s.labelsOK ∧ (∀ a < L, (s.U a).isSome) ∧
      (fun i => s.M i + labelVec s.m s.beta i) ∈ twist s.σ (C.B s.m 1) ∧
      IsBinary (secBσ C s.m 1 s.σ (fun i => s.M i + labelVec s.m s.beta i)))
  | none => false

/-- **Definition 13** (`P_PAY`) on Alice's table `M_A` with public
`(π, J, E, σ, M, payload)`: dimensions, canonical syntax, the branch equations, extensions
`g ∈ D`, `f ∈ A^σ`, and `s₀ = sec_σ(f) ∈ {0,1}`, `s₁ = sec_σ(f) + sec(g) ∈ {0,1}`. -/
noncomputable def payPred (C : CodeFamily) (N₀ : ℕ) (m : ℕ) (MA y : Bits) : Bool := by
  classical
  exact
  match unpack y with
  | [πb, Jb, Eb, σb, Mb, P] =>
    let n := kk * N₀ * m
    let s : SelData := { m := m, N₀ := N₀, π := (unpack πb).map bitsNat, T := [], J := Jb, beta := [], E := Eb, U := fun _ => none, V := fun _ => 0, σ := decVec m σb, M := decVec m Mb }
    decide (MA.length = 6 * n ∧ Jb.length = n ∧ Eb.length = m ∧
      (∀ idx < n, (tableEntry MA idx).isSome) ∧
      ∃ fg, payExtensions C 1 s MA (readPayload s P) = some fg ∧
        IsBinary (secAσ C m 1 s.σ fg.2) ∧
        IsBinary (fun t => secAσ C m 1 s.σ fg.2 t + C.secB m 1 fg.1 t))
  | _ => false

/-- The predicate language of Protocol 2 at length `m`. -/
noncomputable def L2 (C : CodeFamily) (N₀ m : ℕ) : PredLang where
  Pred := P2Pred
  enc := P2Pred.enc
  dec := P2Pred.dec
  eval := fun P M y => match P with
    | .proj S => decide (proj S M = y)
    | .label => labelPred C N₀ m M y
    | .pay => payPred C N₀ m M y

/-- The kind of the `k`-th request of Protocol 2: owner, `0` commit or `1` check, records, and
predicate tag (`0` projection, `1` LABEL, `2` PAY). -/
def p2Schedule : List (Bool × ℕ × List ℕ × ℕ) :=
  [(true, 0, [0], 0), (false, 0, [1], 0), (false, 0, [2], 0), (true, 1, [0], 0),
   (false, 0, [3], 0), (true, 0, [4], 0), (false, 1, [3], 0), (false, 1, [1], 0),
   (false, 1, [2], 0), (true, 1, [4], 0), (false, 1, [3], 0), (false, 1, [1, 3], 1),
   (true, 1, [4], 0), (true, 1, [4], 2)]

/-- The authorized schedule of Protocol 2: the `k`-th accepted command has the prescribed owner,
kind, records and predicate kind. -/
def sched2 (hist : List (Bool × Bits)) (c : Bool × Bits) : Bool :=
  match p2Schedule[hist.length]? with
  | none => false
  | some (p, kind, ids, ptag) =>
    decide (c.1 = p) && match unpack c.2 with
      | [t, i, l, _] =>
        if kind = 0 then decide (bitsNat t = 0 ∧ [bitsNat i] = ids)
        else decide (bitsNat t = 1 ∧ (unpack i).map bitsNat = ids) &&
          match P2Pred.dec l with
          | some (.proj _) => ptag == 0
          | some .label => ptag == 1
          | some .pay => ptag == 2
          | none => false
      | _ => false

/-- A CP commit command. -/
def commitCmd (id len : ℕ) (M : Bits) : Bits := pack [encNat 0, encNat id, encNat len, M]

/-- A CP check command. -/
def checkCmd (ids : List ℕ) (P : Bits) (y : Bits) : Bits :=
  pack [encNat 1, pack (ids.map encNat), P, y]

/-- Read a certificate `pack [pack [1, ids, P, y], [true]]`: returns `(ids, P, y)`. -/
def readCert (c : Bits) : Option (List ℕ × Bits × Bits) :=
  match unpack c with
  | [req, [true]] => match unpack req with
    | [t, ids, P, y] => if bitsNat t = 1 then some ((unpack ids).map bitsNat, P, y) else none
    | _ => none
  | _ => none

/-- Wait for the certificate of the prescribed request on `ids` with predicate `P` and return its
public value `y`. -/
def waitCert (ids : List ℕ) (P : Bits) : Prog Bits := do
  let c ← Prog.wait
  match readCert c with
  | some (ids', P', y) => do Prog.check (decide (ids' = ids ∧ P' = P)); pure y
  | none => failure

/-- Positions of trit `a` in the offset record. -/
def tritPos (S : List ℕ) : List ℕ := S.flatMap fun a => [2 * a, 2 * a + 1]

/-- Positions of column `a` in the column record. -/
def colPos (S : List ℕ) : List ℕ := S.flatMap fun a => [3 * a, 3 * a + 1, 3 * a + 2]

/-- Positions of the entries of data indices `S` in the table (six bits each). -/
def entryPos (S : List ℕ) : List ℕ := S.flatMap fun i => (List.range 6).map fun t => 6 * i + t

/-- Positions of `(X_a, C_a)` of data indices `S` in the table. -/
def xcPos (S : List ℕ) : List ℕ := S.flatMap fun i => [6 * i, 6 * i + 1, 6 * i + 5]

/-- The data indices of all selectors. -/
def selIdx (N₀ m : ℕ) (J : Bits) : List ℕ := (List.range (kk * N₀ * m)).filter fun t => J.getD t false

/-- Field element `0` or `1` of a bit. -/
noncomputable def bitF (b : Bool) : F64 := if b then 1 else 0

/-- **Protocol 2**, Alice (sender), input `[S₀, S₁]`. -/
noncomputable def protocol2A (C : CodeFamily) (N₀ : ℕ) (ηMS : ℝ) (ell : ℕ → ℕ) (lam : ℕ)
    (inp : Bits) : Prog Bits := do
  let m := mOT lam (ell lam)
  let n := kk * N₀ * m
  let tA := tAOf m
  let L := n + tA
  let S0 := inp.getD 0 false
  let S1 := inp.getD 1 false
  -- Step 1
  let Xin ← sampleVec (sampleTrit lam) L
  let V ← sampleVec (sampleTrit lam) L
  let perm ← shuffle lam (List.range L)
  let TA := perm.take tA
  let _ ← Prog.call (commitCmd 0 L (incidence L TA))
  -- Step 2 (Bob's offset receipt)
  let _ ← Prog.wait
  -- Step 3
  Prog.send (encTrits V)
  let ans ← Prog.dev 0 (encQuestions Xin)
  let Ain : ℕ → Fin 3 → Bool := fun a => rowOf (ansPair ans a)
  -- Step 4 (Bob's column receipt)
  let _ ← Prog.wait
  -- Step 5
  let _ ← Prog.call (checkCmd [0] (P2Pred.proj (List.range L)).enc (incidence L TA))
  let π ← shuffle lam ((List.range L).filter fun a => a ∉ TA)
  Prog.send (pack (π.map encNat))
  -- Step 6 (Bob's M_B receipt)
  let _ ← Prog.wait
  -- Step 7
  let Cs ← sampleVec Prog.coin L
  let entry : ℕ → Entry := fun a =>
    if h : a < L then (if Cs ⟨a, h⟩ then ⟨Xin ⟨a, h⟩, Ain a, true⟩ else ⟨0, ![false, false, false], false⟩)
    else ⟨0, ![false, false, false], false⟩
  let MA := (π.map fun a => (entry a).enc).flatten
  let _ ← Prog.call (commitCmd 4 (6 * n) MA)
  -- Step 8 (Bob's openings: audit masks, offsets and columns on T_A)
  let Tb ← waitCert [3] (P2Pred.proj (List.range n)).enc
  let Ub ← waitCert [1] (P2Pred.proj (tritPos TA)).enc
  let Bb ← waitCert [2] (P2Pred.proj (colPos TA)).enc
  -- Step 9
  let sAud : SelData := { m := m, N₀ := N₀, π := π, T := Tb, J := [], beta := [], E := [], U := fun _ => none, V := fun _ => 0, σ := fun _ => 1, M := fun _ => 0 }
  Prog.check (decide (Tb.length = n ∧ ∀ i < m, ∀ j < kk, (sAud.Tset i j).length = 1))
  let Uts := decTrits tA Ub
  Prog.check (Uts.isSome ∧ Bb.length = 3 * tA)
  let losses := (List.range tA).filter fun t =>
    let a := TA.getD t 0
    let u : Fin 3 := match Uts with
      | some fu => if h : t < tA then fu ⟨t, h⟩ else 0
      | none => 0
    let y := u + (if h : a < L then V ⟨a, h⟩ else 0)
    let col : Fin 3 → Bool := ![Bb.getD (3 * t) false, Bb.getD (3 * t + 1) false, Bb.getD (3 * t + 2) false]
    (entry a).C && !(MS (entry a).X y (entry a).A col)
  let tst := decide ((losses.length : ℝ) ≤ kappaTest ηMS * tA)
  Prog.send [tst]
  Prog.check tst
  let audIdx := (List.range n).filter fun t => Tb.getD t false
  let _ ← Prog.call (checkCmd [4] (P2Pred.proj (entryPos audIdx)).enc (proj (entryPos audIdx) MA))
  -- Step 10
  let aud ← Prog.recv
  Prog.check (aud = [true])
  let ES ← waitCert [3] (P2Pred.proj ((List.range n).map (· + n) ++
    (List.range m).map (· + (2 * n + kk * m)))).enc
  -- Step 11
  let Jb := ES.take n
  let Eb := ES.drop n
  let sSel : SelData := { sAud with J := Jb, E := Eb }
  Prog.check (decide (ES.length = n + m ∧ (support Eb).length ≤ eraseCap m ∧
    ∀ i < m, ∀ j < kk, if sSel.erased i then sSel.Jset i j = [] else
      (∀ t ∈ sSel.Jset i j, t ∉ sSel.Tset i j) ∧ (N₀ : ℝ) / 8 ≤ (sSel.Jset i j).length ∧
        ((sSel.Jset i j).length : ℝ) ≤ (N₀ : ℝ) / 2))
  Prog.send [true]
  -- Step 12 (Bob's σ, M and LABEL)
  let σM ← Prog.recv
  let (σb, Mb) := match unpack σM with | [a, b] => (a, b) | _ => ([], [])
  let _ ← waitCert [1, 3] P2Pred.label.enc
    |>.bind fun y => do Prog.check (decide (y = pack [encTrits V, incidence L TA,
      pack (π.map encNat), σb, Mb])); pure y
  -- Step 13
  let σ := decVec m σb
  let Mv := decVec m Mb
  let cf ← sampleVec sampleF64 (C.dimA m 1)
  let cg ← sampleVec sampleF64 (C.dimB m 1)
  let f : Fin m → F64 := fun i => σ i * C.paramA m 1 (fun _ => bitF S0) cf i
  let g : Fin m → F64 := C.paramB m 1 (fun _ => bitF S0 + bitF S1) cg
  let sPay : SelData := { sSel with σ := σ, M := Mv }
  let payload ← honestPayload sPay MA f g
  Prog.send payload
  let xc := xcPos (selIdx N₀ m Jb)
  let _ ← Prog.call (checkCmd [4] (P2Pred.proj xc).enc (proj xc MA))
  let _ ← Prog.call (checkCmd [4] P2Pred.pay.enc (pack [pack (π.map encNat), Jb, Eb, σb, Mb, payload]))
  -- Step 14 (Bob's completion signal)
  let _ ← Prog.recv
  -- Step 15
  pure []

/-- **Protocol 2**, Bob (receiver), input `[d]`. -/
noncomputable def protocol2B (C : CodeFamily) (N₀ : ℕ) (ηMS : ℝ) (ell : ℕ → ℕ) (lam : ℕ)
    (inp : Bits) : Prog Bits := do
  let m := mOT lam (ell lam)
  let n := kk * N₀ * m
  let tA := tAOf m
  let L := n + tA
  let d := inp.getD 0 false
  -- Step 1 (Alice's test-set receipt)
  let _ ← Prog.wait
  -- Step 2
  let U ← sampleVec (sampleTrit lam) L
  let _ ← Prog.call (commitCmd 1 (2 * L) (encTrits U))
  -- Step 3
  let Vb ← Prog.recv
  let V ← match decTrits L Vb with | some V => pure V | none => failure
  -- Step 4
  let Y : Fin L → Fin 3 := fun a => U a + V a
  let ans ← Prog.dev 0 (encQuestions Y)
  let Bcol : ℕ → Fin 3 → Bool := fun a => colOf (ansPair ans a)
  let _ ← Prog.call (commitCmd 2 (3 * L) ((List.range L).flatMap fun a => List.ofFn (Bcol a)))
  -- Step 5
  let TAb ← waitCert [0] (P2Pred.proj (List.range L)).enc
  let TA := support TAb
  Prog.check (decide (TAb.length = L ∧ TA.length = tA))
  let πb ← Prog.recv
  let π := (unpack πb).map bitsNat
  Prog.check (decide (π.length = n ∧ π.Nodup ∧ ∀ a ∈ π, a < L ∧ a ∉ TA))
  -- Step 6
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
  let Tinc := (List.range n).map fun idx =>
    decide (idx % N₀ = audAt (idx / N₀ / kk) (idx / N₀ % kk))
  let Jinc := (List.range n).map fun idx =>
    decide (idx % N₀ ∈ Jsel (idx / N₀ / kk) (idx / N₀ % kk))
  let betaB := (List.range (kk * m)).map fun t => betaAt (t / kk) (t % kk)
  let Einc := (List.range m).map erasedSym
  let MB := Tinc ++ Jinc ++ betaB ++ Einc
  let _ ← Prog.call (commitCmd 3 (2 * n + kk * m + m) MB)
  -- Step 7 (Alice's table receipt)
  let _ ← Prog.wait
  -- Step 8
  let _ ← Prog.call (checkCmd [3] (P2Pred.proj (List.range n)).enc Tinc)
  let _ ← Prog.call (checkCmd [1] (P2Pred.proj (tritPos TA)).enc (proj (tritPos TA) (encTrits U)))
  let Brec := (List.range L).flatMap fun a => List.ofFn (Bcol a)
  let _ ← Prog.call (checkCmd [2] (P2Pred.proj (colPos TA)).enc (proj (colPos TA) Brec))
  -- Step 9
  let tst ← Prog.recv
  Prog.check (tst = [true])
  let audIdx := (List.range n).filter fun t => Tinc.getD t false
  let audVals ← waitCert [4] (P2Pred.proj (entryPos audIdx)).enc
  -- Step 10
  let audEntries := (List.range audIdx.length).map fun t => decEntry ((audVals.drop (6 * t)).take 6)
  Prog.check (decide (audVals.length = 6 * audIdx.length ∧ ∀ e ∈ audEntries, e.isSome))
  let audLoss := ((List.range audIdx.length).filter fun t =>
    let a := π.getD (audIdx.getD t 0) 0
    match audEntries.getD t none with
    | some e => e.C && (e.A (Yat a) != Bcol a e.X)
    | none => false).length
  let aud := decide ((Einc.filter id).length ≤ eraseCap m ∧
    (audLoss : ℝ) ≤ kappaAud N₀ ηMS * kk * m)
  Prog.send [aud]
  Prog.check aud
  let ESpos := (List.range n).map (· + n) ++ (List.range m).map (· + (2 * n + kk * m))
  let _ ← Prog.call (checkCmd [3] (P2Pred.proj ESpos).enc (proj ESpos MB))
  -- Step 11
  let sel ← Prog.recv
  Prog.check (sel = [true])
  -- Step 12
  let σ ← sampleVec (sampleF64Star m) m
  let cR ← sampleVec sampleF64 (C.dimB m 1)
  let R : Fin m → F64 := fun i => σ i * C.paramB m 1 (fun _ => bitF d) cR i
  let beta := labelVec m betaB
  let Mv : Fin m → F64 := fun i => beta i + R i
  Prog.send (pack [encVec σ, encVec Mv])
  let _ ← Prog.call (checkCmd [1, 3] P2Pred.label.enc
    (pack [encTrits V, incidence L TA, pack (π.map encNat), encVec σ, encVec Mv]))
  -- Step 13 (payload, projections of (X, C) on the selectors, PAY)
  let payload ← Prog.recv
  let xc := xcPos (selIdx N₀ m Jinc)
  let xcVals ← waitCert [4] (P2Pred.proj xc).enc
  let _ ← waitCert [4] P2Pred.pay.enc
  -- Step 14
  let s : SelData := { m := m, N₀ := N₀, π := π, T := Tinc, J := Jinc, beta := betaB, E := Einc, U := fun _ => none, V := fun _ => 0, σ := σ, M := Mv }
  let selList := selIdx N₀ m Jinc
  let xcAt : ℕ → Option (Fin 3 × Bool) := fun idx =>
    match selList.idxOf? idx with
    | some t => (decTrit (xcVals.getD (3 * t) false) (xcVals.getD (3 * t + 1) false)).map
        fun x => (x, xcVals.getD (3 * t + 2) false)
    | none => none
  Prog.check (decide (xcVals.length = 3 * selList.length ∧ ∀ idx ∈ selList, (xcAt idx).isSome))
  let pay := readPayload s payload
  let Hhat : Fin m → F64 := fun i =>
    if s.erased i then 0 else ∑ j : Fin 6,
      let b := betaAt i j
      match unpack (pay i j b) with
      | [Smat, Fb] =>
        let Zhat : Bits := (s.Jset i j).map fun t =>
          let idx := blockIdx N₀ i j t
          match xcAt idx with
          | some (x, c) => c && Bcol (π.getD idx 0) x
          | none => false
        decVec 1 Fb 0 + matApply Smat Zhat
      | _ => 0
  let Eset : Finset (Fin m) := by classical exact Finset.univ.filter fun i => s.erased i
  let out : Bool := by
    classical
    exact match C.decodeA m 1 σ Eset (TOf m) Hhat with
    | some H => if secAσ C m 1 σ H 0 = 1 then true else false
    | none => false
  Prog.send [true]
  pure [out]

/-- **Protocol 2** in the commit-and-prove hybrid: one batch (`0`) of `L` coordinates, Alice
answering rows, one budget group. -/
noncomputable def protocol2 (C : CodeFamily) (N₀ : ℕ) (ηMS : ℝ) (ell : ℕ → ℕ) : Protocol where
  codeA := fun lam x => (protocol2A C N₀ ηMS ell lam x).run
  codeB := fun lam x => (protocol2B C N₀ ηMS ell lam x).run
  nb := fun _ => 1
  ng := fun _ => 1
  group := fun _ _ => 0
  coords := fun lam _ => LOf N₀ (mOT lam (ell lam))
  rowsA := fun _ _ => true
  steps := fun lam => 2 ^ (LOf N₀ (mOT lam (ell lam)) + lam)

/-- The commit-and-prove functionality of Protocol 2: predicate language `L2` at the length
`m(λ, ℓ(λ))` and Protocol 2's own schedule. -/
noncomputable def cp2 (C : CodeFamily) (N₀ : ℕ) (ell : ℕ → ℕ) : Func :=
  idealCP (fun lam => L2 C N₀ (mOT lam (ell lam))) sched2

end DIObliviousTransfer


