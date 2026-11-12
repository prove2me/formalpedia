-- Prove2me | Definitions.Def_DIObliviousTransfer_SelData
-- name    : DIObliviousTransfer_SelData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:08:06.959618+00:00
-- url     : https://prove2.me/theorems/f67e7151-9bc7-4253-b79f-ecad7ddfeeb6
-- title:
--   Shared machinery of the transfer and source protocols
-- statement:
--   The protocols use the following common machinery.
--   - **Samplers** (p.27): field elements from six fair bits; nonzero elements by at most $m$ rejections, then $1$; uniform elements of $[0,N)$ by rejection capped at $\lambda$ trials with fallback $0$; trits, orderings (Fisher–Yates) and size-$t$ sets.
--   - **Encodings:** trits as two bits, rows and columns as three bits, field elements as six basis coordinates, sets as incidence strings.
--   - **Microblock geometry:** block $i\cdot k+j$ of $N_0$ consecutive data positions in the order $\pi$.
--   - **Predicate cores:** the selector syntax and label conditions shared by $P_{\mathrm{LABEL}}$ and MODE; the payload values $p^b_{i,j}=F^b_{i,j}+S^b_{i,j}Z^b_{i,j}$ recomputed from the stored table, with the extension systems into $D$ and $A^\sigma$ shared by $P_{\mathrm{PAY}}$ and (23); and the honest payload construction (Protocol 2 Step 13, (22)).
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), p.27; §3.3, pp.28–30; Protocol 2, pp.30–31; (22)–(23), pp.47–48

import Mathlib
import Definitions.Def_DIObliviousTransfer_Ltotal
import Definitions.Def_DIObliviousTransfer_Protocol
import Definitions.Def_DIObliviousTransfer_MS

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), §3.2 (p.27, the
bounded samplers), §3.3 (pp.28–30: records, Definitions 12–13), §3.4 (Protocol 2, pp.30–31),
§5.2–5.3 (Definition 14, Protocol 7, (22)–(23), pp.46–48): the shared machinery of the transfer
and source protocols.

**Formalization Note** (decisions D15, D20, and encodings). Honest controllers are written in
`Prog = OptionT Code`, where `failure` is the global abort (honest output `⊥`). Samplers (p.27):
a field element from six fair bits; a nonzero field element by at most `m` rejections of zero,
then the fixed fallback `1`; a uniform element of `[0, N)` by rejection on `⌈log₂ N⌉` fair bits,
capped at `λ` trials with fallback `0`; uniform trits, uniform orderings (Fisher–Yates) and
uniform size-`t` sets (the first `t` entries of a uniform ordering) from that sampler. Records use
fixed canonical encodings: a trit as two bits (`00, 01, 10`; `11` rejected), a row or column as its
three bits, a field element as its six basis coordinates, a set as an incidence string. The data
positions are the complement of the test set in the order `π`; microblock `(i, j)` is the block
number `i·k + j` of `N₀` consecutive data positions; audit and selector masks are incidence
strings over data positions in that order, labels are indexed by `i·k + j`.
-/

open Code

namespace Prog

/-- A fair coin. -/
def coin : Prog Bool := OptionT.lift (Code.coin Code.ret)
/-- Send a message to the other party. -/
def send (m : Bits) : Prog Unit := OptionT.lift (Code.send m (Code.ret ()))
/-- Receive a message from the other party. -/
def recv : Prog Bits := OptionT.lift (Code.recv Code.ret)
/-- Use the party's share of device batch `b` with questions `qs`; returns the answers. -/
def dev (b : ℕ) (qs : Bits) : Prog Bits := OptionT.lift (Code.dev b qs Code.ret)
/-- An ideal call; `⊥` is a global abort. -/
def call (x : Bits) : Prog Bits := OptionT.mk (Code.call x Code.ret)
/-- Wait for a delivery of the ideal functionality; `⊥` is a global abort. -/
def wait : Prog Bits := OptionT.mk (Code.fwait Code.ret)
/-- Abort unless `b`. -/
def check (b : Bool) : Prog Unit := if b then pure () else failure
/-- `n` fair bits. -/
def bits : ℕ → Prog Bits
  | 0 => pure []
  | n + 1 => do let b ← coin; let r ← bits n; pure (b :: r)

end Prog

/-- A uniform element of `[0, N)`: rejection on `⌈log₂ N⌉` fair bits, at most `tries` trials,
fallback `0`. -/
def sampleBelow (N : ℕ) : ℕ → Prog ℕ
  | 0 => pure 0
  | tries + 1 => do
    let b ← Prog.bits (Nat.clog 2 N)
    let v := bitsNat b
    if v < N then pure v else sampleBelow N tries

/-- A uniform trit (bounded rejection, `λ` trials). -/
def sampleTrit (lam : ℕ) : Prog (Fin 3) := do
  let v ← sampleBelow 3 lam
  pure (if h : v < 3 then ⟨v, h⟩ else 0)

/-- A field element from six fair bits. -/
noncomputable def sampleF64 : Prog F64 := do
  let b ← Prog.bits 6
  pure (f64OfBits fun j => b.getD j false)

/-- A nonzero field element: at most `tries` rejections of zero, then the fallback `1`. -/
noncomputable def sampleF64Star : ℕ → Prog F64
  | 0 => pure 1
  | tries + 1 => do
    let z ← sampleF64
    if z = 0 then sampleF64Star tries else pure z

/-- A vector of independent samples. -/
def sampleVec {α : Type} (s : Prog α) : (n : ℕ) → Prog (Fin n → α)
  | 0 => pure Fin.elim0
  | n + 1 => do
    let a ← s
    let r ← sampleVec s n
    pure (Fin.cons a r)

/-- Fisher–Yates on a list, with `fuel` steps (the list length). -/
def shuffleAux (lam : ℕ) : ℕ → List ℕ → Prog (List ℕ)
  | 0, _ => pure []
  | _, [] => pure []
  | fuel + 1, x :: xs => do
    let i ← sampleBelow (xs.length + 1) lam
    let l := x :: xs
    let rest ← shuffleAux lam fuel (l.eraseIdx i)
    pure (l.getD i x :: rest)

/-- A uniform ordering of a list (Fisher–Yates with the bounded sampler). -/
def shuffle (lam : ℕ) (l : List ℕ) : Prog (List ℕ) := shuffleAux lam l.length l

/-- Encoding of a trit as two bits. -/
def encTrit (t : Fin 3) : Bits := [t.val = 2, t.val = 1]

/-- Decoding of a two-bit trit; `11` is invalid. -/
def decTrit (b0 b1 : Bool) : Option (Fin 3) :=
  match b0, b1 with
  | false, false => some 0
  | false, true => some 1
  | true, false => some 2
  | true, true => none

/-- A string of `L` trits, two bits each. -/
def encTrits {L : ℕ} (v : Fin L → Fin 3) : Bits := (List.ofFn v).flatMap encTrit

/-- Decoding of a trit string of length exactly `2L`, all encodings valid. -/
def decTrits (L : ℕ) (b : Bits) : Option (Fin L → Fin 3) :=
  if b.length = 2 * L ∧ ∀ a : Fin L, (decTrit (b.getD (2 * a) false) (b.getD (2 * a + 1) false)).isSome
  then some fun a => (decTrit (b.getD (2 * a) false) (b.getD (2 * a + 1) false)).getD 0
  else none

/-- The question string of a device batch. -/
def encQuestions {L : ℕ} (v : Fin L → Fin 3) : Bits := encTrits v

/-- Recorded answers: two bits per coordinate (missing bits read `false`). -/
def ansPair (ans : Bits) (a : ℕ) : Bool × Bool := (ans.getD (2 * a) false, ans.getD (2 * a + 1) false)

/-- An incidence string of length `L` of a list of positions. -/
def incidence (L : ℕ) (S : List ℕ) : Bits := (List.range L).map fun a => decide (a ∈ S)

/-- The positions of an incidence string. -/
def support (b : Bits) : List ℕ := (List.range b.length).filter fun a => b.getD a false

/-- Projection `π_S(M)`: the entries of `M` at the positions `S`. -/
def proj (S : List ℕ) (M : Bits) : Bits := S.map fun a => M.getD a false

/-- The data position of microblock `(i, j)`, offset `t` (block `i·k + j` of `N₀` consecutive data
positions of the ordering `π`). -/
def blockPos (π : List ℕ) (N₀ i j t : ℕ) : ℕ := π.getD ((i * kk + j) * N₀ + t) 0

/-- The data-order index of microblock `(i, j)`, offset `t`. -/
def blockIdx (N₀ i j t : ℕ) : ℕ := (i * kk + j) * N₀ + t

/-- `β_i = Σ_j e_j β_{i,j}` from the `km` label bits (index `i·k + j`). -/
noncomputable def labelVec (m : ℕ) (beta : Bits) : Fin m → F64 :=
  fun i => ∑ j : Fin 6, if beta.getD (i * kk + j) false then basisE j else 0

/-- The field element represented by the binary `k × |J|` matrix `S` (row-major bits) applied to
`Z ∈ F₂^{|J|}`. -/
noncomputable def matApply (S Z : Bits) : F64 :=
  ∑ r : Fin 6, if (List.range Z.length).foldl
      (fun acc t => acc ^^ (S.getD (r * Z.length + t) false && Z.getD t false)) false
    then basisE r else 0

/-- `sec_σ(v) = sec(σ^{-1} ∗ v)` for the code `B`. -/
noncomputable def secBσ (C : CodeFamily) (m q : ℕ) (σ v : Fin m → F64) : Fin q → F64 :=
  C.secB m q (fun i => (σ i)⁻¹ * v i)

/-- `sec_σ(v) = sec(σ^{-1} ∗ v)` for the code `A`. -/
noncomputable def secAσ (C : CodeFamily) (m q : ℕ) (σ v : Fin m → F64) : Fin q → F64 :=
  C.secA m q (fun i => (σ i)⁻¹ * v i)

/-- A secret is binary (each coordinate `0` or `1`). -/
def IsBinary {q : ℕ} (u : Fin q → F64) : Prop := ∀ i, u i = 0 ∨ u i = 1

/-- The secret `u ∈ F₂^q ⊆ F₆₄^q` of a bit string. -/
noncomputable def bitsSecret (q : ℕ) (u : Bits) : Fin q → F64 := fun i => if u.getD i false then 1 else 0

/-- The data the label and mode predicates read: the microblock geometry, audits `T`, selectors
`J` (data-order incidence strings), labels `β` (`km` bits), erasures `E` (`m` bits), offsets `U`,
Alice's offsets `V`, the ordering `π`, and `(σ, M)`. -/
structure SelData where
  m : ℕ
  N₀ : ℕ
  π : List ℕ
  T : Bits
  J : Bits
  beta : Bits
  E : Bits
  U : ℕ → Option (Fin 3)
  V : ℕ → Fin 3
  σ : Fin m → F64
  M : Fin m → F64

namespace SelData

variable (s : SelData)

/-- The selector `J_{i,j}` as data-order indices. -/
def Jset (i j : ℕ) : List ℕ := (List.range s.N₀).filter fun t => s.J.getD (blockIdx s.N₀ i j t) false

/-- The audit positions of microblock `(i, j)`. -/
def Tset (i j : ℕ) : List ℕ := (List.range s.N₀).filter fun t => s.T.getD (blockIdx s.N₀ i j t) false

/-- `i ∈ E`. -/
def erased (i : ℕ) : Bool := s.E.getD i false

/-- The selector syntax shared by `P_LABEL` (Definition 12) and MODE (Definition 14): lengths,
`|E| ≤ ⌊m/100⌋`, one audit position per microblock, `J_{i,j} = ∅` on erased symbols and
`J_{i,j} ⊆ I_{i,j} ∖ T_{i,j}`, `N₀/8 ≤ |J_{i,j}| ≤ N₀/2` otherwise, `σ ∈ (F₆₄^*)^m`. -/
def syntaxOK : Prop :=
  s.T.length = kk * s.N₀ * s.m ∧ s.J.length = kk * s.N₀ * s.m ∧ s.beta.length = kk * s.m ∧
  s.E.length = s.m ∧ (support s.E).length ≤ eraseCap s.m ∧
  (∀ i < s.m, ∀ j < kk, (s.Tset i j).length = 1 ∧
    (if s.erased i then s.Jset i j = [] else
      (∀ t ∈ s.Jset i j, t ∉ s.Tset i j) ∧
      (s.N₀ : ℝ) / 8 ≤ (s.Jset i j).length ∧ ((s.Jset i j).length : ℝ) ≤ (s.N₀ : ℝ) / 2)) ∧
  ∀ i, s.σ i ≠ 0

/-- The label consistency `U_a + V_a = β_{i,j}` on the selectors (Definition 12) / the inclusion
`J_{i,j} ⊆ {a : U'_a + V_a = β'_{i,j}}` (21). -/
def labelsOK : Prop :=
  ∀ i < s.m, ∀ j < kk, ∀ t ∈ s.Jset i j,
    ∃ u, s.U (blockPos s.π s.N₀ i j t) = some u ∧
      u + s.V (blockPos s.π s.N₀ i j t) = (if s.beta.getD (i * kk + j) false then 1 else 0)

end SelData

/-- A canonical table entry `(X_a, A_a, C_a)` (6 bits: trit, row, anchor flag). -/
structure Entry where
  X : Fin 3
  A : Fin 3 → Bool
  C : Bool

/-- Encoding of a table entry. -/
def Entry.enc (e : Entry) : Bits := encTrit e.X ++ List.ofFn e.A ++ [e.C]

/-- Decoding of a 6-bit table entry with canonical syntax: valid trit, even row, and
`(X_a, A_a) = (0, 000)` when `C_a = 0`. -/
def decEntry (b : Bits) : Option Entry :=
  match decTrit (b.getD 0 false) (b.getD 1 false) with
  | none => none
  | some x =>
    let A : Fin 3 → Bool := ![b.getD 2 false, b.getD 3 false, b.getD 4 false]
    let C := b.getD 5 false
    if (A 0 ^^ A 1 ^^ A 2) = false ∧ (C = true ∨ (x = 0 ∧ A = ![false, false, false])) then
      some ⟨x, A, C⟩ else none

/-- The table (6 bits per data position, in data order). -/
def tableEntry (MA : Bits) (idx : ℕ) : Option Entry := decEntry ((MA.drop (6 * idx)).take 6)

/-- The payload of one microblock and branch: the binary matrix `S^b_{i,j}` (row-major) and the
ciphertext `F^b_{i,j}`. -/
def encPayload (S : Bits) (F : F64) (encF : F64 → Bits) : Bits := pack [S, encF F]

/-- The payload values `p^b_{i,j} = F^b_{i,j} + K^b_{i,j}`, `K = S Z^b_{i,j}`, `Z^b_{i,j} = (A_a[b])_{a ∈ J_{i,j}}`,
recomputed from the stored table (11), (22)–(23). `pay i j b = pack [S, F]`. -/
noncomputable def payValue (s : SelData) (MA : Bits) (pay : ℕ → ℕ → Bool → Bits) (i j : ℕ) (b : Bool) :
    Option F64 :=
  match unpack (pay i j b) with
  | [S, F] =>
    let Js := s.Jset i j
    let Z : Option Bits := (Js.map fun t => (tableEntry MA (blockIdx s.N₀ i j t)).map fun e =>
      e.A (if b then 1 else 0)).allSome
    match Z with
    | some Z => if S.length = kk * Z.length ∧ F.length = 6 then
        some (decVec 1 F 0 + matApply S Z) else none
    | none => none
  | _ => none

/-- The payload-consistency core of `P_PAY` (Definition 13) and of `OpenVer_str` (23): every
nonerased payload is well formed, `g_i = (p⁰_{i,j} + p¹_{i,j})/e_j` is independent of `j`, and with
`f_i = Σ_j p⁰_{i,j} + M_i g_i` the two extension systems into `D` (secret map `sec`) and `A^σ`
have solutions; returns them. -/
noncomputable def payExtensions (C : CodeFamily) (q : ℕ) (s : SelData) (MA : Bits)
    (pay : ℕ → ℕ → Bool → Bits) : Option ((Fin s.m → F64) × (Fin s.m → F64)) := by
  classical
  exact
  let Eset : Finset (Fin s.m) := Finset.univ.filter fun i => s.erased i
  let ps : ℕ → ℕ → Bool → Option F64 := payValue s MA pay
  if ∀ i : Fin s.m, s.erased i = false → ∀ j < kk, ∀ b, (ps i j b).isSome then
    let p : ℕ → ℕ → Bool → F64 := fun i j b => (ps i j b).getD 0
    let g : Fin s.m → F64 := fun i => if s.erased i then 0 else (p i 0 false + p i 0 true) / basisE 0
    let f : Fin s.m → F64 := fun i => if s.erased i then 0 else
      (∑ j : Fin 6, p i j false) + s.M i * g i
    if ∀ i : Fin s.m, s.erased i = false → ∀ j : Fin 6, (p i j false + p i j true) / basisE j = g i then
      match C.extB s.m q Eset g, C.extA s.m q s.σ Eset f with
      | some gD, some fA => some (gD, fA)
      | _, _ => none
    else none
  else none

/-- The honest payload construction (Protocol 2, Step 13; Protocol 7, Step 10, (22)): shares
`Q_{i,j}` uniform with `Σ_j Q_{i,j} = f_i + M_i g_i`, `p^b_{i,j} = Q_{i,j} + b e_j g_i`, and for each
nonerased microblock and branch a fresh uniform binary matrix `S^b_{i,j}` and
`F^b_{i,j} = p^b_{i,j} + S^b_{i,j} Z^b_{i,j}`. Returns the payload string
`pack [pack [S, F] for i ∉ E, j, b]`. -/
noncomputable def honestPayload (s : SelData) (MA : Bits) (f g : Fin s.m → F64) : Prog Bits := do
  let rows ← (List.finRange s.m).mapM fun (i : Fin s.m) => do
    if s.erased i.val then pure [] else do
      let Q ← sampleVec sampleF64 5
      let total := f i + s.M i * g i
      let Qk : Fin 6 → F64 := fun j => if h : j.val < 5 then Q ⟨j.val, h⟩ else
        total - ∑ t : Fin 5, Q t
      (List.finRange 6).flatMapM fun (j : Fin 6) => [false, true].mapM fun b => do
        let Z : Bits := (s.Jset i.val j.val).map fun t =>
          ((tableEntry MA (blockIdx s.N₀ i.val j.val t)).map fun e => e.A (if b then 1 else 0)).getD false
        let S ← Prog.bits (kk * Z.length)
        let p := Qk j + (if b then basisE j * g i else 0)
        pure (pack [S, encVec (fun _ : Fin 1 => p + matApply S Z)])
  pure (pack rows.flatten)

/-- The payload string read back as `pay i j b` (nonerased symbols in order). -/
def readPayload (s : SelData) (P : Bits) : ℕ → ℕ → Bool → Bits :=
  fun i j b =>
    let idx := ((List.range i).filter fun i' => !s.erased i').length
    (unpack P).getD ((idx * kk + j) * 2 + (if b then 1 else 0)) []

end DIObliviousTransfer


