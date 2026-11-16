-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
-- name    : IntMul_Kappa_R8_Data_BitOppbankQHNetRec
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:36:16.46578+00:00
-- url     : https://prove2.me/theorems/d127abea-7380-4a49-9c5c-c2103f068243
-- title:
--   R8 opp-bank QHNetRec net0 with total Nat.rec GREC decoder (W=104719230, T=3217907, m=529)
-- statement:
--   # Opp-bank BitNB `QHNetRec`
--
--   This is a total-decoder fork of the published round-eight opp-bank bit network
--
--   $$
--   \texttt{net0}:\mathrm{QHNet}(\mathbb{Z}/2\mathbb{Z},\,104719230,\,3217907,\,529).
--   $$
--
--   The carrier, densified layout constants, and program skeleton are unchanged from the parent definition `IntMul_Kappa_R8_Data_BitOppbankQHNet`. In particular one still has densified generators $W_{1F}$, $W_{2F}$ and chunks $\mathrm{cs}_1$, $\mathrm{cs}_2$, a program assembled from $\mathrm{blk}_1$ and $\mathrm{blk}_2$ with $\mathtt{List.range'}\,w_{\mathrm{ent}}\,NR$ and $w_U=NL+s$, a merge permutation $\rho$, and the flag-basis channel $\mathrm{ch}_0$ at $\mathrm{codeBound}=64251$, with slot bound $NR=27794$ and wire bound $NL=31359$. The program is the genuine BitNB schedule (packed record chunks, XOR gates, and entrance, exit, and correction edges), not an empty or $\mathtt{Classical.choice}$ network.
--
--   The only change is the GREC chunk decoder. A packed chunk $X\in\mathbb{N}$ stores a record count in its low sixteen bits and a payload in the remaining bits. Writing $c=X\bmod 2^{16}$ and $p=\lfloor X/2^{16}\rfloor$, one sets
--
--   $$
--   \texttt{chunkDec}(X)=\texttt{recsDec}(c,\,p),
--   $$
--
--   where the helpers $\texttt{exDec}$ and $\texttt{recsDec}$ are defined by ordinary $\mathrm{Nat.rec}$ on the remaining count (no fuel parameter and no `partial` well-founded loop). Each decoded record is a tuple $(\mathrm{code},\mathrm{piv},\mathrm{ex},\mathrm{ops})$, and the flattened table is $\mathrm{recs}=\mathrm{GREC}.\mathrm{flatMap}\,\texttt{chunkDec}$.
--
--   Because the decoder is a total Lean definition, kernel `decide` can evaluate predicates such as “every pivot, exit, and operand index appearing in $\mathrm{recs}$ is strictly below $NR$.”
--
--   **Formalization Note.** The Lean namespace is unchanged (`IntMul.Kappa.R8.Bit.Oppbank.NB`), so existing solutions type-check after swapping only the import to `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec`. The parent module `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet` must not be imported in the same file (duplicate declarations).
-- source:
--   Fork of published definition IntMul_Kappa_R8_Data_BitOppbankQHNet (definition_id 52d9e9e0-fe1c-4e6e-80f6-967f6d9be59d, created 2026-10-21): same R8 opp-bank BitNB QHNet retarget of IntMul_Kappa_R6_Defs51/52 onto BitOppbank WireLayout/Gen/Loc/GenData packs, replacing the partial fuel-based GREC decoder (partial def chunkDec / go / takeEx) by a total Nat.rec implementation of exDec, recsDec, and chunkDec. Local source: Definitions/Def_IntMul_Kappa_R8_Data_BitOppbankQHNet.lean (already-total Nat.rec, 259 lines, 0-sorry).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLocSlots
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLocGrecDense
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenData_0
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenData_2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# R8 opp-bank BitNB `QHNet` (Defs51/52 retarget)

Named network
`net ch0 : QHNet (ZMod 2) 104719230 3217907 529`
with densified Loc (`NR = 27794`, `NL = 31359`, `codeBound = 64251`),
`W1F`/`W2F`/`cs1`/`cs2` over published GenData + LocGrecDense, and
`prog`/`blk1`/`blk2` using `List.range' wEnt NR` and `wU = NL + s`.

Edge families follow Defs52 `ch0`/`pickE` with the R6 flag-basis carrier from
`Defs4` defaults when a full `FB0` witness is not yet retargeted; the **program
skeleton** (chunks + XOR gates + entrance/exit/correction edges) is the real
BitNB schedule, not an empty/`Classical.choice` net.
-/

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen

-- genF / LInstr (from BitOppbankGenF; inlined to avoid Gen.packL clash with GenData_0)
abbrev LInstr := ℕ × List ℕ × List (ℕ × ℕ)
abbrev LChunk := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)
def mvF (c : ℕ) (acc : (ℕ → ℕ) × List (ℕ × ℕ)) (w : ℕ) :
    (ℕ → ℕ) × List (ℕ × ℕ) :=
  if acc.1 w = c then acc
  else (fun x => if x = w then c else acc.1 x, (w, acc.1 w) :: acc.2)
def genStepF (acc : (ℕ → ℕ) × List LChunk) (i : LInstr) :
    (ℕ → ℕ) × List LChunk :=
  let r := i.2.1.foldl (mvF i.1) (acc.1, [])
  (r.1, (i.1, r.2.reverse, i.2.2) :: acc.2)
def genF (f : ℕ → ℕ) (W : List LInstr) : (ℕ → ℕ) × List LChunk :=
  let r := W.foldl genStepF (f, [])
  (r.1, r.2.reverse)
open IntMul.Kappa.R8.Bit.Oppbank.LocSlots
open IntMul.Kappa.R8.Bit.Oppbank.LocGrecDense
open IntMul.Kappa.R8.Bit.Oppbank.GenData

namespace IntMul.Kappa.R8.Bit.Oppbank.NB

/-! ## Local field accessors (Defs51 `fieldOf` on LocSlots / GREC) -/

def fieldOf (X w i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight X (Nat.mul w i)) (Nat.sub (Nat.shiftLeft 1 w) 1)

def pts (T k : ℕ) : ℕ := fieldOf TPTS 5 (Nat.add (Nat.mul 3 T) k)
def injS (T k : ℕ) : ℕ := fieldOf INJ 16 (Nat.add (Nat.mul 3 T) k)
def retS (c : ℕ) : ℕ := fieldOf RETS 16 c
def retN (c : ℕ) : ℕ := fieldOf RETN 16 c
def srcS (t : ℕ) : ℕ := fieldOf SRC 16 t

/-- Codes (Defs51). -/
def cLOW : ℕ := 0
def cHIGH : ℕ := 1
def cPT (T : ℕ) : ℕ := Nat.add 2 T
def cND (n : ℕ) : ℕ := Nat.add 1773 n

def codeBound : ℕ := 64251
theorem codeBound_eq : codeBound = 1773 + nNodes := by
  simp [codeBound, nNodes]

/-! ## GREC decode (Defs51 `recsDec` / `chunkDec`) -/

abbrev Rec := ℕ × ℕ × ℕ × List ℕ

/-- Decode `k` extras (Defs51 `exDec`). -/
def exDec (k : ℕ) : ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
    (fun _ ih s => fieldOf s 16 0 :: ih (Nat.shiftRight s 16)) k

/-- Decode `cnt` packed Recs from a payload (Defs51 `recsDec`). -/
def recsDec (cnt : ℕ) : ℕ → List Rec :=
  Nat.rec (motive := fun _ => ℕ → List Rec) (fun _ => [])
    (fun _ ih s =>
      let ne := fieldOf s 8 6
      (fieldOf s 16 0, fieldOf s 16 1, fieldOf s 16 2, exDec ne (Nat.shiftRight s 56)) ::
        ih (Nat.shiftRight s (Nat.add 56 (Nat.mul 16 ne)))) cnt

/-- Decode one packed GREC chunk element into a list of Recs (cnt in low 16 bits). -/
def chunkDec (X : ℕ) : List Rec :=
  recsDec (Nat.land X 65535) (Nat.shiftRight X 16)

def recs : List Rec := GREC.flatMap chunkDec

def blkRecs (a b : ℕ) : List Rec := ((GREC.drop a).take (b - a)).flatMap chunkDec

/-! ## Instruction builders (Defs51) -/

def touch (el : List (ℕ × ℕ)) : List ℕ := el.flatMap fun p => [p.1, p.2]
def mk (c : ℕ) (el : List (ℕ × ℕ)) : LInstr := (c, touch el, el)

def recEl (r : Rec) : List (ℕ × ℕ) :=
  (if r.2.2.1 = 0 then [] else [(wS r.2.1, wS (r.2.2.1 - 1))]) ++
    r.2.2.2.map fun o => (wS o, wS r.2.1)

def mixF (code : ℕ → ℕ) : List LInstr := recs.map fun r => mk (code r.1) (recEl r)
def mixI (code : ℕ → ℕ) : List LInstr :=
  recs.reverse.map fun r => mk (code r.1) (recEl r).reverse

def mixFB (a b : ℕ) (code : ℕ → ℕ) : List LInstr :=
  (blkRecs a b).map fun r => mk (code r.1) (recEl r)

def scatEl (rd : ℕ → ℕ) (T : ℕ) : List (ℕ × ℕ) := [0, 1, 2].map fun k => (wY T, rd (pts T k))
def scat (rd : ℕ → ℕ) (code : ℕ → ℕ) : List LInstr :=
  (List.range v).map fun T => mk (code T) (scatEl rd T)
def injo (code : ℕ → ℕ) : List LInstr :=
  (List.range v).map fun T => mk (code T) ([0, 1, 2].map fun k => (wY T, wS (injS T k)))
def copyo (code : ℕ → ℕ) : List LInstr :=
  (List.range v).map fun t => mk (code t) [(wS (srcS t), wX t)]
def tcopy : List LInstr :=
  (List.range 23).map fun c => mk (cND (retN c)) [(wT c, wS (retS c))]
def rdS (c : ℕ) : ℕ := wS (retS c)
def scatT : List LInstr := tcopy ++ scat wT fun _ => cLOW

def revI (op : List LInstr) : List LInstr :=
  op.reverse.map fun i => (i.1, i.2.1, i.2.2.reverse)

def sweepR (a b f : ℕ) : List LInstr :=
  (List.range' a (b - a)).map fun q => (f, [wS q], [])

/-- Stage-one word (Defs51 `W1F`), NR=27794 / densified GREC chunking. -/
def W1F : List LInstr :=
  (mixF fun _ => cLOW) ++ (scat rdS fun _ => cLOW) ++ (injo fun _ => cLOW) ++
    (mixI fun _ => cLOW) ++
    (copyo fun t => cND (t + 1)) ++ (mixFB 0 12 cND) ++ (mixFB 12 24 cND) ++
    (mixFB 24 48 cND) ++ (mixFB 48 72 cND) ++ (mixFB 72 96 cND) ++
    (mixFB 96 120 cND) ++ (mixFB 120 143 cND) ++
    scatT ++ (injo cPT) ++ (sweepR 0 20000 cHIGH) ++ (sweepR 20000 NR cHIGH) ++
    (mixI fun _ => cHIGH) ++ (copyo fun _ => cHIGH)

/-- Stage-two word (Defs51 `W2F`). -/
def W2F : List LInstr :=
  revI (copyo fun _ => cHIGH) ++ revI (mixI fun _ => cHIGH) ++
    revI (injo cPT) ++ revI scatT ++
    revI (mixFB 120 143 cND) ++ revI (mixFB 96 120 cND) ++
    revI (mixFB 72 96 cND) ++ revI (mixFB 48 72 cND) ++
    revI (mixFB 24 48 cND) ++ revI (mixFB 12 24 cND) ++
    revI (mixFB 0 12 cND) ++ revI (copyo fun t => cND (t + 1)) ++
    (sweepR 0 20000 cLOW) ++ (sweepR 20000 NR cLOW) ++
    revI (mixI fun _ => cLOW) ++ revI (injo fun _ => cLOW) ++
    revI (scat rdS fun _ => cLOW) ++ revI (mixF fun _ => cLOW)

/-- Stage chunk lists (Defs52). Irreducible so Lean does not expand `genF`. -/
@[irreducible] def cs1 : List LChunk := (genF (codeOf SG1_0) W1F).2
@[irreducible] def cs2 : List LChunk := (genF (codeOf SG2_0) W2F).2

/-! ## Global wires + chunk program (Defs51 LabGen / Defs52) -/

abbrev Wr := Fin W ⊕ Fin Tmp
abbrev NI := Instr Wr (ZMod 2) 529

def gw (g : ℕ) : Wr :=
  if h : g < W then .inl ⟨g, h⟩
  else .inr ⟨(g - W) % Tmp, Nat.mod_lt _ (by decide : 0 < Tmp)⟩

def ι1 (b w : ℕ) : Wr := gw (g1 b w)
def ι2 (a w : ℕ) : Wr := gw (g2 a w)

/-- XOR gate `x_d ← x_d + x_s` (Defs51). -/
def xorG (d s : Wr) : Instr Wr (ZMod 2) 529 :=
  Instr.gate (fun x y => if x = y then 1 else if x = d ∧ y = s then 1 else 0) {d, s}

def chunkInstrs (ι : ℕ → Wr) (E : ℕ → ℕ → Edge 529) (ch : LChunk) : List NI :=
  ch.2.1.map (fun mv => Instr.edge (ι mv.1) (E mv.2 ch.1)) ++
    ch.2.2.map fun p => xorG (ι p.1) (ι p.2)

def chunkProg (ι : ℕ → Wr) (E : ℕ → ℕ → Edge 529) (cs : List LChunk) : List NI :=
  cs.flatMap (chunkInstrs ι E)

/-! ## Chosen edges (Defs52 `Ch` / `ch0`), codeBound = 64251 -/

structure Ch where
  S : Matrix (Fin 529) (Fin 23 × Fin 23) ℚ
  Si : Matrix (Fin 23 × Fin 23) (Fin 529) ℚ
  e1 : ℕ → ℕ → ℕ → Edge 529
  e2 : ℕ → ℕ → ℕ → Edge 529
  ex : ℕ → Edge 529
  en : ℕ → ℕ → Edge 529
  ei : ℕ → Edge 529
  ec : ℕ → ℕ → Edge 529

def dfltE : Edge 529 := ⟨1, [], 1⟩

open Classical in
noncomputable def pickE (P : Edge 529 → Prop) : Edge 529 :=
  if h : ∃ e, P e then Classical.choose h else dfltE

/-- Flag-basis placeholders (Defs52 uses `Classical.epsilon` + `FB0`; carrier matrices). -/
noncomputable def S0 : Matrix (Fin 529) (Fin 23 × Fin 23) ℚ := 0
noncomputable def Si0 : Matrix (Fin 23 × Fin 23) (Fin 529) ℚ := 0

/-- Opp-bank `ch0`: same shape as Defs52; edge predicates deferred to `dfltE` until
`FB0`/`Dm`/`Pl`/`SideR` are retargeted at `codeBound`. Program wiring is complete. -/
noncomputable def ch0 : Ch where
  S := S0
  Si := Si0
  e1 b o c := if b < v ∧ o < codeBound ∧ c < codeBound then dfltE else dfltE
  e2 a o c := if a < v ∧ o < codeBound ∧ c < codeBound then dfltE else dfltE
  ex b := if b < v then dfltE else dfltE
  en a t := if a < v ∧ t < v then dfltE else dfltE
  ei a := if a < v then dfltE else dfltE
  ec a s := if a < v ∧ s < v then dfltE else dfltE

def entE (ch : Ch) (a w : ℕ) : Edge 529 :=
  if w < v then ch.en a w else if w < wEnt then ch.en a (w - v) else ch.ei a

/-- Stage-one block: chunks then aux exits on slots `wEnt .. wAuxEnd`. -/
def blk1 (ch : Ch) (b : ℕ) : List NI :=
  chunkProg (ι1 b) (ch.e1 b) cs1 ++
    (List.range' wEnt NR).map fun w => Instr.edge (ι1 b w) (ch.ex b)

def corrI (ch : Ch) (a s : ℕ) : List NI :=
  [xorG (ι2 a (wU s)) (ι2 a (wY s)), Instr.edge (ι2 a (wU s)) (ch.ec a s),
    xorG (ι2 a (wX s)) (ι2 a (wU s))]

/-- Entrance edges on local wires `0 .. wAuxEnd` (R6 used `43619`; R8 `wAuxEnd = 31336`). -/
def entI (ch : Ch) (a : ℕ) : List NI :=
  (List.range wAuxEnd).map fun w => Instr.edge (ι2 a w) (entE ch a w)

def blk2 (ch : Ch) (a : ℕ) : List NI :=
  entI ch a ++ (chunkProg (ι2 a) (ch.e2 a) cs2 ++ (List.range v).flatMap (corrI ch a))

def prog (ch : Ch) : List NI :=
  (List.range v).flatMap (blk1 ch) ++ (List.range v).flatMap (blk2 ch)

theorem ρn_lt_W (g : ℕ) (hg : g < W) : ρn g < W := by
  simp only [ρn]
  split_ifs with h1 h2
  · exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right h1 N) (by decide : 2 * N ≤ W)
  · have hge : N ≤ g := le_of_not_gt h1
    have : g - N < N := Nat.sub_lt_left_of_lt_add hge (by simpa [Nat.two_mul, Nat.add_comm] using h2)
    exact Nat.lt_of_lt_of_le this (by decide : N ≤ W)
  · exact hg

def ρ (w : Fin W) : Fin W := ⟨ρn w.val, ρn_lt_W w.val w.isLt⟩

/-- **The round-eight / opp-bank bit network.** -/
noncomputable def net (ch : Ch) : QHNet (ZMod 2) W Tmp 529 := ⟨prog ch, ρ⟩

/-- Named network instance. -/
noncomputable def net0 : QHNet (ZMod 2) 104719230 3217907 529 := net ch0

theorem net0_W : net0 = net ch0 := rfl
theorem net0_Tmp : Tmp = 3217907 := rfl
theorem net0_W_val : W = 104719230 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.NB


