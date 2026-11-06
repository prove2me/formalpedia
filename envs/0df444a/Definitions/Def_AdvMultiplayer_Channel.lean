-- Prove2me | Definitions.Def_AdvMultiplayer_Channel
-- name    : AdvMultiplayer_Channel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:03.821337+00:00
-- url     : https://prove2.me/theorems/7815575f-6347-4844-9e1e-c33e84878390
-- title:
--   The parity channel, records and parsing
-- statement:
--   A message is a word $u\in\mathbb F_2^B$. A round supplies $H_t(u)=c_t\cdot u\oplus b_t$. To send $u$, the sender plays the receiver's arm if $H_t(u)=0$ and its own arm otherwise, so a positive receiver observation gives the equation $c_t\cdot u=1\oplus b_t$. The decoder appends such equations to a batch and, at $Q_{\mathrm{dec}}$ equations, solves the system by Gaussian elimination and clears the batch; the output is the unique solution, or $\bot$.
--
--   DOWN records $(\sigma,a,e,h,q)$ and UP records $(\sigma,S,\delta,q)$ are encoded in five $L$-bit blocks by (34). Parsing returns a record exactly when the word encodes an element of the admissible sets $\mathcal M^{\mathrm{DOWN}}$, $\mathcal M^{\mathrm{UP}}$.
--
--   **Formalization Note.** Field $j$ occupies bits $jL,\dots,jL+L-1$, least significant first. Gaussian elimination is a ticked program. The analysis's notion of solutions is the separate set `solutions`.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Section 4.1, Algorithm 2, p.21; Section 5.2, (21), (33), (34), pp.22, 31-32

import Mathlib
import Definitions.Def_AdvMultiplayer_Size
import Definitions.Def_LNTopology_Hermetization_tick

open LNTopology.Hermetization

namespace AdvMultiplayer

variable (p : Size)

/-- A word of `F₂^B` (p.21). -/
abbrev Word := Fin p.Bmsg → Bool

/-- The binary dot product `c · u` (p.21). -/
def dotW {n : ℕ} (c u : Fin n → Bool) : Bool :=
  (List.finRange n).foldl (fun acc k => xor acc (c k && u k)) false

/-- `H_t(u) = c_t · u ⊕ b_t` (p.21). -/
def hVal (c : Word p) (b : Bool) (u : Word p) : Bool := xor (dotW c u) b

/-- `H_t(u)` as a program: `O(B)` operations (Section 8, p.49). -/
def hProg (c : Word p) (b : Bool) (u : Word p) : StateM ℕ Bool := do
  tick p.Bmsg
  pure (hVal p c b u)

/-- `SendArm(u, R_send, R_receive)` of Algorithm 2, p.21: `R_receive` if `H_t(u) = 0`, else
`R_send`. -/
def sendArm (c : Word p) (b : Bool) (u : Word p) (rSend rRecv : ℕ) : StateM ℕ ℕ := do
  let v ← hProg p c b u
  pure (if v then rSend else rRecv)

/-- One equation `c · u = 1 ⊕ b` of a batch, with the round of its positive test. -/
structure Eqn where
  /-- The coefficients `c_t`. -/
  c : Word p
  /-- The constant `b_t`. -/
  b : Bool
  /-- The positive-test round. -/
  rnd : ℕ

/-- An equation batch `W` (Algorithm 2). -/
abbrev Batch := List (Eqn p)

/-- The solutions of a batch over `F₂^B`. -/
def solutions (W : Batch p) : Set (Word p) := {u | ∀ e ∈ W, dotW e.c u = !e.b}

/-- Add row `e` into row `f` over `F₂`. -/
def xorRow (f e : Word p × Bool) : Word p × Bool :=
  (fun k => xor (f.1 k) (e.1 k), xor f.2 e.2)

/-- **Gaussian elimination over `F₂`.** Gan, arXiv:2610.05688, Algorithm 2 line 6 and App. A.2, p.55:
the unique solution of the system `{c·u = rhs}`, or `none` when there is no solution or more than one.
Gauss–Jordan elimination, charging `O(B)` per row operation, so `O(QB²)` in all. -/
def gaussProg (W : List (Word p × Bool)) : StateM ℕ (Option (Word p)) := do
  let mut rows := W
  let mut piv : List (Fin p.Bmsg × (Word p × Bool)) := []
  let mut full := true
  for k in List.finRange p.Bmsg do
    tick (1 + rows.length)
    match rows.findIdx? (fun e => e.1 k) with
    | none => full := false
    | some idx =>
      match rows[idx]? with
      | none => full := false
      | some e =>
        tick ((rows.length + piv.length) * p.Bmsg)
        rows := (rows.eraseIdx idx).map fun f => if f.1 k then xorRow p f e else f
        piv := piv.map (fun f => (f.1, if f.2.1 k then xorRow p f.2 e else f.2)) ++ [(k, e)]
  tick (1 + rows.length + piv.length)
  if full && rows.all (fun f => !f.2) then
    pure (some fun k => match piv.find? (fun f => f.1 == k) with
      | some f => f.2.2
      | none => false)
  else pure none

/-- `DecodeStep(W, Y)` of Algorithm 2, p.21: on `Y > 0` append `c_t·u = 1 ⊕ b_t`; on a full batch
of `Q_dec` equations solve it and clear it. Returns the new batch and, at a decision, the completed
batch with the unique solution or `none` (the paper's `⊥`). -/
noncomputable def decodeStep (W : Batch p) (c : Word p) (b : Bool) (t : ℕ) (pos : Bool) :
    StateM ℕ (Batch p × Option (Batch p × Option (Word p))) := do
  let W' := if pos then W ++ [⟨c, b, t⟩] else W
  tick (1 + W'.length)
  if W'.length < p.Qdec then
    pure (W', none)
  else
    let sol ← gaussProg p (W'.map fun e => (e.c, !e.b))
    pure ([], some (W', sol))

/-- A DOWN record `(σ, a, e, h, q)` (21), p.22. -/
structure DownRec where
  σ : ℕ
  a : ℕ
  e : ℕ
  h : ℕ
  q : ℕ

/-- An UP record `(σ, S, δ, q)` (33), p.31. -/
structure UpRec where
  σ : ℕ
  S : ℕ
  δ : ℕ
  q : ℕ

/-- Concatenation of five `L`-bit blocks (`bin_L` least significant bit first): bit `k` of the word
is bit `k mod L` of block `k / L`. -/
def encFields (f : ℕ → ℕ) : Word p := fun k => (f (k.val / p.Lfield)).testBit (k.val % p.Lfield)

/-- `Enc^DOWN` (34), p.32. -/
def encDown (M : DownRec) : Word p :=
  encFields p fun j => match j with
    | 0 => M.σ
    | 1 => M.a
    | 2 => M.e
    | 3 => M.h
    | _ => M.q

/-- `Enc^UP` (34), p.32: the fifth block is `0^L`. -/
def encUp (M : UpRec) : Word p :=
  encFields p fun j => match j with
    | 0 => M.σ
    | 1 => M.S
    | 2 => M.δ
    | 3 => M.q
    | _ => 0

/-- Block `j` of a word, read as a natural number. -/
def fieldOf (w : Word p) (j : ℕ) : ℕ :=
  (List.range p.Lfield).foldl
    (fun acc k => if h : j * p.Lfield + k < p.Bmsg then
      (if w ⟨j * p.Lfield + k, h⟩ then acc + 2 ^ k else acc) else acc) 0

/-- The admissible DOWN records `𝓜^DOWN` (p.32). -/
def AdmDown (M : DownRec) : Prop :=
  M.σ ∈ Finset.Icc 1 p.T ∧ M.a ∈ Finset.Icc 1 p.K ∧ M.e ∈ Finset.Icc 1 p.K ∧ M.a ≠ M.e ∧
    M.h ≤ p.bN ∧ p.betaOf p.eta ≤ ((1 : ℝ) / 2) ^ M.h ∧
    ((1 : ℝ) / 2) ^ M.h ≤ 1 / (16 * (p.m : ℝ) * (p.K : ℝ)) ∧ M.q ≤ p.T * p.D

/-- The admissible UP records `𝓜^UP` (p.32). -/
def AdmUp (M : UpRec) : Prop :=
  (M.σ = 0 ∧ M.S = 0 ∧ M.δ = 0 ∧ M.q = 0) ∨
    (M.σ ∈ Finset.Icc 1 p.T ∧ M.S ≤ p.T * p.D ∧ M.δ ≤ p.D ∧ M.q ≤ p.T * p.D)

/-- `Parse^DOWN` (p.32), as a function: `Enc⁻¹(w)` if `w` encodes an admissible record. -/
noncomputable def parseDown (w : Word p) : Option DownRec := by
  classical exact
    let M : DownRec := ⟨fieldOf p w 0, fieldOf p w 1, fieldOf p w 2, fieldOf p w 3, fieldOf p w 4⟩
    if AdmDown p M then some M else none

/-- `Parse^UP` (p.32). -/
noncomputable def parseUp (w : Word p) : Option UpRec := by
  classical exact
    let M : UpRec := ⟨fieldOf p w 0, fieldOf p w 1, fieldOf p w 2, fieldOf p w 3⟩
    if AdmUp p M ∧ fieldOf p w 4 = 0 then some M else none

end AdvMultiplayer


