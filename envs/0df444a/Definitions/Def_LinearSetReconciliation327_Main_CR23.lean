-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CR23
-- name    : LinearSetReconciliation327_Main_CR23
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-21T09:45:14.552841+00:00
-- url     : https://prove2.me/theorems/ab380da3-2d83-4b34-a01a-1f490e6f3aa7
-- title:
--   The CR23 sparse-recovery sketch, its preprocessing table, and the toggle program
-- statement:
--   The concrete CR23 sparse-recovery construction used by Proposition 2.3: the layered bipartite expander parameters $D=1024\log N$, $M=2^{68}t$ and $R=DM(\log N+1)$; the parity-check matrix whose check $(s,y)$ stacks the bitmasked label rows with the count-parity row, and the associated $\mathbb{F}_2$-linear sketch $CR_{N,t}$; the preprocessed table that stores, for every coordinate and seed, the payload word address and the bit mask of that check, together with the rebasing predicate that singles out exactly the address-valued cells; the payload-at-base-$\beta$ memory model; and the toggle program `progUp`, a compiled straight-line prologue followed by a countdown loop that XORs one column of the sketch into the packed payload in place.
-- source:
--   A. (2026), arXiv:2611.11409, \u00a72.3 (Proposition 2.3); M. Cheraghchi and I. Ribeiro, Simple Codes for Sparse Recovery, arXiv:1901.02852, \u00a71.2 and Definition 2, https://arxiv.org/abs/1901.02852

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel

set_option autoImplicit false

noncomputable section

namespace LinearSetReconciliation327.Main

/-- `log N`: the label width in bits, i.e. the number of bitmasked rows of one check.  We use
`clog 2 (N+1)`, so `N < 2^(cr23Lb N)` holds for every `N` and the labels `0 … N-1` fit. -/
def cr23Lb (N : ℕ) : ℕ := Nat.clog 2 (N + 1)
/-- `D = 64·log N` seeds.  CR23 Theorem 5 gives `D = O(log N/ε)`; with `ε = 1/4` this is
`O(log N)` and we take the slack constant `1024` (the probabilistic method needs the constant to
absorb a `log(N/t)` union bound; see the status note). -/
def cr23D (N : ℕ) : ℕ := 1024 * cr23Lb N
/-- `M = 64t` buckets per seed.  CR23 Theorem 5 gives `M = O(K/ε)` with `K = 2t`, `ε = 1/4`,
i.e. `M = O(t)`; `64t` is the concrete choice.  The constant `64` is what makes the *per-layer*
bad-event bound a one-line counting estimate: for `s ≤ 2t` we have `M/((1-ε)s) ≥ 42`, so
`ln(M/((1-ε)s)) > 3 > (1-ε)/ε`, and `#image ≤ (1-ε)s` forces all `s` balls into a chosen `u`-subset,
giving `Pr ≤ C(M,u)·(u/M)^s ≤ exp(-0.26·s)` — no concentration inequality needed.

Note `cr23M 0 = 0`, so `R = 0` for `t = 0`. -/
def cr23M (t : ℕ) : ℕ := 2 ^ 68 * t
/-- Rows of the parity-check matrix: `D·M` checks, each contributing its `log N` bitmasked rows
and its single un-bitmasked count-parity row (CR23 §1.2, "stack the two matrices"). -/
def cr23R (N t : ℕ) : ℕ := (cr23D N * cr23M t) * (cr23Lb N + 1)
/-- Word width: `1024·(log N + 1)`, a `Θ(log N)` width (`WidthOK` with `cW = 4096`) which is also
a multiple of `log N + 1`, so one check's `log N + 1` bits sit in a single word. -/
def cr23Word (N : ℕ) : ℕ := 1024 * (cr23Lb N + 1)
/-- A row triple `((s,y),k)`: seed `s`, bucket `y`, and `k` — either the label bit `k < log N`, or
`k = log N`, which is the un-bitmasked count-parity row of that check. -/
abbrev Cr23Row (N t : ℕ) : Type := (Fin (cr23D N) × Fin (cr23M t)) × Fin (cr23Lb N + 1)
/-- Row triples are `Fin R` in the obvious way, `((s,y),k) ↦ (s·M + y)·(log N + 1) + k`. -/
def cr23RowEquiv (N t : ℕ) : Cr23Row N t ≃ Fin (cr23R N t) :=
  (finProdFinEquiv.prodCongr (Equiv.refl (Fin (cr23Lb N + 1)))).trans finProdFinEquiv
/-- The parity-check bit: row `((s,y),k)` sees coordinate `v` iff `v` is dealt to bucket `y` of
seed `s` (i.e. `C v s = y`) *and* either `k = log N` (the count-parity row) or bit `k` of the
binary label `v` is set.  This is CR23 §1.2: the binary expansion of the column index, multiplied
by the entry of the expander matrix, stacked with the original. -/
def cr23Entry (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (q : Cr23Row N t)
    (v : Fin N) : ZMod 2 :=
  if C v q.1.1 = q.1.2 then
    (if q.2.val = cr23Lb N then 1 else if (v.val / 2 ^ q.2.val) % 2 = 1 then 1 else 0)
  else 0
/-- The parity-check matrix `CR_{N,t}` of CR23. -/
def cr23Matrix (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) :
    Matrix (Fin (cr23R N t)) (Fin N) (ZMod 2) :=
  fun p v => cr23Entry N t C ((cr23RowEquiv N t).symm p) v
/-- The CR sketch: `ZMod 2`-linear because every row is a parity check. -/
def cr23Sketch (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) :
    (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (cr23R N t) → ZMod 2) :=
  (cr23Matrix N t C).mulVecLin
/-- The index of the check `(s,y)`: its rows are `cr23Check·(lb+1) + k`, `k < lb+1`.  (Written
`y + M·s` rather than `s·M + y`: the value is the same, but `% M` and `/ M` are then the two
projections `bucket` and `seed` of the check.) -/
def cr23Check (N t : ℕ) (s : Fin (cr23D N)) (y : Fin (cr23M t)) : ℕ := y.val + cr23M t * s.val
/-- The payload word holding check `(s, C v s)`, i.e. the whole block of `lb+1` rows of that check
(the block never crosses a word boundary because `W` is a multiple of `lb+1`). -/
def cr23Addr (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (s : Fin (cr23D N))
    (v : Fin N) : ℕ := cr23Check N t s (C v s) / 1024
/-- The seed-`s` part of column `v` of the sketch: the rows of the check `(s, C v s)` that column
`v` meets.  Row `p` belongs to that check iff `p / (lb+1) = s·M + C v s`. -/
def cr23Lvl (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) (s : ℕ) :
    Fin (cr23R N t) → ZMod 2 :=
  fun p =>
    if hs : s < cr23D N then
      (if p.val / (cr23Lb N + 1) = cr23Check N t ⟨s, hs⟩ (C v ⟨s, hs⟩) then
        cr23Sketch N t C (Pi.single v 1) p else 0)
    else 0
/-- The mask to XOR into the payload word `cr23Addr s v` to toggle the seed-`s` part of column `v`:
the `lb+1` bits of the check's block, at their offset inside that word. -/
def cr23Mask (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (s : Fin (cr23D N))
    (v : Fin N) : ℕ := packMem (cr23Word N) (cr23Lvl N t C v s.val) (cr23Addr N t C s v)
/-- `1 + N + 2·D·v`: the start of the two-word records of coordinate `v`. -/
def upBase (N : ℕ) (v : ℕ) : ℕ := 1 + N + 2 * (cr23D N * v)
/-- One past the last record of the pair block: `2·D` words per coordinate. -/
def cr23PairEnd (N : ℕ) : ℕ := 1 + N + 2 * (cr23D N * N)
/-- The start of the expander-adjacency block of the table. -/
def cr23Graph0 (N : ℕ) : ℕ := cr23PairEnd N
/-- **The deterministic preprocessing table of the update program**: the expander adjacency
`cr23Det` is kept verbatim on its own addresses, and the `(addr, mask)` record of every
`(coordinate, seed)` pair is appended after it. -/
def cr23UpDet (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) : ℕ → ℕ :=
  fun q =>
    if h0 : q = 0 then cr23D N
    else if hb : q ≤ N then upBase N (q - 1)
    else if hN : 0 < N ∧ 0 < cr23D N then
      (if hp : q < cr23PairEnd N then
        (if (q - (1 + N)) % 2 = 0 then
          cr23Addr N t C ⟨(q - (1 + N)) / 2 % cr23D N, Nat.mod_lt _ hN.2⟩
            ⟨(q - (1 + N)) / 2 / cr23D N % N, Nat.mod_lt _ hN.1⟩
        else
          cr23Mask N t C ⟨(q - (1 + N)) / 2 % cr23D N, Nat.mod_lt _ hN.2⟩
            ⟨(q - (1 + N)) / 2 / cr23D N % N, Nat.mod_lt _ hN.1⟩)
      else
        (C ⟨(q - cr23Graph0 N) % N, Nat.mod_lt _ hN.1⟩
          ⟨(q - cr23Graph0 N) / N % cr23D N, Nat.mod_lt _ hN.2⟩).val)
    else 0
/-- The prologue of `progUp`: fetch the seed count `D = det 0`, the record base `det (1+v)` of
coordinate `v`, and set up the loop registers. -/
def progUpPre : List Instr :=
  [iImm r13 1, iImm r12 2, iTbl r3 r1, iAdd r4 r0 r13, iTbl r5 r4, iBor r7 r5 r5,
   iAdd r10 r5 r13, iAdd r11 r5 r3, iAdd r11 r11 r3, iBor r6 r3 r3]
/-- The loop body of `progUp`: read the pair `(addr, mask)` of the current seed from the table, XOR
the mask into the payload word `addr`, advance both pointers and count down. -/
def progUpBody : List Instr :=
  [iTbl r8 r7, iTbl r9 r10, iLd r4 r8, iBxor r4 r4 r9, iSt r8 r4,
   iAdd r7 r7 r12, iAdd r10 r10 r12, iSub r6 r6 r13]
/-- The update program of Proposition 2.3.  It toggles column `v` of `CR_{N,t}` into the packed
payload: one read-modify-write per seed, `D = O(log N)` seeds, so `O(log N)` word operations. -/
def progUpStmt : Stmt :=
  Stmt.seq (Stmt.code progUpPre) (Stmt.loop (Cond.neqz r6) (Stmt.code progUpBody))
/-- The update program, compiled from `0` and followed by `halt`. -/
def progUp : Program := Stmt.compile progUpStmt 0 ++ [iHalt]
/-- One past the last cell of the update program's table; the decoder's own cells start here. -/
def cr23DecBase (N : ℕ) : ℕ := cr23Graph0 N + N * cr23D N
/-- **The decoder's preprocessing table**: the update program's table, plus `M` and `lb` in the two
cells just above the graph block. -/
def cr23DecDet (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) : ℕ → ℕ :=
  fun q =>
    if q < cr23DecBase N then cr23UpDet N t C q
    else if q = cr23DecBase N then cr23M t
    else if q = cr23DecBase N + 1 then cr23Lb N else 0
/-- The record block of the table starts here. -/
def cr23RecLo (N : ℕ) : ℕ := 1 + N
/-- **The address cells of the table.**  `a` is an even offset inside the record block, i.e.
`a = upBase N v + 2·s`: by `cr23UpDet_addr` that cell holds `cr23Addr N t C s v`, a *memory* address
of the packed payload.  These, and only these, are the cells a rebasing may move. -/
def cr23AddrSlot (N a : ℕ) : Prop :=
  cr23RecLo N ≤ a ∧ a < cr23Graph0 N ∧ (a - cr23RecLo N) % 2 = 0
instance cr23AddrSlot_decidable (N a : ℕ) : Decidable (cr23AddrSlot N a) := by
  unfold cr23AddrSlot; infer_instance
/-- **The rebased table**: `cr23DecDet N t C`, with `β` added to every cell that holds a *memory*
address.  Cells holding numbers (counts, indices, masks, field offsets) and cells holding `det`
indices (record bases) are left exactly as they are. -/
def cr23DecDetAt (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β : ℕ) : ℕ → ℕ :=
  fun a => if cr23AddrSlot N a then β + cr23DecDet N t C a else cr23DecDet N t C a
/-- The packed payload `y` stored from word `β` upwards, zero below `β` and above the payload. -/
def payMem (W : ℕ) {M : ℕ} (β : ℕ) (y : Fin M → ZMod 2) : ℕ → ℕ :=
  fun a => if β ≤ a ∧ a - β < wordsOf W M then packMem W y (a - β) else 0
/-- The start state of a run at payload base `β`: payload at `β`, argument register `r0 = i`. -/
def payStart (W : ℕ) {M : ℕ} (β : ℕ) (y : Fin M → ZMod 2) (i : ℕ) : RAMState :=
  initState (payMem W β y) i 0 0

end LinearSetReconciliation327.Main


