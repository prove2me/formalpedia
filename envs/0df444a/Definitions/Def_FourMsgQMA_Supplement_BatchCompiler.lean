-- Prove2me | Definitions.Def_FourMsgQMA_Supplement_BatchCompiler
-- name    : FourMsgQMA_Supplement_BatchCompiler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T16:30:08.658547+00:00
-- url     : https://prove2.me/theorems/e0c79cb1-059c-41a0-a091-e76ec8f81dcd
-- title:
--   The §4.2 four-message batch construction (Figure 3)
-- statement:
--   The **batch construction of §4.2** from a base protocol $\Pi_0$, a block commitment $\mathrm{SC}$, a vector BARG $B$ for the path relation $R_{\mathrm{path}}$ (Figure 3) and a leveled FHE, for $k$ entries with $d=\lceil\log_2k\rceil$, $K=2^d$, reference index $i_0=1$, and $X$ padded to $K$ entries by copying $x_1$:
--
--   1. $M_1$: one base setup $(p,r)\leftarrow\mathrm{Gen}(1^\lambda,T)$, FHE keys $(PK_\ell,SK_\ell)$ for $0\le\ell\le d$, $ct_\ell=\mathrm{Enc}(PK_\ell,SK_{\ell+1})$, $ct_r=\mathrm{Enc}(PK_d,r)$, and SC and $B$ parameters at $i_0$; the verifier keeps $SK_0$.
--   2. $M_2$: $\alpha=\mathrm{SC.Com}(hk,(\mu_i)_{i\in[K]})$.
--   3. $M_3$: a uniform base challenge $c$.
--   4. $M_4=(q,\pi)$: leaves $q_i=\mathrm{Eval}(PK_d,V(x_i,\cdot,\mu_i,c,z_i),ct_r)$, internal nodes $\mathrm{Eval}(PK_\ell,G_{q_{v0},q_{v1}},ct_\ell)$ with $G_{a,b}(SK)=D_{SK}(a)\wedge D_{SK}(b)$, root $q$, and a batch proof $\pi$ that every local instance $u_i=(i,x_i,\gamma,\alpha,c,q)$ satisfies $R_{\mathrm{path}}$.
--
--   The decision is $B.\mathrm{Verify}(crs,(u_i)_{i\in[K]},\pi)\wedge D_{SK_0}(q)$. The honest prover runs the $k$ base provers side by side on $\bigotimes_{i\in[k]}\omega_i$.
--
--   **Formalization Note** Pinned-down version (operator request): the circuits for $V$, $G_{a,b}$ and $R_{\mathrm{path}}$, the common level $L$, the block length and the declared lengths are implementation choices whose required properties are `BCImpl.Valid`; secret keys and the base tape are encrypted bit by bit.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §4.2, pp.26–28 (PDF 28–30), Figure 3

import Mathlib
import Definitions.Def_FourMsgQMA_FHE
import Definitions.Def_FourMsgQMA_IndexBARG
import Definitions.Def_FourMsgQMA_Supplement_BatchArg
import Definitions.Def_FourMsgQMA_Supplement_BaseSoundAt
import Definitions.Def_FourMsgQMA_Supplement_CircuitPolicyArg

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §4.2 (pp.26–28, PDF 28–30) and Figure 3:
the four-message batch construction from a base protocol `Π₀`, a block commitment `SC`, a vector
BARG `B` for the path relation `R_path`, and a leveled FHE.

Pinned-down version (operator request).

* `d = ⌈log₂ k⌉`, `K = 2^d`, reference index `i₀ = 1`; `X` is padded to `K` entries by copying
  `x₁`, and the honest prover copies `µ₁`, `z₁` likewise; one common FHE level `L = lev(λ, T, d)`.
* The circuits handed to `FHE.Eval` and the relation circuit of `B` are the implementation choices
  of `BCImpl` (the paper's "`V(x_i, ·, µ, c, z)`", "`G_{a,b}`", "Choose a common FHE depth bound
  `L = poly(λ, T, d)`", and the relation descriptor that "fixes all input and witness bounds");
  `BCImpl.Valid` states what the paper requires of them.
* Messages: `M1 = pack [p, hk, (PK_ℓ), (ct_ℓ), ct_r, crs]`, `M2 = α`, `M3 = c`, `M4 = pack [q, π]`.
  The `SC` block of entry `i` is `pack [µ_i]` padded to `m_µ` bits. The local instance and witness
  of `R_path` are `pack [i, x_i, γ, α, c, q]` and `pack [µ-block, ρ, z, (w₁, …, w_d)]`, padded to the
  declared lengths `n` and `m`; `Dec` rejects a batch whose instances do not fit.
* Secret keys and the base tape are encrypted bit by bit; the verifier's coin lengths cover the
  largest secret key and base tape the generators can output.
* The honest prover runs the `k` base cores side by side, core `i` on its own region of wires, and
  computes the commitment, the evaluation tree, the openings and the batch proof classically.
-/

namespace Supplement

open Classical QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- The primitives of §4.1 (p.26). -/
structure BCPrims where
  /-- The base protocol `Π₀`. -/
  base : BaseProtocol
  /-- The block commitment `SC`. -/
  sc : SEC
  /-- The vector BARG `B`. -/
  vb : VectorBARG
  /-- The leveled FHE. -/
  fhe : FHE

/-- The implementation choices of §4.2 the paper leaves open. -/
structure BCImpl where
  /-- The common FHE level `L(λ, T, d)`. -/
  lev : ℕ → ℕ → ℕ → ℕ
  /-- The `SC` block length `m_µ(λ, T)`. -/
  mmu : ℕ → ℕ → ℕ
  /-- The declared instance length `n(λ, T, k)` of `R_path`. -/
  nPath : ℕ → ℕ → ℕ → ℕ
  /-- The declared witness length `m(λ, T, k)` of `R_path`. -/
  mPath : ℕ → ℕ → ℕ → ℕ
  /-- A circuit on `n` inputs for `r ↦ V(x, r, µ, c, z)`: `(λ, T, x, µ, c, z, n)`. -/
  vCirc : ℕ → ℕ → Bits → Bits → Bits → Bits → ℕ → NandCircuit
  /-- A circuit on `n` inputs for `SK ↦ D_SK(a) ∧ D_SK(b)`: `(a, b, n)`. -/
  gCirc : Bits → Bits → ℕ → NandCircuit
  /-- The relation circuit of `R_path` at `(λ, T, k)`. -/
  pathCirc : ℕ → ℕ → ℕ → NandCircuit
  /-- The fixed length bound `(λ, T, k)` of the prover's answers; longer answers are rejected
  ("All messages have fixed polynomial bounds", p.11; "The verifier rejects an incorrectly sized
  `α`", p.28). -/
  ansLen : ℕ → ℕ → ℕ → ℕ

/-- The block of `µ` committed with `SC`. -/
def muBlock (m : ℕ) (μ : Bits) : Bits := padTo m (pack [μ])

/-- The local relation `R_path` of Figure 3 (p.27) at `(λ, T, k)`, on an instance and a witness
read from their packed encodings. Instance `u_i = (i, x_i, γ, α, c, q)` with
`γ = (hk, (PK_ℓ)_{ℓ ≤ d}, (ct_ℓ)_{ℓ < d}, ct_r)`; witness `w_i = (µ-block, ρ, z, ω)` with
`ω = (w₁, …, w_d)` one sibling ciphertext per depth. It rejects malformed inputs and otherwise
accepts exactly when `SC.Verify(hk, α, i, µ-block, ρ) = 1` and, with
`q̂_d = FHE.Eval(PK_d, V(x_i, ·, µ, c, z), ct_r)` and, for `ℓ = d − 1, …, 0` with `b_ℓ` the bit of
`i − 1` at depth `ℓ` from the root, `q̂_ℓ = FHE.Eval(PK_ℓ, G_{q̂_{ℓ+1}, w_{ℓ+1}}, ct_ℓ)` if `b_ℓ = 0`
and `FHE.Eval(PK_ℓ, G_{w_{ℓ+1}, q̂_{ℓ+1}}, ct_ℓ)` if `b_ℓ = 1`, the last value is `q̂₀ = q`. -/
def rpath (P : BCPrims) (I : BCImpl) (lam T k : ℕ) (ui wi : Bits) : Bool :=
  let a := unpack ui
  let i := bitsVal (a.getD 0 [])
  let x := a.getD 1 []
  let γ := unpack (a.getD 2 [])
  let α := a.getD 3 []
  let c := a.getD 4 []
  let q := a.getD 5 []
  let hk := γ.getD 0 []
  let pks := unpack (γ.getD 1 [])
  let cts := (unpack (γ.getD 2 [])).map unpack
  let ctr := unpack (γ.getD 3 [])
  let w := unpack wi
  let blk := w.getD 0 []
  let μ := (unpack blk).headD []
  let z := w.getD 2 []
  let ω := unpack (w.getD 3 [])
  let d := clog2 k
  let leaf := P.fhe.eval (pks.getD d []) (I.vCirc lam T x μ c z ctr.length) ctr
  let root := (List.range d).reverse.foldl (fun cur l =>
      let b := (i - 1).testBit (d - 1 - l)
      let g := if b then I.gCirc (ω.getD l []) cur (cts.getD l []).length
        else I.gCirc cur (ω.getD l []) (cts.getD l []).length
      P.fhe.eval (pks.getD l []) g (cts.getD l [])) leaf
  decide (1 ≤ i ∧ i ≤ 2 ^ d) && decide (ω.length = d) && decide (blk.length = I.mmu lam T) &&
    P.sc.verify hk α i blk (w.getD 1 []) && decide (root = q)

/-- The `K` entries of the padded batch: `x₁, …, x_k, x₁, …, x₁`. -/
def padBatch (k : ℕ) (X : List Bits) : List Bits :=
  (List.range (2 ^ clog2 k)).map fun j => if j < k then X.getD j [] else X.getD 0 []

/-- The packed `γ = (hk, (PK_ℓ), (ct_ℓ), ct_r)`. -/
def gammaOf (hk : Bits) (pks : List Bits) (cts : List (List Bits)) (ctr : List Bits) : Bits :=
  pack [hk, pack pks, pack (cts.map pack), pack ctr]

/-- The local instance `u_i = (i, x_i, γ, α, c, q)`, unpadded. -/
def pathInst (i : ℕ) (x γ α c q : Bits) : Bits := pack [binNat i, x, γ, α, c, q]

/-- The verifier's coin layout at `(λ, k, T)`: offsets of the base key, the `d + 1` FHE keys, the
tapes of `ct_ℓ` and `ct_r`, `SC` and `B`, and the total. -/
noncomputable def bcLayout (P : BCPrims) (I : BCImpl) (lam k T : ℕ) : List ℕ :=
  let d := clog2 k
  let L := I.lev lam T d
  let gE := P.fhe.genCoins lam L
  let eC := P.fhe.encCoins lam L
  let skM := maxLen gE fun r => (P.fhe.gen lam L r).2
  let rM := maxLen (P.base.genCoins lam T) fun r => (P.base.gen lam T r).2
  let n := I.nPath lam T k
  let m := I.mPath lam T k
  let sizes := [P.base.genCoins lam T, (d + 1) * gE, d * (skM * eC), rM * eC,
    P.sc.setupCoins lam (2 ^ d) (I.mmu lam T),
    P.vb.setupCoins lam (2 ^ d) (relSize n m (I.pathCirc lam T k))]
  (List.range (sizes.length + 1)).map fun j => (sizes.take j).sum

/-- Message 1 (`V₁`, p.27–28) at `(λ, k, T)` from the coins `r`: `M1 = (p, γ, crs)` and the
verifier state `pack [k, T, M1, SK₀]`. -/
noncomputable def bcFirst (P : BCPrims) (I : BCImpl) (lam k T : ℕ) (r : Bits) : Bits × Bits :=
  let d := clog2 k
  let L := I.lev lam T d
  let gE := P.fhe.genCoins lam L
  let eC := P.fhe.encCoins lam L
  let skM := maxLen gE fun r => (P.fhe.gen lam L r).2
  let o := bcLayout P I lam k T
  let n := I.nPath lam T k
  let m := I.mPath lam T k
  let pr := P.base.gen lam T (slice r (o.getD 0 0) (P.base.genCoins lam T))
  let keys := (List.range (d + 1)).map fun l => P.fhe.gen lam L (slice r (o.getD 1 0 + l * gE) gE)
  let pks := keys.map Prod.fst
  let cts := (List.range d).map fun l =>
    encBits P.fhe (pks.getD l []) (keys.getD (l + 1) ([], [])).2 r (o.getD 2 0 + l * (skM * eC)) eC
  let ctr := encBits P.fhe (pks.getD d []) pr.2 r (o.getD 3 0) eC
  let hk := (P.sc.setup lam (2 ^ d) (I.mmu lam T) 1 (slice r (o.getD 4 0) (P.sc.setupCoins lam (2 ^ d) (I.mmu lam T)))).1
  let crs := (P.vb.setup lam (2 ^ d) n m (I.pathCirc lam T k) 1
    (slice r (o.getD 5 0) (P.vb.setupCoins lam (2 ^ d) (relSize n m (I.pathCirc lam T k))))).1
  let m1 := pack [pr.1, hk, pack pks, pack (cts.map pack), pack ctr, crs]
  (m1, pack [binNat k, binNat T, m1, (keys.getD 0 ([], [])).2])

/-- The §4.2 verifier with honest-prover fields `hon`: `Pre` records `(k, T)` and the coins; `V₁`
sends `M1`; `V₂` sends a fresh uniform `c ∈ {0,1}^{m(λ,T)}`; `Dec(X, v₂, (q, π))` builds
`u_i = (i, x_i, γ, α, c, q)` for the padded batch, rejects answers longer than the fixed bound, a
batch of the wrong size or with an instance longer than `n`, and returns `B.Verify(crs, (u_i)_{i ∈ [K]}, π) ∧ D_{SK₀}(q)`. -/
noncomputable def batchCompilerVerifier (P : BCPrims) (I : BCImpl)
    (hon : (ℕ → ℕ → ℕ) × (ℕ → ℕ → List Bits → Core) × (ℕ → ℕ → List Bits → ℕ → ℕ) ×
      (ℕ → ℕ → List Bits → ℕ → Bits → Bits) × (ℕ → ℕ → List Bits → ℕ → Bits → Bits)) : BatchArg where
  coins0 := fun lam k T => (bcLayout P I lam k T).getLastD 0
  coins1 := fun _ _ _ => 0
  coins2 := fun lam _ T => P.base.chalLen lam T
  pre := fun _ k T r => pack [binNat k, binNat T, r]
  v1 := fun lam v0 _ =>
    let l := unpack v0
    bcFirst P I lam (bitsVal (l.getD 0 [])) (bitsVal (l.getD 1 [])) (l.getD 2 [])
  v2 := fun _ v1 a1 r => (r, pack [v1, a1, r])
  dec := fun lam X v2 a2 =>
    let st := unpack v2
    let st1 := unpack (st.getD 0 [])
    let k := bitsVal (st1.getD 0 [])
    let T := bitsVal (st1.getD 1 [])
    let m1 := unpack (st1.getD 2 [])
    let sk0 := st1.getD 3 []
    let α := st.getD 1 []
    let c := st.getD 2 []
    let fin := unpack a2
    let q := fin.getD 0 []
    let π := fin.getD 1 []
    let γ := pack [m1.getD 1 [], m1.getD 2 [], m1.getD 3 [], m1.getD 4 []]
    let us := (padBatch k X).zipIdx.map fun p => pathInst (p.2 + 1) p.1 γ α c q
    decide (α.length ≤ I.ansLen lam T k) && decide (a2.length ≤ I.ansLen lam T k) &&
    decide (X.length = k) && us.all (fun u => decide (u.length ≤ I.nPath lam T k)) &&
      P.vb.verify (m1.getD 5 []) (us.map (padTo (I.nPath lam T k))) π && fheD P.fhe sk0 q
  copies := hon.1
  core := hon.2.1
  region := hon.2.2.1
  toCore := hon.2.2.2.1
  toVerifier := hon.2.2.2.2

/-! ### The honest prover (pp.28) -/

/-- An instruction of an `m`-wire circuit placed on the wires `o, …, o + m − 1` of an `n`-wire core
(dropped if it does not fit; it always fits in `batchCore`). -/
def shiftInstr (n o : ℕ) {m : ℕ} : Instr m → List (Instr n)
  | .h i => if h : o + i.val < n then [.h ⟨o + i.val, h⟩] else []
  | .s i => if h : o + i.val < n then [.s ⟨o + i.val, h⟩] else []
  | .t i => if h : o + i.val < n then [.t ⟨o + i.val, h⟩] else []
  | .x i => if h : o + i.val < n then [.x ⟨o + i.val, h⟩] else []
  | .cnot i j _ => if h : o + i.val < n ∧ o + j.val < n ∧ o + i.val ≠ o + j.val then
      [.cnot ⟨o + i.val, h.1⟩ ⟨o + j.val, h.2.1⟩ (fun e => h.2.2 (congrArg Fin.val e))] else []

/-- A wire list placed from wire `o` on. -/
def shiftWires (n o : ℕ) {m : ℕ} (w : List (Fin m)) : List (Fin n) :=
  w.filterMap fun a => if h : o + a.val < n then some ⟨o + a.val, h⟩ else none

/-- The offset of the region of core `i`. -/
def coreOff (cs : List Core) (i : ℕ) : ℕ := ((cs.take i).map Core.n).sum

/-- The cores `cs` side by side: core `i` on the wires from `coreOff cs i` on; round `j` writes the
inputs, runs the layered circuits one core after the other, and measures the output wires of all
cores, in the order of `cs`; the tape is the cores' tapes followed by `extra` bits. -/
def batchCore (cs : List Core) (extra : ℕ) : Core where
  n := (cs.map Core.n).sum
  steps := (List.range ((cs.map fun S => S.steps.length).foldr max 0)).map fun j =>
    { inW := (List.range cs.length).flatMap fun i =>
        shiftWires _ (coreOff cs i) ((cs.getD i ⟨0, [], 0⟩).stepAt j).inW
      circ := (List.range cs.length).flatMap fun i =>
        ((cs.getD i ⟨0, [], 0⟩).stepAt j).circ.map fun layer => layer.flatMap (shiftInstr _ (coreOff cs i))
      outW := (List.range cs.length).flatMap fun i =>
        shiftWires _ (coreOff cs i) ((cs.getD i ⟨0, [], 0⟩).stepAt j).outW }
  tape := (cs.map Core.tape).sum + extra

/-- The view of base prover `i` inside a batch view `v = pack (u :: q₀ :: c₀ :: q₁ :: c₁ …)`: its slice
of the tape, the base messages (the base key `p`, the first field of `M1`; the challenge `c = M3`),
and its slice of each measured core outcome. -/
def entryView (cs : List Core) (i : ℕ) (v : Bits) : Bits :=
  let S := cs.getD i ⟨0, [], 0⟩
  let tOff := ((cs.take i).map Core.tape).sum
  let oOff : ℕ → ℕ := fun j => ((cs.take i).map fun S' => S'.outLen j).sum
  pack ((unpack v).zipIdx.map fun p =>
    if p.2 = 0 then slice p.1 tOff S.tape
    else if p.2 % 2 = 1 then (if p.2 = 1 then (unpack p.1).headD [] else p.1)
    else slice p.1 (oOff (p.2 / 2 - 1)) (S.outLen (p.2 / 2 - 1)))

/-- The honest prover's classical computation (p.28) at `(λ, T)` for the batch `X` (`k = |X|`)
from the batch view `v = pack (u :: M1 :: c₀ :: M3 :: c₁ …)`: every `µ_i` (from the base controllers
on the round-0 view), the `SC` blocks of the `K` padded entries and `α = SC.Com(hk, blocks)`; every
`z_i`; the leaves `q_i = FHE.Eval(PK_d, V(x_i, ·, µ_i, c, z_i), ct_r)` (padded entries copy entry
`1`), the internal nodes `q_v = FHE.Eval(PK_ℓ, G_{q_{v0}, q_{v1}}, ct_ℓ)` and the root `q`; and the
unpadded local instances `u_i = (i, x_i, γ, α, c, q)` and witnesses
`w_i = (µ_i-block, SC.Open(hk, blocks, i), z_i, sibling path)` for `i ∈ [K]`. -/
noncomputable def bcLocal (P : BCPrims) (I : BCImpl) (lam T : ℕ) (X : List Bits) (v : Bits) :
    Bits × List Bits × List Bits × Bits :=
  let k := X.length
  let d := clog2 k
  let K := 2 ^ d
  let cs := X.map (P.base.core lam)
  let l := unpack v
  let m1 := unpack (l.getD 1 [])
  let hk := m1.getD 1 []
  let pks := unpack (m1.getD 2 [])
  let cts := (unpack (m1.getD 3 [])).map unpack
  let ctr := unpack (m1.getD 4 [])
  let v0 := pack (l.take 3)
  let μs := (List.range k).map fun i => P.base.toVerifier lam (X.getD i []) 0 (entryView cs i v0)
  let blocks := (List.range K).map fun i => muBlock (I.mmu lam T) (μs.getD (if i < k then i else 0) [])
  let α := P.sc.com hk blocks
  let c := l.getD 3 []
  let zs := (List.range k).map fun i => P.base.toVerifier lam (X.getD i []) 1 (entryView cs i v)
  let leaf : ℕ → Bits := fun i =>
    let i' := if i < k then i else 0
    P.fhe.eval (pks.getD d []) (I.vCirc lam T (X.getD i' []) (μs.getD i' []) c (zs.getD i' []) ctr.length) ctr
  let node : ℕ → ℕ → Bits := fun h => Nat.rec (motive := fun _ => ℕ → Bits) leaf
    (fun h' prev jj => P.fhe.eval (pks.getD (d - h' - 1) [])
      (I.gCirc (prev (2 * jj)) (prev (2 * jj + 1)) (cts.getD (d - h' - 1) []).length) (cts.getD (d - h' - 1) [])) h
  let q := node d 0
  let γ := gammaOf hk pks cts ctr
  let us := (List.range K).map fun i => pathInst (i + 1) ((padBatch k X).getD i []) γ α c q
  let ws := (List.range K).map fun i => pack [blocks.getD i [], P.sc.opn hk blocks (i + 1),
    zs.getD (if i < k then i else 0) [],
    pack ((List.range d).map fun ℓ => node (d - ℓ - 1) ((i / 2 ^ (d - ℓ - 1)) ^^^ 1))]
  (α, us, ws, q)

/-- The honest prover's answers: round 0 sends `α`; round 1 sends `(q, π)` with
`π = B.Prove(crs, (u_i padded to n), (w_i padded to m))`, using the last `B.proveCoins` bits of the
tape. -/
noncomputable def bcAnswer (P : BCPrims) (I : BCImpl) (lam T : ℕ) (X : List Bits) (j : ℕ) (v : Bits) :
    Bits :=
  let o := bcLocal P I lam T X v
  if j = 0 then o.1 else
  let l := unpack v
  let crs := (unpack (l.getD 1 [])).getD 5 []
  let tape := l.getD 0 []
  let π := P.vb.prove crs (o.2.1.map (padTo (I.nPath lam T X.length)))
    (o.2.2.1.map (padTo (I.mPath lam T X.length))) (tape.drop ((X.map (P.base.core lam)).map Core.tape).sum)
  pack [o.2.2.2, π]

/-- The §4.2 construction as a batch argument: the verifier of `batchCompilerVerifier` and the
honest prover that runs the `k` base cores side by side (`N(λ, T)` copies of each entry's witness on
its own region, no further copies), with `bcAnswer` as its answer controller and the base
controllers writing into the cores. -/
noncomputable def batchCompiler (P : BCPrims) (I : BCImpl) : BatchArg :=
  batchCompilerVerifier P I
    (P.base.copies,
     fun lam T X => batchCore (X.map (P.base.core lam))
       (P.vb.proveCoins lam (2 ^ clog2 X.length)
         (relSize (I.nPath lam T X.length) (I.mPath lam T X.length) (I.pathCirc lam T X.length))),
     fun lam _ X i => (P.base.core lam (X.getD i [])).n,
     fun lam _ X j v =>
       let cs := X.map (P.base.core lam)
       (List.range X.length).flatMap fun i =>
         padTo ((cs.getD i ⟨0, [], 0⟩).stepAt j).inW.length
           (P.base.toCore lam (X.getD i []) j (entryView cs i v)),
     fun lam T X j v => bcAnswer P I lam T X j v)

/-- The requirements of §4.2 (pp.26–27) on the implementation choices: the circuits compute their
functions (`vCirc`: `r ↦ V(x, r, µ, c, z)`; `gCirc a b`: `SK ↦ D_SK(a) ∧ D_SK(b)`; `pathCirc`:
`R_path` on `n + m` inputs), every circuit evaluated under a key of level `L = lev(λ, T, d)` has depth
at most `L` on the inputs it is evaluated on (`vCirc` for an entry with `t_L(x) ≤ T`, a challenge of
the prescribed length and the length of a base tape of `Gen(1^λ, T)`; `gCirc` for the length of a
secret key of `FHE.Gen(1^λ, 1^L)`), the compilers are polynomial time, the bounds are polynomial,
and the declared lengths fit the honest encodings: `pack [µ]` fits `m_µ` for every honest first
response at `t_L(x) ≤ T`, and the honest local instances, witnesses and answers fit `n`, `m` and the
answer bound for every batch with `t_L(x_i) ≤ T`, every view the honest prover can have (its tape of
the prescribed length, the genuine `M1` and a challenge of the prescribed length) and every outcome
of the verifier's key generation ("The relation descriptor fixes all input and witness bounds",
p.27; "Choose a common FHE depth bound `L = poly(λ, T, d)` supporting both `V` and two total
decryption circuits followed by one and gate", pp.26–27). -/
def BCImpl.Valid (I : BCImpl) (P : BCPrims) (F : QMAFamily) : Prop :=
  (∀ lam T x μ c z n, Computes (I.vCirc lam T x μ c z n) n fun r => P.base.verdict lam x r μ c z) ∧
  (∀ a b n, Computes (I.gCirc a b n) n fun sk => fheD P.fhe sk a && fheD P.fhe sk b) ∧
  (∀ lam T k, RelationOK (I.nPath lam T k) (I.mPath lam T k) (I.pathCirc lam T k) ∧
    ∀ w : Bits, w.length = I.nPath lam T k + I.mPath lam T k →
      (I.pathCirc lam T k).eval w =
        rpath P I lam T k (w.take (I.nPath lam T k)) (w.drop (I.nPath lam T k))) ∧
  (∀ lam T d (x : Str) μ c z (rb : Bits), localCost F x ≤ T → c.length = P.base.chalLen lam T →
    rb.length = P.base.genCoins lam T →
    (I.vCirc lam T x μ c z (P.base.gen lam T rb).2.length).depth ≤ I.lev lam T d) ∧
  (∀ lam T d a b (r : Bits), r.length = P.fhe.genCoins lam (I.lev lam T d) →
    (I.gCirc a b (P.fhe.gen lam (I.lev lam T d) r).2.length).depth ≤ I.lev lam T d) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam T x μ c z n,
    g (pack [unary lam, unary T, x, μ, c, z, unary n]) = (I.vCirc lam T x μ c z n).encode) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ a b n, g (pack [a, b, unary n]) = (I.gCirc a b n).encode) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam T k,
    g (pack [unary lam, unary T, unary k]) = (I.pathCirc lam T k).encode) ∧
  (∃ p : MvPolynomial (Fin 4) ℕ, ∀ lam T k,
    I.lev lam T (clog2 k) ≤ eval4 p lam T (clog2 (k + 1)) 0 ∧ I.mmu lam T ≤ eval4 p lam T 0 0 ∧
      I.nPath lam T k ≤ eval4 p lam T (clog2 (k + 1)) 0 ∧ I.mPath lam T k ≤ eval4 p lam T (clog2 (k + 1)) 0 ∧
      (I.pathCirc lam T k).size ≤ eval4 p lam T (clog2 (k + 1)) 0 ∧
      I.ansLen lam T k ≤ eval4 p lam T (clog2 (k + 1)) 0) ∧
  (∀ lam T (x : Str) (v : Bits), localCost F x ≤ T →
    (pack [P.base.toVerifier lam x 0 v]).length ≤ I.mmu lam T) ∧
  (∀ lam T (X : List Bits) (r tape c0 c c1 : Bits), (∀ x ∈ X, localCost F x ≤ T) →
    r.length = (bcLayout P I lam X.length T).getLastD 0 →
    tape.length = ((X.map (P.base.core lam)).map Core.tape).sum +
      P.vb.proveCoins lam (2 ^ clog2 X.length)
        (relSize (I.nPath lam T X.length) (I.mPath lam T X.length) (I.pathCirc lam T X.length)) →
    c.length = P.base.chalLen lam T →
    let v := pack [tape, (bcFirst P I lam X.length T r).1, c0, c, c1]
    (∀ u ∈ (bcLocal P I lam T X v).2.1, u.length ≤ I.nPath lam T X.length) ∧
      (∀ w ∈ (bcLocal P I lam T X v).2.2.1, w.length ≤ I.mPath lam T X.length) ∧
      ∀ j, (bcAnswer P I lam T X j v).length ≤ I.ansLen lam T X.length)

end Supplement

end FourMsgQMA


