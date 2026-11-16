-- Prove2me | Definitions.Def_FourMsgQMA_Supplement_CircuitPolicyArg
-- name    : FourMsgQMA_Supplement_CircuitPolicyArg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:27:01.134077+00:00
-- url     : https://prove2.me/theorems/362c595b-4692-400a-8db8-e7edb97f383d
-- title:
--   The §5.1 four-message construction for NP ∘ batchQMA as an Arg4 (Figures 4 and 5)
-- statement:
--   The **four-message construction of §5.1** for a circuit policy $C$ with $k$ inputs and $s$ gates and a batch $X$, from a base protocol $\Pi_0$, a leveled FHE, a block commitment $\mathrm{SC}$, an index BARG $\mathrm{IB}$, Merkle commitments $\mathrm{MT}$ and Kilian's argument $\Sigma$:
--
--   1. $M_1$: the base key, $d+1$ FHE keys ($d=\lceil\log_2k\rceil$) with the encrypted key chain and the encrypted base tape, the SC and IB parameters, Merkle keys and digests of the policy table and of the indexed inputs $(i,x_i)$, a Merkle key for the selection vector, and a Kilian key $vk$.
--   2. $M_2=(\alpha_\mu,h_y,\beta)$: the commitments to the first base responses and to the selection $y$, and the Kilian root for the **authorization relation** $R_{\mathrm{auth}}$ (Figure 4: the committed table is a canonical circuit, $y$ is committed under $h_y$, and the wire values satisfy $C(y)=1$).
--   3. $M_3=(c,\xi)$: a uniform base challenge and a Kilian seed.
--   4. $M_4=(q,\pi,a_\Sigma)$: the root of an encrypted AND tree (selected leaves evaluate the base verifier, unselected leaves the constant-one circuit), an index-BARG proof for the **selected-index relation** $R_{\mathrm{sel}}$ (Figure 5), and the Kilian response.
--
--   The decision is $\Sigma.\mathrm{Verify}\wedge\mathrm{IB.Verify}(crs,C_\theta,\pi)\wedge D_{SK_0}(q)$; if $C(0)=1$ the verifier accepts (no no-batches exist).
--
--   **Formalization Note** Pinned-down version (operator request): the circuits for $V(x_i,\cdot,\mu,c,z)$, $G_{v_0,v_1}$, the constant one and $C_\theta$, and the bounds $L$, $B_C$, $m_C$, $m_\mu$ and the format bound on $|\alpha_\mu|$ (checked by the decision), are implementation choices whose required properties are `CPImpl.Valid`; $T=t(X)$; indices are 1-based, Merkle positions $i-1$.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §5.1, pp.33–38 (PDF 35–40), Figures 4–5

import Mathlib
import Definitions.Def_FourMsgQMA_Arg4
import Definitions.Def_FourMsgQMA_FHE
import Definitions.Def_FourMsgQMA_IndexBARG
import Definitions.Def_FourMsgQMA_Supplement_BaseSoundAt
import Definitions.Def_FourMsgQMA_Supplement_Kilian

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §5.1 (pp.33–38, PDF 35–40), Figures 4
and 5: the four-message construction for NP ∘ batchQMA with a circuit policy, as the verifier of a
published `FourMsgQMA.Arg4`.

Ingredients (p.33): a base protocol `Π₀`, a leveled FHE, a block commitment `SC`, an index BARG
`IB`, Merkle commitments `MT` (the balanced tree `Supplement.merkleCommit` of a hash family), and
Kilian's argument `Σ` for the authorization relation `R_auth`.

Pinned-down version (operator request).

* The paper leaves the circuits handed to `FHE.Eval` and `IB` implicit ("`V(x_i, ·, µ, c, z)`",
  "`G_{v₀,v₁}`", "the fixed, canonical constant-one circuit", "the index circuit `C_θ`") and fixes
  the level and size bounds by "Choose the compatible depth bounds `L_ℓ` as in Section 4" and "fixed
  bounds `B_C, m_C = poly(H)`". These are the fields of `CPImpl`; `CPImpl.Valid` states what the
  paper requires of them (each circuit computes its function, polynomial-time compilation, depth
  at most the common level `L`), and the soundness theorem holds for every valid choice.
* `T = t(X) = max_i t_L(x_i)` (`batchCost`), `d = ⌈log₂ k⌉`, `K = 2^d`, one common level
  `L = lev(λ, T, d)` for the `d + 1` FHE keys; indices `i ∈ [k]` are 1-based as in the paper, a
  Merkle position is `i − 1`.
* Every message is a `pack` of its fields; secret keys and the base tape are encrypted bit by bit.
  `M1 = (p, hk, crs, (PK_ℓ), (ct_ℓ), ct_r, hk_C, h_C, hk_X, h_X, hk_y, vk)`, `M2 = (α_µ, h_y, β)`,
  `M3 = (c, ξ)`, `M4 = (q, π, a_Σ)`.
* The policy table is committed as `s + 1` records (header `(k, s, out)` and one record
  `(type, u_t, v_t)` per gate), each the `pack` of the three numbers in binary padded to
  `6⌈log₂(k + s + 5)⌉ + 3` bits; an indexed input `(i, x_i)` is the `pack` of `i` in binary and `x_i`,
  padded to `2(⌈log₂(k + 1)⌉ + T) + 2` bits.
* The verifier's coin lengths are the least bounds covering every instance of the given size and
  every outcome of the key generators.
-/

namespace Supplement

open Classical QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- The primitives of §5.1 (p.33). -/
structure CPPrims where
  /-- The base protocol `Π₀`. -/
  base : BaseProtocol
  /-- The leveled FHE. -/
  fhe : FHE
  /-- The block commitment `SC`. -/
  sc : SEC
  /-- The index BARG `IB`. -/
  ib : IndexBARG
  /-- The hash family of the Merkle commitments `MT`. -/
  mt : HashFamily
  /-- Kilian's argument `Σ` (its hash family and PCP). -/
  kil : Kilian

/-- The implementation choices the paper leaves open. -/
structure CPImpl where
  /-- The common FHE level `L(λ, T, d)`. -/
  lev : ℕ → ℕ → ℕ → ℕ
  /-- The size bound `B_C(λ, T, k, s)` of the index circuit. -/
  bc : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- The index-BARG witness length `m_C(λ, T, k, s)`. -/
  mc : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- The base first-response length `m_µ(λ, T)`, the block length of `SC`. -/
  mmu : ℕ → ℕ → ℕ
  /-- A circuit on `n` inputs for `r ↦ V(x, r, µ, c, z)`: `(λ, T, x, µ, c, z, n)`. -/
  vCirc : ℕ → ℕ → Bits → Bits → Bits → Bits → ℕ → NandCircuit
  /-- A circuit on `n` inputs for `SK ↦ D_SK(a) ∧ D_SK(b)`: `(a, b, n)`. -/
  gCirc : Bits → Bits → ℕ → NandCircuit
  /-- The constant-one circuit on `n` inputs. -/
  oneCirc : ℕ → NandCircuit
  /-- The index circuit `C_θ` compiled from `θ`. -/
  selCirc : ℕ → Bits → NandCircuit
  /-- The declared instance and witness bounds of `R_auth`. -/
  authIn : ℕ → ℕ
  /-- See `authIn`. -/
  authWit : ℕ → ℕ
  /-- The fixed length bound `(λ, T, k)` of the commitment `α_µ`; a longer `α_µ` is rejected
  ("The final decision checks the fixed formats", p.37). -/
  aLen : ℕ → ℕ → ℕ → ℕ

/-- `C` is a well-formed circuit on `n` inputs computing `f` on every `n`-bit input. -/
def Computes (C : NandCircuit) (n : ℕ) (f : Bits → Bool) : Prop :=
  C.WellFormed ∧ C.nIn = n ∧ ∀ w : Bits, w.length = n → C.eval w = f w

/-- `D_SK(ct) = [FHE.Dec(SK, ct) = 1]` (p.27). -/
def fheD (E : FHE) (sk ct : Bits) : Bool := E.dec sk ct

/-- `slice r o n`: `n` coins of `r` from offset `o`. -/
def slice (r : Bits) (o n : ℕ) : Bits := (r.drop o).take n

/-- The largest length of `f r` over the coin strings `r` of length `c`. -/
noncomputable def maxLen (c : ℕ) (f : Bits → Bits) : ℕ :=
  Finset.univ.sup fun r : Qubits c => (f (toBits r)).length

/-- Bit-by-bit encryption of `b` under `PK`, the `j`-th bit with the tape at `o + j·e`. -/
def encBits (E : FHE) (PK b r : Bits) (o e : ℕ) : List Bits :=
  (List.range b.length).map fun j => E.enc PK (b.getD j false) (slice r (o + j * e) e)

/-- The record length `6⌈log₂(k + s + 5)⌉ + 3` of the policy table. -/
def recLen (k s : ℕ) : ℕ := 6 * clog2 (k + s + 5) + 3

/-- A record: three numbers in binary, packed and padded. -/
def record (k s a b c : ℕ) : Bits := padTo (recLen k s) (pack [binNat a, binNat b, binNat c])

/-- The canonical policy records of `C`: the header `(k, s, out)` and the gate records. -/
def policyRecords {k s : ℕ} (C : PolicyCircuit k s) : List Bits :=
  record k s k s C.out :: List.ofFn fun j : Fin s => record k s (C.gate j).1.code (C.gate j).2.1 (C.gate j).2.2

/-- The block length `m_X = 2(⌈log₂(k + 1)⌉ + T) + 2` of an indexed input. -/
def xLen (k T : ℕ) : ℕ := 2 * (clog2 (k + 1) + T) + 2

/-- The block `(i, x)` of the indexed input vector. -/
def xBlock (k T i : ℕ) (x : Bits) : Bits := padTo (xLen k T) (pack [binNat i, x])

/-- The numbers of a record. -/
def recordNums (rec : Bits) : ℕ × ℕ × ℕ :=
  let l := unpack rec
  (bitsVal (l.getD 0 []), bitsVal (l.getD 1 []), bitsVal (l.getD 2 []))

/-- The gate type of a code. -/
def typeOfCode : ℕ → Option GateType
  | 0 => some .and | 1 => some .or | 2 => some .not | 3 => some .zero | 4 => some .one | _ => none

/-- The authorization relation `R_auth` of Figure 4 (p.34). Instance
`u = pack [hk_C, hk_y, h_C, h_y, k, s]` (`k, s` in binary); witness `w = pack [C', y, a]`, with `C'`
the packed list of policy records, `y ∈ {0,1}^k` and `a ∈ {0,1}^{k+s}`. It accepts exactly when:

1. `MT.Commit(hk_C, C') = h_C` (with `s + 1` records of the record length) and
   `MT.Commit(hk_y, y) = h_y` (one-bit blocks);
2. `C'` is a canonical table: header `(k, s, out)` with `out ∈ [k + s]`; each gate `t = k + 1 + j` has
   a type code in `{0, …, 4}` and children `1 ≤ u_t, v_t < t`, `v_t = u_t` for NOT, `u_t = v_t = 1`
   for a constant;
3. `a_i = y_i` for `i ∈ [k]`, `a_t = gate_t(a_{u_t}, a_{v_t})` for `k < t ≤ k + s`, and `a_out = 1`. -/
def rauth (H : HashFamily) (n m : ℕ → ℕ) : Relation where
  inLen := n
  witLen := m
  rel := fun u w =>
    let a := unpack u
    let k := bitsVal (a.getD 4 [])
    let s := bitsVal (a.getD 5 [])
    let ww := unpack w
    let recs := unpack (ww.getD 0 [])
    let y := ww.getD 1 []
    let arr := ww.getD 2 []
    let hdr := recordNums (recs.getD 0 [])
    let gate (t : ℕ) : ℕ × ℕ × ℕ := recordNums (recs.getD (t - k) [])
    let av (t : ℕ) : Bool := arr.getD (t - 1) false
    decide (recs.length = s + 1) && recs.all (fun rec => decide (rec.length = recLen k s)) &&
      decide (y.length = k) && decide (arr.length = k + s) &&
      decide (merkleCommit H (s + 1) (recLen k s) (a.getD 0 []) recs = a.getD 2 []) &&
      decide (merkleCommit H k 1 (a.getD 1 []) (bitBlocks y) = a.getD 3 []) &&
      decide (hdr.1 = k ∧ hdr.2.1 = s ∧ 1 ≤ hdr.2.2 ∧ hdr.2.2 ≤ k + s) &&
      ((List.range s).all fun j =>
        let t := k + 1 + j
        let g := gate t
        match typeOfCode g.1 with
        | none => false
        | some ty =>
          decide (1 ≤ g.2.1 ∧ g.2.1 < t ∧ 1 ≤ g.2.2 ∧ g.2.2 < t) &&
            decide (ty = .not → g.2.2 = g.2.1) &&
            decide (ty = .zero ∨ ty = .one → g.2.1 = 1 ∧ g.2.2 = 1) &&
            decide (av t = ty.apply (av g.2.1) (av g.2.2))) &&
      ((List.range k).all fun i => decide (av (i + 1) = y.getD i false)) &&
      av hdr.2.2

/-- The public data `θ` of the local index relation (p.34): the parameters `(k, T, s)`, then
`hk` (of `SC`), the FHE public keys, the encrypted key chain, the encrypted base tape, `hk_X, h_X,
hk_y, h_y`, and the later fields `α_µ, c, q`. -/
def theta (k T s : ℕ) (hk : Bits) (pks : List Bits) (cts : List (List Bits)) (ctr : List Bits)
    (hkX hX hky hy αμ c q : Bits) : Bits :=
  pack [binNat k, binNat T, binNat s, hk, pack pks, pack (cts.map pack), pack ctr, hkX, hX, hky, hy, αμ, c, q]

/-- The selected-index relation `R_sel(θ, i; w)` of Figure 5 (p.35). The witness is
`w = pack [x, ρ_X, b, ρ_y, µ, ρ_µ, z, χ]` (`χ` the packed sibling ciphertexts `χ₀, …, χ_{d−1}`),
read from its first `m_C` bits. It rejects malformed inputs and otherwise accepts exactly when:

1. `b ∈ {0,1}`, `MT.Verify(hk_X, h_X, i, (i, x), ρ_X) = 1`, `MT.Verify(hk_y, h_y, i, b, ρ_y) = 1`;
2. if `b = 1`: `|µ| = m_µ`, `SC.Verify(hk, α_µ, i, µ, ρ_µ) = 1`, and the leaf is
   `q̂_d = Eval(PK_d, V(x, ·, µ, c, z), ct_r)`; if `b = 0`: `µ, ρ_µ, z` are the fixed dummy values
   (empty) and `q̂_d = Eval(PK_d, 1, ct_r)`;
3. with `ϵ₀ ⋯ ϵ_{d−1}` the binary representation of `i − 1` from root to leaf, for
   `ℓ = d − 1, …, 0`: `(v₀, v₁) = (q̂_{ℓ+1}, χ_ℓ)` if `ϵ_ℓ = 0` and `(χ_ℓ, q̂_{ℓ+1})` if `ϵ_ℓ = 1`,
   `q̂_ℓ = Eval(PK_ℓ, G_{v₀,v₁}, ct_ℓ)`; and `q̂₀ = q`. -/
def rsel (P : CPPrims) (I : CPImpl) (lam : ℕ) (θ : Bits) (i : ℕ) (w : Bits) : Bool :=
  let t := unpack θ
  let k := bitsVal (t.getD 0 [])
  let T := bitsVal (t.getD 1 [])
  let s := bitsVal (t.getD 2 [])
  let hk := t.getD 3 []
  let pks := unpack (t.getD 4 [])
  let cts := (unpack (t.getD 5 [])).map unpack
  let ctr := unpack (t.getD 6 [])
  let hkX := t.getD 7 []
  let hX := t.getD 8 []
  let hky := t.getD 9 []
  let hy := t.getD 10 []
  let αμ := t.getD 11 []
  let c := t.getD 12 []
  let q := t.getD 13 []
  let d := clog2 k
  let f := unpack (w.take (I.mc lam T k s))
  let x := f.getD 0 []
  let b := f.getD 2 []
  let μ := f.getD 4 []
  let ρμ := f.getD 5 []
  let z := f.getD 6 []
  let χ := unpack (f.getD 7 [])
  let leaf : Bits :=
    if b = [true] then P.fhe.eval (pks.getD d []) (I.vCirc lam T x μ c z ctr.length) ctr
    else P.fhe.eval (pks.getD d []) (I.oneCirc ctr.length) ctr
  let up : ℕ → Bits → Bits := fun l cur =>
    let ε := (i - 1).testBit (d - 1 - l)
    let v0 := if ε then χ.getD l [] else cur
    let v1 := if ε then cur else χ.getD l []
    P.fhe.eval (pks.getD l []) (I.gCirc v0 v1 (cts.getD l []).length) (cts.getD l [])
  let root := (List.range d).reverse.foldl (fun cur l => up l cur) leaf
  decide (1 ≤ i ∧ i ≤ k) && decide (b = [true] ∨ b = [false]) && decide (χ.length = d) &&
    merkleVerify P.mt lam k (xLen k T) hkX hX (i - 1) (xBlock k T i x) (f.getD 1 []) &&
    merkleVerify P.mt lam k 1 hky hy (i - 1) b (f.getD 3 []) &&
    (if b = [true] then decide (μ.length = I.mmu lam T) && P.sc.verify hk αμ i μ ρμ
      else decide (μ = [] ∧ ρμ = [] ∧ z = [])) &&
    decide (root = q)

/-- The instance encoded by a string, if any (`Inst.encode` is injective). -/
noncomputable def decodeInst (b : Bits) : Option Inst :=
  if h : ∃ u : Inst, u.encode = b then some (Classical.choose h) else none

/-- The parameters of the construction on `u`: `T = t(X)`, `d = ⌈log₂ k⌉`, `L = lev(λ, T, d)`. -/
def cpT (F : QMAFamily) (u : Inst) : ℕ := batchCost F u

/-- The coin layout of `M1` on `u`: the offsets of the base key, the `d + 1` FHE keys, the
encryption tapes of `ct_ℓ` and `ct_r` (one tape per encrypted bit, bounded by the largest secret
key and base tape the generators can output), `SC`, `IB`, `hk_C`, `hk_X`, `hk_y` and `vk`, and the
total. -/
noncomputable def cpLayout (P : CPPrims) (I : CPImpl) (F : QMAFamily) (lam : ℕ) (u : Inst) : List ℕ :=
  let T := cpT F u
  let d := clog2 u.k
  let L := I.lev lam T d
  let gE := P.fhe.genCoins lam L
  let eC := P.fhe.encCoins lam L
  let skM := maxLen gE fun r => (P.fhe.gen lam L r).2
  let rM := maxLen (P.base.genCoins lam T) fun r => (P.base.gen lam T r).2
  let sizes := [P.base.genCoins lam T, (d + 1) * gE, d * (skM * eC), rM * eC,
    P.sc.setupCoins lam u.k (I.mmu lam T), P.ib.setupCoins lam u.k (I.bc lam T u.k u.s) (I.mc lam T u.k u.s),
    merkleCoins P.mt lam (u.s + 1) (recLen u.k u.s), merkleCoins P.mt lam u.k (xLen u.k T),
    merkleCoins P.mt lam u.k 1, P.kil.setupCoins lam]
  (List.range (sizes.length + 1)).map fun j => (sizes.take j).sum

/-- The first message `M1`, its private state and the instance data, from the coins `r`: the
packed `M1`, and the verifier state `pack [u, M1, SK₀, (SK_ℓ lengths)]`. -/
noncomputable def cpFirst (P : CPPrims) (I : CPImpl) (F : QMAFamily) (lam : ℕ) (u : Inst) (r : Bits) :
    Bits × Bits :=
  let T := cpT F u
  let d := clog2 u.k
  let L := I.lev lam T d
  let gE := P.fhe.genCoins lam L
  let eC := P.fhe.encCoins lam L
  let skM := maxLen gE fun r => (P.fhe.gen lam L r).2
  let o := cpLayout P I F lam u
  let pr := P.base.gen lam T (slice r (o.getD 0 0) (P.base.genCoins lam T))
  let keys := (List.range (d + 1)).map fun l => P.fhe.gen lam L (slice r (o.getD 1 0 + l * gE) gE)
  let pks := keys.map Prod.fst
  let cts := (List.range d).map fun l =>
    encBits P.fhe (pks.getD l []) (keys.getD (l + 1) ([], [])).2 r (o.getD 2 0 + l * (skM * eC)) eC
  let ctr := encBits P.fhe (pks.getD d []) pr.2 r (o.getD 3 0) eC
  let hk := (P.sc.setup lam u.k (I.mmu lam T) 1 (slice r (o.getD 4 0) (P.sc.setupCoins lam u.k (I.mmu lam T)))).1
  let crs := (P.ib.setup lam u.k (I.bc lam T u.k u.s) (I.mc lam T u.k u.s) 1
    (slice r (o.getD 5 0) (P.ib.setupCoins lam u.k (I.bc lam T u.k u.s) (I.mc lam T u.k u.s)))).1
  let hkC := merkleGen P.mt lam (u.s + 1) (recLen u.k u.s) (slice r (o.getD 6 0) (merkleCoins P.mt lam (u.s + 1) (recLen u.k u.s)))
  let hkX := merkleGen P.mt lam u.k (xLen u.k T) (slice r (o.getD 7 0) (merkleCoins P.mt lam u.k (xLen u.k T)))
  let hky := merkleGen P.mt lam u.k 1 (slice r (o.getD 8 0) (merkleCoins P.mt lam u.k 1))
  let vk := P.kil.setup lam (slice r (o.getD 9 0) (P.kil.setupCoins lam))
  let hC := merkleCommit P.mt (u.s + 1) (recLen u.k u.s) hkC (policyRecords u.C)
  let hX := merkleCommit P.mt u.k (xLen u.k T) hkX (List.ofFn fun i : Fin u.k => xBlock u.k T (i + 1) (u.X i))
  let m1 := pack [pr.1, hk, crs, pack pks, pack (cts.map pack), pack ctr, hkC, hC, hkX, hX, hky, vk]
  (m1, pack [u.encode, m1, (keys.getD 0 ([], [])).2])

/-- The authorization instance `u = (hk_C, hk_y, h_C, h_y, k, s)`. -/
def authInst (k s : ℕ) (hkC hky hC hy : Bits) : Bits := pack [hkC, hky, hC, hy, binNat k, binNat s]

/-- The expected length of `h_y`: the root digest length of the selection tree. -/
def hyLen (H : HashFamily) (lam k : ℕ) : ℕ := (merkleBitHash H).digestLen lam k

/-- The number of `V₂` coins needed on `u` for setup coins `r`: the base challenge and the Kilian
seed for the authorization instance with an `h_y` of the expected length. -/
noncomputable def cpNeed2 (P : CPPrims) (I : CPImpl) (F : QMAFamily) (lam : ℕ) (u : Inst) (r : Bits) : ℕ :=
  let m1 := unpack (cpFirst P I F lam u r).1
  P.base.chalLen lam (cpT F u) +
    P.kil.pcp.seedLen lam (authInst u.k u.s (m1.getD 6 []) (m1.getD 10 []) (m1.getD 7 [])
      (zeros (hyLen P.mt lam u.k))).length

/-- The verifier of the §5.1 construction (p.36–37) as an `Arg4`, with the honest-prover fields
`hon` supplied separately (soundness does not depend on them). `Pre` records the statement and the
setup coins; `V₁` sends `M1`; `V₂` sends `M3 = (c, ξ)`, fresh uniform strings; `Dec` accepts
outright when `C(0) = 1` (the dummy-message rule, p.34) and otherwise checks the formats (the
length of `h_y`, and `|α_µ|` at most the fixed bound `aLen`) and
`Σ.Verify(vk, u, β, ξ, a_Σ) ∧ IB.Verify(crs, C_θ, π) ∧ D_{SK₀}(q)`. An unparsable statement is
rejected. -/
noncomputable def circuitPolicyArg (P : CPPrims) (I : CPImpl) (F : QMAFamily)
    (hon : (ℕ → ℕ → ℕ) × (ℕ → Bits → Bits → Core) × (ℕ → Bits → Bits → ℕ → Bits → Bits) ×
      (ℕ → Bits → Bits → ℕ → Bits → Bits)) : Arg4 where
  coins0 := fun lam m => sSup {n | ∃ u : Inst, u.size = m ∧ n = (cpLayout P I F lam u).getLastD 0}
  coins1 := fun _ _ => 0
  coins2 := fun lam m => sSup {n | ∃ u : Inst, u.size = m ∧ ∃ r : Bits, n = cpNeed2 P I F lam u r}
  pre := fun _ x r => pack [x, r]
  v1 := fun lam v0 _ =>
    match decodeInst ((unpack v0).getD 0 []) with
    | none => ([], [])
    | some u => cpFirst P I F lam u ((unpack v0).getD 1 [])
  v2 := fun lam v1 a1 r =>
    let st := unpack v1
    match decodeInst (st.getD 0 []) with
    | none => ([], [])
    | some u =>
      let m1 := unpack (st.getD 1 [])
      let a := unpack a1
      let nc := P.base.chalLen lam (cpT F u)
      let ua := authInst u.k u.s (m1.getD 6 []) (m1.getD 10 []) (m1.getD 7 []) (a.getD 1 [])
      let c := r.take nc
      let ξ := (r.drop nc).take (P.kil.pcp.seedLen lam ua.length)
      (pack [c, ξ], pack [v1, a1, c, ξ])
  dec := fun lam v2 a2 =>
    let st := unpack v2
    let st1 := unpack (st.getD 0 [])
    match decodeInst (st1.getD 0 []) with
    | none => false
    | some u =>
      if u.C.eval (fun _ => false) = true then true else
      let T := cpT F u
      let m1 := unpack (st1.getD 1 [])
      let sk0 := st1.getD 2 []
      let a := unpack (st.getD 1 [])
      let αμ := a.getD 0 []
      let hy := a.getD 1 []
      let β := a.getD 2 []
      let c := st.getD 2 []
      let ξ := st.getD 3 []
      let fin := unpack a2
      let q := fin.getD 0 []
      let π := fin.getD 1 []
      let aS := fin.getD 2 []
      let pks := unpack (m1.getD 3 [])
      let cts := (unpack (m1.getD 4 [])).map unpack
      let ctr := unpack (m1.getD 5 [])
      let θ := theta u.k T u.s (m1.getD 1 []) pks cts ctr (m1.getD 8 []) (m1.getD 9 []) (m1.getD 10 []) hy αμ c q
      let ua := authInst u.k u.s (m1.getD 6 []) (m1.getD 10 []) (m1.getD 7 []) hy
      decide (hy.length = hyLen P.mt lam u.k) && decide (αμ.length ≤ I.aLen lam T u.k) &&
        P.kil.verify lam (m1.getD 11 []) ua β ξ aS &&
        P.ib.verify (m1.getD 2 []) (I.selCirc lam θ) π && fheD P.fhe sk0 q
  copies := hon.1
  core := hon.2.1
  toCore := hon.2.2.1
  toVerifier := hon.2.2.2

/-- The requirements of §5.1 and §4 (p.27, pp.34–36) on the implementation choices, for the
primitives `P` and the verification family `F`:

1. `vCirc` computes `r ↦ V(x, r, µ, c, z)` on `n` inputs, `gCirc a b` computes
   `SK ↦ D_SK(a) ∧ D_SK(b)`, `oneCirc` computes the constant one, and, for every `θ` the verifier
   can form (the fields of a genuine `M1` on an instance `u`, an `h_y` of the expected length, an
   `α_µ` within the fixed bound `aLen`, a challenge `c` of the prescribed length and any `q`),
   `selCirc λ θ` computes `(i, w) ↦ R_sel(θ, i; w)` on `[k] × {0,1}^{m_C}` with at most `B_C` gates
   ("`C_θ` itself is selected after setup", p.34);
2. every circuit evaluated under a key of level `L = lev(λ, T, d)` has depth at most `L` on the
   inputs it is evaluated on: `vCirc` for an entry with `t_L(x) ≤ T`, a challenge of the prescribed
   length and the length of a base tape of `Gen(1^λ, T)`; `gCirc` for the length of a secret key of
   `FHE.Gen(1^λ, 1^L)`; `oneCirc` everywhere;
3. the compilers are polynomial time, and `lev`, `B_C`, `m_C`, `m_µ`, `aLen` and the `R_auth`
   bounds are polynomially bounded.

These are the paper's "compatible depth bounds" and "fixed bounds `B_C, m_C = poly(H)`". -/
def CPImpl.Valid (I : CPImpl) (P : CPPrims) (F : QMAFamily) : Prop :=
  (∀ lam T x μ c z n, Computes (I.vCirc lam T x μ c z n) n fun r => P.base.verdict lam x r μ c z) ∧
  (∀ a b n, Computes (I.gCirc a b n) n fun sk => fheD P.fhe sk a && fheD P.fhe sk b) ∧
  (∀ n, Computes (I.oneCirc n) n fun _ => true) ∧
  (∀ lam (u : Inst) (r hy αμ c q : Bits), (cpLayout P I F lam u).getLastD 0 ≤ r.length →
    hy.length = hyLen P.mt lam u.k → αμ.length ≤ I.aLen lam (cpT F u) u.k →
    c.length = P.base.chalLen lam (cpT F u) →
    let T := cpT F u
    let m1 := unpack (cpFirst P I F lam u r).1
    let θ := theta u.k T u.s (m1.getD 1 []) (unpack (m1.getD 3 [])) ((unpack (m1.getD 4 [])).map unpack)
      (unpack (m1.getD 5 [])) (m1.getD 8 []) (m1.getD 9 []) (m1.getD 10 []) hy αμ c q
    IndexCircuitOK u.k (I.bc lam T u.k u.s) (I.mc lam T u.k u.s) (I.selCirc lam θ) ∧
      ∀ i w, 1 ≤ i → i ≤ u.k → w.length = I.mc lam T u.k u.s →
        indexEval u.k (I.selCirc lam θ) i w = rsel P I lam θ i w) ∧
  (∀ lam T d (x : Str) μ c z (rb : Bits), localCost F x ≤ T → c.length = P.base.chalLen lam T →
    rb.length = P.base.genCoins lam T →
    (I.vCirc lam T x μ c z (P.base.gen lam T rb).2.length).depth ≤ I.lev lam T d) ∧
  (∀ lam T d a b (r : Bits), r.length = P.fhe.genCoins lam (I.lev lam T d) →
    (I.gCirc a b (P.fhe.gen lam (I.lev lam T d) r).2.length).depth ≤ I.lev lam T d) ∧
  (∀ lam T d n, (I.oneCirc n).depth ≤ I.lev lam T d) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam T x μ c z n,
    g (pack [unary lam, unary T, x, μ, c, z, unary n]) = (I.vCirc lam T x μ c z n).encode) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ a b n, g (pack [a, b, unary n]) = (I.gCirc a b n).encode) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ n, g (unary n) = (I.oneCirc n).encode) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam θ, g (pack [unary lam, θ]) = (I.selCirc lam θ).encode) ∧
  (∃ p : MvPolynomial (Fin 4) ℕ, ∀ lam T k s,
    I.lev lam T (clog2 k) ≤ eval4 p lam T (clog2 k) 0 ∧ I.bc lam T k s ≤ eval4 p lam T (clog2 (k + 1)) (clog2 (s + 1)) ∧
      I.mc lam T k s ≤ eval4 p lam T (clog2 (k + 1)) (clog2 (s + 1)) ∧ I.mmu lam T ≤ eval4 p lam T 0 0 ∧
      I.aLen lam T k ≤ eval4 p lam T (clog2 (k + 1)) 0) ∧
  PolyBound I.authIn ∧ PolyBound I.authWit

end Supplement

end FourMsgQMA


