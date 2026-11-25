-- Prove2me | Definitions.Def_DetDLP_W3_Separator
-- name    : DetDLP_W3_Separator
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:51:44.868903+00:00
-- url     : https://prove2.me/theorems/d34f31d9-6222-40e8-a98c-0b82a9a3c574
-- title:
--   Stage II: native-address lookup-separator BTN interface
-- statement:
--   A native-address lookup-separator interface for the elliptic and prime-field branches. It records tuple validity, positive-filter integer mass, exact truncated Newton-binomial readout without modular wraparound, the lookup terminal geometry required by terminal-preserving contraction, and uniform deterministic graph-construction and local-entry-evaluation machines. The branch query includes its actual hash seed, encoded factor blocks, public data, labels and prefix bits; address assignments therefore cannot be supplied independently of the native hash encoding.
-- source:
--   Deterministic Discrete Logarithms, §2.3 and §4.2–4.3, especially (4.3)–(4.5) and the proof of Theorem 1.1, pp. 14–16; referee revision R2.

import Definitions.Def_DetDLP_W3_CosetTrace
import Definitions.Def_DetDLP_FactorBase
import Definitions.Def_DetDLP_TerminalBTN

set_option autoImplicit false
namespace DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

structure w3_Query where
  V : Type
  [group : AddCommGroup V]
  M : ℕ
  nz : NeZero M
  b : ℕ
  m : ℕ
  k : ℕ
  FB : IndexedFactorBase V m
  P : V
  y : w3_Label M FB.totalCoords
  code : FB.BlockTuple → FB.BlockTuple → List Bool
  pre : List Bool
  input : List Bool
  -- Indexed addresses are public native hash addresses, not ranks in an arbitrary set.
  addr : (i : Fin m) → Fin (FB.blocks i).length → ℕ
attribute [instance] w3_Query.group w3_Query.nz

def w3_bits (b x : ℕ) : List Bool := List.ofFn fun i : Fin b => x.testBit i.val

def w3_tupleWord {G : Type} {m : ℕ} (FB : IndexedFactorBase G m) (word : G → List Bool)
    (X Y : FB.BlockTuple) : List Bool :=
  ([X,Y] : List FB.BlockTuple).flatMap fun T => (List.finRange m).flatMap fun i =>
    (List.finRange 2).flatMap fun s => word ((FB.blocks i).get (T i s))

noncomputable def w3_fpFB {p m : ℕ} (F : Fin m → List (ZMod p)ˣ) : IndexedFactorBase (Additive (ZMod p)ˣ) m :=
  ⟨fun i => (F i).map Additive.ofMul⟩

noncomputable def w3_ecQueries (q : w3_Query) : Prop := ∃ (p : ℕ) (_hp : Fact p.Prime),
  ∃ (E : WeierstrassCurve (ZMod p)) (_hE : E.IsElliptic),
  E.a₁ = 0 ∧ E.a₂ = 0 ∧ E.a₃ = 0 ∧ 67 < p ∧
  letI := ecPointFintype E
  let M := Fintype.card E.toAffine.Point
  let b := bitLen p
  let m := blockCount b
  let T := hashThreshold p (M-1) m M
  let k := Nat.clog 2 (2*T)
  64 ≤ M ∧ ∃ (hNZ : 0 < M) (hM : 4096*m ≤ M-1) (seed : ECSeed p m) (F : Fin m → List E.toAffine.Point),
    (∀ i, (F i).Nodup ∧ (F i).toFinset = ecFactorBlock E T seed i) ∧
    ∃ (P : E.toAffine.Point) (y : w3_Label M (IndexedFactorBase.mk F).totalCoords) (pre : List Bool),
      let FB : IndexedFactorBase E.toAffine.Point m := ⟨F⟩
      let input := Encoding.encodeList id [encodeCurveInput p E, encodeNatListBin (pointCoords P),
        encodeNatListBin [M,T], encodeNatListBin ((List.finRange m).flatMap fun i =>
          [((seed i false).1.val+1),(seed i false).2.val,((seed i true).1.val+1),(seed i true).2.val]),
        encodeECFactorBlocks F, encodeNatListBin (List.ofFn fun j => (y j).val), pre]
      q = { V := E.toAffine.Point, M := M, nz := ⟨Nat.ne_of_gt hNZ⟩, b := b, m := m, k := k, FB := FB, P := P,
            y := y, code := w3_tupleWord FB (fun A => (pointCoords A).flatMap (w3_bits b)),
            pre := pre, input := input, addr := fun i r => match (F i).get r with
              | .zero => 2*T
              | .some x z _ => let s := decide (z.val % 2 = 1); let ab := seed i s
                               ((ab.1.val+1)*x.val+ab.2.val)%p + (if s then T else 0) }

noncomputable def w3_fpQueries (q : w3_Query) : Prop := ∃ (p : ℕ) (_hp : Fact p.Prime),
  let M := p-1
  let b := bitLen p
  let m := blockCount b
  let T := hashThreshold p M m M
  let k := Nat.clog 2 (2*T)
  67 < p ∧ ∃ (hNZ : 0 < M) (hM : 64 ≤ M) (_hM' : 4096*m ≤ M) (seed : FpSeed p m) (F : Fin m → List (ZMod p)ˣ),
    (∀ i, (F i).Nodup ∧ (F i).toFinset = fpFactorBlock T seed i) ∧
    ∃ (P : (ZMod p)ˣ) (y : w3_Label M (w3_fpFB F).totalCoords) (pre : List Bool),
      let FB := w3_fpFB F
      let input := Encoding.encodeList id [encodeNatListBin [p,(P : ZMod p).val,M,T],
        encodeNatListBin ((List.finRange m).flatMap fun i => [((seed i).1.val+1),(seed i).2.val]),
        encodeFpFactorBlocks F, encodeNatListBin (List.ofFn fun j => (y j).val), pre]
      q = { V := Additive (ZMod p)ˣ, M := M, nz := ⟨Nat.ne_of_gt hNZ⟩, b := b, m := m, k := k, FB := FB, P := Additive.ofMul P,
            y := y, code := w3_tupleWord FB (fun A => w3_bits b ((A.toMul : (ZMod p)ˣ) : ZMod p).val),
            pre := pre, input := input, addr := fun i r =>
              (((seed i).1.val+1)*(((FB.blocks i).get r).toMul : ZMod p).val + (seed i).2.val)%p }

def w3_valid (q : w3_Query) (t : q.FB.BlockTuple × q.FB.BlockTuple) : Prop :=
  q.FB.tupleVal t.2 = q.FB.tupleVal t.1 + q.P ∧ q.pre <+: q.code t.1 t.2

noncomputable def w3_mass (q : w3_Query) : ℤ := by
  classical
  exact ∑ t : q.FB.BlockTuple × q.FB.BlockTuple,
    if w3_valid q t then (filterPoly (2*q.m) q.M).eval (w3_delta q.FB q.M q.y t.1 t.2) else 0

def w3_precision (q : w3_Query) : ℕ :=
  2 + 4*q.m*q.k + dFilt (2*q.m) * Nat.clog 2 (2*(2*q.m)*q.M+2)

def w3_len (q : w3_Query) := dFilt (2*q.m) + 1

noncomputable def w3_binWord (q : w3_Query) (z : ℤ) : TruncPoly (w3_precision q) (w3_len q) :=
  Ideal.Quotient.mk _ (∑ j : Fin (w3_len q), Polynomial.monomial j.val
    ((intBinom z j.val : ℤ) : ZMod (2 ^ w3_precision q)))

noncomputable def w3_pairWeight (q : w3_Query) (t : q.FB.BlockTuple × q.FB.BlockTuple) : TruncPoly (w3_precision q) (w3_len q) :=
  ∏ i : Fin q.m, ∏ s : Fin 2,
    w3_binWord q (-((q.y (q.FB.coordOf i (t.1 i s))).val : ℤ)) * w3_binWord q ((q.y (q.FB.coordOf i (t.2 i s))).val : ℤ)

structure w3_Net (q : w3_Query) (C : ℕ) where
  G : BipartiteMultigraph
  S : ℕ
  desc : List Bool
  T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly (w3_precision q) (w3_len q)
  spec : LookupSeparatorSpec G q.m q.k S (C * Nat.ceil ((q.b : ℝ)^((3 : ℝ)/4)))
  shape : 2 ≤ q.b ∧ 1 ≤ q.m ∧ 1 ≤ q.k ∧ blockCount q.b ≤ C*q.m ∧ q.m ≤ C*blockCount q.b ∧
    S ≤ C*q.m*q.b ∧ 4*q.m*q.k ≤ C*q.b ∧ q.b ≤ C*(4*q.m*q.k) ∧
    1 ≤ w3_precision q ∧ w3_precision q ≤ S ∧ 1 ≤ w3_len q ∧ w3_len q ≤ C*q.m
  coreOK : (Fin G.nE → Bool) → Prop
  decode : {a // coreOK a} ≃ {t // w3_valid q t}
  live_weight : ∀ a : {a // coreOK a}, (∏ v, T v (fun j => a.val ((G.ports v).get j))) = w3_pairWeight q (decode a).val
  dead_weight : ∀ a : Fin G.nE → Bool, ¬coreOK a → (∏ v, T v (fun j => a ((G.ports v).get j))) = 0
  nowrap : w3_mass q < (2 : ℤ)^w3_precision q
  readout : ∀ c : Fin (w3_len q) → ℕ, (∀ i, c i < 2^w3_precision q) →
    BTNContract G T = truncPolyOfCoeffs (w3_precision q) (w3_len q) c →
    ((∑ j : Fin (w3_len q), (newtonCoeff (2*q.m) q.M j.val : ZMod (2^w3_precision q)) * (c j : ZMod (2^w3_precision q))).val : ℤ) = w3_mass q

def w3_packet {q : w3_Query} {C : ℕ} (n : w3_Net q C) : List Bool :=
  encodeTerminalBTNInstance n.desc n.G q.b q.m q.k n.S (w3_precision q) (w3_len q) n.spec.lookupVerts

/-- Interface of a uniform graph builder and local polynomial entry evaluator. The input includes
    native seeds, public constants, blocks, labels and prefix but no filter answer or logarithms. -/
def w3_Separator (family : w3_Query → Prop) : Prop :=
  ∃ (C c : ℕ) (build : PrimitiveMachine) (ob : Fin build.tapeCount) (eval : PrimitiveMachine) (oe : Fin eval.tapeCount),
    0 < C ∧ 0 < c ∧ ∀ q, family q → ∃ n : w3_Net q C,
      n.G.nV ≤ (n.S+n.desc.length+1)^c ∧
      RunsWithin build ob q.input (w3_packet n) (polyBound c q.input.length) (polyBound c q.input.length) ∧
      BTNEntryEvaluable n.desc n.G (w3_precision q) (w3_len q) n.T eval oe
        (polyBound c (n.S+n.desc.length)) (polyBound c (n.S+n.desc.length))

end DetDLP


