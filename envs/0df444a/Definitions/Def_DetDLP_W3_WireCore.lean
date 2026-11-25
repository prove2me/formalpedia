-- Prove2me | Definitions.Def_DetDLP_W3_WireCore
-- name    : DetDLP_W3_WireCore
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T21:30:11.310141+00:00
-- url     : https://prove2.me/theorems/4cfb34e2-6746-4fd7-9717-873f459381ce
-- title:
--   Raw Stage II arithmetic core and polynomial packet programs
-- statement:
--   Interface preceding M5 equality subdivision. A raw core has weighted ordered ports, Boolean validity checks, bijective decoding by legal tuple pairs and explicit pre-subdivision wire and degree budgets. A uniform family gives two total polynomial-time functions: one emits the canonical packet and one encodes each ring-valued local entry. The returned packet is tied to the same numerical graph and designated addresses used for its semantic proof.
-- source:
--   Deterministic Discrete Logarithms §4.2, dedicated address wiring, totalized lookups, and core subdivision (steps 1–3), pp. 14–15.

import Definitions.Def_DetDLP_W3_Separator
import Definitions.Def_DetDLP_W4_M5Subdivision
import Definitions.Def_ToTuring_PolyT

set_option autoImplicit false
namespace DetDLP
open w4_M5Network

/-- A family of local ring tensors compiled by M5 equality subdivision. -/
def w3_liftTensor {R : Type*} [Zero R] [One R] (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → R) :
    (v : Fin G.subdivision.nV) → (Fin (G.subdivision.deg v) → Bool) → R :=
  Fin.addCases (fun v a => T v (fun j => a (G.oldPort v j)))
    (fun e a => if a (G.equalityLeftPort e) = a (G.equalityRightPort e) then 1 else 0)

/-- A separator prior to subdivision. The arithmetic circuit and address tensors reside here.
    Complexity for the input decoder and vertex entries is supplied by a separate uniform family. -/
structure w3_WireCore (q : w3_Query) (C : ℕ) where
  G : WireGraph
  L : Finset (Fin G.nV)
  S : ℕ
  desc : List Bool
  T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly (w3_precision q) (w3_len q)
  checks : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool
  decode : {a // G.Satisfies checks a} ≃ {t // w3_valid q t}
  live : ∀ a : {a // G.Satisfies checks a}, (∏ v, T v (fun j => a.val ((G.ports v).get j))) = w3_pairWeight q (decode a).val
  dead : ∀ a : Fin G.nE → Bool, ¬G.Satisfies checks a → (∏ v, T v (fun j => a ((G.ports v).get j))) = 0
  lookup_count : L.card = 4*q.m
  lookup_degrees : ∀ v ∈ L, G.deg v = q.k
  orientation : ∀ e, (G.endpoints e).2 ∉ L
  core_edges : 2*G.nE ≤ S
  core_degrees : ∀ v ∉ L, G.deg v ≤ C * Nat.ceil ((q.b:ℝ)^((3:ℝ)/4))
  equality_degree : 2 ≤ C * Nat.ceil ((q.b:ℝ)^((3:ℝ)/4))
  shape : 2 ≤ q.b ∧ 1 ≤ q.m ∧ 1 ≤ q.k ∧ blockCount q.b ≤ C*q.m ∧ q.m ≤ C*blockCount q.b ∧
    S ≤ C*q.m*q.b ∧ 4*q.m*q.k ≤ C*q.b ∧ q.b ≤ C*(4*q.m*q.k) ∧
    1 ≤ w3_precision q ∧ w3_precision q ≤ S ∧ 1 ≤ w3_len q ∧ w3_len q ≤ C*q.m

def w3_wirePacket {q : w3_Query} {C : ℕ} (W : w3_WireCore q C) : List Bool :=
  encodeTerminalBTNInstance W.desc W.G.subdivision q.b q.m q.k W.S (w3_precision q) (w3_len q) (W.L.image W.G.oldVertex)

/-- Total list functions computing the raw arithmetic network packet and its tensor entries.
    The polynomial query-length bound converts PolyT's word-size budget to Theorem 4.3's local budget. -/
def w3_polyWireFamily (family : w3_Query → Prop) : Prop :=
  ∃ (C c : ℕ) (build entry : List Bool → List Bool), 0 < C ∧ 0 < c ∧ Groundwork.PolyT build ∧ Groundwork.PolyT entry ∧
    ∀ q, family q → ∃ W : w3_WireCore q C, build q.input = w3_wirePacket W ∧
      W.G.subdivision.nV ≤ (W.S+W.desc.length+1)^c ∧
      ∀ (v : Fin W.G.subdivision.nV) (a : Fin (W.G.subdivision.deg v) → Bool),
        let w := encodePortQuery W.desc v.val (List.ofFn a)
        w.length+1 ≤ (W.S+W.desc.length+1)^c ∧
        EncodesTruncPoly (w3_precision q) (w3_len q) (entry w) (w3_liftTensor W.G W.T v a)

end DetDLP


