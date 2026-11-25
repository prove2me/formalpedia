-- Prove2me | Definitions.Def_DetDLP_D4StoppedNode
-- name    : DetDLP_D4StoppedNode
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:25:51.868249+00:00
-- url     : https://prove2.me/theorems/cb965063-2b60-4b93-80df-a9198d5b6d43
-- title:
--   Descriptors and pinned tensors of stopped source vertices
-- statement:
--   A lookup record names an original vertex. A stopped record stores the residual graph and a table whose original-vertex rows select each port from either the pinned open assignment or the internal assignment. Packet rows carry a descriptor; their creation precision and tensor are semantic data, not serialized tables. The value represented by a stopped record is the canonical coordinate lift of the contraction of its pinned residual graph.
-- source:
--   Concrete source interface for DetDLP.AppendixD4 and DetDLP.D3Stopped, worker specification M14-StoppedSrc, items 1–3.

import Definitions.Def_DetDLP_D3StoppedRaw

set_option autoImplicit false
namespace DetDLP.D4StoppedNode
open AppendixD4 ResidualScalarOracle Polynomial OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
noncomputable section

def lookupDesc (origDesc : Bits) (origV κ l q : ℕ) : Bits :=
  false :: Encoding.encodeList id [origDesc, countWord origV, countWord κ, countWord l, countWord q]

def liftBase (f : ℤ[X]) (l q : ℕ) (a : Fin l → ℕ) : B f l q :=
  AdjoinRoot.mk _ (∑ j : Fin l, monomial j.val (AdjoinRoot.of _ (a j : ZMod (2^q))))

/-- Emit one block of width κ per original coefficient, including the empty block when κ = 0. -/
def pad (κ : ℕ) (a : List ℕ) : List ℕ :=
  a.flatMap fun n => match κ with | 0 => [] | k+1 => n :: List.replicate k 0

inductive VertexSpec where
  | orig (origV : ℕ) (perm : List (Bool × ℕ))
  | pkt (pktDesc : Bits)

def VertexSpec.bits : VertexSpec → Bits
  | .orig v perm => false :: Encoding.encodeList id [countWord v,
      Encoding.encodeList (fun r => r.1 :: countWord r.2) perm]
  | .pkt d => true :: d

def routedBits (perm : List (Bool × ℕ)) (alpha beta : Bits) : Bits :=
  perm.map fun r => (if r.1 then alpha else beta)[r.2]?.getD false

def stoppedDesc (origDesc : Bits) (S l P d₀ : ℕ) (f : ℤ[X]) (G : Graph) (vTableBits : Bits) : Bits :=
  true :: Encoding.encodeList id [countWord S, countWord l, countWord P, G.encode,
    D3Stopped.descOf d₀ f (Encoding.encodeList id [origDesc, vTableBits])]

/-- Semantic information about packet entries is never serialized. The descriptor is the handle
    used by the external packet machine, whose correctness is a separate run hypothesis. -/
structure Packet (f : ℤ[X]) (l P deg : ℕ) where
  creation : ℕ
  le_precision : creation ≤ P
  entry : (Fin deg → Bool) → B f l creation

/-- The original table is identified by its graph and tensor, not by an arbitrary source value.
    Each route contains exactly one entry per original port and every read is in bounds. -/
structure StoppedSpec (origG G : Graph) (f : ℤ[X]) (l P openDeg : ℕ) where
  vTable : Fin G.nV → VertexSpec
  validOrig : ∀ w v perm, vTable w = .orig v perm →
    ∃ hv : v < origG.nV, perm.length = origG.deg ⟨v,hv⟩ ∧
      ∀ r ∈ perm, r.2 < (if r.1 then openDeg else G.deg w)
  packet : ∀ w d, vTable w = .pkt d → Packet f l P (G.deg w)

variable {origG G : Graph} {f : ℤ[X]} {l P openDeg : ℕ}
variable (s : StoppedSpec origG G f l P openDeg)

def StoppedSpec.tableBits : Bits := Encoding.encodeList VertexSpec.bits (List.ofFn s.vTable)

def StoppedSpec.payload (origDesc : Bits) (α : Fin openDeg → Bool) : Bits :=
  Encoding.encodeList id [origDesc, s.tableBits, List.ofFn α]

def StoppedSpec.entry (hf : f.Monic) (A : Tensor origG (Fin l → ℕ))
    (α : Fin openDeg → Bool) : Tensor G (B f l P) := fun w β =>
  match h : s.vTable w with
  | .orig v perm =>
    let hv := (s.validOrig w v perm h).choose
    let bits := routedBits perm (List.ofFn α) (List.ofFn β)
    liftBase f l P (A ⟨v,hv⟩ (fun j => bits[j.val]?.getD false))
  | .pkt d => let p := s.packet w d h; lift hf P (p.entry β)

def StoppedSpec.value (hf : f.Monic) (A : Tensor origG (Fin l → ℕ))
    (q : ℕ) (α : Fin openDeg → Bool) : B f l q :=
  lift hf q (BTNContract G (s.entry hf A α))
end
end DetDLP.D4StoppedNode


