-- Prove2me | Definitions.Def_DetDLP_S8J_CircuitRealizes
-- name    : DetDLP_S8J_CircuitRealizes
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:39:12.647672+00:00
-- url     : https://prove2.me/theorems/22ff2a9a-acb2-4306-9d3b-d53c20254e47
-- title:
--   Copy-cycle satisfaction decoding and BTN packet interfaces
-- statement:
--   A copy-cycle layout encodes signals through occurrence bits. When the cycle wiring is connected, satisfaction decodes bijectively to logical gate assignments, with a BTN PolyT packet interface.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8J_HashGateLayout
import Definitions.Def_DetDLP_S8H_CopyCycle
import Definitions.Def_DetDLP_S8C_WireBTN
import Definitions.Def_DetDLP_S8C_Packet

set_option autoImplicit false
namespace DetDLP.S8J.CircuitRealizes
open S8H.CopyCycle S8C Groundwork
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

structure Block where
  A : w3_FactorLayout
  t : w3_factorTest A

def empty : Block where
  A := ⟨0,0,0,Fin.elim0,Fin.elim0,Fin.elim0,fun b => Fin.elim0 b⟩
  t := fun g => Fin.elim0 g

def assemble : List Block → Block
  | [] => empty
  | b :: bs => ⟨join b.A (assemble bs).A, joinTest b.t (assemble bs).t⟩

noncomputable def hashBlock {d p : ℕ} (hd : 1 ≤ d) (a x : ℕ) (r : w3_fpHashCert d p hd) : Block := by
  classical exact ⟨_,HashGateLayout.tests hd a x r⟩

def lessBlock (d : ℕ) : Block := ⟨S8C.AddLayout.layout (d+1), S8C.AddLayout.test true⟩

theorem lessBlock_iff (d u B : ℕ) (r : w3_slotDiff d) :
    Accept (lessBlock d).A (lessBlock d).t (HashGateLayout.addBits u r.1.val B r.2) ↔ w3_slotLt d u B r :=
  HashGateLayout.addBits_iff (by omega) u r.1.val B true r.2

def smallBlock (k : ℕ) (_ : k ≤ 4) (check : (Fin k → Bool) → Bool) : Block where
  A := ⟨1,k,k,fun _ => 0,id,id,fun _ => rfl⟩
  t := fun _g a => check (fun i => a ⟨i,Subsingleton.elim _ _⟩)

/-- A cycle represents one signal exactly when successor-invariance implies constancy
    on that signal's fibre. The section excludes dangling logical signals. -/
structure Wiring (n k : ℕ) where
  next : Equiv.Perm (Fin n)
  signal : Fin n → Fin k
  rep : Fin k → Fin n
  section_eq : ∀ i, signal (rep i) = i
  next_eq : ∀ i, signal (next i) = signal i
  connected : ∀ a : Fin n → Bool, (∀ i, a i = a (next i)) → ∀ i, a (rep (signal i)) = a i

variable {k : ℕ} (b : Block) (W : Wiring b.A.ne k)

def circuit := S8H.CopyCycle.layout b.A.gate W.next
def test : w3_factorTest (circuit b W) := S8H.CopyCycle.checks b.A.gate W.next b.t

abbrev Logical := {a : Fin k → Bool // ∀ g, b.t g (fun e => a (W.signal e.val)) = true}

def decode : {x // (w3_factorGraph (circuit b W)).Satisfies (w3_factorChecks _ (test b W)) x} ≃ Logical b W :=
  (w3_factorEquiv _ _).trans {
    toFun := fun x => ⟨fun i => x.val (W.rep i),by
      obtain ⟨ht,hw⟩ := (checks_iff _ _ b.t x.val).mp x.property
      simpa only [W.connected x.val hw] using ht⟩
    invFun := fun a => ⟨fun i => a.val (W.signal i),(checks_iff _ _ b.t _).mpr
      ⟨a.property,fun i => congrArg a.val (W.next_eq i).symm⟩⟩
    left_inv := fun x => Subtype.ext (funext (W.connected x.val ((checks_iff _ _ b.t _).mp x.property).2))
    right_inv := fun a => Subtype.ext (funext fun i => congrArg a.val (W.section_eq i)) }

theorem degree (i : Fin b.A.ne) : (w3_factorGraph (circuit b W)).deg (Fin.natAdd (circuit b W).ng i) ≤ 6 :=
  (bitDegree _ _ _).le.trans (by decide)

abbrev G := w3_factorGraph (circuit b W)
abbrev T := w3_factorChecks (circuit b W) (test b W)

theorem realizes (make port : List Bool → List Bool) (L s base : ℕ) (w : List Bool)
    {A : Type} [Fintype A] (sem : Logical b W ≃ A) (hs : 2 ≤ s) (hb : base ≤ s)
    (he : 2*(G b W).nE < s) (hv : (G b W).nV+(G b W).nE ≤ s^L)
    (hd : max (Finset.univ.sup (G b W).deg) 2 ≤ Nat.ceil ((s:ℝ)^((9:ℝ)/10)))
    (h1 : s+w.length ≤ L*blockCount base*base) (h2 : s+w.length ≤ L*(base+1)^L)
    (hm : make w = encodeBTNInstance w (G b W).subdivision s s 1)
    (hp : ∀ (v : Fin (G b W).subdivision.nV) (a : Fin ((G b W).subdivision.deg v) → Bool),
      let z := encodePortQuery w v.val (List.ofFn a)
      z.length ≤ L*(s+w.length+1)^L ∧ port z = encodeNatListBin [if (G b W).subdivisionTensor (T b W) v a then 1 else 0]) :
    Realizes make port L w base (Fintype.card A) :=
  wireRealizes make port L s base w _ _ ((decode b W).trans sem) hs hb he hv hd h1 h2 hm hp

/-- Numeric descriptions are indexed by the actual input word, including on malformed inputs. -/
structure Packets where
  nv : PacketWord → ℕ
  ne : PacketWord → ℕ
  scale : PacketWord → ℕ
  side : PacketWord → ℕ → Bool
  src : PacketWord → ℕ → ℕ
  dst : PacketWord → ℕ → ℕ
  check : PacketWord × ℕ × PacketWord → Bool
  nv_poly : PolyT nv
  ne_poly : PolyT ne
  scale_poly : PolyT scale
  nv_unary : Unary nv
  ne_unary : Unary ne
  side_poly : PolyT fun z : PacketWord × ℕ => side z.1 z.2
  src_poly : PolyT fun z : PacketWord × ℕ => src z.1 z.2
  dst_poly : PolyT fun z : PacketWord × ℕ => dst z.1 z.2
  check_poly : PolyT check

def Packets.make (P : Packets) (w : PacketWord) := outerPacket w
  (graphPacket (P.nv w) (P.ne w) (P.side w) (P.src w) (P.dst w)) (P.scale w)

theorem Packets.poly (P : Packets) : PolyT P.make ∧ PolyT (portPacket P.check) :=
  ⟨outerPacket_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f
    (graphPacket_poly P.nv_poly P.ne_poly P.nv_unary P.ne_unary P.side_poly P.src_poly P.dst_poly)
    P.scale_poly, portPacket_poly P.check_poly⟩

theorem packetsRealize (P : Packets) (L base : ℕ) (w : PacketWord)
    {A : Type} [Fintype A] (sem : Logical b W ≃ A) (hs : 2 ≤ P.scale w) (hb : base ≤ P.scale w)
    (he : 2*(G b W).nE < P.scale w) (hv : (G b W).nV+(G b W).nE ≤ (P.scale w)^L)
    (hd : max (Finset.univ.sup (G b W).deg) 2 ≤ Nat.ceil ((P.scale w:ℝ)^((9:ℝ)/10)))
    (h1 : P.scale w+w.length ≤ L*blockCount base*base) (h2 : P.scale w+w.length ≤ L*(base+1)^L)
    (hnv : P.nv w = (G b W).subdivision.nV) (hne : P.ne w = (G b W).subdivision.nE)
    (hside : ∀ i : Fin (G b W).subdivision.nV, P.side w i.val = (G b W).subdivision.side i)
    (hsrc : ∀ i : Fin (G b W).subdivision.nE, P.src w i.val = ((G b W).subdivision.endpoints i).1.val)
    (hdst : ∀ i : Fin (G b W).subdivision.nE, P.dst w i.val = ((G b W).subdivision.endpoints i).2.val)
    (hp : ∀ (v : Fin (G b W).subdivision.nV) (a : Fin ((G b W).subdivision.deg v) → Bool),
      (encodePortQuery w v.val (List.ofFn a)).length ≤ L*(P.scale w+w.length+1)^L ∧
      P.check (w,v.val,List.ofFn a) = (G b W).subdivisionTensor (T b W) v a) :
    Realizes P.make (portPacket P.check) L w base (Fintype.card A) := by
  apply realizes b W _ _ L (P.scale w) base w sem hs hb he hv hd h1 h2
  · unfold Packets.make; rw [hnv,hne,graphPacket_eq _ _ _ _ hside hsrc hdst,outerPacket_eq]
  · intro v a; exact ⟨(hp v a).1,by rw [portPacket_eq,(hp v a).2]⟩

end DetDLP.S8J.CircuitRealizes


