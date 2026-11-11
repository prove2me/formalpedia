-- Prove2me | Definitions.Def_NecklacePPAD_Main_Construction
-- name    : NecklacePPAD_Main_Construction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:08:08.883916+00:00
-- url     : https://prove2.me/theorems/886d1571-61eb-4772-8d86-8c654c5a87ea
-- title:
--   The gadget colours and the necklace of the reduction from Pure-Circuit (§4.2), and its decoding (§4.3)
-- statement:
--   Given half-sizes $(b_{\rm NOR},b_{\rm NP},b_{\rm NOT})$ and a Pure-Circuit instance $(V,G)$ (the published `PCInst`), the **gadget colours** are, gate by gate in list order: for $(\mathrm{NOR},u,v,w)$ one colour of kind NOR with input list $(u,u,v,v)$ and output $w$ with threshold 1; for the $k$-th gate $(\mathrm{PURIFY},u,v,w)$, with new auxiliary nodes $v'=(k,0)$, $w'=(k,1)$, a colour of kind NP with input list $(u,u,u)$ and outputs $v'$ (threshold 1) and $w'$ (threshold 2), a colour of kind NOT with input list $(v',v')$ and output $v$ (threshold 1), and a colour of kind NOT with input list $(w',w')$ and output $w$ (threshold 1). The nodes $V^+$ are $V$ plus the auxiliary nodes; the **host** of a node is the colour of which it is an output. A colour $d$ of kind $K$ has $s_d$ = length of its input list, $b_d=b_K$, $m_d=2b_d-s_d$.
--
--   The free choices of the page are a `Layout`: an order $d_1,\dots,d_n$ of the colours ("arbitrarily") and, for every colour $c$ and segment $i$, an order of the beads of $\Sigma^c_i$ ("in any order"), i.e. any permutation of the beads of colour $d$, one for every colour $d$ and every entry $y$ of $d$'s input list with host $c$ and $\sigma(y)=i$, where $\tau(d_r)=(r-1)\bmod 2$ and $\sigma(y)=\sigma(\kappa)$ by (1) for the host's $b,s,\tau$ and $y$'s threshold $\kappa$. The block of $c$ is $B(c)=c\,\Sigma^c_1\,c\,\Sigma^c_2\,c\cdots c\,\Sigma^c_{m_c-1}\,c$ ($m_c$ letters $c$) and the necklace is $a=B(d_1)\cdots B(d_n)$; `blocks` are the intervals these words occupy, and `sensorPos d k` is the position of the bead for the $k$-th entry of $d$'s input list.
--
--   **Decoding (§4.3):** a split $\ell$ of $a$ is complemented if $\ell(1)=1$; then $\mathrm{val}(x)=R_{h(x)}(\sigma(x))$ for $x\in V^+$ with host $h(x)$, and the assignment is $x=\mathrm{val}|_V$. `canonLayout` is the canonical choice (colours in gate order, $\Sigma^c_i$ in colour-then-entry order) used by the polynomial-time maps.
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Necklace Splitting with Ten Beads per Colour is PPAD-Hard (STOC 2027 submission, sha256 d5b5449c…41ac), §4.2, p. 7 (PDF 9), and §4.3, p. 7 (PDF 9)

import Mathlib
import Definitions.Def_NecklacePPAD_Main_Reading

set_option autoImplicit false

namespace NecklacePPAD.Main

open LpBallVI.Affine

/-- The three kinds of gadget colour of §4.2 (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission,
sha256 d5b5449c…, p. 7 (PDF 9)): NOR, NP and NOT. -/
inductive Kind where
  | nor
  | np
  | not
  deriving DecidableEq

/-- The half-sizes `(b_NOR, b_NP, b_NOT)` of §4.2, fixed constants of the construction. -/
structure HalfSizes where
  bNOR : ℕ
  bNP : ℕ
  bNOT : ℕ

/-- The half-size `b_K` of kind `K`. -/
def HalfSizes.get (H : HalfSizes) : Kind → ℕ
  | .nor => H.bNOR
  | .np => H.bNP
  | .not => H.bNOT

/-- The node set `V⁺ ⊇ V` of §4.2: a node `inl x` of the Pure-Circuit instance, or the auxiliary
node `inr (k, false)` (`v′`) or `inr (k, true)` (`w′`) of the `k`-th gate (0-based position in the
gate list); only PURIFY gates use their auxiliary nodes. -/
abbrev Node (I : PCInst) : Type := Fin I.n ⊕ (Fin I.gates.length × Bool)

/-- A gadget colour: its kind, its input list (nodes with repetitions) and its output nodes with
their thresholds. -/
structure Gadget (I : PCInst) where
  kind : Kind
  inputs : List (Node I)
  outputs : List (Node I × ℕ)

/-- The gadget colours created for the `k`-th gate (§4.2, p. 7): for `(NOR, u, v, w)` one colour of
kind NOR with input list `(u, u, v, v)` and output `w` with threshold 1; for `(PURIFY, u, v, w)` a
colour of kind NP with input list `(u, u, u)` and outputs `v′` (threshold 1), `w′` (threshold 2), a
colour of kind NOT with input list `(v′, v′)` and output `v` (threshold 1), and a colour of kind NOT
with input list `(w′, w′)` and output `w` (threshold 1). -/
def gateGadgets (I : PCInst) (k : Fin I.gates.length) : PCGate I.n → List (Gadget I)
  | .nor u v w => [⟨.nor, [.inl u, .inl u, .inl v, .inl v], [(.inl w, 1)]⟩]
  | .purify u v w =>
      [⟨.np, [.inl u, .inl u, .inl u], [(.inr (k, false), 1), (.inr (k, true), 2)]⟩,
       ⟨.not, [.inr (k, false), .inr (k, false)], [(.inl v, 1)]⟩,
       ⟨.not, [.inr (k, true), .inr (k, true)], [(.inl w, 1)]⟩]

/-- All gadget colours, gate by gate in the order of the gate list. -/
def gadgets (I : PCInst) : List (Gadget I) :=
  (List.finRange I.gates.length).flatMap (fun k => gateGadgets I k (I.gates.get k))

/-- The number `n` of gadget colours; the colours are `Fin (numColours I)`. -/
abbrev numColours (I : PCInst) : ℕ := (gadgets I).length

/-- The gadget colour `c`. -/
def gad (I : PCInst) (c : Fin (numColours I)) : Gadget I := (gadgets I).get c

/-- The **host** of a node: the gadget colour of which it is an output (the first one; it is
unique, §4.2). -/
def host (I : PCInst) (x : Node I) : Option (Fin (numColours I)) :=
  (List.finRange (numColours I)).find? (fun c => (gad I c).outputs.any (fun p => decide (p.1 = x)))

/-- The threshold `κ` of a node as an output of its host. -/
def threshold (I : PCInst) (x : Node I) : ℕ :=
  match host I x with
  | some c => (((gad I c).outputs.find? (fun p => decide (p.1 = x))).map Prod.snd).getD 0
  | none => 0

/-- `b_d = b_K` for a colour `d` of kind `K`. -/
def bOf (I : PCInst) (H : HalfSizes) (d : Fin (numColours I)) : ℕ := H.get (gad I d).kind

/-- `s_d`: the length of the input list of `d`. -/
def sOf (I : PCInst) (d : Fin (numColours I)) : ℕ := (gad I d).inputs.length

/-- `m_d = 2 b_d − s_d`. -/
def mOf (I : PCInst) (H : HalfSizes) (d : Fin (numColours I)) : ℕ := 2 * bOf I H d - sOf I d

/-- The orientation of §4.2 for the colour order `ord` (`ord r = d_{r+1}`, 0-based `r`):
`τ(d_r) = (r − 1) mod 2` on the page, i.e. `(ord⁻¹ d) mod 2` with 0-based `r`. -/
def tauOrd {m : ℕ} (ord : Fin m ≃ Fin m) (d : Fin m) : ℕ := (ord.symm d).val % 2

/-- The segment `σ(x) = σ(κ)` of the host `d` of `x` given by (1) with `τ = τ(d)`, `κ` the
threshold of `x` (§4.2). -/
def seg (I : PCInst) (H : HalfSizes) (ord : Fin (numColours I) ≃ Fin (numColours I))
    (x : Node I) : ℕ :=
  match host I x with
  | some c => sigmaSeg (bOf I H c) (sOf I c) (tauOrd ord c) (threshold I x)
  | none => 0

/-- A position of the constructed word: the home bead of colour `c` in its block, or the sensor
bead of colour `d` for the `k`-th entry (0-based) of its input list. -/
inductive Slot (m : ℕ) where
  | home (c : Fin m)
  | sensor (d : Fin m) (k : ℕ)
  deriving DecidableEq

/-- The colour of a slot. -/
def Slot.colour {m : ℕ} : Slot m → Fin m
  | .home c => c
  | .sensor d _ => d

/-- The beads of `Σ^c_i` in a canonical order (§4.2): one bead of colour `d` for every colour `d`
and every entry `y` (the `k`-th) of the input list of `d` with host `c` and `σ(y) = i`. -/
def canonSigma (I : PCInst) (H : HalfSizes) (ord : Fin (numColours I) ≃ Fin (numColours I))
    (c : Fin (numColours I)) (i : ℕ) : List (Slot (numColours I)) :=
  (List.finRange (numColours I)).flatMap (fun d =>
    (List.finRange (gad I d).inputs.length).filterMap (fun k =>
      if host I ((gad I d).inputs.get k) = some c ∧ seg I H ord ((gad I d).inputs.get k) = i then
        some (Slot.sensor d k.val) else none))

/-- The free choices of §4.2: the order `d_1, …, d_n` of the gadget colours ("arbitrarily";
`ord r = d_{r+1}`) and, for every colour `c` and segment `i`, the order of the beads of `Σ^c_i`
("in any order"): any permutation of `canonSigma`. -/
structure Layout (I : PCInst) (H : HalfSizes) where
  ord : Fin (numColours I) ≃ Fin (numColours I)
  sig : Fin (numColours I) → ℕ → List (Slot (numColours I))
  sig_perm : ∀ c i, (sig c i).Perm (canonSigma I H ord c i)

namespace Layout

variable {I : PCInst} {H : HalfSizes}

/-- The block `B(c) = c Σ^c_1 c Σ^c_2 c ⋯ c Σ^c_{m_c−1} c` with `m_c` letters `c` (§4.2). -/
def block (L : Layout I H) (c : Fin (numColours I)) : List (Slot (numColours I)) :=
  Slot.home c :: (List.range' 1 (mOf I H c - 1)).flatMap (fun i => L.sig c i ++ [Slot.home c])

/-- The slots of `a = B(d_1) B(d_2) ⋯ B(d_n)`. -/
def slots (L : Layout I H) : List (Slot (numColours I)) :=
  (List.finRange (numColours I)).flatMap (fun r => L.block (L.ord r))

/-- **The necklace `a` of §4.2**: the colours of the slots of `B(d_1) ⋯ B(d_n)`. -/
def necklace (L : Layout I H) : Necklace := ⟨numColours I, L.slots.map Slot.colour⟩

/-- The first (0-based) position of `B(c)`: the total length of the blocks placed before it. -/
def start (L : Layout I H) (c : Fin (numColours I)) : ℕ :=
  (((List.finRange (numColours I)).filter (fun r => r < L.ord.symm c)).map
    (fun r => (L.block (L.ord r)).length)).sum

/-- The blocks `B(d_r)` of the constructed necklace, as position intervals. -/
def blocks (L : Layout I H) : Blocks (numColours I) where
  lo c := L.start c
  hi c := L.start c + (L.block c).length - 1

/-- The position of the sensor bead of colour `d` for the `k`-th entry of its input list. -/
def sensorPos (L : Layout I H) (d : Fin (numColours I)) (k : ℕ) : ℕ :=
  L.slots.idxOf (Slot.sensor d k)

/-- The split normalised as in §4.3: complemented if necessary so that `ℓ(1) = 0`. -/
def normLab (L : Layout I H) (ℓ : Fin L.necklace.N → Bool) : Fin L.necklace.N → Bool :=
  if L.necklace.lab ℓ 0 then (fun q => !ℓ q) else ℓ

/-- **The decoding** of §4.3: `val(x) = R_{h(x)}(σ(x)) ∈ {0, 1, ⊥}` for `x ∈ V⁺`, computed from the
normalised split, `h(x)` the host of `x` (a node with no host, an unused auxiliary node, reads `⊥`). -/
def val (L : Layout I H) (ℓ : Fin L.necklace.N → Bool) (x : Node I) : PVal :=
  match host I x with
  | some c => reading L.necklace L.blocks (L.normLab ℓ) c (seg I H L.ord x)
  | none => .bot

/-- The assignment `x = val|_V` read off a split (§4.3). -/
def decode (L : Layout I H) (ℓ : Fin L.necklace.N → Bool) : Fin I.n → PVal :=
  fun v => L.val ℓ (.inl v)

end Layout

/-- The canonical choice of the free orders: colours in the order of the gadget list (gates in the
order of the instance) and the beads of every `Σ^c_i` in `canonSigma` order. -/
def canonLayout (I : PCInst) (H : HalfSizes) : Layout I H where
  ord := Equiv.refl _
  sig := canonSigma I H (Equiv.refl _)
  sig_perm := fun _ _ => List.Perm.refl _

/-- A NOR gate. -/
def PCGate.isNor {n : ℕ} : PCGate n → Bool
  | .nor _ _ _ => true
  | .purify _ _ _ => false

end NecklacePPAD.Main


