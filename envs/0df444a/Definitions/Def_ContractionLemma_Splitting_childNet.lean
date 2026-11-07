-- Prove2me | Definitions.Def_ContractionLemma_Splitting_childNet
-- name    : ContractionLemma_Splitting_childNet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:02:29.275622+00:00
-- url     : https://prove2.me/theorems/d2b88d60-2179-4661-99d5-5b074a9f792d
-- title:
--   The packet tensors $\kappa_{g,P}\mu_{g,P}$ and the networks $G_{g,\beta}$
-- statement:
--   Fix an exponent vector $\beta$, a level-$i$ group $g$ and a packet $P$. Let $\beta_{g,P}$ be the part of $\beta$ on the modes received by $g$ in $P$, and
--
--   $$
--   \kappa_{g,P}(Y,X)=\Big[\prod_{x\in g\cap P}\chi_{Y_x}\Big(\omega_x+\sum_\xi c_{x,\xi}\xi\Big)\Big]_{\beta_{g,P}},\qquad
--   \mu_{g,P}(X)=\prod_{\xi\text{ sent by }g\text{ in }P}\xi(X)^{\beta_\xi},
--   $$
--
--   where $[\,\cdot\,]_\beta$ is the coefficient of $\prod_\xi\xi^{\beta_\xi}$. The network $G_{g,\beta}$ has as vertices the old row and column vertices of $g$, with their tables unchanged, and one packet tensor per packet $P$, with table $\kappa_{g,P}\cdot\mu_{g,P}$. Each bit of $g$ becomes an edge from its old vertex to the packet tensor of its packet. The network is bipartite, with the old vertices on one side and the packet tensors on the other.
--
--   **Formalization Note** A packet with no bit of $g$ keeps its packet tensor as an isolated vertex whose constant table is the constant factor; the paper multiplies this constant into another table. The contraction is the same.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), proof of Lemma A.12.2, p.90

import Mathlib
import Definitions.Def_ContractionLemma_BipNet
import Definitions.Def_ContractionLemma_BipNet_Phi
import Definitions.Def_ContractionLemma_Packing
import Definitions.Def_ContractionLemma_NodeField
import Definitions.Def_ContractionLemma_Splitting_modeSet

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

namespace Splitting

variable {U W E : Type*} {f : ℤ[X]} {a : ℕ}

/-- The mode `ξ` is received by the level-`i` group `g`: some row bit of `g` crosses into its
tile (p.89). -/
def ReceivedBy [Fintype E] {R : Type*} (G : BipNet U W E R) (pk : Packing U W E a) (i p' : ℕ)
    (g : Fin 64) (ξ : Mode G pk i p') : Prop :=
  ∃ e, pk.rowSym (G.rowOf e) i = g ∧ Hears G pk i e ξ.1.1 ξ.1.2.1

/-- The mode `ξ` is sent by the level-`i` group `g`: its tile has a column of `g` (p.89). -/
def SentBy [Fintype E] {R : Type*} (G : BipNet U W E R) (pk : Packing U W E a) (i p' : ℕ)
    (g : Fin 64) (ξ : Mode G pk i p') : Prop :=
  ∃ e', InTile pk i ξ.1.1 ξ.1.2.1 e' ∧ pk.colSym (G.colOf e') i = g

/-- `κ_{g,P}(Y, X) = [∏_{x ∈ g ∩ P} χ_{Y_x}(ω_x + ∑_ξ c_{x,ξ} ξ)]_{β_{g,P}}` (p.90), with
`β_{g,P}` the part of `β` on the modes received by `g` in `P`. -/
noncomputable def kappa [Fintype E] (G : BipNet U W E (NodeField f)) (pk : Packing U W E a)
    (t : ℤ) (i : ℕ) (z : NodeField f) (p' : ℕ) (g : Fin 64) (P : Fin pk.np)
    (β : Mode G pk i p' → ℕ) (Y X : E → Bool) : NodeField f := by
  classical
  exact MvPolynomial.coeff
    (Finsupp.equivFunOnFinite.symm fun ξ => if ξ.1.1 = P ∧ ReceivedBy G pk i p' g ξ then β ξ else 0)
    (∏ e ∈ Finset.univ.filter (fun e => pk.rowSym (G.rowOf e) i = g ∧ pk.packet e = P),
      wireFactor G pk t i z p' e Y X)

/-- `μ_{g,P}(X) = ∏_{ξ sent by g in P} ξ(X)^{β_ξ}` (p.90). -/
noncomputable def mu [Fintype E] {R : Type*} (G : BipNet U W E R) (pk : Packing U W E a)
    (i p' : ℕ) (g : Fin 64) (P : Fin pk.np) (β : Mode G pk i p' → ℕ) (X : E → Bool) :
    NodeField f := by
  classical
  exact ∏ ξ ∈ Finset.univ.filter (fun ξ : Mode G pk i p' => ξ.1.1 = P ∧ SentBy G pk i p' g ξ),
    modeVal G pk i p' ξ X ^ β ξ

/-- The old vertices of the level-`i` group `g`: its row and column vertices. -/
abbrev OldV {R : Type*} (G : BipNet U W E R) (pk : Packing U W E a) (i : ℕ) (g : Fin 64) :=
  {u : U // pk.rowSym u i = g} ⊕ {w : W // pk.colSym w i = g}

/-- The bits of the level-`i` group `g`: the row bits whose row vertex is in `g` and the column
bits whose column vertex is in `g`. -/
abbrev Bits {R : Type*} (G : BipNet U W E R) (pk : Packing U W E a) (i : ℕ) (g : Fin 64) :=
  {e : E // pk.rowSym (G.rowOf e) i = g} ⊕ {e : E // pk.colSym (G.colOf e) i = g}

/-- The packet of a bit of the group `g`. -/
def bitPacket {R : Type*} {G : BipNet U W E R} {pk : Packing U W E a} {i : ℕ} {g : Fin 64} :
    Bits G pk i g → Fin pk.np
  | Sum.inl e => pk.packet e.1
  | Sum.inr e => pk.packet e.1

/-- The row bits read by the packet tensor of `P`, from its table argument (`false` off `g ∩ P`). -/
noncomputable def bitY {R : Type*} (G : BipNet U W E R) (pk : Packing U W E a) (i : ℕ) (g : Fin 64)
    (P : Fin pk.np) (zz : {b : Bits G pk i g // bitPacket b = P} → Bool) (e : E) : Bool := by
  classical
  exact if h : pk.rowSym (G.rowOf e) i = g ∧ pk.packet e = P then
    zz ⟨Sum.inl ⟨e, h.1⟩, h.2⟩ else false

/-- The column bits read by the packet tensor of `P`, from its table argument (`false` off
`g ∩ P`). -/
noncomputable def bitX {R : Type*} (G : BipNet U W E R) (pk : Packing U W E a) (i : ℕ) (g : Fin 64)
    (P : Fin pk.np) (zz : {b : Bits G pk i g // bitPacket b = P} → Bool) (e : E) : Bool := by
  classical
  exact if h : pk.colSym (G.colOf e) i = g ∧ pk.packet e = P then
    zz ⟨Sum.inr ⟨e, h.1⟩, h.2⟩ else false

/-- **The packet tensor** of the level-`i` group `g` in the packet `P`: the table
`κ_{g,P} · μ_{g,P}` (proof of Lemma A.12.2, p.90). -/
noncomputable def packetTensor [Fintype E] (G : BipNet U W E (NodeField f)) (pk : Packing U W E a)
    (t : ℤ) (i : ℕ) (z : NodeField f) (p' : ℕ) (g : Fin 64) (β : Mode G pk i p' → ℕ)
    (P : Fin pk.np) (zz : {b : Bits G pk i g // bitPacket b = P} → Bool) : NodeField f :=
  kappa G pk t i z p' g P β (bitY G pk i g P zz) (bitX G pk i g P zz) *
    mu G pk i p' g P β (bitX G pk i g P zz)

/-- **The network `G_{g,β}`** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), proof of Lemma A.12.2, p.90 (PDF p.93).

Its vertices are the old row and column vertices of the level-`i` group `g`, with their tables
unchanged, and one packet tensor per packet `P`, with table `κ_{g,P} · μ_{g,P}`. Each bit of `g`
becomes an edge from its old vertex to the packet tensor of its packet. The network is
bipartite, with the old vertices on one side and the packet tensors on the other.

**Formalization Note.** A packet with no bit of `g` keeps its packet tensor as an isolated
vertex whose (constant) table is the constant factor; the paper multiplies this constant into
the table of another vertex instead. The contraction is the same. -/
noncomputable def childNet [Fintype E] (G : BipNet U W E (NodeField f)) (pk : Packing U W E a)
    (t : ℤ) (i : ℕ) (z : NodeField f) (p' : ℕ) (g : Fin 64) (β : Mode G pk i p' → ℕ) :
    BipNet (OldV G pk i g) (Fin pk.np) (Bits G pk i g) (NodeField f) where
  rowOf
    | Sum.inl e => Sum.inl ⟨G.rowOf e.1, e.2⟩
    | Sum.inr e => Sum.inr ⟨G.colOf e.1, e.2⟩
  colOf := bitPacket
  rowTable
    | Sum.inl u => fun zz => G.rowTable u.1 fun e =>
        zz ⟨Sum.inl ⟨e.1, (congrArg (fun x => pk.rowSym x i) e.2).trans u.2⟩,
          congrArg Sum.inl (Subtype.ext e.2)⟩
    | Sum.inr w => fun zz => G.colTable w.1 fun e =>
        zz ⟨Sum.inr ⟨e.1, (congrArg (fun x => pk.colSym x i) e.2).trans w.2⟩,
          congrArg Sum.inr (Subtype.ext e.2)⟩
  colTable P zz := packetTensor G pk t i z p' g β P zz

end Splitting

end ContractionLemma


