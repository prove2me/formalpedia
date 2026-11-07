-- Prove2me | Definitions.Def_ContractionLemma_Net_normalForm
-- name    : ContractionLemma_Net_normalForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:59:11.971651+00:00
-- url     : https://prove2.me/theorems/4c4d6544-b4a9-467f-ac44-d22f46623f96
-- title:
--   The normal form $G^\prime$: every edge subdivided by an equality vertex
-- statement:
--   Let $G$ be a network. The **normal form** $G'$ deletes the isolated vertices and multiplies their constant entries into a scalar $c$. It replaces every edge $e=\{u,v\}$ by a path $u - m_e - v$ through a new vertex $m_e$ with the equality table
--
--   $$
--   T_{m_e}(x,y)=[x=y].
--   $$
--
--   The old non-isolated vertices, with their tables unchanged, are the row vertices, and the new vertices are the column vertices. The module also fixes the word that describes $G'$ and $c$ for an encoded instance.
--
--   **Formalization Note** The edges of $G'$ are the pairs $(e,b)$, where $b$ selects an endpoint of $e$. An old vertex reads through $(e,b)$, with $b$ its side of $e$, the bit it read through $e$. Tables are indexed by incident edges, so keeping the order of each vertex's incident edges needs no separate bookkeeping.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), App. A.3.1, p.51 and proof of Lemma A.3, p.82

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_Net
import Definitions.Def_ContractionLemma_BipNet
import Definitions.Def_ContractionLemma_Instance

set_option autoImplicit false

namespace ContractionLemma

open OAI.Algorithms.SubexponentialSAT

namespace Net

variable {V E R : Type*}

/-- A vertex is isolated when no edge is incident to it. -/
def IsIsolated (G : Net V E R) (v : V) : Prop := ∀ e, (G.ends e).1 ≠ v ∧ (G.ends e).2 ≠ v

instance [Fintype E] [DecidableEq V] (G : Net V E R) : DecidablePred G.IsIsolated :=
  fun v => inferInstanceAs (Decidable (∀ e, (G.ends e).1 ≠ v ∧ (G.ends e).2 ≠ v))

/-- The endpoint of edge `e` on side `b` (`false`: first endpoint, `true`: second). -/
def endOn (G : Net V E R) (e : E) (b : Bool) : V := if b then (G.ends e).2 else (G.ends e).1

lemma endOn_not_isolated (G : Net V E R) (e : E) (b : Bool) : ¬ G.IsIsolated (G.endOn e b) := by
  intro h
  cases b
  · exact (h e).1 rfl
  · exact (h e).2 rfl

/-- The side of an edge `e` incident to `v` on which `v` lies. -/
def sideOf [DecidableEq V] (G : Net V E R) (v : V) (e : E) : Bool := decide ((G.ends e).1 ≠ v)

lemma endOn_sideOf [DecidableEq V] (G : Net V E R) (v : V) (e : E)
    (h : (G.ends e).1 = v ∨ (G.ends e).2 = v) : G.endOn e (G.sideOf v e) = v := by
  unfold endOn sideOf
  by_cases h1 : (G.ends e).1 = v
  · simp [h1]
  · simp only [ne_eq, h1, not_false_eq_true, decide_true, if_true]
    exact h.resolve_left h1

/-- **The scalar `c` of the normal form** (Lemma A.3, proof on p.82): the product of the
(constant) entries of the isolated vertices. -/
def nfScalar [Fintype V] [DecidableEq V] [Fintype E] [CommSemiring R] (G : Net V E R) : R :=
  ∏ v ∈ Finset.univ.filter G.IsIsolated, G.table v (fun _ => false)

/-- **The normal form `G′`** (Lemma A.3, construction in App. A.3.1, p.51 and proof p.82) of
Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript, sha256 049caea1…).

Isolated vertices are deleted. Every edge `e = {u, v}` is replaced by a path `u – m_e – v`
through a new vertex `m_e` with the equality table `[x = y]`. The row vertices of `G′` are the
non-isolated old vertices, with their tables unchanged; the column vertices are the new
vertices `m_e`, one per edge `e`; the edges of `G′` are the pairs `(e, b)`, `(e, false)`
joining the first endpoint of `e` to `m_e` and `(e, true)` joining the second endpoint to
`m_e`.

**Formalization Note.** An old vertex `u` reads, through the new edge `(e, b)` with `b` its
side of `e`, the bit it read through `e`. Tables are indexed by incident edges, so "keeping the
order of each vertex's incident edges" needs no separate bookkeeping. -/
def normalForm [DecidableEq V] [CommSemiring R] (G : Net V E R) :
    BipNet {v : V // ¬ G.IsIsolated v} E (E × Bool) R where
  rowOf p := ⟨G.endOn p.1 p.2, G.endOn_not_isolated p.1 p.2⟩
  colOf p := p.1
  rowTable u z := G.table u.1 fun e =>
    z ⟨(e.1, G.sideOf u.1 e.1), Subtype.ext (G.endOn_sideOf u.1 e.1 e.2)⟩
  colTable e z := if z ⟨(e, false), rfl⟩ = z ⟨(e, true), rfl⟩ then 1 else 0

end Net

namespace Instance

/-- The description of the normal form `G′` of the network of `I` together with its scalar
`c ∈ R_{P,ℓ}`, as a word: the coefficients of `c`, the list of the non-isolated old vertices
(the row vertices of `G′`, in increasing order), and the edge list of `G′`, the edge `(e, b)`
written as its row endpoint and its column vertex `m_e` (named by `e`), for
`e = 0, …, m - 1` and `b = false, true`. -/
noncomputable def nfWord (I : Instance) (c : TruncPoly I.P) : List Bool := by
  classical
  exact Encoding.encodeList id
    [truncWord I.ℓ c,
      Encoding.encodeList (fun v : Fin I.n => Encoding.encodeNat v)
        ((Finset.univ.filter fun v : Fin I.n =>
          ∃ e, (I.ends e).1 = v ∨ (I.ends e).2 = v).sort (· ≤ ·)),
      Encoding.encodeList
        (fun p : Fin I.m × Bool => Encoding.encodeNat
          (if p.2 then (I.ends p.1).2 else (I.ends p.1).1) ++ Encoding.encodeNat p.1)
        ((List.finRange I.m).flatMap fun e => [(e, false), (e, true)])]

end Instance

end ContractionLemma


