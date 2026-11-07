-- Prove2me | Definitions.Def_ContractionLemma_Instance
-- name    : ContractionLemma_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:30.561059+00:00
-- url     : https://prove2.me/theorems/ecf2d0e1-f13d-4ece-99dd-a26641cf8484
-- title:
--   Instances, the ring $R_{P,\ell}=(\mathbb Z/2^P\mathbb Z)[V]/(V^\ell)$, and entry machines
-- statement:
--   The ring of the contraction lemma is the ring of truncated polynomials $R_{P,\ell}=(\mathbb Z/2^P\mathbb Z)[V]/(V^\ell)$, whose elements are lists of $\ell$ integers modulo $2^P$, added and multiplied like the coefficients of polynomials in a formal variable $V$, with $V^\ell$ and higher powers discarded. For $\ell=1$ it is $\mathbb Z/2^P\mathbb Z$.
--
--   An **instance** is the input from which a network is produced: a word $x$, the scale $s$, the parameters $P,\ell$, and the edge list of a loopless multigraph on $n$ vertices with $m$ edges. Its encoding writes $x$, then $s,P,\ell,n,m$ and each edge's endpoints in unary, and $N$ denotes the length of this encoding. The tables are not part of the instance. An **entry machine** $E$ computes them within time $\tau$ and space $\sigma$ when, for every vertex $v$ and every assignment $z$ of its edges, $E$ on input (instance, $v$, $z$ in increasing edge order) outputs the $\ell$ coefficients of $T_v(z)$, each as an integer in $[0,2^P)$ in binary. For Theorem A.2 the output is the single residue in $[0,2^P)$.
--
--   **Formalization Note** An element of $R_{P,\ell}$ is represented by any polynomial in $(\mathbb Z/2^P\mathbb Z)[V]$ and stands for its coefficients of degree below $\ell$. Truncation is a ring homomorphism, so a contraction may be computed in the polynomial ring and read off afterwards.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), §2.1, p.16; App. A.1, p.49; App. A.8, p.81

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_Net
import Definitions.Def_ContractionLemma_RunsWithin

set_option autoImplicit false

namespace ContractionLemma

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **The truncated polynomial ring `R_{P,ℓ} = (ℤ/2^Pℤ)[V]/(V^ℓ)`** — Gajulapalli,
*The Contraction Lemma Beyond ETH* (manuscript, sha256 049caea1…), §2.1, p.16 (and App. A.8,
p.81).

**Formalization Note.** An element of `R_{P,ℓ}` is represented by any polynomial in
`(ZMod (2^P))[V]`; it stands for its residue modulo `V^ℓ`, i.e. for its coefficients of degree
`< ℓ`. Truncation is a ring homomorphism, so a contraction may be computed in `(ZMod (2^P))[V]`
and truncated afterwards: its `ℓ` low coefficients are those of the contraction in `R_{P,ℓ}`. -/
abbrev TruncPoly (P : ℕ) := Polynomial (ZMod (2 ^ P))

/-- The output word of an element of `R_{P,ℓ}`: the list of its `ℓ` coefficients
`c_0, …, c_{ℓ-1}`, each an integer in `[0, 2^P)` written in binary (`countWord`), framed by
`encodeList`. -/
def truncWord {P : ℕ} (ℓ : ℕ) (r : TruncPoly P) : List Bool :=
  Encoding.encodeList countWord (List.ofFn fun k : Fin ℓ => (r.coeff k).val)

/-- **An instance**: the input from which a network is produced (p.16), with its explicit
description. `input` is the original input, `s` the scale, `P` and `ℓ` the parameters of
`R_{P,ℓ}`, and `ends` the edge list of the network on vertices `Fin n` and edges `Fin m`
(loopless, multi-edges allowed). The tables are not part of the instance: they are given by an
entry machine (`EntryComputes`). -/
structure Instance where
  /-- the original input -/
  input : List Bool
  /-- the scale `s` -/
  s : ℕ
  /-- the precision `P` -/
  P : ℕ
  /-- the truncation order `ℓ` -/
  ℓ : ℕ
  /-- number of vertices -/
  n : ℕ
  /-- number of edges -/
  m : ℕ
  /-- endpoints of each edge -/
  ends : Fin m → Fin n × Fin n
  /-- no loops -/
  loopless : ∀ e, (ends e).1 ≠ (ends e).2

namespace Instance

/-- The encoding of an instance: the input, then `s, P, ℓ, n, m` in unary, then the edge list,
each edge as its two endpoints in unary. `N := I.encode.length` is the input length. -/
def encode (I : Instance) : List Bool :=
  Encoding.encodeList id
    [I.input, Encoding.encodeNat I.s, Encoding.encodeNat I.P, Encoding.encodeNat I.ℓ,
      Encoding.encodeNat I.n, Encoding.encodeNat I.m,
      Encoding.encodeList (fun e : Fin I.m => Encoding.encodeNat (I.ends e).1 ++
        Encoding.encodeNat (I.ends e).2) (List.finRange I.m)]

/-- Tables for the network of `I` with entries in `R`. -/
abbrev Tables (I : Instance) (R : Type*) :=
  (v : Fin I.n) → ({e : Fin I.m // (I.ends e).1 = v ∨ (I.ends e).2 = v} → Bool) → R

/-- The network of `I` with tables `T`. -/
def net {R : Type*} (I : Instance) (T : I.Tables R) : Net (Fin I.n) (Fin I.m) R :=
  ⟨I.ends, I.loopless, T⟩

/-- The degree of a vertex of `I` (incident edges, with multiplicity). -/
def deg (I : Instance) (v : Fin I.n) : ℕ :=
  (Finset.univ.filter fun e => (I.ends e).1 = v ∨ (I.ends e).2 = v).card

/-- The maximum degree of the network of `I`. -/
def maxDeg (I : Instance) : ℕ := Finset.univ.sup I.deg

/-- The bits read by the table of `v`, listed in increasing edge order. -/
def incidentBits (I : Instance) (v : Fin I.n)
    (z : {e : Fin I.m // (I.ends e).1 = v ∨ (I.ends e).2 = v} → Bool) : List Bool :=
  ((Finset.univ.filter fun e => (I.ends e).1 = v ∨ (I.ends e).2 = v).sort (· ≤ ·)).map
    fun e => if h : (I.ends e).1 = v ∨ (I.ends e).2 = v then z ⟨e, h⟩ else false

/-- The input of the entry machine for the entry `T_v(z)`: the instance, the vertex `v` in
unary, and the bits `z` in increasing edge order. -/
def entryInput (I : Instance) (v : Fin I.n)
    (z : {e : Fin I.m // (I.ends e).1 = v ∨ (I.ends e).2 = v} → Bool) : List Bool :=
  Encoding.encodeList id [I.encode, Encoding.encodeNat v, I.incidentBits v z]

/-- **"Each entry `T_v(·)` can be computed in time `τ` and space `σ`"** (p.16), for entries in
`R_{P,ℓ}`: on the input `entryInput I v z`, the entry machine `E` halts within `τ` steps and
`σ` visited cells with the word of `T v z ∈ R_{P,ℓ}` (its `ℓ` coefficients) on tape `out`. -/
def EntryComputes (E : PrimitiveMachine) (out : Fin E.tapeCount) (I : Instance)
    (T : I.Tables (TruncPoly I.P)) (τ σ : ℝ) : Prop :=
  ∀ v z, RunsWithin E out (I.entryInput v z) (truncWord I.ℓ (T v z)) τ σ

/-- The same for entries that are integers modulo `2^P` (Theorem A.2): the output is the
residue as an integer in `[0, 2^P)`, in binary. -/
def EntryComputesMod (E : PrimitiveMachine) (out : Fin E.tapeCount) (I : Instance)
    (T : I.Tables (ZMod (2 ^ I.P))) (τ σ : ℝ) : Prop :=
  ∀ v z, RunsWithin E out (I.entryInput v z) (countWord (T v z).val) τ σ

end Instance

end ContractionLemma


