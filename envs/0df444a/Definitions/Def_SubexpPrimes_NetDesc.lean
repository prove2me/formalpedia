-- Prove2me | Definitions.Def_SubexpPrimes_NetDesc
-- name    : SubexpPrimes_NetDesc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:26.416857+00:00
-- url     : https://prove2.me/theorems/22b4bd67-6eef-4eca-8919-e18ef788eea8
-- title:
--   Description of a network, and its entry algorithm
-- statement:
--   The **description** of a network is its graph on vertices $\{0,\dots,n-1\}$ and edges $\{0,\dots,m-1\}$, the set $W$ of designated weighted vertices, the precision $p$, the designated input edges, and further data for the entry algorithm. Its encoding is a bit word with all numbers in unary, and $L$ is its length. The entries are not part of it: they "are given by an algorithm that, on input $v$ and a local assignment, returns the entry; they are never written out as truth tables".
--
--   The hypothesis on values is that at the vertices of $W$ the entries lie in $2^{-p}\mathbb Z\cap[-1,1]$, and elsewhere in $\{0,1\}$. A machine **computes the entries** if, on the description, a vertex and a local assignment in increasing edge order, it outputs the integer $k$ with $T_v(z)=k/2^p$.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Definition 2.1, p.13; Theorem 2.5, p.15

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_Net
import Definitions.Def_SubexpPrimes_RunsWithin

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/-- **The description of a network** — Gajulapalli, *Deterministic Construction of Primes in
Subexponential Time* (manuscript, sha256 6ad4d3de…), Definition 2.1, p.13 ("Entry functions are
given by an algorithm … never written out as truth tables"), and Theorem 2.5, p.15.

The graph on vertices `Fin n` and edges `Fin m`, the set `W` of designated weighted vertices, the
precision `prec` (the `p` of `2^{-p}ℤ`), the designated input edges `inputs`, and `data`: whatever
else the entry algorithm needs, such as the input from which the network was produced. The entries
themselves are not part of the description. -/
structure NetDesc where
  /-- number of vertices -/
  n : ℕ
  /-- number of edges -/
  m : ℕ
  /-- endpoints of each edge -/
  ends : Fin m → Fin n × Fin n
  /-- no loops -/
  loopless : ∀ e, (ends e).1 ≠ (ends e).2
  /-- the designated weighted vertices -/
  W : Finset (Fin n)
  /-- the precision: entries lie in `2^{-prec} ℤ` -/
  prec : ℕ
  /-- the designated input edges, in the order of the input word -/
  inputs : List (Fin m)
  /-- further data for the entry algorithm -/
  data : List Bool

namespace NetDesc

/-- The encoding of a description: `n`, `m`, the edge list, `W`, `prec`, the input edges and
`data`, every number in unary, so `L := D.encode.length` bounds `n`, `m`, `|W|`, `prec`. -/
def encode (D : NetDesc) : List Bool :=
  Encoding.encodeList id
    [Encoding.encodeNat D.n, Encoding.encodeNat D.m,
      Encoding.encodeList (fun e : Fin D.m => Encoding.encodeNat (D.ends e).1 ++
        Encoding.encodeNat (D.ends e).2) (List.finRange D.m),
      Encoding.encodeList (fun v : Fin D.n => Encoding.encodeNat v) (D.W.sort (· ≤ ·)),
      Encoding.encodeNat D.prec,
      Encoding.encodeList (fun e : Fin D.m => Encoding.encodeNat e) D.inputs,
      D.data]

/-- Entry functions for the network of `D`, with entries in `R`. -/
abbrev Tables (D : NetDesc) (R : Type*) :=
  (v : Fin D.n) → ({e : Fin D.m // (D.ends e).1 = v ∨ (D.ends e).2 = v} → Bool) → R

/-- The network of `D` with entries `T`. -/
def net {R : Type*} (D : NetDesc) (T : D.Tables R) : Net (Fin D.n) (Fin D.m) R :=
  ⟨D.ends, D.loopless, T⟩

/-- The degree of a vertex of `D`. -/
def deg (D : NetDesc) (v : Fin D.n) : ℕ :=
  (Finset.univ.filter fun e => (D.ends e).1 = v ∨ (D.ends e).2 = v).card

/-- The degree of `D`: `max_v |E(v)|`, and `0` without vertices. -/
def maxDeg (D : NetDesc) : ℕ := Finset.univ.sup D.deg

/-- The bits read by the table of `v`, in increasing edge order. -/
def incidentBits (D : NetDesc) (v : Fin D.n)
    (z : {e : Fin D.m // (D.ends e).1 = v ∨ (D.ends e).2 = v} → Bool) : List Bool :=
  ((Finset.univ.filter fun e => (D.ends e).1 = v ∨ (D.ends e).2 = v).sort (· ≤ ·)).map
    fun e => if h : (D.ends e).1 = v ∨ (D.ends e).2 = v then z ⟨e, h⟩ else false

/-- The input of the entry algorithm: the description, the vertex, the local assignment. -/
def entryInput (D : NetDesc) (v : Fin D.n)
    (z : {e : Fin D.m // (D.ends e).1 = v ∨ (D.ends e).2 = v} → Bool) : List Bool :=
  Encoding.encodeList id [D.encode, Encoding.encodeNat v, D.incidentBits v z]

/-- The hypotheses of Theorem 2.5 on the values of the entries (p.15): "At w designated vertices
the entries lie in 2^{−p}ℤ ∩ [−1, 1]; all other entries lie in {0, 1}". A vertex of `W` may also
have Boolean entries, and negative entries occur only on `W`. -/
def EntriesInRange (D : NetDesc) (T : D.Tables ℚ) : Prop :=
  ∀ v z, (v ∈ D.W → (∃ k : ℤ, T v z = (k : ℚ) / 2 ^ D.prec) ∧ |T v z| ≤ 1) ∧
    (v ∉ D.W → T v z = 0 ∨ T v z = 1)

/-- **"Entries are computed by `E` in time `τ` and space `σ`"** (Definition 2.1, p.13): on the
input `entryInput D v z`, the machine `E` halts with the integer `k` on tape `out`, where
`T v z = k / 2^{prec}`. -/
def EntryComputes (D : NetDesc) (E : PrimitiveMachine) (out : Fin E.tapeCount)
    (T : D.Tables ℚ) (τ σ : ℝ) : Prop :=
  ∀ v z, ∃ k : ℤ, T v z = (k : ℚ) / 2 ^ D.prec ∧
    RunsWithin E out (D.entryInput v z) (intWord k) τ σ

end NetDesc

end SubexpPrimes


