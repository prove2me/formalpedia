-- Prove2me | Definitions.Def_QuadraticRE_Supplement_CSConstruction
-- name    : QuadraticRE_Supplement_CSConstruction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:54:24.130508+00:00
-- url     : https://prove2.me/theorems/9fbc7e07-5e53-493a-9424-64b2abe42494
-- title:
--   Constructions of client–server protocols and their efficiency
-- statement:
--   The public parameters of a client–server construction are a mod-2 branching-program representation of $f:\{0,1\}^N\to\{0,1\}^b$ with the assignment of the $N$ input bits to $m\ge1$ input clients, the number $n$ of servers, a threshold $t$ with $n>2t$, and $1^\lambda$ with $\lambda\ge1$; they are encoded with all numbers in unary. $F$ is $f$ applied to the clients' bits.
--
--   A **construction** gives, for every such parameter, a protocol for $F$ in the model of Definition 6.10 and a simulator on uniform coins. It is **polynomial-time** if fixed polynomial-time machines, each receiving the encoded parameters, compute: all lengths of tapes and messages and the simulator's coin count; every client's and the receiver's first-round message; every server's reply; the receiver's decoder; and the simulator. The **total communication** is the sum of the bit lengths of all uploads and replies.
--
--   These objects state the efficiency clauses of Theorem 6.13.
--
--   **Formalization Note** Machine time is polynomial in the length of the machine's input, which starts with the encoded parameters; their length is polynomially related to $m+n+\sigma+\lambda$.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Definition 3.7, pp.15–16; Definition 6.10, pp.43–44; Theorem 6.13, p.47

import Mathlib
import Definitions.Def_QuadraticRE_PolyTimeFn
import Definitions.Def_QuadraticRE_Supplement_ClientServer

namespace QuadraticRE.Supplement

open QuadraticRE CSProtocol

/-- The public parameters of a client–server construction for Theorem 6.13 of Orsini, Patra, *From
Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.47: a mod-2
branching-program representation `rep` of `F : {0,1}^N → {0,1}^b`, the number `m ≥ 1` of input
clients with the assignment `owner` of the `N` input bits to them (p.14), the number `n` of servers,
the threshold `t` with `n > 2t` (so `0 ≤ t < n`), and `1^λ` with `λ ≥ 1`. -/
structure CSParam where
  rep : Rep
  m : ℕ
  n : ℕ
  t : ℕ
  owner : Fin rep.N → Fin m
  lam : ℕ
  hm : 1 ≤ m
  ht : 2 * t < n
  hlam : 1 ≤ lam

/-- The function `F(x_1, …, x_m) = f(x)` of the clients' inputs, `f` the function represented by
`rep`. -/
noncomputable def CSParam.F (p : CSParam) : (∀ i, CInput p.owner i) → Fin p.rep.b → F2 :=
  fun x => p.rep.eval (assemble p.owner x)

/-- The bit encoding of the public parameters: every number in unary (`rep`, `m`, `n`, `t`, `λ`, and
the owner of each input bit), so its length is polynomially related to `m + n + σ + λ`. -/
def encCSParam (p : CSParam) : List Bool :=
  encTokens (repTokens p.rep ++ [p.m, p.n, p.t, p.lam] ++ List.ofFn fun j => (p.owner j).val)

/-- The bits of a client's input, in the order of the input positions it owns. -/
def bitsIn {N m : ℕ} (owner : Fin N → Fin m) (i : Fin m) (xi : CInput owner i) : List Bool :=
  (List.finRange N).filterMap fun j => if h : owner j = i then some (decide (xi ⟨j, h⟩ = 1)) else none

/-- The bits of a family of vectors indexed by `Fin k`, concatenated in index order. -/
def bitsPi {k : ℕ} {len : Fin k → ℕ} (v : ∀ i, Fin (len i) → F2) : List Bool :=
  (List.finRange k).flatMap fun i => bits (v i)

/-- The lengths of a protocol: client tapes, receiver tape, server tapes, uploads (row order),
receiver uploads, replies. -/
def CSProtocol.lengthTokens {N m n b : ℕ} {owner : Fin N → Fin m} (Pr : CSProtocol m n owner b) :
    List ℕ :=
  List.ofFn Pr.rC ++ [Pr.rD] ++ List.ofFn Pr.rS ++
    (List.finRange m).flatMap (fun i => List.ofFn (Pr.up i)) ++ List.ofFn Pr.upD ++ List.ofFn Pr.rep

/-- The total communication in bits: all uploads and all replies. -/
def CSProtocol.comm {N m n b : ℕ} {owner : Fin N → Fin m} (Pr : CSProtocol m n owner b) : ℕ :=
  (∑ i, ∑ s, Pr.up i s) + (∑ s, Pr.upD s) + ∑ s, Pr.rep s

/-- The bit encoding of a coalition: membership of each input client, of the receiver, of each
server. -/
def encCoalition {m n : ℕ} (C : Coalition m n) : List Bool :=
  List.ofFn (fun i : Fin m => decide (i ∈ C.I)) ++ [C.D] ++ List.ofFn (fun s : Fin n => decide (s ∈ C.B))

/-- The bit encoding of the inputs `x[C]` the simulator receives. -/
def encCInputs {N m n : ℕ} {owner : Fin N → Fin m} (C : Coalition m n)
    (xI : ∀ i, i ∈ C.I → CInput owner i) : List Bool :=
  (List.finRange m).flatMap fun i => if h : i ∈ C.I then bitsIn owner i (xI i h) else []

/-- The bit encoding of a view: for each party `[0]` if absent, else `1` followed by its components. -/
def CSProtocol.encView {N m n b : ℕ} {owner : Fin N → Fin m} (Pr : CSProtocol m n owner b)
    (v : Pr.View) : List Bool :=
  (List.finRange m).flatMap (fun i => match v.1 i with
      | none => [false]
      | some (xi, r) => true :: (bitsIn owner i xi ++ bits r)) ++
    (match v.2.1 with
      | none => [false]
      | some (r, ys) => true :: (bits r ++ bitsPi ys)) ++
    (List.finRange n).flatMap (fun s => match v.2.2 s with
      | none => [false]
      | some (r, us, u) => true :: (bits r ++ bitsPi us ++ bits u))

/-- A construction of client–server protocols (Definition 3.7 conventions, p.15): for every public
parameter `p`, a protocol for `p.F` and a simulator on `τ p` uniform coins. -/
structure CSConstruction where
  prot : ∀ p : CSParam, CSProtocol p.m p.n p.owner p.rep.b
  τ : CSParam → ℕ
  sim : ∀ p : CSParam, (C : Coalition p.m p.n) → (∀ i, i ∈ C.I → CInput p.owner i) →
    Option (Fin p.rep.b → F2) → (Fin (τ p) → F2) → (prot p).View

/-- "Its construction and all protocol and simulation algorithms run in time polynomial" (Theorem
6.13, p.47): fixed polynomial-time machines, each taking the encoded public parameters first, for the
construction (all lengths and the simulator's coin count), each client's and the receiver's
first-round message, each server's reply, the receiver's decoder and the simulator. Inputs and outputs
are the bits of the data, in order. -/
structure CSConstruction.IsPolyTime (K : CSConstruction) : Prop where
  construct : PolyTimeFn encCSParam (fun p => encTokens ((K.prot p).lengthTokens ++ [K.τ p]))
  upload : PolyTimeFn
    (fun a : Σ p : CSParam, Σ i : Fin p.m, Fin p.n × CInput p.owner i × (Fin ((K.prot p).rC i) → F2) =>
      encCSParam a.1 ++ encNat a.2.1 ++ encNat a.2.2.1 ++ bitsIn a.1.owner a.2.1 a.2.2.2.1 ++
        bits a.2.2.2.2)
    (fun a => bits ((K.prot a.1).M a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2))
  uploadD : PolyTimeFn
    (fun a : Σ p : CSParam, Fin p.n × (Fin (K.prot p).rD → F2) =>
      encCSParam a.1 ++ encNat a.2.1 ++ bits a.2.2)
    (fun a => bits ((K.prot a.1).MD a.2.1 a.2.2))
  server : PolyTimeFn
    (fun a : Σ p : CSParam, Σ s : Fin p.n, (∀ i, Fin ((K.prot p).up i s) → F2) ×
        (Fin ((K.prot p).upD s) → F2) × (Fin ((K.prot p).rS s) → F2) =>
      encCSParam a.1 ++ encNat a.2.1 ++ bitsPi a.2.2.1 ++ bits a.2.2.2.1 ++ bits a.2.2.2.2)
    (fun a => bits ((K.prot a.1).H a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2))
  decoder : PolyTimeFn
    (fun a : Σ p : CSParam, (Fin (K.prot p).rD → F2) × (∀ s, Fin ((K.prot p).rep s) → F2) =>
      encCSParam a.1 ++ bits a.2.1 ++ bitsPi a.2.2)
    (fun a => encOpt ((K.prot a.1).Dec a.2.1 a.2.2))
  simulator : PolyTimeFn
    (fun a : Σ p : CSParam, Σ C : Coalition p.m p.n, (∀ i, i ∈ C.I → CInput p.owner i) ×
        Option (Fin p.rep.b → F2) × (Fin (K.τ p) → F2) =>
      encCSParam a.1 ++ encCoalition a.2.1 ++ encCInputs a.2.1 a.2.2.1 ++ encOpt a.2.2.2.1 ++
        bits a.2.2.2.2)
    (fun a => (K.prot a.1).encView (K.sim a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2))

end QuadraticRE.Supplement


