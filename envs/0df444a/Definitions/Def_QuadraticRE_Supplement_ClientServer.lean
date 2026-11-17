-- Prove2me | Definitions.Def_QuadraticRE_Supplement_ClientServer
-- name    : QuadraticRE_Supplement_ClientServer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:53:53.476075+00:00
-- url     : https://prove2.me/theorems/b8d933b9-d994-4c2f-982d-e9751c0a8528
-- title:
--   Non-interactive client–server protocols, views, correctness and privacy against $A_t$
-- statement:
--   Let $F:X_1\times\dots\times X_m\to\{0,1\}^b$, where $X_i$ is the set of values of the input bits assigned to client $i$. A **non-interactive client–server protocol** (Definition 6.10) has input clients $C_1,\dots,C_m$, a receiver $D$ without input and servers $S_1,\dots,S_n$ without input. Every party $P$ samples an independent uniform tape $R_P$.
--
--   1. First round: $m_{i,s}=M_{i,s}(x_i,R_{C_i})$ and $m_{D,s}=M_{D,s}(R_D)$ are sent to $S_s$.
--   2. Second round: $S_s$ sends $Y_s=H_s((m_{i,s})_i,m_{D,s},R_{S_s})$ to $D$, which outputs $\mathrm{out}_D(x)=\mathrm{Dec}(R_D,(Y_s)_s)\in\{0,1\}^b\cup\{\perp\}$.
--
--   There is no other communication, setup, correlated randomness or oblivious transfer. The protocol has **correctness error** $\delta$ if $\Pr[\mathrm{out}_D(x)\neq F(x)]\le\delta$ for every $x$. The class $A_t$ consists of the coalitions made of any set of input clients, possibly $D$, and at most $t$ servers. The **view** of a coalition contains the inputs and complete tapes of its members and every message they receive. The protocol has **statistical privacy error** $\varepsilon$ against $A_t$ with simulator $\mathrm{Sim}$ if
--   $$\mathrm{SD}\big(\mathrm{Sim}(C,x[C],F(x)\text{ if }D\in C),\ \mathrm{View}_C(x)\big)\le\varepsilon$$
--   for every input $x$ and every $C\in A_t$.
--
--   These notions state Theorem 6.13.
--
--   **Formalization Note** Tape, upload and reply spaces are bit strings of given lengths (nonempty also for length $0$); such a protocol is a protocol of Definition 6.10. The assignment of the $N$ input bits of $F$ to the clients is a map $\mathrm{owner}:[N]\to[m]$. The view is one tuple with an empty slot for each party outside the coalition, so real and simulated views live on one finite set. The simulator is a deterministic map of uniform coins.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Definition 6.10, pp.43–44; p.44 (class $A_t$); Definitions 3.5 and 6.4, pp.15, 40; Lemma 6.12, p.46

import Mathlib
import Definitions.Def_QuadraticRE_SD

namespace QuadraticRE.Supplement

open QuadraticRE

/-- The input space `X_i` of input client `i`, for an assignment `owner : Fin N → Fin m` of the `N`
input bits of `F` to the `m` input clients (Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027
submission manuscript (sha256 0c94deae…), p.14: "the representation also specifies the assignment of
these bits to the parties"): the bits client `i` owns. -/
abbrev CInput {N m : ℕ} (owner : Fin N → Fin m) (i : Fin m) : Type := {j : Fin N // owner j = i} → F2

/-- The full input `x ∈ F₂^N` assembled from the clients' inputs. -/
def assemble {N m : ℕ} (owner : Fin N → Fin m) (x : ∀ i, CInput owner i) : Fin N → F2 :=
  fun j => x (owner j) ⟨j, rfl⟩

/-- A non-interactive client–server protocol, Definition 6.10, pp.43–44, with `m` input clients
`C_1, …, C_m` (client `i` holds `x_i ∈ X_i`), a receiver `D` without input and `n` servers without
input, for a function with output in `F₂^b`. Every party `P` has a uniform tape `R_P`.

1. First round: `m_{i,s} = M_{i,s}(x_i, R_{C_i})` and `m_{D,s} = M_{D,s}(R_D)` are sent to `S_s`.
2. Second round: `Y_s = H_s((m_{i,s})_i, m_{D,s}, R_{S_s})` is sent to `D`, which outputs
   `out_D(x) = Dec(R_D, (Y_s)_s) ∈ F₂^b ∪ {⊥}` (`none` is `⊥`).

There is no other communication, no setup, no correlated randomness and no oblivious transfer; the
maps are otherwise unrestricted.

**Formalization Note.** Tape, upload and reply spaces are bit strings `F₂^k` of the stated lengths
(nonempty also for `k = 0`); this is the case of Definition 6.10 used for the efficiency clause of
Theorem 6.13, and a protocol of this form is a protocol of Definition 6.10. -/
structure CSProtocol {N : ℕ} (m n : ℕ) (owner : Fin N → Fin m) (b : ℕ) where
  rC : Fin m → ℕ
  rD : ℕ
  rS : Fin n → ℕ
  up : Fin m → Fin n → ℕ
  upD : Fin n → ℕ
  rep : Fin n → ℕ
  M : ∀ i s, CInput owner i → (Fin (rC i) → F2) → Fin (up i s) → F2
  MD : ∀ s, (Fin rD → F2) → Fin (upD s) → F2
  H : ∀ s, (∀ i, Fin (up i s) → F2) → (Fin (upD s) → F2) → (Fin (rS s) → F2) → Fin (rep s) → F2
  Dec : (Fin rD → F2) → (∀ s, Fin (rep s) → F2) → Option (Fin b → F2)

namespace CSProtocol

variable {N m n b : ℕ} {owner : Fin N → Fin m}

/-- The joint tape of all parties: input clients, receiver, servers, sampled independently and
uniformly (a uniform element of the product). -/
abbrev Tapes (Pr : CSProtocol m n owner b) : Type :=
  (∀ i, Fin (Pr.rC i) → F2) × (Fin Pr.rD → F2) × (∀ s, Fin (Pr.rS s) → F2)

/-- The uploads server `s` receives from the input clients. -/
def uploads (Pr : CSProtocol m n owner b) (x : ∀ i, CInput owner i) (R : Pr.Tapes) (s : Fin n) :
    ∀ i, Fin (Pr.up i s) → F2 :=
  fun i => Pr.M i s (x i) (R.1 i)

/-- The reply of server `s`. -/
def reply (Pr : CSProtocol m n owner b) (x : ∀ i, CInput owner i) (R : Pr.Tapes) (s : Fin n) :
    Fin (Pr.rep s) → F2 :=
  Pr.H s (Pr.uploads x R s) (Pr.MD s R.2.1) (R.2.2 s)

/-- The receiver's output `out_D(x) = Dec(R_D, (Y_s)_s)`. -/
def out (Pr : CSProtocol m n owner b) (x : ∀ i, CInput owner i) (R : Pr.Tapes) : Option (Fin b → F2) :=
  Pr.Dec R.2.1 (fun s => Pr.reply x R s)

/-- A static semi-honest coalition: a set `I` of input clients, possibly the receiver (`D = true`), and
a set `B` of servers. -/
structure Coalition (m n : ℕ) where
  I : Finset (Fin m)
  D : Bool
  B : Finset (Fin n)

/-- The class `A_t` of Definition 6.10, p.44: any set of input clients, possibly the receiver, and at
most `t` servers. -/
def Coalition.InA (t : ℕ) (C : Coalition m n) : Prop := C.B.card ≤ t

/-- The view of a coalition (conventions of Definitions 3.5 and 6.4 and `View_C` of Lemma 6.12,
pp.15, 40, 46): the inputs and complete tapes of its members and every message they receive. Each
component is `none` for a party outside the coalition:

* input client `i`: its input and tape (input clients receive no messages);
* the receiver: its tape and all replies `(Y_s)_s`;
* server `s`: its tape, the uploads `(m_{i,s})_i` and `m_{D,s}`.

The type does not depend on the coalition, so real and simulated views are compared on one finite
set. -/
abbrev View (Pr : CSProtocol m n owner b) : Type :=
  (∀ i, Option (CInput owner i × (Fin (Pr.rC i) → F2))) ×
  Option ((Fin Pr.rD → F2) × (∀ s, Fin (Pr.rep s) → F2)) ×
  (∀ s, Option ((Fin (Pr.rS s) → F2) × (∀ i, Fin (Pr.up i s) → F2) × (Fin (Pr.upD s) → F2)))

open Classical in
/-- The view `View_C(x)` of coalition `C` on input `x` and joint tape `R`. -/
noncomputable def view (Pr : CSProtocol m n owner b) (C : Coalition m n) (x : ∀ i, CInput owner i)
    (R : Pr.Tapes) : Pr.View :=
  (fun i => if i ∈ C.I then some (x i, R.1 i) else none,
   if C.D then some (R.2.1, fun s => Pr.reply x R s) else none,
   fun s => if s ∈ C.B then some (R.2.2 s, Pr.uploads x R s, Pr.MD s R.2.1) else none)

/-- Correctness error at most `δ`, Definition 6.10: for every input `x`,
`Pr_R[out_D(x) ≠ F(x)] ≤ δ`. -/
def IsCorrect (Pr : CSProtocol m n owner b) (F : (∀ i, CInput owner i) → Fin b → F2) (δ : ℝ) : Prop :=
  ∀ x, prob (fun R : Pr.Tapes => Pr.out x R ≠ some (F x)) ≤ δ

open Classical in
/-- Statistical privacy error at most `ε` against `A_t`, with the simulator given on `τ` uniform coins:
for every input `x` and every coalition `C ∈ A_t`,
`SD(Sim(C, x[C], F(x) if D ∈ C), View_C(x)) ≤ ε`. The simulator receives the coalition, the inputs of
its input clients and, only when the receiver is in the coalition, the output `F(x)`. -/
def IsPrivate (Pr : CSProtocol m n owner b) (F : (∀ i, CInput owner i) → Fin b → F2) (t : ℕ) (ε : ℝ)
    (τ : ℕ)
    (sim : (C : Coalition m n) → (∀ i, i ∈ C.I → CInput owner i) → Option (Fin b → F2) →
      (Fin τ → F2) → Pr.View) : Prop :=
  ∀ (x : ∀ i, CInput owner i) (C : Coalition m n), C.InA t →
    SD (law (sim C (fun i _ => x i) (if C.D then some (F x) else none)))
      (law (Pr.view C x)) ≤ ε

end CSProtocol

end QuadraticRE.Supplement


