-- Prove2me | Definitions.Def_MixedORAM_PublicRead_Model
-- name    : MixedORAM_PublicRead_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:45:36.987748+00:00
-- url     : https://prove2.me/theorems/791286a1-20ff-4e25-940c-2f212a48f7b9
-- title:
--   Online randomized cell-probe ORAM: requests, decision-tree programs, implementations, executions, traces and per-read correctness
-- statement:
--   A logical array has $n$ words of $w$ bits. A **request** is a pair (mode, operation): the mode is *public* or *private*, the operation is $\mathrm{read}(x)$ or $\mathrm{write}(x,v)$ with an address $x\in\{0,\dots,n-1\}$ and a $w$-bit word $v$. All four combinations of mode and kind are allowed (the *full API*).
--
--   The passive server has $2^a$ cells of $w$ bits, addressed by $a$-bit strings. A **probe** reads one cell or overwrites one cell (an overwrite returns nothing). A request is served by an adaptive **cell-probe program**, a decision tree whose nodes read a cell (and branch on its contents) or overwrite a cell, and whose leaves return a $w$-bit answer and the new client state. Local computation is free.
--
--   An **implementation** with parameters $(n,w,m,a)$ consists of
--
--   - a request-independent **preprocessing**: for an initial array $A_0$, a probability law over (the list of its probes, the initial server memory, the initial client state);
--   - a **step**: for the retained client state $s$ and the request $r$, a probability law over programs.
--
--   The client state retained between requests is a string of $m\cdot w$ bits. Requests are served online: each request runs a program drawn independently from the step law at the current state, on the current memory.
--
--   The **execution** on an input $(A_0,u)$ (initial array, finite request list) records for each request its probes and its answer. The **observed trace** consists of the preprocessing probes and, for each request, the list of its probes (address and direction); it contains neither cell contents nor answers. The **correct answer** to a read of $x$ after the requests $u_{<t}$ is the value of the latest write to $x$ among them, or $A_0(x)$.
--
--   An implementation has **per-read correctness** if for every initial array, every finite request list $u$ and every position $t$ of $u$ holding a read of $x$ (public or private),
--   $$\Pr\big[\text{answer of request } t = \text{correct answer}\big]\ \ge\ \tfrac23 .$$
--
--   **Formalization Note** Positions are $0$-based. The step law depends only on the retained state and the request, which is the paper's "the preprocessing and each request have their own independent random tapes" (p. 14). Only the state kept between requests is bounded by $mw$ bits; memory used inside a request is free.
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), p. 4, §2.1; p. 14, Appendix A preamble

import Mathlib

set_option autoImplicit false

namespace MixedORAM.PublicRead

/-- The **mode** of a logical request (Ciszewski, Ragnoli, *Access Cost Tradeoffs in Mixed-Mode
Oblivious RAM*, STOC 2027 submission (manuscript sha256 a4f849fd…), §1, p. 1: "lets each request be
marked public or private"). -/
inductive Mode where
  | pub
  | priv
  deriving DecidableEq

/-- The **kind** of a logical request: a read or a write (§2.2, p. 4: "each private request's kind
(read/write)"). -/
inductive Kind where
  | read
  | write
  deriving DecidableEq

/-- A logical operation on the array of `n` words of `w` bits: `read x` or `write x v`, with
`x ∈ Fin n` (the paper's `[n]`, shifted to start at `0`) and `v` a `w`-bit word. -/
inductive Op (n w : ℕ) where
  | read (x : Fin n)
  | write (x : Fin n) (v : BitVec w)
  deriving DecidableEq

/-- The kind (read or write) of an operation. -/
def Op.kind {n w : ℕ} : Op n w → Kind
  | .read _ => .read
  | .write _ _ => .write

/-- The logical address of an operation. -/
def Op.addr {n w : ℕ} : Op n w → Fin n
  | .read x => x
  | .write x _ => x

/-- A logical **request**: a mode together with an operation. The full API allows all four
combinations of mode and kind (§2.1, p. 4; Theorem A.1, p. 14: "every fixed full-API input"). -/
structure Request (n w : ℕ) where
  mode : Mode
  op : Op n w
  deriving DecidableEq

/-- **Server memory** with `a`-bit physical addresses: each of the `2^a` cells holds a `w`-bit word
(§2.1, p. 4: "The passive server stores w-bit cells at addresses of O(w) bits"). -/
abbrev Memory (a w : ℕ) := BitVec a → BitVec w

/-- The client's **retained state** between requests: `m · w` bits (§2.1, p. 4: "The client retains
at most mw bits"). -/
abbrev ClientState (m w : ℕ) := BitVec (m * w)

/-- One **probe**: a physical address and a direction (`isWrite = true` for an overwrite, `false`
for a read). The observed trace records exactly these two fields of every probe (§2.1, p. 4). -/
structure Probe (a : ℕ) where
  addr : BitVec a
  isWrite : Bool
  deriving DecidableEq

/-- An adaptive **cell-probe program** (a decision tree) with `a`-bit addresses and `w`-bit cells,
returning a `w`-bit answer and a value of type `σ` (the new client state):
`ret ans s` stops; `read x k` reads cell `x` and continues with `k` applied to its contents;
`write x v k` overwrites cell `x` with `v` (returning nothing) and continues with `k`.
Local computation is free (§2.1, p. 4: "a probe reads or overwrites one cell (an overwrite returns no
old contents), and local computation is free"). -/
inductive Prog (a w : ℕ) (σ : Type) : Type where
  | ret (ans : BitVec w) (s : σ) : Prog a w σ
  | read (addr : BitVec a) (k : BitVec w → Prog a w σ) : Prog a w σ
  | write (addr : BitVec a) (v : BitVec w) (k : Prog a w σ) : Prog a w σ

/-- Running a program on server memory `M`: the list of its probes in order, its answer, its final
state and the server memory afterwards. -/
def Prog.run {a w : ℕ} {σ : Type} : Prog a w σ → Memory a w →
    List (Probe a) × BitVec w × σ × Memory a w
  | .ret ans s, M => ([], ans, s, M)
  | .read x k, M =>
      let r := (k (M x)).run M
      (⟨x, false⟩ :: r.1, r.2)
  | .write x v k, M =>
      let r := k.run (Function.update M x v)
      (⟨x, true⟩ :: r.1, r.2)

/-- An **online randomized cell-probe implementation** with array size `n`, word size `w`, `m`
client words and `a`-bit physical addresses (§2.1, p. 4; Appendix A, p. 14).

* `init A₀` is the law of the outcome of the request-independent preprocessing on the initial
  array `A₀`: the probes it makes (observed by the server), the server memory and the client state
  it leaves ("Initial contents and request-independent preprocessing may be arbitrary, subject to
  the memory bound", p. 14; "Request-independent preprocessing obeys the memory bound and is charged
  separately", p. 4).
* `step s r` is the law of the cell-probe program run for request `r` when the retained client
  state is `s`; each request uses its own independent randomness ("Without loss of generality, the
  preprocessing and each request have their own independent random tapes", p. 14).

Requests are served online, each completing before the next arrives; between requests the client
keeps only its state in `ClientState m w` (`m · w` bits). -/
structure Impl (n w m a : ℕ) where
  init : (Fin n → BitVec w) → PMF (List (Probe a) × Memory a w × ClientState m w)
  step : ClientState m w → Request n w → PMF (Prog a w (ClientState m w))

/-- What one request produced: its probes (addresses and directions) and its returned word. -/
structure StepRecord (a w : ℕ) where
  probes : List (Probe a)
  answer : BitVec w

/-- Serving a list of requests online from server memory `M` and client state `s`: the law of the
list of step records, one per request. -/
noncomputable def Impl.runFrom {n w m a : ℕ} (I : Impl n w m a) :
    List (Request n w) → Memory a w × ClientState m w → PMF (List (StepRecord a w))
  | [], _ => PMF.pure []
  | r :: rs, (M, s) =>
      (I.step s r).bind fun P =>
        let o := P.run M
        (I.runFrom rs (o.2.2.2, o.2.2.1)).map fun t => ⟨o.1, o.2.1⟩ :: t

/-- The **run** of `I` on the input `(A₀, u)` (initial array `A₀`, request list `u`):
preprocessing, then every request of `u` in order. Its value is the list of preprocessing probes
together with the step records of the requests. -/
noncomputable def Impl.run {n w m a : ℕ} (I : Impl n w m a) (A₀ : Fin n → BitVec w)
    (u : List (Request n w)) : PMF (List (Probe a) × List (StepRecord a w)) :=
  (I.init A₀).bind fun x => (I.runFrom u (x.2.1, x.2.2)).map fun res => (x.1, res)

/-- The **execution** of `I` on `(A₀, u)`: the law of the step records of the requests. -/
noncomputable def Impl.exec {n w m a : ℕ} (I : Impl n w m a) (A₀ : Fin n → BitVec w)
    (u : List (Request n w)) : PMF (List (StepRecord a w)) :=
  (I.run A₀ u).map Prod.snd

/-- The request part of a trace: one list of probes per request; the list structure marks the
request boundaries. -/
abbrev ReqTrace (a : ℕ) := List (List (Probe a))

/-- An observed **trace**: the preprocessing probes, then one list of probes per request. It
contains neither cell contents nor answers (§2.1, p. 4: "The observed trace consists of probe
addresses, probe directions, and logical request boundaries, but neither cell contents nor returned
answers"). -/
abbrev Trace (a : ℕ) := List (Probe a) × ReqTrace a

/-- The request part of the trace of an execution. -/
def traceOf {a w : ℕ} (res : List (StepRecord a w)) : ReqTrace a := res.map (·.probes)

/-- The law of the observed trace of `I` on `(A₀, u)`. -/
noncomputable def Impl.traceDist {n w m a : ℕ} (I : Impl n w m a) (A₀ : Fin n → BitVec w)
    (u : List (Request n w)) : PMF (Trace a) :=
  (I.run A₀ u).map fun x => (x.1, traceOf x.2)

/-- The **correct answer** to a read of `x` issued after the requests `u`: the value of the latest
write to `x` in `u` (public or private), or `A₀ x` if there is none. -/
def correctAnswer {n w : ℕ} (A₀ : Fin n → BitVec w) (u : List (Request n w)) (x : Fin n) :
    BitVec w :=
  u.foldl (fun acc r => match r.op with
    | .write y v => if y = x then v else acc
    | .read _ => acc) (A₀ x)

/-- **Per-read correctness at least 2/3 on every fixed input** (§2.1, p. 4: "Every read must be
correct with probability at least 2/3 on every fixed input"; Theorem A.1: "on every fixed full-API
input"): for every initial array `A₀`, every finite request list `u` and every position `t` of `u`
holding a read of `x` (public or private), the answer of request `t` equals the correct answer with
probability at least `2/3`. Positions are `0`-based. -/
def Impl.Correct {n w m a : ℕ} (I : Impl n w m a) : Prop :=
  ∀ (A₀ : Fin n → BitVec w) (u : List (Request n w)) (t : ℕ) (x : Fin n) (ht : t < u.length),
    (u[t]'ht).op = .read x →
      (2 / 3 : ENNReal) ≤ (I.exec A₀ u).toOuterMeasure
        {res | (res[t]?).map (·.answer) = some (correctAnswer A₀ (u.take t) x)}

end MixedORAM.PublicRead


