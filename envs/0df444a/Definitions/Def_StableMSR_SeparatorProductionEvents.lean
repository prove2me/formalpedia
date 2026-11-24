-- Prove2me | Definitions.Def_StableMSR_SeparatorProductionEvents
-- name    : StableMSR_SeparatorProductionEvents
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-23T23:05:39.745242+00:00
-- url     : https://prove2.me/theorems/26915519-b450-43e5-b88a-8c1d9cbd7bff
-- title:
--   Ordered separator productions and symbolic child handles
-- statement:
--   The tight-separator dynamic program records each accepted pivot as a sequence of owned masks and child handles, followed by a union with its preceding alternative. Handles index the events in chronological order. The initial handle denotes failure, and a final save records the conjunction of root components. Replay starts with the two constant gates and translates every event into concrete local gate addresses.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Formal implementation of the finite separator circuit.

import Definitions.Def_StableMSR_TightComponentTrace
namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
def litStep (z:Gates×ℕ) (m:List ℕ) : Gates×ℕ :=
  let g:=z.1.push (.atom m)
  (g.push (.both z.2 z.1.size),g.size)

def sonStep (z:Gates×ℕ) (p:ℕ) : Gates×ℕ := (z.1.push (.both z.2 p),z.1.size)

end StableMSR.Recovery.TightLanguage
namespace StableMSR.Recovery.NativeWriter.Production
open SingleCircuit TightLanguage
set_option autoImplicit false

/-- Children and previous alternatives are referenced by event number. Handle zero is the failing alternative. -/
inductive Event where
  | mask (points : List ℕ)
  | child (ref : ℕ)
  | join (prior : ℕ)
  | save
  deriving DecidableEq, Repr

/-- Each successful pivot emits its owned blocks in the order supplied by the instance. -/
def chartAlgebra (d : Instance) : Algebra (List Event) ℕ where
  initial := []
  fail := 0
  alternative := fun es k v x cs =>
    let out := es ++ (d.owned v x).map Event.mask ++ cs.map Event.child ++ [.join k]
    (out,out.length)
  finish := fun es cs =>
    let out := es ++ cs.map Event.child ++ [.save]
    (out,out.length)

def chart (d : Instance) (w : ℕ) := scan (chartAlgebra d) d w

/-- An event handle denotes the local gate completing the corresponding alternative or root. -/
structure State where
  gates : Gates
  tail : ℕ
  memo : Array ℕ

def initial : State := ⟨#[.atom [],.stop],0,#[1]⟩
def resolve (s : State) (k : ℕ) := s.memo[k]?.getD 1

def step (s : State) : Event → State
  | .mask m =>
    let q := litStep (s.gates,s.tail) m
    ⟨q.1,q.2,s.memo.push 1⟩
  | .child k =>
    let q := sonStep (s.gates,s.tail) (resolve s k)
    ⟨q.1,q.2,s.memo.push 1⟩
  | .join k =>
    ⟨s.gates.push (.either (resolve s k) s.tail),0,s.memo.push s.gates.size⟩
  | .save => ⟨s.gates,0,s.memo.push s.tail⟩

def play (es : List Event) := es.foldl step initial
def result (t : List Event × ℕ) : Gates×ℕ := ((play t.1).gates,resolve (play t.1) t.2)

end StableMSR.Recovery.NativeWriter.Production


