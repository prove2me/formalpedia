-- Prove2me | Definitions.Def_InducedExpanderTest989_Structural_Programs
-- name    : InducedExpanderTest989_Structural_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:57:05.086793+00:00
-- url     : https://prove2.me/theorems/431a29f3-c563-4238-b8ee-1d6a6ee17e6a
-- title:
--   Randomized oracle programs and operational cost semantics
-- statement:
--   A randomized oracle computation is a finite tree with a return value, an adjacency query, a uniform draw from a positive finite set, or a unit of elementary work. A query continuation receives only that oracle answer. No program constructor receives a graph. Uniform draws at successive nodes use independent randomness. For an oracle O, evaluation recursively averages rewards at sample nodes, follows the actual answer at query nodes, and preserves rewards at tick nodes. Acceptance uses reward 1 for true and 0 for false.
--   $$\operatorname{queriesOn}(O,p)=\text{maximum number of query nodes on an execution},\qquad
--   \operatorname{timeOn}(O,p)=\text{maximum number of nonreturn nodes on an execution}.$$
--   At a sample node the maximum ranges over every possible draw; at a query it follows O's actual answer. These counts are computed from the tree and oracle, not fields or inputs. A polymorphic return type supports composition; the tester itself returns Bool. This is the declared operational encoding of the paper's unit-cost arithmetic model.
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.16 (PDF p.18), Algorithm 1; §1.1 p.2; §3 p.13; running-time accounting p.32; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Graph

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

/-- Finite oracle computation tree: G is deliberately absent from the type. -/
inductive Prog (n d : ℕ) (A : Type) : Type
  | ret : A → Prog n d A
  | query : (v : Fin n) → (i : Fin d) → (Option (Fin n) → Prog n d A) → Prog n d A
  | sample : (m : ℕ) → 0 < m → (Fin m → Prog n d A) → Prog n d A
  | tick : Prog n d A → Prog n d A

namespace Prog
variable {n d : ℕ} {A B : Type}
def bind (p : Prog n d A) (f : A → Prog n d B) : Prog n d B :=
  match p with
  | .ret a => f a
  | .query v i k => .query v i (fun z => bind (k z) f)
  | .sample m hm k => .sample m hm (fun z => bind (k z) f)
  | .tick k => .tick (bind k f)
instance : Monad (Prog n d) where
  pure := .ret
  bind := bind

def charge (t : ℕ) (p : Prog n d A) : Prog n d A :=
  match t with
  | 0 => p
  | t+1 => .tick (charge t p)

def eval (O : Oracle n d) (reward : A → ℝ) : Prog n d A → ℝ
  | .ret a => reward a
  | .query v i k => eval O reward (k (O v i))
  | .sample m _ k => (∑ j, eval O reward (k j)) / m
  | .tick k => eval O reward k

def queriesOn (O : Oracle n d) : Prog n d A → ℕ
  | .ret _ => 0
  | .query v i k => 1 + queriesOn O (k (O v i))
  | .sample _ _ k => Finset.univ.sup (fun j => queriesOn O (k j))
  | .tick k => queriesOn O k

def timeOn (O : Oracle n d) : Prog n d A → ℕ
  | .ret _ => 0
  | .query v i k => 1 + timeOn O (k (O v i))
  | .sample _ _ k => 1 + Finset.univ.sup (fun j => timeOn O (k j))
  | .tick k => 1 + timeOn O k
end Prog

def acceptProb {n d : ℕ} (O : Oracle n d) (p : Prog n d Bool) : ℝ :=
  Prog.eval O (fun b => if b then 1 else 0) p

end InducedExpanderTest989.Structural


