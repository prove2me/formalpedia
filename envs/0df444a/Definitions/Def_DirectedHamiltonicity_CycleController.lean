-- Prove2me | Definitions.Def_DirectedHamiltonicity_CycleController
-- name    : DirectedHamiltonicity_CycleController
-- status  : Definition
-- author  : @Soh Kumabe
-- created : 2026-11-27T03:27:32.997802+00:00
-- url     : https://prove2.me/theorems/649cc585-7699-5729-8f13-0370f251cbbd
-- title:
--   Bounded control programs with finite parity-subroutine calls
-- statement:
--   A finite control program composes structured log-cost instructions, indexed writes to a query input array, loops and fresh calls to a fixed bounded RAM. The dynamics charge a guest its complete allowance, enforce polynomial caller word lengths, and give the application-specific uniform realization predicate.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, Section 2, proof of Theorem 1. https://arxiv.org/html/2609.39062v2#S2

import Definitions.Def_DirectedHamiltonicity_CycleSearch
import Definitions.Def_LogCostRAM_StructuredExecution

namespace DirectedHamiltonicity.Main.CycleReduction.CoinWindow

/-- A bounded virtual coin tape. Missing bits of the host tape count as zero inside the window. -/
def window (coins : List Bool) (start length : ℕ) : List Bool :=
  List.ofFn fun i : Fin length => coins[start+i.val]?.getD false

end DirectedHamiltonicity.Main.CycleReduction.CoinWindow

namespace DirectedHamiltonicity.Main.CycleReduction.OuterMachine

open TargetedSamplers TargetedSamplers.Structured

structure Data where
  bank : Store
  port : ℕ → ℕ
  epoch : ℕ

def Data.publish (d : Data) (a b : ℕ) : Data :=
  {d with port := Function.update d.port (d.bank.mem a) (d.bank.mem b)}

def Data.returnBit (d : Data) (bit : Bool) : Data :=
  {d with bank := (d.bank.write 0 0).write 5 bit.toNat, epoch := d.epoch+1}

inductive Code where
  | pure (c : Cmd)
  | port (key src : ℕ)
  | query
  | seq (first second : Code)
  | branch (a b : ℕ) (yes no : Code)
  | loop (a b : ℕ) (body : Code)

/-- The outer instruction set admits only bounded-word structured RAM blocks, a data transfer
to the input port and one fixed, independently restarted bit subroutine. -/
inductive Eval (Q : Program) (τ : Tapes) (w : ℕ) : Code → Data → Data → ℕ → Prop
  | pure {d : Data} {c t k} : d.bank.Fits w → Exec τ (fun v => v.Fits w) c d.bank t k →
      Eval Q τ w (.pure c) d {d with bank := t} k
  | port (d : Data) (a b : ℕ) : d.bank.Fits w → Eval Q τ w (.port a b) d (d.publish a b) 1
  | query (d : Data) (x : List Bool) (v : Bool) : d.bank.Fits w → d.epoch.size≤w →
      d.bank.mem 1=1 → d.bank.mem 2=x.length → (∀ i<x.length, d.port i=bitVal x[i]?) →
      Q.RunsIn (runTapes x (CoinWindow.window τ.coins (d.bank.mem 3) (d.bank.mem 4))) (d.bank.mem 0) (some [v]) →
      Eval Q τ w .query d (d.returnBit v) (d.bank.mem 0+1)
  | seq {c f d u t k l} : Eval Q τ w c d u k → Eval Q τ w f u t l → Eval Q τ w (.seq c f) d t (k+l)
  | yes {a b c f d t k} : d.bank.Fits w → d.bank.mem a≤d.bank.mem b → Eval Q τ w c d t k →
      Eval Q τ w (.branch a b c f) d t (1+k)
  | no {a b c f d t k} : d.bank.Fits w → ¬d.bank.mem a≤d.bank.mem b → Eval Q τ w f d t k →
      Eval Q τ w (.branch a b c f) d t (1+k+1)
  | done {a b c d} : d.bank.Fits w → d.bank.mem a≤d.bank.mem b → Eval Q τ w (.loop a b c) d d 1
  | again {a b c d m t k l} : d.bank.Fits w → ¬d.bank.mem a≤d.bank.mem b → Eval Q τ w c d m k →
      Eval Q τ w (.loop a b c) m t l → Eval Q τ w (.loop a b c) d t (1+k+1+l)

def initial : Data := ⟨⟨fun _ => 0,[]⟩,fun _ => 0,0⟩

/-- Uniform source-level bounds on the caller's word lengths and charged control steps. -/
def BoundedController (Q : Program) (A k : ℕ) :=
  ∃ (c : Code) (width work : Polynomial ℕ), ∀ (n : ℕ) (adj : Fin n → Fin n → Bool) (coins : List Bool),
    ∃ (d : Data) (j : ℕ), Eval Q (runTapes (encodeDigraph n adj) coins) (width.eval (n+1)) c initial d j ∧
      d.bank.out=[answer Q A k adj coins] ∧ j ≤ searchWork A k n*work.eval (n+1)

end DirectedHamiltonicity.Main.CycleReduction.OuterMachine


