-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_ArrayRAM
-- name    : PandoraKnapsack_Skipping_ArrayRAM
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-25T17:38:20.983384+00:00
-- url     : https://prove2.me/theorems/6447ce1b-b7dc-49f9-8489-e4b120e2c3d6
-- title:
--   Typed indexed-array language for the stochastic knapsack algorithm
-- statement:
--   Natural expressions compute indices and real expressions operate on data and indexed tables. A source execution records its cost including memory-address walks, comparisons, uniform draws, and coefficient queries. A bounded loop snapshots its limit before the first iteration.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, explicit implementation of Algorithm 1 and the polynomial-time clause of Theorem 5.1 under the machine model in Prove2Me theorem 7898d376-37b2-42fd-8375-13696ef594ef. Derived implementation for the dyadic approximate solver.

import Definitions.Def_PandoraKnapsack_Skipping_StructuredRAM

namespace PandoraKnapsack.Skipping.ArrayRAM

structure Store where
  ns : ℕ → ℕ
  rs : ℕ → ℝ
  tab : Fin 16 → ℕ → ℝ
  out : ℕ → ℝ
  draws : ℕ

noncomputable def initial (n m T : ℕ) : Store :=
  ⟨fun k => if k = 0 then n else if k = 1 then m else 0,
   fun k => if k = 0 then T else 0, fun _ _ => 0,
   fun k => (initState n m T).core.mem k, 0⟩

def Store.setN (s : Store) (r v : ℕ) := {s with ns := Function.update s.ns r v}
def Store.setR (s : Store) (r : ℕ) (v : ℝ) := {s with rs := Function.update s.rs r v}
def Store.put (s : Store) (t : Fin 16) (i : ℕ) (v : ℝ) :=
  {s with tab := Function.update s.tab t (Function.update (s.tab t) i v)}
def Store.writeOut (s : Store) (i : ℕ) (v : ℝ) := {s with out := Function.update s.out i v}

inductive N where
  | lit (c : ℕ)
  | var (r : ℕ)
  | add (a b : N)
  | mul (a b : N)
instance {i : ℕ} : OfNat N i := ⟨.lit i⟩
instance : Add N := ⟨.add⟩
instance : Mul N := ⟨.mul⟩

def N.eval (s : Store) : N → ℕ
  | .lit k => k
  | .var i => s.ns i
  | .add a b => a.eval s + b.eval s
  | .mul a b => a.eval s * b.eval s

inductive R where
  | lit (c : ℝ)
  | var (r : ℕ)
  | nat (a : N)
  | get (table : Fin 16) (a : N)
  | add (a b : R)
  | sub (a b : R)
  | mul (a b : R)
  | div (a b : R)

noncomputable instance {i : ℕ} : OfNat R i := ⟨.lit i⟩
instance : Add R := ⟨.add⟩
instance : Sub R := ⟨.sub⟩
instance : Mul R := ⟨.mul⟩
instance : Div R := ⟨.div⟩

noncomputable def R.eval (s : Store) : R → ℝ
  | .lit z => z
  | .var k => s.rs k
  | .nat a => a.eval s
  | .get t i => s.tab t (i.eval s)
  | .add a b => a.eval s + b.eval s
  | .sub a b => a.eval s - b.eval s
  | .mul a b => a.eval s * b.eval s
  | .div a b => a.eval s / b.eval s

inductive C where
  | skip
  | seq (a b : C)
  | letN (r : ℕ) (a : N)
  | letR (r : ℕ) (e : R)
  | put (table : Fin 16) (idx : N) (e : R)
  | out (idx : N) (e : R)
  | itePos (e : R) (yes no : C)
  | forN (idx : ℕ) (bound : N) (body : C)
  | whilePos (e : R) (body : C)
  | value (dst : ℕ) (i : N)
  | cost (dst : ℕ) (i j : N)
  | cdf (dst : ℕ) (i j : N) (e : R)
  | truncMean (dst : ℕ) (i j : N) (e : R)
  | uniform (dst : ℕ)

def tableOffset (t : Fin 16) (i : ℕ) := 1+16*i+t.val

def N.work : N → ℕ
  | .lit _ | .var _ => 1
  | .add a b | .mul a b => a.work+b.work+1

def R.work (s : Store) : R → ℕ
  | .lit _ | .var _ => 1
  | .nat a => a.work
  | .get t i => i.work+4+(5*tableOffset t (i.eval s)+5)
  | .add a b | .sub a b | .mul a b | .div a b => a.work s + b.work s + 1

variable {n m T : ℕ}

noncomputable def valueAt (I : Instance n m T) (i : ℕ) : ℝ :=
  match ptrIndex n (i : ℤ) with | some k => I.value k | none => 0

noncomputable def pairAt (n m : ℕ) (i j : ℕ) (f : Fin n → Fin m → ℝ) : ℝ :=
  match ptrIndex n (i : ℤ), ptrIndex m (j : ℤ) with | some k,some l => f k l | _,_ => 0

def indexWork (s : Store) (i : N) := i.work + (5*i.eval s + 4)

/-- The for-loop snapshots its bound once, sets idx before each iteration, and leaves idx equal
to that bound. Costs count the real pointer machine's executed instructions. -/
inductive Exec (I : Instance n m T) (ω : ℕ → ℝ) : C → Store → Store → ℕ → Prop where
  | skip (s) : Exec I ω .skip s s 0
  | seq {a b s u v k l} : Exec I ω a s u k → Exec I ω b u v l → Exec I ω (.seq a b) s v (k+l)
  | letN (s r a) : Exec I ω (.letN r a) s (s.setN r (a.eval s)) (a.work+1)
  | letR (s r e) : Exec I ω (.letR r e) s (s.setR r (e.eval s)) (e.work s+1)
  | put (s t i e) : Exec I ω (.put t i e) s (s.put t (i.eval s) (e.eval s))
      (i.work+4+e.work s+(5*tableOffset t (i.eval s)+5))
  | out (s i e) : Exec I ω (.out i e) s (s.writeOut (i.eval s) (e.eval s))
      (i.work+e.work s+(5*i.eval s+5))
  | ite_true {s v e yes no k} : 0 < e.eval s → Exec I ω yes s v k →
      Exec I ω (.itePos e yes no) s v (e.work s+1+k+1)
  | ite_false {s v e yes no k} : e.eval s ≤ 0 → Exec I ω no s v k →
      Exec I ω (.itePos e yes no) s v (e.work s+1+k)
  | while_false {s e body} : e.eval s ≤ 0 → Exec I ω (.whilePos e body) s s (e.work s+1)
  | while_true {s u v e body k l} : 0 < e.eval s → Exec I ω body s u k →
      Exec I ω (.whilePos e body) u v l → Exec I ω (.whilePos e body) s v (e.work s+1+k+1+l)
  | forN (idx : ℕ) (bound : N) (body : C) (ss : ℕ → Store) (ks : ℕ → ℕ) :
      (∀ j < bound.eval (ss 0), Exec I ω body ((ss j).setN idx j) (ss (j+1)) (ks j)) →
      Exec I ω (.forN idx bound body) (ss 0) ((ss (bound.eval (ss 0))).setN idx (bound.eval (ss 0)))
        (bound.work+4+5*(bound.eval (ss 0))+∑ j ∈ Finset.range (bound.eval (ss 0)), ks j)
  | value (s dst i) : Exec I ω (.value dst i) s (s.setR dst (valueAt I (i.eval s)))
      (indexWork s i+1)
  | cost (s dst i j) : Exec I ω (.cost dst i j) s
      (s.setR dst (pairAt n m (i.eval s) (j.eval s) I.cost)) (indexWork s i+indexWork s j+1)
  | cdf (s dst i j e) : Exec I ω (.cdf dst i j e) s
      (s.setR dst (pairAt n m (i.eval s) (j.eval s) (fun a b => PandoraKnapsack.Skipping.cdf I a b (e.eval s))))
      (indexWork s i+indexWork s j+e.work s+1)
  | truncMean (s dst i j e) : Exec I ω (.truncMean dst i j e) s
      (s.setR dst (pairAt n m (i.eval s) (j.eval s) (fun a b => PandoraKnapsack.Skipping.truncMean I a b (e.eval s))))
      (indexWork s i+indexWork s j+e.work s+1)
  | uniform (s dst) : Exec I ω (.uniform dst) s {s.setR dst (ω s.draws) with draws := s.draws+1} 1

end PandoraKnapsack.Skipping.ArrayRAM


