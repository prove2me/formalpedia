-- Prove2me | Definitions.Def_MatchingNearLinear_Glauber_Sampler
-- name    : MatchingNearLinear_Glauber_Sampler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T15:56:54.40833+00:00
-- url     : https://prove2.me/theorems/d17211da-89f6-4a49-990f-8ca0a675a469
-- title:
--   Metered mate-array sampling with doubling schedules
-- statement:
--   The random-choice RAM primitives are random-access reads and writes, arithmetic, comparison, exact uniform edge selection and Bernoulli draws. A metered computation returns its value and the list of primitives it actually executes. The mate array holds a matched neighbor or an unmatched marker per vertex. A step selects an original edge, erases it when present, then inserts it with probability $\lambda_e/(1+\lambda_e)$ when both endpoints are free. Initialization reads the labeled input and initializes the array; output enumerates occupied edges. The execution starts from the empty matching.
--
--   $$\Pr(\text{tape})=\prod_{i=1}^T\frac1m p_{e_i}^{B_i}(1-p_{e_i})^{1-B_i},\qquad p_e=\lambda_e/(1+\lambda_e).$$
--
--   The output law is the push-forward of this tape law through execution, and work is the executed primitive count plus schedule computation. A doubling loop computes $L(x)=\min\{l:x\le2^l\}$ using only additions and comparisons. An independent operational relation certifies its terminating trace; interpreter fuel is a termination certificate, not a RAM oracle. Parameter-only natural constants give schedules $KmL(n/\varepsilon)^2$ and $Km(L(n)^2+L(1/\varepsilon))$. Variable-length decoding is additionally charged, as in the source; no finite-bit bound is claimed.
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Theorem 1.1 implementation, printed p.2 (PDF p.4); §2.3, printed p.9 (PDF p.11); §4, printed p.22 (PDF p.24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_MatchingModel

set_option autoImplicit false

namespace MatchingNearLinear.Glauber


open scoped BigOperators
noncomputable section
open Classical

/-- Each constructor is one source-model RAM primitive, including random access. -/
inductive Primitive where
  | read | write | add | multiply | divide | compare | uniform | bernoulli
  deriving DecidableEq

abbrev Metered (α : Type) := α × List Primitive

def ret {α : Type} (x : α) : Metered α := (x, [])
def bind {α β : Type} (x : Metered α) (f : α → Metered β) : Metered β :=
  let y := f x.1
  (y.1, x.2 ++ y.2)
instance : Monad Metered where
  pure := ret
  bind := bind

def primitive {α : Type} (op : Primitive) (value : α) : Metered α := (value, [op])

abbrev Mates (n : ℕ) := Fin n → Option (Fin n)

def readMate {n : ℕ} (M : Mates n) (v : Fin n) : Metered (Option (Fin n)) := primitive .read (M v)
def writeMate {n : ℕ} (M : Mates n) (v : Fin n) (x : Option (Fin n)) : Metered (Mates n) :=
  primitive .write (Function.update M v x)

def initializeMates {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) : Metered (Mates n) := do
  -- Read the labeled input once. Variable-length decoding is charged separately.
  let _ ← (List.finRange m).foldlM (fun (_ : Unit) e => do
    let _ ← primitive .read (G.u e)
    let _ ← primitive .read (G.v e)
    let _ ← primitive .read (lam e)
    let _ ← primitive .compare true
    let _ ← primitive .add (e.val+1)
    pure ()) ()
  let _ ← primitive .compare false
  let M ← (List.finRange n).foldlM (fun M v => do
    let _ ← primitive .compare true
    let M ← writeMate M v none
    let _ ← primitive .add (v.val+1)
    pure M) (fun _ => none)
  let _ ← primitive .compare false
  pure M

/-- A tape supplies the outcomes of the exact uniform choice and the Bernoulli draw.
The execution uses mate-array reads and writes, not a matching-membership oracle. -/
def mateStep {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ)
    (M : Mates n) (choice : Fin m × Bool) : Metered (Mates n) := do
  let e ← primitive .uniform choice.1
  let u ← primitive .read (G.u e)
  let v ← primitive .read (G.v e)
  let a ← primitive .read (lam e)
  let den ← primitive .add (1+a)
  let p ← primitive .divide (a/den)
  let mark ← primitive .bernoulli (p, choice.2)
  let mu ← readMate M u
  let occupied ← primitive .compare (mu = some v)
  let M ← if occupied then do
    let M ← writeMate M u none
    writeMate M v none
    else pure M
  let mu ← readMate M u
  let mv ← readMate M v
  let freeU ← primitive .compare (mu = none)
  let freeV ← primitive .compare (mv = none)
  let insertable ← primitive .compare (mark.2 ∧ freeU ∧ freeV)
  if insertable then do
    let M ← writeMate M u (some v)
    writeMate M v (some u)
  else pure M

def readOutputBuffer {n m : ℕ} (G : Input n m) (M : Mates n) : Metered (List (Fin m)) := do
  let out ← (List.finRange m).foldlM (fun S e => do
    let u ← primitive .read (G.u e)
    let v ← primitive .read (G.v e)
    let mu ← readMate M u
    let occupied ← primitive .compare (mu = some v)
    let S ← if occupied then primitive .write (e :: S) else pure S
    let _ ← primitive .compare true
    let _ ← primitive .add (e.val+1)
    pure S) []
  let _ ← primitive .compare false
  pure out

/-- Decode the emitted edge buffer as a mathematical set; no set-insertion oracle is run. -/
def readOutput {n m : ℕ} (G : Input n m) (M : Mates n) : Metered (Config m) :=
  let out := readOutputBuffer G M
  (out.1.toFinset, out.2)

/-- Executes precisely T updates and then enumerates the occupied edges. -/
def execute {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (T : ℕ)
    (tape : Fin T → Fin m × Bool) : Metered (Config m) := do
  let M ← initializeMates G lam
  let M ← (List.finRange T).foldlM (fun M i => do
    let _ ← primitive .compare true
    let M ← mateStep G lam M (tape i)
    let _ ← primitive .add (i.val + 1)
    pure M) M
  let _ ← primitive .compare false
  readOutput G M

def tapeWeight {m T : ℕ} (lam : Fin m → ℝ) (tape : Fin T → Fin m × Bool) : ℝ :=
  ∏ i, (1/(m:ℝ)) * (if (tape i).2 then lam (tape i).1 / (1+lam (tape i).1)
    else 1-lam (tape i).1 / (1+lam (tape i).1))

/-- The output law is the push-forward of independent program choices through execution. -/
def outputLaw {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (T : ℕ) (S : Config m) : ℝ :=
  ∑ tape : Fin T → Fin m × Bool, if (execute G lam T tape).1 = S then tapeWeight lam tape else 0

/-- Termination certificate for doubling. The search itself uses doubling and comparisons. -/
def doublingLength (x : ℝ) : ℕ := Nat.find (show ∃ k : ℕ, x ≤ (2:ℝ)^k from
  let ⟨k,hk⟩ := pow_unbounded_of_one_lt x (by norm_num : (1:ℝ) < 2)
  ⟨k, hk.le⟩)

/-- Certified interpreter for the deterministic doubling loop; fuel is a semantic termination
certificate. It is not read by the RAM program and is not a charged primitive or oracle. -/
def doublingLoop (x : ℝ) : ℕ → ℝ → ℕ → Metered ℕ
  | 0, _, k => ret k
  | fuel+1, v, k => do
      let done ← primitive .compare (x ≤ v)
      if done then pure k else do
        let v ← primitive .add (v+v)
        let k ← primitive .add (k+1)
        doublingLoop x fuel v k

def computeLength (x : ℝ) : Metered ℕ := doublingLoop x (doublingLength x + 1) 1 0

/-- Horizon computation contains no logarithm/ceiling/mixing-time RAM instruction. -/
def nonuniformSchedule (K m n : ℕ) (eps : ℝ) : Metered ℕ := do
  let x ← primitive .divide ((n:ℝ)/eps)
  let l ← computeLength x
  let ll ← primitive .multiply (l*l)
  let km ← primitive .multiply (K*m)
  primitive .multiply (km*ll)

def uniformSchedule (K m n : ℕ) (eps : ℝ) : Metered ℕ := do
  let l ← computeLength (n:ℝ)
  let x ← primitive .divide (1/eps)
  let h ← computeLength x
  let ll ← primitive .multiply (l*l)
  let s ← primitive .add (ll+h)
  let km ← primitive .multiply (K*m)
  primitive .multiply (km*s)

/-- Costs are the length of the executed primitive trace plus schedule computation. -/
def samplingWork {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ)
    (schedule : Metered ℕ) (tape : Fin schedule.1 → Fin m × Bool) : ℕ :=
  schedule.2.length + (execute G lam schedule.1 tape).2.length


/-- Small-step semantics of an unbounded deterministic doubling loop. This relation has
no length oracle and no fuel instruction; the metered interpreter returns its finite trace. -/
inductive DoublingExecution (x : ℝ) : ℝ → ℕ → Metered ℕ → Prop where
  | stop (v : ℝ) (k : ℕ) (h : x ≤ v) :
      DoublingExecution x v k (k, [.compare])
  | step (v : ℝ) (k : ℕ) (out : Metered ℕ) (h : v < x)
      (next : DoublingExecution x (v+v) (k+1) out) :
      DoublingExecution x v k (out.1, [.compare, .add, .add] ++ out.2)

end
end MatchingNearLinear.Glauber


