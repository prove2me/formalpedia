-- Prove2me | Definitions.Def_DetDLP_D4Plan
-- name    : DetDLP_D4Plan
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:52:03.943605+00:00
-- url     : https://prove2.me/theorems/0ef434a1-8098-4bf9-8904-68fbec7d0de5
-- title:
--   A counted family of guarded terminal residuals
-- statement:
--   A plan assigns a weighted residual network to each finite rank. Header and branch words carry the parameters, weights, and vertex descriptors used by the enumerator and digit evaluator. Their contracts distinguish polynomial workspace from the permitted exponential running time.

import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_TerminalBTN
import Definitions.Def_DetDLP_FactorBase
set_option autoImplicit false
namespace DetDLP.D4Plan
open AppendixD4 ResidualScalarOracle Polynomial OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
noncomputable section
structure Input (C c : ℕ) where
  b : ℕ
  m : ℕ
  k : ℕ
  S : ℕ
  p : ℕ
  l : ℕ
  desc : Bits
  G : Graph
  spec : LookupSeparatorSpec G m k S (C * Nat.ceil ((b:ℝ)^((3:ℝ)/4)))
  A : Tensor G (Fin l → ℕ)
  hb : 2 ≤ b
  hm : 1 ≤ m
  hk : 1 ≤ k
  bm : blockCount b ≤ C*m
  mb : m ≤ C*blockCount b
  hS : S ≤ C*m*b
  upper : 4*m*k ≤ C*b
  lower : b ≤ C*(4*m*k)
  hp : 1 ≤ p
  pS : p ≤ S
  hl : 1 ≤ l
  lm : l ≤ C*m
  nV : G.nV ≤ (S+desc.length+1)^c
  bounded : ∀ v t i, A v t i < 2^p
variable {C c : ℕ} (x : Input C c)
def size := x.S+x.desc.length
def input := encodeTerminalBTNInstance x.desc x.G x.b x.m x.k x.S x.p x.l x.spec.lookupVerts
def entry (E : PrimitiveMachine) (o : Fin E.tapeCount) := ∀ v t, RunsWithin E o (encodePortQuery x.desc v.val (List.ofFn t)) (encodeNatListBin (List.ofFn (x.A v t))) (polyBound c (size x)) (polyBound c (size x))
def Z := BTNContract x.G (fun v t => ∑ i : Fin x.l, monomial i.val (x.A v t i : ℤ))
def answer := encodeNatListBin (List.ofFn fun i : Fin x.l => ((Z x).coeff i.val : ZMod (2^x.p)).val)
def time (K : ℕ) := polyBound K (size x)*(2:ℝ)^((K:ℝ)*((x.b:ℝ)/x.m+(x.b:ℝ)/Real.sqrt (logSafe x.m)))
/-- Descriptors name the individual vertex tensors; no evaluation table is stored in a branch. -/
structure Plan where
  f : ℤ[X]
  hf : f.Monic
  deg : f.natDegree = 4*Nat.clog 2 x.S
  zero : Fin f.natDegree
  zero_val : zero.val = 0
  guard : ℕ
  N : ℕ
  R : Fin N → Graph
  V : (u : Fin N) → Tensor (R u) (B f x.l (guard+x.p))
  w : Fin N → B f x.l (guard+x.p)
  source : (u : Fin N) → Fin (R u).nV → Bits
  edges : ∀ u, (R u).nE = 4*x.m*x.k
  vertices : ∀ u, (R u).nV ≤ 4*x.m+64^(Nat.clog 32 (4*x.m))
  degree : ∀ u, (R u).maxDeg*x.m ≤ 1217*(C+1)^3*x.b
  correct : answer x = encodeNatListBin (List.ofFn fun j : Fin x.l => word f x.l (guard+x.p) hf (∑ u, w u * BTNContract (R u) (V u)) j zero / 2^guard)
variable {x} (P : Plan x)
def branch (u : Fin P.N) := Encoding.encodeList id [P.R u |>.encode, residue P.f x.l (P.guard+x.p) P.hf (P.w u), Encoding.encodeList id (List.ofFn (P.source u))]
def header := Encoding.encodeList id [countWord P.N,countWord P.guard,polynomialBits P.f]
def rankQuery (x : Input C c) (j : ℕ) := Encoding.encodeList id [input x, countWord j]
def h (u : Fin P.N) := digitWidth (4*x.m*x.k) (P.R u).nV
def J (u : Fin P.N) := digits (P.guard+x.p) (h P u)
def digitDesc (u : Fin P.N) (a : Fin (P.R u).nV → Fin (J P u)) := Encoding.encodeList id [input x,header P,branch P u,encodeNatListBin (List.ofFn fun v => (a v).val)]
variable (E : PrimitiveMachine) (o : Fin E.tapeCount)
def Enumerates (A : PrimitiveMachine) (oa : Fin A.tapeCount) (K : ℕ) (P : Plan x) :=
  let scale := polyBound K (size x)
  let t := scale*(2:ℝ)^((K:ℝ)*((x.b:ℝ)/x.m))
  RunsWithin A oa (rankQuery x 0) (header P) t scale ∧ (∀ u, RunsWithin A oa (rankQuery x (u.val+1)) (branch P u) t scale) ∧
  ((P.N:ℝ) ≤ Real.exp ((K:ℝ)*((x.b:ℝ)/(Nat.clog 2 x.S:ℝ)^(7/40:ℝ)+(Nat.clog 2 x.S:ℝ)^(13/10:ℝ)))) ∧
  (∀ u, ((J P u^(P.R u).nV:ℕ):ℝ) ≤ Real.exp ((K:ℝ)*(Nat.clog 2 x.S:ℝ)^(13/10:ℝ))) ∧
  ((P.guard:ℝ) ≤ scale) ∧ ((header P).length:ℝ) ≤ scale ∧
  (∀ u a, ((digitDesc P u a).length:ℝ) ≤ scale) ∧
  (∀ u, precision P.f x.l (P.R u) (h P u) (4*x.m*x.k) ≤ K*x.b ∧ spacing P.f (P.R u)*x.l ≤ K*x.b)
/-- A descriptor identifies either an original lookup entry or a stopped, pinned core call.
The concrete source evaluator is uniform across all ranks and all instances. -/
def Sources (B₀ : PrimitiveMachine) (ob : Fin B₀.tapeCount) (K : ℕ) (P : Plan x) := ∀ u v t,
  RunsWithin B₀ ob (encodePortQuery (P.source u v) v.val (List.ofFn t)) (residue P.f x.l (P.guard+x.p) P.hf (P.V u v t))
    (polyBound K (size x)*(2:ℝ)^((K:ℝ)*((x.b:ℝ)/x.m))) (polyBound K (size x))
def Digits (D : PrimitiveMachine) (od : Fin D.tapeCount) (K : ℕ) (P : Plan x) := ∀ u a,
  ∃ T : ℕ, 1 ≤ T ∧ (T:ℝ) ≤ polyBound K (size x)*(2:ℝ)^((K:ℝ)*((x.b:ℝ)/x.m)) ∧
  BTNEntryEvaluable (digitDesc P u a) (P.R u) (precision P.f x.l (P.R u) (h P u) (4*x.m*x.k)) (spacing P.f (P.R u)*x.l)
    (query P.f x.l (P.guard+x.p) P.hf (P.R u) (P.V u) (J P u) (h P u) (4*x.m*x.k) a) D od T (((x.b+(digitDesc P u a).length:ℕ):ℝ)^K)
end
end DetDLP.D4Plan


