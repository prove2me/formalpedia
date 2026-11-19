-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_NativeCertificateInterfaces
-- name    : EdgeSublinearMWIS_Main_NativeCertificateInterfaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T12:07:23.676653+00:00
-- url     : https://prove2.me/theorems/a2fca228-d6f7-41df-8294-834424b627c1
-- title:
--   Native certificate, recursion and polynomial resource interfaces
-- statement:
--   These definitions expose the certificate-family systems and feasible-point recovery input, the complete recursive node execution contract, and the natural polynomial resource predicates used by the native solver. For each program, the input predicates state its stored arrays, dimensions and arithmetic bounds. The polynomial predicate means exact equality with a polynomial having natural coefficients, not a freely assigned running-time field. All construction, recovery, recursion and resource-correctness claims remain separate theorem obligations.
-- source:
--   Bonnet–Chang, Theorem 2 and §5–6, pp. 2, 12–20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf. Exact native interfaces: https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs — RamCertificateFamilies.lean (Input), CertificateFamilyPrograms.lean, RamRecoverFeasibleSystem.lean (Input), RamStoredFeasibility.lean (Input), RamResourcePolynomial.lean (HasPolynomial), RamUniformSolverBounds.lean; https://github.com/EdouardBonnet/lax-263307/tree/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs — NativeNodeProtocol.lean (Executes), NativeNodeExecution.lean (Resources), NativeSelectedNear.lean (Program).

import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeOperationalInterfaces

-- Solutions.RAM_Lax109476Proofs_IntegerCertificates
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerCertificates

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding







def pairMatrix {m n : ℕ} (P : Program ℤ m n) :
    Matrix (Fin m ⊕ (Fin n ⊕ Bool)) (Fin n ⊕ Fin m) ℤ
  | .inl i => Sum.elim (P.A i) (fun _ => 0)
  | .inr (.inl j) => Sum.elim (fun _ => 0) (fun i => -P.A i j)
  | .inr (.inr false) => Sum.elim P.c (fun i => -P.b i)
  | .inr (.inr true) => Sum.elim (fun j => -P.c j) P.b

def pairBound {m n : ℕ} (P : Program ℤ m n) :
    (Fin m ⊕ (Fin n ⊕ Bool)) → ℤ
  | .inl i => P.b i
  | .inr (.inl j) => -P.c j
  | .inr (.inr _) => 0









def rayMatrix {m n : ℕ} (P : Program ℤ m n) :
    Matrix (Fin m ⊕ (Fin m ⊕ Unit)) (Fin n ⊕ Fin n) ℤ
  | .inl i => Sum.elim (P.A i) (fun _ => 0)
  | .inr (.inl i) => Sum.elim (fun _ => 0) (P.A i)
  | .inr (.inr _) => Sum.elim (fun _ => 0) (fun j => -P.c j)

def rayBound {m n : ℕ} (P : Program ℤ m n) :
    (Fin m ⊕ (Fin m ⊕ Unit)) → ℤ
  | .inl i => P.b i
  | .inr (.inl _) => 0
  | .inr (.inr _) => -1







end Lax109476Proofs.IntegerCertificates

end

-- Solutions.RAM_Lax109476Proofs_LexicographicMinima
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicMinima

open Lax109476.LinearProgram Lax109476.RationalCertificates









def equationProgram {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) :
    Program ℚ (m + m) n where
  A := Fin.addCases C (fun i j => -C i j)
  b := Fin.addCases b (fun i => -b i)
  c := 0







end Lax109476Proofs.LexicographicMinima

end

-- Solutions.RAM_Lax109476Proofs_IntegerPointRecovery
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerPointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding

def slackMatrix {m n : ℕ} (P : Program ℤ m n) : Matrix (Fin m) (Fin (n + m)) ℤ :=
  fun i => Fin.addCases (P.A i) (fun j => if j = i then 1 else 0)













end Lax109476Proofs.IntegerPointRecovery

end

-- Solutions.RAM_Lax109476Proofs_IndexedPointRecovery
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax109476Proofs.IndexedPointRecovery

open Lax109476.LinearProgram IntegerEncoding

def reindexProgram {κ ι : Type*} {r n : ℕ} (A : κ → ι → ℤ) (b : κ → ℤ)
    (er : κ ≃ Fin r) (ec : ι ≃ Fin n) : Program ℤ r n where
  A i j := A (er.symm i) (ec.symm j)
  b i := b (er.symm i)
  c := 0







end Lax109476Proofs.IndexedPointRecovery

end

-- Solutions.RAM_Lax109476Proofs_CertificateSearch
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

open scoped BigOperators

namespace Lax109476Proofs.CertificateSearch

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding IntegerCertificates

def unitFin : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv _ := Subsingleton.elim _ _

def pairRows (m n : ℕ) : (Fin m ⊕ (Fin n ⊕ Bool)) ≃ Fin (m + (n + 2)) :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _) finTwoEquiv.symm).trans
    finSumFinEquiv)).trans finSumFinEquiv

def rayRows (m : ℕ) : (Fin m ⊕ (Fin m ⊕ Unit)) ≃ Fin (m + (m + 1)) :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _) unitFin).trans
    finSumFinEquiv)).trans finSumFinEquiv



































end Lax109476Proofs.CertificateSearch

end

-- Solutions.RAM_Lax109476Proofs_CertificateFamilyPrograms
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

namespace Lax109476Proofs.CertificateFamilyPrograms

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates IndexedPointRecovery CertificateSearch

def optimal {m n : ℕ} (P : Program ℤ m n) : Program ℤ (m + (n + 2)) (n + m) :=
  reindexProgram (pairMatrix P) (pairBound P) (pairRows m n) finSumFinEquiv



def unbounded {m n : ℕ} (P : Program ℤ m n) : Program ℤ (m + (m + 1)) (n + n) :=
  reindexProgram (rayMatrix P) (rayBound P) (rayRows m) finSumFinEquiv













end Lax109476Proofs.CertificateFamilyPrograms

end

-- Solutions.RAM_Lax109476Proofs_RamStoredFeasibility
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamStoredFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep RationalArithmeticBounds IntegerEncoding



def Input {m n : ℕ} (P : Program ℚ m n) (σ : Env) : Prop :=
  RepresentsProgram P σ ∧ Extents "int.A" (m * n) σ ∧ Extents "int.b" m σ ∧
    Extents "int.c" n σ ∧ RamFeasibilityQuery.Workspace m n σ









end Lax109476Proofs.RamStoredFeasibility

end

-- Solutions.RAM_Lax109476Proofs_RamRecoveryThreshold
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRecoveryThreshold

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRationalScalars RamEllipsoidStep RationalArithmeticBounds

def State {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (σ : Env) : Prop :=
  Represents "point.A" (RamMatrixStorage.flatten P.A) σ ∧ Represents "point.b" (List.ofFn P.b) σ ∧
    Represents "point.x" (List.ofFn x) σ ∧ σ.vars "point.m" = m ∧ σ.vars "point.n" = n ∧
    σ.vars "point.k" = k



def Persistent {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (σ : Env) : Prop :=
  State P x k σ ∧ Workspace m n σ


















end Lax109476Proofs.RamRecoveryThreshold

end

-- Solutions.RAM_Lax109476Proofs_RamStandardPointRecovery
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped Matrix

namespace Lax109476Proofs.RamStandardPointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RationalArithmeticBounds LexicographicMinima
open RamRecoveryThreshold

def program {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : Program ℚ (m + m) n :=
  equationProgram (C.map (fun z => (z : ℚ))) (fun i => (b i : ℚ))







end Lax109476Proofs.RamStandardPointRecovery

end

-- Solutions.RAM_Lax109476Proofs_RamCertificateFamilies
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCertificateFamilies

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamCertificateSource CertificateFamilyPrograms







def Input {m n : ℕ} (P : Program ℤ m n) (r s : ℕ) (σ : Env) : Prop :=
  Data P σ ∧ Extents "system.A" (r * s) σ ∧ Extents "system.b" r σ









end Lax109476Proofs.RamCertificateFamilies

end

-- Solutions.RAM_Lax109476Proofs_RamRecoverFeasibleSystem
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRecoverFeasibleSystem

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEquationData RamEllipsoidStep RationalArithmeticBounds
open IntegerEncoding IntegerPointRecovery












def Input {m n : ℕ} (P : Program ℤ m n) (S N : ℕ) (σ : Env) : Prop :=
  Data P σ ∧ σ.vars "system.H" = 2 ^ (2 * S) ∧
    Extents "point.A" ((m + m) * (n + m)) σ ∧ Extents "point.b" (m + m) σ ∧
    Extents "point.x" (n + m) σ ∧ RamRecoveryThreshold.Workspace (m + m) (n + m) σ ∧
    (σ.arrs "cf.stack").length = N






end Lax109476Proofs.RamRecoverFeasibleSystem

end

-- Solutions.RAM_Lax109476Proofs_RamResourcePolynomial
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamResourcePolynomial

def HasPolynomial (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, p.eval n = f n













attribute [irreducible] HasPolynomial

open Lean Meta Elab Tactic

























end Lax109476Proofs.RamResourcePolynomial

end

-- Solutions.RAM_Lax263307Proofs_NativeMachineSegment
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeMachineSegment

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineTrace

/-- A finite sequence of phase transitions that may stop at a parent
continuation rather than halting the whole machine. -/
inductive Segment (B : ℕ) (cases : List Com) : ℕ → ℕ → Env → Env → Prop
  | nil (σ : Env) : Segment B cases 0 0 σ σ
  | step {σ μ τ : Env} {steps total cost : ℕ} (h : σ.vars "machine.running"=1)
      (j : Fin cases.length) (hj : σ.vars "machine.phase"=j.val)
      (rr : Run B cases[j.val] σ μ cost) (rest : Segment B cases steps total μ τ) :
      Segment B cases (steps+1) (cost+total) σ τ











end Lax263307Proofs.NativeMachineSegment

end

-- Solutions.RAM_Lax263307Proofs_NativeRoundTrace
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeRoundTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 RoundedOracleSearch NativeCoreMachine NativeMachineSegment

def Stopped {m : ℕ} (answer : Option (Finset (Fin m))) (σ : Env) : Prop :=
  σ.vars "machine.running"=1 ∧ σ.vars "machine.phase"=14 ∧ NativeTargetDriver.Reply answer σ









end Lax263307Proofs.NativeRoundTrace

end

-- Solutions.RAM_Lax263307Proofs_NativeOracleContext
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeOracleContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment

def RootData (base σ : Env) : Prop :=
  σ.vars "root.target"=base.vars "root.target" ∧ σ.vars "root.fuel"=base.vars "root.fuel"



























end Lax263307Proofs.NativeOracleContext

end

-- Solutions.RAM_Lax263307Proofs_NativeNodeProtocol
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeNodeProtocol

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment NativeOracleContext























structure Input {n : ℕ} (B D fuel S v : ℕ) (cfg : Config) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k : ℕ) (extent : String → ℕ) (front : List ℕ) (σ : Env) : Prop where
  protocol : Protocol B D S v cfg extent front σ
  order : σ.vars "graph.n"=n
  graph : Prefix (NativeWeightReduction.adjacency G) "search.graph" σ
  target : σ.vars "node.k"=k
  depth : σ.vars "recursion.fuel"=fuel

def Executes (B D fuel S v steps time : ℕ) (cfg : Config) (lp flow : List ℕ → List ℕ)
    (extent : String → ℕ) (eligible : Eligible) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] k (front : List ℕ) σ,
    eligible fuel n G k front.length → Input B D fuel S v cfg G k extent front σ →
    σ.vars "machine.running"=1 → σ.vars "machine.phase"=1 →
    ∃ τ s t,Segment B (phases cfg) s t σ τ ∧ s≤ steps ∧ t≤ time ∧
      NativeRoundTrace.Stopped (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k) τ ∧
      Protocol B D S v cfg extent front τ ∧ RootData σ τ ∧ GraphData G τ





end Lax263307Proofs.NativeNodeProtocol

end


