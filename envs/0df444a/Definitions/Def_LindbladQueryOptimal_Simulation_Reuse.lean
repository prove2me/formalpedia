-- Prove2me | Definitions.Def_LindbladQueryOptimal_Simulation_Reuse
-- name    : LindbladQueryOptimal_Simulation_Reuse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:42.310857+00:00
-- url     : https://prove2.me/theorems/0639469f-1e6d-4f63-8e66-c452d371cd21
-- title:
--   Shared-private reuse blocks and layerwise SELECT query programs
-- statement:
--   For a public space $\mathcal H_P$, a private space $\mathcal H_C$, a unitary $S$ and a positive reuse length $s$, construct the actual stage $J_kSJ_k^\dagger+I-J_kJ_k^\dagger$ on $(\mathbb C^s\otimes\mathcal H_P)\oplus\mathcal H_C$. The private space is shared by every stage. Fourier distribution and recombination define $R_s$, whose zero-reuse-label public block is $P_s$. Define
--   $$g_s(A)=\frac1s\sum_{j=0}^{s-1}A^j,\quad \widetilde P=\sum_{j=1}^{s_{\max}}\lambda_jP_j,\quad p_{\rm err}(A)=\sum_{j=1}^{s_{\max}}\lambda_jg_j(A),\quad \Lambda=\sum_j|\lambda_j|.$$
--   A query program consists of known unitaries and controlled applications of the same unknown $S$ on orthogonal spectator sectors. Each such SELECT layer counts as one controlled application, independently of its number of spectator labels. Its complement is fixed. The program, its known isometric layouts, and its query counter are defined before any accuracy or block-encoding assertion.
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Eqs. (21)–(32), pp. 10–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Core

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev ReuseSpace (s p c : ℕ) := Sum (Fin s × Fin p) (Fin c)

def reuseEmbedding {s p c : ℕ} (k : Fin s) :
    Matrix (ReuseSpace s p c) (Sum (Fin p) (Fin c)) ℂ := fun x y =>
  match x,y with
  | .inl (l,a),.inl b => if l = k ∧ a = b then 1 else 0
  | .inr a,.inr b => if a = b then 1 else 0
  | _,_ => 0

/-- The actual shared-private stage (23), including the inactive public branches. -/
def reuseStage {s p c : ℕ} (S : Op (Sum (Fin p) (Fin c))) (k : Fin s) :
    Op (ReuseSpace s p c) :=
  let J := reuseEmbedding (p := p) (c := c) k
  J * S * Jᴴ + (1 - J * Jᴴ)

def reuseFourier (s p c : ℕ) : Op (ReuseSpace s p c) := fun x y =>
  match x,y with
  | .inl (k,a), .inl (l,b) => if a = b then
      (Real.sqrt (s : ℝ) : ℂ)⁻¹ *
        Complex.exp (2 * Real.pi * Complex.I * (k.val : ℂ) * (l.val : ℂ) / (s : ℂ)) else 0
  | .inr a,.inr b => if a = b then 1 else 0
  | _,_ => 0

/-- Fourier distribution, chronological reuse, Fourier recombination; zero private input. -/
def reuseUnitary {p c : ℕ} (s : ℕ) (S : Op (Sum (Fin p) (Fin c))) :
    Op (ReuseSpace s p c) :=
  (reuseFourier s p c)ᴴ *
    ((List.ofFn (reuseStage (s := s) S)).foldl (fun A U => U*A) 1) *
    reuseFourier s p c

def reusePublic (s p c : ℕ) : Matrix (ReuseSpace s p c) (Fin p) ℂ := fun x y =>
  match x with | .inl (k,a) => if k.val = 0 ∧ a = y then 1 else 0 | .inr _ => 0

def reuseBlock {p c : ℕ} (s : ℕ) (S : Op (Sum (Fin p) (Fin c))) : Op (Fin p) :=
  (reusePublic s p c)ᴴ * reuseUnitary s S * reusePublic s p c

def movingAverage {a : Type} [Fintype a] [DecidableEq a] (s : ℕ) (A : Op a) : Op a :=
  (s : ℂ)⁻¹ • ∑ j ∈ Finset.range s, A^j

def lcuNormalization {s : ℕ} (lam : Fin s → ℂ) : ℝ := ∑ j, ‖lam j‖

def lcuReuse {p c s : ℕ} (lam : Fin s → ℂ) (S : Op (Sum (Fin p) (Fin c))) : Op (Fin p) :=
  ∑ j, lam j • reuseBlock (j.val+1) S

def reuseErrorPolynomial {s : ℕ} {a : Type} [Fintype a] [DecidableEq a]
    (lam : Fin s → ℂ) (A : Op a) : Op a := ∑ j, lam j • movingAverage (j.val+1) A

/-- One controlled application of S, with any fixed spectator labels. The
orthogonal copies are simultaneously acted on by the same S, so this is one
layerwise SELECT query, not one query per copy. The complement is fixed. -/
structure QueryLayer (w a : ℕ) where
  copies : ℕ
  embed : Fin copies → Matrix (Fin w) (Fin a) ℂ
  orthogonal : ∀ i j, (embed i)ᴴ * embed j = if i = j then 1 else 0

def queryLayerMatrix {w a : ℕ} (Q : QueryLayer w a) (S : Op (Fin a)) : Op (Fin w) :=
  1 - ∑ j, Q.embed j * (Q.embed j)ᴴ + ∑ j, Q.embed j * S * (Q.embed j)ᴴ

inductive ReuseGate (w a : ℕ) where
  | known (U : Op (Fin w)) (hU : unitary U)
  | select (Q : QueryLayer w a)

def reuseProgramMatrix {w a : ℕ} (gates : List (ReuseGate w a)) (S : Op (Fin a)) : Op (Fin w) :=
  gates.foldl (fun A g => (match g with
    | .known U _ => U | .select Q => queryLayerMatrix Q S) * A) 1

def reuseQueryCount {w a : ℕ} (gates : List (ReuseGate w a)) : ℕ :=
  (gates.map fun g => match g with | .known .. => 0 | .select .. => 1).sum

/-- Coordinate identification only; all circuit steps are selected before S. -/
def sumCoordinates (p c : ℕ) : Fin (p+c) ≃ Sum (Fin p) (Fin c) := finSumFinEquiv.symm

def numberedTransducer {p c : ℕ} (S : Op (Sum (Fin p) (Fin c))) : Op (Fin (p+c)) :=
  fun x y => S (sumCoordinates p c x) (sumCoordinates p c y)

end LindbladQueryOptimal.Simulation


