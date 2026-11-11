-- Prove2me | Definitions.Def_LabelSymmetricCollision215_Collision_Model
-- name    : LabelSymmetricCollision215_Collision_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:17.727393+00:00
-- url     : https://prove2.me/theorems/7464dd96-f7f2-4a4b-bf87-1c6448dc2f08
-- title:
--   Finite unitary query model, measured success and reduced-state symmetry
-- statement:
--   Let $M,N$ be positive integers and $W$ a finite workspace basis. The algorithm space has basis $(([M]\times\mathbb Z/N\mathbb Z)\times W)$; the input register has basis all functions $[M]\to\mathbb Z/N\mathbb Z$. A query adds $f(x)$ modulo $N$. The published query algorithm supplies a fixed unit start and input-independent unitaries. Success is the uniform average of the squared final computational amplitudes decoded into triples $x_1<x_2$, $f(x_1)=f(x_2)=y$, with a separate failure outcome.
--
--   The Fourier columns have exponent $-pz$. The purified state is formed from the actual algorithm amplitudes; its input reduced matrix is their partial trace over the algorithm. Label symmetry means invariance of this matrix under every range permutation at every checkpoint. All algorithm registers are charged by $\dim H_A\le2^S$; the analytical input register is not charged. The definition also supplies finite coordinate linear maps, basis masks, orbit spans and $\log_2N=\log N/\log2$.
--
--   These definitions give an operational interface with no assumed progress or lower bound.
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, §§2.1,2.3–2.4,4.1; PDF 11,13–15,22 / printed 9,11–13,20

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

noncomputable section
open scoped ComplexConjugate

namespace LabelSymmetricCollision215.Collision
attribute [local instance] Classical.propDecidable

/-! Finite complex coordinate model of §§2.1,2.3–2.4 and 4.1.
The algorithm basis is ((address,value),work); input is a separate uncharged register. -/
abbrev Reg (M N : ℕ) (W : Type) := (Fin M × ZMod N) × W
abbrev Input (M N : ℕ) := Fin M → ZMod N
abbrev DB (M N : ℕ) := Fin M → Option (ZMod N)
abbrev Alg (M N T : ℕ) (W : Type) [Fintype W] [DecidableEq W] [NeZero N] :=
  QAlgorithms.QueryAlg (Fin M) (ZMod N) W T
abbrev H (ι : Type) [Fintype ι] := EuclideanSpace ℂ ι

def mat {ι κ : Type} [Fintype ι] [Fintype κ] (a : Matrix ι κ ℂ) : H κ →L[ℂ] H ι :=
  (Matrix.toEuclideanLin a).toContinuousLinearMap

def basis {ι : Type} [Fintype ι] (i : ι) : H ι :=
  WithLp.toLp 2 (fun j => if j = i then 1 else 0)

def mask {ι : Type} [Fintype ι] (p : ι → Prop) : H ι →L[ℂ] H ι :=
  mat (Matrix.diagonal (fun i => if p i then 1 else 0))

def omega (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
def phase {N : ℕ} (p y : ZMod N) : ℂ := omega N ^ (p.val * y.val)
def fourier {N : ℕ} [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  fun z p => conj (phase p z) / (Real.sqrt N : ℂ)

/-- Fourier columns are |p-hat>, with exponent -p z, as in Definition 2.2. -/
def fourierReg (M N : ℕ) (W : Type) [Fintype W] [NeZero N] :
    Matrix (Reg M N W) (Reg M N W) ℂ :=
  fun a b => if a.1.1 = b.1.1 ∧ a.2 = b.2 then fourier a.1.2 b.1.2 else 0

def computationalState {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (A : Alg M N T W) (f : Input M N) (t : Fin (T+1)) : H (Reg M N W) :=
  A.stateAt (QAlgorithms.xorOracle f) t

def fourierState {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (A : Alg M N T W) (f : Input M N) (t : Fin (T+1)) : H (Reg M N W) :=
  mat (star (fourierReg M N W)) (computationalState A f t)

def jointState {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (A : Alg M N T W) (δ : PMF (Input M N)) (t : Fin (T+1)) :
    H (Reg M N W × Input M N) :=
  WithLp.toLp 2 (fun a => (Real.sqrt (δ a.2).toReal : ℂ) * fourierState A a.2 t a.1)

def uniformJoint {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (A : Alg M N T W) (t : Fin (T+1)) : H (Reg M N W × Input M N) :=
  WithLp.toLp 2 (fun a => fourierState A a.2 t a.1 / (Real.sqrt (N^M) : ℂ))

/-- Actual partial trace over the algorithm, using any purified finite joint vector. -/
def reduced {B I : Type} [Fintype B] [Fintype I] (ψ : H (B × I)) : Matrix I I ℂ :=
  fun f g => ∑ b, ψ (b,f) * conj (ψ (b,g))

def relabel {M N : ℕ} (σ : Equiv.Perm (ZMod N)) (f : Input M N) := σ ∘ f

def labelMatrix (M N : ℕ) [NeZero N] (σ : Equiv.Perm (ZMod N)) :
    Matrix (Input M N) (Input M N) ℂ :=
  fun f g => if f = relabel σ g then 1 else 0

def LabelSymmetric {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (A : Alg M N T W) : Prop :=
  ∀ t σ, labelMatrix M N σ * reduced (uniformJoint A t) * star (labelMatrix M N σ) =
    reduced (uniformJoint A t)

def UsesSpace (M N : ℕ) (W : Type) [Fintype W] [NeZero N] (S : ℝ) : Prop :=
  (Fintype.card (Reg M N W) : ℝ) ≤ (2 : ℝ)^S

abbrev Output (M N : ℕ) := Option (Fin M × Fin M × ZMod N)
def ValidOutput {M N : ℕ} (f : Input M N) : Output M N → Prop
  | none => False
  | some (x₁,x₂,y) => x₁ < x₂ ∧ f x₁ = y ∧ f x₂ = y

def success {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (A : Alg M N T W) (out : Reg M N W → Output M N) : ℝ :=
  (∑ f : Input M N, ∑ b : Reg M N W,
    if ValidOutput f (out b) then ‖computationalState A f (Fin.last T) b‖^2 else 0) /
    (N^M : ℕ)

def orbitSpan {G V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : G → V →ₗ[ℂ] V) (v : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range (fun g => ρ g v))

def logTwo (N : ℕ) : ℝ := Real.log N / Real.log 2

end LabelSymmetricCollision215.Collision


