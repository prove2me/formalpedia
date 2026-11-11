-- Prove2me | Definitions.Def_LabelSymmetricCollision215_Collision_Recording
-- name    : LabelSymmetricCollision215_Collision_Recording
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:55.18513+00:00
-- url     : https://prove2.me/theorems/d1260697-71d1-46a0-a27c-f85e7463138b
-- title:
--   Concrete compressed oracle and database projections
-- statement:
--   Enlarge every input cell to $\mathbb C[\mathbb Z/N\mathbb Z\cup\{\bot\}]$. The local real unitary $Q$ swaps the empty basis vector with the uniform label vector and fixes their common orthogonal complement. Compression is the tensor product of $Q$ restricted to the original label space. The recording cell query is $Q\operatorname{diag}(1,\omega_N^{py})Q$, extended to the queried address and acting trivially on all other cells. Recording states are obtained from the actual Fourier-coordinate start and inter-query unitaries, with every database cell initially empty.
--
--   The image projector is $\mathrm{Comp}\mathrm{Comp}^\dagger$. Coordinate masks give collision, collision-free, exact occupancy, exact occupied-set sectors, and product-basis projections. Progress is the norm of the collision component of the recording state. The orbit restriction used in the vector theorems is separately named and takes an actual vector; it is never an algorithm field.
--
--   This concrete construction supports comparisons of standard and recording dynamics.
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, §§3.1–3.2,4.1,4.5; PDF 16–18,22,31 / printed 14–16,20,29

import Definitions.Def_LabelSymmetricCollision215_Collision_Model

noncomputable section
open scoped ComplexConjugate

namespace LabelSymmetricCollision215.Collision
attribute [local instance] Classical.propDecidable

/-! Concrete compression is the local swap of the empty symbol and the uniform label state.
The recording query is conjugation of the locally extended phase oracle, not a progress axiom. -/
def emptyAmplitude {N : ℕ} (a : Option (ZMod N)) : ℂ := if a = none then 1 else 0
def uniformAmplitude {N : ℕ} (a : Option (ZMod N)) : ℂ :=
  if a = none then 0 else 1 / (Real.sqrt N : ℂ)

def swapCell (N : ℕ) [NeZero N] : Matrix (Option (ZMod N)) (Option (ZMod N)) ℂ :=
  fun a b => (if a = b then 1 else 0) - emptyAmplitude a * emptyAmplitude b -
    uniformAmplitude a * uniformAmplitude b + emptyAmplitude a * uniformAmplitude b +
    uniformAmplitude a * emptyAmplitude b

def compressCell (N : ℕ) [NeZero N] : Matrix (Option (ZMod N)) (ZMod N) ℂ :=
  fun a b => swapCell N a (some b)

def compress (M N : ℕ) (W : Type) [Fintype W] [NeZero N] :
    H (Reg M N W × Input M N) →L[ℂ] H (Reg M N W × DB M N) :=
  mat (fun a b => if a.1 = b.1 then ∏ x, compressCell N (a.2 x) (b.2 x) else 0)

def compressedProjection (M N : ℕ) (W : Type) [Fintype W] [NeZero N] :
    H (Reg M N W × DB M N) →L[ℂ] H (Reg M N W × DB M N) :=
  (compress M N W).comp (compress M N W).adjoint

/-- The extension has phase one on the empty cell; p=0 is the identity on every cell. -/
def recordingCell (N : ℕ) [NeZero N] (p : ZMod N) :
    Matrix (Option (ZMod N)) (Option (ZMod N)) ℂ :=
  swapCell N * Matrix.diagonal (fun a => match a with
    | none => 1 | some y => phase p y) * swapCell N

def recordingOracle (M N : ℕ) (W : Type) [Fintype W] [NeZero N] :
    H (Reg M N W × DB M N) →L[ℂ] H (Reg M N W × DB M N) :=
  mat (fun a b => if a.1 = b.1 ∧ ∀ j, j ≠ b.1.1.1 → a.2 j = b.2 j
    then recordingCell N b.1.1.2 (a.2 b.1.1.1) (b.2 b.1.1.1) else 0)

def liftAlgorithm (M N : ℕ) (W : Type) [Fintype W] [NeZero N]
    (U : Matrix (Reg M N W) (Reg M N W) ℂ) :
    H (Reg M N W × DB M N) →L[ℂ] H (Reg M N W × DB M N) :=
  mat (fun a b => if a.2 = b.2 then
    (star (fourierReg M N W) * U * fourierReg M N W) a.1 b.1 else 0)

def recordingState {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (A : Alg M N T W) : Fin (T+1) → H (Reg M N W × DB M N) :=
  Fin.induction
    (WithLp.toLp 2 (fun a => if a.2 = (fun _ => none) then
      mat (star (fourierReg M N W)) (QAlgorithms.act (A.U 0 : Matrix _ _ ℂ) A.start) a.1
      else 0))
    (fun i ψ => liftAlgorithm M N W (A.U i.succ : Matrix _ _ ℂ)
      (recordingOracle M N W ψ))

def occupied {M N : ℕ} (d : DB M N) : Finset (Fin M) :=
  Finset.univ.filter (fun x => d x ≠ none)
def HasCollision {M N : ℕ} (d : DB M N) : Prop :=
  ∃ x₁ x₂ y, x₁ < x₂ ∧ d x₁ = some y ∧ d x₂ = some y

def collisionProjection (M N : ℕ) (W : Type) [Fintype W] [NeZero N] :=
  mask (fun a : Reg M N W × DB M N => HasCollision a.2)
def freeProjection (M N : ℕ) (W : Type) [Fintype W] [NeZero N] :=
  mask (fun a : Reg M N W × DB M N => ¬ HasCollision a.2)
def occupancyProjection (M N : ℕ) (W : Type) [Fintype W] [NeZero N] (s : ℕ) :=
  mask (fun a : Reg M N W × DB M N => (occupied a.2).card = s)
def sectorProjection {M N : ℕ} {W : Type} [Fintype W] [NeZero N]
    (η : Reg M N W) (I : Finset (Fin M)) :=
  mask (fun a : Reg M N W × DB M N => a.1 = η ∧ occupied a.2 = I)
def basisProjection {M N : ℕ} {W : Type} [Fintype W] [NeZero N] (η : Reg M N W) :=
  mask (fun a : Reg M N W × DB M N => a.1 = η)

def SupportedAtMost {M N : ℕ} {W : Type} [Fintype W] [NeZero N]
    (t : ℕ) (φ : H (Reg M N W × DB M N)) : Prop :=
  ∀ a, φ a ≠ 0 → (occupied a.2).card ≤ t

def databaseAction (M N : ℕ) (W : Type) [Fintype W] [NeZero N]
    (σ : Equiv.Perm (ZMod N)) :
    H (Reg M N W × DB M N) →L[ℂ] H (Reg M N W × DB M N) :=
  mat (fun a b => if a.1 = b.1 ∧ a.2 = (fun x => Option.map σ (b.2 x)) then 1 else 0)

def progress {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (A : Alg M N T W) (t : Fin (T+1)) : ℝ :=
  ‖collisionProjection M N W (recordingState A t)‖

def OrbitBound {M N : ℕ} {W : Type} [Fintype W] [NeZero N]
    (S : ℝ) (φ : H (Reg M N W × DB M N)) : Prop :=
  ∀ η, (Module.finrank ℂ (orbitSpan (fun σ => (databaseAction M N W σ).toLinearMap)
    (basisProjection η φ)) : ℝ) ≤ (2 : ℝ)^S

end LabelSymmetricCollision215.Collision


