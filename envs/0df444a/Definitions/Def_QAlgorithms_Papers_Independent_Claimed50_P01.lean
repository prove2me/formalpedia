-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P01
-- name    : QAlgorithms_Papers_Independent_Claimed50_P01
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T08:26:58.592896+00:00
-- url     : https://prove2.me/theorems/44811c3a-cc73-482d-8c0c-1eba8feb18e6
-- title:
--   Definitions for Weak Schur sampling with logarithmic quantum memory
-- statement:
--   The objects the formalized statements of *Weak Schur sampling with logarithmic quantum memory* (arXiv:2309.11947) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `QIndex`: Coordinates on the actual irreducible module, not on its isotypic component (PDF pp.3-4, Eqs.(4),(10)).
--   - `terminal`: Terminal Young label of a history (PDF p.8).
--   - `historyPrefix`: Forget the latest arrival (PDF pp.8-9, induction in Eqs.(41)-(44)).
--   - `Path`: Valid Young-lattice paths: inclusion together with the sizes already in the shape types says that precisely one box is added (PDF pp.4,8).
--   - `pathPrefix`: A valid path remains valid after dropping its final shape (PDF p.9).
--   - `PathsTo`: All paths ending at one Young label (PDF pp.8-9, multiplicity labels).
--   - `qAction`: The actual unitary-group representation in the fixed module coordinates (PDF pp.3-4, Eqs.(3),(10)).
--   - `CGSystem`: Fixed one-qudit CG operations, expressed in the accepted realizations of Q. The fields are precisely the local unitary-intertwiner definition of Eq.(10), including zero blocks for invalid additions. No global Schur identity, Born law, resource bound, or instrument correctness is an assumed field (PDF pp.4-5). Any one fixed choice is used coherently throughout; it never takes rho as input.
--   - `emptyCoordinates`: Empty-register coordinate change. This is the amplitude of the unique empty word in the fixed orthonormal module basis; no unnormalized input state is used.
--   - `sequentialKraus`: Eq.(35)-(37): a product of single, measured CG blocks, with latest factor on the left. Tensoring the previous map with identity receives the next system without replacing an entangled arrival by an independent density operator.
--   - `sequentialBranch`: The subnormalized CP branch of the sequential algorithm (PDF p.8, Eq.(36)).
--   - `pathProbability`: Observed full-path probability is the trace of its actual sequential branch (PDF p.9, Eqs.(38)-(39)); it is not defined using the target projector.
--   - `labelProbability`: Forgetting the classical path sums branch probabilities incoherently (PDF p.9, Eq.(39)).
--   - `GTIndex`: Schur coordinates with path as multiplicity label (PDF pp.5,8).
--   - `superCG`: Eq.(11): all copies receive the same local CG operation. The only nonzero block extends the old path by the newly measured shape (PDF pp.5,8-9).
--   - `gtTransform`: Eq.(13): the coherent Schur transform is built independently from the super CG operations. It is not defined to be the sequential measured path map. The same fixed C is used on every copy and at every occurrence (PDF p.5).
--   - `schurBlock`: Rectangular version of Pi_(lambda,p)^Sch U^Sch: retain precisely one irrep copy, removing zero-padded rows (PDF p.7, Eq.(23), and footnote 5).
--   - `paddedKraus`: Tensor the sequential branch with identity on every unread system before applying it to the full stream state (PDF p.8, Eq.(37)).
--   - `paddedBranch`: Subnormalized retained-irrep/unread-input joint branch, preserving all residual correlations (PDF pp.8-9).
--   - `traceUnread`: Trace over the unread, right tensor factor; never discard correlations by factorizing the input (PDF p.8, identity padding in Eq.(37)).
--   - `prefixDensity`: Density operator of a fixed input prefix, not of an outcome-selected stopping rule (PDF pp.2,6).
--   - `peakMemory`: Peak active quantum workspace of Algorithm 1: the retained irrep plus the next d-level arrival. The classical path and unread systems are outside it. Nat.clog is the minimum number of d-level wires for this dimension when d>=2 (PDF p.6). The k=0 term accounts for receiving the first system.
--   - `multiplicityProbability`: Report a multiplicity basis index by decoding the classical path, with the bijection fixed before the input (PDF p.9, last paragraph).
-- source:
--   Weak Schur sampling with logarithmic quantum memory, arXiv:2309.11947v1, https://arxiv.org/abs/2309.11947v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylMeasurements

/-!
Statements from Cervero-Martín and Mančinska, arXiv:2309.11947v1.
The local CG coordinates below are fixed independently of the input. They use
orthonormal coordinates on the accepted irreducible modules, not the accepted
polar-normalized `Schur.decomposition`. The latter is never used here.
The zero-box case is solely an auxiliary initialization for the recursion;
all source results require at least one incoming system.
-/

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.Independent.Claimed50.P01

attribute [local instance] Classical.propDecidable

/-- Coordinates on the actual irreducible module, not on its isotypic component
(PDF pp.3-4, Eqs.(4),(10)). -/
abbrev QIndex {d n : ℕ} (lambda : Schur.Partition d n) :=
  Fin (Module.finrank ℂ (Schur.schurModule lambda))

/-- Terminal Young label of a history (PDF p.8). -/
def terminal {d n : ℕ} (p : ((k : Fin (n + 1)) → Schur.Partition d k.val)) : Schur.Partition d n := p (Fin.last n)

/-- Forget the latest arrival (PDF pp.8-9, induction in Eqs.(41)-(44)). -/
def historyPrefix {d n : ℕ} (p : ((k : Fin ((n + 1) + 1)) → Schur.Partition d k.val)) : ((k : Fin (n + 1)) → Schur.Partition d k.val) :=
  fun k => p k.castSucc

/-- Valid Young-lattice paths: inclusion together with the sizes already in the
shape types says that precisely one box is added (PDF pp.4,8). -/
abbrev Path (d n : ℕ) :=
  {p : ((k : Fin (n + 1)) → Schur.Partition d k.val) // ∀ k : Fin n, (p k.castSucc).val ≤ (p k.succ).val}

/-- A valid path remains valid after dropping its final shape (PDF p.9). -/
def pathPrefix {d n : ℕ} (p : Path d (n + 1)) : Path d n :=
  ⟨historyPrefix p.val, fun k => p.property k.castSucc⟩

/-- All paths ending at one Young label (PDF pp.8-9, multiplicity labels). -/
abbrev PathsTo {d n : ℕ} (lambda : Schur.Partition d n) :=
  {p : Path d n // terminal p.val = lambda}

/-- The actual unitary-group representation in the fixed module coordinates
(PDF pp.3-4, Eqs.(3),(10)). -/
def qAction {d n : ℕ} (lambda : Schur.Partition d n)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (QIndex lambda) (QIndex lambda) ℂ :=
  Matrix.of fun i j => inner ℂ (stdOrthonormalBasis ℂ (Schur.schurModule lambda) i)
    (Schur.polynomialRepresentation lambda (U : Matrix (Fin d) (Fin d) ℂ)
      (stdOrthonormalBasis ℂ (Schur.schurModule lambda) j))

/-- Fixed one-qudit CG operations, expressed in the accepted realizations of Q.
The fields are precisely the local unitary-intertwiner definition of Eq.(10),
including zero blocks for invalid additions. No global Schur identity, Born law,
resource bound, or instrument correctness is an assumed field (PDF pp.4-5).
Any one fixed choice is used coherently throughout; it never takes rho as input. -/
structure CGSystem (d : ℕ) where
  block : {k : ℕ} → (lambda : Schur.Partition d k) →
    (mu : Schur.Partition d (k + 1)) →
    Matrix (QIndex mu) (QIndex lambda × Fin d) ℂ
  invalid : ∀ {k} (lambda : Schur.Partition d k) (mu : Schur.Partition d (k + 1)),
    ¬ lambda.val ≤ mu.val → block lambda mu = 0
  isometry : ∀ {k} (lambda : Schur.Partition d k),
    ∑ mu : Schur.Partition d (k + 1), (block lambda mu)ᴴ * block lambda mu = 1
  onto : ∀ {k} (lambda : Schur.Partition d k) (mu : Schur.Partition d (k + 1)),
    lambda.val ≤ mu.val → block lambda mu * (block lambda mu)ᴴ = 1
  orthogonal : ∀ {k} (lambda : Schur.Partition d k)
    (mu nu : Schur.Partition d (k + 1)), mu ≠ nu →
    block lambda mu * (block lambda nu)ᴴ = 0
  intertwines : ∀ {k} (lambda : Schur.Partition d k)
    (mu : Schur.Partition d (k + 1)) (U : Matrix.unitaryGroup (Fin d) ℂ),
    block lambda mu * Matrix.kronecker (qAction lambda U) (U : Matrix (Fin d) (Fin d) ℂ) =
      qAction mu U * block lambda mu

/-- Empty-register coordinate change. This is the amplitude of the unique empty
word in the fixed orthonormal module basis; no unnormalized input state is used. -/
def emptyCoordinates {d : ℕ} (lambda : Schur.Partition d 0) :
    Matrix (QIndex lambda) ((Fin 0 → Fin d)) ℂ :=
  Matrix.of fun i w => star ((stdOrthonormalBasis ℂ (Schur.schurModule lambda) i).val w)

/-- Eq.(35)-(37): a product of single, measured CG blocks, with latest factor on
the left. Tensoring the previous map with identity receives the next system
without replacing an entangled arrival by an independent density operator. -/
def sequentialKraus {d : ℕ} (C : CGSystem d) :
    (n : ℕ) → (p : ((k : Fin (n + 1)) → Schur.Partition d k.val)) → Matrix (QIndex (terminal p)) ((Fin n → Fin d)) ℂ
  | 0, p => emptyCoordinates (terminal p)
  | n + 1, p =>
      C.block (terminal (historyPrefix p)) (terminal p) *
        (Matrix.kronecker (sequentialKraus C n (historyPrefix p))
          (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix id
            (fun w => (Fin.init w, w (Fin.last n)))

/-- The subnormalized CP branch of the sequential algorithm (PDF p.8, Eq.(36)). -/
def sequentialBranch {d n : ℕ} (C : CGSystem d) (p : Path d n)
    (rho : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ) :
    Matrix (QIndex (terminal p.val)) (QIndex (terminal p.val)) ℂ :=
  sequentialKraus C n p.val * rho * (sequentialKraus C n p.val)ᴴ

/-- Observed full-path probability is the trace of its actual sequential branch
(PDF p.9, Eqs.(38)-(39)); it is not defined using the target projector. -/
def pathProbability {d n : ℕ} (C : CGSystem d) (p : Path d n)
    (rho : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ) : ℝ :=
  (sequentialBranch C p rho).trace.re

/-- Forgetting the classical path sums branch probabilities incoherently
(PDF p.9, Eq.(39)). -/
def labelProbability {d n : ℕ} (C : CGSystem d) (lambda : Schur.Partition d n)
    (rho : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ) : ℝ :=
  ∑ p : Path d n, if terminal p.val = lambda then pathProbability C p rho else 0

/-- Schur coordinates with path as multiplicity label (PDF pp.5,8). -/
abbrev GTIndex (d n : ℕ) := (p : Path d n) × QIndex (terminal p.val)

/-- Eq.(11): all copies receive the same local CG operation. The only nonzero
block extends the old path by the newly measured shape (PDF pp.5,8-9). -/
def superCG {d : ℕ} (C : CGSystem d) (n : ℕ) :
    Matrix (GTIndex d (n + 1)) (GTIndex d n × Fin d) ℂ :=
  Matrix.of fun a b =>
    if h : pathPrefix a.1 = b.1.1 then
      C.block (terminal (pathPrefix a.1).val) (terminal a.1.val) a.2
        (cast (congrArg (fun p : Path d n => QIndex (terminal p.val)) h.symm) b.1.2, b.2)
    else 0

/-- Eq.(13): the coherent Schur transform is built independently from the super
CG operations. It is not defined to be the sequential measured path map.
The same fixed C is used on every copy and at every occurrence (PDF p.5). -/
def gtTransform {d : ℕ} (C : CGSystem d) :
    (n : ℕ) → Matrix (GTIndex d n) ((Fin n → Fin d)) ℂ
  | 0 => Matrix.of fun a w => emptyCoordinates (terminal a.1.val) a.2 w
  | n + 1 => superCG C n *
      (Matrix.kronecker (gtTransform C n) (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix id
        (fun w => (Fin.init w, w (Fin.last n)))

/-- Rectangular version of Pi_(lambda,p)^Sch U^Sch: retain precisely one irrep
copy, removing zero-padded rows (PDF p.7, Eq.(23), and footnote 5). -/
def schurBlock {d n : ℕ} (C : CGSystem d) (p : Path d n) :
    Matrix (QIndex (terminal p.val)) ((Fin n → Fin d)) ℂ :=
  (gtTransform C n).submatrix (fun q => ⟨p, q⟩) id

/-- Tensor the sequential branch with identity on every unread system before
applying it to the full stream state (PDF p.8, Eq.(37)). -/
def paddedKraus {d k : ℕ} (C : CGSystem d) (p : Path d k) (r : ℕ) :
    Matrix (QIndex (terminal p.val) × (Fin r → Fin d)) ((Fin (k + r) → Fin d)) ℂ :=
  Matrix.of fun a w =>
    if a.2 = (fun i => w (Fin.natAdd k i)) then
      sequentialKraus C k p.val a.1 (fun i => w (Fin.castAdd r i))
    else 0

/-- Subnormalized retained-irrep/unread-input joint branch, preserving all
residual correlations (PDF pp.8-9). -/
def paddedBranch {d k : ℕ} (C : CGSystem d) (p : Path d k) {r : ℕ}
    (rho : Matrix ((Fin (k + r) → Fin d)) ((Fin (k + r) → Fin d)) ℂ) :
    Matrix (QIndex (terminal p.val) × (Fin r → Fin d))
      (QIndex (terminal p.val) × (Fin r → Fin d)) ℂ :=
  paddedKraus C p r * rho * (paddedKraus C p r)ᴴ

/-- Trace over the unread, right tensor factor; never discard correlations by
factorizing the input (PDF p.8, identity padding in Eq.(37)). -/
def traceUnread {A B : Type*} [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ :=
  Matrix.of fun a b => ∑ u : B, rho (a, u) (b, u)

/-- Density operator of a fixed input prefix, not of an outcome-selected stopping
rule (PDF pp.2,6). -/
def prefixDensity {d : ℕ} (k r : ℕ)
    (rho : Matrix ((Fin (k + r) → Fin d)) ((Fin (k + r) → Fin d)) ℂ) :
    Matrix ((Fin k → Fin d)) ((Fin k → Fin d)) ℂ :=
  Matrix.of fun a b => ∑ u : (Fin r → Fin d), rho (Fin.append a u) (Fin.append b u)

/-- Peak active quantum workspace of Algorithm 1: the retained irrep plus the
next d-level arrival. The classical path and unread systems are outside it.
Nat.clog is the minimum number of d-level wires for this dimension when d>=2
(PDF p.6). The k=0 term accounts for receiving the first system. -/
def peakMemory (d n : ℕ) : ℕ :=
  (Finset.range n).sup fun k =>
    (Finset.univ : Finset (Schur.Partition d k)).sup fun lambda =>
      Nat.clog d (d * Module.finrank ℂ (Schur.schurModule lambda))

/-- Report a multiplicity basis index by decoding the classical path, with the
bijection fixed before the input (PDF p.9, last paragraph). -/
def multiplicityProbability {d n : ℕ} {lambda : Schur.Partition d n}
    (C : CGSystem d)
    (decode : PathsTo lambda ≃ Fin (Module.finrank ℂ (Schur.spechtSpace lambda)))
    (i : Fin (Module.finrank ℂ (Schur.spechtSpace lambda)))
    (rho : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ) : ℝ :=
  pathProbability C (decode.symm i).val rho

/-- A zero-box history performs only the empty-register coordinate change. -/
example {d : ℕ} (C : CGSystem d) (p : ((k : Fin (0 + 1)) → Schur.Partition d k.val)) :
    sequentialKraus C 0 p = emptyCoordinates (terminal p) := rfl

/-- A single CG arrival appears on the left, preserving the order in Eq.(37). -/
example {d n : ℕ} (C : CGSystem d) (p : ((k : Fin ((n + 1) + 1)) → Schur.Partition d k.val)) :
    sequentialKraus C (n + 1) p =
      C.block (terminal (historyPrefix p)) (terminal p) *
        (Matrix.kronecker (sequentialKraus C n (historyPrefix p))
          (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix id
            (fun w => (Fin.init w, w (Fin.last n))) := rfl

/-- The trace on a product sums the unread factor once, without squaring a trace. -/
example {A B : Type*} [Fintype B] (X : Matrix A A ℂ) (Y : Matrix B B ℂ) :
    traceUnread (Matrix.kronecker X Y) = Y.trace • X := by
  ext a b
  simp [traceUnread, Matrix.kronecker, Matrix.trace, Finset.mul_sum, mul_comm]

/-- Receiving no system uses no memory; source theorems exclude this input. -/
example (d : ℕ) : peakMemory d 0 = 0 := by simp [peakMemory]

end QAlgorithms.Papers.Independent.Claimed50.P01


