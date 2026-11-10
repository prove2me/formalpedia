-- Prove2me | Definitions.Def_BMPV1173_Verification_ImplicitAdapters
-- name    : BMPV1173_Verification_ImplicitAdapters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:05:41.777636+00:00
-- url     : https://prove2.me/theorems/a4c13b4b-b97f-422e-b54b-d1b85c292c3b
-- title:
--   Finite-universe and coherent predicate-oracle adapters for Lemma 2.5
-- statement:
--   Embeds the known universe of M labels into a universe of size max(2,n,M), with dummy labels unmarked. The enumeration adapter translates Boolean marks to ZMod 2 and gives the extra dummy query the fixed answer zero. The predicate-oracle matrix is the supplied query circuit followed by a Boolean copy and its inverse. Thus the compute/copy/uncompute construction uses the actual circuit rather than a stipulated cost or arbitrary answer distribution. The two counting/preparation and enumeration theorems themselves remain existing Open references.
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, §2.2, Lemma 2.5 and Remark 2.8, printed p.15 = PDF p.15.

import Definitions.Def_BMPV1173_Verification_Resources

/-! Adapters for the two Open Lemma 2.5 companions. These are actual
finite-universe and oracle maps, rather than assumed query-complexity inequalities. -/
namespace BMPV1173.Verification

noncomputable section

/-- Pad to at least the ambient n, at least two, and at least M. -/
def implicitUniverse (n M : ℕ) := max 2 (max n M)

def implicitEmbed (n M : ℕ) (i : Fin M) : Fin (implicitUniverse n M) :=
  ⟨i.val, lt_of_lt_of_le i.isLt (le_trans (le_max_right n M) (le_max_right 2 (max n M)))⟩

def implicitKnownSet (n M : ℕ) : Finset (Fin (implicitUniverse n M)) :=
  Finset.univ.image (implicitEmbed n M)

/-- Dummy labels are unmarked; on the known embedded set this is exactly g. -/
def paddedMembership (n M : ℕ) (g : Fin M → Bool) : Fin (implicitUniverse n M) → Bool :=
  fun i => if h : i.val < M then g ⟨i.val,h⟩ else false

def boolToZMod (b : Bool) : ZMod 2 := if b then 1 else 0

def enumerationMembership {M : ℕ} (g : Fin M → Bool) : Option (Fin M) → ZMod 2 :=
  fun i => i.elim 0 (fun j => boolToZMod (g j))

/-- Matrix of the actual T-query unitary product, with no reference to A.start. -/
def circuitMatrix {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
    {T : ℕ} (A : QAlgorithms.QueryAlg ι Bool W T) (x : ι → Bool) :
    Matrix ((ι × Bool) × W) ((ι × Bool) × W) ℂ :=
  Matrix.of fun i j => applyCircuit A x (QAlgorithms.ket j) i

/-- Copy the computed Boolean output into a separate bit; leave the full
computation register unchanged. This is a permutation matrix. -/
def copyOutput {Z : Type} [DecidableEq Z] (out : Z → Bool) :
    Matrix (Z × Bool) (Z × Bool) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2 = xor q.2 (out q.1) then 1 else 0

/-- Compute/copy/uncompute, using the T-query circuit, one query-free copy,
and its T-query inverse. For XOR entry queries the inverse oracle is the same
oracle. The total is 2T input queries; imperfect tests remain physical circuits. -/
def simulatedPredicateOracle {ι W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QAlgorithms.QueryAlg ι Bool W T) (out : (ι × Bool) × W → Bool) (x : ι → Bool) :
    Matrix (((ι × Bool) × W) × Bool) (((ι × Bool) × W) × Bool) ℂ :=
  Matrix.kronecker (circuitMatrix A x).conjTranspose (1 : Matrix Bool Bool ℂ) *
    copyOutput out * Matrix.kronecker (circuitMatrix A x) (1 : Matrix Bool Bool ℂ)

end
end BMPV1173.Verification


