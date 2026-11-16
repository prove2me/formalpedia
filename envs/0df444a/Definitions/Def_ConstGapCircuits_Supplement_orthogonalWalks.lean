-- Prove2me | Definitions.Def_ConstGapCircuits_Supplement_orthogonalWalks
-- name    : ConstGapCircuits_Supplement_orthogonalWalks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:28:47.046631+00:00
-- url     : https://prove2.me/theorems/d4668296-551d-4d81-9e88-74a958b30ad4
-- title:
--   Orthogonal Pauli rotations and orthogonal brickwork laws
-- statement:
--   Let $Y_n$ be the Hermitian Pauli strings with an odd number of $Y$ tensor factors. For $n\ge1$, this set has $2^{n-1}(2^n-1)$ elements. The random Pauli orthogonal rotation on $\mathrm{SO}(2^n)$ is
--   $$
--   \nu_{\mathrm{RPOR}}=\frac1{|Y_n|}\sum_{P\in Y_n}\mu_{\{e^{i\theta P}:\theta\in\mathbb R/2\pi\mathbb Z\}},\qquad
--    e^{i\theta P}=\cos\theta\,I+i\sin\theta\,P,
--   $$
--   where $\mu$ denotes Haar probability on the indicated circle. This is uniform choice of $P$ followed by an independent uniform angle.
--
--   The laws $\nu_{\mathrm{BROCC}}$ on $\mathrm{Cl}(n;\mathbb R)$ and $\nu_{\mathrm{BROC}}$ on $\mathrm{SO}(2^n)$ use one independent Haar gate on each of the $n-1$ bonds of an open chain. The gate groups are respectively $\mathrm{LCl}(\{j,j+1\},n;\mathbb R)$ and $\mathrm{LO}(\{j,j+1\},n)$. The published ordered convolution applies even zero-based bonds followed by odd zero-based bonds, giving the paper's depth-two brickwork order.
--
--   These laws are the orthogonal companions of the published unitary and Clifford laws. All local groups include their central signs, and all rotation subgroups lie in the designated orthogonal parent group.
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), pp. 2–3, 18, 25–26, 28, Definition 1.2, Theorems 2.50, 3.54, 4.19 and equations (3.53)–(3.55); PDF sha256 e8cf47b0382db220adaab4a2a08a778925d68118885ede05fe433e280cb5da26

import Definitions.Def_ConstGapCircuits_Supplement_orthogonalGroups
import Definitions.Def_ConstGapCircuits_walks

noncomputable section

namespace ConstGapCircuits.Supplement
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Y_n in (3.53): the Hermitian Pauli strings with an odd number of Y factors. -/
abbrev OddYIndex (n : ℕ) :=
  {p : Fin n → Fin 4 // Odd ((Finset.univ.filter (fun i => p i = 2)).card)}

/-- Uniform Pauli choice followed by the uniform circle rotation, (3.53)--(3.55).
For n≥1 the index type is nonempty and each summand is Haar probability. -/
def rpor (n : ℕ) : Measure (SO n) :=
  (Fintype.card (OddYIndex n) : ℝ≥0∞)⁻¹ •
    ∑ p : OddYIndex n, haarOn (thetaSubgroup (soInclusion n) circleAngles p.val)

/-- Orthogonal Clifford open-chain brickwork, even zero-based bonds then odd bonds. -/
def brocc (n : ℕ) : Measure (OCl n) :=
  brickwork n (fun j => haarOn (localOrthogonalClifford (edgeSupport n j)))

/-- Orthogonal open-chain brickwork with the full supported orthogonal local groups. -/
def broc (n : ℕ) : Measure (SO n) :=
  brickwork n (fun j => haarOn (localOrthogonal (edgeSupport n j)))

end ConstGapCircuits.Supplement


