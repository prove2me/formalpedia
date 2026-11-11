-- Prove2me | Definitions.Def_ShortestPlanarDisjoint_Main_Isolation
-- name    : ShortestPlanarDisjoint_Main_Isolation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:40.573516+00:00
-- url     : https://prove2.me/theorems/2788d08e-85da-4625-b223-fe06d777f3d2
-- title:
--   Prescribed perturbations and the isolation event
-- statement:
--   Let $I$ be a routing instance on $n$ vertices, with $m$ actual graph edges. Set
--   $R_0$ to the least power of two at least $mn$. A perturbation chooses, independently
--   on each edge, a uniform integer $R(e)$ from $\{1,\ldots,R_0\}$. Define
--
--   $$\ell(e)=(mn)^2w(e)+R(e).$$
--
--   Values on nonedges are zero and unused. The isolation probability is the fraction
--   of the finite product of all perturbations for which there exists exactly one
--   minimum-$\ell$ linkage. The uniqueness event includes attainment and comparison
--   with every linkage; it is not a supplied property of the perturbation. For $mn=0$
--   the power-of-two function returns one, so the sample space still exists. The source
--   isolation assertion is used only in its nontrivial feasible regime. Original zero
--   costs are permitted. This is the exact perturbation used for original-cost recovery,
--   with a range and probability different from the range-$2m$ half-probability lemma.
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Section 4.2 (perturbation and Lemma 4.1), p. 13 (PDF p. 15)

import Definitions.Def_ShortestPlanarDisjoint_Main_Linkage

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main

noncomputable section

/-- The least power of two not less than t; t=0 gives 1. -/
def nextPowerTwo (t : ℕ) : ℕ := 2 ^ Nat.clog 2 t

def RoutingInput.edgeCount {n k : ℕ} (I : RoutingInput n k) : ℕ := Fintype.card I.Edge

/-- The range mandated in §4.2, rather than the weaker [1,2m] range. -/
def RoutingInput.randomRange {n k : ℕ} (I : RoutingInput n k) : ℕ :=
  nextPowerTwo (I.edgeCount * n)

/-- An independent choice of a uniform integer in [1,R₀] for each actual edge. -/
abbrev Perturbation {n k : ℕ} (I : RoutingInput n k) := I.Edge → Fin I.randomRange

/-- Original zero costs are allowed. Only perturbed costs must be positive.
Values on nonedges are set to zero and play no mathematical role. -/
def perturbedWeight {n k : ℕ} (I : RoutingInput n k) (R : Perturbation I)
    (e : Sym2 (Fin n)) : ℕ := by
  classical
  exact if h : e ∈ I.graph.edgeSet then
    (I.edgeCount * n) ^ 2 * I.weight e + (R ⟨e, h⟩).val + 1 else 0

/-- Uniform finite probability, with the event containing the full minimum assertion.
There is no assumed isolation oracle and no division by a possibly empty linkage family. -/
def isolationProbability {n k : ℕ} (I : RoutingInput n k) : ℚ := by
  classical
  exact ((Finset.univ.filter (fun R : Perturbation I =>
    ∃! L : Linkage I, L.IsMinimumFor (perturbedWeight I R))).card : ℚ) /
      Fintype.card (Perturbation I)

end
end ShortestPlanarDisjoint.Main


