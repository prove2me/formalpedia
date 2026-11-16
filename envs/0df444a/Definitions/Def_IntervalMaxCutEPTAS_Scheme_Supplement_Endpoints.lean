-- Prove2me | Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_Endpoints
-- name    : IntervalMaxCutEPTAS_Scheme_Supplement_Endpoints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:27:30.675831+00:00
-- url     : https://prove2.me/theorems/368a937b-0946-42a9-8ee1-c2e002681ae2
-- title:
--   Ancestral endpoints and external neighborhoods
-- statement:
--   Fix the rank representation, dyadic hierarchy and good shift of §4. For a nonroot open cell $C$, $P(C)$ is the finite set of distinct integer endpoints of rounded groups anchored at proper ancestors of $C$ that lie strictly inside $C$. Multiplicities are discarded. Define
--
--   $$d_C(\xi)=\min\{\xi-\operatorname{lo}(C),\operatorname{hi}(C)-\xi\},\qquad K(C)=\bigl|\{N_H(v)\setminus V_C:v\in V_C\}\bigr|.$$
--
--   In particular $K(C)=0$ if $V_C$ is empty. The parameter is exactly $\sigma=2^{-b}$. These statistics are shared by Lemmas 6.1–6.3; they count actual neighbor sets, rather than groups or labels.
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), §6–§6.1, PDF p. 23 (printed p. 22)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Hierarchy

set_option autoImplicit false

namespace IntervalMaxCutEPTAS.Scheme.Supplement

open Classical

/-- §6.1: distinct ancestral integer endpoint positions in the open cell. -/
noncomputable def ancestralPositions {n : ℕ} (P : Setup n) (C : ℕ) : Finset ℤ :=
  (((groups P).filter (fun g => IsProperAncestor (anchor P g) C)).biUnion
    (fun g => {A P g, B P g})).filter (fun ξ => cellLo n C < ξ ∧ ξ < cellHi n C)

/-- Distance to the nearer boundary; used only for points inside a valid cell. -/
def boundaryDistance (n C : ℕ) (ξ : ℤ) : ℝ :=
  min ((ξ : ℝ) - cellLo n C) ((cellHi n C : ℝ) - ξ)

/-- The actual external neighbors in H, on the original vertex set. -/
noncomputable def externalNeighbors {n : ℕ} (P : Setup n) (C : ℕ)
    (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => u ∉ VC P C ∧ (H P).Adj v u)

/-- Number of distinct neighbor sets, zero when VC is empty. -/
noncomputable def neighborhoodCount {n : ℕ} (P : Setup n) (C : ℕ) : ℕ :=
  ((VC P C).image (externalNeighbors P C)).card

/-- The section's exact dyadic accuracy. -/
noncomputable def sigma (b : ℕ) : ℝ := (2 : ℝ) ^ (-(b : ℤ))

end IntervalMaxCutEPTAS.Scheme.Supplement


