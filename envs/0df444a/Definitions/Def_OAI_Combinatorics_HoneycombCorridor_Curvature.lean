-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
-- name    : OAI_Combinatorics_HoneycombCorridor_Curvature
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:36:40.281475+00:00
-- url     : https://prove2.me/theorems/db9d5044-d1d3-4af8-a477-2540f2e009b4
-- title:
--   Turn counts and discrete curvature of honeycomb cells
-- statement:
--   Combinatorial curvature for finite sets $S$ of hexagonal faces of the honeycomb lattice.
--
--   1. **Turn units.** A left turn counts $+1$ and a right turn $-1$; $\mathrm{turnUnits}(w)$ is the sum over the word $w$, so the total turning angle of $w$ is $\frac\pi3\,\mathrm{turnUnits}(w)$.
--   2. **Local counts.** For a vertex $v$, $\mathrm{faceCount}(S,v)$ is the number of its three incident faces lying in $S$ and $\mathrm{edgeCount}(S,v)$ the number of its three incident edges that are cell edges of $S$.
--   3. **Curvature.** The cell curvature at $v$ is
--   $$
--   \kappa_S(v)=6-3\,\mathrm{edgeCount}(S,v)+\mathrm{faceCount}(S,v).
--   $$
--   4. **Germ bookkeeping.** The right face of $(v,k)$ is the left face of $(v,k+2)$, the edge of a germ has the germ's slot, and a germ $(v,e_2)$ lies on edge $e$ exactly when $v$ is one of the two ends of $e$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Curvature.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Curvature.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def turnUnit (b : Bool) : ℤ := if b then 1 else -1

def turnUnits (w : List Bool) : ℤ := (w.map turnUnit).sum

def faceCount (S : Finset FaceIndex) (v : Vertex) : ℤ :=
  ∑ k : Fin 3, if leftFace (v,k) ∈ S then 1 else 0

def edgeCount (S : Finset FaceIndex) (v : Vertex) : ℤ :=
  ∑ k : Fin 3, if edgeOf (v,k) ∈ cellEdges S then 1 else 0

def cellCurvature (S : Finset FaceIndex) (v : Vertex) : ℤ :=
  6 - 3 * edgeCount S v + faceCount S v

@[simp] theorem rightFace_prev (v : Vertex) (k : Fin 3) :
    rightFace (v,k) = leftFace (v,k+2) := by
  cases v <;> fin_cases k <;> simp [rightFace,reverseGerm,neighbor,leftFace]

@[simp] theorem edgeOf_slot (g : Germ) : (edgeOf g).2 = g.2 := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [edgeOf]

@[simp] theorem edgeOf_canonical (e : EdgeIndex) : edgeOf (canonicalDart e) = e := by
  rcases e with ⟨⟨i,j⟩,k⟩
  rfl

@[simp] theorem edgeOf_downEnd (e : EdgeIndex) : edgeOf (downEnd e,e.2) = e := by
  change edgeOf (reverseGerm (canonicalDart e)) = e
  rw [edgeOf_reverse,edgeOf_canonical]

theorem edgeOf_eq_iff (v : Vertex) (e : EdgeIndex) :
    edgeOf (v,e.2) = e ↔ v = upEnd e ∨ v = downEnd e := by
  constructor
  · intro h
    rcases canonicalDart_edgeOf (v,e.2) with h' | h'
    · rw [h] at h'
      exact Or.inl (congrArg Prod.fst h').symm
    · rw [h] at h'
      have he := congrArg (fun x : Germ => (reverseGerm x).1) h'
      simp only [reverseGerm_reverseGerm] at he
      exact Or.inr he.symm
  · rintro (rfl | rfl)
    · exact edgeOf_canonical e
    · exact edgeOf_downEnd e

end PolynomialVacuumBridge.Corridor

end

end OAI


