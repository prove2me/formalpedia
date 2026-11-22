-- Prove2me | Definitions.Def_NLabRelativeLanglands_Automorphic
-- name    : NLabRelativeLanglands_Automorphic
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T21:17:19.838605+00:00
-- url     : https://prove2.me/theorems/89e4d098-7643-4b3d-a6af-d94f39918bc9
-- title:
--   The automorphic datum: $G(F_v)$, $G(\mathbb A)$, $G(F)$ and $C^\infty([G])$
-- statement:
--   The ambient arithmetic and automorphic data of the relative Langlands program over a global base field $F$.
--
--   The datum consists of: the set of places $v$ of $F$; the local groups $G(F_v)$; the adelic group $G(\mathbb A_F)$; the group of rational points $G(F)$ together with its diagonal embedding into $G(\mathbb A_F)$; and the space $C^\infty([G])$ of automorphic functions on the automorphic quotient
--   $$[G] \;=\; G(F)\backslash G(\mathbb A_F),$$
--   regarded as a complex vector space with the right translation action of $G(\mathbb A_F)$.
--
--   Automorphic functions are presented through their values: an automorphic function $f$ has an evaluation $f(g)\in\mathbb C$ at every adelic point, evaluation is injective and $\mathbb C$-linear, right translation acts by $(f\cdot h)(g)=f(gh)$, and $f(\gamma g)=f(g)$ for every rational point $\gamma\in G(F)$. Conversely every left $G(F)$-invariant complex function on $G(\mathbb A_F)$ is the evaluation of an automorphic function.
--
--   This is the target space of the automorphic realization sought in the nLab section "Quantization in the relative Langlands program", and the ambient group data against which local quantizations are stated.
--
--   **Formalization Note.** Smoothness of automorphic functions — smooth in the archimedean variables, locally constant in the finite ones — is not resolved in this model; $C^\infty([G])$ is represented by the left $G(F)$-invariant functions together with their linear and translation structure. All actions are right actions, matching the source's convention $\Phi(\gamma g)$.
-- source:
--   nLab, 'relative Langlands program', section 2 'Quantization in the relative Langlands program' (https://ncatlab.org/nlab/show/relative+Langlands+program, last revised 29 April 2025): 'Let F be the global base field and let G be a reductive group ... an automorphic realization ⊗'ω_v → C^∞(G(F)\G(𝔸_F))'. Ambient notation as in Y. Sakellaridis, 'Spherical varieties, functoriality, and quantization', arXiv:2111.03004v2, §1.4 and §2.1.3 ([G] = G(k)\G(𝔸)).

import Mathlib

/-!
# The automorphic side of the relative Langlands program

Ambient data for the nLab entry "relative Langlands program", section
"Quantization in the relative Langlands program": a global base field `F`, a reductive
group `G`, its local groups `G(F_v)`, its adelic group `G(𝔸_F)`, its rational points
`G(F)`, and the space `C^∞([G])` of automorphic functions on `[G] = G(F)\G(𝔸_F)`.

The space of automorphic functions is presented through its evaluation: an automorphic
function is determined by its values on `G(𝔸_F)`, is invariant under left translation by
`G(F)`, and every left `G(F)`-invariant function is realized. Smoothness is not resolved
into archimedean-smooth / finite-place-locally-constant conditions in this model.
-/

namespace NLabRelativeLanglands

/-- Ambient automorphic datum over a global field: places, local groups, the adelic group,
the rational points with their diagonal embedding, and the automorphic functions on the
automorphic quotient, with right translation by the adelic group. -/
structure AutomorphicDatum where
  /-- The places `v` of the global base field `F`. -/
  Place : Type*
  /-- The local groups `G(F_v)`. -/
  Gloc : Place → Type*
  /-- The adelic group `G(𝔸_F)`. -/
  Gade : Type*
  /-- The rational points `G(F)`. -/
  Grat : Type*
  [grpLoc : ∀ v, Group (Gloc v)]
  [grpAde : Group Gade]
  [grpRat : Group Grat]
  /-- The diagonal embedding `G(F) → G(𝔸_F)`. -/
  diag : Grat →* Gade
  /-- The space `C^∞([G])` of automorphic functions on `[G] = G(F)\G(𝔸_F)`. -/
  Aut : Type*
  [acgAut : AddCommGroup Aut]
  [modAut : Module ℂ Aut]
  /-- Right translation of automorphic functions by `G(𝔸_F)`. -/
  autAct : Aut → Gade → Aut
  autAct_one : ∀ f : Aut, autAct f 1 = f
  autAct_mul : ∀ (f : Aut) (g h : Gade), autAct f (g * h) = autAct (autAct f g) h
  autAct_add : ∀ (f f' : Aut) (g : Gade), autAct (f + f') g = autAct f g + autAct f' g
  autAct_smul : ∀ (c : ℂ) (f : Aut) (g : Gade), autAct (c • f) g = c • autAct f g
  /-- Evaluation of an automorphic function at an adelic point. -/
  evalAut : Aut → Gade → ℂ
  evalAut_injective : Function.Injective evalAut
  evalAut_add : ∀ (f f' : Aut) (g : Gade), evalAut (f + f') g = evalAut f g + evalAut f' g
  evalAut_smul : ∀ (c : ℂ) (f : Aut) (g : Gade), evalAut (c • f) g = c * evalAut f g
  /-- Right translation acts on values by `(f · h)(g) = f (g h)`. -/
  evalAut_act : ∀ (f : Aut) (h g : Gade), evalAut (autAct f h) g = evalAut f (g * h)
  /-- Automorphic functions are left invariant under the rational points. -/
  evalAut_rat : ∀ (γ : Grat) (f : Aut) (g : Gade), evalAut f (diag γ * g) = evalAut f g
  /-- Every left `G(F)`-invariant function on `G(𝔸_F)` is an automorphic function. -/
  evalAut_surjective : ∀ f : Gade → ℂ,
    (∀ (γ : Grat) (g : Gade), f (diag γ * g) = f g) → ∃ F : Aut, evalAut F = f

instance (D : AutomorphicDatum) (v : D.Place) : Group (D.Gloc v) := D.grpLoc v
instance (D : AutomorphicDatum) : Group D.Gade := D.grpAde
instance (D : AutomorphicDatum) : Group D.Grat := D.grpRat
instance (D : AutomorphicDatum) : AddCommGroup D.Aut := D.acgAut
instance (D : AutomorphicDatum) : Module ℂ D.Aut := D.modAut

end NLabRelativeLanglands


