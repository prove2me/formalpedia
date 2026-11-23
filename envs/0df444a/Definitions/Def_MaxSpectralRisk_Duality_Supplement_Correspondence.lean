-- Prove2me | Definitions.Def_MaxSpectralRisk_Duality_Supplement_Correspondence
-- name    : MaxSpectralRisk_Duality_Supplement_Correspondence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:05:57.882983+00:00
-- url     : https://prove2.me/theorems/acdd8d0c-6226-44cf-b805-44ab57652181
-- title:
--   Definition 2 — lower hemicontinuity and continuous correspondences
-- statement:
--   For topological spaces $E,F$, a correspondence $G:E\rightrightarrows F$ is lower hemicontinuous when, for every $x\in E$ and open $O\subseteq F$ meeting $G(x)$, all sufficiently nearby values $G(y)$ also meet $O$:
--   $$
--   G(x)\cap O\ne\varnothing\quad\Longrightarrow\quad
--   \exists U\in\mathcal N(x),\ \forall y\in U,\ G(y)\cap O\ne\varnothing.
--   $$
--   It is continuous as a correspondence when it is both upper and lower hemicontinuous. The upper half uses the published open-set predicate `CoupledLearning.IsUHC` on the whole domain. These notions provide the exact two conclusions of Theorem 2.
--
--   **Formalization Note** On metric spaces the neighbourhood formulation is equivalent to Definition 2's positive-radius ball formulation. The printed upper-half centre $x$ is read as the bound point $v$, as required by the surrounding sentence. No compactness or nonemptiness is built into these definitions.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 12, Definition 2

import Mathlib
import Definitions.Def_CoupledLearning_IsUHC

namespace MaxSpectralRisk.Duality.Supplement

open Filter Topology

/-- Definition 2, p. 12: the open-set definition of lower hemicontinuity.
On metric spaces an eventual neighbourhood contains a ball of positive radius. -/
def IsLHC {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (G : E → Set F) : Prop :=
  ∀ x, ∀ O : Set F, IsOpen O → (G x ∩ O).Nonempty →
    ∀ᶠ y in 𝓝 x, (G y ∩ O).Nonempty

/-- Definition 2, p. 12: both upper and lower hemicontinuity, on the full domain.
The upper half uses the existing published open-set definition. -/
def ContinuousCorrespondence {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (G : E → Set F) : Prop :=
  CoupledLearning.IsUHC Set.univ G ∧ IsLHC G

end MaxSpectralRisk.Duality.Supplement


