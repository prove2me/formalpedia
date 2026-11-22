-- Prove2me | Definitions.Def_MasulloGRH_ExpDecayStages
-- name    : MasulloGRH_ExpDecayStages
-- status  : Definition
-- author  : @sflicht
-- created : 2026-11-21T18:21:06.13618+00:00
-- url     : https://prove2.me/theorems/6f2d97ac-2e7f-4eb9-befe-bad2d5e92422
-- title:
--   The stages $\mathcal S_I(k,G)$ of $k$-invariant elements of $\mathcal S_I(G)$ with their projective topology
-- statement:
--   Let $(G,|\cdot|_G)$ be an $\mathbb R_{>0}$-modulated abelian topological group, $I\subset\mathbb R$ an interval, and $k\le G$ a subgroup.
--
--   1. $\mathcal S_I(k,G)\subseteq\mathcal S_I(G)$ is the linear subspace of $k$-invariant elements: $\phi(gh)=\phi(g)$ for all $g\in G$, $h\in k$.
--   2. $\mathcal S_I(k,G)$ carries the projective topology of the operators
--   $$T_a\colon\mathcal S_I(k,G)\to\mathcal S(G/k),\qquad T_a(\phi)=|\cdot|_G^a\,\phi\quad(a\in I),$$
--   i.e. the coarsest topology making all $T_a$ continuous.
--   3. $\iota_k\colon\mathcal S_I(k,G)\to\mathcal S_I(G)$ denotes the inclusion.
--
--   These are the spaces whose locally convex inductive limit over the good subgroups $k$ defines the topology of $\mathcal S_I(G)$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Definition D.3.3.3 (p. 805)

import Definitions.Def_MasulloGRH_ExpDecaySpaces

/-!
# The stages `S_I(k, G)` of the space `S_I(G)`

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix D,
Definition D.3.3.3 (p. 805).
-/

namespace MasulloGRH

open Topology

noncomputable section

universe u

variable (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The subspace `S_I(k, G)` of `k`-invariant elements of `S_I(G)` (D.3.3.1). -/
def expDecayInvSubmodule (m : G → ℝ) (I : Set ℝ) (k : Subgroup G) :
    Submodule ℂ (ExpDecaySchwartz G m I) where
  carrier := {ϕ | ∀ h ∈ k, ∀ g : G, ϕ.toFun (g * h) = ϕ.toFun g}
  add_mem' {ϕ ψ} hϕ hψ h hh g := by
    show ϕ.1 (g * h) + ψ.1 (g * h) = ϕ.1 g + ψ.1 g
    rw [show ϕ.1 (g * h) = ϕ.1 g from hϕ h hh g, show ψ.1 (g * h) = ψ.1 g from hψ h hh g]
  zero_mem' h _ g := rfl
  smul_mem' c ϕ hϕ h hh g := by
    show c * ϕ.1 (g * h) = c * ϕ.1 g
    rw [show ϕ.1 (g * h) = ϕ.1 g from hϕ h hh g]

/-- The stage `S_I(k, G)` (Definition D.3.3.3) as a type. -/
def ExpDecayStage (m : G → ℝ) (I : Set ℝ) (k : Subgroup G) : Type u :=
  ↥(expDecayInvSubmodule G m I k)

instance (m : G → ℝ) (I : Set ℝ) (k : Subgroup G) : AddCommGroup (ExpDecayStage G m I k) :=
  inferInstanceAs (AddCommGroup ↥(expDecayInvSubmodule G m I k))

instance (m : G → ℝ) (I : Set ℝ) (k : Subgroup G) : Module ℂ (ExpDecayStage G m I k) :=
  inferInstanceAs (Module ℂ ↥(expDecayInvSubmodule G m I k))

/-- The projective topology of the operators `T_a : S_I(k, G) → S(G/k)`, `a ∈ I` (D.3.3.2). -/
instance (m : G → ℝ) (I : Set ℝ) (k : Subgroup G) : TopologicalSpace (ExpDecayStage G m I k) :=
  ⨅ (a : ℝ) (_ : a ∈ I),
    TopologicalSpace.induced (fun ϕ : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k a ϕ.1)
      inferInstance

/-- The inclusion `S_I(k, G) → S_I(G)`. -/
def ExpDecayStage.incl (m : G → ℝ) (I : Set ℝ) (k : Subgroup G) :
    ExpDecayStage G m I k →ₗ[ℂ] ExpDecaySchwartz G m I :=
  (expDecayInvSubmodule G m I k).subtype

end

end MasulloGRH


