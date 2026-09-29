-- Prove2me | Definitions.Def_ModularCurve_JOnePOps
-- name    : ModularCurve_JOnePOps
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/cda9169e-0cbc-5d69-b10f-89840c441b14
-- title:
--   Operator package on a Néron special fibre datum
-- statement:
--   Over a fixed natural number $p$ and a geometric datum `G : NeronSpecialFibreGeom p` — that is, abelian groups $J^0_s$, $J_I$, $J_E$, an additive subgroup $T \subseteq J^0_s$ (the field `torus`), and a surjective additive map $\pi \colon J^0_s \to J_I \times J_E$ whose kernel is exactly $T$ — the module defines a structure [`ModularCurve.JOneP.NeronSpecialFibreOps G`](../def/ModularCurve_JOnePOps.html#L13) packaging operators on that datum together with the relations they are required to satisfy. The data fields are: families `hecke`, `heckeI`, `heckeE` of additive endomorphisms of $J^0_s$, $J_I$, $J_E$ indexed by $\mathbb{N}$; two group homomorphisms `diamondP` and `inertia` from $(\mathbb{Z}/p)^\times$ into the additive automorphism group of $J^0_s$; a family `diamondN` of additive endomorphisms of $J^0_s$ indexed by $\mathbb{N}$; an additive automorphism `w` of $J^0_s$; additive endomorphisms `verI` of $J_I$ and `frobE` of $J_E$; and a family `diamondNI` of additive endomorphisms of $J_I$.
--
--   The law fields are carried as hypotheses of the structure: the endomorphisms `hecke ℓ` commute with one another, and each commutes with every `diamondP b` and every `inertia b`; both `diamondP b` and `inertia b` fix every element of $T$; for $\ell \neq p$ the projection is equivariant, $\pi(T_\ell x) = (T_\ell \pi(x)_1, T_\ell \pi(x)_2)$ with the three `hecke` families at index $\ell$; and at $\ell = p$ the Eichler–Shimura-shaped identity $\pi(T_p x) = \bigl(\langle p\rangle\,V(\pi(x)_1),\, F(\pi(x)_2)\bigr)$ holds for all $x \in J^0_s$, where $\langle p \rangle =$ `diamondNI p`, $V =$ `verI` and $F =$ `frobE`. No law constrains `diamondN` or `w`, which are pure data here; nothing is constructed or proved in the module, so an instance of the structure must supply all operators and all relations.
--
--   **Relation to Mathlib.** Mathlib has no notion of the special fibre of the Néron model of a modular Jacobian or of Hecke, diamond, Verschiebung and Frobenius operators on it; this structure is the project's own. The multiplicative structure on `AddAut` used in the types of `diamondP` and `inertia` is the one vendored in `Compat_Mathlib430` as a renamed copy of the Mathlib v4.30.0 group instance.
--
--   **Where it is used.** The structure records, in purely group-theoretic form, the operator side of the description of the special fibre at $p$ of the Néron model of the Jacobian of $X_1(Mp)$: inertia at $p$ acting through $(\mathbb{Z}/p)^\times$ and trivially on the toric part, and $T_p$ inducing $\langle p\rangle V$ on one component and Frobenius on the other. Such data feed the weight- and level-lowering analysis at $p$ that precedes the application of modularity lifting in the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JOnePOps.lean

import Mathlib
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModularCurve

namespace JOneP

variable {p : ℕ}

structure NeronSpecialFibreOps (G : NeronSpecialFibreGeom p) where

  hecke : ℕ → (G.J0s →+ G.J0s)
  heckeI : ℕ → (G.JI →+ G.JI)
  heckeE : ℕ → (G.JE →+ G.JE)
  proj_hecke : ∀ (ℓ : ℕ) (x : G.J0s), ℓ ≠ p → G.proj (hecke ℓ x) = (heckeI ℓ (G.proj x).1, heckeE ℓ (G.proj x).2)

  diamondP : (ZMod p)ˣ →* AddAut G.J0s
  diamondN : ℕ → (G.J0s →+ G.J0s)
  w : G.J0s ≃+ G.J0s
  inertia : (ZMod p)ˣ →* AddAut G.J0s

  verI : G.JI →+ G.JI
  frobE : G.JE →+ G.JE
  diamondNI : ℕ → (G.JI →+ G.JI)

  hecke_comm : ∀ ℓ ℓ' : ℕ, (hecke ℓ).comp (hecke ℓ') = (hecke ℓ').comp (hecke ℓ)
  diamondP_hecke : ∀ (b : (ZMod p)ˣ) (ℓ : ℕ) (x : G.J0s), diamondP b (hecke ℓ x) = hecke ℓ (diamondP b x)
  inertia_hecke : ∀ (b : (ZMod p)ˣ) (ℓ : ℕ) (x : G.J0s), inertia b (hecke ℓ x) = hecke ℓ (inertia b x)
  diamondP_torus : ∀ (b : (ZMod p)ˣ) (x : G.J0s), x ∈ G.torus → diamondP b x = x
  inertia_torus : ∀ (b : (ZMod p)ˣ) (x : G.J0s), x ∈ G.torus → inertia b x = x

  proj_heckeP : ∀ x : G.J0s, G.proj (hecke p x) = (diamondNI p (verI (G.proj x).1), frobE (G.proj x).2)

end JOneP

end ModularCurve


