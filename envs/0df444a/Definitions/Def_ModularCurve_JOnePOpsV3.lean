-- Prove2me | Definitions.Def_ModularCurve_JOnePOpsV3
-- name    : ModularCurve_JOnePOpsV3
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/a4f0d2b5-db80-55d9-a1ce-cba5dca00c15
-- title:
--   Hecke and diamond operators on a Néron special-fibre datum
-- statement:
--   The ambient datum is [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](../def/ModularCurve_JOnePGeom.html#L9): three abelian groups $J^0_s$, $J_I$, $J_E$, an additive subgroup $T \subseteq J^0_s$ (the toric part), and an additive map $\pi \colon J^0_s \to J_I \times J_E$ which is required to be surjective with kernel exactly $T$; so $J^0_s/T \cong J_I \times J_E$. Over such a datum (with $p$ nonzero), `NeronSpecialFibreOpsV3` is a structure bundling operators together with the relations they satisfy, each relation being a field of the structure.
--
--   The data fields are: for every natural number $\ell$, additive endomorphisms $\mathrm{hecke}\,\ell$ of $J^0_s$, $\mathrm{heckeI}\,\ell$ of $J_I$ and $\mathrm{heckeE}\,\ell$ of $J_E$; two group homomorphisms $\mathrm{diamondP}, \mathrm{inertia} \colon (\mathbb{Z}/p)^\times \to \operatorname{AddAut}(J^0_s)$; a family $\mathrm{diamondN} \colon \mathbb{N} \to \operatorname{End}(J^0_s)$ and a family $\mathrm{diamondNI} \colon \mathbb{N} \to \operatorname{End}(J_I)$; an additive automorphism $w$ of $J^0_s$; and additive endomorphisms $\mathrm{verI}$ of $J_I$ and $\mathrm{frobE}$ of $J_E$.
--
--   The axiom fields are: for $\ell \neq p$, $\pi$ intertwines the Hecke operators, $\pi(\mathrm{hecke}\,\ell\,(x)) = (\mathrm{heckeI}\,\ell\,(\pi(x)_1), \mathrm{heckeE}\,\ell\,(\pi(x)_2))$; the endomorphisms $\mathrm{hecke}\,\ell$ of $J^0_s$ commute with one another; each $\mathrm{diamondP}\,b$ and each $\mathrm{inertia}\,b$ commutes with every $\mathrm{hecke}\,\ell$; and both $\mathrm{diamondP}\,b$ and $\mathrm{inertia}\,b$ fix every element of $T$ pointwise. No field relates $\mathrm{hecke}\,p$ to $\mathrm{verI}$ and $\mathrm{frobE}$, so the Eichler–Shimura relation at $p$ is not part of this axiomatisation; likewise $w$, $\mathrm{diamondN}$ and $\mathrm{diamondNI}$ are carried as data with no constraints imposed here.
--
--   **Relation to Mathlib.** Mathlib has no axiomatisation of the special fibre of a Jacobian at a prime of bad reduction; this structure is the project's own, built only from Mathlib's `AddMonoidHom`, `AddEquiv`, `AddSubgroup` and the group `AddAut` (the latter via the project's Mathlib-compatibility module).
--
--   **Where it is used.** The structure provides the abstract interface through which the level-$p$ part of the argument (Ribet-style level lowering at $p$, and the descent for $U_p$ on the norm-free part of the special fibre) manipulates Hecke, diamond and inertia operators on the special fibre at $p$ of the Néron model of the Jacobian of the relevant modular curve, without reference to the geometry that produces them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JOnePOpsV3.lean

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

structure NeronSpecialFibreOpsV3 [NeZero p] (G : NeronSpecialFibreGeom p) where

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

end JOneP

end ModularCurve


