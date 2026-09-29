-- Prove2me | Definitions.Def_ModularCurve_JOnePOpsV2
-- name    : ModularCurve_JOnePOpsV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/fac81fa0-7542-5cdf-a15c-ce435909ae8b
-- title:
--   Operator package on a Néron special-fibre datum for J1​(p)
-- statement:
--   Over a prime $p$ and a datum $G$ of type `NeronSpecialFibreGeom p` — abelian groups $G.J0s$, $G.JI$, $G.JE$, an additive subgroup $G.torus \subseteq G.J0s$, and a surjective homomorphism $G.proj\colon G.J0s \to G.JI \times G.JE$ whose kernel is exactly $G.torus$ — the structure `NeronSpecialFibreOpsV2` bundles a family of operators on that datum together with the relations they are required to satisfy, all as fields.
--
--   The data fields are: for each natural number $\ell$, additive endomorphisms `hecke` $\ell$ of $G.J0s$, `heckeI` $\ell$ of $G.JI$ and `heckeE` $\ell$ of $G.JE$; a monoid homomorphism `diamondP` from $(\mathbb{Z}/p)^\times$ to the additive automorphism group of $G.J0s$, and a second such homomorphism `inertia`; a family `diamondN` of additive endomorphisms of $G.J0s$ indexed by $\mathbb{N}$, together with a family `diamondNI` of additive endomorphisms of $G.JI$; an additive automorphism `w` of $G.J0s$; and endomorphisms `verI` of $G.JI$ and `frobE` of $G.JE$. The relation fields assert: for $\ell \ne p$ the projection intertwines the Hecke operators, $G.proj(\mathrm{hecke}_\ell\, x) = (\mathrm{heckeI}_\ell (G.proj\,x)_1, \mathrm{heckeE}_\ell (G.proj\,x)_2)$; the endomorphisms $\mathrm{hecke}_\ell$ commute with one another, and each commutes with every $\mathrm{diamondP}\,b$ and every $\mathrm{inertia}\,b$; both $\mathrm{diamondP}\,b$ and $\mathrm{inertia}\,b$ fix every element of $G.torus$ pointwise; and, in place of an unconditional relation at $\ell = p$, a restricted Eichler–Shimura relation: for every $x \in G.J0s$ with $\sum_{b \in (\mathbb{Z}/p)^\times} \mathrm{diamondP}\,b\,(x) = 0$ one has $G.proj(\mathrm{hecke}_p\,x) = \bigl(\mathrm{diamondNI}_p(\mathrm{verI}\,(G.proj\,x)_1),\ \mathrm{frobE}\,(G.proj\,x)_2\bigr)$. No field constrains `w` or `diamondN`, and the Hecke indices range over all natural numbers without any multiplicativity or Eichler–Shimura condition beyond those listed. The structure is thus an axiomatic interface: an inhabitant must supply all the operators and verify exactly these laws.
--
--   **Relation to Mathlib.** Mathlib has no Néron models of Jacobians of modular curves, nor Hecke, diamond, Verschiebung or Frobenius operators on their special fibres; the geometric datum and this operator package are the project's own axiomatic interface, phrased purely in terms of abelian groups and additive homomorphisms.
--
--   **Where it is used.** The package records the structure of the special fibre at $p$ of the Néron model of the Jacobian of the modular curve of level $\Gamma_1(M) \cap \Gamma_1(p)$: two components with Jacobians $G.JI$ and $G.JE$, a toric part on which the inertia action factoring through $(\mathbb{Z}/p)^\times$ is trivial, and $T_p$ acting as $\langle p \rangle V$ on one component and as Frobenius on the other. It supports the weight- and level-lowering analysis at $p$ that feeds into the modularity route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JOnePOpsV2.lean

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

structure NeronSpecialFibreOpsV2 [NeZero p] (G : NeronSpecialFibreGeom p) where

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

  proj_heckeP : ∀ x : G.J0s, (∑ b : (ZMod p)ˣ, diamondP b x) = 0 →
    G.proj (hecke p x) = (diamondNI p (verI (G.proj x).1), frobE (G.proj x).2)

end JOneP

end ModularCurve


