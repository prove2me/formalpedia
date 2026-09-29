-- Prove2me | Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechReversal
-- name    : AlgebraicGeometry_OrderedAffineCoverCechReversal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/57318f3f-87f1-5924-88d8-7dea4f19c114
-- title:
--   Reversal operator on ordered Čech cochains
-- statement:
--   Throughout, $K$ is an ordered affine cover of a scheme $V$ — a finite linearly ordered index type $\iota$ together with affine opens $U_i \subseteq V$ whose supremum is $\top$ — and $F$ is an `OModulePresheaf` over a morphism $\pi : V \to \operatorname{Spec} R$, that is, an assignment $U \mapsto F(U)$ of $R$-modules with $\Gamma(V,U)$-module structures compatible over $R$ and $R$-linear restriction maps `F.res` functorial in inclusions. For $n : \mathbb{N}$, an unordered multi-index is a tuple $t : \mathrm{Fin}(n+1) \to \iota$ (the type `K.OIdx n`), with associated open $K.\mathrm{ointer}\,t = \bigsqcap_j U_{t(j)}$, and the ordered cochain module `F.ocochain K n` is the product $\prod_t F(K.\mathrm{ointer}\,t)$.
--
--   Three elementary lemmas record the effect of reversing a tuple, i.e. of precomposing with `Fin.rev`: the reversal is an involution on tuples, `comp_rev_comp_rev` stating $(t \circ \mathrm{rev}) \circ \mathrm{rev} = t$, and the two opens $K.\mathrm{ointer}\,t$ and $K.\mathrm{ointer}(t \circ \mathrm{rev})$ satisfy each of the two inequalities `ointer_le_ointer_comp_rev` and `ointer_comp_rev_le_ointer` (so they are equal as opens, but the comparison is supplied as inequalities, all transport of sections being performed by `F.res`).
--
--   The object defined is the reversal endomorphism `F.orev K n`, an $R$-linear map from `F.ocochain K n` to itself, given componentwise by
--   $$(\mathrm{orev}\,c)(t_0,\dots,t_n) \;=\; (-1)^{n(n+1)/2}\, c(t_n,\dots,t_0)\big|_{U_t},$$
--   where the restriction is along `ointer_le_ointer_comp_rev` and the exponent $n(n+1)/2$ is natural-number division. The companion lemma `orev_apply` states exactly this formula for the value of `F.orev K n c` at a tuple $t$. No compatibility of `orev` with the ordered differential, with the cup product, or with the alternating-cochain maps is asserted here; only the operator and the sign convention are fixed.
--
--   **Relation to Mathlib.** Mathlib has no Čech complex for an ordered affine cover of a scheme with coefficients in a presheaf of modules of this shape; the cover structure, the cochain modules and this reversal operator are the project's own, built on Mathlib's scheme, affine open and linear algebra API.
--
--   **Where it is used.** The sign $(-1)^{n(n+1)/2}$ is the one for which reversal is a cochain map that interchanges the two factors of the ordered cup product up to the sign $(-1)^{ab}$; the operator therefore serves in establishing graded commutativity of the cup product on Čech cohomology within the coherent-cohomology machinery used for the scheme-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCechReversal.lean

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

theorem comp_rev_comp_rev {n : ℕ} (t : K.OIdx n) : (t ∘ Fin.rev) ∘ Fin.rev = t :=
  funext fun j => congrArg t (Fin.rev_rev j)

theorem ointer_le_ointer_comp_rev {n : ℕ} (t : K.OIdx n) : K.ointer t ≤ K.ointer (t ∘ Fin.rev) :=
  le_iInf fun j => iInf_le _ (Fin.rev j)

theorem ointer_comp_rev_le_ointer {n : ℕ} (t : K.OIdx n) : K.ointer (t ∘ Fin.rev) ≤ K.ointer t :=
  le_iInf fun j => (iInf_le (fun i => K.U ((t ∘ Fin.rev) i)) (Fin.rev j)).trans
    (le_of_eq (congrArg (fun i => K.U (t i)) (Fin.rev_rev j)))

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

def orev (n : ℕ) : F.ocochain K n →ₗ[R] F.ocochain K n :=
  LinearMap.pi fun t => ((-1 : ℤ) ^ (n * (n + 1) / 2)) •
    ((F.res (K.ointer_le_ointer_comp_rev t)).comp (LinearMap.proj (t ∘ Fin.rev)))

theorem orev_apply (n : ℕ) (c : F.ocochain K n) (t : K.OIdx n) :
    F.orev K n c t = ((-1 : ℤ) ^ (n * (n + 1) / 2)) • F.res (K.ointer_le_ointer_comp_rev t) (c (t ∘ Fin.rev)) := by
  simp only [orev, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]

end OModulePresheaf

end AlgebraicGeometry

end


