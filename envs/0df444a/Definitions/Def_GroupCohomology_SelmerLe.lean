-- Prove2me | Definitions.Def_GroupCohomology_SelmerLe
-- name    : GroupCohomology_SelmerLe
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/a55e6d63-95a4-58bd-ad07-3871c59436f4
-- title:
--   One-sided Greenberg–Wiles inequality and Selmer comparison step
-- statement:
--   The standing context is a field $k$, a group $\Gamma$, a finite index type $\iota$ with groups $\Gamma_v$ and homomorphisms $\mathrm{loc}_v:\Gamma_v\to\Gamma$, two objects $M,M'$ of `Rep k Γ`, and for each $v$ a $k$-bilinear pairing `pairing v` between $H^1$ of the restriction of $M$ along $\mathrm{loc}_v$ and $H^1$ of the restriction of $M'$. Throughout, for a family $L$ of local conditions $L_v\subseteq H^1(\Gamma_v,M)$, `selmer loc M L` is the intersection over $v$ of the preimages of $L_v$ under the restriction maps $H^1(\Gamma,M)\to H^1(\Gamma_v,M)$, and `dualConditions loc M M' pairing L` is the family whose $v$-th member consists of those $w$ with `pairing v x w = 0` for all $x\in L_v$; $\rho$-invariants play the role of $H^0$.
--
--   `greenbergWilesLe` is the predicate asserting the single inequality of natural numbers
--   $$\dim_k \mathrm{Sel}_L(M)+\dim_k (M')^{\Gamma}+\sum_v \dim_k M^{\Gamma_v}\ \le\ \dim_k \mathrm{Sel}_{L^{\perp}}(M')+\dim_k M^{\Gamma}+\sum_v \dim_k L_v,$$
--   with all dimensions taken as `Module.finrank` (hence $0$ in the infinite-dimensional case). `greenbergWilesLe_of_greenbergWilesEq` deduces it from the corresponding equality predicate `greenbergWilesEq` of the imported module. `IsGreenbergWilesLeDatum` is a `Prop`-valued structure bundling, for a given family $L$: finite-dimensionality of the Selmer group, of the dual Selmer group attached to $L^{\perp}$, and of each $L_v$, together with the above inequality as a field; `IsGreenbergWilesDatum.toLe` converts the equality-bearing datum of the imported module into this weaker one.
--
--   `selmerComparisonStep L L'` is the predicate stating that if $L_v\subseteq L'_v$ for all $v$ then
--   $$\dim_k \mathrm{Sel}_{L'}(M)+\dim_k \mathrm{Sel}_{L^{\perp}}(M')+\sum_v \dim_k L_v\ \le\ \dim_k \mathrm{Sel}_{L}(M)+\dim_k \mathrm{Sel}_{L'^{\perp}}(M')+\sum_v \dim_k L'_v,$$
--   a subtraction-free form of the statement that enlarging the local conditions increases the Selmer defect by at most the change in local dimensions. `selmerComparisonStep_refl` records the case $L'=L$, where both sides agree.
--
--   **Relation to Mathlib.** Mathlib supplies the ingredients ($H^1$ of a representation and its functoriality, `Rep.res`, `Representation.invariants`, `Module.finrank`) but has no Selmer group attached to a family of local conditions; the Selmer module, the orthogonal complement under a pairing and the Greenberg–Wiles predicates are the project's own, defined in the imported module and weakened to an inequality here.
--
--   **Where it is used.** The Taylor–Wiles patching argument uses only the $\le$ direction of the Greenberg–Wiles formula, bounding the dimension of the Selmer group for the chosen local conditions in terms of the dual Selmer group, the global invariants and the local dimensions; isolating that direction, together with the comparison step for nested families of local conditions, allows the bound to be obtained by iterating a local-duality comparison from a base family rather than invoking the full global Euler characteristic formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_SelmerLe.lean

import Definitions.Def_GroupCohomology_Selmer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} [Fintype ι] {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ) (M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

def greenbergWilesLe (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop :=
  finrank k (selmer loc M L)
      + finrank k M'.ρ.invariants
      + ∑ v, finrank k (Rep.res (loc v) M).ρ.invariants
    ≤ finrank k (selmer loc M' (dualConditions loc M M' pairing L))
      + finrank k M.ρ.invariants
      + ∑ v, finrank k (L v)

theorem greenbergWilesLe_of_greenbergWilesEq
    {L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : greenbergWilesEq loc M M' pairing L) : greenbergWilesLe loc M M' pairing L :=
  le_of_eq h

structure IsGreenbergWilesLeDatum (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    Prop where

  finite_selmer : FiniteDimensional k (selmer loc M L)

  finite_dualSelmer :
    FiniteDimensional k (selmer loc M' (dualConditions loc M M' pairing L))

  finite_local : ∀ v, FiniteDimensional k (L v)

  le : greenbergWilesLe loc M M' pairing L

theorem IsGreenbergWilesDatum.toLe {L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : IsGreenbergWilesDatum loc M M' pairing L) :
    IsGreenbergWilesLeDatum loc M M' pairing L where
  finite_selmer := h.finite_selmer
  finite_dualSelmer := h.finite_dualSelmer
  finite_local := h.finite_local
  le := greenbergWilesLe_of_greenbergWilesEq loc M M' pairing h.formula

def selmerComparisonStep (L L' : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop :=
  (∀ v, L v ≤ L' v) →
    finrank k (selmer loc M L')
        + finrank k (selmer loc M' (dualConditions loc M M' pairing L))
        + ∑ v, finrank k (L v)
      ≤ finrank k (selmer loc M L)
          + finrank k (selmer loc M' (dualConditions loc M M' pairing L'))
          + ∑ v, finrank k (L' v)

theorem selmerComparisonStep_refl (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    selmerComparisonStep loc M M' pairing L L := fun _ => le_refl _

end groupCohomology


