-- Prove2me | Definitions.Def_DualSelmer_ExtConditions
-- name    : DualSelmer_ExtConditions
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/97c73ebb-db3e-5989-8bfc-b063c0355c8b
-- title:
--   Character modules and excised local conditions for Selmer groups
-- statement:
--   Two small constructions are made in the setting of a field $k$, a group $\Gamma$, an index type $\iota$, a family of groups $\Gamma_v$ and homomorphisms $\mathrm{loc}_v : \Gamma_v \to \Gamma$, together with a representation $M : \mathrm{Rep}\,k\,\Gamma$.
--
--   First, [`groupCohomology.ofChar`](../def/DualSelmer_ExtConditions.html#L13) attaches to a character $\psi : \Gamma \to k^\times$ the one-dimensional representation $k(\psi)$: the underlying module is $k$ itself, obtained as the trivial representation of $\Gamma$ on $k$ twisted by $\psi$, so that $g$ acts as multiplication by $\psi(g)$. Here the twist of a representation $\rho$ by $\psi$ is the representation $g \mapsto \psi(g)\cdot \rho(g)$.
--
--   Second, [`groupCohomology.extConditions`](../def/DualSelmer_ExtConditions.html#L19) modifies a family of local conditions. Given a set $P \subseteq \iota$ of indices and a family $U$ assigning to each $v$ a $k$-subspace $U_v \subseteq H^1(\mathrm{Res}_{\mathrm{loc}_v} M)$, the new family sends $v$ to the zero subspace if $v \in P$ and to $U_v$ otherwise; membership in $P$ is decided classically. Thus it is the family $U$ with the conditions at the places of $P$ tightened to the strictest possible one. The two accompanying lemmas record exactly this case split: the value is $\bot$ at $v \in P$ and $U_v$ at $v \notin P$. Feeding such a family into the Selmer construction of the imported module cuts out the classes whose localisations lie in $U_v$ away from $P$ and vanish at every $v \in P$.
--
--   **Relation to Mathlib.** The character module is built from Mathlib's trivial representation and `Rep.of` using the twisting operation [`Representation.twist`](../def/GroupCohomology_Selmer.html#L15) defined in the imported Selmer module; the manipulation of families of local conditions at a set of places is the project's own, Mathlib having no notion of Selmer local conditions.
--
--   **Where it is used.** The family produced by `extConditions` is the shape of local condition used for the Selmer groups attached to Tate twists $k(\psi)$ — taking $\psi$ a power of the mod $p$ cyclotomic character and $P$ the set consisting of $p$ and the archimedean place, with $U_v$ the unramified subspace elsewhere — whose dimensions are compared with those of the dual Selmer group by the Greenberg–Wiles formula recorded in the imported module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_DualSelmer_ExtConditions.lean

import Definitions.Def_GroupCohomology_Selmer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Module Classical

universe u

namespace groupCohomology

variable {k : Type u} [Field k] {Γ : Type u} [Group Γ]

noncomputable abbrev ofChar (ψ : Γ →* kˣ) : Rep k Γ :=
  Rep.of ((Representation.trivial k Γ k).twist ψ)

variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)

noncomputable def extConditions (P : Set ι)
    (U : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) (v : ι) :
    Submodule k (H1 (Rep.res (loc v) M)) :=
  if v ∈ P then ⊥ else U v

lemma extConditions_of_mem {P : Set ι} {U : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    {v : ι} (hv : v ∈ P) : extConditions loc M P U v = ⊥ := by
  simp [extConditions, hv]

lemma extConditions_of_not_mem {P : Set ι} {U : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    {v : ι} (hv : v ∉ P) : extConditions loc M P U v = U v := by
  simp [extConditions, hv]

end groupCohomology


