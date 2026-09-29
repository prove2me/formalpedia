-- Prove2me | Definitions.Def_Dieudonne_HondaSelfExt
-- name    : Dieudonne_HondaSelfExt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/3973105c-da30-5f7a-bacf-1575de55ea5c
-- title:
--   Self-extension module of a Honda system: extension and inner pairs
-- statement:
--   The standing data are a commutative ring $\mathcal{O}$, an element $\ell \in \mathcal{O}$, an $\mathcal{O}$-module $D$, and a Honda system $H$ for $\ell$ on $D$, i.e. $\mathcal{O}$-linear endomorphisms $F, V$ of $D$ with $F \circ V = V \circ F = \ell \cdot \mathrm{id}$ together with a submodule $L \subseteq D$ satisfying: every $x \in L$ lying in $\operatorname{range} F$ is of the form $\ell y$ with $y \in L$; $\ell y \in \operatorname{range} F$ for all $y \in L$; $\operatorname{range} F + L = D$; and $V$ is injective on $L$.
--
--   Four submodules and one linear map are defined. `extPairs` is the submodule of pairs $(X, Y) \in \operatorname{End}_{\mathcal{O}}(D)^2$ satisfying $F \circ Y + X \circ V = 0$ and $V \circ X + Y \circ F = 0$ — the conditions for the block-triangular pair $\begin{pmatrix} F & X \\ 0 & F\end{pmatrix}$, $\begin{pmatrix} V & Y \\ 0 & V\end{pmatrix}$ on $D \times D$ to satisfy the two Dieudonné identities. `filteredEnd` is the submodule of $a \in \operatorname{End}_{\mathcal{O}}(D)$ with $a(L) \subseteq L$. `innerDerivation` is the $\mathcal{O}$-linear map $a \mapsto (F \circ a - a \circ F,\ V \circ a - a \circ V)$, and `innerPairs` is the image of `filteredEnd` under it; `innerPairs_le_extPairs` records that it lands in `extPairs`, by $F(Vx) = V(Fx) = \ell x$. `endHonda` is the intersection of `filteredEnd` with the kernel of `innerDerivation`, characterised as those $a$ with $a(L) \subseteq L$, $F \circ a = a \circ F$ and $V \circ a = a \circ V$. Finally `selfExt` is the quotient of the submodule `extPairs`, viewed as a type, by the preimage of `innerPairs` under the inclusion of `extPairs`, and is equipped with its abelian group and $\mathcal{O}$-module structures. Membership lemmas unfold `extPairs`, `filteredEnd` and `endHonda`, and `innerDerivation_apply` evaluates the map.
--
--   Thus `selfExt` is a presentation of the self-extension group in terms of a fixed splitting of the underlying module as $D \times D$ with Hodge submodule $L \times L$, rather than a Yoneda Ext group defined categorically.
--
--   **Relation to Mathlib.** Mathlib has no Dieudonné modules or Honda systems; these notions, and the self-extension presentation built from them, are the project's own, formulated with Mathlib's submodule, endomorphism and quotient-module machinery.
--
--   **Where it is used.** These constructions provide the explicit presentation of $\operatorname{Ext}^1(H, H)$ used to compute the tangent space of the flat (Fontaine–Laffaille) deformation functor at $\ell = 0$, and hence the dimension bound on flat deformation rings entering the modularity lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Dieudonne_HondaSelfExt.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LinearMap Submodule Function

universe u v

namespace Deformation

namespace HondaSystem

variable {𝓞 : Type u} [CommRing 𝓞] {ℓ : 𝓞} {D : Type v} [AddCommGroup D] [Module 𝓞 D]
  (H : HondaSystem ℓ D)

def extPairs : Submodule 𝓞 (Module.End 𝓞 D × Module.End 𝓞 D) where
  carrier := {XY | H.F ∘ₗ XY.2 + XY.1 ∘ₗ H.V = 0 ∧ H.V ∘ₗ XY.1 + XY.2 ∘ₗ H.F = 0}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    obtain ⟨ha₁, ha₂⟩ := ha
    obtain ⟨hb₁, hb₂⟩ := hb
    constructor
    · rw [Prod.snd_add, Prod.fst_add, comp_add, add_comp, add_add_add_comm, ha₁, hb₁, add_zero]
    · rw [Prod.snd_add, Prod.fst_add, comp_add, add_comp, add_add_add_comm, ha₂, hb₂, add_zero]
  smul_mem' c a ha := by
    obtain ⟨ha₁, ha₂⟩ := ha
    constructor
    · rw [Prod.smul_snd, Prod.smul_fst, comp_smul, smul_comp, ← smul_add, ha₁, smul_zero]
    · rw [Prod.smul_snd, Prod.smul_fst, comp_smul, smul_comp, ← smul_add, ha₂, smul_zero]

theorem mem_extPairs_iff (XY : Module.End 𝓞 D × Module.End 𝓞 D) :
    XY ∈ H.extPairs ↔ H.F ∘ₗ XY.2 + XY.1 ∘ₗ H.V = 0 ∧ H.V ∘ₗ XY.1 + XY.2 ∘ₗ H.F = 0 :=
  Iff.rfl

def filteredEnd : Submodule 𝓞 (Module.End 𝓞 D) where
  carrier := {a | ∀ x ∈ H.L, a x ∈ H.L}
  zero_mem' := fun x _ => by simp
  add_mem' {a b} ha hb := fun x hx => by
    simpa using H.L.add_mem (ha x hx) (hb x hx)
  smul_mem' c a ha := fun x hx => by
    simpa using H.L.smul_mem c (ha x hx)

theorem mem_filteredEnd_iff (a : Module.End 𝓞 D) :
    a ∈ H.filteredEnd ↔ ∀ x ∈ H.L, a x ∈ H.L :=
  Iff.rfl

def innerDerivation : Module.End 𝓞 D →ₗ[𝓞] Module.End 𝓞 D × Module.End 𝓞 D where
  toFun a := (H.F ∘ₗ a - a ∘ₗ H.F, H.V ∘ₗ a - a ∘ₗ H.V)
  map_add' a b := by
    ext x <;> simp [sub_add_sub_comm]
  map_smul' c a := by
    ext x <;> simp [smul_sub]

theorem innerDerivation_apply (a : Module.End 𝓞 D) :
    H.innerDerivation a = (H.F ∘ₗ a - a ∘ₗ H.F, H.V ∘ₗ a - a ∘ₗ H.V) :=
  rfl

def innerPairs : Submodule 𝓞 (Module.End 𝓞 D × Module.End 𝓞 D) :=
  H.filteredEnd.map H.innerDerivation

def endHonda : Submodule 𝓞 (Module.End 𝓞 D) :=
  H.filteredEnd ⊓ LinearMap.ker H.innerDerivation

theorem mem_endHonda_iff (a : Module.End 𝓞 D) :
    a ∈ H.endHonda ↔ (∀ x ∈ H.L, a x ∈ H.L) ∧ H.F ∘ₗ a = a ∘ₗ H.F ∧ H.V ∘ₗ a = a ∘ₗ H.V := by
  simp only [endHonda, Submodule.mem_inf, mem_filteredEnd_iff, LinearMap.mem_ker,
    innerDerivation_apply, Prod.mk_eq_zero, sub_eq_zero]

theorem innerPairs_le_extPairs : H.innerPairs ≤ H.extPairs := by
  rintro _ ⟨a, -, rfl⟩
  rw [mem_extPairs_iff, innerDerivation_apply]
  constructor
  · ext x
    simp [H.toDieudonneDatum.F_V_apply]
  · ext x
    simp [H.toDieudonneDatum.V_F_apply]

def selfExt : Type v :=
  ↥H.extPairs ⧸ (H.innerPairs.comap H.extPairs.subtype)

instance instAddCommGroupSelfExt : AddCommGroup H.selfExt :=
  inferInstanceAs (AddCommGroup (↥H.extPairs ⧸ (H.innerPairs.comap H.extPairs.subtype)))

instance instModuleSelfExt : Module 𝓞 H.selfExt :=
  inferInstanceAs (Module 𝓞 (↥H.extPairs ⧸ (H.innerPairs.comap H.extPairs.subtype)))

end HondaSystem

end Deformation


