-- Prove2me | Definitions.Def_ClassGroup_ModP
-- name    : ClassGroup_ModP
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/15aef7c5-5bce-5d76-8e09-f9cb19d38a85
-- title:
--   Mod-p quotients of abelian groups and of class groups
-- statement:
--   For a natural number $p$ and an additive commutative group $M$, `nsmulRange p M` is the additive subgroup of $M$ given by the image of the multiplication-by-$p$ map $x \mapsto p \cdot x$, i.e. $pM$; membership is characterised by $x \in pM \iff \exists y,\ p\cdot y = x$, and $p\cdot x$ always lies in it. The abbreviation `ModP p M` is the quotient additive group $M/pM$, and when $p \neq 0$ it is equipped with its $\mathbb{Z}/p$-module structure (every element is killed by $p$). The canonical projection `ModP.proj p M`, of type $M \to M/pM$, is an additive homomorphism; it is surjective, and `ModP.proj_eq_zero_iff` says its kernel is exactly $pM$, again in the form $\exists y,\ p \cdot y = x$. Since an additive endomorphism $f$ of $M$ carries $pM$ into $pM$ (`nsmulRange_le_comap`, stated as $pM \le f^{-1}(pM)$), each $f : M \to_+ M$ descends to `ModP.mapHom p f` on $M/pM$, and `ModP.mapEnd p f` regards this descent as a $\mathbb{Z}/p$-linear endomorphism of $M/pM$; both commute with the projection.
--
--   In the second part $p$ is a nonzero natural number and $R$ a commutative domain. `ClGalModule p R` is $M/pM$ for $M$ the class group $\mathrm{Cl}(R)$ written additively, that is $\mathrm{Cl}(R)/p\,\mathrm{Cl}(R)$ as a $\mathbb{Z}/p$-vector space, and `clProj` is the associated surjective projection from the additive copy of $\mathrm{Cl}(R)$. For a ring automorphism $g : R \simeq_{+*} R$, `clEnd p g` is the $\mathbb{Z}/p$-linear endomorphism of $\mathrm{Cl}(R)/p\,\mathrm{Cl}(R)$ obtained by descending the automorphism of the class group induced by $g$ through `ClassGroup.mulEquiv`; `clEnd_clProj` records that it sends the class of $C$ to the class of $g$ applied to $C$. No compatibility of `clEnd` with composition of automorphisms is asserted here.
--
--   **Relation to Mathlib.** The class group and the action of a ring automorphism on it (`ClassGroup`, `ClassGroup.mulEquiv`), as well as the $\mathbb{Z}/p$-module structure on a quotient by a subgroup containing all $p$-multiples, are Mathlib's; the subgroup $pM$, the quotient $M/pM$ with its projection and induced endomorphisms, and their specialisation to class groups are the project's own packaging.
--
--   **Where it is used.** These definitions provide the carrier $\mathrm{Cl}(R)/p\,\mathrm{Cl}(R)$ together with the endomorphisms induced by ring automorphisms of $R$, the $\mathbb{Z}/p$-module with Galois action on which Stickelberger- and Herbrand–Ribet-type statements about class groups of cyclotomic fields are formulated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ClassGroup_ModP.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NumberField nonZeroDivisors

namespace JacobiSumStickelberger

section ModP

variable (p : ℕ) (M : Type*) [AddCommGroup M]

def nsmulRange : AddSubgroup M where
  carrier := Set.range fun x : M => p • x
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, smul_add p x y⟩
  zero_mem' := ⟨0, smul_zero p⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by simp⟩

@[simp] lemma mem_nsmulRange {x : M} : x ∈ nsmulRange p M ↔ ∃ y, p • y = x := Iff.rfl

lemma nsmul_mem_nsmulRange (x : M) : p • x ∈ nsmulRange p M := ⟨x, rfl⟩

abbrev ModP : Type _ := M ⧸ nsmulRange p M

instance instModuleZModModP [NeZero p] : Module (ZMod p) (ModP p M) :=
  QuotientAddGroup.zmodModule (nsmul_mem_nsmulRange p M)

def ModP.proj : M →+ ModP p M := QuotientAddGroup.mk' (nsmulRange p M)

@[simp] lemma ModP.proj_apply (x : M) : ModP.proj p M x = QuotientAddGroup.mk x := rfl

theorem ModP.proj_surjective : Function.Surjective (ModP.proj p M) :=
  QuotientAddGroup.mk'_surjective _

theorem ModP.proj_eq_zero_iff {x : M} : ModP.proj p M x = 0 ↔ ∃ y, p • y = x :=
  (QuotientAddGroup.eq_zero_iff x).trans (mem_nsmulRange p M)

variable {M} in

lemma nsmulRange_le_comap (f : M →+ M) : nsmulRange p M ≤ (nsmulRange p M).comap f := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (map_nsmul f p x).symm⟩

variable {M} in

def ModP.mapHom (f : M →+ M) : ModP p M →+ ModP p M :=
  QuotientAddGroup.map (nsmulRange p M) (nsmulRange p M) f (nsmulRange_le_comap p f)

variable {M} in
@[simp] lemma ModP.mapHom_proj (f : M →+ M) (x : M) :
    ModP.mapHom p f (ModP.proj p M x) = ModP.proj p M (f x) := rfl

variable {M} in

noncomputable def ModP.mapEnd [NeZero p] (f : M →+ M) : Module.End (ZMod p) (ModP p M) :=
  (ModP.mapHom p f).toZModLinearMap p

variable {M} in
@[simp] lemma ModP.mapEnd_proj [NeZero p] (f : M →+ M) (x : M) :
    ModP.mapEnd p f (ModP.proj p M x) = ModP.proj p M (f x) := rfl

end ModP

section ClassGroupCarrier

variable (p : ℕ) [NeZero p]
variable (R : Type*) [CommRing R] [IsDomain R]

abbrev ClGalModule : Type _ := ModP p (Additive (ClassGroup R))

noncomputable def clProj : Additive (ClassGroup R) →+ ClGalModule p R :=
  ModP.proj p (Additive (ClassGroup R))

omit [NeZero p] in
theorem clProj_surjective : Function.Surjective (clProj p R) :=
  ModP.proj_surjective p (Additive (ClassGroup R))

variable {R}

noncomputable def clEnd (g : R ≃+* R) : Module.End (ZMod p) (ClGalModule p R) :=
  ModP.mapEnd p (MonoidHom.toAdditive (ClassGroup.mulEquiv g).toMonoidHom)

@[simp] lemma clEnd_clProj (g : R ≃+* R) (C : ClassGroup R) :
    clEnd p g (clProj p R (Additive.ofMul C)) =
      clProj p R (Additive.ofMul (ClassGroup.mulEquiv g C)) := rfl

end ClassGroupCarrier

end JacobiSumStickelberger


