-- Prove2me | Definitions.Def_ExtCitation_CyclotomicUnits
-- name    : ExtCitation_CyclotomicUnits
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/75de0816-51f2-50ea-849b-9699c2345752
-- title:
--   Galois action on cyclotomic units mod p-th powers
-- statement:
--   Fix a prime $p$. For a commutative ring $R$, the module works with $\mathrm{ModP}\,p\,(\mathrm{Additive}\,R^\times)$, that is the quotient of the additive group $\mathrm{Additive}\,R^\times$ by the subgroup of $p$-multiples — multiplicatively, $R^\times/(R^\times)^p$ — equipped with its $\mathbb{Z}/p$-module structure. `unitsEnd p R g` is the $\mathbb{Z}/p$-linear endomorphism of this quotient induced by the automorphism of $R^\times$ attached to a ring automorphism $g$ of $R$; the accompanying simp lemma records its value on the class of a unit $u$ as the class of $g(u)$, and `unitsEndHom p R` assembles $g\mapsto{}$`unitsEnd p R g` into a monoid homomorphism $\mathrm{Aut}(R)\to\mathrm{End}_{\mathbb{Z}/p}\bigl(R^\times/(R^\times)^p\bigr)$. An instance records that `CyclotomicField p ℚ` is a $p$-cyclotomic extension of $\mathbb{Q}$.
--
--   For $K=$ `CyclotomicField p ℚ`, `unitsGalAction p` is the monoid homomorphism $(\mathbb{Z}/p)^\times\to\mathrm{End}_{\mathbb{Z}/p}\bigl(\mathcal{O}_K^\times/(\mathcal{O}_K^\times)^p\bigr)$ obtained by composing `clRingAction p K` — which sends $d$ to the automorphism of $\mathcal{O}_K$ obtained by inverting the cyclotomic character isomorphism $(K\simeq_{\mathbb{Q}}K)\simeq(\mathbb{Z}/p)^\times$ of `cycloGalEquiv` and restricting the resulting field automorphism to the ring of integers — with `unitsEndHom`. For $i\in\mathbb{N}$, `unitsOmegaEigenspace p i` is the $\mathbb{Z}/p$-submodule of $\mathcal{O}_K^\times/(\mathcal{O}_K^\times)^p$ cut out by the predicate `IsOmegaEigenvector`, namely $\{a : \rho(d)\,a=(d\bmod p)^i\cdot a\text{ for all }d\in(\mathbb{Z}/p)^\times\}$ with $\rho=$ `unitsGalAction p`, the $\omega^i$-eigenspace. Finally, for an arbitrary $\mathbb{Z}/p$-module $M$ and an arbitrary action $\rho:(\mathbb{Z}/p)^\times\to\mathrm{End}_{\mathbb{Z}/p}(M)$, `omegaIdempotent p ρ i` is the endomorphism $\bigl(\#(\mathbb{Z}/p)^\times\bigr)^{-1}\sum_{d\in(\mathbb{Z}/p)^\times}\bigl((d)^i\bigr)^{-1}\,\rho(d)$ of $M$, the scalars being taken in $\mathbb{Z}/p$; it is defined as this element, with no idempotence or projection property asserted at this point.
--
--   **Relation to Mathlib.** The quotient $R^\times/(R^\times)^p$ as a $\mathbb{Z}/p$-module with its induced functoriality, the $\omega^i$-eigenspace and the averaging endomorphism are the project's own constructions, built on Mathlib's cyclotomic-character isomorphism `IsCyclotomicExtension.autEquivPow` and on `galRestrict` for restricting field automorphisms to rings of integers; the unit-group version here parallels the project's class-group version `clGalAction`.
--
--   **Where it is used.** These definitions provide the $(\mathbb{Z}/p)^\times$-module framework — units modulo $p$-th powers, $\omega^i$-eigenspaces and the averaging endomorphisms — in which Stickelberger- and Jacobi-sum-type statements about $\mathbb{Q}(\zeta_p)$ are formulated in the development, alongside the corresponding action on the $p$-torsion of the class group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ExtCitation_CyclotomicUnits.lean

import Definitions.Def_ClassGroup_GaloisAction
import Definitions.Def_Stickelberger_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ExtCitation.Cyclotomic

open NumberField JacobiSumStickelberger Stickelberger

variable (p : ℕ) [Fact p.Prime]

section UnitsGalAction

variable (R : Type*) [CommRing R]

noncomputable def unitsEnd (g : R ≃+* R) :
    Module.End (ZMod p) (ModP p (Additive Rˣ)) :=
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ModP.mapEnd p (MulEquiv.toAdditive (Units.mapEquiv g.toMulEquiv)).toAddMonoidHom

variable {R} in
@[simp] lemma unitsEnd_proj (g : R ≃+* R) (u : Rˣ) :
    unitsEnd p R g (ModP.proj p (Additive Rˣ) (Additive.ofMul u)) =
      ModP.proj p (Additive Rˣ) (Additive.ofMul (Units.mapEquiv g.toMulEquiv u)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rfl

noncomputable def unitsEndHom : (R ≃+* R) →* Module.End (ZMod p) (ModP p (Additive Rˣ)) where
  toFun := unitsEnd p R
  map_one' := by
    ext a
    obtain ⟨u, rfl⟩ := ModP.proj_surjective p (Additive Rˣ) a
    exact unitsEnd_proj p (RingEquiv.refl R) u.toMul
  map_mul' g h := by
    ext a
    obtain ⟨u, rfl⟩ := ModP.proj_surjective p (Additive Rˣ) a
    simp only [Module.End.mul_apply]
    rfl

end UnitsGalAction

set_option backward.isDefEq.respectTransparency false in

noncomputable instance instIsCycExt :
    IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
  inferInstance

noncomputable def unitsGalAction :
    (ZMod p)ˣ →* Module.End (ZMod p)
      (ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)) :=
  (unitsEndHom p (𝓞 (CyclotomicField p ℚ))).comp (clRingAction p (CyclotomicField p ℚ))

def unitsOmegaEigenspace (i : ℕ) :
    Submodule (ZMod p) (ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)) where
  carrier := {a | IsOmegaEigenvector (unitsGalAction p) i a}
  add_mem' {a b} ha hb d := by
    simp only [Set.mem_setOf_eq, IsOmegaEigenvector] at *
    rw [map_add, ha d, hb d, smul_add]
  zero_mem' d := by simp
  smul_mem' c a ha d := by
    simp only [Set.mem_setOf_eq, IsOmegaEigenvector] at *
    rw [map_smul, ha d, smul_comm]

noncomputable def omegaIdempotent {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (ρ : (ZMod p)ˣ →* Module.End (ZMod p) M) (i : ℕ) : Module.End (ZMod p) M :=
  (Nat.card (ZMod p)ˣ : ZMod p)⁻¹ • ∑ d : (ZMod p)ˣ, (((d : ZMod p) ^ i)⁻¹) • ρ d

end ExtCitation.Cyclotomic


