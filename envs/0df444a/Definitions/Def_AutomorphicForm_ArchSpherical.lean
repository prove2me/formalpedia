-- Prove2me | Definitions.Def_AutomorphicForm_ArchSpherical
-- name    : AutomorphicForm_ArchSpherical
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/2b9a9089-ac3f-5a2c-a258-d9b2a4cb81e0
-- title:
--   Spherical archimedean test factors and level-spherical test functions
-- statement:
--   Throughout, $F$ is a number field with ring of integers $\mathcal O_F$, and `ArchTypeFamily F` records, for each infinite place $w$, a finite list of representations $\rho$ of the subgroup `rowIsometrySubgroup₀ w.Completion` of $\mathrm{GL}_2(F_w)$ on spaces $\mathbb C^n$ (an `ArchRepAt F w`).
--
--   The first definition, `IsArchSphericalOfType F tys fa`, is a three-clause predicate on a function $fa$ on $\mathrm{GL}_2$ of the infinite adeles: the predicate `IsArchTestFactor F fa`; the bi-finiteness condition `IsArchFactorBiFinite F tys fa`, which asserts that $x \mapsto fa(x^{-1})$ lies in $\bigsqcap_w \bigsqcup_i$ of the right-equivariant type submodules `archFactorTypeSubmoduleAt` attached to $tys.\mathrm{rep}\,w\,i$, and that $fa$ itself lies in the corresponding infimum of suprema of the dual type submodules; and conjugation invariance, $fa(k x k^{-1}) = fa(x)$ for every infinite place $w$, every $k$ in `rowIsometrySubgroup₀ w.Completion` embedded at $w$ by `archRowIsometryInclAt₀`, and every $x$.
--
--   The second definition, `IsLevelSphericalOfType F tys U f`, applies to a subgroup $U$ of the adelic group `AdelicGL2 (𝓞 F) F` and a function $f$ on it: it asserts the existence of $fa$ satisfying the same three clauses, written out flatly, such that for all $g$, $f(g)$ equals $fa$ of the archimedean component `glArch` of $g$ times the value at the finite component `glFin` of $g$ of the $\mathbb C$-valued indicator function of the image of $U$ under `glFin`. Thus $f$ is the pure product of an archimedean spherical factor of type $tys$ with the indicator of the finite projection of the level subgroup.
--
--   The remaining declarations restate both predicates as their defining conjunctions, repackage the three archimedean clauses in `IsLevelSphericalOfType` as `IsArchSphericalOfType`, and record that the zero function satisfies both predicates, for every type family and every level subgroup.
--
--   **Relation to Mathlib.** Mathlib has no notion of adelic test functions, archimedean $K$-types or level-spherical functions on $\mathrm{GL}_2$ of the adeles; these predicates are the project's own, built on its adelic $\mathrm{GL}_2$, Haar measure and type-submodule machinery.
--
--   **Where it is used.** These test functions supply the convolution operators used to cut out isotypic pieces of spaces of cusp forms on $\mathrm{GL}_2$ over a number field: the conjugation-invariance clause is what makes the associated right-convolution operators act on a fixed level-and-type cut, in the admissibility arguments for cuspidal constituents that precede the comparison of Hecke eigensystems with Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ArchSpherical.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def IsArchSphericalOfType (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) : Prop :=
  IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
    ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x

theorem isArchSphericalOfType_iff (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    IsArchSphericalOfType F tys fa ↔
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
          fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x := Iff.rfl

theorem isArchSphericalOfType_zero (tys : ArchTypeFamily F) : IsArchSphericalOfType F tys (fun _ => 0) :=
  ⟨isArchTestFactor_zero F, isArchFactorBiFinite_zero F tys, fun _ _ _ => rfl⟩

def IsLevelSphericalOfType (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
    IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
    (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
    ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
      Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)))
        (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g)

theorem isLevelSphericalOfType_iff (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) :
    IsLevelSphericalOfType F tys U f ↔
      ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
        IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
          fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
        ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
          Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g) := Iff.rfl

theorem isLevelSphericalOfType_iff' (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) :
    IsLevelSphericalOfType F tys U f ↔
      ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchSphericalOfType F tys fa ∧
        ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
          Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g) :=
  ⟨fun ⟨fa, h1, h2, h3, h4⟩ => ⟨fa, ⟨h1, h2, h3⟩, h4⟩, fun ⟨fa, ⟨h1, h2, h3⟩, h4⟩ => ⟨fa, h1, h2, h3, h4⟩⟩

theorem isLevelSphericalOfType_zero (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F)) :
    IsLevelSphericalOfType F tys U (fun _ => 0) :=
  ⟨fun _ => 0, isArchTestFactor_zero F, isArchFactorBiFinite_zero F tys, fun _ _ _ => rfl,
    fun _ => (zero_mul _).symm⟩

end AutomorphicForm

end


