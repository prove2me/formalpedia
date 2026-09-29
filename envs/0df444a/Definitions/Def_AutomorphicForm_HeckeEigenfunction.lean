-- Prove2me | Definitions.Def_AutomorphicForm_HeckeEigenfunction
-- name    : AutomorphicForm_HeckeEigenfunction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/4e6f4d66-754d-5125-990c-5ad6319f2bf0
-- title:
--   Hecke eigenfunction predicate linking automorphic functions and eigensystems
-- statement:
--   Throughout, $F$ is a number field and $G$ denotes `AdelicGL2 (𝓞 F) F`, i.e. $\mathrm{GL}_2$ of the adele ring of $F$. `RightTranslationGroup F` is $G^{\mathrm{op}}$ viewed through the domain-action synonym `DomMulAct`, so that it acts on functions $G \to \mathbb{C}$ by precomposition; `rightTranslationEmbed F` is the monoid homomorphism attaching to $g \in G$ the corresponding element, and the induced action is $(g \cdot \varphi)(x) = \varphi(xg)$. For a height-one prime $v$ of $\mathcal{O}_F$, `uniformizerIdele F v` is the unit idele whose component at $v$ is the unit given by the chosen uniformiser of $\mathcal{O}_F$ at $v$ and whose remaining components, finite and archimedean, are $1$. For `pins : CarrierPins F` — a bundle carrying a measurable space and measure on $G$, a subset $D \subseteq G$, a subgroup $Z$ of the idele units, an assignment $N \mapsto U(N)$ of subgroups of $G$ to ideals, an assignment $v \mapsto \mathrm{gen}(v)$ of elements of $G$ to height-one primes, and a measurable space and measure on the adeles — and an ideal $N$, `levelRT pins N` is the image of $U(N)$ under `rightTranslationEmbed F`.
--
--   The central definition is `IsHeckeEigenfunctionOf pins ξ φ Φ`, where $\xi : Z \to \mathbb{C}^{\times}$ is a homomorphism, $\varphi : G \to \mathbb{C}$, and $\Phi$ is a Hecke eigensystem (an ideal `level` $\neq 0$ together with functions $a, b$ on the height-one spectrum, valued in $\mathbb{C}$ here). It asserts that $\varphi$ lies in the fixed points of `levelRT pins Φ.level` acting on functions $G \to \mathbb{C}$, and that for every height-one prime $v$ not dividing $\Phi.\mathrm{level}$: first, the image of $U(\Phi.\mathrm{level}) \cdot \{\mathrm{gen}(v)\}$ in the quotient of the right-translation group by `levelRT pins Φ.level` is finite, and the abstract Hecke operator attached to $\mathrm{gen}(v)$ with equal source and target level subgroup — the sum of the translates $g_i \cdot \varphi$ over coset representatives of that image — sends $\varphi$ to $\Phi.a(v)\,\varphi$ inside the fixed-point space; second, `uniformizerIdele F v` belongs to $Z$ and $\Phi.b(v) = \#(\mathcal{O}_F/v) \cdot \xi(\text{uniformizerIdele } F\ v)$. Thus the determinant parameter is pinned down with the residue-cardinality factor explicit, and the eigenvalue and central-character conditions are the only requirements: no cuspidality, growth or integrability condition enters. The membership and finiteness facts needed to form the fixed-point element and the operator appear as existentially quantified proof components of the predicate.
--
--   Two results accompany the definition. `IsHeckeEigenfunctionOf.agreesAwayFromFinite_of_level_eq` states that if one function $\varphi$, with the same `pins` and $\xi$, is a Hecke eigenfunction of two eigensystems $\Phi$ and $\Phi'$ of equal level and $\varphi$ is somewhere nonzero, then $\Phi$ and $\Phi'$ agree away from a finite set of primes, namely the prime divisors of the common level: the $a$-components agree because cancelling a nonzero value of $\varphi$ in the two eigenvalue equations, the $b$-components because both are computed by the same formula in $\xi$. `isHeckeEigenfunctionOf_zero_inhabitant` exhibits the predicate as satisfiable, by the zero function over $\mathbb{Q}$ with a degenerate bundle (trivial central subgroup, trivial level subgroups, generators equal to $1$), $\xi$ trivial, level the unit ideal, $a \equiv 0$ and $b(v) = \#(\mathbb{Z}/v)$.
--
--   **Relation to Mathlib.** The right-translation group is built from Mathlib's `DomMulAct` and `MulOpposite`, and invariance is expressed with Mathlib's `MulAction.fixedPoints`. `CarrierPins`, `HeckeEigensystem` and the double-coset operator [`AbstractHeckeOperator.HeckeOperator`](../def/AbstractHeckeOperator.html#L136) are the project's own notions; Mathlib has no adelic Hecke eigensystem or Hecke eigenfunction predicate.
--
--   **Where it is used.** The predicate is the interface between analytic automorphic objects on $\mathrm{GL}_2$ over a number field and the purely arithmetic data of a Hecke eigensystem (level, trace and determinant parameters at the good primes), which is what the base-change, descent and multiplicity-one statements about eigensystems are formulated in terms of.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_HeckeEigenfunction.lean

import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AbstractHeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MulAction NumberField.AdelicLevel
open scoped Pointwise

noncomputable section

namespace AutomorphicForm

section Defs

variable (F : Type) [Field F] [NumberField F]

abbrev RightTranslationGroup : Type _ :=
  DomMulAct ((AdelicGL2 (𝓞 F) F)ᵐᵒᵖ)

def rightTranslationEmbed : AdelicGL2 (𝓞 F) F →* RightTranslationGroup F where
  toFun g := DomMulAct.mk (MulOpposite.op g)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem rightTranslationEmbed_smul_apply (g x : AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    (rightTranslationEmbed F g • φ) x = φ (x * g) := rfl

def uniformizerIdele (v : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (uniformizerUnit F v))

end Defs

variable {F : Type} [Field F] [NumberField F]

def levelRT (pins : CarrierPins F) (N : Ideal (𝓞 F)) :
    Subgroup (RightTranslationGroup F) :=
  (pins.U N).map (rightTranslationEmbed F)

def IsHeckeEigenfunctionOf (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (Φ : HeckeEigensystem F ℂ) : Prop :=
  ∃ hmem : φ ∈ fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ),
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Φ.level →
      (∃ hfin : (QuotientGroup.mk ''
            ((levelRT pins Φ.level : Set (RightTranslationGroup F))
              * {rightTranslationEmbed F (pins.gen v)}) :
            Set (RightTranslationGroup F ⧸ levelRT pins Φ.level)).Finite,
        AbstractHeckeOperator.HeckeOperator (R := ℂ)
            (rightTranslationEmbed F (pins.gen v))
            (levelRT pins Φ.level) (levelRT pins Φ.level) hfin ⟨φ, hmem⟩
          = Φ.a v •
            (⟨φ, hmem⟩ : fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ)))
      ∧ ∃ hz : uniformizerIdele F v ∈ pins.Z,
          Φ.b v = (Nat.card ((𝓞 F) ⧸ v.asIdeal) : ℂ)
            * ((ξ ⟨uniformizerIdele F v, hz⟩ : ℂˣ) : ℂ)

namespace IsHeckeEigenfunctionOf

theorem agreesAwayFromFinite_of_level_eq {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} {Φ Φ' : HeckeEigensystem F ℂ}
    (h : IsHeckeEigenfunctionOf pins ξ φ Φ) (h' : IsHeckeEigenfunctionOf pins ξ φ Φ')
    (hlev : Φ.level = Φ'.level) (hnz : ∃ x, φ x ≠ 0) :
    HeckeEigensystem.AgreesAwayFromFinite Φ Φ' := by
  obtain ⟨x₀, hx₀⟩ := hnz
  obtain ⟨N', hN', a', b'⟩ := Φ'
  dsimp only at hlev
  subst hlev
  obtain ⟨hmem, hcl⟩ := h
  obtain ⟨hmem', hcl'⟩ := h'
  have hfactors : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Φ.level}.Finite :=
    Ideal.finite_factors (by simpa using Φ.level_ne_bot)
  refine ⟨hfactors.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
  obtain ⟨⟨hfin, heig⟩, hz, hb⟩ := hcl v hv
  obtain ⟨⟨hfin', heig'⟩, hz', hb'⟩ := hcl' v hv
  constructor
  · have hEq :
        Φ.a v • (⟨φ, hmem⟩ :
            fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ))
          = a' v • (⟨φ, hmem⟩ :
            fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ)) :=
      heig.symm.trans heig'
    have hval := congrArg Subtype.val hEq
    rw [FixedPoints.coe_smul, FixedPoints.coe_smul] at hval
    have hpt := congrFun hval x₀
    simp only [Pi.smul_apply, smul_eq_mul] at hpt
    exact mul_right_cancel₀ hx₀ hpt
  · exact hb.trans hb'.symm

end IsHeckeEigenfunctionOf

theorem isHeckeEigenfunctionOf_zero_inhabitant :
    ∃ (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (Φ : HeckeEigensystem ℚ ℂ), IsHeckeEigenfunctionOf pins ξ φ Φ := by
  refine ⟨⟨⊤, 0, ∅, ⊤, fun _ => ⊥, fun _ => 1, ⊤, 0⟩, 1, (fun _ => (0 : ℂ)),
    ⟨⊤, by simp, fun _ => 0,
      fun v => (Nat.card ((𝓞 ℚ) ⧸ v.asIdeal) : ℂ) * 1⟩, ?_⟩
  have hmem0 : (fun _ => (0 : ℂ)) ∈
      fixedPoints (levelRT (F := ℚ) ⟨⊤, 0, ∅, ⊤, fun _ => ⊥, fun _ => 1, ⊤, 0⟩ ⊤)
        (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) := fun _ => smul_zero _
  refine ⟨hmem0, fun v _ => ⟨⟨?_, ?_⟩, Subgroup.mem_top _, rfl⟩⟩
  · refine Set.Finite.image _ (Set.Finite.subset (Set.finite_singleton 1) ?_)
    rintro x ⟨u, hu, y, hy, rfl⟩
    rcases hy with rfl
    have hu1 : u = 1 := by
      rcases hu with ⟨w, hw, rfl⟩
      rcases hw with rfl
      exact map_one _
    simp [hu1]
  · have hzero : (⟨(fun _ => (0 : ℂ)), hmem0⟩ :
        fixedPoints (levelRT (F := ℚ) ⟨⊤, 0, ∅, ⊤, fun _ => ⊥, fun _ => 1, ⊤, 0⟩ ⊤)
          (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) = 0 := Subtype.ext rfl
    rw [hzero, map_zero]
    exact Subtype.ext (by simp)

end AutomorphicForm

end


