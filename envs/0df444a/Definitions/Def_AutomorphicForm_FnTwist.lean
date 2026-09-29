-- Prove2me | Definitions.Def_AutomorphicForm_FnTwist
-- name    : AutomorphicForm_FnTwist
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/5f6b16ad-8e23-504f-ba14-ad9841188e0c
-- title:
--   Twisting adelic GL(2) functions by determinant characters
-- statement:
--   Throughout, $F$ is a number field with ring of integers $\mathcal{O}_F$, and the ambient group is `AdelicGL2 (𝓞 F) F`, i.e. $\mathrm{GL}_2$ of the adele ring of $F$. For a monoid homomorphism $\eta : \mathbb{A}_F^\times \to \mathbb{C}^\times$ and a function $\varphi$ on this group, `fnTwist F η φ` is the pointwise product $g \mapsto \mathrm{chiDet}\,\eta\,(g)\cdot\varphi(g)$, where `chiDet (𝓞 F) F η` is the complex-valued function on $\mathrm{GL}_2(\mathbb{A}_F)$ attached to $\eta$ through the determinant. The elementary lemmas record that the twist of the zero function is zero, that twisting by the trivial character is the identity operation, and that twists compose: twisting by $\eta_2$ and then by $\eta_1$ equals twisting by $\eta_1\eta_2$. Two transformation rules for `chiDet` are proved: for $z \in \mathbb{A}_F^\times$ one has $\det(\mathrm{centralScalar}\,z) = z^2$ (the central element being the scalar matrix of size $2$), whence $\mathrm{chiDet}\,\eta\,(\mathrm{centralScalar}\,z\cdot g) = \eta(z)^2\,\mathrm{chiDet}\,\eta\,(g)$; and if $\eta$ satisfies the predicate `IsIdeleClassChar` (a condition indexed by elements of $F^\times$, applied here to $\det\gamma$ to give the value $1$), then `chiDet` is invariant under left multiplication by the image of any $\gamma \in \mathrm{GL}_2(F)$ under `globalPoints`. Correspondingly, `twistedCentralChar F Z ξ η` is the character $z \mapsto \xi(z)\,\eta(z)^2$ of a subgroup $Z \le \mathbb{A}_F^\times$, and `isLsXiFunction_fnTwist` states that if $\varphi$ satisfies `IsLsXiFunction` for $(Z,\xi)$ — left invariance under global points together with the central transformation rule by $\xi$ — then `fnTwist F η φ` satisfies it for $(Z, \xi\cdot(\eta|_Z)^2)$. Finally, in any topological group, if two functions are each fixed by an open subgroup of a subgroup $H$ under right translation (`IsSmoothVector` for `RightTranslationFn`), so is their pointwise product; applied to the subgroup of elements with trivial archimedean component, this gives that `fnTwist F η φ` is `IsKfSmooth` whenever both `chiDet (𝓞 F) F η` and $\varphi$ are. The trivial character satisfies `IsIdeleClassChar`, and `twistedCentralChar` by it returns $\xi$ unchanged.
--
--   **Relation to Mathlib.** Mathlib has no vocabulary for adelic automorphic forms; the notions twisted here (`chiDet`, `IsLsXiFunction`, `IsIdeleClassChar`, `IsKfSmooth`) are the project's own, and smoothness is formulated via the project's `IsSmoothVector`, meaning that the stabiliser of the vector is open. The general product lemma for smooth vectors is stated for arbitrary Mathlib topological groups acting by right translation.
--
--   **Where it is used.** These lemmas provide the bookkeeping for changing an automorphic function on $\mathrm{GL}_2(\mathbb{A}_F)$ by a character of the ideles composed with the determinant: invariance under the global points is unaffected, the central character is multiplied by the square of the restricted character, and finite-level smoothness is preserved. Such twists are used when normalising central characters on the automorphic side of the modularity arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_FnTwist.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField MeasureTheory Matrix
open AutomorphicForm FLT.SmoothVectors

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def fnTwist (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => chiDet (𝓞 F) F η g * φ g

@[simp] theorem fnTwist_apply (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    fnTwist F η φ g = chiDet (𝓞 F) F η g * φ g := rfl

@[simp] theorem fnTwist_zero (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) :
    fnTwist F η (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  ext g; simp [fnTwist]

theorem fnTwist_one (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    fnTwist F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) φ = φ := by
  ext g; simp [fnTwist, chiDet]

theorem fnTwist_fnTwist (η₁ η₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    fnTwist F η₁ (fnTwist F η₂ φ) = fnTwist F (η₁ * η₂) φ := by
  ext g; simp only [fnTwist, chiDet, MonoidHom.mul_apply, Units.val_mul]; ring

theorem det_centralScalar (z : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z) = z ^ 2 := by
  rw [show centralScalar (𝓞 F) F = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem chiDet_centralScalar_mul (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    chiDet (𝓞 F) F η (centralScalar (𝓞 F) F z * g) =
      ((η z : ℂˣ) : ℂ) ^ 2 * chiDet (𝓞 F) F η g := by
  simp only [chiDet, map_mul, det_centralScalar F, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]

def twistedCentralChar (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : Z →* ℂˣ :=
  ξ * (η.comp Z.subtype) ^ 2

theorem chiDet_globalPoints_mul (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hηF : IsIdeleClassChar (𝓞 F) F η) (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    chiDet (𝓞 F) F η (globalPoints (𝓞 F) F γ * g) = chiDet (𝓞 F) F η g := by
  unfold chiDet
  congr 1
  rw [map_mul, globalPoints, Matrix.GeneralLinearGroup.map_det, map_mul,
    hηF (Matrix.GeneralLinearGroup.det γ), one_mul]

theorem isLsXiFunction_fnTwist {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hηF : IsIdeleClassChar (𝓞 F) F η)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ) :
    IsLsXiFunction (𝓞 F) F Z (twistedCentralChar F Z ξ η) (fnTwist F η φ) := by
  refine ⟨fun γ g => ?_, fun z g => ?_⟩
  · simp only [fnTwist_apply, chiDet_globalPoints_mul F η hηF, hφ.left_invariant γ g]
  · simp only [fnTwist_apply, chiDet_centralScalar_mul F, hφ.central_transform z g,
      twistedCentralChar, MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]
    ring

theorem isSmoothVector_rightTranslationFn_mul {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {M : Type*} [Mul M] {H : Subgroup G} {φ ψ : G → M}
    (hφ : IsSmoothVector H (RightTranslationFn.mk (G := G) φ))
    (hψ : IsSmoothVector H (RightTranslationFn.mk (G := G) ψ)) :
    IsSmoothVector H (RightTranslationFn.mk (G := G) (fun g => φ g * ψ g)) := by
  rw [isSmoothVector_iff_isOpen_stabilizer]
  refine Subgroup.isOpen_mono ?_ (isOpen_coe_inf_stabilizer hφ hψ)
  intro k hk
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    Subgroup.smul_def, Subgroup.smul_def] at hk
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  refine RightTranslationFn.ext fun g => ?_
  have hφk : φ (g * ↑k) = φ g := by
    have := congrFun (congrArg RightTranslationFn.toFun hk.1) g
    simp only [RightTranslationFn.toFun_smul] at this
    exact this
  have hψk : ψ (g * ↑k) = ψ g := by
    have := congrFun (congrArg RightTranslationFn.toFun hk.2) g
    simp only [RightTranslationFn.toFun_smul] at this
    exact this
  simp only [RightTranslationFn.toFun_smul]
  exact congrArg₂ (· * ·) hφk hψk

theorem isKfSmooth_fnTwist (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hηKf : IsKfSmooth F (chiDet (𝓞 F) F η)) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsKfSmooth F φ) : IsKfSmooth F (fnTwist F η φ) :=
  isSmoothVector_rightTranslationFn_mul hηKf hφ

theorem twistedCentralChar_one (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ) :
    twistedCentralChar F Z ξ 1 = ξ := by
  ext z; simp [twistedCentralChar]

theorem isIdeleClassChar_one : IsIdeleClassChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) :=
  fun _ => rfl

end AutomorphicForm

end


