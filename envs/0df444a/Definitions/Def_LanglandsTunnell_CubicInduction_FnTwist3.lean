-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_FnTwist3
-- name    : LanglandsTunnell_CubicInduction_FnTwist3
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/fd5836a5-fe7f-545d-a849-c54fa7300bde
-- title:
--   Determinant characters and cubic twists on adelic GL3​
-- statement:
--   The standing context is a Dedekind domain $R$ with fraction field $K$, with $\mathbb{A} =$ `AdeleRing R K` the associated adele ring and `AdelicGL n R K` the group $\mathrm{GL}_n(\mathbb{A})$. Given a homomorphism $\eta : \mathbb{A}^\times \to \mathbb{C}^\times$, `chiDetGL n R K η` is the complex-valued function $g \mapsto \eta(\det g)$ on $\mathrm{GL}_n(\mathbb{A})$. The accompanying lemmas record its defining value, that it is constantly $1$ for $\eta = 1$, that it is multiplicative both in $\eta$ and in $g$, that it is nowhere zero, and that it has modulus $1$ everywhere when $\eta$ satisfies [`AutomorphicForm.IsUnitaryChar R K`](../def/AutomorphicForm_AdelicLsXi.html#L24), i.e. $\lVert\eta(x)\rVert = 1$ for every idele $x$. Two equivariance computations are recorded: $\det$ of the central scalar `centralScalarGL n R K z` (the matrix $z \cdot 1$) is $z^n$, whence $\chi_\eta(z \cdot 1 \cdot g) = \eta(z)^n \chi_\eta(g)$; and $\det$ of `globalPointsGL n R K γ`, the image of $\gamma \in \mathrm{GL}_n(K)$ under the entrywise map $K \to \mathbb{A}$, is the image of $\det\gamma$, whence $\chi_\eta$ is invariant under left translation by $\mathrm{GL}_n(K)$ as soon as $\eta$ is trivial on the image of $K^\times$ ([`AutomorphicForm.IsIdeleClassChar R K`](../def/AutomorphicForm_AdelicLsXi.html#L21)).
--
--   In rank $3$ the determinants of the upper unitriangular matrix `upperUnipotent3 x y z` and of the two one-parameter families `radicalP21 v`, `radicalP12 v` are shown to be $1$ over any commutative ring, so $\chi_\eta$ is invariant under left translation by these elements. Finally, `fnTwist3 R K η φ` is the pointwise product $g \mapsto \eta(\det g)\,\varphi(g)$ of $\chi_\eta$ with a function $\varphi$ on $\mathrm{GL}_3(\mathbb{A})$; it kills the zero function, is the identity for $\eta = 1$, and composing twists by $\eta_2$ then $\eta_1$ gives the twist by $\eta_1\eta_2$. The character `twistedCentralChar3 R K ω η` is the pointwise product $\omega\,\eta^3$; it equals $\omega$ when $\eta = 1$, is an idele-class character when $\omega$ and $\eta$ are, and, whenever $\varphi(z\cdot 1 \cdot g) = \omega(z)\varphi(g)$ for a given idele $z$ and point $g$, the twist of $\varphi$ by $\eta$ satisfies the same relation at $z, g$ with $\omega$ replaced by $\omega\eta^3$.
--
--   **Relation to Mathlib.** Mathlib supplies $\mathrm{GL}_n$ over the adele ring together with `Matrix.GeneralLinearGroup.det`, `Matrix.GeneralLinearGroup.map` and `Matrix.GeneralLinearGroup.scalar`; the determinant character, the twist operation and the twisted central character, as well as the predicates on idele characters they use, are the project's own.
--
--   **Where it is used.** These are bookkeeping operations for the cubic (Langlands–Tunnell) induction step, where automorphic forms on $\mathrm{GL}_3$ of the adeles are manipulated: twisting by a determinant character changes the central character by the cube of that character while preserving left $\mathrm{GL}_3(K)$-invariance and invariance under the unipotent radicals used to form constant terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_FnTwist3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section DetCharacter

variable (n : ℕ) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def chiDetGL (η : (AdeleRing R K)ˣ →* ℂˣ) : AdelicGL n R K → ℂ :=
  fun g => ((η (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)

theorem chiDetGL_apply (η : (AdeleRing R K)ˣ →* ℂˣ) (g : AdelicGL n R K) :
    chiDetGL n R K η g = ((η (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := rfl

theorem chiDetGL_one (g : AdelicGL n R K) : chiDetGL n R K (1 : (AdeleRing R K)ˣ →* ℂˣ) g = 1 := by
  simp [chiDetGL]

theorem chiDetGL_mul_apply (η₁ η₂ : (AdeleRing R K)ˣ →* ℂˣ) (g : AdelicGL n R K) :
    chiDetGL n R K (η₁ * η₂) g = chiDetGL n R K η₁ g * chiDetGL n R K η₂ g := by
  simp [chiDetGL]

theorem chiDetGL_mul (η : (AdeleRing R K)ˣ →* ℂˣ) (g h : AdelicGL n R K) :
    chiDetGL n R K η (g * h) = chiDetGL n R K η g * chiDetGL n R K η h := by
  simp [chiDetGL, map_mul]

theorem chiDetGL_ne_zero (η : (AdeleRing R K)ˣ →* ℂˣ) (g : AdelicGL n R K) : chiDetGL n R K η g ≠ 0 :=
  (η (Matrix.GeneralLinearGroup.det g)).ne_zero

theorem norm_chiDetGL_eq_one {η : (AdeleRing R K)ˣ →* ℂˣ} (hη : AutomorphicForm.IsUnitaryChar R K η)
    (g : AdelicGL n R K) : ‖chiDetGL n R K η g‖ = 1 :=
  hη _

theorem det_centralScalarGL (z : (AdeleRing R K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalarGL n R K z) = z ^ n := by
  rw [show centralScalarGL n R K = Matrix.GeneralLinearGroup.scalar (Fin n) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem chiDetGL_centralScalarGL_mul (η : (AdeleRing R K)ˣ →* ℂˣ) (z : (AdeleRing R K)ˣ)
    (g : AdelicGL n R K) :
    chiDetGL n R K η (centralScalarGL n R K z * g) = ((η z : ℂˣ) : ℂ) ^ n * chiDetGL n R K η g := by
  simp only [chiDetGL, map_mul, det_centralScalarGL, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]

theorem det_globalPointsGL (γ : Matrix.GeneralLinearGroup (Fin n) K) :
    Matrix.GeneralLinearGroup.det (globalPointsGL n R K γ) =
      Units.map (algebraMap K (AdeleRing R K)) (Matrix.GeneralLinearGroup.det γ) :=
  Matrix.GeneralLinearGroup.map_det _ _

theorem chiDetGL_globalPointsGL_mul {η : (AdeleRing R K)ˣ →* ℂˣ}
    (hη : AutomorphicForm.IsIdeleClassChar R K η) (γ : Matrix.GeneralLinearGroup (Fin n) K)
    (g : AdelicGL n R K) : chiDetGL n R K η (globalPointsGL n R K γ * g) = chiDetGL n R K η g := by
  unfold chiDetGL
  congr 1
  rw [map_mul, det_globalPointsGL, map_mul, hη (Matrix.GeneralLinearGroup.det γ), one_mul]

end DetCharacter

section DetUnipotent

variable {A : Type*} [CommRing A]

theorem det_upperUnipotent3 (x y z : A) : Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z) = 1 := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_three]

theorem det_radicalP21 (v : Fin 2 → A) : Matrix.GeneralLinearGroup.det (radicalP21 v) = 1 :=
  det_upperUnipotent3 _ _ _

theorem det_radicalP12 (v : Fin 2 → A) : Matrix.GeneralLinearGroup.det (radicalP12 v) = 1 :=
  det_upperUnipotent3 _ _ _

end DetUnipotent

section DetCharacterThree

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem chiDetGL_three_centralScalarGL_mul (η : (AdeleRing R K)ˣ →* ℂˣ) (z : (AdeleRing R K)ˣ)
    (g : AdelicGL 3 R K) :
    chiDetGL 3 R K η (centralScalarGL 3 R K z * g) = ((η z : ℂˣ) : ℂ) ^ 3 * chiDetGL 3 R K η g :=
  chiDetGL_centralScalarGL_mul 3 R K η z g

theorem chiDetGL_upperUnipotent3_mul (η : (AdeleRing R K)ˣ →* ℂˣ) (x y z : AdeleRing R K)
    (g : AdelicGL 3 R K) : chiDetGL 3 R K η (upperUnipotent3 x y z * g) = chiDetGL 3 R K η g := by
  simp [chiDetGL, map_mul, det_upperUnipotent3]

theorem chiDetGL_radicalP21_mul (η : (AdeleRing R K)ˣ →* ℂˣ) (v : Fin 2 → AdeleRing R K)
    (g : AdelicGL 3 R K) : chiDetGL 3 R K η (radicalP21 v * g) = chiDetGL 3 R K η g := by
  simp [chiDetGL, map_mul, det_radicalP21]

theorem chiDetGL_radicalP12_mul (η : (AdeleRing R K)ˣ →* ℂˣ) (v : Fin 2 → AdeleRing R K)
    (g : AdelicGL 3 R K) : chiDetGL 3 R K η (radicalP12 v * g) = chiDetGL 3 R K η g := by
  simp [chiDetGL, map_mul, det_radicalP12]

end DetCharacterThree

section Twist

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def fnTwist3 (η : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL 3 R K → ℂ) : AdelicGL 3 R K → ℂ :=
  fun g => chiDetGL 3 R K η g * φ g

@[simp] theorem fnTwist3_apply (η : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL 3 R K → ℂ) (g : AdelicGL 3 R K) :
    fnTwist3 R K η φ g = chiDetGL 3 R K η g * φ g := rfl

theorem fnTwist3_zero (η : (AdeleRing R K)ˣ →* ℂˣ) : fnTwist3 R K η (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  ext g; simp [fnTwist3]

theorem fnTwist3_one (φ : AdelicGL 3 R K → ℂ) : fnTwist3 R K (1 : (AdeleRing R K)ˣ →* ℂˣ) φ = φ := by
  ext g; simp [fnTwist3, chiDetGL]

theorem fnTwist3_fnTwist3 (η₁ η₂ : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL 3 R K → ℂ) :
    fnTwist3 R K η₁ (fnTwist3 R K η₂ φ) = fnTwist3 R K (η₁ * η₂) φ := by
  ext g; simp only [fnTwist3, chiDetGL, MonoidHom.mul_apply, Units.val_mul]; ring

def twistedCentralChar3 (ω η : (AdeleRing R K)ˣ →* ℂˣ) : (AdeleRing R K)ˣ →* ℂˣ :=
  ω * η ^ 3

theorem twistedCentralChar3_apply (ω η : (AdeleRing R K)ˣ →* ℂˣ) (z : (AdeleRing R K)ˣ) :
    (twistedCentralChar3 R K ω η z : ℂ) = (ω z : ℂ) * (η z : ℂ) ^ 3 := by
  simp only [twistedCentralChar3, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]

theorem twistedCentralChar3_one (ω : (AdeleRing R K)ˣ →* ℂˣ) : twistedCentralChar3 R K ω 1 = ω := by
  ext z; simp [twistedCentralChar3]

theorem isIdeleClassChar_twistedCentralChar3 {ω η : (AdeleRing R K)ˣ →* ℂˣ}
    (hω : AutomorphicForm.IsIdeleClassChar R K ω) (hη : AutomorphicForm.IsIdeleClassChar R K η) :
    AutomorphicForm.IsIdeleClassChar R K (twistedCentralChar3 R K ω η) := fun u => by
  simp only [twistedCentralChar3, MonoidHom.mul_apply, MonoidHom.pow_apply, hω u, hη u, one_pow, mul_one]

theorem fnTwist3_centralScalarGL_mul (ω η : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL 3 R K → ℂ)
    (z : (AdeleRing R K)ˣ) (g : AdelicGL 3 R K) (hφ : φ (centralScalarGL 3 R K z * g) = (ω z : ℂ) * φ g) :
    fnTwist3 R K η φ (centralScalarGL 3 R K z * g) = (twistedCentralChar3 R K ω η z : ℂ) * fnTwist3 R K η φ g := by
  simp only [fnTwist3_apply, chiDetGL_three_centralScalarGL_mul, hφ, twistedCentralChar3_apply]; ring

end Twist

end LanglandsTunnell.CubicInduction

end


