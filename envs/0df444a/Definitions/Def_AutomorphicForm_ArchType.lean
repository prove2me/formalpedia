-- Prove2me | Definitions.Def_AutomorphicForm_ArchType
-- name    : AutomorphicForm_ArchType
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/ad430148-4aa3-5400-9b8a-2d573edbf8a9
-- title:
--   Archimedean type of adelic automorphic forms on GL2​
-- statement:
--   Let $F$ be a number field. The module first builds inclusions of local unit groups at an infinite place into the adelic group. Via the ring equivalence `archMatrixPiEquiv` identifying $2\times 2$ matrices over the infinite adele ring with the product over infinite places $w$ of $2\times 2$ matrices over `w.Completion`, `archMatrixUpdate F w m` is the matrix whose $w$-component is $m$ and whose component at every $v\neq w$ is the identity matrix (`Function.update 1 w m`); the helper lemmas record its components, that it sends $1$ to $1$ and respects multiplication, which makes it a monoid homomorphism `archMatrixInclHom`, whence `archGLIncl F w` : $\mathrm{GL}_2(F_w) \to^* \mathrm{GL}_2(\mathbb{A}_{F,\infty})$ by `Units.map`. `adelicMatrixProdEquiv` is the ring equivalence between $2\times2$ matrices over the full adele ring and the product of matrices over the infinite and the finite adele rings; composing the induced unit-group equivalence with the inclusion $k\mapsto (k,1)$ gives `adelicArchGLIncl F` : $\mathrm{GL}_2(\mathbb{A}_{F,\infty}) \to^*$ `AdelicGL2 (𝓞 F) F`, and `adelicArchGLInclAt F w` is its composite with `archGLIncl F w`. Two lemmas record that the archimedean projection `glArch` of `adelicArchGLIncl F k` is $k$ and the finite projection `glFin` is $1$; two further lemmas record the analogous component identities for `archGLIncl`.
--
--   The predicates are the point of the module. For a place $w$ and a monoid homomorphism $\chi$ from the project's `rowIsometrySubgroup w.Completion` to $\mathbb{C}^\times$, `HasArchCharacterAt F w χ φ` asserts, for a function $\varphi$ on `AdelicGL2 (𝓞 F) F` with no continuity or smoothness demanded, that $\varphi(g\,\iota_w(k))=\chi(k)\varphi(g)$ for all $k$ in that subgroup and all $g$, where $\iota_w=$`adelicArchGLInclAt F w`. `HasArchType F χ φ` says this holds at every infinite place for the corresponding member of a family $\chi=(\chi_w)_w$. `archRowIsometryAt F w` is the image subgroup of `rowIsometrySubgroup w.Completion` under `archGLIncl F w`. Finally: the zero function has every archimedean type; constants have the trivial type; the constant $1$ fails any character taking a value $\neq 1$, and any nonzero constant fails any type with some $\chi_{w_0}$ nontrivial. No function of a nontrivial type is constructed here.
--
--   **Relation to Mathlib.** The transversal notions — the row-isometry subgroup, `AdelicGL2`, the projections `glArch` and `glFin`, and the predicates `HasArchCharacterAt`/`HasArchType` — are the project's own; the matrix and unit-group plumbing (`Matrix.piRingEquiv`, `Units.map`, `MulEquiv.prodUnits`, `InfiniteAdeleRing`, `IsDedekindDomain.FiniteAdeleRing`) is Mathlib's.
--
--   **Where it is used.** These predicates fix the archimedean equivariance condition in the project's definition of adelic automorphic forms on $\mathrm{GL}_2$, the forms through which the modularity side of the Frey-curve argument is phrased; they encode a one-dimensional $K_\infty$-type rather than general $K_\infty$-finiteness. The specific weight character at a real place is treated elsewhere, each consumer binding its own family $\chi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ArchType.lean

import Definitions.Def_AutomorphicForm_RowIsometryInvariance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField AdelicLevel IsDedekindDomain Matrix

open scoped Classical

namespace AutomorphicForm

section MatrixFurniture

variable (F : Type) [Field F]

noncomputable section

abbrev archMatrixPiEquiv :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) ≃+* Π w : InfinitePlace F,
      Matrix (Fin 2) (Fin 2) w.Completion :=
  Matrix.piRingEquiv (β := fun w : InfinitePlace F => w.Completion)

theorem archMatrixPiEquiv_apply (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
    (w : InfinitePlace F) (i j : Fin 2) :
    archMatrixPiEquiv F m w i j = m i j w := rfl

def archMatrixUpdate (w : InfinitePlace F) (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) :=
  (archMatrixPiEquiv F).symm (Function.update 1 w m)

theorem archMatrixPiEquiv_archMatrixUpdate (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    archMatrixPiEquiv F (archMatrixUpdate F w m)
      = Function.update (1 : Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w m :=
  (archMatrixPiEquiv F).apply_symm_apply _

theorem archMatrixUpdate_apply_self (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) (i j : Fin 2) :
    archMatrixUpdate F w m i j w = m i j := by
  have h := archMatrixPiEquiv_archMatrixUpdate F w m
  have hw := congrFun h w
  simp only [Function.update_self] at hw
  exact congrFun (congrFun hw i) j

theorem archMatrixUpdate_apply_of_ne (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) (i j : Fin 2)
    {v : InfinitePlace F} (hvw : v ≠ w) :
    archMatrixUpdate F w m i j v = (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j := by
  have h := archMatrixPiEquiv_archMatrixUpdate F w m
  have hv := congrFun h v
  simp only [Function.update_of_ne hvw, Pi.one_apply] at hv
  exact congrFun (congrFun hv i) j

theorem archMatrixUpdate_one (w : InfinitePlace F) :
    archMatrixUpdate F w (1 : Matrix (Fin 2) (Fin 2) w.Completion) = 1 := by
  apply (archMatrixPiEquiv F).injective
  rw [archMatrixPiEquiv_archMatrixUpdate, map_one]
  exact Function.update_eq_self_iff.mpr rfl

theorem archMatrixUpdate_mul (w : InfinitePlace F)
    (a b : Matrix (Fin 2) (Fin 2) w.Completion) :
    archMatrixUpdate F w (a * b) = archMatrixUpdate F w a * archMatrixUpdate F w b := by
  apply (archMatrixPiEquiv F).injective
  rw [archMatrixPiEquiv_archMatrixUpdate, map_mul,
    archMatrixPiEquiv_archMatrixUpdate, archMatrixPiEquiv_archMatrixUpdate]
  funext v
  by_cases hv : v = w
  · subst hv
    simp
  · simp [Function.update_of_ne hv]

def archMatrixInclHom (w : InfinitePlace F) :
    Matrix (Fin 2) (Fin 2) w.Completion →* Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) where
  toFun := archMatrixUpdate F w
  map_one' := archMatrixUpdate_one F w
  map_mul' := archMatrixUpdate_mul F w

def archGLIncl (w : InfinitePlace F) :
    GL (Fin 2) w.Completion →* GL (Fin 2) (InfiniteAdeleRing F) :=
  Units.map (archMatrixInclHom F w)

end

end MatrixFurniture

section ComponentReceipts

variable (F : Type) [Field F]

theorem archComponent_archGLIncl_self (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    archComponent F w (archGLIncl F w k) = k := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show archEval F w (archMatrixUpdate F w (k : _) i j) = (k : _) i j
  rw [archEval_apply, archMatrixUpdate_apply_self]

theorem archComponent_archGLIncl_of_ne {v w : InfinitePlace F} (hvw : v ≠ w)
    (k : GL (Fin 2) w.Completion) :
    archComponent F v (archGLIncl F w k) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show archEval F v (archMatrixUpdate F w (k : _) i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j
  rw [archEval_apply, archMatrixUpdate_apply_of_ne _ _ _ _ _ hvw]

end ComponentReceipts

section AdelicInclusion

variable (F : Type) [Field F] [NumberField F]

noncomputable section

def adelicMatrixProdEquiv :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) ≃+*
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) ×
        Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) where
  toFun M := ((RingHom.fst _ _).mapMatrix M, (RingHom.snd _ _).mapMatrix M)
  invFun p := Matrix.of fun i j => (p.1 i j, p.2 i j)
  left_inv M := by ext i j; rfl
  right_inv p := by ext i j <;> rfl
  map_mul' M N := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul]; exact map_mul _ M N
    · simp only [Prod.snd_mul]; exact map_mul _ M N
  map_add' M N := rfl

def adelicArchGLIncl : GL (Fin 2) (InfiniteAdeleRing F) →* AdelicGL2 (𝓞 F) F :=
  (Units.mapEquiv (adelicMatrixProdEquiv F).symm.toMulEquiv).toMonoidHom.comp <|
    (MulEquiv.prodUnits.symm : _ ≃* (_ × _)ˣ).toMonoidHom.comp <|
      MonoidHom.prod (MonoidHom.id _) (1 : _ →* GL (Fin 2) _)

def adelicArchGLInclAt (w : InfinitePlace F) :
    GL (Fin 2) w.Completion →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLIncl F).comp (archGLIncl F w)

theorem glArch_adelicArchGLIncl (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    glArch (𝓞 F) F (adelicArchGLIncl F k) = k := by
  ext i j
  rfl

theorem glFin_adelicArchGLIncl (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    glFin (𝓞 F) F (adelicArchGLIncl F k) = 1 := by
  ext i j
  rfl

end

end AdelicInclusion

section Predicate

variable (F : Type) [Field F] [NumberField F]

noncomputable def archRowIsometryAt (w : InfinitePlace F) : Subgroup (GL (Fin 2) (InfiniteAdeleRing F)) :=
  (rowIsometrySubgroup w.Completion).map (archGLIncl F w)

def HasArchCharacterAt (w : InfinitePlace F) (χ : rowIsometrySubgroup w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ k : rowIsometrySubgroup w.Completion, ∀ g : AdelicGL2 (𝓞 F) F,
    φ (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion))
      = (χ k : ℂ) * φ g

def HasArchType (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ w : InfinitePlace F, HasArchCharacterAt F w (χ w) φ

theorem hasArchType_zero (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ) :
    HasArchType F χ (fun _ => 0) := fun _ _ _ => by simp

theorem hasArchType_const_of_trivial (c : ℂ) :
    HasArchType F (fun _ => 1) (fun _ => c) := fun _ _ _ => (one_mul c).symm

theorem not_hasArchCharacterAt_one_of_ne_one (w : InfinitePlace F)
    (χ : rowIsometrySubgroup w.Completion →* ℂˣ)
    (k : rowIsometrySubgroup w.Completion) (hχ : χ k ≠ 1) :
    ¬ HasArchCharacterAt F w χ (fun _ => (1 : ℂ)) := fun h => by
  have hk := h k 1
  simp only [mul_one] at hk
  exact hχ (Units.val_eq_one.mp hk.symm)

theorem not_hasArchType_const_of_exists_ne_one
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ)
    (w₀ : InfinitePlace F) (k : rowIsometrySubgroup w₀.Completion) (hχ : χ w₀ k ≠ 1)
    (c : ℂ) (hc : c ≠ 0) :
    ¬ HasArchType F χ (fun _ => c) := fun h => by
  have hk : c = (χ w₀ k : ℂ) * c := h w₀ k 1
  have : ((χ w₀ k : ℂ) - 1) * c = 0 := by linear_combination -hk
  rcases mul_eq_zero.mp this with h1 | h0
  · exact hχ (Units.val_eq_one.mp (sub_eq_zero.mp h1))
  · exact hc h0

end Predicate

end AutomorphicForm


