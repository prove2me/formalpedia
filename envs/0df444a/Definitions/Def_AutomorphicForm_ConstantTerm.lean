-- Prove2me | Definitions.Def_AutomorphicForm_ConstantTerm
-- name    : AutomorphicForm_ConstantTerm
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/1348c743-ec7e-5a46-83d1-4994bed44054
-- title:
--   Unipotent elements of GL2​ and an abstract constant term
-- statement:
--   Two unrelated-looking pieces of elementary infrastructure. First, for a commutative ring $R$, `unipotentGL2 x` is the element of $\mathrm{GL}_2(R)$ given by the matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ together with its explicit inverse $\begin{pmatrix}1&-x\\0&1\end{pmatrix}$; the accompanying lemmas record the coercion to a matrix, that $x=0$ gives the identity, the additivity $u(x+y)=u(x)u(y)$ (so the order of multiplication is immaterial here), and package this as a monoid homomorphism `unipotentGL2Hom` from `Multiplicative R` (the additive group of $R$ written multiplicatively) to $\mathrm{GL}_2(R)$. Second, for a measurable space $Q$, a group $G$ (with no topology, measurability or integrability hypotheses on $G$), a family $u : Q \to G$, a measure $\mu$ on $Q$ and a function $f : G \to \mathbb{C}$, the integrand `constantTermIntegrand u f g` is $q \mapsto f(u(q)\,g)$ and `constantTerm μ u f g` is its Bochner integral $\int_Q f(u(q)g)\,d\mu(q)$; since Mathlib's integral is defined to be $0$ for non-integrable functions, no integrability is assumed and none is asserted. Two computations are recorded: the constant term of the zero function vanishes, and if $\mu$ is a probability measure the constant term of the constant function $c$ is $c$. Finally `IsCuspidalFn μ u f` is the predicate that $\mathrm{constantTerm}\ \mu\ u\ f\ g = 0$ for every $g \in G$. Thus cuspidality here is a purely formal condition relative to the chosen data $(Q,\mu,u)$: it becomes the classical vanishing of the constant term $\varphi_N(g)=\int f(n(x)g)\,dx$ along the unipotent radical only once $Q$, $\mu$ and $u$ are instantiated with an adelic quotient, a Haar probability measure and the unipotent family above.
--
--   **Relation to Mathlib.** Mathlib supplies the matrix and general linear group machinery and the Bochner integral used here, but has no notion of constant term along a unipotent family nor of a cuspidal function; those are the project's own definitions, stated for abstract data $(Q,\mu,u)$ rather than for a specific adelic group.
--
--   **Where it is used.** These definitions are the base layer for the project's treatment of cuspidality for automorphic forms on $\mathrm{GL}_2$, the cuspidal condition entering the modularity side of the argument; the module is imported throughout the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ConstantTerm.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Matrix MeasureTheory

namespace AutomorphicForm

section Unipotent

variable {R : Type*} [CommRing R]

private theorem unipotent_mul_unipotent (x y : R) :
    !![1, x; 0, 1] * !![1, y; 0, 1] = !![1, x + y; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def unipotentGL2 (x : R) : GL (Fin 2) R where
  val := !![1, x; 0, 1]
  inv := !![1, -x; 0, 1]
  val_inv := by rw [unipotent_mul_unipotent, add_neg_cancel, Matrix.one_fin_two]
  inv_val := by rw [unipotent_mul_unipotent, neg_add_cancel, Matrix.one_fin_two]

@[simp] theorem unipotentGL2_coe (x : R) :
    (unipotentGL2 x : Matrix (Fin 2) (Fin 2) R) = !![1, x; 0, 1] := rfl

@[simp] theorem unipotentGL2_zero : unipotentGL2 (0 : R) = 1 := by
  ext i j; simp [unipotentGL2, Matrix.one_fin_two]

theorem unipotentGL2_add (x y : R) :
    unipotentGL2 (x + y) = unipotentGL2 x * unipotentGL2 y := by
  ext i j; simp only [unipotentGL2, Units.val_mul, unipotent_mul_unipotent]

def unipotentGL2Hom : Multiplicative R →* GL (Fin 2) R where
  toFun x := unipotentGL2 x.toAdd
  map_one' := unipotentGL2_zero
  map_mul' x y := unipotentGL2_add x.toAdd y.toAdd

end Unipotent

section ConstantTerm

variable {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]

def constantTermIntegrand (u : Q → G) (f : G → ℂ) (g : G) : Q → ℂ :=
  fun q => f (u q * g)

noncomputable def constantTerm (μ : Measure Q) (u : Q → G) (f : G → ℂ) (g : G) : ℂ :=
  ∫ q, constantTermIntegrand u f g q ∂μ

@[simp] theorem constantTerm_zero (μ : Measure Q) (u : Q → G) (g : G) :
    constantTerm μ u (fun _ => (0 : ℂ)) g = 0 := by
  simp [constantTerm, constantTermIntegrand]

@[simp] theorem constantTerm_const (μ : Measure Q) [IsProbabilityMeasure μ] (u : Q → G)
    (c : ℂ) (g : G) : constantTerm μ u (fun _ => c) g = c := by
  simp [constantTerm, constantTermIntegrand, integral_const, measureReal_def]

def IsCuspidalFn (μ : Measure Q) (u : Q → G) (f : G → ℂ) : Prop :=
  ∀ g : G, constantTerm μ u f g = 0

end ConstantTerm

end AutomorphicForm


