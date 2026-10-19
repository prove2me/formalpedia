-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
-- name    : OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:56:18.864984+00:00
-- url     : https://prove2.me/theorems/6251bef5-b031-403c-bfa0-e0b7afbc7634
-- title:
--   The cyclic group algebra as a polynomial quotient
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction. Write $R[\mathbb Z/n]$ for the cyclic group ring (finitely supported coefficient functions on $\mathbb Z/n$ with convolution), $e_a$ for its basis element at $a$, and $f^{*}(a)=\overline{f(-a)}$ for its involution, which reverses indices and applies the coefficient star.
--
--   1. **Relation and generator.** The polynomial $X^n-1\in R[X]$ and the basis element $e_1$ at the generator of $\mathbb Z/n$.
--   2. **Power character.** For an element $x$ of a monoid with $x^n=1$ and $n>0$, the character of $\mathbb Z/n$ sending $a$ to $x^{a}$, with $a$ read in $\{0,\dots,n-1\}$.
--   3. **Polynomial presentation.** For a commutative ring $R$ and $n>0$, the $R$-algebra isomorphism
--   $$
--   R[\mathbb Z/n]\;\cong\;R[X]/(X^n-1),\qquad e_a\mapsto X^{a},
--   $$
--   built from the two universal properties. Its inverse evaluates a polynomial at $e_1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclicPolynomial.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/CyclicPolynomial.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CirculantHadamard mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation

namespace OAI

universe uR uA

/-!
# The polynomial presentation of the actual cyclic group algebra

For a commutative coefficient ring and a positive integer `n`, the cyclic group
algebra is the quotient of `R[X]` by `X ^ n - 1`. The two maps are defined
by their universal properties, and both inverse identities are proved explicitly.
No domain property of the finite group algebra is used.
-/

noncomputable section

namespace CirculantHadamard.CyclicPolynomial

open Polynomial

variable (R : Type uR) [CommRing R] (n : ℕ)

/-- The defining polynomial of the cyclic group algebra. -/
def relation : R[X] := X ^ n - 1

/-- The basis element at the distinguished generator of the cyclic group. -/
def generator : AddMonoidAlgebra R (ZMod n) := AddMonoidAlgebra.single 1 1

theorem generator_pow : generator R n ^ n = 1 := by
  simp [generator, AddMonoidAlgebra.single_pow, nsmul_eq_mul,
    AddMonoidAlgebra.one_def]

theorem root_pow : AdjoinRoot.root (relation R n) ^ n = 1 := by
  have h : AdjoinRoot.mk (relation R n) (X ^ n - 1) = 0 :=
    AdjoinRoot.mk_self (f := relation R n)
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact sub_eq_zero.mp h

variable {R}

/-- A genuine cyclic character associated to an element whose `n`th power is one. -/
def powerCharacter {A : Type uA} [Monoid A] [NeZero n]
    (x : A) (hx : x ^ n = 1) : Multiplicative (ZMod n) →* A where
  toFun a := x ^ a.toAdd.val
  map_one' := by
    change x ^ (0 : ZMod n).val = 1
    simp
  map_mul' a b := by
    change x ^ (a.toAdd + b.toAdd).val =
      x ^ a.toAdd.val * x ^ b.toAdd.val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

@[simp]
theorem powerCharacter_apply {A : Type uA} [Monoid A] [NeZero n]
    (x : A) (hx : x ^ n = 1) (i : ZMod n) :
    powerCharacter n x hx (Multiplicative.ofAdd i) = x ^ i.val := rfl

@[simp]
theorem powerCharacter_generator {A : Type uA} [Monoid A] [NeZero n]
    (x : A) (hx : x ^ n = 1) :
    powerCharacter n x hx (Multiplicative.ofAdd 1) = x := by
  change x ^ (1 : ZMod n).val = x
  rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hx, pow_one]

variable (R)

/-- Send the cyclic basis element at `i` to the `i.val`th power of the root. -/
def toPolynomial [NeZero n] :
    AddMonoidAlgebra R (ZMod n) →ₐ[R] AdjoinRoot (relation R n) :=
  AddMonoidAlgebra.lift R (AdjoinRoot (relation R n)) (ZMod n)
    (powerCharacter n (AdjoinRoot.root (relation R n)) (root_pow R n))

@[simp]
theorem toPolynomial_single [NeZero n] (i : ZMod n) (r : R) :
    toPolynomial R n (AddMonoidAlgebra.single i r) =
      algebraMap R (AdjoinRoot (relation R n)) r *
        AdjoinRoot.root (relation R n) ^ i.val := by
  simp [toPolynomial, Algebra.smul_def]

@[simp]
theorem toPolynomial_generator [NeZero n] :
    toPolynomial R n (generator R n) = AdjoinRoot.root (relation R n) := by
  simp only [generator, toPolynomial, AddMonoidAlgebra.lift_single,
    powerCharacter_generator, one_smul]

theorem generator_isRoot : aeval (generator R n) (relation R n) = 0 := by
  simp [relation, generator_pow]

/-- Evaluate the polynomial quotient at the actual cyclic group-ring generator. -/
def fromPolynomial :
    AdjoinRoot (relation R n) →ₐ[R] AddMonoidAlgebra R (ZMod n) :=
  AdjoinRoot.liftAlgHom (relation R n)
    (Algebra.ofId R (AddMonoidAlgebra R (ZMod n)))
    (generator R n) (generator_isRoot R n)

@[simp]
theorem fromPolynomial_root :
    fromPolynomial R n (AdjoinRoot.root (relation R n)) = generator R n := by
  exact AdjoinRoot.liftAlgHom_root (relation R n)
    (Algebra.ofId R (AddMonoidAlgebra R (ZMod n)))
    (generator R n) (generator_isRoot R n)

@[simp]
theorem fromPolynomial_mk (p : R[X]) :
    fromPolynomial R n (AdjoinRoot.mk (relation R n) p) =
      aeval (generator R n) p := by
  exact AdjoinRoot.liftAlgHom_mk (relation R n)
    (Algebra.ofId R (AddMonoidAlgebra R (ZMod n)))
    (generator R n) (generator_isRoot R n) p

theorem generator_pow_val [NeZero n] (i : ZMod n) :
    generator R n ^ i.val = AddMonoidAlgebra.single i 1 := by
  simp [generator, AddMonoidAlgebra.single_pow, nsmul_eq_mul]

theorem toPolynomial_comp_fromPolynomial [NeZero n] :
    (toPolynomial R n).comp (fromPolynomial R n) =
      AlgHom.id R (AdjoinRoot (relation R n)) := by
  apply AdjoinRoot.algHom_ext
  simp

theorem fromPolynomial_comp_toPolynomial [NeZero n] :
    (fromPolynomial R n).comp (toPolynomial R n) =
      AlgHom.id R (AddMonoidAlgebra R (ZMod n)) := by
  apply AddMonoidAlgebra.algHom_ext
  · intro i
    simp [generator_pow_val]
  · exact Subsingleton.elim _ _

/-- The actual cyclic group algebra is the polynomial quotient by `X ^ n - 1`. -/
def cyclicEquiv [NeZero n] :
    AddMonoidAlgebra R (ZMod n) ≃ₐ[R] AdjoinRoot (relation R n) :=
  AlgEquiv.ofAlgHom (toPolynomial R n) (fromPolynomial R n)
    (toPolynomial_comp_fromPolynomial R n) (fromPolynomial_comp_toPolynomial R n)

@[simp]
theorem cyclicEquiv_single [NeZero n] (i : ZMod n) (r : R) :
    cyclicEquiv R n (AddMonoidAlgebra.single i r) =
      algebraMap R (AdjoinRoot (relation R n)) r *
        AdjoinRoot.root (relation R n) ^ i.val :=
  toPolynomial_single R n i r

@[simp]
theorem cyclicEquiv_generator [NeZero n] :
    cyclicEquiv R n (generator R n) = AdjoinRoot.root (relation R n) :=
  toPolynomial_generator R n

@[simp]
theorem cyclicEquiv_symm_root [NeZero n] :
    (cyclicEquiv R n).symm (AdjoinRoot.root (relation R n)) = generator R n :=
  fromPolynomial_root R n

@[simp]
theorem cyclicEquiv_symm_mk [NeZero n] (p : R[X]) :
    (cyclicEquiv R n).symm (AdjoinRoot.mk (relation R n) p) =
      aeval (generator R n) p :=
  fromPolynomial_mk R n p

@[simp]
theorem cyclicEquiv_aeval [NeZero n] (p : R[X]) :
    cyclicEquiv R n (aeval (generator R n) p) =
      AdjoinRoot.mk (relation R n) p := by
  rw [← Polynomial.aeval_algHom_apply, cyclicEquiv_generator,
    AdjoinRoot.aeval_eq]

end CirculantHadamard.CyclicPolynomial

end

end OAI


