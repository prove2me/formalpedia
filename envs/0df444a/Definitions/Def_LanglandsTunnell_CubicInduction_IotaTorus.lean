-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
-- name    : LanglandsTunnell_CubicInduction_IotaTorus
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/9388b3ce-c78e-54e4-8eae-099e526eca31
-- title:
--   Diagonal tori in GL₂/GL₃ over p-adic completions; countability
-- statement:
--   For a commutative ring $A$ and a unit $x \in A^\times$, `diagUnitGL2 x` is the element of $\mathrm{GL}_2(A)$ with matrix $\begin{pmatrix}x&0\\0&1\end{pmatrix}$, its inverse being given by $x^{-1}$ in the corner; `coe_diagUnitGL2` records the underlying matrix, and `diagHom` packages $x \mapsto$ `diagUnitGL2 x` as a monoid homomorphism $A^\times \to \mathrm{GL}_2(A)$, with `diagHom_apply` identifying its values.
--
--   The second group of definitions works at a finite place $v$ of $\mathbb{Q}$, i.e. a height-one prime of the ring of integers $\mathcal{O}_{\mathbb{Q}}$. Here `ratPrimeAt v` is the image in the $v$-adic completion of $\mathbb{Q}$ of the natural number $\mathrm{absNorm}(v)$, that is of the residue characteristic $p$; `ratPrimeAt_ne_zero` shows it is nonzero, using that the absolute norm of a height-one prime exceeds $1$ together with the characteristic-zero structure of the completion, and `ratPrimeUnit v` is the resulting unit of $\mathbb{Q}_v$. For $n \in \mathbb{N}$, `iotaTorusLocal v n` is the image of $\mathrm{diag}(p^n,1)$ under the block embedding `iotaGL` of $\mathrm{GL}_2$ into $\mathrm{GL}_3$, hence the element $\mathrm{diag}(p^n,1,1)$ of $\mathrm{GL}_3(\mathbb{Q}_v)$. The lemmas `iotaTorusLocal_zero` and `iotaTorusLocal_add` state that this assignment sends $0$ to the identity and addition of exponents to multiplication, so that $n \mapsto$ `iotaTorusLocal v n` is a one-parameter semigroup of diagonal elements.
--
--   Finally, for a countable field $K$ two countability instances are provided: $\mathrm{GL}_2(K)$ is countable, by injectivity of the passage to the underlying $2 \times 2$ matrix; and `MirabolicIndex K`, the quotient of $\mathrm{GL}_2(K)$ by the right coset relation of the range of the unipotent homomorphism $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$, is countable as a quotient of a countable type.
--
--   **Relation to Mathlib.** `diagHom` records in explicit $2\times 2$ matrix notation the same homomorphism as the project's [`NumberField.AdelicLevel.diagOne`](../def/NumberField_AdelicLevel.html#L624), which uses `Matrix.diagonal ![a, 1]`; the countability statements are instances assembled from Mathlib's countability machinery.
--
--   **Where it is used.** These diagonal elements supply the torus translations used in the cubic (non-normal cubic base change) induction feeding into the Langlands–Tunnell theorem, which provides the modularity of the mod $3$ representation attached to a Frey curve. The countability instances serve the bookkeeping over the mirabolic coset index set that parametrises the relevant orbit decompositions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_IotaTorus.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section DiagHom

variable {A : Type*} [CommRing A]

def diagUnitGL2 (x : Aˣ) : GL (Fin 2) A where
  val := !![(x : A), 0; 0, 1]
  inv := !![((x⁻¹ : Aˣ) : A), 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem coe_diagUnitGL2 (x : Aˣ) :
    ((diagUnitGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(x : A), 0; 0, 1] :=
  rfl

def diagHom : Aˣ →* GL (Fin 2) A where
  toFun := diagUnitGL2
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagHom_apply (x : Aˣ) : diagHom x = diagUnitGL2 x :=
  rfl

end DiagHom

section RatTorus

variable (v : HeightOneSpectrum (𝓞 ℚ))

def ratPrimeAt : v.adicCompletion ℚ :=
  ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ)

theorem ratPrimeAt_ne_zero : ratPrimeAt v ≠ 0 := by
  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  have h : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  exact Nat.cast_ne_zero.mpr (by omega)

def ratPrimeUnit : (v.adicCompletion ℚ)ˣ :=
  Units.mk0 (ratPrimeAt v) (ratPrimeAt_ne_zero v)

def iotaTorusLocal (n : ℕ) : GL (Fin 3) (v.adicCompletion ℚ) :=
  iotaGL (diagHom (ratPrimeUnit v ^ n))

@[simp] theorem iotaTorusLocal_zero : iotaTorusLocal v 0 = 1 := by
  simp only [iotaTorusLocal, pow_zero, map_one]

theorem iotaTorusLocal_add (m n : ℕ) :
    iotaTorusLocal v (m + n) = iotaTorusLocal v m * iotaTorusLocal v n := by
  simp only [iotaTorusLocal, pow_add, map_mul]

end RatTorus

section Countable

variable (K : Type*) [Field K] [Countable K]

instance countable_GL2 : Countable (GL (Fin 2) K) :=
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  Function.Injective.countable fun _ _ h => Units.ext h

instance countable_mirabolicIndex : Countable (MirabolicIndex K) := by
  unfold MirabolicIndex
  infer_instance

end Countable

end LanglandsTunnell.CubicInduction


