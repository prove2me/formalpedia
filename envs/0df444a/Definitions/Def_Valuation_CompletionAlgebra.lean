-- Prove2me | Definitions.Def_Valuation_CompletionAlgebra
-- name    : Valuation_CompletionAlgebra
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/23035f84-0ef6-512a-b3df-6448f85287bc
-- title:
--   Algebra structure on the completion of a valued field
-- statement:
--   Fix a field $K$, a linearly ordered commutative group with zero $\Gamma_0$, and a valuation $v \colon K \to \Gamma_0$. Mathlib's `WithVal v` is the type $K$ equipped with the uniform structure coming from $v$, and `v.Completion` is the uniform-space completion of that type. Two instances are recorded for `WithVal v`: the multiplication maps $x \mapsto a x$ by a fixed scalar $a \in K$ are continuous (`continuousConstSMul_withVal`, since they are multiplication by the constant `WithVal.toVal v a`), and consequently, the scalar action of $K$ on `WithVal v` being by multiplication in a topological group setting, they are uniformly continuous (`uniformContinuousConstSMul_withVal`, obtained from the continuity statement). With uniform continuity of the constant scalar multiplications available, Mathlib's construction of an algebra structure on a completion applies, and `algebraCompletion` records the resulting instance `Algebra K v.Completion`.
--
--   Two simple identities pin down this structure in terms of the canonical map $K \to$ `v.Completion`: `algebraMap_completion_apply` states that $\mathrm{algebraMap}\,K\,\hat K_v(a)$ is the image $(a : \hat K_v)$ of $a$ under the coercion, and `smul_completion_def` states that $a \bullet x = (a : \hat K_v) \cdot x$ for $a \in K$ and $x \in \hat K_v$. The module also records, as an `example`, that the scalar multiplication of $K$ on `v.Completion` coming from the algebra structure coincides with the pre-existing scalar multiplication on a completion obtained by continuous extension; so hypotheses such as a scalar-tower condition formulated against either action are literally the same hypothesis, and no separate algebra binder together with a compatibility equation between `algebraMap` and the coercion is needed.
--
--   **Relation to Mathlib.** The two `ContinuousConstSMul`/`UniformContinuousConstSMul` instances and the `Algebra K v.Completion` instance fill a gap in Mathlib: Mathlib's algebra structure on a uniform-space completion requires uniform continuity of the constant scalar multiplications on `WithVal v`, which was not registered there; the instance itself is then Mathlib's, and the scalar action agrees with Mathlib's action on a completion.
--
--   **Where it is used.** The resulting canonical `Algebra K v.Completion` is used when completions of a field at a place are treated as algebras over that field — for instance completions of $\overline{\mathbb{Q}}$ at a place, and constant-field extensions of function fields over $\overline{\mathbb{Q}}$, where a scalar tower between the base field, the completion and a larger field can be stated with this instance.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Valuation_CompletionAlgebra.lean

import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.UniformMulAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace Valuation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

instance continuousConstSMul_withVal : ContinuousConstSMul K (WithVal v) :=
  ⟨fun a => continuous_const_mul (WithVal.toVal v a)⟩

instance uniformContinuousConstSMul_withVal : UniformContinuousConstSMul K (WithVal v) :=
  uniformContinuousConstSMul_of_continuousConstSMul K (WithVal v)

instance algebraCompletion : Algebra K v.Completion := inferInstance

@[simp] theorem algebraMap_completion_apply (a : K) : algebraMap K v.Completion a = (a : v.Completion) := rfl

theorem smul_completion_def (a : K) (x : v.Completion) : a • x = (a : v.Completion) * x :=
  Algebra.smul_def a x

example : (Algebra.toSMul : SMul K v.Completion) = UniformSpace.Completion.instSMul K (WithVal v) := rfl

end Valuation

end


