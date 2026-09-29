-- Prove2me | Definitions.Def_AutomorphicForm_AdelicKernel
-- name    : AutomorphicForm_AdelicKernel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/6486bbd6-b8db-5687-ae5e-f81176cb60f8
-- title:
--   Adelic trace-formula kernel for GL2​ and its conjugacy-cell parts
-- statement:
--   Throughout, $F$ is a number field, $\mathbb{A}_F$ its adele ring (formed from the ring of integers $\mathcal{O}_F$ and $F$), and `AdelicGL2 (𝓞 F) F` is $\mathrm{GL}_2(\mathbb{A}_F)$; `globalPoints` is the group homomorphism $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb{A}_F)$ induced by the structure map $F \to \mathbb{A}_F$. For a test function $f$ on $\mathrm{GL}_2(\mathbb{A}_F)$ with values in an arbitrary additive commutative monoid $M$, `adelicKernel` is the function of two adelic arguments
--   $$K_f(x,y) \;=\; \sum_{\gamma \in \mathrm{GL}_2(F)}^{\mathrm{f}} f\bigl(x^{-1}\,\gamma\,y\bigr),$$
--   the sum being Mathlib's `finsum`: it is the finite sum of the values when the family has finite support and $0$ otherwise, so that any identity about $K_f$ must carry its own finiteness hypothesis. Four further definitions, `adelicKernelCentralPart`, `adelicKernelUnipotentPart`, `adelicKernelHyperbolicPart` and `adelicKernelEllipticPart`, are the same expression with the index restricted to one of the four conjugacy-type cells of $\mathrm{GL}_2(F)$: $\gamma$ is of central type if its matrix is a scalar multiple of the identity; of unipotent type if it is not central and its characteristic polynomial is $(X-a)^2$ for some $a \in F$; of hyperbolic type if that polynomial is $(X-a)(X-b)$ with $a \neq b$ in $F$; and of elliptic type if it has no root in $F$. These four conditions are mutually exclusive and exhaust $\mathrm{GL}_2(F)$.
--
--   The final declaration `AdelicKernelLocalFiniteness` is a proposition attached to $F$, not a theorem proved here: it asserts that for every compact subset $C \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ and all $x, y \in \mathrm{GL}_2(\mathbb{A}_F)$, the set of $\gamma \in \mathrm{GL}_2(F)$ with $x^{-1}\gamma y \in C$ is finite. It is the interface through which consumers assume the discreteness property of $\mathrm{GL}_2(F)$ inside $\mathrm{GL}_2(\mathbb{A}_F)$ that makes the kernel sums locally finite.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, the general linear group of matrices and the `finsum` convention; the kernel, its conjugacy-cell parts and the local-finiteness proposition, as well as the underlying conjugacy-type predicates on $2 \times 2$ matrices, are the project's own.
--
--   **Where it is used.** These definitions provide the vocabulary of the adelic trace formula for $\mathrm{GL}_2$ over a number field, on the automorphic side of the development; the cell decomposition of the kernel is the shape in which the geometric side of such a formula is organised.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_AdelicKernel.lean

import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix

open scoped NumberField

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

section Kernel

variable {M : Type*} [AddCommMonoid M]

def adelicKernel (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) : M :=
  ∑ᶠ γ : GL (Fin 2) F, f (x⁻¹ * globalPoints (𝓞 F) F γ * y)

def adelicKernelCentralPart (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) : M :=
  ∑ᶠ γ ∈ centralCell F, f (x⁻¹ * globalPoints (𝓞 F) F γ * y)

def adelicKernelUnipotentPart (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) : M :=
  ∑ᶠ γ ∈ unipotentCell F, f (x⁻¹ * globalPoints (𝓞 F) F γ * y)

def adelicKernelHyperbolicPart (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) : M :=
  ∑ᶠ γ ∈ hyperbolicCell F, f (x⁻¹ * globalPoints (𝓞 F) F γ * y)

def adelicKernelEllipticPart (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) : M :=
  ∑ᶠ γ ∈ ellipticCell F, f (x⁻¹ * globalPoints (𝓞 F) F γ * y)

end Kernel

def AdelicKernelLocalFiniteness : Prop :=
  ∀ C : Set (AdelicGL2 (𝓞 F) F), IsCompact C → ∀ x y : AdelicGL2 (𝓞 F) F,
    {γ : GL (Fin 2) F | x⁻¹ * globalPoints (𝓞 F) F γ * y ∈ C}.Finite

end AutomorphicForm


