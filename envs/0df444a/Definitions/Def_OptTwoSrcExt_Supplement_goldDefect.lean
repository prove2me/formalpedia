-- Prove2me | Definitions.Def_OptTwoSrcExt_Supplement_goldDefect
-- name    : OptTwoSrcExt_Supplement_goldDefect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:36:44.868275+00:00
-- url     : https://prove2.me/theorems/33043fff-cc25-4362-8f29-e492a724632c
-- title:
--   Additive energy, graph of a map, $\mathrm{RM}(2,N)|_A$, the Gold space and the Gold defect $d_c(f;A)$
-- statement:
--   1. For a finite subset $S$ of a binary vector space, its **additive energy** is
--   $$E(S)=\big|\{(z_1,z_2,z_3,z_4)\in S^4: z_1+z_2+z_3+z_4=0\}\big| .$$
--   2. For $A\subseteq L$ and $f:A\to L$, the **graph** of $f$ on $A$ is $\mathrm{Graph}(f|_A)=\{(x,f(x)):x\in A\}\subseteq L\times L$.
--   3. Let $L=\mathbb F_{2^N}$. $\mathrm{RM}(2,N)|_A\le\mathbb F_2^A$ is the space of restrictions to $A$ of Boolean polynomials of degree at most two in the binary coordinates of $L$ (constants included).
--   4. The **Gold space** is $C_c=\{z\mapsto \mathrm{Tr}_{L/\mathbb F_2}(a_0z+\sum_{j=1}^c a_jz^{1+2^j}):a_0,\dots,a_c\in L\}$, and its pullback is $(C_c\circ f)|_A=\{x\mapsto\varphi(f(x)):\varphi\in C_c\}\le\mathbb F_2^A$.
--   5. The **Gold defect** is
--   $$d_c(f;A)=\dim_{\mathbb F_2}\frac{(C_c\circ f)|_A+\mathrm{RM}(2,N)|_A}{\mathrm{RM}(2,N)|_A},$$
--   the sum and quotient taken inside the function space $\mathbb F_2^A$ (3.45).
--
--   The defect measures how far the pulled-back Gold functions are from quadratic functions on $A$; it is the parameter of the amortized recognition theorem (Theorem 3.44).
--
--   **Formalization Note** $\mathrm{RM}(2,N)|_A$ is written as the span of the constant function, the $\mathbb F_2$-linear functionals of $L$ and their pairwise products; this is the span of the monomials of degree at most two in any fixed binary coordinates, so no coordinates need to be chosen. The quotient dimension is the difference of two finite dimensions.
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), §3.3.1, p.53 (PDF p.55); (3.45), p.55 (PDF p.57)

import Mathlib

namespace OptTwoSrcExt.Supplement

/-- **Additive energy of a finite set `S` in a binary vector space.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), §3.3.1 "Parallel coupled equations and graph energy",
printed p.53 (PDF p.55): "For a finite subset S of a binary vector space, write
E(S) = |{(z1, z2, z3, z4) ∈ S^4 : z1 + z2 + z3 + z4 = 0}|."  -/
noncomputable def addEnergy {V : Type*} [AddCommGroup V] (S : Finset V) : ℕ := by
  classical
  exact ((S ×ˢ S ×ˢ S ×ˢ S).filter fun z => z.1 + z.2.1 + z.2.2.1 + z.2.2.2 = 0).card

/-- **The graph of `f` restricted to `A`**, `Graph(f|A) = {(x, f(x)) : x ∈ A} ⊆ L × L` (p.53). -/
noncomputable def graphOn {L : Type*} (A : Finset L) (f : L → L) : Finset (L × L) := by
  classical
  exact A.image fun x => (x, f x)

/-- **`RM(2, N)|_A`: restrictions to `A` of Boolean polynomials of degree at most two in the binary
coordinates of `L`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), printed p.55 (PDF p.57): "The space RM(2, N)|A consists of
restrictions to A of Boolean polynomials of degree at most two in the fixed binary coordinates of L;
it includes the constant functions."

The span over `𝔽₂`, inside the functions `A → 𝔽₂`, of the constant `1`, the `𝔽₂`-linear functionals
`φ` and the products `φ ψ` of two of them.

**Formalization Note.** Every coordinate function is a linear functional and every linear functional
is a sum of coordinates, so this span equals the span of the monomials of degree at most two in any
fixed binary coordinates of `L`; the definition needs no choice of coordinates. -/
def rm2On {L : Type*} [AddCommGroup L] [Module (ZMod 2) L] (A : Finset L) :
    Submodule (ZMod 2) (A → ZMod 2) :=
  Submodule.span (ZMod 2)
    ({fun _ => 1} ∪ Set.range (fun φ : L →ₗ[ZMod 2] ZMod 2 => fun x : A => φ x) ∪
      Set.range (fun φψ : (L →ₗ[ZMod 2] ZMod 2) × (L →ₗ[ZMod 2] ZMod 2) =>
        fun x : A => φψ.1 x * φψ.2 x))

/-- **The pulled-back Gold space `(C_c ∘ f)|_A`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), printed p.55 (PDF p.57):
"C_c = {z ↦ Tr_{L/F2}(a0 z + Σ_{j=1}^c aj z^{1+2^j}) : a0, . . . , ac ∈ L}. … For A ⊆ L and
f : A → L, its pullback space is (C_c ∘ f)|A := {x ↦ φ(f(x)) : φ ∈ C_c} ⩽ F_2^A."

The span (in fact the set, which is already a subspace) of the functions
`x ↦ Tr_{L/𝔽₂}(a₀ f(x) + Σ_{j=1}^c a_j f(x)^{1+2^j})` on `A`, `a₀, …, a_c ∈ L`. -/
noncomputable def goldPullback {L : Type*} [Field L] [Algebra (ZMod 2) L] (c : ℕ) (A : Finset L)
    (f : L → L) : Submodule (ZMod 2) (A → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun a : Fin (c + 1) → L => fun x : A =>
    Algebra.trace (ZMod 2) L
      (a 0 * f x + ∑ j : Fin c, a j.succ * f x ^ (1 + 2 ^ ((j : ℕ) + 1))))

/-- **The full Gold defect `d_c(f; A)`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), (3.45), printed p.55 (PDF p.57):
"d_c(f; A) = dim_{F2}(((C_c ∘ f)|A + RM(2, N)|A) / RM(2, N)|A). The sum and quotient are taken
inside the function space F_2^A."

`goldDefect c A f = dim((C_c ∘ f)|_A + RM(2,N)|_A) − dim RM(2,N)|_A`, the dimension of the quotient.

**Formalization Note.** The function space `A → 𝔽₂` is finite dimensional, so both dimensions are
finite and the natural-number subtraction is the exact quotient dimension (the second space is
contained in the first). `f` is a map `L → L`; only its values on `A` enter. -/
noncomputable def goldDefect {L : Type*} [Field L] [Algebra (ZMod 2) L] (c : ℕ) (A : Finset L)
    (f : L → L) : ℕ :=
  Module.finrank (ZMod 2) ↥(goldPullback c A f ⊔ rm2On A) - Module.finrank (ZMod 2) ↥(rm2On A)

end OptTwoSrcExt.Supplement


