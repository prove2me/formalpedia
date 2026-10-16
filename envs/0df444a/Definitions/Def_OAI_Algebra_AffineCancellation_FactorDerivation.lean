-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
-- name    : OAI_Algebra_AffineCancellation_FactorDerivation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:52:21.440278+00:00
-- url     : https://prove2.me/theorems/c565ac35-9f8a-4374-b402-cb3acdeeabdf
-- title:
--   Dividing a derivation by a common factor $c$ along an injective algebra map
-- statement:
--   Let $k$ be a commutative ring, let $S$ and $R$ be commutative $k$-algebras with $R$ an integral domain, let $f:S\to R$ be an injective $k$-algebra homomorphism, let $D$ be a $k$-linear derivation of $R$, and let $c\in R$ with $c\neq0$. Assume that for every $s\in S$ there is some $t\in S$ with $D(f(s))=c\,f(t)$.
--
--   1. **The value map.** For $s\in S$, $\delta(s)$ is a chosen element $t$ as in the hypothesis, so that $D(f(s))=c\,f(\delta(s))$ for every $s$. Because $f$ is injective and $c$ can be cancelled in the domain $R$, this $t$ is unique.
--
--   2. **Linearity and the Leibniz rule.** For $s,t\in S$ and $a\in k$,
--   $$\delta(s+t)=\delta(s)+\delta(t),\qquad \delta(as)=a\,\delta(s),\qquad \delta(st)=s\,\delta(t)+t\,\delta(s).$$
--
--   3. **The derivation.** $\delta$ is therefore a $k$-linear derivation of $S$. It is characterized by
--   $$D\bigl(f(s)\bigr)=c\,f\bigl(\delta(s)\bigr)\qquad(s\in S).$$
--
--   Informally, $\delta$ is the derivation $c^{-1}D$ restricted to the subring $f(S)\cong S$. It is defined whenever $D$ maps $f(S)$ into $c\,f(S)$. The construction is used to divide a derivation by a common factor of all its values. A separate result shows that $\delta$ is locally nilpotent whenever $D$ is.
--
--   **Formalization Note** `value` picks $t$ with `Classical.choose` from the hypothesis `h : ∀ s, ∃ t, D (f s) = c * f t`; the defining equation `specification` holds without the domain assumption. The derivation `derivation : Derivation k S S` uses injectivity `hf` and `hc : c ≠ 0` to prove additivity, $k$-linearity and the Leibniz rule.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/FactorDerivation.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/FactorDerivation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension

namespace OAI

noncomputable section

namespace ComplexCancellation.FactorDerivation
variable {k S R : Type*} [CommRing k] [CommRing S] [CommRing R] [IsDomain R]
  [Algebra k S] [Algebra k R]
variable (f : S →ₐ[k] R) (hf : Function.Injective f)
  (D : Derivation k R R) (c : R) (hc : c ≠ 0)
  (h : ∀ s : S, ∃ t : S, D (f s)=c*f t)
def value (s : S) : S := Classical.choose (h s)
omit [IsDomain R] in
lemma specification (s : S) : D (f s)=c*f (value f D c h s) := Classical.choose_spec (h s)
include hf hc in
lemma value_add (s t : S) : value f D c h (s+t)=value f D c h s+value f D c h t := by
  apply hf
  apply mul_left_cancel₀ hc
  rw [← specification,map_add,map_add,map_add,mul_add,← specification,← specification]
include hf hc in
lemma value_smul (a : k) (s : S) : value f D c h (a • s)=a • value f D c h s := by
  apply hf
  apply mul_left_cancel₀ hc
  rw [← specification,map_smul,Derivation.map_smul,map_smul,mul_smul_comm,← specification]
include hf hc in
lemma value_mul (s t : S) :
    value f D c h (s*t)=s*value f D c h t+t*value f D c h s := by
  apply hf
  apply mul_left_cancel₀ hc
  rw [← specification,map_mul,Derivation.leibniz,smul_eq_mul,smul_eq_mul,
    specification f D c h s,specification f D c h t,map_add,map_mul,map_mul]
  ring
def derivation : Derivation k S S where
  toLinearMap := {
    toFun := value f D c h
    map_add' := value_add f hf D c hc h
    map_smul' := value_smul f hf D c hc h }
  map_one_eq_zero' := by
    apply hf
    apply mul_left_cancel₀ hc
    change c*f (value f D c h 1)=c*f 0
    rw [← specification,map_one,Derivation.map_one_eq_zero,map_zero,mul_zero]
  leibniz' s t := by
    exact value_mul f hf D c hc h s t
end ComplexCancellation.FactorDerivation

end

end OAI


