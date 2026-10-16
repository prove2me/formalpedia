-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
-- name    : OAI_Algebra_AffineCancellation_Clearing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:58:38.077915+00:00
-- url     : https://prove2.me/theorems/5dabf79b-8004-4e38-b090-3001dbf98f75
-- title:
--   Subalgebra of elements whose denominators are cleared by powers of a fixed element
-- statement:
--   Let $k$ be a commutative ring, let $S$ and $R$ be commutative $k$-algebras, let $f:S\to R$ be a $k$-algebra homomorphism and let $p\in S$.
--
--   1. **Clearing subalgebra.** Define
--   $$C_f(p)=\bigl\{\,r\in R\ :\ f(p)^n\,r=f(s)\ \text{for some } n\in\mathbb{N}\text{ and } s\in S\,\bigr\}.$$
--   This set contains $0$, $1$ and the image of $k$, and it is closed under addition and multiplication. It is therefore a $k$-subalgebra of $R$: the elements of $R$ that become values of $f$ after multiplication by a power of $f(p)$.
--
--   2. **Injectivity criterion.** Let $K$ be a commutative $k$-algebra and $e:R\to K$ a $k$-algebra homomorphism. Assume that $e\circ f$ is injective, that $f(p)$ is a non-zero-divisor of $R$ and that $C_f(p)=R$. Then $e$ is injective.
--
--   3. **Generator criterion.** Let $q:k[X_i : i\in I]\to R$ be a surjective $k$-algebra homomorphism from a polynomial ring in variables indexed by an arbitrary set $I$. If $q(X_i)\in C_f(p)$ for every $i\in I$, then $C_f(p)=R$.
--
--   The condition $C_f(p)=R$ says that every element of $R$ is brought into $f(S)$ by multiplication with a suitable power of $f(p)$; informally, $R\subseteq f(S)[f(p)^{-1}]$. The two criteria reduce injectivity of a map out of $R$ to injectivity on $S$, and they reduce the condition $C_f(p)=R$ to a check on generators of $R$.
--
--   **Formalization Note** The subalgebra is `subalgebra f p : Subalgebra k R`. Non-zero-divisors are expressed with `IsLeftRegular`, and the condition $C_f(p)=R$ is `subalgebra f p = ⊤`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Clearing.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Clearing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation

namespace OAI

noncomputable section

namespace ComplexCancellation.Clearing
variable {k S R : Type*} [CommRing k] [CommRing S] [CommRing R] [Algebra k S] [Algebra k R]

/-- Elements whose denominators can be cleared with a power of a fixed base element. -/
def subalgebra (f : S →ₐ[k] R) (p : S) : Subalgebra k R where
  carrier := {r | ∃ n : ℕ, ∃ s : S, f p ^ n * r = f s}
  zero_mem' := ⟨0,0,by simp⟩
  one_mem' := ⟨0,1,by simp⟩
  add_mem' := by
    rintro r s ⟨n,a,ha⟩ ⟨m,b,hb⟩
    refine ⟨n+m,p^m*a+p^n*b,?_⟩
    rw [map_add,map_mul,map_mul,map_pow,map_pow,← ha,← hb,pow_add]
    ring
  mul_mem' := by
    rintro r s ⟨n,a,ha⟩ ⟨m,b,hb⟩
    refine ⟨n+m,a*b,?_⟩
    rw [map_mul,← ha,← hb,pow_add]
    ring
  algebraMap_mem' c := ⟨0,algebraMap k S c,by simp⟩

lemma injective_of_clearing {K : Type*} [CommRing K] [Algebra k K]
    (e : R →ₐ[k] K) (f : S →ₐ[k] R) (p : S)
    (hef : Function.Injective (e.comp f)) (hp : IsLeftRegular (f p))
    (h : subalgebra f p = ⊤) : Function.Injective e := by
  apply (injective_iff_map_eq_zero e).mpr
  intro r hr
  have hm : r ∈ subalgebra f p := by rw [h]; trivial
  obtain ⟨n,s,hs⟩ := hm
  have hz : s = 0 := by
    apply hef
    change e (f s) = e (f 0)
    rw [← hs,map_mul,hr,mul_zero,map_zero,map_zero]
  rw [hz,map_zero] at hs
  exact isLeftRegular_iff_right_eq_zero_of_mul.mp (hp.pow n) r hs

lemma top_of_generators {ι : Type*} (q : MvPolynomial ι k →ₐ[k] R)
    (hq : Function.Surjective q) (f : S →ₐ[k] R) (p : S)
    (hX : ∀ i, q (MvPolynomial.X i) ∈ subalgebra f p) : subalgebra f p = ⊤ := by
  apply top_unique
  intro r hrTop
  clear hrTop
  obtain ⟨r,rfl⟩ := hq r
  induction r using MvPolynomial.induction_on with
  | C c => exact (q.commutes c) ▸ (subalgebra f p).algebraMap_mem c
  | add r s hr hs => rw [map_add]; exact add_mem hr hs
  | mul_X r i hr => rw [map_mul]; exact mul_mem hr (hX i)

end ComplexCancellation.Clearing

end

end OAI


