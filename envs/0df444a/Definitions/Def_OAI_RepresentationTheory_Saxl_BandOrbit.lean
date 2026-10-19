-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
-- name    : OAI_RepresentationTheory_Saxl_BandOrbit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:22:21.296961+00:00
-- url     : https://prove2.me/theorems/5b17a3f7-4f5e-4be3-ac2c-83b83d8bb921
-- title:
--   Blockwise permutation homomorphism and the colored band orbit map
-- statement:
--   Block permutations of a split position set, and an orbit map that spreads a linear map over all recolorings of one block.
--
--   For $n,d\in\mathbb{N}$ write $[n]=\{0,1,\dots,n-1\}$ and let $M_{n,d}$ be the complex vector space of functions $x:[d]^{[n]}\to\mathbb{C}$ on words $w:[n]\to[d]$ (positions $[n]$, letters $[d]$), with indicator vectors $\delta_w$; the symmetric group $\mathfrak S_n$ acts by $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot\delta_w=\delta_{w\circ g^{-1}}$. Fix a bijection $\theta:[n]\to[a]\sqcup[b]$ splitting the positions into a block $A$ of size $a$ and a block $B$ of size $b$. For $g\in\mathfrak S_a$ and $h\in\mathfrak S_b$ let $g\oplus_\theta h\in\mathfrak S_n$ be the permutation that acts as $g$ on the positions of $A$ and as $h$ on those of $B$, transported through $\theta$.
--
--   1. **Block permutations multiply blockwise.** For $g,g'\in\mathfrak S_a$ and $h,h'\in\mathfrak S_b$,
--   $$
--   (gg')\oplus_\theta(hh')=(g\oplus_\theta h)\,(g'\oplus_\theta h'),\qquad 1\oplus_\theta 1=1,
--   $$
--   so $(g,h)\mapsto g\oplus_\theta h$ is a group homomorphism $\mathfrak S_a\times\mathfrak S_b\to\mathfrak S_n$.
--
--   2. **Colored band orbit map.** Let $\rho$ be a representation of $\mathfrak S_n$ on a complex vector space $X$, let $c:[b]\to[k]$ be a coloring of the positions of $B$ with $k$ colors, and let $F:X\to Y$ be a linear map into a complex vector space $Y$. The orbit map $\mathcal O$ is the linear map from $X$ to the space of functions $[k]^{[b]}\to Y$ given, for every coloring $w:[b]\to[k]$, by
--   $$
--   \mathcal O(x)(w)=\sum_{\substack{g\in\mathfrak S_b\\ c\circ g^{-1}=w}}F\big(\rho(1\oplus_\theta g^{-1})\,x\big),
--   $$
--   that is, $\mathcal O(x)=\sum_{g\in\mathfrak S_b}\delta_{c\circ g^{-1}}\otimes F\big(\rho(1\oplus_\theta g^{-1})x\big)$.
--
--   The orbit map spreads a map that only sees the block $A$ over all recolorings of the block $B$. If $F(\rho(h\oplus_\theta 1)x)=\tau(h)F(x)$ for a representation $\tau$ of $\mathfrak S_a$ on $Y$, then $\mathcal O(\rho(h\oplus_\theta q)x)(w)=\tau(h)\,\mathcal O(x)(w\circ q)$ for all $h\in\mathfrak S_a$ and $q\in\mathfrak S_b$; and if $F\neq 0$ is unchanged by the permutations of $B$ that preserve $c$, then $\mathcal O\neq 0$, since $\mathcal O(x)(c)$ is a positive integer multiple of $F(x)$.
--
--   **Formalization Note** The block permutation $g\oplus_\theta h$ is `sumPerm e g h`, defined as `e.symm.permCongr (Equiv.sumCongr g h)`; the two identities of item 1 are the lemmas `sumPerm_mul` and `sumPerm_one`. The orbit map is `bandOrbitMap e ρ c F`, valued in `(Fin b → Fin k) → Y`, and the indicator condition $c\circ g^{-1}=w$ is written as the value at $w$ of `Pi.single (c ∘ g⁻¹) 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/BandOrbit.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/BandOrbit.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

@[simp] lemma sumPerm_mul {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g g' : Equiv.Perm (Fin a)) (h h' : Equiv.Perm (Fin b)) :
    sumPerm e (g*g') (h*h') = sumPerm e g h * sumPerm e g' h' := by
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j <;> simp only [sumPerm_left, sumPerm_right, Equiv.Perm.mul_apply]

@[simp] lemma sumPerm_one {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    sumPerm e 1 1 = 1 := by
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j <;> simp only [sumPerm_left,sumPerm_right,Equiv.Perm.one_apply]

def bandOrbitMap {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y) :
    X →ₗ[ℂ] ((Fin b → Fin k) → Y) where
  toFun x w := ∑ g : Equiv.Perm (Fin b),
    ((Pi.single (c ∘ (g⁻¹ : Equiv.Perm (Fin b))) (1:ℂ) : WordSpace b k) w) • F (ρ (sumPerm e 1 g⁻¹) x)
  map_add' x y := by ext w; simp only [map_add,smul_add,Finset.sum_add_distrib,Pi.add_apply]
  map_smul' c x := by
    ext w
    simp only [map_smul,Pi.smul_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    exact smul_comm _ _ _

end Saxl

end

end OAI


