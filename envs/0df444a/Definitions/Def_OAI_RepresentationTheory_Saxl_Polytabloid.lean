-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
-- name    : OAI_RepresentationTheory_Saxl_Polytabloid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T22:44:39.201875+00:00
-- url     : https://prove2.me/theorems/7f00716c-1e01-4f10-b039-a57e050e7bbc
-- title:
--   Complex sign character and the column antisymmetrizer of a tableau
-- statement:
--   For $n\in\mathbb{N}$ write $[n]=\{0,1,\dots,n-1\}$ and let $S_n$ be the symmetric group on $[n]$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}=\mathbb{C}^{[d]^n}$ is the space of complex functions on words, with standard basis vectors $e_a$ (the indicator function of the word $a$), so that $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$. The group $S_n$ acts on $W_{n,d}$ by permuting positions, $(\rho_{n,d}(g)x)(a)=x(a\circ g)$; equivalently $\rho_{n,d}(g)e_a=e_{a\circ g^{-1}}$.
--
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$) closed under decreasing either coordinate, and a tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$. Its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i\in[n]$. The file introduces the following objects.
--
--   1. **Complex sign character.** The multiplicative map $\operatorname{sgn}_{\mathbb{C}}:S_n\to\mathbb{C}$, $g\mapsto\operatorname{sgn}(g)\in\{1,-1\}$, a monoid homomorphism into $(\mathbb{C},\cdot)$. It satisfies $\operatorname{sgn}_{\mathbb{C}}(g^{-1})=\operatorname{sgn}_{\mathbb{C}}(g)$ and $\operatorname{sgn}_{\mathbb{C}}(g)\operatorname{sgn}_{\mathbb{C}}(g)=1$ for all $g\in S_n$.
--   2. **Action on basis words.** For every $g\in S_n$ and every word $a\in[d]^n$,
--   $$
--   \rho_{n,d}(g)\,e_a=e_{a\circ g^{-1}} .
--   $$
--   3. **Column antisymmetrizer.** For a tableau $t$ of shape $\mu$ on $n$ positions and an arbitrary alphabet size $d$, the linear endomorphism
--   $$
--   A_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,\rho_{n,d}(g)\ \in\ \operatorname{End}_{\mathbb{C}}(W_{n,d}).
--   $$
--
--   The antisymmetrizer is the operator behind the polytabloid: if $\ell(\mu)$ is the number of rows of $\mu$ and $r_t:[n]\to[\ell(\mu)]$ is the row word of $t$ (sending $i$ to the row index of $t(i)$), then the polytabloid of $t$ is by definition $e_t=A_t\,e_{r_t}\in W_{n,\ell(\mu)}$ (with $d=\ell(\mu)$), and the Specht module of $t$ is the span of the $S_n$-orbit of $e_t$. In the surrounding development $A_t$ is shown to map the row-tabloid permutation module into the line spanned by $e_t$, which is the key input for the irreducibility of Specht modules.
--
--   **Formalization Note** `signC` composes `Equiv.Perm.sign` with the coercions from the units of the integers into the complex numbers and is a monoid homomorphism into the complex numbers; the identities in item 1 are `signC_def`, `signC_inv` and `signC_mul_self`, item 2 is `wordRep_single` (with `Pi.single a 1` for $e_a$), and `columnAlt t` sums over the finite subgroup `columnGroup t`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/Polytabloid.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/Polytabloid.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- A finite set is the unique maximizer of its strictly signed separator.
Used below for the Ferrers equality case in the Specht submodule theorem. -/
/- A column-injective rearrangement of the canonical row word has precisely
Ferrers support. This is the equality-of-margins argument, without using
unproved Specht or Young-rule inputs. -/
/- The complex-valued sign character. -/
def signC {n : ℕ} : Equiv.Perm (Fin n) →* ℂ :=
  ((Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)).comp Equiv.Perm.sign

@[simp] lemma signC_def {n : ℕ} (g : Equiv.Perm (Fin n)) :
    signC g = (((Equiv.Perm.sign g) : ℤ) : ℂ) := rfl

@[simp] lemma signC_inv {n : ℕ} (g : Equiv.Perm (Fin n)) : signC g⁻¹ = signC g := by
  simp [signC_def, Equiv.Perm.sign_inv]

@[simp] lemma signC_mul_self {n : ℕ} (g : Equiv.Perm (Fin n)) : signC g * signC g = 1 := by
  calc signC g * signC g = signC (g⁻¹ * g) := by rw [map_mul, signC_inv]
       _ = 1 := by rw [inv_mul_cancel, map_one]

lemma wordRep_single {n d : ℕ} (g : Equiv.Perm (Fin n)) (a : Fin n → Fin d) :
    wordRep n d g (Pi.single a 1) = Pi.single (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) (1 : ℂ) := by
  classical
  ext b
  change (Pi.single a (1 : ℂ) : WordSpace n d) (b ∘ g) = _
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    have hh := congrFun h (g⁻¹ i)
    simpa using hh
  · intro h
    funext i
    have hh := congrFun h (g i)
    simpa using hh

/- Actual column antisymmetrizer on the word-coordinate module. -/
def columnAlt {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Module.End ℂ (WordSpace n d) := by
  classical
  letI := Fintype.ofFinite (columnGroup t)
  exact ∑ g : columnGroup t,
    signC (g : Equiv.Perm (Fin n)) • wordRep n d (g : Equiv.Perm (Fin n))

/- Construction of the witnessing column rearrangement. -/
end Saxl

end

end OAI


